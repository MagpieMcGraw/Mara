// Mara profiler — linked into `mara build -profile` builds.
//
// Each fun the compiler probes (llvm.odin: one that calls something or loops,
// and main) calls __mara_prof_enter first thing and __mara_prof_exit before
// each return, passing its slot: a global the compiler writes per fun with
// its name and where it's written, and a pointer this file fills on the fun's
// first call. Straight-line code that calls nothing isn't probed — a probe
// would cost more than it — so its time is its caller's own.
//
// Per fun it keeps:
//   calls  — how many calls ended
//   total  — the time in it, callees included (outermost calls only, so a
//            recursive fun's time isn't counted twice)
//   sum    — every call's time added up: the average's
//   self   — the time in its own code, callees excluded
//   inner  — the probed calls inside its outermost calls
//   each call's time (callees included): min, max, and a histogram the
//            median is read from (to within about 3%)
// Times are TSC ticks (rdtsc), turned into seconds at the end by the rate
// measured against the OS clock over the run.
//
// A probed call costs its caller the probes' time (measured at the end: an
// empty call's), and a fun's total has its inner calls' — for a fun that
// makes millions of tiny calls, most of it. That isn't taken off (in place,
// with the optimizer's changes around it, a probe's cost isn't the measured
// one closely enough to subtract); each row says instead how much of its
// total it is: probes %.
//
// At exit (atexit — `exit()` from an assert or crash too) calls still running
// end there, and the table goes to profile.txt NEXT TO THE EXECUTABLE, one
// line per fun, the most total time first. The file, for readers like
// `mara view`: header lines, then a line starting `total ms` naming the
// columns, then one row per fun — eight numbers, the fun's name, its
// file:line — separated by spaces (no field has one).
//
// One thread: Mara programs have one. An exit whose fun isn't the call
// running is a compiler bug — reported, and the process ends without a
// profile rather than with a wrong one.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <unistd.h>
#endif

#define MARA_PROF_FILE "profile.txt"
#define MARA_PATH_CAP  4096

// The histogram of a fun's call times: times under 16 ticks exactly, the rest
// by their top 5 bits — 16 buckets per doubling, each 1/16 of it wide.
#define HIST_LINEAR   16
#define HIST_SUB_BITS 4
#define HIST_SUB      (1 << HIST_SUB_BITS)
#define HIST_BUCKETS  (HIST_LINEAR + (64 - HIST_SUB_BITS) * HIST_SUB)

typedef struct Mara_Prof_Fun {
    const char* name;
    const char* where;
    uint64_t calls;
    uint64_t total;
    uint64_t sum;
    uint64_t self;
    uint64_t inner;
    uint64_t min, max;
    uint32_t running;   // its calls running now: >1 while it recurses
    uint64_t hist[HIST_BUCKETS];
} Mara_Prof_Fun;

// What the compiler writes per probed fun: `{ ptr, ptr, ptr }` in the IR.
typedef struct Mara_Prof_Slot {
    const char*    name;
    const char*    where;
    Mara_Prof_Fun* fun;   // null until its first call
} Mara_Prof_Slot;

// A call running: whose, when it began, how much of it its callees took, and
// how many probed calls ended inside it.
typedef struct Mara_Prof_Frame {
    Mara_Prof_Fun* fun;
    uint64_t start;
    uint64_t callees;
    uint64_t inner;
} Mara_Prof_Frame;

static struct {
    int              started;
    const char*      build;        // "debug build" / "release build", from main
    uint64_t         start_ticks;
    double           start_os;     // seconds, the OS clock
    Mara_Prof_Fun**  funs;         // every fun called, in first-call order
    size_t           nfuns, capfuns;
    Mara_Prof_Frame* stack;
    size_t           depth, capstack;
} prof;

// Directory of the running executable (runtime/mara_crash.c).
size_t __mara_exe_dir(char* out, size_t cap);

static uint64_t prof_ticks(void) {
#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
    return __builtin_ia32_rdtsc();
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
#endif
}

static double prof_os_seconds(void) {
#ifdef _WIN32
    LARGE_INTEGER c, f;
    QueryPerformanceCounter(&c);
    QueryPerformanceFrequency(&f);
    return (double)c.QuadPart / (double)f.QuadPart;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
#endif
}

static void prof_fail(const char* what) {
    fprintf(stderr, "profile: %s\n", what);
    _Exit(1);
}

static void prof_dump(void);

// The run's start. Main calls it first thing, naming the build; a probed fun
// called before that (a global's initializer) starts the run itself.
void __mara_prof_start(const char* build) {
    if (build) prof.build = build;
    if (prof.started) return;
    prof.started = 1;
    prof.start_ticks = prof_ticks();
    prof.start_os = prof_os_seconds();
    atexit(prof_dump);
}

static Mara_Prof_Fun* prof_register(Mara_Prof_Slot* slot) {
    if (!prof.started) __mara_prof_start(NULL);
    Mara_Prof_Fun* f = (Mara_Prof_Fun*)calloc(1, sizeof *f);
    if (!f) prof_fail("out of memory");
    f->name = slot->name;
    f->where = slot->where;
    if (prof.nfuns == prof.capfuns) {
        prof.capfuns = prof.capfuns ? prof.capfuns * 2 : 256;
        prof.funs = (Mara_Prof_Fun**)realloc(prof.funs, prof.capfuns * sizeof *prof.funs);
        if (!prof.funs) prof_fail("out of memory");
    }
    prof.funs[prof.nfuns++] = f;
    slot->fun = f;
    return f;
}

static int prof_bucket(uint64_t t) {
    if (t < HIST_LINEAR) return (int)t;
    int e = 63 - __builtin_clzll(t);   // >= HIST_SUB_BITS
    int sub = (int)((t >> (e - HIST_SUB_BITS)) & (HIST_SUB - 1));
    return HIST_LINEAR + (e - HIST_SUB_BITS) * HIST_SUB + sub;
}

// The middle of a bucket's range of ticks.
static double prof_bucket_mid(int b) {
    if (b < HIST_LINEAR) return (double)b;
    int i = b - HIST_LINEAR;
    int e = i / HIST_SUB + HIST_SUB_BITS, sub = i % HIST_SUB;
    double width = ldexp(1.0, e - HIST_SUB_BITS);
    return ldexp(1.0, e) + sub * width + width / 2;
}

void __mara_prof_enter(Mara_Prof_Slot* slot) {
    Mara_Prof_Fun* f = slot->fun;
    if (!f) f = prof_register(slot);
    if (prof.depth == prof.capstack) {
        prof.capstack = prof.capstack ? prof.capstack * 2 : 1024;
        prof.stack = (Mara_Prof_Frame*)realloc(prof.stack, prof.capstack * sizeof *prof.stack);
        if (!prof.stack) prof_fail("out of memory");
    }
    Mara_Prof_Frame* fr = &prof.stack[prof.depth++];
    fr->fun = f;
    fr->callees = 0;
    fr->inner = 0;
    f->running += 1;
    fr->start = prof_ticks();   // last: the probe's own work isn't the fun's
}

// The call on top of the stack ends at `t`.
static void prof_end_call(uint64_t t) {
    Mara_Prof_Frame* fr = &prof.stack[--prof.depth];
    Mara_Prof_Fun* f = fr->fun;
    uint64_t d = t - fr->start;
    f->calls += 1;
    f->sum += d;
    f->self += d > fr->callees ? d - fr->callees : 0;
    f->running -= 1;
    if (f->running == 0) {
        f->total += d;
        f->inner += fr->inner;
    }
    if (f->calls == 1 || d < f->min) f->min = d;
    if (d > f->max) f->max = d;
    f->hist[prof_bucket(d)] += 1;
    if (prof.depth > 0) {
        Mara_Prof_Frame* caller = &prof.stack[prof.depth - 1];
        caller->callees += d;
        caller->inner += fr->inner + 1;
    }
}

void __mara_prof_exit(Mara_Prof_Slot* slot) {
    uint64_t t = prof_ticks();   // first: the probe's own work isn't the fun's
    if (prof.depth == 0 || prof.stack[prof.depth - 1].fun != slot->fun) {
        char msg[512];
        snprintf(msg, sizeof msg, "'%s' (%s) returned while %s was running: a compiler bug; no profile written",
                 slot->name, slot->where, prof.depth ? prof.stack[prof.depth - 1].fun->name : "no call");
        prof_fail(msg);
    }
    prof_end_call(t);
}

// Ticks per second: the ticks over the OS clock's seconds since the start —
// waited out to a tenth of a second, so a short run's rate is still good.
static double prof_rate(void) {
#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
    double os = prof_os_seconds();
    while (os - prof.start_os < 0.1) os = prof_os_seconds();
    return (double)(prof_ticks() - prof.start_ticks) / (os - prof.start_os);
#else
    return 1e9;
#endif
}

// What a probed call costs its caller: an empty call's enter and exit, timed.
static double prof_probe_ticks(void) {
    static Mara_Prof_Fun empty;
    static Mara_Prof_Slot slot = { "", "", &empty };
    enum { N = 100000 };
    uint64_t t0 = prof_ticks();
    for (int i = 0; i < N; i++) {
        __mara_prof_enter(&slot);
        __mara_prof_exit(&slot);
    }
    return (double)(prof_ticks() - t0) / N;
}

// The running executable's file name: "" when it can't be told.
static void prof_exe_name(char* out, size_t cap) {
    char full[MARA_PATH_CAP];
    size_t dir = __mara_exe_dir(full, sizeof full);
#ifdef _WIN32
    DWORD n = GetModuleFileNameA(NULL, full, (DWORD)sizeof full);
    if (n == 0 || n >= sizeof full) { full[0] = 0; dir = 0; }
#elif defined(__linux__)
    ssize_t n = readlink("/proc/self/exe", full, sizeof full - 1);
    full[n > 0 ? n : 0] = 0;
    if (n <= 0) dir = 0;
#else
    full[0] = 0; dir = 0;
#endif
    snprintf(out, cap, "%s", full + dir);
}

static uint64_t prof_median(const Mara_Prof_Fun* f) {
    uint64_t half = (f->calls + 1) / 2, seen = 0;
    for (int b = 0; b < HIST_BUCKETS; b++) {
        seen += f->hist[b];
        if (seen >= half) {
            double m = prof_bucket_mid(b);
            if (m < (double)f->min) return f->min;
            if (m > (double)f->max) return f->max;
            return (uint64_t)m;
        }
    }
    return f->max;
}

static int prof_by_total(const void* a, const void* b) {
    const Mara_Prof_Fun* x = *(Mara_Prof_Fun* const*)a;
    const Mara_Prof_Fun* y = *(Mara_Prof_Fun* const*)b;
    if (x->total != y->total) return x->total > y->total ? -1 : 1;
    return strcmp(x->name, y->name);
}

static void prof_dump(void) {
    uint64_t end = prof_ticks();
    size_t open = prof.depth;
    while (prof.depth > 0) prof_end_call(end);
    double rate = prof_rate();
    double probe = prof_probe_ticks();
    double ms = 1e3 / rate, us = 1e6 / rate;

    char path[MARA_PATH_CAP];
    size_t dir = __mara_exe_dir(path, sizeof path - 32);
    snprintf(path + dir, sizeof path - dir, "%s", MARA_PROF_FILE);
    FILE* out = fopen(path, "wb");
    if (!out) {
        fprintf(stderr, "profile: can't write %s\n", path);
        return;
    }

    char stamp[64] = "";
    time_t now = time(NULL);
    struct tm* tm = localtime(&now);
    if (tm) strftime(stamp, sizeof stamp, "%Y-%m-%d %H:%M:%S", tm);
    char exe[MARA_PATH_CAP];
    prof_exe_name(exe, sizeof exe);
    double run = (double)(end - prof.start_ticks) / rate;
    fprintf(out, "Mara profile: %s, %s, %.3f %s, %s\n", exe, prof.build ? prof.build : "build unknown",
            run < 1 ? run * 1e3 : run, run < 1 ? "ms" : "s", stamp);
    fprintf(out, "Times per call include the callees; self is the fun's own code. Median: within about 3%%.\n");
    fprintf(out, "Each probed call costs its caller about %.3f us; probes %% is how much of a fun's total that is, for the calls inside it.\n", probe * us);
    fprintf(out, "Funs that call nothing and don't loop aren't probed: their time is their caller's self.\n");
    if (open) fprintf(out, "%zu calls were running at exit; their times end there.\n", open);
    fprintf(out, "\n");

    qsort(prof.funs, prof.nfuns, sizeof *prof.funs, prof_by_total);
    int wname = 3;
    for (size_t i = 0; i < prof.nfuns; i++) {
        int n = (int)strlen(prof.funs[i]->name);
        if (n > wname) wname = n;
    }
    fprintf(out, "%12s %12s %10s %12s %12s %12s %12s %8s  %-*s  %s\n",
            "total ms", "self ms", "calls", "avg us", "min us", "median us", "max us", "probes %", wname, "fun", "where");
    for (size_t i = 0; i < prof.nfuns; i++) {
        Mara_Prof_Fun* f = prof.funs[i];
        if (f->calls == 0) continue;
        double probes = f->total ? f->inner * probe / f->total * 100 : 0;
        fprintf(out, "%12.3f %12.3f %10llu %12.3f %12.3f %12.3f %12.3f %8.0f  %-*s  %s\n",
                f->total * ms, f->self * ms, (unsigned long long)f->calls,
                (double)f->sum / f->calls * us, f->min * us, prof_median(f) * us, f->max * us,
                probes > 100 ? 100 : probes, wname, f->name, f->where);
    }
    fclose(out);
    fflush(stdout);   // (the program's output first)
    fprintf(stderr, "profile: %s\n", path);
}
