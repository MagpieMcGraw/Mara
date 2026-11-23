// Mara profiler — linked into `mara build -profile time` builds.
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
//            recursive fun's time isn't counted twice). The average is this
//            over its calls: for a fun that calls itself, its time shared
//            among all its calls — their own times overlap, each holding
//            the calls inside it, and add up to more than the run.
//   self   — the time in its own code, callees excluded
//   inner  — the probed calls inside its outermost calls
//   each call's time (callees included): min, max, and a histogram the
//            median is read from (to within about 3%)
// Times are TSC ticks (rdtsc), turned into seconds at the end by the rate
// measured against the OS clock over the run.
//
// And the call tree: a node per fun per caller — main, game_run under main,
// game_draw under game_run — with the time in the fun and its calls when
// called along that path. A fun that calls itself, however far down, counts
// in the node it's already running in: the tree's paths name no fun twice.
//
// A probed call costs its caller the probes' time (measured at the end: an
// empty call's), and a fun's total has its inner calls' — for a fun that
// makes millions of tiny calls, most of it. That isn't taken off (in place,
// with the optimizer's changes around it, a probe's cost isn't the measured
// one closely enough to subtract); each row says instead how much of its
// total it is: probes %.
//
// At exit (atexit — `exit()` from an assert or crash too) calls still running
// end there (the header names them: where a crash was), and the table goes
// to profile.txt NEXT TO THE EXECUTABLE, one line per fun, the most total time
// first. The file, for readers like
// `mara view`: header lines, then a line starting `total ms` naming the
// columns, then one row per fun — eight numbers, the fun's name, its
// file:line — separated by spaces (no field has one). After the table, a
// line starting `call tree:`, a line naming its columns (`depth`), then a row
// per node, callers before their callees, the callees with the most time
// first: its depth (0: called by nothing), its total ms, its calls, its
// fun's row in the table (from 0), the fun's name.
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
    uint64_t self;
    uint64_t inner;
    uint64_t min, max;
    uint32_t running;   // its calls running now: >1 while it recurses
    uint32_t row;       // its row in the table written
    struct Mara_Prof_Node* last;   // the node of its last call: the next is likely the same
    uint64_t hist[HIST_BUCKETS];
} Mara_Prof_Fun;

// A fun as called along one path: under its caller's node.
typedef struct Mara_Prof_Node {
    Mara_Prof_Fun* fun;
    struct Mara_Prof_Node* parent;
    struct Mara_Prof_Node* child;   // its first callee's
    struct Mara_Prof_Node* next;    // its caller's next callee's
    uint64_t total;                 // the time in it (outermost calls only), callees included
    uint64_t calls;
    uint32_t running;
} Mara_Prof_Node;

#define MARA_PROF_NODES 32768   // the most the tree keeps: calls past them count in their caller's

// What the compiler writes per probed fun: `{ ptr, ptr, ptr }` in the IR.
typedef struct Mara_Prof_Slot {
    const char*    name;
    const char*    where;
    Mara_Prof_Fun* fun;   // null until its first call
} Mara_Prof_Slot;

// A call running: whose, its node in the call tree (and whether the call
// counts there: not when the tree was full), when it began, how much of it
// its callees took, and how many probed calls ended inside it.
typedef struct Mara_Prof_Frame {
    Mara_Prof_Fun* fun;
    Mara_Prof_Node* node;
    uint64_t start;
    uint64_t callees;
    uint64_t inner;
    uint32_t counts;
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
    Mara_Prof_Node   root;         // the call tree: its callees are the calls nothing called (main)
    Mara_Prof_Node*  nodes;        // room for MARA_PROF_NODES
    size_t           nnodes;
    uint64_t         untreed;      // calls the full tree had no node for
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
    // (A fun timed around its calls has a slot in each module that calls it:
    // one line for all of them.)
    for (size_t i = 0; i < prof.nfuns; i++) {
        Mara_Prof_Fun* had = prof.funs[i];
        if (strcmp(had->name, slot->name) == 0 && strcmp(had->where, slot->where) == 0) { slot->fun = had; return had; }
    }
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

// The node of fun f called from the node `at`: made on the first such call.
// NULL when the tree is full.
static Mara_Prof_Node* prof_node(Mara_Prof_Node* at, Mara_Prof_Fun* f) {
    for (Mara_Prof_Node* n = at->child; n; n = n->next) if (n->fun == f) return n;
    if (!prof.nodes) {
        prof.nodes = (Mara_Prof_Node*)calloc(MARA_PROF_NODES, sizeof *prof.nodes);
        if (!prof.nodes) prof_fail("out of memory");
    }
    if (prof.nnodes == MARA_PROF_NODES) return NULL;
    Mara_Prof_Node* n = &prof.nodes[prof.nnodes++];
    n->fun = f;
    n->parent = at;
    n->next = at->child;
    at->child = n;
    return n;
}

void __mara_prof_enter(Mara_Prof_Slot* slot) {
    Mara_Prof_Fun* f = slot->fun;
    if (!f) f = prof_register(slot);
    // Its node: its last call's when the caller's the same; a call of a fun
    // that's running, the node it runs in up the path; else found among the
    // caller's, or made.
    Mara_Prof_Node* at = prof.depth ? prof.stack[prof.depth - 1].node : &prof.root;
    Mara_Prof_Node* n = f->last;
    uint32_t counts = 1;
    if (!n || n->parent != at) {
        n = NULL;
        if (f->running) for (n = at; n && n->fun != f; n = n->parent) {}
        if (!n) n = prof_node(at, f);
        if (n) f->last = n;
        else { n = at; counts = 0; prof.untreed += 1; }
    }
    if (prof.depth == prof.capstack) {
        prof.capstack = prof.capstack ? prof.capstack * 2 : 1024;
        prof.stack = (Mara_Prof_Frame*)realloc(prof.stack, prof.capstack * sizeof *prof.stack);
        if (!prof.stack) prof_fail("out of memory");
    }
    Mara_Prof_Frame* fr = &prof.stack[prof.depth++];
    fr->fun = f;
    fr->node = n;
    fr->counts = counts;
    fr->callees = 0;
    fr->inner = 0;
    f->running += 1;
    n->running += counts;
    fr->start = prof_ticks();   // last: the probe's own work isn't the fun's
}

// The call on top of the stack ends at `t`.
static void prof_end_call(uint64_t t) {
    Mara_Prof_Frame* fr = &prof.stack[--prof.depth];
    Mara_Prof_Fun* f = fr->fun;
    uint64_t d = t - fr->start;
    f->calls += 1;
    f->self += d > fr->callees ? d - fr->callees : 0;
    f->running -= 1;
    if (f->running == 0) {
        f->total += d;
        f->inner += fr->inner;
    }
    if (f->calls == 1 || d < f->min) f->min = d;
    if (d > f->max) f->max = d;
    f->hist[prof_bucket(d)] += 1;
    if (fr->counts) {
        Mara_Prof_Node* n = fr->node;
        n->calls += 1;
        n->running -= 1;
        if (n->running == 0) n->total += d;
    }
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
    // (Its node isn't the tree's: taken off again.)
    Mara_Prof_Node* was_child = prof.root.child;
    size_t was_nodes = prof.nnodes;
    uint64_t was_untreed = prof.untreed;
    uint64_t t0 = prof_ticks();
    for (int i = 0; i < N; i++) {
        __mara_prof_enter(&slot);
        __mara_prof_exit(&slot);
    }
    double each = (double)(prof_ticks() - t0) / N;
    prof.root.child = was_child;
    prof.nnodes = was_nodes;
    prof.untreed = was_untreed;
    return each;
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

static int prof_node_by_total(const void* a, const void* b) {
    const Mara_Prof_Node* x = *(Mara_Prof_Node* const*)a;
    const Mara_Prof_Node* y = *(Mara_Prof_Node* const*)b;
    if (x->total != y->total) return x->total > y->total ? -1 : 1;
    return strcmp(x->fun->name, y->fun->name);
}

// The callees of a node written, each before its own: the most time first.
static void prof_dump_nodes(FILE* out, const Mara_Prof_Node* at, int depth, double ms) {
    size_t n = 0;
    for (Mara_Prof_Node* c = at->child; c; c = c->next) n++;
    if (n == 0) return;
    Mara_Prof_Node** sorted = (Mara_Prof_Node**)malloc(n * sizeof *sorted);
    if (!sorted) return;
    n = 0;
    for (Mara_Prof_Node* c = at->child; c; c = c->next) sorted[n++] = c;
    qsort(sorted, n, sizeof *sorted, prof_node_by_total);
    for (size_t i = 0; i < n; i++) {
        const Mara_Prof_Node* c = sorted[i];
        fprintf(out, "%12d %12.3f %10llu %6u  %*s%s\n", depth, c->total * ms,
                (unsigned long long)c->calls, c->fun->row, depth * 2, "", c->fun->name);
        prof_dump_nodes(out, c, depth + 1, ms);
    }
    free(sorted);
}

static void prof_dump(void) {
    uint64_t end = prof_ticks();
    size_t open = prof.depth;
    // The calls running, innermost first: where a crash was. A fun's calls in
    // a row (a recursion) are one line.
    enum { SHOWN = 20 };
    Mara_Prof_Fun* running[SHOWN];
    size_t times[SHOWN], shown = 0, listed = 0;
    for (size_t i = open; i > 0; i--) {
        Mara_Prof_Fun* f = prof.stack[i - 1].fun;
        if (shown > 0 && running[shown - 1] == f) { times[shown - 1]++; listed++; continue; }
        if (shown == SHOWN) break;
        running[shown] = f;
        times[shown++] = 1;
        listed++;
    }
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
    if (open) {
        if (open == 1) fprintf(out, "1 call was running at exit; its time ends there:\n");
        else           fprintf(out, "%zu calls were running at exit; their times end there. Innermost first:\n", open);
        for (size_t i = 0; i < shown; i++) {
            fprintf(out, "    %s  %s", running[i]->name, running[i]->where);
            if (times[i] > 1) fprintf(out, "  (%zu calls in a row)", times[i]);
            fprintf(out, "\n");
        }
        if (open > listed) fprintf(out, "    ... %zu more\n", open - listed);
    }
    fprintf(out, "\n");

    qsort(prof.funs, prof.nfuns, sizeof *prof.funs, prof_by_total);
    int wname = 3;
    for (size_t i = 0; i < prof.nfuns; i++) {
        int n = (int)strlen(prof.funs[i]->name);
        if (n > wname) wname = n;
    }
    fprintf(out, "%12s %12s %10s %12s %12s %12s %12s %8s  %-*s  %s\n",
            "total ms", "self ms", "calls", "avg us", "min us", "median us", "max us", "probes %", wname, "fun", "where");
    uint32_t rows = 0;
    for (size_t i = 0; i < prof.nfuns; i++) {
        Mara_Prof_Fun* f = prof.funs[i];
        if (f->calls == 0) continue;
        f->row = rows++;
        double probes = f->total ? f->inner * probe / f->total * 100 : 0;
        fprintf(out, "%12.3f %12.3f %10llu %12.3f %12.3f %12.3f %12.3f %8.0f  %-*s  %s\n",
                f->total * ms, f->self * ms, (unsigned long long)f->calls,
                (double)f->total / f->calls * us, f->min * us, prof_median(f) * us, f->max * us,
                probes > 100 ? 100 : probes, wname, f->name, f->where);
    }

    fprintf(out, "\ncall tree: each fun under its caller, with its time when called from there. row: the fun's line in the table above, from 0.");
    if (prof.untreed) fprintf(out, " The tree was full (%d nodes): %llu calls count in their callers only.", MARA_PROF_NODES, (unsigned long long)prof.untreed);
    fprintf(out, "\n%12s %12s %10s %6s  %s\n", "depth", "total ms", "calls", "row", "fun");
    prof_dump_nodes(out, &prof.root, 0, ms);
    fclose(out);
    fflush(stdout);   // (the program's output first)
    fprintf(stderr, "profile: %s\n", path);
}
