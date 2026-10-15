// Mara crash journal — linked into every native build.
//
// Asserts and crash() tee their failure message here, and so do crashes the
// program doesn't report itself (a stack overflow, a bad memory access: see
// __mara_crash_install, at the end): __mara_crash_begin
// stamps a new entry, __mara_tee_printf mirrors each printf into it, and
// __mara_crash_end appends the finished entry to crash.txt NEXT TO THE
// EXECUTABLE — not the working directory; programs get launched with
// arbitrary cwds — then trims the file back under the cap by dropping whole
// entries, oldest first. Entries are separated by a blank line; the trim
// scans for "\n\n". A process writes at most one entry — it exits right
// after — so the file grows at the rate the program crashes.
//
// Robustness model:
//   - The entry is built in memory and lands in ONE OS-level append
//     (FILE_APPEND_DATA / O_APPEND), so concurrent crashers can't interleave
//     mid-entry and dying mid-crash can't leave half an entry behind.
//   - The trim rewrites via crash.txt.tmp + rename-over, so a process dying
//     mid-trim can't destroy the journal.
//   - Everything fails soft: stdout still carries the message when the exe
//     path can't be resolved or the disk doesn't cooperate.
//
// Compiled once to a sibling mara_crash.o (redone when this file is newer);
// link_native appends it to every native link.

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <unistd.h>
#include <fcntl.h>
#endif

#define MARA_CRASH_FILE "crash.txt"
#define MARA_CRASH_CAP  (1 << 20)
#define MARA_ENTRY_CAP  (64 * 1024)
#define MARA_PATH_CAP   4096

static char   mara_entry[MARA_ENTRY_CAP];
static size_t mara_entry_len = 0;
static int    mara_entry_active = 0;

// Directory of the running executable, written into `out` WITH a trailing
// separator. Returns the prefix length; 0 means unresolvable (out is then an
// empty string and paths built on it fall back to the working directory).
// (The profiler, runtime/mara_prof.c, writes its file there too.)
size_t __mara_exe_dir(char* out, size_t cap) {
    out[0] = 0;
#ifdef _WIN32
    DWORD n = GetModuleFileNameA(NULL, out, (DWORD)cap);
    if (n == 0 || n >= cap) { out[0] = 0; return 0; }
    size_t i = (size_t)n;
    while (i > 0 && out[i - 1] != '\\' && out[i - 1] != '/') i -= 1;
    out[i] = 0;
    return i;
#elif defined(__linux__)
    ssize_t n = readlink("/proc/self/exe", out, cap - 1);
    if (n <= 0) { out[0] = 0; return 0; }
    out[n] = 0;
    size_t i = (size_t)n;
    while (i > 0 && out[i - 1] != '/') i -= 1;
    out[i] = 0;
    return i;
#else
    return 0;  // unknown platform: cwd fallback
#endif
}

void __mara_crash_begin(void) {
    mara_entry_active = 1;
    mara_entry_len = 0;
    time_t now = time(NULL);
    struct tm* t = localtime(&now);
    char stamp[64];
    if (t && strftime(stamp, sizeof stamp, "%Y-%m-%d %H:%M:%S", t)) {
        int n = snprintf(mara_entry, sizeof mara_entry, "%s\n", stamp);
        if (n > 0) mara_entry_len = (size_t)n;
    }
}

int __mara_tee_printf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    if (mara_entry_active && mara_entry_len < sizeof mara_entry) {
        va_list copy;
        va_copy(copy, args);
        int n = vsnprintf(mara_entry + mara_entry_len,
                          sizeof mara_entry - mara_entry_len, fmt, copy);
        va_end(copy);
        if (n > 0) {
            mara_entry_len += (size_t)n;
            // vsnprintf reports the would-be length; clamp on truncation.
            if (mara_entry_len > sizeof mara_entry) mara_entry_len = sizeof mara_entry;
        }
    }
    int written = vprintf(fmt, args);
    va_end(args);
    return written;
}

// One-shot append: the whole entry in a single OS-level end-of-file write.
static void mara_append_entry(const char* path) {
#ifdef _WIN32
    HANDLE h = CreateFileA(path, FILE_APPEND_DATA,
                           FILE_SHARE_READ | FILE_SHARE_WRITE, NULL,
                           OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h == INVALID_HANDLE_VALUE) return;
    DWORD wrote = 0;
    WriteFile(h, mara_entry, (DWORD)mara_entry_len, &wrote, NULL);
    CloseHandle(h);
#else
    int fd = open(path, O_WRONLY | O_APPEND | O_CREAT, 0644);
    if (fd < 0) return;
    (void)!write(fd, mara_entry, mara_entry_len);
    close(fd);
#endif
}

// Drop whole entries from the head until the file fits the cap. Runs after
// the new entry is written, so the newest entry always survives intact. The
// rewrite goes through a temp file + rename-over: dying mid-trim leaves the
// original journal untouched.
static void mara_crash_trim(const char* path, const char* tmp_path) {
    FILE* f = fopen(path, "rb");
    if (!f) return;
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    if (size <= MARA_CRASH_CAP) { fclose(f); return; }
    char* buf = (char*)malloc((size_t)size);
    if (!buf) { fclose(f); return; }
    fseek(f, 0, SEEK_SET);
    long got = (long)fread(buf, 1, (size_t)size, f);
    fclose(f);
    long start = 0;
    while (got - start > MARA_CRASH_CAP) {
        long i = start;
        while (i + 1 < got && !(buf[i] == '\n' && buf[i + 1] == '\n')) i += 1;
        if (i + 1 >= got) { start = got - MARA_CRASH_CAP; break; }  // one giant entry: hard cut
        start = i + 2;
    }
    FILE* out = fopen(tmp_path, "wb");
    if (!out) { free(buf); return; }
    size_t need = (size_t)(got - start);
    size_t put = fwrite(buf + start, 1, need, out);
    fclose(out);
    free(buf);
    if (put != need) { remove(tmp_path); return; }  // short write: keep the original
#ifdef _WIN32
    MoveFileExA(tmp_path, path, MOVEFILE_REPLACE_EXISTING);
#else
    rename(tmp_path, path);
#endif
}

// --- the calls that were running ------------------------------------------------
//
// A report ends with the calls that were running when it was made, innermost
// first, each where it was in the source:
//
//     at area (dbg.mara:38)
//     at main (dbg.mara:56)
//
// The stack is walked by the unwind info every function has (.pdata), from
// the crash's own registers — or, for an assert's report, from here — and
// each address is named by the program's debug info (its PDB, beside it)
// through dbghelp, loaded only now. That's done on a thread of its own: a
// stack overflow's report has little stack left. An assert's report leaves
// out the runtime's own frames (__mara_*) it starts in; every report leaves
// out the C runtime's below main. A call that calls itself again and again
// is one line, and a deep stack shows its first calls and its last. A
// program with no debug info (a -release build) reports no calls. (A file
// in the program's directory is named from there; another, in full.)

#ifdef _WIN32
#include <dbghelp.h>

#define MARA_FRAMES_CAP  200000   // (a stack overflow's: 1 MB of small frames, and room)
#define MARA_FRAMES_HEAD 40
#define MARA_FRAMES_TAIL 12

typedef BOOL  (WINAPI *Mara_SymInitialize)(HANDLE, PCSTR, BOOL);
typedef DWORD (WINAPI *Mara_SymSetOptions)(DWORD);
typedef BOOL  (WINAPI *Mara_SymFromAddr)(HANDLE, DWORD64, PDWORD64, PSYMBOL_INFO);
typedef BOOL  (WINAPI *Mara_SymGetLineFromAddr64)(HANDLE, DWORD64, PDWORD, PIMAGEHLP_LINE64);

// A frame: its address, and how many times in a row the stack has it.
typedef struct { DWORD64 at; int times; } Mara_Frame;

// A run of frames: `period` of them from `at`, `times` over (calls that call
// each other again and again).
typedef struct { int at, period, times; } Mara_Run;

#define MARA_CYCLE_CAP 4   // (the longest cycle of calls a run folds)

// What the debug info says of an address: its function, its source line.
typedef struct {
    char  name[256];
    char  file[MARA_PATH_CAP];
    DWORD line;
} Mara_Place;

static CONTEXT mara_stack_from;
static int     mara_stack_skip;     // an assert's: the runtime's frames it starts in, left out
static int     mara_stack_done = 0;
static Mara_SymFromAddr          mara_sym_from_addr;
static Mara_SymGetLineFromAddr64 mara_sym_line;
static char    mara_dir[MARA_PATH_CAP];
static size_t  mara_dir_len;

// The stack's frames from a context: each one unwound by its function's
// unwind info; a leaf's (none), returned from the top of its stack. A
// stack too broken to walk ends where it breaks.
static int mara_walk(CONTEXT ctx, Mara_Frame* frames) {
    int n = 0;
    __try {
        for (int k = 0; k < MARA_FRAMES_CAP; k++) {
            if (n > 0 && frames[n - 1].at == ctx.Rip) {
                frames[n - 1].times += 1;
            } else {
                frames[n].at = ctx.Rip;
                frames[n].times = 1;
                n += 1;
            }
            DWORD64 base = 0;
            PRUNTIME_FUNCTION fn = RtlLookupFunctionEntry(ctx.Rip, &base, NULL);
            if (fn) {
                PVOID data;
                DWORD64 frame;
                RtlVirtualUnwind(UNW_FLAG_NHANDLER, base, ctx.Rip, fn, &ctx, &data, &frame, NULL);
            } else {
                ctx.Rip = *(DWORD64*)ctx.Rsp;
                ctx.Rsp += 8;
            }
            if (ctx.Rip == 0) break;
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}
    return n;
}

// A frame's place: of its address, the crash's; of a return address, the
// call's, just before it.
static void mara_place(Mara_Frame* frames, int i, Mara_Place* p) {
    DWORD64 at = frames[i].at - (i > 0 ? 1 : 0);
    p->name[0] = 0;
    p->file[0] = 0;
    p->line = 0;
    union { SYMBOL_INFO info; char room[sizeof(SYMBOL_INFO) + 256]; } sym;
    memset(&sym, 0, sizeof sym);
    sym.info.SizeOfStruct = sizeof(SYMBOL_INFO);
    sym.info.MaxNameLen = 255;
    DWORD64 off = 0;
    if (mara_sym_from_addr(GetCurrentProcess(), at, &off, &sym.info)) snprintf(p->name, sizeof p->name, "%s", sym.info.Name);
    IMAGEHLP_LINE64 line;
    memset(&line, 0, sizeof line);
    line.SizeOfStruct = sizeof line;
    DWORD col = 0;
    if (mara_sym_line(GetCurrentProcess(), at, &col, &line) && line.FileName) {
        snprintf(p->file, sizeof p->file, "%s", line.FileName);
        p->line = line.LineNumber;
    }
}

static int mara_is_mara(Mara_Place* p) {
    size_t n = strlen(p->file);
    return n > 5 && _stricmp(p->file + n - 5, ".mara") == 0;
}

static void mara_print_frame(Mara_Frame* frames, int i) {
    Mara_Place p;
    mara_place(frames, i, &p);
    const char* file = p.file;
    if (mara_dir_len && _strnicmp(file, mara_dir, mara_dir_len) == 0) file += mara_dir_len;
    if (p.line) {
        __mara_tee_printf("  at %s (%s:%lu)\n", p.name[0] ? p.name : "?", file, (unsigned long)p.line);
    } else if (p.name[0]) {
        __mara_tee_printf("  at %s\n", p.name);
    } else {
        // No debug info: its module, and where in it.
        HMODULE mod = NULL;
        char path[MARA_PATH_CAP] = "?";
        if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, (LPCSTR)frames[i].at, &mod)) {
            GetModuleFileNameA(mod, path, sizeof path);
        }
        const char* base = path;
        for (const char* c = path; *c; c++) if (*c == '\\' || *c == '/') base = c + 1;
        __mara_tee_printf("  at %s+0x%llX\n", base, (unsigned long long)(frames[i].at - (DWORD64)mod));
    }
    if (frames[i].times > 1) __mara_tee_printf("  ... the same call %d more times\n", frames[i].times - 1);
}

// Whether the `period` frames from a and from b are the same calls.
static int mara_same(Mara_Frame* frames, int a, int b, int period) {
    for (int k = 0; k < period; k++) {
        if (frames[a + k].at != frames[b + k].at || frames[a + k].times != frames[b + k].times) return 0;
    }
    return 1;
}

static void mara_print_run(Mara_Frame* frames, Mara_Run r) {
    for (int k = 0; k < r.period; k++) mara_print_frame(frames, r.at + k);
    if (r.times > 1) __mara_tee_printf("  ... the %d calls above, %d more times\n", r.period, r.times - 1);
}

static DWORD WINAPI mara_stack_thread(LPVOID unused) {
    (void)unused;
    HMODULE dbghelp = LoadLibraryA("dbghelp.dll");
    if (!dbghelp) return 0;
    Mara_SymInitialize init = (Mara_SymInitialize)(void*)GetProcAddress(dbghelp, "SymInitialize");
    Mara_SymSetOptions options = (Mara_SymSetOptions)(void*)GetProcAddress(dbghelp, "SymSetOptions");
    mara_sym_from_addr = (Mara_SymFromAddr)(void*)GetProcAddress(dbghelp, "SymFromAddr");
    mara_sym_line = (Mara_SymGetLineFromAddr64)(void*)GetProcAddress(dbghelp, "SymGetLineFromAddr64");
    if (!init || !options || !mara_sym_from_addr || !mara_sym_line) return 0;
    options(SYMOPT_LOAD_LINES | SYMOPT_UNDNAME | SYMOPT_DEFERRED_LOADS | SYMOPT_FAIL_CRITICAL_ERRORS | SYMOPT_NO_PROMPTS);
    mara_dir_len = __mara_exe_dir(mara_dir, sizeof mara_dir);
    if (!init(GetCurrentProcess(), mara_dir_len ? mara_dir : NULL, TRUE)) return 0;
    Mara_Frame* frames = (Mara_Frame*)VirtualAlloc(NULL, sizeof(Mara_Frame) * MARA_FRAMES_CAP, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!frames) return 0;
    int n = mara_walk(mara_stack_from, frames);

    // From the first frame not the runtime's own (an assert's) to main.
    Mara_Place p;
    int first = 0;
    for (; mara_stack_skip && first < n; first++) {
        mara_place(frames, first, &p);
        const char* name = p.name;
        while (*name == '_') name++;   // (dbghelp names a C function with one _ fewer)
        if (p.name[0] && strncmp(name, "mara_", 5) != 0) break;
    }
    int last = n - 1, mara = 0;
    for (int i = n - 1; i >= first && i >= n - 32; i--) {
        mara_place(frames, i, &p);
        if (strcmp(p.name, "main") == 0 && mara_is_mara(&p)) { last = i; mara = 1; break; }
    }
    for (int i = first; i <= last && i < first + MARA_FRAMES_HEAD && !mara; i++) {
        mara_place(frames, i, &p);
        mara = mara_is_mara(&p);
    }
    if (!mara) return 0;   // (no debug info)

    // The frames as runs: a cycle of a few calls that repeats (calls that
    // call each other), once.
    Mara_Run* runs = (Mara_Run*)VirtualAlloc(NULL, sizeof(Mara_Run) * (size_t)(last - first + 1), MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!runs) return 0;
    int nruns = 0;
    for (int i = first; i <= last; ) {
        Mara_Run r = {i, 1, 1};
        for (int period = 2; period <= MARA_CYCLE_CAP; period++) {
            int times = 1;
            while (i + (times + 1) * period - 1 <= last && mara_same(frames, i, i + times * period, period)) times += 1;
            if (times >= 3 && times * period > r.times * r.period) r = (Mara_Run){i, period, times};
        }
        runs[nruns++] = r;
        i += r.period * r.times;
    }
    if (nruns <= MARA_FRAMES_HEAD + MARA_FRAMES_TAIL + 1) {
        for (int k = 0; k < nruns; k++) mara_print_run(frames, runs[k]);
    } else {
        long long calls = 0;
        for (int k = MARA_FRAMES_HEAD; k < nruns - MARA_FRAMES_TAIL; k++) {
            for (int j = 0; j < runs[k].period; j++) calls += (long long)frames[runs[k].at + j].times * runs[k].times;
        }
        for (int k = 0; k < MARA_FRAMES_HEAD; k++) mara_print_run(frames, runs[k]);
        __mara_tee_printf("  ... %lld more calls\n", calls);
        for (int k = nruns - MARA_FRAMES_TAIL; k < nruns; k++) mara_print_run(frames, runs[k]);
    }
    return 0;
}

// The calls running at `from`, into the report, once.
static void mara_stack(CONTEXT* from, int skip) {
    if (mara_stack_done) return;
    mara_stack_done = 1;
    mara_stack_from = *from;
    mara_stack_skip = skip;
    fflush(stdout);
    HANDLE t = CreateThread(NULL, 1 << 20, mara_stack_thread, NULL, 0, NULL);
    if (t) {
        WaitForSingleObject(t, 10000);
        CloseHandle(t);
    }
}
#endif

void __mara_crash_end(void) {
    if (!mara_entry_active) return;
#ifdef _WIN32
    {
        CONTEXT here;
        RtlCaptureContext(&here);
        mara_stack(&here, 1);
    }
#endif
    mara_entry_active = 0;
    if (mara_entry_len == 0) return;
    // Blank-line entry separator (message lines already end with '\n').
    if (mara_entry_len >= sizeof mara_entry) mara_entry_len = sizeof mara_entry - 1;
    mara_entry[mara_entry_len] = '\n';
    mara_entry_len += 1;

    char path[MARA_PATH_CAP];
    size_t dir = __mara_exe_dir(path, sizeof path - 32);
    snprintf(path + dir, sizeof path - dir, "%s", MARA_CRASH_FILE);
    mara_append_entry(path);

    char tmp[MARA_PATH_CAP];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    mara_crash_trim(path, tmp);
}

// --- crashes the program doesn't report itself ----------------------------------
//
// A stack overflow, a bad memory access: the OS ends the process without a
// word. main calls __mara_crash_install first thing (a DLL has no main, and
// leaves its host's crashes alone), and such a crash is then reported as an
// assert reports itself — "Crashed: <what>" on stdout and in crash.txt — and
// the process exits with the OS's code for it (0xC00000FD for a stack
// overflow; 128 + the signal on Linux) through exit(), so atexit work still
// runs: a -profile time build's profile, naming the calls that were running. A
// crash inside the report is left to the OS.

#ifdef _WIN32

static const char* mara_exception_name(DWORD code) {
    switch (code) {
    case EXCEPTION_STACK_OVERFLOW:        return "stack overflow";
    case EXCEPTION_ACCESS_VIOLATION:      return "bad memory access";
    case EXCEPTION_IN_PAGE_ERROR:         return "bad memory access (a page that couldn't be read in)";
    case EXCEPTION_DATATYPE_MISALIGNMENT: return "misaligned memory access";
    case EXCEPTION_INT_DIVIDE_BY_ZERO:    return "integer division by zero";
    case EXCEPTION_INT_OVERFLOW:          return "integer overflow";
    case EXCEPTION_ILLEGAL_INSTRUCTION:   return "illegal instruction";
    case EXCEPTION_PRIV_INSTRUCTION:      return "privileged instruction";
    }
    return NULL;
}

static volatile LONG mara_crashing = 0;

static LONG WINAPI mara_crash_filter(EXCEPTION_POINTERS* info) {
    if (InterlockedExchange(&mara_crashing, 1)) return EXCEPTION_CONTINUE_SEARCH;
    EXCEPTION_RECORD* r = info->ExceptionRecord;
    DWORD code = r->ExceptionCode;
    const char* what = mara_exception_name(code);
    __mara_crash_begin();
    if (!what) {
        __mara_tee_printf("Crashed: exception 0x%08lX\n", (unsigned long)code);
    } else if (code == EXCEPTION_ACCESS_VIOLATION && r->NumberParameters >= 2) {
        ULONG_PTR how = r->ExceptionInformation[0];
        __mara_tee_printf("Crashed: %s, %s address 0x%llX\n", what,
                          how == 0 ? "reading" : how == 1 ? "writing" : "running code at",
                          (unsigned long long)r->ExceptionInformation[1]);
    } else {
        __mara_tee_printf("Crashed: %s\n", what);
    }
    mara_stack(info->ContextRecord, 0);
    __mara_crash_end();
    fflush(stdout);
    exit((int)code);
}

void __mara_crash_install(void) {
    // A stack overflow's report runs on what's left of the stack: keep it
    // enough (taken from the stack's 1 MB).
    ULONG reserve = 64 * 1024;
    SetThreadStackGuarantee(&reserve);
    SetUnhandledExceptionFilter(mara_crash_filter);
}

#else

#include <signal.h>
#include <sys/resource.h>

static char mara_signal_stack[64 * 1024];   // the report's: the stack may be what overflowed
static char* mara_stack_top;                 // main's stack, for telling an overflow
static size_t mara_stack_size;
static volatile sig_atomic_t mara_crashing = 0;

static void mara_crash_signal(int sig, siginfo_t* info, void* context) {
    (void)context;
    if (mara_crashing) { signal(sig, SIG_DFL); raise(sig); return; }
    mara_crashing = 1;
    char* at = (char*)info->si_addr;
    int overflow = sig == SIGSEGV && mara_stack_size && at <= mara_stack_top &&
                   at >= mara_stack_top - mara_stack_size - 64 * 1024;
    __mara_crash_begin();
    if (overflow)                         __mara_tee_printf("Crashed: stack overflow\n");
    else if (sig == SIGSEGV || sig == SIGBUS) __mara_tee_printf("Crashed: bad memory access, address %p\n", (void*)at);
    else if (sig == SIGFPE)               __mara_tee_printf("Crashed: arithmetic error (integer division by zero?)\n");
    else if (sig == SIGILL)               __mara_tee_printf("Crashed: illegal instruction\n");
    else                                  __mara_tee_printf("Crashed: signal %d\n", sig);
    __mara_crash_end();
    fflush(stdout);
    exit(128 + sig);
}

void __mara_crash_install(void) {
    char here;
    mara_stack_top = &here;
    struct rlimit rl;
    if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY) mara_stack_size = (size_t)rl.rlim_cur;

    stack_t ss;
    memset(&ss, 0, sizeof ss);
    ss.ss_sp = mara_signal_stack;
    ss.ss_size = sizeof mara_signal_stack;
    sigaltstack(&ss, NULL);

    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_sigaction = mara_crash_signal;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    int sigs[] = { SIGSEGV, SIGBUS, SIGFPE, SIGILL };
    for (int i = 0; i < 4; i++) sigaction(sigs[i], &sa, NULL);
}

#endif
