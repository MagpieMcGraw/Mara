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

void __mara_crash_end(void) {
    if (!mara_entry_active) return;
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
// runs: a -profile build's profile, naming the calls that were running. A
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
