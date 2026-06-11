// Mara crash journal — linked into every native build.
//
// Asserts and crash() tee their failure message here: __mara_crash_begin
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
static size_t mara_exe_dir(char* out, size_t cap) {
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
    size_t dir = mara_exe_dir(path, sizeof path - 32);
    snprintf(path + dir, sizeof path - dir, "%s", MARA_CRASH_FILE);
    mara_append_entry(path);

    char tmp[MARA_PATH_CAP];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    mara_crash_trim(path, tmp);
}
