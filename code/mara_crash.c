// Mara crash journal — linked into every native build.
//
// Asserts and crash() tee their failure message here: __mara_crash_begin
// opens crash.txt (append) in the working directory and stamps the entry,
// __mara_tee_printf mirrors each printf into it, __mara_crash_end closes the
// entry and trims the file back under the cap by dropping whole entries,
// oldest first. Entries are separated by a blank line; the trim scans for
// "\n\n". A process writes at most one entry — it exits right after — so the
// file grows at the rate the program crashes.
//
// Compiled once to a sibling mara_crash.o (redone when this file is newer);
// link_native appends it to every native link.

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <time.h>

#define MARA_CRASH_FILE "crash.txt"
#define MARA_CRASH_CAP  (1 << 20)

static FILE* mara_crash_file = NULL;

void __mara_crash_begin(void) {
    mara_crash_file = fopen(MARA_CRASH_FILE, "ab");
    if (!mara_crash_file) return;  // unwritable dir — stdout still reports
    time_t now = time(NULL);
    struct tm* t = localtime(&now);
    char stamp[64];
    if (t && strftime(stamp, sizeof stamp, "%Y-%m-%d %H:%M:%S", t)) {
        fprintf(mara_crash_file, "%s\n", stamp);
    }
}

int __mara_tee_printf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    if (mara_crash_file) {
        va_list copy;
        va_copy(copy, args);
        vfprintf(mara_crash_file, fmt, copy);
        va_end(copy);
    }
    int written = vprintf(fmt, args);
    va_end(args);
    return written;
}

// Drop whole entries from the head until the file fits the cap. Runs after
// the new entry is written, so the newest entry always survives intact.
static void mara_crash_trim(void) {
    FILE* f = fopen(MARA_CRASH_FILE, "rb");
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
    f = fopen(MARA_CRASH_FILE, "wb");
    if (f) {
        fwrite(buf + start, 1, (size_t)(got - start), f);
        fclose(f);
    }
    free(buf);
}

void __mara_crash_end(void) {
    if (!mara_crash_file) return;
    fputc('\n', mara_crash_file);
    fclose(mara_crash_file);
    mara_crash_file = NULL;
    mara_crash_trim();
}
