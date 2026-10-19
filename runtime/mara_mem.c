// Mara memory profiler — linked into `mara build -profile memory` builds.
//
// How full each partial array ([..N]T) ever gets, and how much of each arena
// is ever in use at once: what to size their N, their bytes, by.
//
// The compiler tells it about a partial array by its address — its len, the
// elements right after it (codegen.odin, PARTIAL_ELEMENTS_FIELD):
//   __mara_mem_new(hdr, site)   one laid down — a declaration, a constructor's
//                               field, a zeroing: a new instance of its site
//   __mara_mem_into(hdr, site)  one copied into place: the instance there when
//                               it's this one (its site, its elements), else a
//                               new one (no site: none)
//   __mara_mem_len(hdr)         a len written — `.len =`, an append, a take, a
//                               copy of elements in: the instance there, if
//                               any, sees it
// A site is where an N is written — a local's declaration, a struct's field:
// a global the compiler writes per site in each module it's used in (its
// name, where it's written, its cap, its element's size, and this file's
// record of it, filled on first use; the same site from several modules is
// one record, by name and place).
//
// Arenas (mara.memory, under #profile_memory) tell it themselves, after
// their cursor moves:
//   __mara_mem_arena(kind, base)  base's len the bytes in use, its cap the
//                                 arena's size; base's elements say which
//
// What's at a list's address later may be something else: the instance there
// ended (its frame left, its storage reused) — told by a new one laid down
// there, or one of another site copied in.
//
// Per site: instances, cap, element size, the peak len any instance reached,
// the median of the instances' peaks (a log histogram: within about 3%), and
// so the bytes each instance reserves and what shrinking N to the peak would
// save. At exit (atexit — `exit()` from an assert or crash too) every instance
// still there ends, and the table goes to memory.txt NEXT TO THE EXECUTABLE:
// header lines, then a line starting `unused B` naming the columns, then one
// row per site — seven numbers, the site's name, its file:line — the most
// unused bytes first; then a line starting `size B` naming the arenas'
// columns, one row per arena — three numbers, its kind. Fields are separated
// by spaces (none has one).
//
// One thread: Mara programs have one.

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

#define MARA_MEM_FILE "memory.txt"
#define MARA_PATH_CAP 4096

// The histogram of a site's instances' peaks: under 16 exactly, the rest by
// their top 5 bits — 16 buckets per doubling, each 1/16 of it wide.
#define HIST_LINEAR   16
#define HIST_SUB_BITS 4
#define HIST_SUB      (1 << HIST_SUB_BITS)
#define HIST_BUCKETS  (HIST_LINEAR + (64 - HIST_SUB_BITS) * HIST_SUB)

// A slice's header, as Mara lays it out (codegen.odin, SLICE): its len, its
// cap, its elements' address — an arena's base.
typedef struct Mara_Header {
    int64_t len;
    int64_t cap;
    void*   data;
} Mara_Header;
// A partial array: its len, its elements after it (its cap, its type's: the
// site's).
typedef struct Mara_List {
    int64_t len;
} Mara_List;

typedef struct Mara_Mem_Rec {
    const char* name;
    const char* where;
    int64_t cap;
    int64_t elem;
    uint64_t instances;
    int64_t peak;        // the most any instance held
    int64_t least;       // the least any instance's most was
    uint64_t hist[HIST_BUCKETS];
} Mara_Mem_Rec;

// What the compiler writes per site: `{ ptr, ptr, i64, i64, ptr }` in the IR.
typedef struct Mara_Mem_Site {
    const char*   name;
    const char*   where;
    int64_t       cap;
    int64_t       elem;
    Mara_Mem_Rec* rec;   // filled on first use
} Mara_Mem_Site;

// An instance: a partial array alive at its header's address.
typedef struct Mara_Mem_Inst {
    const Mara_List* hdr;     // NULL: empty; TOMB: was one
    void*         data;
    int64_t       cap;
    Mara_Mem_Rec* rec;
    int64_t       peak;
} Mara_Mem_Inst;

#define TOMB ((const Mara_List*)1)

typedef struct Mara_Mem_Arena {
    const char* kind;
    void*   data;
    int64_t size;
    int64_t peak;
} Mara_Mem_Arena;

static struct {
    const char*     build;
    Mara_Mem_Inst*  slots;    // open addressing by header address
    size_t          cap, used, live;
    Mara_Mem_Rec**  recs;
    size_t          nrecs, caprecs;
    Mara_Mem_Arena* arenas;
    size_t          narenas, caparenas;
    uint64_t        len_probes;
} mem;

size_t __mara_exe_dir(char* out, size_t cap);

static void mem_dump(void);

// The run's start: main calls it first thing, naming the build.
void __mara_mem_start(const char* build) {
    if (build) mem.build = build;
    atexit(mem_dump);
}

static int mem_bucket(uint64_t t) {
    if (t < HIST_LINEAR) return (int)t;
    int e = 63 - __builtin_clzll(t);   // >= HIST_SUB_BITS
    int sub = (int)((t >> (e - HIST_SUB_BITS)) & (HIST_SUB - 1));
    return HIST_LINEAR + (e - HIST_SUB_BITS) * HIST_SUB + sub;
}

// The middle of a bucket's range.
static double mem_bucket_mid(int b) {
    if (b < HIST_LINEAR) return (double)b;
    int i = b - HIST_LINEAR;
    int e = i / HIST_SUB + HIST_SUB_BITS, sub = i % HIST_SUB;
    double width = ldexp(1.0, e - HIST_SUB_BITS);
    return ldexp(1.0, e) + sub * width + width / 2;
}

static int64_t mem_median(const Mara_Mem_Rec* r) {
    uint64_t half = (r->instances + 1) / 2, seen = 0;
    for (int b = 0; b < HIST_BUCKETS; b++) {
        seen += r->hist[b];
        if (seen >= half) {
            double m = mem_bucket_mid(b);
            if (m > (double)r->peak) return r->peak;
            if (m < (double)r->least) return r->least;
            return (int64_t)m;
        }
    }
    return r->peak;
}

// A site's record: the one for its name and place, made on first use.
static Mara_Mem_Rec* mem_rec(Mara_Mem_Site* site) {
    if (site->rec) return site->rec;
    for (size_t i = 0; i < mem.nrecs; i++) {
        Mara_Mem_Rec* r = mem.recs[i];
        if (r->cap == site->cap && r->elem == site->elem &&
            strcmp(r->name, site->name) == 0 && strcmp(r->where, site->where) == 0) {
            site->rec = r;
            return r;
        }
    }
    Mara_Mem_Rec* r = (Mara_Mem_Rec*)calloc(1, sizeof *r);
    if (!r) { fprintf(stderr, "memory profile: out of memory\n"); exit(1); }
    r->name = site->name;
    r->where = site->where;
    r->cap = site->cap;
    r->elem = site->elem;
    if (mem.nrecs == mem.caprecs) {
        mem.caprecs = mem.caprecs ? mem.caprecs * 2 : 256;
        mem.recs = (Mara_Mem_Rec**)realloc(mem.recs, mem.caprecs * sizeof *mem.recs);
        if (!mem.recs) { fprintf(stderr, "memory profile: out of memory\n"); exit(1); }
    }
    mem.recs[mem.nrecs++] = r;
    site->rec = r;
    return r;
}

static size_t mem_hash(const void* p) {
    uint64_t x = (uint64_t)(uintptr_t)p;
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33;
    return (size_t)x;
}

// The instance at a header's address, or NULL.
static Mara_Mem_Inst* mem_find(const Mara_List* hdr) {
    if (!mem.cap) return NULL;
    size_t mask = mem.cap - 1;
    for (size_t i = mem_hash(hdr) & mask;; i = (i + 1) & mask) {
        Mara_Mem_Inst* s = &mem.slots[i];
        if (s->hdr == hdr) return s;
        if (s->hdr == NULL) return NULL;
    }
}

// An instance ended: its peak to its site's.
static void mem_end(Mara_Mem_Inst* s) {
    Mara_Mem_Rec* r = s->rec;
    if (r->instances == 0 || s->peak < r->least) r->least = s->peak;
    r->instances++;
    if (s->peak > r->peak) r->peak = s->peak;
    r->hist[mem_bucket((uint64_t)(s->peak < 0 ? 0 : s->peak))]++;
    s->hdr = TOMB;
    mem.live--;
}

static void mem_grow(void) {
    size_t old = mem.cap;
    Mara_Mem_Inst* slots = mem.slots;
    mem.cap = old ? old * 2 : 4096;
    mem.slots = (Mara_Mem_Inst*)calloc(mem.cap, sizeof *mem.slots);
    if (!mem.slots) { fprintf(stderr, "memory profile: out of memory\n"); exit(1); }
    mem.used = 0;
    size_t mask = mem.cap - 1;
    for (size_t k = 0; k < old; k++) {
        if (slots[k].hdr == NULL || slots[k].hdr == TOMB) continue;
        size_t i = mem_hash(slots[k].hdr) & mask;
        while (mem.slots[i].hdr) i = (i + 1) & mask;
        mem.slots[i] = slots[k];
        mem.used++;
    }
    free(slots);
}

// A new instance at hdr, of site's record: one there before ends.
static void mem_begin(const Mara_List* hdr, Mara_Mem_Site* site) {
    Mara_Mem_Inst* s = mem_find(hdr);
    if (s) mem_end(s);
    if ((mem.used + 1) * 2 > mem.cap) mem_grow();
    size_t mask = mem.cap - 1;
    size_t i = mem_hash(hdr) & mask;
    while (mem.slots[i].hdr && mem.slots[i].hdr != TOMB) i = (i + 1) & mask;
    if (mem.slots[i].hdr == NULL) mem.used++;
    s = &mem.slots[i];
    s->hdr = hdr;
    s->data = (void*)(hdr + 1);
    s->cap = site->cap;
    s->rec = mem_rec(site);
    s->peak = hdr->len;
    mem.live++;
}

void __mara_mem_new(const Mara_List* hdr, Mara_Mem_Site* site) {
    if (site) mem_begin(hdr, site);
}

void __mara_mem_into(const Mara_List* hdr, Mara_Mem_Site* site) {
    Mara_Mem_Inst* s = mem_find(hdr);
    if (s && (!site || s->rec == mem_rec(site))) {
        if (hdr->len > s->peak) s->peak = hdr->len;
        return;
    }
    if (site) { mem_begin(hdr, site); return; }
    if (s) mem_end(s);   // (something else is there now)
}

void __mara_mem_len(const Mara_List* hdr) {
    mem.len_probes++;
    Mara_Mem_Inst* s = mem_find(hdr);
    if (!s) return;
    if (hdr->len > s->peak) s->peak = hdr->len;
}

void __mara_mem_arena(const char* kind, const Mara_Header* base) {
    for (size_t i = 0; i < mem.narenas; i++) {
        Mara_Mem_Arena* a = &mem.arenas[i];
        if (a->data == base->data) {
            if (base->len > a->peak) a->peak = base->len;
            return;
        }
    }
    if (mem.narenas == mem.caparenas) {
        mem.caparenas = mem.caparenas ? mem.caparenas * 2 : 8;
        mem.arenas = (Mara_Mem_Arena*)realloc(mem.arenas, mem.caparenas * sizeof *mem.arenas);
        if (!mem.arenas) { fprintf(stderr, "memory profile: out of memory\n"); exit(1); }
    }
    Mara_Mem_Arena* a = &mem.arenas[mem.narenas++];
    a->kind = kind ? kind : "arena";
    a->data = base->data;
    a->size = base->cap;
    a->peak = base->len;
}

static int64_t mem_unused(const Mara_Mem_Rec* r) {
    return (r->cap - r->peak) * r->elem;
}

static int mem_by_unused(const void* a, const void* b) {
    const Mara_Mem_Rec* x = *(Mara_Mem_Rec* const*)a;
    const Mara_Mem_Rec* y = *(Mara_Mem_Rec* const*)b;
    int64_t ux = mem_unused(x), uy = mem_unused(y);
    if (ux != uy) return ux < uy ? 1 : -1;
    return strcmp(x->name, y->name);
}

static void mem_exe_name(char* out, size_t cap) {
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

static void mem_dump(void) {
    // Every instance still there ends now.
    for (size_t i = 0; i < mem.cap; i++) {
        Mara_Mem_Inst* s = &mem.slots[i];
        if (s->hdr && s->hdr != TOMB) mem_end(s);
    }

    char path[MARA_PATH_CAP];
    size_t dir = __mara_exe_dir(path, sizeof path - 32);
    snprintf(path + dir, sizeof path - dir, "%s", MARA_MEM_FILE);
    FILE* out = fopen(path, "wb");
    if (!out) {
        fprintf(stderr, "memory profile: can't write %s\n", path);
        return;
    }
    char stamp[64] = "";
    time_t now = time(NULL);
    struct tm* tm = localtime(&now);
    if (tm) strftime(stamp, sizeof stamp, "%Y-%m-%d %H:%M:%S", tm);
    char exe[MARA_PATH_CAP];
    mem_exe_name(exe, sizeof exe);
    fprintf(out, "Mara memory profile: %s, %s, %s\n", exe, mem.build ? mem.build : "build unknown", stamp);
    fprintf(out, "Each partial array, by where its N is written (a local, a struct's field): how full any instance got.\n");
    fprintf(out, "Unused B: what each instance would save with N its peak. Median: of the instances' peaks, within about 3%%.\n");
    fprintf(out, "%llu len writes looked at.\n", (unsigned long long)mem.len_probes);
    fprintf(out, "\n");

    qsort(mem.recs, mem.nrecs, sizeof *mem.recs, mem_by_unused);
    int wname = 4;
    for (size_t i = 0; i < mem.nrecs; i++) {
        int n = (int)strlen(mem.recs[i]->name);
        if (n > wname) wname = n;
    }
    fprintf(out, "%12s %12s %10s %10s %10s %8s %10s  %-*s  %s\n",
            "unused B", "reserved B", "peak", "median", "cap", "elem B", "instances", wname, "name", "where");
    for (size_t i = 0; i < mem.nrecs; i++) {
        Mara_Mem_Rec* r = mem.recs[i];
        fprintf(out, "%12lld %12lld %10lld %10lld %10lld %8lld %10llu  %-*s  %s\n",
                (long long)mem_unused(r), (long long)(r->cap * r->elem), (long long)r->peak,
                (long long)mem_median(r), (long long)r->cap, (long long)r->elem,
                (unsigned long long)r->instances, wname, r->name, r->where);
    }
    if (mem.narenas) {
        fprintf(out, "\n%12s %12s %8s  %s\n", "size B", "peak B", "peak %", "arena");
        for (size_t i = 0; i < mem.narenas; i++) {
            Mara_Mem_Arena* a = &mem.arenas[i];
            double pct = a->size ? (double)a->peak * 100.0 / (double)a->size : 0;
            fprintf(out, "%12lld %12lld %8.2f  %s\n", (long long)a->size, (long long)a->peak, pct, a->kind);
        }
    }
    fclose(out);
    fflush(stdout);   // (the program's output first)
    fprintf(stderr, "memory profile: %s\n", path);
}
