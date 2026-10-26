// Error return traces — linked into every native build.
//
// An err is 64 bits: its kind low (its error set's id << 16 | its tag), and
// above it the id of its trace here. A trace is where the err was made, then
// each `?` (or `return …, e`) that passed it on, one site each — the site an
// atom, an id into the program's table of text, "lexer.mara:12:37 in digit".
// e.where() reads the first, e.trace() all of them.
//
// The traces are a ring: the newest MARA_ERR_TRACES errs keep theirs. Each
// slot holds its trace's id, so an err kept past its slot's reuse finds a
// newer one there and says its trace is gone, rather than showing another's.
// A trace past MARA_ERR_SITES keeps its first sites and its last.
//
// The compiler calls these where errs are made and passed on (llvm.odin,
// llvm_err_runtime); nothing else does. One ring for the program: Mara runs
// one thread.

#include <stdint.h>
#include <string.h>

#define MARA_ERR_TRACES 64
#define MARA_ERR_SITES  16

typedef struct {
    uint32_t id;                      // its trace's id; 0: none yet
    uint32_t len;                     // how many sites it has
    uint32_t sites[MARA_ERR_SITES];   // where it was made, then each pass
} Mara_Err_Trace;

static Mara_Err_Trace traces[MARA_ERR_TRACES];
static uint32_t last_id;

// The trace an err's id names, while its slot still holds it; else none.
static Mara_Err_Trace *trace_of(uint64_t e) {
    uint32_t id = (uint32_t)(e >> 32);
    if (id == 0) return NULL;
    Mara_Err_Trace *t = &traces[id % MARA_ERR_TRACES];
    return t->id == id ? t : NULL;
}

// An err of kind `kind` made at `site`: a new trace, the err its kind with
// the trace's id above it.
uint64_t __mara_err_made(uint64_t kind, uint32_t site) {
    uint32_t id = ++last_id;
    if (id == 0) id = ++last_id;   // (0 is no trace)
    Mara_Err_Trace *t = &traces[id % MARA_ERR_TRACES];
    t->id = id;
    t->len = 1;
    t->sites[0] = site;
    return (kind & 0xFFFFFFFFu) | ((uint64_t)id << 32);
}

// An err passed on at `site`: the site added to its trace (past its room,
// the last one replaced). Ok passes as it is; a failure with no trace — its
// kind made where none was noted — starts one here.
uint64_t __mara_err_passed(uint64_t e, uint32_t site) {
    if ((e & 0xFFFFFFFFu) == 0) return e;
    if ((uint32_t)(e >> 32) == 0) return __mara_err_made(e, site);
    Mara_Err_Trace *t = trace_of(e);
    if (t == NULL) return e;   // (its trace is gone: newer errs have its slot)
    if (t->len < MARA_ERR_SITES) {
        t->sites[t->len++] = site;
    } else {
        t->sites[MARA_ERR_SITES - 1] = site;
    }
    return e;
}

// Where an err was made: its trace's first site — `none` for an err with no
// trace (Ok), `gone` for one whose trace newer errs have taken the place of.
uint32_t __mara_err_where(uint64_t e, uint32_t none, uint32_t gone) {
    if ((uint32_t)(e >> 32) == 0) return none;
    Mara_Err_Trace *t = trace_of(e);
    return t != NULL ? t->sites[0] : gone;
}

// An err's trace's sites copied into `out` (room for MARA_ERR_SITES):
// how many — 0 for none, or one gone.
int64_t __mara_err_trace(uint64_t e, uint32_t *out) {
    Mara_Err_Trace *t = trace_of(e);
    if (t == NULL) return 0;
    memcpy(out, t->sites, t->len * sizeof(uint32_t));
    return t->len;
}
