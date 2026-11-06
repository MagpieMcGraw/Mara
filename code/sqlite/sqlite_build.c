// SQLite as Mara builds it: `foreign static_lib "sqlite_build"` in sqlite.mara makes
// a static library from this file the first time it's linked. sqlite3.c and
// sqlite3.h are SQLite's amalgamation, version 3.54.1, unchanged (public domain).

// Full-text search, which `CREATE VIRTUAL TABLE ... USING fts5` needs.
#define SQLITE_ENABLE_FTS5 1

// A connection is one thread's, so it needs no lock of its own. Threads share a
// database by each opening a connection to it.
#define SQLITE_THREADSAFE 2

// SQLite's recommended options for speed, from its "compile options" page.
#define SQLITE_DEFAULT_MEMSTATUS 0
#define SQLITE_LIKE_DOESNT_MATCH_BLOBS 1
#define SQLITE_USE_ALLOCA 1
#define SQLITE_OMIT_DEPRECATED 1
#define SQLITE_OMIT_SHARED_CACHE 1

// No extensions loaded from files at run time.
#define SQLITE_OMIT_LOAD_EXTENSION 1

#include "sqlite3.c"
