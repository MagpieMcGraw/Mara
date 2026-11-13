package mara

import "core:c/libc"
import "core:fmt"
import "core:os"
import "core:strings"

// ---------------------------------------------------------------------------
// `mara edit [module] <prefix>.use [name]`: how a module's uses of another
// name it, changed — the use's line, and every name of the used module's
// written in that file with it.
//
//   gl.use other      `gl :: use m` becomes `other :: use m`: gl.X, other.X
//   gl.use            ... `use m`: gl.X is X — or stays m's own name's, m.X,
//                     where X by itself means something else there
//   open_gl.use gl    `use mara.open_gl` becomes `gl :: use mara.open_gl`:
//                     X and open_gl.X are gl.X, v.f(a) calling its f is
//                     gl.f(v, a)
//
// What a name means is the name table's answer and the checker's (the call a
// method call makes, a bare variant's enum). The module is checked again
// with the files written; one that doesn't check gets them back as they were.
// ---------------------------------------------------------------------------

// A use of the module's to change: its Import, its name's token (the alias,
// else its path's last part), the module it uses.
@(private="file")
Edit_Use :: struct {
    imp:   Tree_Id,
    alias: Token_Id,
    tok:   Token_Id,
    used:  ^Scope,
}

edit_use :: proc(checked: ^Checked_Program, module, prefix: string, to: []string) -> (said: string, ok: bool) {
    r, t, a := checked.names, &build_tree, checked.annot
    if len(to) > 1 { return "mara edit: <prefix>.use takes the new name, or none: the module's names by themselves\n", false }
    name := to[0] if len(to) == 1 else ""
    for c, i in name {
        if !(c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || i > 0 && c >= '0' && c <= '9') {
            return fmt.tprintf("mara edit: '%s' isn't a name\n", name), false
        }
    }
    uses := make([dynamic]Edit_Use)
    for u in names_module_uses(r, module) {
        parts := tree_token_list(t, t.a[u.imp])
        if len(parts) == 0 { continue }
        tok := u.alias if u.alias != 0 else parts[len(parts) - 1]
        used := r.named[tok] or_else nil   // (nil: a struct's or a fun's)
        if used == nil || tc_text(tok) != prefix && !(u.alias == 0 && used.name == prefix) { continue }
        append(&uses, Edit_Use{u.imp, u.alias, tok, used})
    }
    if len(uses) == 0 { return fmt.tprintf("mara edit: no use in %s names a module %s\n", module, prefix), false }

    // (The call each call node makes, as checked: any instance's.)
    callee := make(map[Tree_Id]^Type_Scope)
    for key, ts in a.callees {
        _, n := annot_split(key)
        if n not_in callee { callee[n] = ts }
    }
    edits := make([dynamic]Order_Edit)
    names, kept := 0, 0
    // Nothing of the new name may be in sight where it's written.
    free :: proc(r: ^Name_Table, name: string, at: Token_Id) -> string {
        _, found, miss := names_find(r, name, at)
        if !found && len(miss.owners) == 0 && miss.hidden == "" { return "" }
        return fmt.tprintf("mara edit: '%s' means something already at %s\n", name, token_location(build_tokens[at]))
    }
    // (A token's text made another; the text from one token up to another
    // cut; text put before a token.)
    swap :: proc(edits: ^[dynamic]Order_Edit, tok: Token_Id, text: string) {
        a := build_tokens[tok]
        append(edits, Order_Edit{a.file, int(a.offset), int(a.offset + a.len), text})
    }
    cut :: proc(edits: ^[dynamic]Order_Edit, from, to: Token_Id) {
        a, b := build_tokens[from], build_tokens[to]
        append(edits, Order_Edit{a.file, int(a.offset), int(b.offset), ""})
    }
    insert :: proc(edits: ^[dynamic]Order_Edit, tok: Token_Id, text: string) {
        a := build_tokens[tok]
        append(edits, Order_Edit{a.file, int(a.offset), int(a.offset), text})
    }
    for u in uses {
        cur := tc_text(u.tok)
        last := u.used.name[strings.last_index_byte(u.used.name, '.') + 1:]
        if name == "" && u.alias == 0 { return fmt.tprintf("%s's names are by themselves in %s already.\n", u.used.name, build_files[build_tokens[u.tok].file].path), true }
        if name == cur { return fmt.tprintf("%s goes by %s already.\n", u.used.name, name), true }
        if name != "" { if problem := free(r, name, u.tok); problem != "" { return problem, false } }
        sf := build_files[build_tokens[u.tok].file]

        // The names written through it: `cur.X`, cur the use's name there.
        for i in sf.first_token ..< sf.end_token {
            if build_tokens[i].kind != .Identifier || i == u.tok || tc_text(i) != cur || i + 2 >= sf.end_token { continue }
            if build_tokens[i + 1].kind != .Dot || build_tokens[i + 2].kind != .Identifier || build_tokens[i - 1].kind == .Dot { continue }
            if ref, found, _ := names_find(r, cur, i); !found || ref.decl != u.tok { continue }
            names += 1
            if name != "" {
                if problem := free(r, name, i); problem != "" { return problem, false }
                swap(&edits, i, name)
                continue
            }
            // (By itself, when that means nothing else there; else through
            // the module's own name, which the plain use declares.)
            _, found, miss := names_find(r, tc_text(i + 2), i)
            if !found && len(miss.owners) == 0 && miss.hidden == "" {
                cut(&edits, i, i + 2)
            } else {
                if problem := free(r, last, i); problem != "" { return problem, false }
                swap(&edits, i, last)
                kept += 1
            }
        }

        // A plain use given a name: the module's names written by themselves
        // — a definition's, a call its group or its fun answers, a variant
        // of its enums — and the method calls that call its funs.
        if name != "" && u.alias == 0 {
            mine :: proc(used: ^Scope, decl: Token_Id) -> bool {
                return decl != 0 && build_files[build_tokens[decl].file].module == used.name
            }
            variant := make(map[Tree_Id]bool, allocator = context.temp_allocator)
            lo, hi := tree_file_nodes(t, build_tokens[u.tok].file)
            for inst, i in a.instances {
                for n in max(lo, inst.lo) ..= min(hi, inst.hi) {
                    if ref := a.refs[i][n - inst.lo]; ref.kind == .Variant && t.tag[n] == .Ident {
                        if v, has := u.used.variants[tc_text(t.main[n])]; has && v.decl == ref.decl { variant[n] = true }
                    }
                }
            }
            for n in lo ..= hi {
                tok: Token_Id
                ref := r.refs[n]
                #partial switch t.tag[n] {
                case .Ident, .Call, .Type_Generic:
                    tok = t.main[n]
                case .Type_Name:
                    parts := tree_token_list(t, t.a[n])
                    if len(parts) == 0 { continue }
                    tok = parts[0]
                    if len(parts) > 1 { ref = r.token_refs[tok] or_else Ref{} }
                case .Method_Call:
                    // (`v.f(a)` calling the module's f: `name.f(v, a)`.)
                    mv := method_view(t, n)
                    ts := callee[n] or_else nil
                    d, has := u.used.defs[tc_text(mv.name)]
                    if q := r.refs[mv.receiver]; ts == nil || !has || q.kind == .Module || q.kind == .Type { continue }
                    if !(d.decl == ts.decl || r.dispatches[d.decl] && mine(u.used, ts.decl)) || build_tokens[mv.name + 1].kind != .Left_Paren { continue }
                    if problem := free(r, name, t.first[mv.receiver]); problem != "" { return problem, false }
                    first, end := build_tokens[t.first[mv.receiver]], build_tokens[t.end[mv.receiver] - 1]
                    paren := build_tokens[mv.name + 1]
                    append(&edits, Order_Edit{first.file, int(first.offset), int(first.offset), fmt.tprintf("%s.%s(", name, tc_text(mv.name))})
                    append(&edits, Order_Edit{first.file, int(end.offset + end.len), int(paren.offset + 1), ", " if len(mv.args) > 0 else ""})
                    names += 1
                    continue
                case: continue
                }
                if tok == 0 || build_tokens[tok - 1].kind == .Dot { continue }
                d, has := u.used.defs[tc_text(tok)]
                is_def := has && ref.decl == d.decl
                // (A call a dispatch group of several modules answers: the fun called is the module's.)
                is_call := t.tag[n] == .Call && ref.kind == .None && has && callee[n] != nil && mine(u.used, callee[n].decl)
                if !is_def && !is_call && !variant[n] { continue }
                if problem := free(r, name, tok); problem != "" { return problem, false }
                insert(&edits, tok, strings.concatenate({name, "."}))
                names += 1
            }
        }

        // The use's line.
        kw := t.main[u.imp]
        switch {
        case name == "":   cut(&edits, u.alias, kw)
        case u.alias != 0: swap(&edits, u.alias, name)
        case:              insert(&edits, kw, strings.concatenate({name, " :: "}))
        }
    }

    written, failed := edit_apply(edits[:])
    if failed != "" { return failed, false }
    if !edit_checks(module) {
        for e in edits { _ = os.write_entire_file(build_files[e.file].path, transmute([]byte)build_files[e.file].source) }
        return fmt.tprintf("mara edit: %s doesn't check with that (above): its files are as they were\n", module), false
    }
    b := strings.builder_make()
    used := uses[0].used.name
    switch {
    case name == "":
        fmt.sbprintf(&b, "%s's names are by themselves now: %d of them", used, names - kept)
        if kept > 0 { fmt.sbprintf(&b, ", and %d kept through %s, where the name alone means something else", kept, used[strings.last_index_byte(used, '.') + 1:]) }
    case:
        fmt.sbprintf(&b, "%s goes by %s now: %d of its names", used, name, names)
    }
    fmt.sbprintf(&b, " (%s)\n", strings.join(written, ", "))
    return strings.to_string(b), true
}

// Whether the module checks, as its files are now: this compiler run again
// up to the check's end (MARA_CHECK_ONLY). What it says is printed when it
// doesn't.
@(private="file")
edit_checks :: proc(module: string) -> bool {
    out := fmt.tprintf("%s.edit_check.txt", module)
    defer os.remove(out)
    os.set_env("MARA_CHECK_ONLY", "1")
    cmd := fmt.tprintf(`"%s" build %s > "%s" 2>&1`, os.args[0], module, out)
    when ODIN_OS == .Windows { cmd = strings.concatenate({`"`, cmd, `"`}) }
    if libc.system(strings.clone_to_cstring(cmd)) == 0 { return true }
    if said, err := os.read_entire_file(out, context.temp_allocator); err == nil { fmt.print(string(said)) }
    return false
}
