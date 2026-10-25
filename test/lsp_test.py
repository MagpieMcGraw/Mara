"""mara lsp, driven as an editor drives it: started, initialized, a file
opened, then hover, definition, references and document symbols asked;
edits made and not saved — an error typed, then taken away — and each
check's diagnostics read; then shut down. Run from the repo:
    python test/lsp_test.py
Prints each check and "LSP: all good", or what went wrong (exit 1)."""

import json
import os
import subprocess
import sys
import threading
import queue

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MARA = os.environ.get("MARA_EXE") or os.path.join(ROOT, "mara_dev.exe" if os.name == "nt" else "mara_dev")   # (the debug build)
POUNCE = os.path.join(ROOT, "Pounce")
CAMERA = os.path.join(POUNCE, "camera.mara")
FIELDS = os.path.join(ROOT, "test", "lsp_fields", "fields.mara")   # (moved_fields)
FUNS = os.path.join(ROOT, "test", "lsp_fields", "funs.mara")       # (moved_results_params)
CALLS = os.path.join(ROOT, "test", "lsp_fields", "calls.mara")     # (new_call_put_right)
VARIANTS = os.path.join(ROOT, "test", "lsp_fields", "variants.mara")   # (variants_completed)
SHAPES = os.path.join(ROOT, "test", "edit_shapes", "shapes.mara")  # (fun_calls)


def uri(path):
    p = path.replace("\\", "/")
    return "file:///" + p.lstrip("/")


class Client:
    def __init__(self, options=None, utf8=True):
        self.notes = []   # what came while waiting for an answer
        self.p = subprocess.Popen([MARA, "lsp"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, cwd=ROOT)
        self.inbox = queue.Queue()
        threading.Thread(target=self._read, daemon=True).start()
        self.next_id = 0
        caps = {"general": {"positionEncodings": ["utf-8", "utf-16"] if utf8 else ["utf-16"]}}
        self.init = self.request("initialize", {"processId": None, "rootUri": uri(ROOT), "capabilities": caps,
                                                "initializationOptions": options or {}})
        self.notify("initialized", {})

    def _read(self):
        out = self.p.stdout
        while True:
            length = None
            while True:
                line = out.readline()
                if not line:
                    return
                line = line.strip()
                if not line:
                    break
                if line.lower().startswith(b"content-length:"):
                    length = int(line.split(b":")[1])
            self.inbox.put(json.loads(out.read(length)))

    def send(self, msg):
        body = json.dumps(msg).encode("utf-8")
        self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.p.stdin.flush()

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params):
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": self.next_id, "method": method, "params": params})
        while True:
            msg = self.inbox.get(timeout=30)
            if msg.get("id") == self.next_id:
                if "error" in msg:
                    raise RuntimeError(msg["error"])
                return msg["result"]
            self.notes.append(msg)

    def diagnostics_for(self, path, timeout=30):
        """The next diagnostics published for the path."""
        want = uri(path).lower()
        for i, n in enumerate(self.notes):
            if n.get("method") == "textDocument/publishDiagnostics" and n["params"]["uri"].lower() == want:
                del self.notes[i]
                return n["params"]["diagnostics"]
        while True:
            msg = self.inbox.get(timeout=timeout)
            if msg.get("method") == "textDocument/publishDiagnostics" and msg["params"]["uri"].lower() == want:
                return msg["params"]["diagnostics"]
            self.notes.append(msg)

    def close(self):
        self.request("shutdown", None)
        self.notify("exit", None)
        return self.p.wait(timeout=30)


bad = []


def check(what, ok, got):
    print(("ok   " if ok else "FAIL ") + what + ("" if ok else "\n     got: " + json.dumps(got)[:600]))
    if not ok:
        bad.append(what)


def pos(text, line_no, needle, nth=0):
    """0-based line and character (UTF-8 bytes) of `needle` on 1-based line."""
    line = text.split("\n")[line_no - 1]
    at = -1
    for _ in range(nth + 1):
        at = line.index(needle, at + 1)
    return {"line": line_no - 1, "character": len(line[:at].encode("utf-8"))}


def apply(text, edits):
    """Text edits (UTF-8 byte positions) made to a text, last first."""
    lines = text.split("\n")
    for e in sorted(edits, key=lambda e: (e["range"]["start"]["line"], e["range"]["start"]["character"]), reverse=True):
        r = e["range"]
        start = sum(len(l.encode("utf-8")) + 1 for l in lines[:r["start"]["line"]]) + r["start"]["character"]
        end = sum(len(l.encode("utf-8")) + 1 for l in lines[:r["end"]["line"]]) + r["end"]["character"]
        raw = "\n".join(lines).encode("utf-8")
        lines = (raw[:start] + e["newText"].encode("utf-8") + raw[end:]).decode("utf-8").split("\n")
    return "\n".join(lines)


def moved_fields(c):
    """A struct's field moved: its positional literals said to be in the old
    order — even where they still check — and put in the new one, or the
    field put back, by a code action."""
    text = open(FIELDS, encoding="utf-8", newline="").read()
    doc = {"uri": uri(FIELDS)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(FIELDS), "languageId": "mara", "version": 1, "text": text}})
    check("fields: opened, no errors", c.diagnostics_for(FIELDS) == [], None)
    version = 1

    def edit(new):
        nonlocal version
        version += 1
        c.notify("textDocument/didChange", {"textDocument": {"uri": uri(FIELDS), "version": version}, "contentChanges": [{"text": new}]})
        return c.diagnostics_for(FIELDS)

    def actions_at(line_no):
        r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": line_no - 1, "character": 0},
                      "end": {"line": line_no - 1, "character": 0}}, "context": {"diagnostics": []}})
        return {a["title"]: a for a in r or []}

    nl = "\r\n" if "\r\n" in text else "\n"
    kind_line = "\tkind : i64" + nl
    group_line = "\tfile, offset, len : i64" + nl
    struct_line = 1 + next(i for i, l in enumerate(text.split("\n")) if l.startswith("Token :: class"))

    def order_said(diags):
        return [d["message"] for d in diags if "reordered" in d["message"]]

    # kind moved to the end the way an editor does it: cut, then pasted.
    cut = text.replace(kind_line, "", 1)
    moved = cut.replace(group_line, group_line + kind_line, 1)
    edit(cut)
    said = order_said(edit(moved))
    check("fields: kind moved, the two positional literals said to be in the old order (they still check)",
          sum("this literal still gives them in the old order (kind, file, offset, len)" in m for m in said) == 2
          and sum("2 literals still use the old order" in m for m in said) == 1 and len(said) == 3, said)
    acts = actions_at(struct_line)
    put = acts.get("Put the 2 Token literals in the new order (file, offset, len, kind)")
    back = acts.get("Put Token's fields back in the old order (kind, file, offset, len)")
    check("fields: at the struct, reorder the literals or put the fields back", put is not None and back is not None, list(acts))
    edits = put and [e for es in put["edit"]["changes"].values() for e in es] or []
    fixed = apply(moved, edits)
    check("fields: the literals reordered, the named one left", "Token{0, 10, 2, 1}" in fixed and "Token{0, 20, 3, 2}" in fixed
          and "Token{kind = 3, file = 0, offset = 30, len = 4}" in fixed, fixed)
    check("fields: reordered, nothing said", edit(fixed) == [], None)
    check("fields: nothing more offered", actions_at(struct_line) == {}, list(actions_at(struct_line)))

    # Undone a step at a time: the literals back (wrong for the struct now:
    # said), then the field back (right again: nothing said).
    check("fields: the fix undone, the literals said again", len(order_said(edit(moved))) == 3, None)
    check("fields: the move undone too, nothing said", edit(text) == [], None)

    # Moved again, then put back by the other action.
    edit(cut)
    edit(moved)
    acts = actions_at(struct_line)
    back = acts.get("Put Token's fields back in the old order (kind, file, offset, len)")
    restored = apply(moved, back and [e for es in back["edit"]["changes"].values() for e in es] or [])
    check("fields: put back, as it was", restored == text, restored)
    check("fields: put back, nothing said", edit(restored) == [], None)

    # Typed at the end, a key at a time, after the line was cut.
    edit(cut)
    typing = ""
    for ch in "\tkind : i64":
        typing += ch
        edit(cut.replace(group_line, group_line + typing + nl, 1))
    check("fields: typed in its new place, the literals said", len(order_said(edit(moved))) == 3, None)
    check("fields: and back", edit(text) == [], None)

    # A field renamed in place: its literals fit still; then moved, said.
    renamed = text.replace(kind_line, "\tkin : i64" + nl, 1)
    check("fields: a field renamed, nothing said", order_said(edit(renamed)) == [], None)
    moved_renamed = renamed.replace("\tkin : i64" + nl, "", 1).replace(group_line, group_line + "\tkin : i64" + nl, 1)
    said = order_said(edit(moved_renamed))
    check("fields: the renamed field moved, said in its name", len(said) == 3 and "(kin, file, offset, len)" in said[0], said)
    edit(text)
    c.notify("textDocument/didClose", {"textDocument": doc})


def moved_results_params(c):
    """A fun's results swapped: its returns and destructures said and put in
    the new order; then its params, its calls."""
    text = open(FUNS, encoding="utf-8", newline="").read()
    doc = {"uri": uri(FUNS)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(FUNS), "languageId": "mara", "version": 1, "text": text}})
    check("results: opened, no errors", c.diagnostics_for(FUNS) == [], None)
    version = 1

    def edit(new):
        nonlocal version
        version += 1
        c.notify("textDocument/didChange", {"textDocument": {"uri": uri(FUNS), "version": version}, "contentChanges": [{"text": new}]})
        return [d["message"] for d in c.diagnostics_for(FUNS) if "reordered" in d["message"]]

    def actions_at(line_no):
        r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": line_no - 1, "character": 0},
                      "end": {"line": line_no - 1, "character": 0}}, "context": {"diagnostics": []}})
        return {a["title"]: a for a in r or []}

    fun_line = 1 + next(i for i, l in enumerate(text.split("\n")) if l.startswith("span :: fun"))
    swapped = text.replace("-> i64, bool {", "-> bool, i64 {", 1)
    said = edit(swapped)
    check("results: swapped, the returns and destructures said", len(said) == 5
          and sum("this return still gives them in the old order (i64, bool)" in m for m in said) == 2
          and sum("this destructure still names them in the old order (i64, bool)" in m for m in said) == 2, said)
    acts = actions_at(fun_line)
    put = acts.get("Put the 4 places using span's results in the new order (bool, i64)")
    check("results: the action, and putting them back", put is not None and "Put span's results back in the old order (i64, bool)" in acts, list(acts))
    fixed = apply(swapped, put and [e for es in put["edit"]["changes"].values() for e in es] or [])
    check("results: returns and destructures swapped", "return false, 0" in fixed and "return true, at + len" in fixed
          and "ok, end := span(3, 4)" in fixed and "fine, more := span(10, 0)" in fixed, fixed)
    check("results: then nothing said", edit(fixed) == [], None)

    params = fixed.replace("span :: fun(at: i64, len: i64)", "span :: fun(len: i64, at: i64)", 1)
    said = edit(params)
    check("params: swapped, the calls said", len(said) == 3
          and sum("this call still passes them in the old order (at, len)" in m for m in said) == 2, said)
    put = actions_at(fun_line).get("Put the 2 calls of span in the new order (len, at)")
    called = apply(params, put and [e for es in put["edit"]["changes"].values() for e in es] or [])
    check("params: the calls' arguments swapped", "span(4, 3)" in called and "span(0, 10)" in called, called)
    check("params: then nothing said", edit(called) == [], None)
    edit(text)
    c.notify("textDocument/didClose", {"textDocument": doc})


def new_call_put_right(c):
    """A new call written with its arguments the wrong way round, a type
    error there, then swapped by hand: it's taken as written once it checks,
    not as it was first written — nothing said, no action to swap it back."""
    text = open(CALLS, encoding="utf-8", newline="").read()
    doc = {"uri": uri(CALLS)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(CALLS), "languageId": "mara", "version": 1, "text": text}})
    check("new call: opened, no errors", c.diagnostics_for(CALLS) == [], None)
    version = 1

    def edit(new):
        nonlocal version
        version += 1
        c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CALLS), "version": version}, "contentChanges": [{"text": new}]})
        return [d["message"] for d in c.diagnostics_for(CALLS)]

    wrong = text.replace("\treturn 0", "\treturn find(\"a,b\", ',')", 1)
    said = edit(wrong)
    check("new call: written the wrong way round, a type error, no order said",
          any("parameter 'char' expects utf8" in m for m in said) and not any("reordered" in m for m in said), said)
    right = text.replace("\treturn 0", "\treturn find(',', \"a,b\")", 1)
    said = edit(right)
    check("new call: swapped by hand, nothing said", said == [], said)
    call_line = 1 + next(i for i, l in enumerate(right.split("\n")) if "return find(" in l)
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": call_line - 1, "character": 0},
                  "end": {"line": call_line - 1, "character": 0}}, "context": {"diagnostics": []}})
    titles = [a["title"] for a in r or [] if a.get("kind") != "refactor"]
    check("new call: no action to swap it back", titles == [], titles)
    edit(text)
    c.notify("textDocument/didClose", {"textDocument": doc})


def variants_completed(c):
    """A name completed where a type with variants goes — a fun's return, its
    result a Token_Kind: the type's variants offered, though no variant is a
    name in sight by itself (the checker finds a bare one, not the resolver)."""
    text = open(VARIANTS, encoding="utf-8", newline="").read()
    doc = {"uri": uri(VARIANTS)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(VARIANTS), "languageId": "mara", "version": 1, "text": text}})
    check("variants: opened, no errors", c.diagnostics_for(VARIANTS) == [], None)
    edited = text.replace("\treturn Mystery", "\treturn Na", 1)
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(VARIANTS), "version": 2}, "contentChanges": [{"text": edited}]})
    lines = edited.split("\n")
    line_no = next(i for i, l in enumerate(lines) if "return Na" in l)
    at = lines[line_no].index("return Na") + len("return Na")
    r = c.request("textDocument/completion", {"textDocument": doc, "position": {"line": line_no, "character": at}})
    items = {i["label"]: i for i in (r or {}).get("items", [])}
    check("variants: a return's, its result type's", {"Mystery", "Name", "Number"} <= set(items)
          and items["Name"]["kind"] == 20, sorted(items)[:30])
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(VARIANTS), "version": 3}, "contentChanges": [{"text": text}]})
    c.notify("textDocument/didClose", {"textDocument": doc})


def fun_calls(c):
    """At a fun's name, asked: the fun called where its body is written out."""
    text = open(SHAPES, encoding="utf-8", newline="").read()
    doc = {"uri": uri(SHAPES)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(SHAPES), "languageId": "mara", "version": 1, "text": text}})
    c.diagnostics_for(SHAPES)
    line = next(i for i, l in enumerate(text.split("\n")) if l.startswith("emit :: fun"))
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": line, "character": 0},
                  "end": {"line": line, "character": 0}}, "context": {"diagnostics": []}})
    acts = {a["title"]: a for a in r or []}
    act = acts.get("Call emit in the 2 places its body is written out")
    check("calls: offered at the fun's name", act is not None, list(acts))
    done = apply(text, act and [e for es in act["edit"]["changes"].values() for e in es] or [])
    check("calls: the two places its call", done.replace("\r", "").count("return emit(l, 1, ") == 2 and "skip(l)" in done, done)
    other = next(i for i, l in enumerate(text.split("\n")) if l.startswith("next :: fun"))
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": other, "character": 0},
                  "end": {"line": other, "character": 0}}, "context": {"diagnostics": []}})
    check("calls: nothing at a fun whose body isn't written out elsewhere", not any(a["title"].startswith("Call ") for a in r or []), r)

    # One-statement ifs with do: at the if, at its fun's name.
    lines = text.split("\n")
    at_name = next(i for i, l in enumerate(lines) if l.startswith("kind_of :: fun"))
    at_if = next(i for i, l in enumerate(lines) if i > at_name and l.strip() == "if c == '+' {")
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": at_if, "character": 0},
                  "end": {"line": at_if, "character": 0}}, "context": {"diagnostics": []}})
    acts = {a["title"]: a for a in r or []}
    one = acts.get("Write this if with do")
    done = apply(text, one and [e for es in one["edit"]["changes"].values() for e in es] or []).replace("\r", "")
    check("do: at the if, it written with do", "\tif c == '+' do return 1\n\telif c == '-' do return 2\n" in done, list(acts))
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": at_name, "character": 0},
                  "end": {"line": at_name, "character": 0}}, "context": {"diagnostics": []}})
    check("do: at the fun's name, all of its", any(a["title"] == "Write kind_of's 1 if with do" for a in r or []), r)

    # Ifs joined with elif: at one, its run; over a selection, the ones in it.
    first_if = next(i for i, l in enumerate(lines) if l.strip() == "if n < 0 {")
    second_if = next(i for i, l in enumerate(lines) if l.strip() == "if n == 0 {")
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": first_if, "character": 0},
                  "end": {"line": first_if, "character": 0}}, "context": {"diagnostics": []}})
    check("elif: at an if, its run of three", any(a["title"] == "Join these 3 ifs into one chain with elif" for a in r or []), [a["title"] for a in r or []])
    r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": first_if, "character": 0},
                  "end": {"line": second_if, "character": 3}}, "context": {"diagnostics": []}})
    two = next((a for a in r or [] if a["title"] == "Join the 2 selected ifs into one chain with elif"), None)
    done = apply(text, two and [e for es in two["edit"]["changes"].values() for e in es] or []).replace("\r", "")
    check("elif: a selection of two, those two", "\telif n == 0\n\t\treturn 0\n\t}\n\tif n > 100 {" in done, [a["title"] for a in r or []])
    c.notify("textDocument/didClose", {"textDocument": doc})


def main():
    text = open(CAMERA, encoding="utf-8", newline="").read()
    c = Client()
    caps = c.init["capabilities"]
    check("initialize: utf-8, full sync, the four answers", caps.get("positionEncoding") == "utf-8"
          and caps["textDocumentSync"]["change"] == 1 and caps["hoverProvider"] and caps["definitionProvider"]
          and caps["referencesProvider"] and caps["documentSymbolProvider"], caps)

    doc = {"uri": uri(CAMERA)}
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(CAMERA), "languageId": "mara", "version": 1, "text": text}})
    diags = c.diagnostics_for(CAMERA)
    check("opened: camera.mara has no errors", diags == [], diags)

    h = c.request("textDocument/hover", {"textDocument": doc, "position": pos(text, 52, "obj", 1)})
    value = h and h["contents"]["value"] or ""
    check("hover on obj: a field, an Object", "obj — field : Object" in value and "camera.mara:11" in value, h)

    d = c.request("textDocument/definition", {"textDocument": doc, "position": pos(text, 52, "obj_get_directions")})
    check("definition of obj_get_directions: object.mara:21", isinstance(d, dict) and d["uri"].lower().endswith("/object.mara")
          and d["range"]["start"]["line"] == 20, d)

    r = c.request("textDocument/references", {"textDocument": doc, "position": pos(text, 48, "camera_move"),
                                               "context": {"includeDeclaration": True}})
    files = sorted({x["uri"].rsplit("/", 1)[1] for x in r or []})
    check("references to camera_move: its declaration and its call", r is not None and len(r) >= 2
          and "camera.mara" in files and "Pounce.mara" in files, r)

    syms = c.request("textDocument/documentSymbol", {"textDocument": doc})
    names = {s["name"]: s["kind"] for s in syms or []}
    check("symbols: Camera a struct, camera_move a function", names.get("Camera") == 23 and names.get("camera_move") == 12, syms)

    # An error typed, not saved: the check reads the editor's text.
    broken = text.replace("\tspeed: f32 = 500", "\tspeed: f32 = no_such_name", 1)
    check("(the test's edit applies)", broken != text, None)
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": 2}, "contentChanges": [{"text": broken}]})
    diags = c.diagnostics_for(CAMERA)
    line = broken.split("\n").index(next(l for l in broken.split("\n") if "no_such_name" in l))
    check("unsaved error: reported on its line", any(x["range"]["start"]["line"] == line and x["severity"] == 1 for x in diags), diags)

    # A line added above, unsaved: hover still finds what's under the point.
    shifted = "// a line the disk hasn't got\n" + text
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": 3}, "contentChanges": [{"text": shifted}]})
    diags = c.diagnostics_for(CAMERA)
    check("error taken away: none", diags == [], diags)
    h = c.request("textDocument/hover", {"textDocument": doc, "position": pos(shifted, 53, "obj", 1)})
    value = h and h["contents"]["value"] or ""
    check("hover after an unsaved line above: still obj", "obj — field : Object" in value, h)

    h = c.request("textDocument/hover", {"textDocument": doc, "position": {"line": 0, "character": 0}})
    check("hover in a comment: nothing", h is None, h)

    # Completion, each in an unsaved edit that doesn't parse as it stands.
    def complete(edited, line_no, before):
        """Items offered on 1-based line `line_no`, just after `before` there."""
        c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": 9}, "contentChanges": [{"text": edited}]})
        line = edited.split("\n")[line_no - 1]
        at = line.index(before) + len(before)
        r = c.request("textDocument/completion", {"textDocument": doc, "position": {"line": line_no - 1, "character": len(line[:at].encode("utf-8"))}})
        return {i["label"]: i for i in (r or {}).get("items", [])}

    member = text.replace("obj_get_directions(camera.obj.dir)", "obj_get_directions(camera.)", 1)
    items = complete(member, 52, "camera.")
    check("completion after camera.: Camera's fields, its method", {"obj", "proj", "fov_y", "view_and_projections"} <= set(items)
          and items["obj"]["kind"] == 5 and items["view_and_projections"]["kind"] == 2, sorted(items)[:30])

    name = text.replace("\tfwd, up, right := obj_get_directions(camera.obj.dir)", "\tfwd, up, right := obj_get_directions(camera.obj.dir)\n\tcam", 1)
    items = complete(name, 53, "\tcam")
    check("completion of a name: the param, the fun, a local before, keywords", {"camera", "camera_move", "fwd", "return"} <= set(items)
          and items["camera"]["kind"] == 6 and items["camera_move"]["kind"] == 3, sorted(items)[:40])

    module = text.replace("if keyboard.held[sdl.Scancode.W] {", "if keyboard.held[sdl.] {", 1)
    items = complete(module, 56, "sdl.")
    check("completion after a module: its names", "Scancode" in items, sorted(items)[:30])

    variant = text.replace("if keyboard.held[sdl.Scancode.W] {", "if keyboard.held[sdl.Scancode.] {", 1)
    items = complete(variant, 56, "sdl.Scancode.")
    check("completion after a union: its variants", {"W", "A", "Escape"} <= set(items), sorted(items)[:30])

    h = c.request("textDocument/hover", {"textDocument": doc, "position": pos(variant, 52, "obj", 1)})
    check("after completion, hover checks the editor's text again", h is not None and "obj — field" in h["contents"]["value"], h)

    # Renames. The file as it was, checked: its names and their uses kept.
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": 20}, "contentChanges": [{"text": text}]})
    c.request("textDocument/hover", {"textDocument": doc, "position": pos(text, 52, "obj", 1)})

    def actions_at(line_no):
        r = c.request("textDocument/codeAction", {"textDocument": doc, "range": {"start": {"line": line_no - 1, "character": 0},
                      "end": {"line": line_no - 1, "character": 0}}, "context": {"diagnostics": []}})
        # (Its quick fixes: a fun's refactors may be offered on its line too.)
        return {a["title"]: a for a in r or [] if a.get("kind") != "refactor"}

    # camera_move renamed at its definition, a keystroke at a time; its use is in Pounce.mara, not open.
    version = 20
    for name in ["camera_mov", "camera_mo", "camera_", "camera_s", "camera_st", "camera_step"]:
        version += 1
        typed = text.replace("camera_move :: fun", name + " :: fun", 1)
        c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": version}, "contentChanges": [{"text": typed}]})
    acts = actions_at(48)
    rename = acts.get("Rename the 1 use of camera_move to camera_step")
    edits = rename and rename["edit"]["changes"] or {}
    pounce = [e for u, es in edits.items() if u.lower().endswith("/pounce.mara") for e in es]
    check("renamed at its definition: rename its use in Pounce.mara offered", len(pounce) == 1 and pounce[0]["newText"] == "camera_step", acts)
    check("... and putting the name back", "Put the name back: camera_move" in acts, acts)
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": version + 1}, "contentChanges": [{"text": text}]})
    check("name put back: nothing offered", actions_at(48) == {}, actions_at(48))

    # A local renamed: its use further down the same file.
    version += 2
    local = text.replace("\tspeed: f32 = 500", "\tvelocity: f32 = 500", 1)
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": version}, "contentChanges": [{"text": local}]})
    decl_line = 1 + next(i for i, l in enumerate(local.split("\n")) if l.rstrip("\r") == "\tvelocity: f32 = 500")
    acts = actions_at(decl_line)
    rename = next((a for t, a in acts.items() if t.startswith("Rename the") and "speed to velocity" in t), None)
    edits = rename and [e for es in rename["edit"]["changes"].values() for e in es] or []
    check("a local renamed: its uses offered", len(edits) >= 1 and all(e["newText"] == "velocity" for e in edits), acts)
    # The offer taken: its edits made, then nothing more to offer.
    lines = local.split("\n")
    for e in sorted(edits, key=lambda e: (e["range"]["start"]["line"], e["range"]["start"]["character"]), reverse=True):
        r = e["range"]
        line = lines[r["start"]["line"]].encode("utf-8")
        lines[r["start"]["line"]] = (line[:r["start"]["character"]] + e["newText"].encode() + line[r["end"]["character"]:]).decode("utf-8")
    done = "\n".join(lines)
    version += 1
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": version}, "contentChanges": [{"text": done}]})
    check("the offer taken: nothing more offered", actions_at(decl_line) == {}, actions_at(decl_line))
    diags = [n for n in c.notes if n.get("method") == "textDocument/publishDiagnostics"]
    c.notes.clear()

    # F2: a name, its declaration and every use.
    version += 1
    c.notify("textDocument/didChange", {"textDocument": {"uri": uri(CAMERA), "version": version}, "contentChanges": [{"text": text}]})
    r = c.request("textDocument/rename", {"textDocument": doc, "position": pos(text, 48, "camera_move"), "newName": "camera_step"})
    files = {u.rsplit("/", 1)[1]: es for u, es in (r or {}).get("changes", {}).items()}
    check("rename: the declaration in camera.mara, the use in Pounce.mara", set(files) == {"camera.mara", "Pounce.mara"}
          and all(e["newText"] == "camera_step" for es in files.values() for e in es), r)
    try:
        c.request("textDocument/rename", {"textDocument": doc, "position": pos(text, 48, "camera_move"), "newName": "1st"})
        check("rename to no name: refused", False, "accepted")
    except RuntimeError as e:
        check("rename to no name: refused", "isn't a name" in str(e), str(e))

    c.notify("textDocument/didClose", {"textDocument": doc})
    moved_fields(c)
    moved_results_params(c)
    new_call_put_right(c)
    variants_completed(c)
    fun_calls(c)
    code = c.close()
    check("shut down: exit 0", code == 0, code)

    # Options: hover and diagnostics off — not offered, none published.
    c = Client({"hover": False, "diagnostics": False})
    caps = c.init["capabilities"]
    check("options: hover not offered, definition still", not caps["hoverProvider"] and caps["definitionProvider"], caps)
    c.notify("textDocument/didOpen", {"textDocument": {"uri": uri(CAMERA), "languageId": "mara", "version": 1, "text": broken}})
    d = c.request("textDocument/definition", {"textDocument": doc, "position": pos(broken, 52, "obj_get_directions")})
    published = [n for n in c.notes if n.get("method") == "textDocument/publishDiagnostics"]
    check("options: diagnostics off, none published", published == [], published)
    c.close()

    # UTF-16 positions, the protocol's default.
    c = Client(utf8=False)
    check("utf-16 when the client can't take utf-8", c.init["capabilities"]["positionEncoding"] == "utf-16", c.init)
    c.close()

    if bad:
        print("LSP: %d FAILED" % len(bad))
        sys.exit(1)
    print("LSP: all good")


main()
