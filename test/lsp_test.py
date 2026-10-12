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
MARA = os.path.join(ROOT, "Mara.exe" if os.name == "nt" else "mara")
POUNCE = os.path.join(ROOT, "Pounce")
CAMERA = os.path.join(POUNCE, "camera.mara")


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

    c.notify("textDocument/didClose", {"textDocument": doc})
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
