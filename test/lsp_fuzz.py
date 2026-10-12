"""mara lsp on code as it's typed: real files cut and broken the ways an edit
in progress leaves them — cut off mid-line, `x.` with nothing after, a `(`
left open, a line gone (a brace unmatched) — each sent as an unsaved edit
and a hover asked (a check made). The server must answer each: one that
dies or hangs is a crash; its text is saved in test/lsp_crashes/. Run from
the repo:  python test/lsp_fuzz.py [variants per file]"""

import json
import os
import subprocess
import sys
import threading
import queue
import random

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MARA = os.path.join(ROOT, "Mara.exe" if os.name == "nt" else "mara")
FILES = [os.path.join(ROOT, "Pounce", "camera.mara"), os.path.join(ROOT, "Pounce", "Pounce.mara"),
         os.path.join(ROOT, "view", "hub.mara"), os.path.join(ROOT, "view", "docs.mara"),
         os.path.join(ROOT, "code", "os.mara")]
CRASHES = os.path.join(ROOT, "test", "lsp_crashes")
TIMEOUT = 20


def uri(path):
    return "file:///" + path.replace("\\", "/").lstrip("/")


class Server:
    def __init__(self):
        self.p = subprocess.Popen([MARA, "lsp"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, cwd=ROOT)
        self.inbox = queue.Queue()
        threading.Thread(target=self._read, daemon=True).start()
        self.id = 0
        self.request("initialize", {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}})

    def _read(self):
        out = self.p.stdout
        while True:
            length = None
            while True:
                line = out.readline()
                if not line:
                    self.inbox.put(None)
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

    def request(self, method, params):
        self.id += 1
        self.send({"jsonrpc": "2.0", "id": self.id, "method": method, "params": params})
        while True:
            msg = self.inbox.get(timeout=TIMEOUT)
            if msg is None:
                raise EOFError("the server ended")
            if msg.get("id") == self.id:
                return msg

    def change(self, path, text, version):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didChange",
                   "params": {"textDocument": {"uri": uri(path), "version": version}, "contentChanges": [{"text": text}]}})

    def stop(self):
        try:
            self.p.kill()
        except Exception:
            pass


def variants(text, count, rng):
    """Texts an edit in progress leaves, from one that checks."""
    lines = text.split("\n")
    out = []
    for _ in range(count):
        i = rng.randrange(len(lines))
        line = lines[i]
        kind = rng.randrange(5)
        if kind == 0:   # cut off mid-line: the file ends there
            out.append(("cut", "\n".join(lines[:i] + [line[:rng.randrange(len(line) + 1)]])))
        elif kind == 1:   # `x.` with nothing after, the rest of the file as it was
            dots = [k for k, c in enumerate(line) if c == "."]
            if not dots:
                continue
            k = rng.choice(dots)
            out.append(("dot", "\n".join(lines[:i] + [line[:k + 1]] + lines[i + 1:])))
        elif kind == 2:   # a `(` left open at the line's end
            out.append(("paren", "\n".join(lines[:i] + [line + " foo("] + lines[i + 1:])))
        elif kind == 3:   # a line gone: a brace unmatched, a name undeclared
            out.append(("gone", "\n".join(lines[:i] + lines[i + 1:])))
        else:   # the line cut, the rest kept: half a word, half a call
            out.append(("half", "\n".join(lines[:i] + [line[:rng.randrange(len(line) + 1)]] + lines[i + 1:])))
    return out


def main():
    per_file = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    rng = random.Random(int(os.environ.get("SEED", "1")))
    os.makedirs(CRASHES, exist_ok=True)
    server = Server()
    tried = crashed = 0
    for path in FILES:
        text = open(path, encoding="utf-8", newline="").read()
        server.send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                     "params": {"textDocument": {"uri": uri(path), "languageId": "mara", "version": 1, "text": text}}})
        version = 1
        for kind, broken in variants(text, per_file, rng):
            version += 1
            tried += 1
            try:
                server.change(path, broken, version)
                line = rng.randrange(max(1, broken.count("\n")))
                server.request("textDocument/hover", {"textDocument": {"uri": uri(path)}, "position": {"line": line, "character": 2}})
            except (EOFError, queue.Empty, OSError, BrokenPipeError) as e:
                crashed += 1
                name = "%s_%d_%s.mara" % (os.path.basename(path)[:-5], version, kind)
                with open(os.path.join(CRASHES, name), "w", encoding="utf-8", newline="") as f:
                    f.write(broken)
                print("CRASH (%s) on %s: %s" % (kind, name, type(e).__name__))
                server.stop()
                server = Server()
                server.send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                             "params": {"textDocument": {"uri": uri(path), "languageId": "mara", "version": version, "text": text}}})
        server.send({"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {"textDocument": {"uri": uri(path)}}})
    server.stop()
    print("FUZZ: %d edits, %d crashes%s" % (tried, crashed, " (texts in test/lsp_crashes/)" if crashed else ""))
    sys.exit(1 if crashed else 0)


main()
