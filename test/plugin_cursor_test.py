"""The Sublime plugin's cursor: what it asks a window when the cursor rests and
when a file is saved, in files with and without unsaved changes. Sublime stood
in for, and mara too: this checks what's sent — a byte of the file as saved —
not what's answered (test/ask.sh's cursor queries: which token it means).

    python test/plugin_cursor_test.py
"""
import os
import sys
import tempfile
import types

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
timers = []


class Region:
    def __init__(self, a, b=None):
        self.a, self.b = a, a if b is None else b

    def begin(self):
        return min(self.a, self.b)

    def end(self):
        return max(self.a, self.b)

    def empty(self):
        return self.a == self.b

    def size(self):
        return self.end() - self.begin()

    def contains(self, point):
        return self.begin() <= point <= self.end()


class Settings(dict):
    pass


sublime = types.ModuleType("sublime")
sublime.Region = Region
sublime.load_settings = lambda name: Settings()
sublime.set_timeout_async = lambda f, delay=0: timers.append(f)
sublime.set_timeout = lambda f, delay=0: timers.append(f)
sublime_plugin = types.ModuleType("sublime_plugin")
for name in ("EventListener", "TextCommand", "WindowCommand", "ViewEventListener"):
    setattr(sublime_plugin, name, type(name, (), {}))
sys.modules["sublime"], sys.modules["sublime_plugin"] = sublime, sublime_plugin
sys.path.insert(0, os.path.join(ROOT, "editor", "sublime", "MaraAsk"))
import mara_ask

asked = []


def run_mara(args, cwd):
    if "ask" in args:
        asked.append(" ".join(args[args.index("ask") + 1:]))
    return 0, ""


mara_ask._run_mara = run_mara
mara_ask._tell_editor = lambda *a: None
mara_ask._tell_colors = lambda *a: None


class View:
    next_id = 1

    def __init__(self, path, text, dirty=False):
        self.path, self.text, self.dirty = path, text, dirty
        self.caret = 0
        self.anchor = None   # (a highlight's other end)
        self.view_id = View.next_id
        View.next_id += 1
        self.active = self

    def id(self):
        return self.view_id

    def change_count(self):
        return hash(self.text)

    def file_name(self):
        return self.path

    def is_dirty(self):
        return self.dirty

    def size(self):
        return len(self.text)

    def settings(self):
        return Settings()

    def window(self):
        return types.SimpleNamespace(active_view=lambda: self.active)

    def sel(self):
        return [Region(self.caret if self.anchor is None else self.anchor, self.caret)]

    def substr(self, region):
        if isinstance(region, int):   # (a point: its character)
            return self.text[region:region + 1]
        return self.text[region.begin():region.end()]

    def rowcol(self, point):
        row = self.text.count("\n", 0, point)
        return row, point - (self.text.rfind("\n", 0, point) + 1)

    def line(self, point):
        start = self.text.rfind("\n", 0, point) + 1
        end = self.text.find("\n", point)
        return Region(start, len(self.text) if end < 0 else end)

    def click(self, word, k=1):
        self.caret = self.text.index(word) + k
        self.anchor = None
        return self

    def highlight(self, words):
        self.anchor = self.text.index(words)
        self.caret = self.anchor + len(words)
        return self


cursor = mara_ask.MaraCursor()
problems = 0


def check(what, got, want):
    global problems
    ok = got == want
    print("%s %s" % ("ok  " if ok else "FAIL", what))
    if not ok:
        print("     got  %r\n     want %r" % (got, want))
        problems += 1


def rest(view):
    del asked[:]
    cursor.on_selection_modified_async(view)
    while timers:
        timers.pop()()
    return list(asked)


def save(view):
    del asked[:]
    cursor.on_post_save_async(view)
    return list(asked)


# --- which saved line a line is ---------------------------------------------

L = mara_ask._saved_line
saved = ["a", "b", "c", "b", "d"]
check("the same lines: the same line", L(saved, saved, 3), 3)
check("before an edit: the same line", L(["a", "X", "c", "b", "d"], saved, 0), 0)
check("after an edit: the same line", L(["a", "X", "c", "b", "d"], saved, 3), 3)
check("the edited line isn't saved", L(["a", "X", "c", "b", "d"], saved, 1), None)
check("lines added above: moved up", L(["new", "new", "a", "b", "c", "b", "d"], saved, 5), 3)
check("lines taken away above: moved down", L(["c", "b", "d"], saved, 1), 3)
check("a line added: not saved", L(["a", "new", "b", "c", "b", "d"], saved, 1), None)
check("of two the same, the right one", L(["a", "b", "new", "c", "b", "d"], saved, 4), 3)
check("edits in two places: between them", L(["X", "b", "c", "b", "Y", "d"], saved, 2), 2)
check("edits in two places: moved between them", L(["X", "X", "b", "c", "b", "Y", "d"], saved, 3), 2)
check("edits in two places: past them", L(["X", "X", "b", "c", "b", "Y", "d"], saved, 6), 4)
check("edits in two places: the second not saved", L(["X", "b", "c", "b", "Y", "d"], saved, 4), None)

# --- what's asked: a byte in the file as saved ---------------------------------

folder = tempfile.mkdtemp()
path = os.path.join(folder, "m.mara")
disk = 'module m\n\nfirst := 1\nsecond := "é" ++ x\n'
with open(path, "w", encoding="utf-8", newline="\r\n") as f:   # (CRLF on disk: Sublime's buffer has none)
    f.write(disk)
raw = open(path, "rb").read()

view = View(path, disk)
at = raw.index(b"second") + 1
check("nothing unsaved: the byte, CRs counted", rest(view.click("second")), ["-cursor cursor at m.mara@%d" % at])
check("the same rest again: nothing", rest(view), [])
at = raw.index(b"++")
check("past a two-byte character: bytes, not characters", rest(view.click("++", 0)), ["-cursor cursor at m.mara@%d" % at])
lo = raw.index(b"first := 1")
check("a highlight: its two bytes", rest(view.highlight("first := 1")), ["-cursor cursor at m.mara@%d-%d" % (lo, lo + 10)])
check("a highlight over lines: nothing", rest(view.highlight("1\nsecond")), [])
view.click("\n\n", 1)
check("a blank line: asked all the same (the compiler says nothing's there)", rest(view), ["-cursor cursor at m.mara@%d" % (raw.index(b"\r\n\r\n") + 2)])

view = View(path, 'module m\n\nadded := 0\nfirst := 1\nsecond := "é" ++ x\n', dirty=True)
check("unsaved, lines added above: the line in the saved file", rest(view.click("second")), ["-cursor cursor at m.mara@%d" % (raw.index(b"second") + 1)])
check("unsaved, on the new line: said to be unsaved", rest(view.click("added")), ["-cursor #unsaved"])

view = View(path, 'module m\n\nfirst := 12\nsecond := "é" ++ x\n', dirty=True)
check("unsaved, on a changed line: said to be unsaved", rest(view.click("first")), ["-cursor #unsaved"])

gone = View(os.path.join(folder, "gone.mara"), "module m\nname := 1\n", dirty=True)
check("the file's not on disk: said to be unsaved", rest(gone.click("name")), ["-cursor #unsaved"])

view = View(path, disk)
rest(view.click("second"))
check("saved: Ask asked again at the cursor", save(view), ["-cursor what at m.mara@%d" % (raw.index(b"second") + 1)])

other = View(path, disk)
other.click("second")
other.active = View(path, disk)
check("saved, another file being worked in: nothing asked", save(other), [])

text = View(os.path.join(folder, "notes.txt"), "second")
check("not a Mara file saved: nothing asked", save(text.click("second")), [])

print("PLUGIN: %s" % ("all good" if problems == 0 else "%d wrong" % problems))
sys.exit(1 if problems else 0)
