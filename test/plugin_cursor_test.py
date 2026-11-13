"""The Sublime plugin's cursor: what it asks a window when the cursor rests and
when a file is saved, in files with and without unsaved changes. Sublime stood
in for, and mara too: this checks what's sent, not what's answered.

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
docs = []   # (the words each rest gave Docs)
mara_ask._docs_send = lambda mara, cwd, words, *a, **k: docs.append(words) or True
mara_ask._tell_editor = lambda *a: None
mara_ask._tell_colors = lambda *a: None


class View:
    next_id = 1

    def __init__(self, path, text, dirty=False):
        self.path, self.text, self.dirty = path, text, dirty
        self.caret = 0
        self.view_id = View.next_id
        View.next_id += 1
        self.active = self

    def id(self):
        return self.view_id

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
        return [Region(self.caret)]

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

    def word(self, point):
        ok = lambda c: c.isalnum() or c == "_"
        a, b = point, point
        while a > 0 and ok(self.text[a - 1]):
            a -= 1
        while b < len(self.text) and ok(self.text[b]):
            b += 1
        return Region(a, b)

    # (Enough of Sublime's: a comment runs from `//` to its line's end, a string
    # between quotes on one line.)
    def match_selector(self, point, selector):
        line = self.substr(self.line(point))
        before = line[:point - self.line(point).begin()]
        return "//" in before or before.count('"') % 2 == 1

    def click(self, word):
        self.caret = self.text.index(word) + 1
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
    del docs[:]
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

# --- what's asked ------------------------------------------------------------

folder = tempfile.mkdtemp()
path = os.path.join(folder, "m.mara")
disk = "module m\n\nfirst := 1\nsecond := 2\n"
with open(path, "w", encoding="utf-8", newline="\r\n") as f:   # (on disk with CRLF, as ours are)
    f.write(disk)

view = View(path, disk)
check("nothing unsaved: what's at the point", rest(view.click("second")), ["-cursor what at m.mara:4:1"])
check("the same rest again: nothing", rest(view), [])

view = View(path, "module m\n\nadded := 0\nfirst := 1\nsecond := 2\n", dirty=True)
check("unsaved, lines added above: the line in the saved file", rest(view.click("second")), ["-cursor what at m.mara:4:1"])
check("unsaved, on the new line: said to be unsaved", rest(view.click("added")), ["-cursor #unsaved"])

view = View(path, "module m\n\nfirst := 12\nsecond := 2\n", dirty=True)
check("unsaved, on a changed line: said to be unsaved", rest(view.click("first")), ["-cursor #unsaved"])

gone = View(os.path.join(folder, "gone.mara"), "module m\nname := 1\n", dirty=True)
check("the file's not on disk: said to be unsaved", rest(gone.click("name")), ["-cursor #unsaved"])

view = View(path, disk)
rest(view.click("second"))
check("saved: asked again at the cursor", save(view), ["-cursor what at m.mara:4:1"])
view.caret = view.text.index("\n\n") + 1
check("saved, on nothing: nothing asked", save(view), [])

other = View(path, disk)
other.click("second")
other.active = View(path, disk)
check("saved, another file being worked in: nothing asked", save(other), [])

# --- an operator: what it calls ---------------------------------------------

ops_path = os.path.join(folder, "ops.mara")
ops = 'module ops\n\nfull := name ++ "a + b"\nsame := full == "x" // a + b\nf :: fun() -> i64\n'
with open(ops_path, "w", encoding="utf-8", newline="\n") as f:
    f.write(ops)
view = View(ops_path, ops)
check("on `++`: what's at it", rest(view.click("++")), ["-cursor what at ops.mara:3:14"])
view.caret = ops.index("++ ") + 2
check("just past `++`: the same", mara_ask._rest_words(view), ("++", ops.index("++")))
view.caret = ops.index("==")
check("on `==`: what's at it", rest(view), ["-cursor what at ops.mara:4:14"])
view.caret = ops.index("+ b\"")
check("a `+` in a string: nothing", rest(view), [])
view.caret = ops.index("+ b\n")
check("a `+` in a comment: nothing", rest(view), [])
view.caret = ops.index(":=") + 1
check("`:=`: nothing", rest(view), [])
view.caret = ops.index("->") + 1
check("`->`: nothing", rest(view), [])
view.caret = ops.index("++")
check("on `++`: asked, Docs not (no word to look up)", (rest(view), docs), (["-cursor what at ops.mara:3:14"], []))

idx = 'module ops\n\nn := items[i]\nm := items[i + 1].x\ns := "]"\n'
with open(ops_path, "w", encoding="utf-8", newline="\n") as f:
    f.write(idx)
view = View(ops_path, idx)
view.caret = idx.index("i]") + 2
check("just past an index's `]`: what's at it", rest(view), ["-cursor what at ops.mara:3:13"])
view.caret = idx.index("i]") + 1
check("before it, beside a name: the name", rest(view), ["-cursor what at ops.mara:3:12"])
check("... and Docs looks the name up", docs, ["i"])
view.caret = idx.index("1]") + 1
check("beside a number: the `]`", rest(view), ["-cursor what at ops.mara:4:17"])
view.caret = idx.index('"]"') + 2
check("a `]` in a string: nothing", rest(view), [])

calls = 'module ops\n\nn := twice(it.count)\nm := (n + 1) * 2\ntwice :: fun(x: i64) -> i64 {\n'
with open(ops_path, "w", encoding="utf-8", newline="\n") as f:
    f.write(calls)
view = View(ops_path, calls)
view.caret = calls.index("count)") + 6
check("just past a call's `)`: what's at it", rest(view), ["-cursor what at ops.mara:3:20"])
view.caret = calls.index("1)") + 2
check("just past a `)` around a value: what's at it", rest(view), ["-cursor what at ops.mara:4:12"])
view.caret = calls.index("i64)") + 4
check("just past a fun's params: nothing", rest(view), [])
view.caret = calls.index("count)") + 5
check("before a call's `)`: the name beside it", rest(view), ["-cursor what at ops.mara:3:15"])

text = View(os.path.join(folder, "notes.txt"), "second")
check("not a Mara file saved: nothing asked", save(text.click("second")), [])

print("PLUGIN: %s" % ("all good" if problems == 0 else "%d wrong" % problems))
sys.exit(1 if problems else 0)
