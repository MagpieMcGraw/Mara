"""The Sublime plugin's "Name this use…": on a use line it asks for a name and
has the compiler change the use and every name written through it (`mara edit
<module> <prefix>.use [name]`). Sublime stood in for; the compiler is the real
one, run on a copy of test/edit_use.

    python test/plugin_use_test.py
"""
import os
import shutil
import sys
import tempfile
import types

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MARA = os.environ.get("MARA_EXE") or os.path.join(ROOT, "mara_dev.exe" if os.name == "nt" else "mara_dev")


class Region:
    def __init__(self, a, b=None):
        self.a, self.b = a, a if b is None else b

    def begin(self):
        return min(self.a, self.b)

    def end(self):
        return max(self.a, self.b)

    def empty(self):
        return self.a == self.b


said = []      # the status line's messages
panels = []    # what was put in an output panel
sublime = types.ModuleType("sublime")
sublime.Region = Region
sublime.load_settings = lambda name: {}
sublime.status_message = said.append
sublime.set_timeout_async = lambda f, delay=0: f()
sublime.set_timeout = lambda f, delay=0: f()
sublime_plugin = types.ModuleType("sublime_plugin")
for name in ("EventListener", "TextCommand", "WindowCommand", "ViewEventListener"):
    setattr(sublime_plugin, name, type(name, (), {}))
sys.modules["sublime"], sys.modules["sublime_plugin"] = sublime, sublime_plugin
sys.path.insert(0, os.path.join(ROOT, "editor", "sublime", "MaraAsk"))
import mara_ask

mara_ask._settings = lambda: {"mara_path": MARA}
# (Its work is done on a thread: here, at once.)
mara_ask.threading = types.SimpleNamespace(Thread=lambda target, daemon=False: types.SimpleNamespace(start=target))


class Window:
    def __init__(self):
        self.all, self.answer, self.asked, self.shown = [], None, None, []

    def views(self):
        return self.all

    def show_input_panel(self, caption, initial, on_done, on_change, on_cancel):
        self.asked = (caption, initial)
        if self.answer is not None:
            on_done(self.answer)

    def create_output_panel(self, name):
        return types.SimpleNamespace(run_command=lambda command, args: panels.append(args["characters"]))

    def run_command(self, command, args=None):
        self.shown.append(command)


class View:
    # A file as the editor has it: read from disk each time it's looked at,
    # as Sublime reloads a file that changed there; `unsaved` text is written
    # by a save.
    def __init__(self, window, path):
        self.w, self.path, self.caret, self.unsaved = window, path, 0, None
        window.all.append(self)

    def text(self):
        return self.unsaved if self.unsaved is not None else open(self.path, encoding="utf-8", newline="").read()

    def window(self):
        return self.w

    def file_name(self):
        return self.path

    def is_dirty(self):
        return self.unsaved is not None

    def run_command(self, command, args=None):
        if command == "save" and self.unsaved is not None:
            open(self.path, "w", encoding="utf-8", newline="").write(self.unsaved)
            self.unsaved = None

    def size(self):
        return len(self.text())

    def sel(self):
        return [Region(self.caret)]

    def substr(self, region):
        return self.text()[region.begin():region.end()]

    def line(self, point):
        text = self.text()
        start = text.rfind("\n", 0, point) + 1
        end = text.find("\n", point)
        return Region(start, len(text) if end < 0 else end)

    def on(self, words):
        self.caret = self.text().index(words) + 1
        return self


problems = 0


def check(what, ok, got=""):
    global problems
    print("%s %s" % ("ok  " if ok else "FAIL", what))
    if not ok:
        print("     got: %s" % str(got)[:700])
        problems += 1


def name_use(view, answer):
    del said[:], panels[:]
    view.w.answer, view.w.asked, view.w.shown = answer, None, []
    command = mara_ask.MaraUseNameCommand()
    command.view = view
    visible = command.is_visible()
    if visible:
        command.run(None)
    return visible


d = tempfile.mkdtemp(prefix="mara_plugin_use_")
try:
    for f in os.listdir(os.path.join(ROOT, "test", "edit_use")):
        if f.endswith(".mara"):
            shutil.copy(os.path.join(ROOT, "test", "edit_use", f), d)
    window = Window()
    view = View(window, os.path.join(d, "prefixes.mara"))
    original = view.text()

    check("not on a use line: not offered", not name_use(view.on("main :: fun"), "x"))
    check("on a use line: offered, the name it has now in the box",
          name_use(view.on("lib :: use"), None) and window.asked == ("edit_use_lib's names through (none: by themselves):", "lib"), window.asked)
    check("the same name given: nothing done", name_use(view.on("lib :: use"), "lib") and view.text() == original and not said, said)

    name_use(view.on("lib :: use"), "other")
    check("another name: the use and its names, said", "other :: use edit_use_lib" in view.text() and "other.LIMIT" in view.text()
          and said and "goes by other now" in said[-1], (said, view.text()))

    name_use(view.on("other :: use"), "State")
    check("a name that means something already: said, shown in a panel, nothing changed",
          said and "'State' means something already" in said[-1] and panels and "show_panel" in window.shown
          and "other :: use edit_use_lib" in view.text(), (said, panels))

    # (Unsaved text goes to disk first: the compiler edits the files there.)
    view.unsaved = view.text().replace("return 9", "return 9   // fast")
    name_use(view.on("other :: use"), "")
    text = view.text().replace("\r", "")
    check("no name, with unsaved text: saved first, then a plain use, its names by themselves",
          not view.is_dirty() and "\nuse edit_use_lib\n" in text and "return 9   // fast" in text
          and "print(LIMIT, twice(2), mine.w, show(s), mode_speed(Slow))" in text and "s := edit_use_lib.State()" in text, (said, text))

    check("a plain use: offered, nothing in the box",
          name_use(view.on("use edit_use_lib"), None) and window.asked == ("edit_use_lib's names through (none: by themselves):", ""), window.asked)
    name_use(view.on("use edit_use_lib"), "lib")
    check("a name again: as it was at first", view.text() == original.replace("return 9", "return 9   // fast"), (said, view.text()))
finally:
    shutil.rmtree(d, ignore_errors=True)

print("PLUGIN USE: %s" % ("all good" if problems == 0 else "%d wrong" % problems))
sys.exit(1 if problems else 0)
