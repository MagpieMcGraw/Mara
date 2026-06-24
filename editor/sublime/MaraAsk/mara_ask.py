# Mara Ask — a thin Sublime Text front-end for `mara ask`.
#
# The editor already knows the subject: the word under the cursor names a type /
# function, and the cursor's file:line addresses the variable defined there. So a
# query is a keystroke, not a typed command. Output lands in a cleared-per-query
# output panel whose `result_file_regex` makes every `file:line` jump-to-source
# (F4 / double-click) — the analyzer already prints locations everywhere.
#
# Commands:
#   mara_ask        run `mara ask <word>` (kind/direction optional via args)
#   mara_ask_pick   quick-panel to choose one of the matrix cells, then run it
#
# The tool picks the natural kind for a bare query (struct -> types, fn -> call,
# var -> flow), so the no-arg command Just Works on whatever's under the cursor.

import os
import threading
import subprocess

import sublime
import sublime_plugin

SETTINGS = "Mara Ask.sublime-settings"
PANEL = "mara_ask"

# Locations the analyzer prints — "camera.mara:10" or an absolute stdlib path like
# "C:\Code\Mara\code\math.mara:3". File in \1, line in \2; relative paths resolve
# against result_base_dir (the queried module's directory).
RESULT_REGEX = r"([\w./\\:+-]+\.mara):(\d+)"


def _settings():
    return sublime.load_settings(SETTINGS)


def _subject(view):
    # An explicit selection wins (lets you query a dotted path or a trimmed name);
    # otherwise the word under the caret.
    sel = view.sel()[0]
    if not sel.empty():
        return view.substr(sel).strip()
    return view.substr(view.word(sel.b)).strip()


def _run_mara(args, cwd):
    # CREATE_NO_WINDOW keeps a console from flashing on every query (Windows).
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    try:
        # encoding="utf-8" (not text=True): the analyzer emits UTF-8 (— ∞ ⟵ …); on
        # Windows text=True would decode as the ANSI codepage and mojibake them.
        p = subprocess.run(args, cwd=cwd, capture_output=True,
                           encoding="utf-8", errors="replace", creationflags=flags)
        out = p.stdout if p.stdout.strip() else p.stderr
        return p.returncode, out
    except FileNotFoundError:
        return 127, ("mara not found — set \"mara_path\" in "
                     "Mara Ask.sublime-settings\n  (tried: %s)\n" % args[0])
    except Exception as e:
        return 1, "mara ask failed: %s\n" % e


class MaraAskCommand(sublime_plugin.TextCommand):
    def run(self, edit, kind="", direction="", depth=None):
        view = self.view
        word = _subject(view)
        if not word:
            sublime.status_message("Mara Ask: no word under the cursor")
            return

        fname = view.file_name()
        cwd = os.path.dirname(fname) if fname else None

        filt = [a for a in (kind, direction) if a]
        if depth is None:
            depth = _settings().get("default_depth", 0)
        if depth:
            filt.append(str(depth))

        mara = _settings().get("mara_path", "mara")
        name_args = [mara, "ask", word] + filt

        # `at <file>:<line>` addresses the variable declared on the cursor's line —
        # the fallback when <word> isn't a top-level name (i.e. it's a local/param).
        at_args = None
        if fname:
            row = view.rowcol(view.sel()[0].b)[0] + 1
            at_args = [mara, "ask", "at", "%s:%d" % (os.path.basename(fname), row)] + filt

        threading.Thread(target=self._work, args=(name_args, at_args, cwd)).start()

    def _work(self, name_args, at_args, cwd):
        rc, out = _run_mara(name_args, cwd)
        used = name_args
        # A name miss is usually a local/parameter — retry the cursor's file:line,
        # which `at` resolves precisely. Keep the name-query guidance if `at` misses
        # too (it explains how to address a variable).
        if rc != 0 and at_args is not None:
            rc2, out2 = _run_mara(at_args, cwd)
            if rc2 == 0:
                used, out = at_args, out2
        sublime.set_timeout(lambda: self._show(used, cwd, out), 0)

    def _show(self, args, cwd, out):
        window = self.view.window()
        if window is None:
            return
        window.destroy_output_panel(PANEL)        # clear: each query stands alone
        panel = window.create_output_panel(PANEL)
        s = panel.settings()
        s.set("result_file_regex", RESULT_REGEX)
        s.set("result_base_dir", cwd or "")
        s.set("word_wrap", False)
        s.set("line_numbers", False)
        s.set("gutter", False)
        s.set("scroll_past_end", False)
        echo = " ".join(a if " " not in a else '"%s"' % a for a in args)
        panel.run_command("append", {"characters": "$ %s\n\n%s" % (echo, out or "(no output)\n")})
        window.run_command("show_panel", {"panel": "output." + PANEL})


# label, hint, kind, direction — the matrix cells offered by mara_ask_pick.
CELLS = [
    ["overview",    "the subject's natural view (type / call / flow)", "",      ""],
    ["types above", "what supplies it / what it's built from",         "types", "above"],
    ["types below", "what it supplies / what contains it",             "types", "below"],
    ["call above",  "callees / calls that supply it",                  "call",  "above"],
    ["call below",  "callers / calls it supplies",                     "call",  "below"],
    ["flow above",  "what builds this value (lineage)",                "flow",  "above"],
    ["flow below",  "what this value feeds (forward slice)",           "flow",  "below"],
]


class MaraAskPickCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        view = self.view
        items = [[c[0], c[1]] for c in CELLS]

        def on_done(i):
            if i < 0:
                return
            _, _, kind, direction = CELLS[i]
            view.run_command("mara_ask", {"kind": kind, "direction": direction})

        view.window().show_quick_panel(items, on_done)
