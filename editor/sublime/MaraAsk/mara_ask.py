# Mara Ask — a thin Sublime Text front-end for `mara ask`.
#
# The editor already knows the subject: the word under the cursor names a type /
# function, and the cursor's file:line addresses the variable defined there. So a
# query is a keystroke, not a typed command. Output lands in a reused scratch view
# parked in a right-hand split group — a real editor pane (resize / fold / find),
# with `result_file_regex` set so every `file:line` is jump-to-source (F4 / click).
#
# Commands:
#   mara_ask        run `mara ask <word>` (kind/direction optional via args)
#   mara_ask_pick   quick-panel to choose one of the matrix cells, then run it
#
# The tool picks the natural kind for a bare query (struct -> types, fn -> call,
# var -> flow), so the no-arg command Just Works on whatever's under the cursor.

import os
import re
import threading
import subprocess

import sublime
import sublime_plugin

SETTINGS = "Mara Ask.sublime-settings"
VIEW_FLAG = "mara_ask_view"          # marks the one reused output view
VIEW_NAME = "✦ Mara Ask"

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


_LOC_RE = re.compile(RESULT_REGEX)


def _loc_on_line(view):
    # The file:line printed on the cursor's row. Output rows carry locations, so
    # drilling into a name from the output pane can address it precisely via `at`.
    line = view.substr(view.line(view.sel()[0].b))
    m = _LOC_RE.search(line)
    return "%s:%s" % (m.group(1), m.group(2)) if m else None


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


# ---- output view: one reused scratch view in a right-hand split group ---------

def _ask_view(window):
    # Reuse the marked view if it's still open; else mint a fresh scratch view.
    for v in window.views():
        if v.settings().get(VIEW_FLAG):
            return v
    v = window.new_file()
    v.set_name(VIEW_NAME)
    v.set_scratch(True)              # never prompts to save
    v.settings().set(VIEW_FLAG, True)
    return v


def _ensure_right_group(window):
    # Split into two columns ONLY if the window is a single pane, so we never
    # stomp a layout the user set up themselves. Returns the rightmost group.
    if window.num_groups() < 2:
        ratio = _settings().get("split_ratio", 0.6)
        window.set_layout({
            "cols": [0.0, ratio, 1.0],
            "rows": [0.0, 1.0],
            "cells": [[0, 0, 1, 1], [1, 0, 2, 1]],
        })
    return window.num_groups() - 1


def _show_in_view(window, code_view, cwd, echo, out):
    view = _ask_view(window)

    # Park it in the right-hand group (creating the column if needed).
    group = _ensure_right_group(window)
    if window.get_view_index(view)[0] != group:
        window.set_view_index(view, group, len(window.views_in_group(group)))

    s = view.settings()
    s.set("result_file_regex", RESULT_REGEX)   # F4 / click jumps to file:line
    s.set("result_base_dir", cwd or "")
    s.set("word_wrap", False)
    s.set("line_numbers", False)
    s.set("gutter", False)
    s.set("scroll_past_end", False)
    s.set("draw_indent_guides", False)
    s.set("draw_white_space", "none")
    s.set("mara_ask_cwd", cwd or "")   # so a query FROM this pane roots correctly

    body = "$ %s\n\n%s" % (echo, out or "(no output)\n")
    view.set_read_only(False)
    view.run_command("select_all")
    view.run_command("left_delete")            # each query stands alone
    view.run_command("append", {"characters": body, "scroll_to_end": False})
    view.set_read_only(True)
    view.sel().clear()
    view.set_viewport_position((0, 0), False)  # back to the top

    # Keep typing in your code: focus returns to the invoking view, so the next
    # Ctrl+K Ctrl+A reads a word from the code, not from this output pane.
    if code_view is not None and code_view.is_valid():
        window.focus_view(code_view)


class MaraAskCommand(sublime_plugin.TextCommand):
    def run(self, edit, kind="", direction="", depth=None):
        view = self.view
        word = _subject(view)
        if not word:
            sublime.status_message("Mara Ask: no word under the cursor")
            return

        filt = [a for a in (kind, direction) if a]
        if depth is None:
            depth = _settings().get("default_depth", 0)
        if depth:
            filt.append(str(depth))

        mara = _settings().get("mara_path", "mara")
        name_args = [mara, "ask", word] + filt

        # Root the query, and pick the `at <file>:<line>` fallback used when <word>
        # isn't a top-level name (a local/param, or a name drilled in the output).
        if view.settings().get(VIEW_FLAG):
            # Drilling from the output pane: it has no file of its own, so reuse the
            # module dir of the query that filled it, and address the row's printed
            # location for the `at` fallback.
            cwd = view.settings().get("mara_ask_cwd") or None
            loc = _loc_on_line(view)
            at_args = ([mara, "ask", "at", loc] + filt) if loc else None
        else:
            fname = view.file_name()
            cwd = os.path.dirname(fname) if fname else None
            at_args = None
            if fname:
                row = view.rowcol(view.sel()[0].b)[0] + 1
                at_args = [mara, "ask", "at",
                           "%s:%d" % (os.path.basename(fname), row)] + filt

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
        echo = " ".join(a if " " not in a else '"%s"' % a for a in used)
        sublime.set_timeout(lambda: self._present(cwd, echo, out), 0)

    def _present(self, cwd, echo, out):
        window = self.view.window()
        if window is None:
            return
        _show_in_view(window, self.view, cwd, echo, out)


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
