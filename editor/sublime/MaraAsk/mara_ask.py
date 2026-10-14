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

# add_regions keys for the in-code flow highlight: the queried variable, and the
# other variables its flow surfaces. Erased and rewritten on each query.
HL_SUBJECT = "mara_ask_flow_subject"
HL_RELATED = "mara_ask_flow_related"

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


# ---- in-code highlight: mark a flow result's variables in the source -----------
#
# A flow result already prints every relevant variable with its def `file:line`.
# We re-derive each one's name + location, find that name on its source line, and
# add a region — the subject (queried variable) in one colour, the variables its
# flow surfaces in another. Rows under "into calls" are callee landings (a call
# site in another function, not a local), so they're skipped.

# Subject header: "speed — local in camera_move  camera.mara:50   (module …)".
_HEADER_RE = re.compile(r"^(\w+)\s+—\s+\w+\s+in\s+.*?" + RESULT_REGEX)
# `at` note: "(flow rooted at the write on camera.mara:80)" — the real root site.
_ROOT_NOTE_RE = re.compile(r"flow rooted at the write on .*?" + RESULT_REGEX)
# Leading tags on a `flow below` row; the variable name is the token after them.
_KIND_WORDS = frozenset(("modify", "decl", "assign", "write", "destr", "loop", "param"))
_IDENT_RE = re.compile(r"^\w+$")


def _flow_highlights(out):
    # Parse a flow result into (subject, related): the queried variable and the
    # other variables its flow surfaces, each as (name, file, line).
    subject = None
    related = []
    in_landing = False
    for line in out.splitlines():
        if not line.strip() or line.startswith("$ "):
            continue
        if line.startswith(("above (flow)", "below (flow)")):
            in_landing = False
            continue
        if "into calls" in line:          # landings follow until the next section
            in_landing = True
            continue
        if subject is None:
            hm = _HEADER_RE.match(line)
            if hm:
                subject = (hm.group(1), hm.group(2), int(hm.group(3)))
                continue
        if in_landing:
            continue
        locs = _LOC_RE.findall(line)
        if not locs:
            continue
        f, n = locs[-1]
        toks = line[:line.rfind(f)].split()
        if not toks:
            continue
        name = toks[1] if (toks[0] in _KIND_WORDS and len(toks) > 1) else toks[0]
        if _IDENT_RE.match(name):
            related.append((name, f, int(n)))
    # `at` roots flow at a specific write — mark THAT site as the subject, not the
    # declaration the header names.
    if subject is not None:
        rm = _ROOT_NOTE_RE.search(out)
        if rm:
            subject = (subject[0], rm.group(1), int(rm.group(2)))
        related = [r for r in related if r != subject]   # don't double-mark it
    return subject, related


def _norm(p):
    return os.path.normcase(os.path.normpath(p))


def _resolve(cwd, f):
    # Output paths are relative to the queried module's dir (cwd) or absolute.
    return _norm(f if os.path.isabs(f) else os.path.join(cwd or "", f))


def _name_region(view, name, line_1):
    # The first whole-word occurrence of `name` on the given (1-based) source line —
    # the def is the leftmost, which is what the location points at.
    row = line_1 - 1
    if row < 0:
        return None
    line_region = view.line(view.text_point(row, 0))
    m = re.search(r"\b%s\b" % re.escape(name), view.substr(line_region))
    if not m:
        return None
    base = line_region.begin()
    return sublime.Region(base + m.start(), base + m.end())


def _highlight_flow(window, cwd, out):
    subject, related = _flow_highlights(out)
    by_file = {}                          # resolved path -> [(name, line, is_subject)]
    if subject:
        by_file.setdefault(_resolve(cwd, subject[1]), []).append((subject[0], subject[2], True))
    for name, f, ln in related:
        by_file.setdefault(_resolve(cwd, f), []).append((name, ln, False))

    subj_scope = _settings().get("highlight_subject_scope", "region.bluish")
    rel_scope = _settings().get("highlight_scope", "region.yellowish")
    for v in window.views():
        v.erase_regions(HL_SUBJECT)
        v.erase_regions(HL_RELATED)
        fn = v.file_name()
        items = by_file.get(_norm(fn)) if fn else None
        if not items:
            continue
        subj, rel = [], []
        for name, ln, is_subj in items:
            r = _name_region(v, name, ln)
            if r is not None:
                (subj if is_subj else rel).append(r)
        if rel:
            v.add_regions(HL_RELATED, rel, rel_scope, "", sublime.DRAW_NO_OUTLINE)
        if subj:
            v.add_regions(HL_SUBJECT, subj, subj_scope, "", sublime.DRAW_NO_OUTLINE)


def _clear_flow(window):
    for v in window.views():
        v.erase_regions(HL_SUBJECT)
        v.erase_regions(HL_RELATED)


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
        # -show: a `mara view` window open on the module shows the query and its
        # answer in its Ask panel (it answers too; no window, a plain ask).
        ask = [mara, "ask"] + (["-show"] if _settings().get("show_in_window", True) else [])
        name_args = ask + [word] + filt

        # Root the query, and pick the `at <file>:<line>` fallback used when <word>
        # isn't a top-level name (a local/param, or a name drilled in the output).
        if view.settings().get(VIEW_FLAG):
            # Drilling from the output pane: it has no file of its own, so reuse the
            # module dir of the query that filled it, and address the row's printed
            # location for the `at` fallback.
            cwd = view.settings().get("mara_ask_cwd") or None
            loc = _loc_on_line(view)
            at_args = (ask + ["at", loc] + filt) if loc else None
        else:
            fname = view.file_name()
            cwd = os.path.dirname(fname) if fname else None
            at_args = None
            if fname:
                row = view.rowcol(view.sel()[0].b)[0] + 1
                at_args = ask + ["at", "%s:%d" % (os.path.basename(fname), row)] + filt

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
        echo = " ".join(a if " " not in a else '"%s"' % a for a in used if a != "-show")
        sublime.set_timeout(lambda: self._present(cwd, echo, out), 0)

    def _present(self, cwd, echo, out):
        window = self.view.window()
        if window is None:
            return
        _show_in_view(window, self.view, cwd, echo, out)
        # Mark the result's variables in the code (flow results only — they're the
        # ones whose printed locations are local def sites).
        if _settings().get("highlight_flow", True) and "(flow)" in out:
            _highlight_flow(window, cwd, out)
        else:
            _clear_flow(window)


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


class MaraAskClearHighlightsCommand(sublime_plugin.TextCommand):
    # Drop the in-code flow highlight (it's also replaced on the next query).
    def run(self, edit):
        window = self.view.window()
        if window is not None:
            _clear_flow(window)


# ---- the cursor: docs and what's there, in a `mara view` window ----------------
#
# When the cursor rests (delay_ms), and only when where it is changed, a window
# is told two things, for reading after an alt-tab:
#   Docs (mara docs): a window open anywhere looks the words up — what the name
#     at the cursor refers to first, the compiler's answer, then the text
#     matches in the file's directory, the stdlib and doc/.
#   Ask (mara ask -cursor what at <point>): the window open on the file's
#     module shows what's at the cursor at the top of its Ask panel — what the
#     name is, its type, where it's declared, the expressions around it.
# The words: what's highlighted, when something is (one line; a whole fun isn't
# words); else the name under the cursor; else, in a call's parentheses, the fun
# being called (signature help). The point: the cursor — with a highlight, its
# cursor end, so what's under the cursor shows as well. An unsaved file's
# places may be stale: Docs then shows the text matches alone, and Ask waits for
# the save. Off with "docs_at_cursor" / "what_at_cursor" / "signature_help".

_cursor_pending = [0]   # the latest rest's number: older ones don't send
_cursor_sent = [None]   # (file, words, point) last sent: the same again isn't

_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_NOT_CALLS = frozenset(("fun", "if", "elif", "for", "match", "return", "and", "or", "not", "do"))


def _docs_cwd(view):
    # The module the cursor is in: its file's directory; in the output pane,
    # the module of the query that filled it.
    if view.settings().get(VIEW_FLAG):
        return view.settings().get("mara_ask_cwd") or None
    fname = view.file_name()
    if fname and fname.endswith(".mara"):
        return os.path.dirname(fname)
    return None


class MaraCursor(sublime_plugin.EventListener):
    def on_selection_modified_async(self, view):
        sel = view.sel()
        if len(sel) != 1:
            return
        cwd = _docs_cwd(view)
        if cwd is None:
            return
        s = sel[0]
        caret = s.b
        words, point = None, caret
        if not s.empty():
            text = view.substr(s).strip()
            # (A highlight over lines — a whole fun — isn't words to look up.)
            if not text or "\n" in text or len(text) > 200:
                return
            words = text
            # (The cursor end: just past the highlight when it was made left to
            # right — its last character, then, not what follows it.)
            point = s.b - 1 if s.b > s.a else s.b
        else:
            word = view.word(caret)
            name = view.substr(word)
            if _NAME_RE.match(name):
                words, point = name, word.begin()
            elif _settings().get("signature_help", True):
                callee = _callee_at(view, caret)
                if callee is not None:
                    words, point = callee
        if words is None:
            return
        key = (view.file_name() or cwd, words, point)
        _cursor_pending[0] += 1
        number = _cursor_pending[0]
        at = _docs_at(view, point)
        # (Ask's places are the file on disk: an unsaved one's may be stale.)
        what_at = at if not view.is_dirty() else None
        delay = _settings().get("delay_ms", 300)
        sublime.set_timeout_async(lambda: _cursor_send(number, key, cwd, words, at, what_at), delay)


# A point as `mara docs at` and `mara ask what at` take it: "<file>:<line>:
# <col>", from 1; None in a view with no file (the output pane).
def _docs_at(view, point):
    fname = view.file_name()
    if not fname:
        return None
    row, col = view.rowcol(point)
    return "%s:%d:%d" % (os.path.basename(fname), row + 1, col + 1)


# The call being typed at the caret: the name before its unclosed `(` on the
# caret's line — a method's, after its `.` — and where that name starts. None
# when the caret is in no call.
def _callee_at(view, caret):
    start = view.line(caret).begin()
    text = view.substr(sublime.Region(start, caret))
    depth = 0
    i = len(text) - 1
    while i >= 0:
        c = text[i]
        if c == ")":
            depth += 1
        elif c == "(":
            if depth == 0:
                break
            depth -= 1
        i -= 1
    if i < 0:
        return None
    end = i
    j = end
    while j > 0 and (text[j - 1].isalnum() or text[j - 1] == "_"):
        j -= 1
    name = text[j:end]
    if not name or name[0].isdigit() or name in _NOT_CALLS:
        return None
    return name, start + j


# The windows told how to open a file at a line — this Sublime's own subl,
# beside it (`mara editor`): a call their Crash panel shows opens here,
# clicked. Once one has it (it keeps it for every window); until then, tried
# again at each rest.
_editor_told = [False]


def _tell_editor(mara, cwd):
    if _editor_told[0]:
        return
    subl = os.path.join(os.path.dirname(sublime.executable_path()), "subl.exe" if os.name == "nt" else "subl")
    if not os.path.exists(subl):
        _editor_told[0] = True   # (nothing to tell)
        return
    rc, _ = _run_mara([mara, "editor", subl], cwd)
    _editor_told[0] = rc == 0


# The rest's two lookups, unless a newer rest came, or this one was sent already.
def _cursor_send(number, key, cwd, words, at, what_at):
    if number != _cursor_pending[0] or _cursor_sent[0] == key:
        return
    _cursor_sent[0] = key
    mara = _settings().get("mara_path", "mara")
    _tell_editor(mara, cwd)
    if _settings().get("docs_at_cursor", True):
        rc, out = _run_mara([mara, "docs"] + (["at", at] if at else []) + [words], cwd)
        first = out.strip().splitlines()[0] if out.strip() else "no answer"
        sublime.status_message("Mara Docs: " + first)
    if what_at and _settings().get("what_at_cursor", True):
        _run_mara([mara, "ask", "-cursor", "what", "at", what_at], cwd)


# ---- the window: `mara view` on the file's module ----------------------------

_MODULE_RE = re.compile(r"module\s+([A-Za-z0-9_.]+)")


def _module_of(view):
    # The module the file declares: its first line that isn't blank or a
    # comment (`//`, or a `/* … */` block, which nests).
    text = view.substr(sublime.Region(0, min(view.size(), 8000)))
    depth = 0
    for line in text.splitlines():
        s = line.strip()
        if depth > 0 or s.startswith("/*"):
            depth += s.count("/*") - s.count("*/")
            continue
        if not s or s.startswith("//"):
            continue
        m = _MODULE_RE.match(s)
        return m.group(1) if m else None
    return None


def _allow_foreground():
    # Windows lets only the program in front put a window in front: this lets
    # the window `mara view` opens, or brings forward, come in front of Sublime.
    if os.name != "nt":
        return
    try:
        import ctypes
        ctypes.windll.user32.AllowSetForegroundWindow(-1)   # ASFW_ANY
    except Exception:
        pass   # (it opens behind, then: nothing worse)


class MaraViewCommand(sublime_plugin.TextCommand):
    # The window (`mara view`) on the module this file is in — opened, or
    # brought to the front when one's open on it already. In the right-click
    # menu and the command palette, for .mara files.
    def run(self, edit):
        fname = self.view.file_name()
        if not fname:
            sublime.status_message("mara view: save the file first — the window opens on its folder's module")
            return
        mara = _settings().get("mara_path", "mara")
        module = _module_of(self.view)
        cwd = os.path.dirname(fname)
        _allow_foreground()

        def go():
            rc, out = _run_mara([mara, "view"] + ([module] if module else []), cwd)
            if rc != 0:
                lines = out.strip().splitlines()
                sublime.status_message("mara view: " + (lines[0] if lines else "failed (exit %d)" % rc))

        threading.Thread(target=go, daemon=True).start()

    def is_visible(self):
        fname = self.view.file_name()
        return bool(fname and fname.endswith(".mara")) or self.view.match_selector(0, "source.mara")
