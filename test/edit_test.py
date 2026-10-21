"""mara edit, run on a copy of test/lsp_fields: a struct's fields, a fun's
results and params put in another order — its declaration and every place
giving them by position — the program after meaning what it did; and what
it refuses. Run from the repo:
    python test/edit_test.py
Prints each check and "EDIT: all good", or what went wrong (exit 1)."""

import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MARA = os.environ.get("MARA_EXE") or os.path.join(ROOT, "mara_dev.exe" if os.name == "nt" else "mara_dev")   # (the debug build)
FIXTURE = os.path.join(ROOT, "test", "lsp_fields")
EXE = "fields.exe" if os.name == "nt" else "fields"

bad = []


def check(what, ok, got):
    print(("ok   " if ok else "FAIL ") + what + ("" if ok else "\n     got: " + str(got)[:600]))
    if not ok:
        bad.append(what)


def mara(cwd, *args):
    r = subprocess.run([MARA] + list(args), cwd=cwd, capture_output=True, text=True, encoding="utf-8")
    return r.returncode, r.stdout + r.stderr


def read(d, name):
    return open(os.path.join(d, name), encoding="utf-8", newline="").read()


def main():
    d = tempfile.mkdtemp(prefix="mara_edit_")
    try:
        for f in os.listdir(FIXTURE):
            if f.endswith(".mara"):
                shutil.copy(os.path.join(FIXTURE, f), d)
        code, out = mara(d, "build", "fields")
        before = subprocess.run([os.path.join(d, EXE)], capture_output=True, text=True).stdout.split("} ")[-1].strip()

        code, out = mara(d, "edit", "Token.fields", "file", "kind", "offset", "len")
        check("fields: a group split, refused", code == 1 and "are declared together" in out, out)
        code, out = mara(d, "edit", "Token.fields", "file", "offset", "len", "kind")
        text = read(d, "fields.mara")
        check("fields: done, said", code == 0 and "Token's fields now file, offset, len, kind" in out, out)
        check("fields: the declaration's lines moved, the literals' entries, the named one left",
              text.replace("\r", "").count("\tfile, offset, len : i64\n\tkind : i64\n") == 1
              and "Token{0, 10, 2, 1}" in text and "Token{0, 20, 3, 2}" in text
              and "Token{kind = 3, file = 0, offset = 30, len = 4}" in text, text)

        code, out = mara(d, "edit", "span.results", "bool", "i64")
        text = read(d, "funs.mara")
        check("results: the declaration, the returns and destructures", code == 0 and "-> bool, i64 {" in text
              and "return false, 0" in text and "return true, at + len" in text
              and "ok, end := span(3, 4)" in text and "fine, more := span(10, 0)" in text, out + text)
        code, out = mara(d, "edit", "span.params", "len,", "at")
        text = read(d, "funs.mara")
        check("params: the declaration and the calls (parts with commas)", code == 0 and "span :: fun(len: i64, at: i64)" in text
              and "span(4, 3)" in text and "span(0, 10)" in text, out + text)

        code, out = mara(d, "edit", "span.params", "len")
        check("not every part named: refused", code == 1 and "name each once" in out, out)
        code, out = mara(d, "edit", "nothing.fields", "a", "b")
        check("no such struct: said", code == 1 and "no struct with fields named nothing" in out, out)

        code, out = mara(d, "build", "fields")
        after = subprocess.run([os.path.join(d, EXE)], capture_output=True, text=True).stdout.split("} ")[-1].strip()
        check("the program builds, and means what it did", code == 0 and after == before, (before, after, out))
    finally:
        shutil.rmtree(d, ignore_errors=True)

    # A fun's body written out: its call put there — not where its local
    # would be stale (a call writing l.pos between).
    d = tempfile.mkdtemp(prefix="mara_edit_")
    try:
        shutil.copy(os.path.join(ROOT, "test", "edit_shapes", "shapes.mara"), d)
        exe = os.path.join(d, "shapes.exe" if os.name == "nt" else "shapes")
        mara(d, "build", "shapes")
        before = subprocess.run([exe], capture_output=True, text=True).stdout
        code, out = mara(d, "edit", "emit.calls")
        text = read(d, "shapes.mara")
        check("calls: two places, said", code == 0 and "emit called in the 2 places" in out, out)
        check("calls: `here` held by a local unchanged, and a local of its own: calls", "if c == '+' {\n\t\treturn emit(l, 1, 1)\n\t}" in text.replace("\r", "")
              and "if c == '*' {\n\t\treturn emit(l, 1, 3)\n\t}" in text.replace("\r", ""), text)
        check("calls: `here` stale (skip(l) writes l.pos): left", "skip(l)\n\t\tl.pos += 1\n\t\treturn true, Tok{here, 2, 2}" in text.replace("\r", ""), text)
        code, out = mara(d, "build", "shapes")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("calls: the program builds, and means what it did", code == 0 and after == before, (before, after, out))
        code, out = mara(d, "edit", "emit.calls")
        check("calls: again, nothing left", code == 0 and "No place writes out emit's body" in out, out)
    finally:
        shutil.rmtree(d, ignore_errors=True)

    if bad:
        print("EDIT: %d FAILED" % len(bad))
        sys.exit(1)
    print("EDIT: all good")


main()
