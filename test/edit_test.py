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

        # One-statement ifs written with do: the chain whose every branch
        # is one; a branch of two, a comment, one with do already, left.
        code, out = mara(d, "edit", "kind_of.do")
        text = read(d, "shapes.mara").replace("\r", "")
        check("do: one chain, said", code == 0 and "kind_of: 1 if written with do" in out, out)
        check("do: the chain written with do, its elif after it", "\tif c == '+' do return 1\n\telif c == '-' do return 2\n" in text, text)
        check("do: the others left", "\t\tx := 3\n" in text and "// (kept)" in text and "if c == '%' do return 5" in text, text)
        code, out = mara(d, "build", "shapes")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("do: the program builds, and means what it did", code == 0 and after == before, (before, after, out))

        # Ifs one after another, each before the last leaving: one chain.
        code, out = mara(d, "edit", "sign.elif")
        text = read(d, "shapes.mara").replace("\r", "")
        check("elif: three ifs, one chain, said", code == 0 and "sign: 3 ifs joined into 1 chain with elif" in out, out)
        check("elif: joined, the blank line kept, the one after a falling-through branch left",
              "\tif n < 0 {\n\t\treturn -1\n\n\telif n == 0\n\t\treturn 0\n\telif n > 100\n\t\tprint(\"big\")\n\t}\n\tif n > 50 {\n" in text, text)
        code, out = mara(d, "build", "shapes")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("elif: the program builds, and means what it did", code == 0 and after == before, (before, after, out))

        # A braced if then a chain with do: one braced chain, its `}` after.
        code, out = mara(d, "edit", "classify.elif")
        text = read(d, "shapes.mara").replace("\r", "")
        check("elif: a braced if and a do chain joined, the } after them", code == 0 and
              "\t\treturn x\n\telif c == 'b' do return 2\n\telif c == 'c' do return 3\n\telse do return 4\n\t}\n}" in text, out + text)
        # A braced chain's one-statement branches, with do inside its braces.
        code, out = mara(d, "edit", "grade.do")
        text = read(d, "shapes.mara").replace("\r", "")
        check("do: a braced chain's one-statement branches", code == 0 and "grade: 2 branches written with do" in out and
              "\t\treturn 1\n\telif n > 50 do return 2\n\telse do return 3\n\t}" in text, out + text)
        code, out = mara(d, "build", "shapes")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("mixed: the program builds, and means what it did", code == 0 and after == before, (before, after, out))
    finally:
        shutil.rmtree(d, ignore_errors=True)

    # How a use names its module: another name, none (its names by
    # themselves), a name again — the program meaning what it did each time.
    d = tempfile.mkdtemp(prefix="mara_edit_")
    try:
        for f in os.listdir(os.path.join(ROOT, "test", "edit_use")):
            if f.endswith(".mara"):
                shutil.copy(os.path.join(ROOT, "test", "edit_use", f), d)
        exe = os.path.join(d, "prefixes.exe" if os.name == "nt" else "prefixes")
        original = read(d, "prefixes.mara")

        def runs(what):
            code, out = mara(d, "build", "prefixes")
            got = subprocess.run([exe], capture_output=True, text=True).stdout.strip()
            check(what + ": the program builds, and means what it did", code == 0 and got == "10 4 7 3 1", (got, out))

        runs("use, before")
        code, out = mara(d, "edit", "prefixes", "lib.use", "other")
        text = read(d, "prefixes.mara")
        check("use: another name, said", code == 0 and "edit_use_lib goes by other now: 7 of its names" in out, out)
        check("use: its line and every name through it", "other :: use edit_use_lib" in text and "lib.LIMIT" not in text and "lib.Mode" not in text
              and "other.LIMIT, other.twice(2), mine.w, other.show(s), mode_speed(other.Slow)" in text, text)
        runs("use, another name")

        code, out = mara(d, "edit", "prefixes", "other.use", "State")
        check("use: a name that means something already, refused", code == 1 and "'State' means something already" in out
              and read(d, "prefixes.mara") == text, out)

        code, out = mara(d, "edit", "prefixes", "other.use")
        text = read(d, "prefixes.mara")
        check("use: no name, said — one kept", code == 0 and "names are by themselves now: 6 of them, and 1 kept through edit_use_lib" in out, out)
        check("use: a plain use, the names bare, the module's own State's left, the library's through its module",
              "\nuse edit_use_lib\n" in text.replace("\r", "") and "mine : State" in text and "s := edit_use_lib.State()" in text
              and "print(LIMIT, twice(2), mine.w, show(s), mode_speed(Slow))" in text and "m: Mode" in text and "m == Fast" in text, text)
        runs("use, no name")
        code, out = mara(d, "edit", "prefixes", "edit_use_lib.use")
        check("use: no name again, nothing to do", code == 0 and "by themselves in" in out and "already" in out, out)

        # (A method call that calls the module's fun: the fun called through the name.)
        open(os.path.join(d, "prefixes.mara"), "w", encoding="utf-8", newline="").write(text.replace("show(s)", "s.show()"))
        runs("use, a method call")
        code, out = mara(d, "edit", "prefixes", "edit_use_lib.use", "lib")
        check("use: a name again, said", code == 0 and "edit_use_lib goes by lib now: 7 of its names" in out, out)
        check("use: as it was written at first", read(d, "prefixes.mara") == original, read(d, "prefixes.mara"))
        runs("use, a name again")

        # The module's own fun of a library's name: its names by themselves
        # would make `twice(2)` either — the files are put back.
        before = read(d, "clash.mara")
        code, out = mara(d, "edit", "clash", "lib.use")
        check("use: an edit that doesn't check is undone, said why", code == 1 and "'twice' is ambiguous" in out
              and "its files are as they were" in out and read(d, "clash.mara") == before, out)
        code, out = mara(d, "edit", "clash", "nothing.use", "x")
        check("use: no such use, said", code == 1 and "no use in clash names a module nothing" in out, out)
    finally:
        shutil.rmtree(d, ignore_errors=True)

    if bad:
        print("EDIT: %d FAILED" % len(bad))
        sys.exit(1)
    print("EDIT: all good")


main()
