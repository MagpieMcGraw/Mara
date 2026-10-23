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

    # Every address written &x, then ^x: the one character, nothing else —
    # not `a & b`, not `p^`, not a type's `^T`; the program the same each way.
    d = tempfile.mkdtemp(prefix="mara_edit_")
    try:
        shutil.copy(os.path.join(ROOT, "test", "address_caret.mara"), d)
        exe = os.path.join(d, "address_caret.exe" if os.name == "nt" else "address_caret")
        mara(d, "build", "address_caret")
        before = subprocess.run([exe], capture_output=True, text=True).stdout
        code, out = mara(d, "edit", "address_caret.address", "ampersand")
        text = read(d, "address_caret.mara")
        check("address: to &x, said", code == 0 and "address_caret: 9 addresses written &x" in out, out)
        check("address: &x everywhere, the rest left (p^, ^T, the comment)", text.count("^") == 9 and "p := &x" in text and "&x == &x" in text
              and "with &lib do print(\"with:\", work(&lib))" in text and "6 & 3" in text and "n^ += 1" in text and "lib: ^Arena_Basic" in text, text)
        code, out = mara(d, "build", "address_caret")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("address: the program builds, and means what it did", code == 0 and after == before, (before, after, out))
        code, out = mara(d, "edit", "address_caret.address", "caret")
        text = read(d, "address_caret.mara")
        check("address: back to ^x", code == 0 and "address_caret: 10 addresses written ^x" in out
              and text.count("^") == 19 and "^x == ^x" in text and "next(^list)^ = 5" in text and "6 & 3" in text, out + text)
        code, out = mara(d, "edit", "address_caret.address", "caret")
        check("address: again, nothing left", code == 0 and "No address in address_caret is written &x" in out, out)
        code, out = mara(d, "edit", "address_caret.address", "pointy")
        check("address: a word it doesn't know, refused", code == 1 and "caret (^x) or ampersand (&x)" in out, out)
        code, out = mara(d, "build", "address_caret")
        after = subprocess.run([exe], capture_output=True, text=True).stdout
        check("address: built again, the same", code == 0 and after == before, (before, after, out))
    finally:
        shutil.rmtree(d, ignore_errors=True)

    if bad:
        print("EDIT: %d FAILED" % len(bad))
        sys.exit(1)
    print("EDIT: all good")


main()
