"""Writes the tiny TrueType fonts test/font_files.mara reads.

Each is a few hundred bytes: small enough that reading a table past its end
runs off the file (the crash mara.font had on every font under ~310 KB).
Run it from anywhere: `python test/fonts/make_test_fonts.py`.

Glyphs, in font units (1000 an em):
  0  .notdef  a box with a hole (two contours, the inner one turned the other way)
  1  A        a square, 0..500
  2  B        compound: glyph 1, then glyph 1 at half size placed by matching
              its point 1 to the compound's point 2 (so it lands at 500..750
              across, 250..500 up)
  3  C        a ring of four points all off the curve (a rounded diamond)
Characters: A B C -> glyphs 1 2 3, a b -> 3 1, and U+1F600 -> 1 where the
character map reaches past U+FFFF.
"""

import os
import struct

HERE = os.path.dirname(os.path.abspath(__file__))

ON = 0x01


def simple_glyph(contours):
    """contours: lists of (x, y, on_curve). Every delta written as 2 bytes."""
    points = [p for c in contours for p in c]
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    out = struct.pack(">hhhhh", len(contours), min(xs), min(ys), max(xs), max(ys))
    end = -1
    for c in contours:
        end += len(c)
        out += struct.pack(">H", end)
    out += struct.pack(">H", 0)  # no instructions
    out += bytes(ON if p[2] else 0 for p in points)
    prev = 0
    for x in xs:
        out += struct.pack(">h", x - prev)
        prev = x
    prev = 0
    for y in ys:
        out += struct.pack(">h", y - prev)
        prev = y
    return out


def compound_b():
    ARG_1_AND_2_ARE_WORDS = 0x0001
    ARGS_ARE_XY_VALUES = 0x0002
    WE_HAVE_A_SCALE = 0x0008
    MORE_COMPONENTS = 0x0020
    out = struct.pack(">hhhhh", -1, 0, 0, 750, 500)
    # glyph 1 where it is
    out += struct.pack(">HHhh", ARG_1_AND_2_ARE_WORDS | ARGS_ARE_XY_VALUES | MORE_COMPONENTS, 1, 0, 0)
    # glyph 1 at half size, its point 1 on the compound's point 2 (byte args: point numbers)
    out += struct.pack(">HHBBh", WE_HAVE_A_SCALE, 1, 2, 1, 0x2000)
    return out


GLYPHS = [
    simple_glyph([
        [(50, 0, 1), (50, 700, 1), (450, 700, 1), (450, 0, 1)],
        [(100, 50, 1), (400, 50, 1), (400, 650, 1), (100, 650, 1)],
    ]),
    simple_glyph([[(0, 0, 1), (0, 500, 1), (500, 500, 1), (500, 0, 1)]]),
    compound_b(),
    simple_glyph([[(100, 100, 0), (100, 600, 0), (600, 600, 0), (600, 100, 0)]]),
]


def pad4(b):
    return b + b"\0" * (-len(b) % 4)


def cmap_format4(segments, glyph_ids=()):
    """segments: (start, end, id_delta, use_array); use_array segments take
    their glyphs from glyph_ids, in order. A final 0xFFFF segment is added."""
    segments = list(segments) + [(0xFFFF, 0xFFFF, 1, False)]
    n = len(segments)
    ends = b"".join(struct.pack(">H", s[1]) for s in segments)
    starts = b"".join(struct.pack(">H", s[0]) for s in segments)
    deltas = b"".join(struct.pack(">H", s[2] & 0xFFFF) for s in segments)
    ranges = b""
    array_at = 0
    for i, s in enumerate(segments):
        if s[3]:
            # bytes from this idRangeOffset entry to the glyph it names
            ranges += struct.pack(">H", 2 * (n - i) + 2 * array_at)
            array_at += s[1] - s[0] + 1
        else:
            ranges += struct.pack(">H", 0)
    array = b"".join(struct.pack(">H", g) for g in glyph_ids)
    body = ends + b"\0\0" + starts + deltas + ranges + array
    length = 14 + len(body)
    return struct.pack(">HHHHHHH", 4, length, 0, 2 * n, 0, 0, 0) + body


def cmap_format12(groups):
    body = b"".join(struct.pack(">III", *g) for g in groups)
    return struct.pack(">HHIII", 12, 0, 16 + len(body), 0, len(groups)) + body


def cmap_format6(first, glyph_ids):
    body = b"".join(struct.pack(">H", g) for g in glyph_ids)
    return struct.pack(">HHHHH", 6, 10 + len(body), 0, first, len(glyph_ids)) + body


def cmap_format0(mapping):
    ids = bytearray(256)
    for c, g in mapping.items():
        ids[c] = g
    return struct.pack(">HHH", 0, 262, 0) + bytes(ids)


ABC = [(0x41, 0x43, 1 - 0x41, False), (0x61, 0x62, 0, True)]
ABC_ARRAY = [3, 1]


def cmap_table(subtables):
    """subtables: (platform, encoding, bytes), in the order to list them."""
    out = struct.pack(">HH", 0, len(subtables))
    offset = 4 + 8 * len(subtables)
    data = b""
    for platform, encoding, sub in subtables:
        out += struct.pack(">HHI", platform, encoding, offset + len(data))
        data += sub
    return out + data


def checksum(b):
    b = pad4(b)
    return sum(struct.unpack(">%dI" % (len(b) // 4), b)) & 0xFFFFFFFF


def font(cmap, long_loca=False):
    glyf = b""
    offsets = []
    for g in GLYPHS:
        offsets.append(len(glyf))
        glyf += pad4(g)
    offsets.append(len(glyf))
    if long_loca:
        loca = b"".join(struct.pack(">I", o) for o in offsets)
    else:
        loca = b"".join(struct.pack(">H", o // 2) for o in offsets)

    head = struct.pack(">IIIIHHqqhhhhHHhhh",
                       0x00010000, 0x00010000, 0, 0x5F0F3CF5, 0x000B, 1000,
                       0, 0, 0, 0, 750, 700, 0, 8, 2, 1 if long_loca else 0, 0)
    n_hmetrics = 2  # glyphs 2 and 3 share glyph 1's advance
    hhea = struct.pack(">IhhhHhhhhhhhhhhhH",
                       0x00010000, 800, -200, 0, 1000, 0, 0, 750, 1, 0, 0,
                       0, 0, 0, 0, 0, n_hmetrics)
    hmtx = struct.pack(">HhHh", 500, 50, 600, 0) + struct.pack(">hh", 0, 100)
    maxp = struct.pack(">IHHHHHHHHHHHHHH", 0x00010000, len(GLYPHS),
                       8, 2, 8, 2, 2, 0, 0, 0, 0, 0, 0, 2, 1)

    tables = {b"cmap": cmap, b"glyf": glyf, b"head": head, b"hhea": hhea,
              b"hmtx": hmtx, b"loca": loca, b"maxp": maxp}
    tags = sorted(tables)
    n = len(tags)
    entry_selector = n.bit_length() - 1
    search_range = 16 * (1 << entry_selector)
    out = struct.pack(">IHHHH", 0x00010000, n, search_range, entry_selector, 16 * n - search_range)
    offset = 12 + 16 * n
    data = b""
    for tag in tags:
        t = tables[tag]
        out += tag + struct.pack(">III", checksum(t), offset + len(data), len(t))
        data += pad4(t)
    whole = bytearray(out + data)
    head_at = offset + sum(len(pad4(tables[t])) for t in tags[:tags.index(b"head")])
    struct.pack_into(">I", whole, head_at + 8, (0xB1B0AFBA - checksum(bytes(whole))) & 0xFFFFFFFF)
    return bytes(whole)


def write(name, data):
    with open(os.path.join(HERE, name), "wb") as f:
        f.write(data)


def main():
    abc = {0x41: 1, 0x42: 2, 0x43: 3}
    tiny = font(cmap_table([
        (3, 1, cmap_format4(ABC, ABC_ARRAY)),
        (3, 10, cmap_format12([(0x41, 0x43, 1), (0x61, 0x61, 3), (0x62, 0x62, 1), (0x1F600, 0x1F600, 1)])),
    ]))
    write("tiny.ttf", tiny)
    write("tiny_bmp.ttf", font(cmap_table([(3, 1, cmap_format4(ABC, ABC_ARRAY))]), long_loca=True))
    write("tiny_mac0.ttf", font(cmap_table([(1, 0, cmap_format0(abc))])))
    write("tiny_mac6.ttf", font(cmap_table([(1, 0, cmap_format6(0x41, [1, 2, 3]))])))
    write("tiny_symbol.ttf", font(cmap_table([
        (3, 0, cmap_format4([(0xF041, 0xF043, 1 - 0xF041, False)])),
    ])))
    write("tiny_cut.ttf", tiny[:200])
    write("not_truetype.otf", b"OTTO" + b"\0" * 60)


if __name__ == "__main__":
    main()
