# Moving code to slices without a len

Written 2026-10-29 for sooblivion and mara3, against Mara at fa9555d (design/slices_without_len.md).
The errors below are the checker's, from a no-link build of each. Fixing them can bring up more
(later passes run only once the types check), and some changes give no error at all: see the
last section.

## How to move each kind

- **Grows a slice** (`&view + x`, `next(&view)`, an append through a `^[]T`):
  - a param that grows what it points at: `^[]T` → `^[$N]T`, and its callers pass the list,
    `&list`;
  - a struct field that a loader fills: a pointer to the list it fills, `^[64 * MB]byte`, or
    keep it a slice and write it by index with a count;
  - a take filled by appends: write it by index, a count beside it, and cut it to the count at
    the end (`parts = parts[0:k]`). A take is a view of all n of its items now.
- **Writes a slice's len** (`view.len = 0`, `view.len += n`, `view.len = got`):
  - a reset or a count: the thing is a list, or keeps a count of its own;
  - a shrink: reslice it, `view = view[0:n]`.
- **Takes from a slice** (`slice([:n]T, storage)`, `let(T, storage)` with storage a `^[]byte` or a
  slice field): storage is a list — a `^[$N]byte` param, a `^[64 * MB]byte` field, `&list`.
  `&bytes[k]`, at a place, still takes.
- **Reads** (`file_read`, `pipe_read`, `udp_receive`, `tcp_receive`): they read into a window and
  give back the part they filled; nothing sets a len. `file_read(id, &chunk)` with chunk an empty
  list reads into its 0 items and fails with Empty_Window. Give the room:
  `w := chunk[:.cap]`, then `got := file_read(id, &w)?`, and use `got`.
- **Text for C** (the SDL and OpenGL bindings, `process_start`, `load_library`): they take a list,
  `[$N]utf8` — a str64, a Path, a literal. A slice there is an error: copy it into a list.

## Changes no error points at

- A list given as a slice is a view of its items: its cap is its len now, not the list's room.
- A `^[]T` made from a list (`&list` where a `^[]T` is taken) bounds its indexing by the list's
  len, not its room: writing past its items through it stops the program. A fun that writes a
  list's room takes `^[$N]T`.
- `x[:]` and `x[lo:]` of a list end at its len again; `x[a:b]` shows exactly b - a items.
- cstring() of a slice passes only with its 0 as its last item (`b[0 : n + 1]`); of a list, as
  before.
- An arena's cursor is `a.used`; `a.base.len` is its whole size.


## sooblivion: 333 errors

grows a slice: 177, writes a slice's len: 101, takes from a slice: 38, other (most follow from one above): 17.

### model.mara (47)

- 343: takes from a slice — `parts = slice([:shape_count]Model_Part, storage),`
- 344: takes from a slice — `flips = slice([:flip_count]Model_Flip, storage),`
- 345: takes from a slice — `particles = slice([:system_count]Model_Particles, storage),`
- 346: takes from a slice — `motions = slice([:motion_count]Model_Motion, storage),`
- 349: takes from a slice — `palette = slice([:if how.rigged do MODEL_PALETTE else 0]Palette_Entry, storage)}`
- 429: takes from a slice — `vertices := slice([:count]Vertex, storage)`
- 447: grows a slice — `&vertices + vertex`
- 450: takes from a slice — `influences := slice([:0]Skin_Influence, storage)`
- 452: takes from a slice — `influences = slice([:count]Skin_Influence, storage)`
- 461: takes from a slice — `indices := slice([:geometry.triangle_count * 3]u16, storage)`
- 465: grows a slice — `&indices + index`
- 478: grows a slice — `part := next(&model.parts)`
- 547: writes a slice's len — `pose.len = 0`
- 569: grows a slice — `bone := next(pose)`
- 571: mismatched types for '+': ^<error> and []utf8 - did you forget to import the module that defines the overload? — `&bone.name + node.object.name[0 : min(node.object.name.len, 64)]`
- 596: writes a slice's len — `rig.len = 0`
- 617: grows a slice — `rig + Rig_Bone{parent = parent, local = local, track = track}`
- 629: writes a slice's len — `places.len = 0`
- 634: grows a slice — `places + place`
- 644: writes a slice's len — `places.len = 0`
- 653: grows a slice — `places + place`
- 707: takes from a slice — `heaviest := slice([:count][8!]f32, storage)`
- 708: grows a slice — `for k in 0:count do &heaviest + [-1, -1, -1, -1, 0, 0, 0, 0]`
- 730: grows a slice — `&model.palette + Palette_Entry{bone = bone_index, offset = bone.transform}`
- 758: grows a slice — `&model.palette + Palette_Entry{bone = -1, offset = mat4_identity()}`
- 772: grows a slice — `influences + influence`
- 783: grows a slice — `&model.palette + Palette_Entry{bone = how.hang_bone, offset = how.hang_offset}`
- 786: grows a slice — `influences + influence`
- 827: takes from a slice — `moved := slice([:count]Vec3, storage)`
- 828: takes from a slice — `turned := slice([:count]Vec3, storage)`
- 829: takes from a slice — `totals := slice([:count]f32, storage)`
- 831: grows a slice — `&moved + Vec3{0, 0, 0}`
- 832: grows a slice — `&turned + Vec3{0, 0, 0}`
- 833: grows a slice — `&totals + f32(0)`
- 968: grows a slice — `motion := next(&model.motions)`
- 1003: the value of '&motion.key_times + keys.time(k)' is dropped — capture it (`x := ...`) or discard it explicitly (`_ = ...`) — `&motion.key_times + keys.time(k)`
- 1004: the value of '&motion.key_values + value' is dropped — capture it (`x := ...`) or discard it explicitly (`_ = ...`) — `&motion.key_values + value`
- 1009: writes a slice's len — `if motion.key_times.len < 2 do model.motions.len -= 1`
- 1134: grows a slice — `indices + a`
- 1135: grows a slice — `indices + b`
- 1136: grows a slice — `indices + c`
- 1138: grows a slice — `indices + a`
- 1139: grows a slice — `indices + c`
- 1140: grows a slice — `indices + b`
- 1258: grows a slice — `entry := next(&model.particles)`
- 1476: grows a slice — `entry := next(&model.flips)`
- 1482: could not infer type parameter '$N' in call to 'next' — `frame := next(&entry.frames)`

### shader_package.mara (43)

- 32: grows a slice — `shaders + Packaged_Shader{name = names[at : name_end], code = data[at + 260 : end]}`
- 56: grows a slice — `constant := next(constants)`
- 128: grows a slice — `if number == 0 do text + "oPos"`
- 129: grows a slice — `elif number == 1 do text + "oFog"`
- 130: grows a slice — `else do text + "oPts"`
- 133: grows a slice — `text + "oDepth"`
- 136: grows a slice — `if number == 0 do text + "vPos"`
- 137: grows a slice — `else do text + "vFace"`
- 141: grows a slice — `text + "r"`
- 143: grows a slice — `text + "v"`
- 145: grows a slice — `text + "c"`
- 147: grows a slice — `text + (if pixel do "t" else "a")`
- 149: grows a slice — `text + "oD"`
- 151: grows a slice — `text + (if pixel do "o" else "oT")`
- 153: grows a slice — `text + "i"`
- 155: grows a slice — `text + "oC"`
- 157: grows a slice — `text + "s"`
- 159: grows a slice — `text + "b"`
- 161: grows a slice — `text + "p"`
- 163: grows a slice — `text + "?"`
- 165: grows a slice — `text + int_text(number)`
- 172: grows a slice — `text + "-"`
- 176: grows a slice — `text + int_text(whole)`
- 180: grows a slice — `text + "."`
- 182: grows a slice — `for pad in digits.len:4 do text + "0"`
- 186: grows a slice — `text + digits[0 : last]`
- 193: grows a slice — `text + "."`
- 194: grows a slice — `if mask & 1 != 0 do text + "x"`
- 195: grows a slice — `if mask & 2 != 0 do text + "y"`
- 196: grows a slice — `if mask & 4 != 0 do text + "z"`
- 197: grows a slice — `if mask & 8 != 0 do text + "w"`
- 205: grows a slice — `text + "."`
- 208: grows a slice — `text + letters[i64(first)]`
- 211: grows a slice — `for k in 0:4 do text + letters[i64((components >> u32(k * 2)) & 3)]`
- 217: grows a slice — `if modifier == 1 or modifier == 3 or modifier == 5 or modifier == 8 or modifier == 12 do text + "-"`
- 218: grows a slice — `if modifier == 6 do text + "1-"`
- 219: grows a slice — `if modifier == 11 or modifier == 12 do text + "abs("`
- 221: grows a slice — `if modifier == 2 or modifier == 3 do text + "_bias"`
- 222: grows a slice — `if modifier == 4 or modifier == 5 do text + "_bx2"`
- 223: grows a slice — `if modifier == 7 or modifier == 8 do text + "_x2"`
- 224: grows a slice — `if modifier == 11 or modifier == 12 do text + ")"`
- 251: grows a slice — `line := next(lines)`
- 291: grows a slice — `line = next(lines)`

### animation.mara (32)

- 35: takes from a slice — `if not fits(room.len + count * 4 + 16, room.cap) do return slice([:0]f32, room)`
- 36: takes from a slice — `return slice([:count]f32, room)`
- 40: takes from a slice — `if not fits(room.len + count * 16 + 16, room.cap) do return slice([:0][4!]f32, room)`
- 41: takes from a slice — `return slice([:count][4!]f32, room)`
- 45: takes from a slice — `if not fits(room.len + count * 12 + 16, room.cap) do return slice([:0]Vec3, room)`
- 46: takes from a slice — `return slice([:count]Vec3, room)`
- 85: grows a slice — `track := next(tracks)`
- 87: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.rotation_times = []`
- 88: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.rotations = []`
- 90: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.angle_times[axis] = []`
- 91: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.angles[axis] = []`
- 93: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.translation_times = []`
- 94: `[]` has nothing to say what it holds: write where it goes, `xs : []i64 = []`, or pass it where a slice or a list is taken — `track.translations = []`
- 99: writes a slice's len — `if not still_too and not track_moves(track) do tracks.len -= 1`
- 153: grows a slice — `&track.rotation_times + time`
- 154: grows a slice — `&track.rotations + rotation`
- 162: grows a slice — `&track.translation_times + time`
- 163: grows a slice — `&track.translations + translation`
- 169: grows a slice — `&track.rotation_times + 0`
- 170: grows a slice — `&track.rotations + interpolator.rotation`
- 173: grows a slice — `&track.translation_times + 0`
- 174: grows a slice — `&track.translations + interpolator.translation`
- 215: grows a slice — `&track.rotation_times + spline.start_time`
- 216: grows a slice — `&track.rotations + spline.rotation`
- 219: grows a slice — `&track.translation_times + spline.start_time`
- 220: grows a slice — `&track.translations + spline.translation`
- 231: grows a slice — `&track.rotation_times + time`
- 232: grows a slice — `&track.rotations + q`
- 236: grows a slice — `&track.translation_times + time`
- 237: grows a slice — `&track.translations + Vec3{p[0], p[1], p[2]}`
- 312: grows a slice — `&track.angle_times[axis] + time`
- 313: grows a slice — `&track.angles[axis] + angle`

### npc.mara (27)

- 494: writes a slice's len — `room.file.len = 0`
- 495: writes a slice's len — `room.blocks.len = 0`
- 506: writes a slice's len — `room.file.len = 0`
- 507: writes a slice's len — `room.blocks.len = 0`
- 531: writes a slice's len — `room.file.len = 0`
- 532: writes a slice's len — `room.blocks.len = 0`
- 551: writes a slice's len — `room.file.len = 0`
- 552: writes a slice's len — `room.blocks.len = 0`
- 705: writes a slice's len — `room.model.len = 0`
- 707: takes from a slice — `built := slice([:NPC_MODEL_PARTS]Model_Part, &room.model)`
- 708: takes from a slice — `palette := slice([:if rigged do NPC_PALETTE else 0]Palette_Entry, &room.model)`
- 715: writes a slice's len — `skins.len = 0`
- 725: writes a slice's len — `room.file.len = 0`
- 726: writes a slice's len — `room.blocks.len = 0`
- 774: grows a slice — `for entry in made.palette do &palette + entry`
- 788: takes from a slice — `pixels := slice([:4 * MOST_SKIN_TEXELS]byte, skin_storage)`
- 799: writes a slice's len — `if width == 0 do skin_storage.len = taken_at`
- 801: grows a slice — `skin := next(skins)`
- 803: mismatched types for '+': ^<error> and text (8 bytes) - did you forget to import the module that defines the overload? — `&skin.path + "facegen\\"`
- 804: mismatched types for '+': ^<error> and str64 - did you forget to import the module that defines the overload? — `&skin.path + int_text(i64(look.npc_id))`
- 805: mismatched types for '+': ^<error> and text (1 bytes) - did you forget to import the module that defines the overload? — `&skin.path + "\\"`
- 806: mismatched types for '+': ^<error> and str64 - did you forget to import the module that defines the overload? — `&skin.path + int_text(part_index)`
- 817: grows a slice — `&built + made_part^`
- 841: writes a slice's len — `moves.len = 0`
- 867: writes a slice's len — `file_storage.len = 0`
- 882: writes a slice's len — `file_storage.len = 0`
- 891: writes a slice's len — `base_storage.len = 0`

### png.mara (20)

- 37: grows a slice — `out + u8((value >> 24) & 255)`
- 38: grows a slice — `out + u8((value >> 16) & 255)`
- 39: grows a slice — `out + u8((value >> 8) & 255)`
- 40: grows a slice — `out + u8(value & 255)`
- 48: grows a slice — `out + kind`
- 49: grows a slice — `out + data`
- 59: writes a slice's len — `out.len = 0`
- 61: grows a slice — `for b in signature do out + b`
- 80: writes a slice's len — `scratch.len = 0`
- 83: grows a slice — `scratch + u8(0)`
- 84: grows a slice — `scratch + pixels[y * row_size : (y + 1) * row_size]`
- 93: grows a slice — `out + "IDAT"`
- 94: grows a slice — `out + u8(0x78)`
- 95: grows a slice — `out + u8(0x01)`
- 101: grows a slice — `out + u8(if last do 1 else 0)`
- 102: grows a slice — `out + u8(size & 255)`
- 103: grows a slice — `out + u8((size >> 8) & 255)`
- 104: grows a slice — `out + u8((65535 - size) & 255)`
- 105: grows a slice — `out + u8(((65535 - size) >> 8) & 255)`
- 106: grows a slice — `out + rows[at : at + size]`

### speedtree.mara (18)

- 454: takes from a slice — `bark_vertices = slice([:TREE_PART_VERTICES]Vertex, storage),`
- 455: takes from a slice — `bark_indices = slice([:TREE_PART_VERTICES * 6]u16, storage),`
- 456: takes from a slice — `leaf_vertices = slice([:TREE_PART_VERTICES]Vertex, storage),`
- 457: takes from a slice — `leaf_indices = slice([:TREE_PART_VERTICES * 3 / 2]u16, storage),`
- 482: writes a slice's len — `growth.bark_vertices.len = 0`
- 483: writes a slice's len — `growth.bark_indices.len = 0`
- 490: takes from a slice — `parts := slice([:2]Model_Part, storage)`
- 499: grows a slice — `if growth.bark_indices.len > 0 do &parts + tree_part(&growth, false, bark_texture)`
- 500: grows a slice — `if growth.leaf_indices.len > 0 do &parts + tree_part(&growth, true, leaf_texture)`
- 677: grows a slice — `&growth.bark_vertices + Vertex{`
- 689: grows a slice — `&growth.bark_indices + u16(here)`
- 690: grows a slice — `&growth.bark_indices + u16(here + 1)`
- 691: grows a slice — `&growth.bark_indices + u16(above + 1)`
- 692: grows a slice — `&growth.bark_indices + u16(here)`
- 693: grows a slice — `&growth.bark_indices + u16(above + 1)`
- 694: grows a slice — `&growth.bark_indices + u16(above)`
- 734: grows a slice — `&growth.leaf_vertices + Vertex{`
- 742: grows a slice — `for k in [0, 1, 2, 0, 2, 3] do &growth.leaf_indices + u16(first_vertex + k)`

### scene.mara (16)

- 501: writes a slice's len — `cues.len = 0`
- 515: grows a slice — `if sound >= 0 and fits(cues.len + 1, cues.cap) do cues + Door_Cue{time = seconds, sound = sound}`
- 589: writes a slice's len — `room.file.len = 0`
- 592: writes a slice's len — `room.blocks.len = 0`
- 601: writes a slice's len — `room.model.len = 0`
- 928: writes a slice's len — `loader.room.file.len = 0`
- 933: writes a slice's len — `loader.room.model.len = 0`
- 1006: writes a slice's len — `loader.room.file.len = 0`
- 1011: writes a slice's len — `loader.room.model.len = 0`
- 1210: writes a slice's len — `room.file.len = 0`
- 1300: writes a slice's len — `room.file.len = 0`
- 1302: writes a slice's len — `room.blocks.len = 0`
- 1536: writes a slice's len — `room.model.len = 0`
- 1645: grows a slice — `if due and fits(noises.len + 1, noises.cap) do noises + Door_Noise{sound = cue.sound, position = place}`
- 1649: grows a slice — `if sound >= 0 and fits(noises.len + 1, noises.cap) do noises + Door_Noise{sound = sound, position = place}`
- 1747: grows a slice — `textures + texture_grasses_of(scene, plugin, texture, loader)`

### viewer.mara (15)

- 744: writes a slice's len — `grounds.len = 0`
- 745: writes a slice's len — `tree_cells.len = 0`
- 746: writes a slice's len — `grass_cells.len = 0`
- 1276: grows a slice — `if fits(movers.len + 1, movers.cap) do movers + Npc_Mover{reference = other.reference, speed = other.told.speed, way = other.way,`
- 1543: writes a slice's len — `sounds.len = 0`
- 1551: grows a slice — `sounds + Placed_Sound{kind = kind, position = Vec3{0, 0, 0}, key = WEATHER_SOUND_KEY | list_bit | u64(sound.sound),`
- 1615: writes a slice's len — `room.file.len = 0`
- 1617: writes a slice's len — `room.blocks.len = 0`
- 1620: writes a slice's len — `room.model.len = 0`
- 1864: writes a slice's len — `layers.len = 0`
- 1869: writes a slice's len — `room.file.len = 0`
- 1871: writes a slice's len — `room.blocks.len = 0`
- 1874: writes a slice's len — `room.model.len = 0`
- 1881: grows a slice — `layer := next(layers)`
- 2531: writes a slice's len — `scratch.len = 0`

### index_cache.mara (11)

- 57: writes a slice's len — `storage.len = start`
- 97: takes from a slice — `keys := slice([:slots]u64, storage)`
- 98: writes a slice's len — `keys.len = slots`
- 101: takes from a slice — `values := slice([:slots]u32, storage)`
- 102: writes a slice's len — `values.len = slots`
- 142: writes a slice's len — `chunk.len = 8`
- 149: writes a slice's len — `chunk.len = 0`
- 152: writes a slice's len — `chunk.len += 8`
- 159: writes a slice's len — `chunk.len = 0`
- 162: writes a slice's len — `chunk.len += 4`
- 167: writes a slice's len — `chunk.len = 0`

### facegen.mara (8)

- 69: writes a slice's len — `moves.len = 0`
- 72: grows a slice — `for k in 0:count do moves + Vec3{0, 0, 0}`
- 121: writes a slice's len — `out.len = 0`
- 141: grows a slice — `for channel in 0:3 do out + u8(min(max(128 + moves[channel * plane + texel], 0), 255))`
- 142: grows a slice — `out + u8(255)`
- 152: writes a slice's len — `out.len = 0`
- 160: grows a slice — `out + u8(min(max(moved, 0), 255))`
- 162: grows a slice — `out + u8(color[3])`

### render.mara (8)

- 1972: writes a slice's len — `source.len = 0`
- 1973: grows a slice — `source + "#version 450 core\n"`
- 1974: grows a slice — `if bindless do source + "#extension GL_ARB_bindless_texture : require\n#define BINDLESS 1\n"`
- 1975: grows a slice — `source + shared`
- 1976: grows a slice — `source + body`
- 1977: grows a slice — `source + utf8(0)`
- 1978: writes a slice's len — `source.len -= 1`
- 3093: writes a slice's len — `scratch.len = 0`

### bsa.mara (7)

- 113: takes from a slice — `folders := slice([:folder_count]Folder, storage)`
- 114: takes from a slice — `files := slice([:file_count]Archive_File, storage)`
- 127: grows a slice — `folder := next(&folders)`
- 152: grows a slice — `entry := next(&files)`
- 305: writes a slice's len — `storage.len = start + entry.size`
- 315: writes a slice's len — `output.len = 0`
- 317: writes a slice's len — `storage.len = start + output.len`

### land.mara (7)

- 280: writes a slice's len — `indices.len = 0`
- 289: grows a slice — `indices + south_west`
- 290: grows a slice — `indices + south_east`
- 291: grows a slice — `indices + north_east`
- 292: grows a slice — `indices + south_west`
- 293: grows a slice — `indices + north_east`
- 294: grows a slice — `indices + north_west`

### distant.mara (6)

- 41: grows a slice — `text + "-"`
- 44: grows a slice — `if size < 10 do text + "0"`
- 45: grows a slice — `text + int_text(size)`
- 139: writes a slice's len — `room.file.len = 0`
- 141: writes a slice's len — `room.blocks.len = 0`
- 144: writes a slice's len — `room.model.len = 0`

### inflate.mara (6)

- 272: writes a slice's len — `output.len += 1`
- 280: writes a slice's len — `output.len += length`
- 293: writes a slice's len — `room.len = room.cap`
- 349: writes a slice's len — `output.len = written`
- 445: writes a slice's len — `room.len = 0`
- 472: writes a slice's len — `output.len = start + room.len`

### sooblivion.mara (6)

- 166: writes a slice's len — `output.len = 0`
- 382: grows a slice — `entry := next(failures)`
- 384: mismatched types for '+': ^<error> and []utf8 - did you forget to import the module that defines the overload? — `&entry^.type_name + type_name`
- 1528: grows a slice — `entry := next(counts)`
- 1540: writes a slice's len — `scratch.len = 0`
- 2333: writes a slice's len — `scratch.len = 0`

### world.mara (6)

- 40: takes from a slice — `keys := slice([:capacity]u64, storage)`
- 41: takes from a slice — `values := slice([:capacity]u32, storage)`
- 43: grows a slice — `&keys + u64(0)`
- 44: grows a slice — `&values + u32(0)`
- 429: grows a slice — `references + read_reference(plugin, file, header, body)`
- 464: grows a slice — `references + read_reference(plugin, file, header, plugin_bytes(plugin, place + HEADER_SIZE, i64(header.size)))`

### game_settings.mara (5)

- 73: grows a slice — `text + "\t"`
- 74: grows a slice — `text + name`
- 75: grows a slice — `text + " = "`
- 76: grows a slice — `text + int_text(i64(volume * 100 + 0.5))`
- 77: grows a slice — `text + "\n"`

### player.mara (5)

- 247: writes a slice's len — `room.file.len = 0`
- 248: writes a slice's len — `room.blocks.len = 0`
- 261: writes a slice's len — `room.file.len = 0`
- 262: writes a slice's len — `room.blocks.len = 0`
- 264: writes a slice's len — `bones.len = 0`

### sky.mara (5)

- 218: grows a slice — `if weather != 0 and chance > 0 do chances + Weather_Chance{weather = record_form(plugin, record, weather), chance = i64(chance)}`
- 247: writes a slice's len — `chances.len = 0`
- 287: writes a slice's len — `sounds.len = 0`
- 307: grows a slice — `sounds + Region_Sound{sound = record_form(plugin, record, sound), weathers = weathers, chance = f32(chance) / 10000000}`
- 364: writes a slice's len — `scratch.len = 0`

### menus.mara (4)

- 169: writes a slice's len — `scratch.len = 0`
- 954: grows a slice — `drawn + item`
- 1078: writes a slice's len — `lines.len = 0`
- 1096: grows a slice — `lines + Text_Line{start = start, stop = stop, width = text_width(font, text[start : stop])}`

### nif.mara (4)

- 253: takes from a slice — `type_names := slice([:type_count][]utf8, storage)`
- 254: grows a slice — `for i in 0:type_count do &type_names + read_string(reader)`
- 255: takes from a slice — `block_types := slice([:block_count]u16, storage)`
- 256: grows a slice — `for i in 0:block_count do &block_types + read_u16(reader)`

### nif_model.mara (4)

- 643: takes from a slice — `types := slice([:header.type_names.len]Block_Type, storage)`
- 644: grows a slice — `for name in header.type_names do &types + Block_Type.from_text(name)`
- 646: takes from a slice — `blocks := slice([:header.block_count]Block, storage)`
- 659: grows a slice — `&blocks + read_block(&reader, block_type)`

### particles.mara (4)

- 260: grows a slice — `vertices + Particle_Vertex{position = center - right + up, uv = [0, 0], color = color}`
- 261: grows a slice — `vertices + Particle_Vertex{position = center - right - up, uv = [0, 1], color = color}`
- 262: grows a slice — `vertices + Particle_Vertex{position = center + right - up, uv = [1, 1], color = color}`
- 263: grows a slice — `vertices + Particle_Vertex{position = center + right + up, uv = [1, 0], color = color}`

### hud.mara (2)

- 194: writes a slice's len — `scratch.len = 0`
- 220: writes a slice's len — `scratch.len = 0`

### logging.mara (2)

- 120: grows a slice — `text + more`
- 124: grows a slice — `text + more[0 : text.cap - text.len]`

### pathing.mara (2)

- 374: grows a slice — `open + item`
- 390: writes a slice's len — `open.len -= 1`

### sdl_platform.mara (2)

- 88: writes a slice's len — `pixels.len = 0`
- 90: writes a slice's len — `pixels.len = width * height * 4`

### wire.mara (2)

- 236: a call returning 2 values can't be used as a single value — destructure it first (e.g. `a, b := tcp_receive(…)?`) — `open := tcp_receive(connection, &room)?`
- 238: cannot apply 'not' to []byte: it takes a bool (or an error) — `if not open do return Closed`

### audio.mara (1)

- 135: takes from a slice — `audio.clip_room = slice([:room_size]byte, storage)`

### collision.mara (1)

- 188: grows a slice — `points + Vec3{at.x, at.y, at.z}`

### dds.mara (1)

- 211: writes a slice's len — `out.len = start + size`

### disk.mara (1)

- 72: writes a slice's len — `view.len = view.cap`

### esm.mara (1)

- 107: writes a slice's len — `scratch.len = 0`

### file_cache.mara (1)

- 188: writes a slice's len — `storage.len = start + place.size`

### game_files.mara (1)

- 77: grows a slice — `data, read_error := read_entire_file(path, storage)`

### grass.mara (1)

- 222: grows a slice — `blades + Placed_Grass{`

### walking.mara (1)

- 112: grows a slice — `nearby + Nearby{first = range.first, count = range.count, world = instance.world,`

## mara3: 10 errors

grows a slice: 9, other (most follow from one above): 1.

### lexer.mara (7)

- 124: grows a slice — `file.lines + 0`
- 126: grows a slice — `file.tokens + token`
- 129: grows a slice — `file.tokens + Token{0, file.data.len, 0, EOF}`
- 262: grows a slice — `file.lines + (here + 1)`
- 333: grows a slice — `file.lines + (file.pos + 1)`
- 349: grows a slice — `file.lines + (file.pos + 2)`
- 353: grows a slice — `file.lines + (file.pos + 1)`

### compiler.mara (3)

- 65: grows a slice — `if this_file not in files do files + this_file`
- 80: `?` requires the called function's trailing return slot to be an error type — `{&result + read_entire_file(fname, buf)?}`
- 80: grows a slice — `{&result + read_entire_file(fname, buf)?}`

