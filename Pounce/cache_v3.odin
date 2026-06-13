package warlock

import "core:mem"
import "core:os"
import "core:strings"
import "core:fmt"
import "core:path/filepath"

import stbi "vendor:stb/image"
import stbtt "vendor:stb/truetype"

// Cache V3 - Four separate append-only cache files
// Each cache has a fixed-size TOC for future growth, then append-only data
//
// File layout:
//   [Header]
//   [TOC slots: max_count * entry_size]  <- pre-allocated, sparse
//   [Data section]                        <- append-only

CACHE_V3_MODEL_PATH   :: "data/models.bin"
CACHE_V3_TEXTURE_PATH :: "data/textures.bin"
CACHE_V3_FONT_PATH    :: "data/fonts.bin"
CACHE_V3_FONT_ATLAS_PATH :: "data/font_atlases.bin"
CACHE_V3_AUDIO_PATH   :: "data/audio.bin"

CACHE_V3_MAGIC   :: u32(0x43483356)  // "CH3V"
CACHE_V3_VERSION :: u32(4)  // v4: names include subfolder path (e.g. "kenney_castle/bridge")

// Max entries per cache (TOC space pre-allocated)
CACHE_V3_MAX_MODELS       :: 256
CACHE_V3_MAX_TEXTURES     :: 1024
CACHE_V3_MAX_FONTS        :: 64
CACHE_V3_MAX_FONT_ATLASES :: 16
CACHE_V3_MAX_AUDIO        :: 512

// Average name length estimate for TOC allocation
CACHE_V3_AVG_NAME_LEN :: 48

// Header for each cache file
Cache_V3_File_Header :: struct {
    magic:       u32,
    version:     u32,
    asset_type:  u32,  // 0=model, 1=texture, 2=font, 3=audio
    count:       u32,  // current number of entries
    max_count:   u32,  // max entries (TOC slots)
    toc_offset:  u64,  // where TOC starts (right after header)
    data_offset: u64,  // where data section starts
    data_end:    u64,  // current end of data (for appending)
}

// TOC entries - fixed size with inline name buffer
// Names include subfolder path, e.g. "kenney_castle/bridge"
Cache_V3_Model_Entry :: struct {
    name:         [CACHE_V3_AVG_NAME_LEN]u8,
    name_length:  u32,
    vertex_count: u32,
    index_count:  u32,
    _pad:         u32,
    data_offset:  u64,
    data_size:    u64,
}

Cache_V3_Texture_Entry :: struct {
    name:         [CACHE_V3_AVG_NAME_LEN]u8,
    name_length:  u32,
    width:        i32,
    height:       i32,
    channels:     i32,
    data_offset:  u64,
    data_size:    u64,
}

// Font entry - references an atlas by index, stores packed_chars
Cache_V3_Font_Entry :: struct {
    name:         [CACHE_V3_AVG_NAME_LEN]u8,
    name_length:  u32,
    chars_count:  u32,
    atlas_index:  u32,  // which atlas this font belongs to
    _pad:         u32,
    data_offset:  u64,  // packed_chars data
    data_size:    u64,
}

// Font atlas entry - stores the shared texture pixels
Cache_V3_Font_Atlas_Entry :: struct {
    width:       i32,
    height:      i32,
    font_count:  u32,  // how many fonts in this atlas
    _pad:        u32,
    data_offset: u64,  // atlas pixels
    data_size:   u64,
}

Cache_V3_Audio_Entry :: struct {
    name:         [CACHE_V3_AVG_NAME_LEN]u8,
    name_length:  u32,
    sample_rate:  u32,
    channels:     u32,
    _pad:         u32,
    sample_count: u64,
    data_offset:  u64,
    data_size:    u64,
}

// Runtime cache state - loaded from all 4 TOCs
// Asset names include subfolder path, e.g. "kenney_castle/bridge"
Cache_V3 :: struct {
    // Models
    model_count:          int,
    model_names:          []string,  // includes subfolder, e.g. "kenney_castle/bridge"
    model_vertex_counts:  []u32,
    model_index_counts:   []u32,
    model_offsets:        []u64,
    model_sizes:          []u64,
    model_data_offset:    u64,

    // Textures
    texture_count:          int,
    texture_names:          []string,  // includes subfolder, e.g. "kenney_castle/bridge"
    texture_widths:         []i32,
    texture_heights:        []i32,
    texture_offsets:        []u64,
    texture_sizes:          []u64,
    texture_data_offset:    u64,

    // Fonts (individual font entries with packed_chars)
    font_count:          int,
    font_names:          []string,
    font_char_counts:    []u32,
    font_atlas_indices:  []u32,  // which atlas each font belongs to
    font_offsets:        []u64,
    font_sizes:          []u64,
    font_data_offset:    u64,

    // Font atlases (shared texture pixels)
    font_atlas_count:        int,
    font_atlas_widths:       []i32,
    font_atlas_heights:      []i32,
    font_atlas_font_counts:  []u32,
    font_atlas_offsets:      []u64,
    font_atlas_sizes:        []u64,
    font_atlas_data_offset:  u64,

    // Audio
    audio_count:         int,
    audio_names:         []string,
    audio_sample_rates:  []u32,
    audio_channels:      []u32,
    audio_sample_counts: []u64,
    audio_offsets:       []u64,
    audio_sizes:         []u64,
    audio_data_offset:   u64,

    // Validity flags per cache
    models_valid:       bool,
    textures_valid:     bool,
    fonts_valid:        bool,
    font_atlases_valid: bool,
    audio_valid:        bool,

    valid: bool,  // at least one cache loaded
}

// Load TOC from all cache files
cache_v3_load_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    cache.models_valid = cache_v3_load_model_toc(cache, allocator)
    cache.textures_valid = cache_v3_load_texture_toc(cache, allocator)
    cache.fonts_valid = cache_v3_load_font_toc(cache, allocator)
    cache.font_atlases_valid = cache_v3_load_font_atlas_toc(cache, allocator)
    cache.audio_valid = cache_v3_load_audio_toc(cache, allocator)

    cache.valid = cache.models_valid || cache.textures_valid || cache.fonts_valid || cache.audio_valid

    return cache.valid
}

// === Individual TOC loaders ===

cache_v3_load_model_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    file, err := os.open(CACHE_V3_MODEL_PATH)
    if err != os.ERROR_NONE do return false
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    bytes_read, _ := os.read(file, header_bytes)
    if bytes_read != size_of(Cache_V3_File_Header) do return false
    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION do return false
    if header.asset_type != 0 do return false  // not a model cache

    cache.model_count = int(header.count)
    cache.model_data_offset = header.data_offset

    if cache.model_count == 0 {
        return true
    }

    cache.model_names = make([]string, cache.model_count, allocator)
    cache.model_vertex_counts = make([]u32, cache.model_count, allocator)
    cache.model_index_counts = make([]u32, cache.model_count, allocator)
    cache.model_offsets = make([]u64, cache.model_count, allocator)
    cache.model_sizes = make([]u64, cache.model_count, allocator)

    os.seek(file, i64(header.toc_offset), os.SEEK_SET)

    for i in 0..<cache.model_count {
        entry: Cache_V3_Model_Entry
        entry_bytes := mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Model_Entry))
        os.read(file, entry_bytes)

        name_len := min(int(entry.name_length), CACHE_V3_AVG_NAME_LEN)
        if name_len > 0 {
            name_bytes := make([]byte, name_len, allocator)
            mem.copy(raw_data(name_bytes), &entry.name[0], name_len)
            cache.model_names[i] = string(name_bytes)
        }

        cache.model_vertex_counts[i] = entry.vertex_count
        cache.model_index_counts[i] = entry.index_count
        cache.model_offsets[i] = entry.data_offset
        cache.model_sizes[i] = entry.data_size
    }

    return true
}

cache_v3_load_texture_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    file, err := os.open(CACHE_V3_TEXTURE_PATH)
    if err != os.ERROR_NONE do return false
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    bytes_read, _ := os.read(file, header_bytes)
    if bytes_read != size_of(Cache_V3_File_Header) do return false
    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION do return false
    if header.asset_type != 1 do return false

    cache.texture_count = int(header.count)
    cache.texture_data_offset = header.data_offset

    if cache.texture_count == 0 {
        return true
    }

    cache.texture_names = make([]string, cache.texture_count, allocator)
    cache.texture_widths = make([]i32, cache.texture_count, allocator)
    cache.texture_heights = make([]i32, cache.texture_count, allocator)
    cache.texture_offsets = make([]u64, cache.texture_count, allocator)
    cache.texture_sizes = make([]u64, cache.texture_count, allocator)

    os.seek(file, i64(header.toc_offset), os.SEEK_SET)

    for i in 0..<cache.texture_count {
        entry: Cache_V3_Texture_Entry
        entry_bytes := mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Texture_Entry))
        os.read(file, entry_bytes)

        name_len := min(int(entry.name_length), CACHE_V3_AVG_NAME_LEN)
        if name_len > 0 {
            name_bytes := make([]byte, name_len, allocator)
            mem.copy(raw_data(name_bytes), &entry.name[0], name_len)
            cache.texture_names[i] = string(name_bytes)
        }

        cache.texture_widths[i] = entry.width
        cache.texture_heights[i] = entry.height
        cache.texture_offsets[i] = entry.data_offset
        cache.texture_sizes[i] = entry.data_size
    }

    return true
}

cache_v3_load_font_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    file, err := os.open(CACHE_V3_FONT_PATH)
    if err != os.ERROR_NONE do return false
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    bytes_read, _ := os.read(file, header_bytes)
    if bytes_read != size_of(Cache_V3_File_Header) do return false
    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION do return false
    if header.asset_type != 2 do return false

    if header.count == 0 {
        cache.font_count = 0
        cache.font_data_offset = header.data_offset
        return true
    }

    cache.font_count = int(header.count)
    cache.font_data_offset = header.data_offset
    cache.font_names = make([]string, cache.font_count, allocator)
    cache.font_char_counts = make([]u32, cache.font_count, allocator)
    cache.font_atlas_indices = make([]u32, cache.font_count, allocator)
    cache.font_offsets = make([]u64, cache.font_count, allocator)
    cache.font_sizes = make([]u64, cache.font_count, allocator)

    os.seek(file, i64(header.toc_offset), os.SEEK_SET)

    for i in 0..<cache.font_count {
        entry: Cache_V3_Font_Entry
        entry_bytes := mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Font_Entry))
        os.read(file, entry_bytes)

        name_len := min(int(entry.name_length), CACHE_V3_AVG_NAME_LEN)
        if name_len > 0 {
            name_bytes := make([]byte, name_len, allocator)
            mem.copy(raw_data(name_bytes), &entry.name[0], name_len)
            cache.font_names[i] = string(name_bytes)
        }

        cache.font_char_counts[i] = entry.chars_count
        cache.font_atlas_indices[i] = entry.atlas_index
        cache.font_offsets[i] = entry.data_offset
        cache.font_sizes[i] = entry.data_size
    }

    return true
}

cache_v3_load_font_atlas_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    file, err := os.open(CACHE_V3_FONT_ATLAS_PATH)
    if err != os.ERROR_NONE do return false
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    bytes_read, _ := os.read(file, header_bytes)
    if bytes_read != size_of(Cache_V3_File_Header) do return false
    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION do return false
    if header.asset_type != 4 do return false  // 4 = font atlas

    if header.count == 0 {
        cache.font_atlas_count = 0
        cache.font_atlas_data_offset = header.data_offset
        return true
    }

    cache.font_atlas_count = int(header.count)
    cache.font_atlas_data_offset = header.data_offset
    cache.font_atlas_widths = make([]i32, cache.font_atlas_count, allocator)
    cache.font_atlas_heights = make([]i32, cache.font_atlas_count, allocator)
    cache.font_atlas_font_counts = make([]u32, cache.font_atlas_count, allocator)
    cache.font_atlas_offsets = make([]u64, cache.font_atlas_count, allocator)
    cache.font_atlas_sizes = make([]u64, cache.font_atlas_count, allocator)

    os.seek(file, i64(header.toc_offset), os.SEEK_SET)

    for i in 0..<cache.font_atlas_count {
        entry: Cache_V3_Font_Atlas_Entry
        entry_bytes := mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Font_Atlas_Entry))
        os.read(file, entry_bytes)

        cache.font_atlas_widths[i] = entry.width
        cache.font_atlas_heights[i] = entry.height
        cache.font_atlas_font_counts[i] = entry.font_count
        cache.font_atlas_offsets[i] = entry.data_offset
        cache.font_atlas_sizes[i] = entry.data_size
    }

    return true
}

cache_v3_load_audio_toc :: proc(cache: ^Cache_V3, allocator: mem.Allocator) -> bool {
    file, err := os.open(CACHE_V3_AUDIO_PATH)
    if err != os.ERROR_NONE do return false
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    bytes_read, _ := os.read(file, header_bytes)
    if bytes_read != size_of(Cache_V3_File_Header) do return false
    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION do return false
    if header.asset_type != 3 do return false

    if header.count == 0 {
        cache.audio_count = 0
        cache.audio_data_offset = header.data_offset
        return true
    }

    cache.audio_count = int(header.count)
    cache.audio_data_offset = header.data_offset
    cache.audio_names = make([]string, cache.audio_count, allocator)
    cache.audio_sample_rates = make([]u32, cache.audio_count, allocator)
    cache.audio_channels = make([]u32, cache.audio_count, allocator)
    cache.audio_sample_counts = make([]u64, cache.audio_count, allocator)
    cache.audio_offsets = make([]u64, cache.audio_count, allocator)
    cache.audio_sizes = make([]u64, cache.audio_count, allocator)

    os.seek(file, i64(header.toc_offset), os.SEEK_SET)

    for i in 0..<cache.audio_count {
        entry: Cache_V3_Audio_Entry
        entry_bytes := mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Audio_Entry))
        os.read(file, entry_bytes)

        name_len := min(int(entry.name_length), CACHE_V3_AVG_NAME_LEN)
        if name_len > 0 {
            name_bytes := make([]byte, name_len, allocator)
            mem.copy(raw_data(name_bytes), &entry.name[0], name_len)
            cache.audio_names[i] = string(name_bytes)
        }

        cache.audio_sample_rates[i] = entry.sample_rate
        cache.audio_channels[i] = entry.channels
        cache.audio_sample_counts[i] = entry.sample_count
        cache.audio_offsets[i] = entry.data_offset
        cache.audio_sizes[i] = entry.data_size
    }

    return true
}

// === Find functions ===

cache_v3_find_model :: proc(cache: ^Cache_V3, query: string) -> (index: int, found: bool) {
    if !cache.models_valid do return -1, false

    best_index := -1
    best_pos := max(int)

    for i in 0..<cache.model_count {
        pos := string_match(cache.model_names[i], query)
        if pos >= 0 && pos < best_pos {
            best_pos = pos
            best_index = i
        }
    }

    return best_index, best_index >= 0
}

cache_v3_find_texture :: proc(cache: ^Cache_V3, query: string) -> (index: int, found: bool) {
    if !cache.textures_valid do return -1, false

    best_index := -1
    best_pos := max(int)

    for i in 0..<cache.texture_count {
        pos := string_match(cache.texture_names[i], query)
        if pos >= 0 && pos < best_pos {
            best_pos = pos
            best_index = i
        }
    }

    return best_index, best_index >= 0
}

cache_v3_find_font :: proc(cache: ^Cache_V3, query: string) -> (index: int, found: bool) {
    if !cache.fonts_valid do return -1, false

    best_index := -1
    best_pos := max(int)

    for i in 0..<cache.font_count {
        pos := string_match(cache.font_names[i], query)
        if pos >= 0 && pos < best_pos {
            best_pos = pos
            best_index = i
        }
    }

    return best_index, best_index >= 0
}

cache_v3_find_audio :: proc(cache: ^Cache_V3, query: string) -> (index: int, found: bool) {
    if !cache.audio_valid do return -1, false

    best_index := -1
    best_pos := max(int)

    for i in 0..<cache.audio_count {
        pos := string_match(cache.audio_names[i], query)
        if pos >= 0 && pos < best_pos {
            best_pos = pos
            best_index = i
        }
    }

    return best_index, best_index >= 0
}

// === Load individual assets ===

cache_v3_load_model :: proc(cache: ^Cache_V3, index: int, allocator: mem.Allocator) -> (geom: Mesh_Data, ok: bool) {
    if !cache.models_valid || index < 0 || index >= cache.model_count {
        return {}, false
    }

    file, err := os.open(CACHE_V3_MODEL_PATH)
    if err != os.ERROR_NONE {
        return {}, false
    }
    defer os.close(file)

    vertex_count := int(cache.model_vertex_counts[index])
    index_count := int(cache.model_index_counts[index])

    geom.vertices = make([]Vertex, vertex_count, allocator)
    geom.indices = make([]u32, index_count, allocator)

    os.seek(file, i64(cache.model_data_offset + cache.model_offsets[index]), os.SEEK_SET)

    vertex_bytes := mem.slice_to_bytes(geom.vertices)
    os.read(file, vertex_bytes)

    index_bytes := mem.slice_to_bytes(geom.indices)
    os.read(file, index_bytes)

    return geom, true
}

cache_v3_load_texture :: proc(cache: ^Cache_V3, index: int, allocator: mem.Allocator) -> (pixels: []u8, width, height: i32, ok: bool) {
    if !cache.textures_valid || index < 0 || index >= cache.texture_count {
        return nil, 0, 0, false
    }

    file, err := os.open(CACHE_V3_TEXTURE_PATH)
    if err != os.ERROR_NONE {
        return nil, 0, 0, false
    }
    defer os.close(file)

    width = cache.texture_widths[index]
    height = cache.texture_heights[index]
    size := int(cache.texture_sizes[index])

    pixels = make([]u8, size, allocator)

    os.seek(file, i64(cache.texture_data_offset + cache.texture_offsets[index]), os.SEEK_SET)
    os.read(file, pixels)

    return pixels, width, height, true
}

// Load texture using an already-open file handle (avoids open/close overhead)
cache_v3_load_texture_from_handle :: proc(
    cache: ^Cache_V3,
    file: os.Handle,
    index: int,
    allocator: mem.Allocator,
) -> (pixels: []u8, width, height: i32, ok: bool) {
    if !cache.textures_valid || index < 0 || index >= cache.texture_count {
        return nil, 0, 0, false
    }

    width = cache.texture_widths[index]
    height = cache.texture_heights[index]
    size := int(cache.texture_sizes[index])

    pixels = make([]u8, size, allocator)

    os.seek(file, i64(cache.texture_data_offset + cache.texture_offsets[index]), os.SEEK_SET)
    os.read(file, pixels)

    return pixels, width, height, true
}

// Load a font's packed_chars from cache (use cache_v3_load_font_atlas for pixels)
cache_v3_load_font :: proc(cache: ^Cache_V3, index: int, allocator: mem.Allocator) -> (packed_chars: []u8, atlas_index: u32, ok: bool) {
    if !cache.fonts_valid || index < 0 || index >= cache.font_count {
        return nil, 0, false
    }

    file, err := os.open(CACHE_V3_FONT_PATH)
    if err != os.ERROR_NONE {
        return nil, 0, false
    }
    defer os.close(file)

    size := int(cache.font_sizes[index])
    packed_chars = make([]u8, size, allocator)

    os.seek(file, i64(cache.font_data_offset + cache.font_offsets[index]), os.SEEK_SET)
    os.read(file, packed_chars)

    return packed_chars, cache.font_atlas_indices[index], true
}

// Load font atlas pixels from cache
cache_v3_load_font_atlas :: proc(cache: ^Cache_V3, index: int, allocator: mem.Allocator) -> (pixels: []u8, width, height: i32, ok: bool) {
    if !cache.font_atlases_valid || index < 0 || index >= cache.font_atlas_count {
        return nil, 0, 0, false
    }

    file, err := os.open(CACHE_V3_FONT_ATLAS_PATH)
    if err != os.ERROR_NONE {
        return nil, 0, 0, false
    }
    defer os.close(file)

    width = cache.font_atlas_widths[index]
    height = cache.font_atlas_heights[index]
    size := int(cache.font_atlas_sizes[index])

    pixels = make([]u8, size, allocator)

    os.seek(file, i64(cache.font_atlas_data_offset + cache.font_atlas_offsets[index]), os.SEEK_SET)
    os.read(file, pixels)

    return pixels, width, height, true
}

// === Append functions ===

// Append a single model to the cache (creates file if needed)
cache_v3_append_model :: proc(name: string, mesh: Mesh_Data) -> bool {
    cache_ensure_dir()

    // Calculate data size
    vertex_size := u64(len(mesh.vertices) * size_of(Vertex))
    index_size := u64(len(mesh.indices) * size_of(u32))
    data_size := vertex_size + index_size

    // Try to open existing file or create new
    file, err := os.open(CACHE_V3_MODEL_PATH, os.O_RDWR)
    if err != os.ERROR_NONE {
        // Create new cache file
        return cache_v3_create_model_cache_with_entry(name, mesh)
    }
    defer os.close(file)

    // Read header
    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    os.read(file, header_bytes)

    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION || header.asset_type != 0 {
        os.close(file)
        return cache_v3_create_model_cache_with_entry(name, mesh)
    }

    // Check if we have TOC space
    if header.count >= header.max_count {
        return false
    }

    // Calculate where to write new data
    new_data_offset := header.data_end - header.data_offset
    new_entry_index := header.count

    // Write data at end of file
    os.seek(file, i64(header.data_end), os.SEEK_SET)

    if len(mesh.vertices) > 0 {
        os.write(file, mem.slice_to_bytes(mesh.vertices))
    }
    if len(mesh.indices) > 0 {
        os.write(file, mem.slice_to_bytes(mesh.indices))
    }

    // Write TOC entry
    entry: Cache_V3_Model_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.vertex_count = u32(len(mesh.vertices))
    entry.index_count = u32(len(mesh.indices))
    entry.data_offset = new_data_offset
    entry.data_size = data_size

    toc_pos := header.toc_offset + u64(new_entry_index) * u64(size_of(Cache_V3_Model_Entry))
    os.seek(file, i64(toc_pos), os.SEEK_SET)
    os.write(file, mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Model_Entry)))

    // Update header
    header.count += 1
    header.data_end += data_size
    os.seek(file, 0, os.SEEK_SET)
    os.write(file, header_bytes)

    return true
}

// Append a single texture to the cache
cache_v3_append_texture :: proc(name: string, pixels: []u8, width, height: i32) -> bool {
    cache_ensure_dir()

    data_size := u64(len(pixels))

    file, err := os.open(CACHE_V3_TEXTURE_PATH, os.O_RDWR)
    if err != os.ERROR_NONE {
        return cache_v3_create_texture_cache_with_entry(name, pixels, width, height)
    }
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    os.read(file, header_bytes)

    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION || header.asset_type != 1 {
        os.close(file)
        return cache_v3_create_texture_cache_with_entry(name, pixels, width, height)
    }

    if header.count >= header.max_count {
        return false
    }

    new_data_offset := header.data_end - header.data_offset
    new_entry_index := header.count

    // Write data
    os.seek(file, i64(header.data_end), os.SEEK_SET)
    os.write(file, pixels)

    // Write TOC entry
    entry: Cache_V3_Texture_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.width = width
    entry.height = height
    entry.channels = 4
    entry.data_offset = new_data_offset
    entry.data_size = data_size

    toc_pos := header.toc_offset + u64(new_entry_index) * u64(size_of(Cache_V3_Texture_Entry))
    os.seek(file, i64(toc_pos), os.SEEK_SET)
    os.write(file, mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Texture_Entry)))

    // Update header
    header.count += 1
    header.data_end += data_size
    os.seek(file, 0, os.SEEK_SET)
    os.write(file, header_bytes)

    return true
}

// Append a font's packed_chars to the cache
// packed_chars_data is the raw packed_chars bytes, atlas_index references which atlas it belongs to
cache_v3_append_font :: proc(name: string, packed_chars_data: []u8, char_count: u32, atlas_index: u32) -> bool {
    cache_ensure_dir()

    data_size := u64(len(packed_chars_data))

    file, err := os.open(CACHE_V3_FONT_PATH, os.O_RDWR)
    if err != os.ERROR_NONE {
        return cache_v3_create_font_cache_with_entry(name, packed_chars_data, char_count, atlas_index)
    }
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    os.read(file, header_bytes)

    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION || header.asset_type != 2 {
        os.close(file)
        return cache_v3_create_font_cache_with_entry(name, packed_chars_data, char_count, atlas_index)
    }

    if header.count >= header.max_count {
        return false
    }

    new_data_offset := header.data_end - header.data_offset
    new_entry_index := header.count

    os.seek(file, i64(header.data_end), os.SEEK_SET)
    os.write(file, packed_chars_data)

    entry: Cache_V3_Font_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.chars_count = char_count
    entry.atlas_index = atlas_index
    entry.data_offset = new_data_offset
    entry.data_size = data_size

    toc_pos := header.toc_offset + u64(new_entry_index) * u64(size_of(Cache_V3_Font_Entry))
    os.seek(file, i64(toc_pos), os.SEEK_SET)
    os.write(file, mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Font_Entry)))

    header.count += 1
    header.data_end += data_size
    os.seek(file, 0, os.SEEK_SET)
    os.write(file, header_bytes)

    return true
}

// Append a font atlas (shared pixels) to the cache
cache_v3_append_font_atlas :: proc(pixels: []u8, width, height: i32, font_count: u32) -> (atlas_index: u32, ok: bool) {
    cache_ensure_dir()

    data_size := u64(len(pixels))

    file, err := os.open(CACHE_V3_FONT_ATLAS_PATH, os.O_RDWR)
    if err != os.ERROR_NONE {
        return cache_v3_create_font_atlas_cache_with_entry(pixels, width, height, font_count)
    }
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    os.read(file, header_bytes)

    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION || header.asset_type != 4 {
        os.close(file)
        return cache_v3_create_font_atlas_cache_with_entry(pixels, width, height, font_count)
    }

    if header.count >= header.max_count {
        return 0, false
    }

    new_data_offset := header.data_end - header.data_offset
    new_entry_index := header.count

    os.seek(file, i64(header.data_end), os.SEEK_SET)
    os.write(file, pixels)

    entry: Cache_V3_Font_Atlas_Entry
    entry.width = width
    entry.height = height
    entry.font_count = font_count
    entry.data_offset = new_data_offset
    entry.data_size = data_size

    toc_pos := header.toc_offset + u64(new_entry_index) * u64(size_of(Cache_V3_Font_Atlas_Entry))
    os.seek(file, i64(toc_pos), os.SEEK_SET)
    os.write(file, mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Font_Atlas_Entry)))

    header.count += 1
    header.data_end += data_size
    os.seek(file, 0, os.SEEK_SET)
    os.write(file, header_bytes)

    return new_entry_index, true
}

// Append a single audio clip to the cache
cache_v3_append_audio :: proc(name: string, data: []u8, sample_rate, channels: u32, sample_count: u64) -> bool {
    cache_ensure_dir()

    data_size := u64(len(data))

    file, err := os.open(CACHE_V3_AUDIO_PATH, os.O_RDWR)
    if err != os.ERROR_NONE {
        return cache_v3_create_audio_cache_with_entry(name, data, sample_rate, channels, sample_count)
    }
    defer os.close(file)

    header: Cache_V3_File_Header
    header_bytes := mem.slice_ptr(cast(^byte)&header, size_of(Cache_V3_File_Header))
    os.read(file, header_bytes)

    if header.magic != CACHE_V3_MAGIC || header.version != CACHE_V3_VERSION || header.asset_type != 3 {
        os.close(file)
        return cache_v3_create_audio_cache_with_entry(name, data, sample_rate, channels, sample_count)
    }

    if header.count >= header.max_count {
        return false
    }

    new_data_offset := header.data_end - header.data_offset
    new_entry_index := header.count

    os.seek(file, i64(header.data_end), os.SEEK_SET)
    os.write(file, data)

    entry: Cache_V3_Audio_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.sample_rate = sample_rate
    entry.channels = channels
    entry.sample_count = sample_count
    entry.data_offset = new_data_offset
    entry.data_size = data_size

    toc_pos := header.toc_offset + u64(new_entry_index) * u64(size_of(Cache_V3_Audio_Entry))
    os.seek(file, i64(toc_pos), os.SEEK_SET)
    os.write(file, mem.slice_ptr(cast(^byte)&entry, size_of(Cache_V3_Audio_Entry)))

    header.count += 1
    header.data_end += data_size
    os.seek(file, 0, os.SEEK_SET)
    os.write(file, header_bytes)

    return true
}

// === Create cache files with first entry ===

cache_v3_create_model_cache_with_entry :: proc(name: string, mesh: Mesh_Data) -> bool {
    vertex_size := u64(len(mesh.vertices) * size_of(Vertex))
    index_size := u64(len(mesh.indices) * size_of(u32))
    data_size := vertex_size + index_size

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_MODELS * size_of(Cache_V3_Model_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 0,
        count = 1,
        max_count = CACHE_V3_MAX_MODELS,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + data_size,
    }

    // Build first TOC entry
    entry: Cache_V3_Model_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.vertex_count = u32(len(mesh.vertices))
    entry.index_count = u32(len(mesh.indices))
    entry.data_offset = 0
    entry.data_size = data_size

    // Allocate buffer for header + full TOC + data
    total_size := int(data_offset + data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    // Write header
    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))

    // Write first TOC entry (rest stays zero)
    mem.copy(&buffer[toc_offset], &entry, size_of(Cache_V3_Model_Entry))

    // Write data
    offset := int(data_offset)
    if len(mesh.vertices) > 0 {
        mem.copy(&buffer[offset], raw_data(mesh.vertices), int(vertex_size))
        offset += int(vertex_size)
    }
    if len(mesh.indices) > 0 {
        mem.copy(&buffer[offset], raw_data(mesh.indices), int(index_size))
    }

    return os.write_entire_file(CACHE_V3_MODEL_PATH, buffer)
}

cache_v3_create_texture_cache_with_entry :: proc(name: string, pixels: []u8, width, height: i32) -> bool {
    data_size := u64(len(pixels))

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_TEXTURES * size_of(Cache_V3_Texture_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 1,
        count = 1,
        max_count = CACHE_V3_MAX_TEXTURES,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + data_size,
    }

    entry: Cache_V3_Texture_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.width = width
    entry.height = height
    entry.channels = 4
    entry.data_offset = 0
    entry.data_size = data_size

    total_size := int(data_offset + data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))
    mem.copy(&buffer[toc_offset], &entry, size_of(Cache_V3_Texture_Entry))
    mem.copy(&buffer[data_offset], raw_data(pixels), len(pixels))

    return os.write_entire_file(CACHE_V3_TEXTURE_PATH, buffer)
}

cache_v3_create_font_cache_with_entry :: proc(name: string, packed_chars_data: []u8, char_count: u32, atlas_index: u32) -> bool {
    data_size := u64(len(packed_chars_data))

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_FONTS * size_of(Cache_V3_Font_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 2,
        count = 1,
        max_count = CACHE_V3_MAX_FONTS,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + data_size,
    }

    entry: Cache_V3_Font_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.chars_count = char_count
    entry.atlas_index = atlas_index
    entry.data_offset = 0
    entry.data_size = data_size

    total_size := int(data_offset + data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))
    mem.copy(&buffer[toc_offset], &entry, size_of(Cache_V3_Font_Entry))
    mem.copy(&buffer[data_offset], raw_data(packed_chars_data), len(packed_chars_data))

    return os.write_entire_file(CACHE_V3_FONT_PATH, buffer)
}

cache_v3_create_font_atlas_cache_with_entry :: proc(pixels: []u8, width, height: i32, font_count: u32) -> (atlas_index: u32, ok: bool) {
    data_size := u64(len(pixels))

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_FONT_ATLASES * size_of(Cache_V3_Font_Atlas_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 4,  // 4 = font atlas
        count = 1,
        max_count = CACHE_V3_MAX_FONT_ATLASES,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + data_size,
    }

    entry: Cache_V3_Font_Atlas_Entry
    entry.width = width
    entry.height = height
    entry.font_count = font_count
    entry.data_offset = 0
    entry.data_size = data_size

    total_size := int(data_offset + data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))
    mem.copy(&buffer[toc_offset], &entry, size_of(Cache_V3_Font_Atlas_Entry))
    mem.copy(&buffer[data_offset], raw_data(pixels), len(pixels))

    return 0, os.write_entire_file(CACHE_V3_FONT_ATLAS_PATH, buffer)  // First atlas is index 0
}

cache_v3_create_audio_cache_with_entry :: proc(name: string, data: []u8, sample_rate, channels: u32, sample_count: u64) -> bool {
    data_size := u64(len(data))

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_AUDIO * size_of(Cache_V3_Audio_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 3,
        count = 1,
        max_count = CACHE_V3_MAX_AUDIO,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + data_size,
    }

    entry: Cache_V3_Audio_Entry
    name_len := min(len(name), CACHE_V3_AVG_NAME_LEN)
    mem.copy(&entry.name[0], raw_data(name), name_len)
    entry.name_length = u32(name_len)
    entry.sample_rate = sample_rate
    entry.channels = channels
    entry.sample_count = sample_count
    entry.data_offset = 0
    entry.data_size = data_size

    total_size := int(data_offset + data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))
    mem.copy(&buffer[toc_offset], &entry, size_of(Cache_V3_Audio_Entry))
    mem.copy(&buffer[data_offset], raw_data(data), len(data))

    return os.write_entire_file(CACHE_V3_AUDIO_PATH, buffer)
}

// === Batch save (for initial population) ===

// Save all models at once (creates new cache file)
cache_v3_save_models :: proc(models: []Mesh_Data, names: []string) -> bool {
    if len(models) == 0 do return true
    if len(models) != len(names) do return false

    cache_ensure_dir()

    // Calculate total data size
    total_data_size: u64 = 0
    for m in models {
        total_data_size += u64(len(m.vertices) * size_of(Vertex))
        total_data_size += u64(len(m.indices) * size_of(u32))
    }

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_MODELS * size_of(Cache_V3_Model_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 0,
        count = u32(len(models)),
        max_count = CACHE_V3_MAX_MODELS,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + total_data_size,
    }

    total_size := int(data_offset + total_data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))

    // Write TOC entries and data
    current_data_offset: u64 = 0
    toc_write_pos := int(toc_offset)
    data_write_pos := int(data_offset)

    for m, i in models {
        vertex_size := u64(len(m.vertices) * size_of(Vertex))
        index_size := u64(len(m.indices) * size_of(u32))

        entry: Cache_V3_Model_Entry
        name_len := min(len(names[i]), CACHE_V3_AVG_NAME_LEN)
        mem.copy(&entry.name[0], raw_data(names[i]), name_len)
        entry.name_length = u32(name_len)
        entry.vertex_count = u32(len(m.vertices))
        entry.index_count = u32(len(m.indices))
        entry.data_offset = current_data_offset
        entry.data_size = vertex_size + index_size

        mem.copy(&buffer[toc_write_pos], &entry, size_of(Cache_V3_Model_Entry))
        toc_write_pos += size_of(Cache_V3_Model_Entry)

        if len(m.vertices) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(m.vertices), int(vertex_size))
            data_write_pos += int(vertex_size)
        }
        if len(m.indices) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(m.indices), int(index_size))
            data_write_pos += int(index_size)
        }

        current_data_offset += vertex_size + index_size
    }

    return os.write_entire_file(CACHE_V3_MODEL_PATH, buffer)
}

// Save all textures at once
cache_v3_save_textures :: proc(textures: []Cache_V3_Texture_Data, names: []string) -> bool {
    if len(textures) == 0 do return true
    if len(textures) != len(names) do return false

    cache_ensure_dir()

    total_data_size: u64 = 0
    for t in textures {
        total_data_size += u64(len(t.pixels))
    }

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_TEXTURES * size_of(Cache_V3_Texture_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 1,
        count = u32(len(textures)),
        max_count = CACHE_V3_MAX_TEXTURES,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + total_data_size,
    }

    total_size := int(data_offset + total_data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))

    current_data_offset: u64 = 0
    toc_write_pos := int(toc_offset)
    data_write_pos := int(data_offset)

    for t, i in textures {
        entry: Cache_V3_Texture_Entry
        name_len := min(len(names[i]), CACHE_V3_AVG_NAME_LEN)
        mem.copy(&entry.name[0], raw_data(names[i]), name_len)
        entry.name_length = u32(name_len)
        entry.width = t.width
        entry.height = t.height
        entry.channels = 4
        entry.data_offset = current_data_offset
        entry.data_size = u64(len(t.pixels))

        mem.copy(&buffer[toc_write_pos], &entry, size_of(Cache_V3_Texture_Entry))
        toc_write_pos += size_of(Cache_V3_Texture_Entry)

        if len(t.pixels) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(t.pixels), len(t.pixels))
            data_write_pos += len(t.pixels)
        }

        current_data_offset += u64(len(t.pixels))
    }

    return os.write_entire_file(CACHE_V3_TEXTURE_PATH, buffer)
}

// Helper structs
Cache_V3_Texture_Data :: struct {
    pixels: []u8,
    width:  i32,
    height: i32,
}

// Texture data for batch saving - name includes subfolder path
Cache_V3_Texture_Data_Named :: struct {
    pixels: []u8,
    width:  i32,
    height: i32,
    name:   string,  // e.g. "kenney_castle/bridge"
}

// Model data for batch saving - name includes subfolder path
Cache_V3_Model_Data_Named :: struct {
    mesh: Mesh_Data,
    name: string,  // e.g. "kenney_castle/bridge"
}

// Save textures with names (names include subfolder path)
cache_v3_save_textures_named :: proc(textures: []Cache_V3_Texture_Data_Named) -> bool {
    if len(textures) == 0 do return true

    cache_ensure_dir()

    total_data_size: u64 = 0
    for t in textures {
        total_data_size += u64(len(t.pixels))
    }

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_TEXTURES * size_of(Cache_V3_Texture_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 1,
        count = u32(len(textures)),
        max_count = CACHE_V3_MAX_TEXTURES,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + total_data_size,
    }

    total_size := int(data_offset + total_data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))

    current_data_offset: u64 = 0
    toc_write_pos := int(toc_offset)
    data_write_pos := int(data_offset)

    for t in textures {
        entry: Cache_V3_Texture_Entry
        name_len := min(len(t.name), CACHE_V3_AVG_NAME_LEN)
        mem.copy(&entry.name[0], raw_data(t.name), name_len)
        entry.name_length = u32(name_len)
        entry.width = t.width
        entry.height = t.height
        entry.data_offset = current_data_offset
        entry.data_size = u64(len(t.pixels))

        mem.copy(&buffer[toc_write_pos], &entry, size_of(Cache_V3_Texture_Entry))
        toc_write_pos += size_of(Cache_V3_Texture_Entry)

        if len(t.pixels) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(t.pixels), len(t.pixels))
            data_write_pos += len(t.pixels)
        }

        current_data_offset += u64(len(t.pixels))
    }

    return os.write_entire_file(CACHE_V3_TEXTURE_PATH, buffer)
}

// Save models with names (names include subfolder path)
cache_v3_save_models_named :: proc(models: []Cache_V3_Model_Data_Named) -> bool {
    if len(models) == 0 do return true

    cache_ensure_dir()

    total_data_size: u64 = 0
    for m in models {
        total_data_size += u64(len(m.mesh.vertices) * size_of(Vertex))
        total_data_size += u64(len(m.mesh.indices) * size_of(u32))
    }

    toc_offset := u64(size_of(Cache_V3_File_Header))
    toc_size := u64(CACHE_V3_MAX_MODELS * size_of(Cache_V3_Model_Entry))
    data_offset := toc_offset + toc_size

    header := Cache_V3_File_Header{
        magic = CACHE_V3_MAGIC,
        version = CACHE_V3_VERSION,
        asset_type = 0,
        count = u32(len(models)),
        max_count = CACHE_V3_MAX_MODELS,
        toc_offset = toc_offset,
        data_offset = data_offset,
        data_end = data_offset + total_data_size,
    }

    total_size := int(data_offset + total_data_size)
    buffer := make([]byte, total_size, context.temp_allocator)

    mem.copy(&buffer[0], &header, size_of(Cache_V3_File_Header))

    current_data_offset: u64 = 0
    toc_write_pos := int(toc_offset)
    data_write_pos := int(data_offset)

    for m in models {
        vertex_size := u64(len(m.mesh.vertices) * size_of(Vertex))
        index_size := u64(len(m.mesh.indices) * size_of(u32))

        entry: Cache_V3_Model_Entry
        name_len := min(len(m.name), CACHE_V3_AVG_NAME_LEN)
        mem.copy(&entry.name[0], raw_data(m.name), name_len)
        entry.name_length = u32(name_len)
        entry.vertex_count = u32(len(m.mesh.vertices))
        entry.index_count = u32(len(m.mesh.indices))
        entry.data_offset = current_data_offset
        entry.data_size = vertex_size + index_size

        mem.copy(&buffer[toc_write_pos], &entry, size_of(Cache_V3_Model_Entry))
        toc_write_pos += size_of(Cache_V3_Model_Entry)

        if len(m.mesh.vertices) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(m.mesh.vertices), int(vertex_size))
            data_write_pos += int(vertex_size)
        }
        if len(m.mesh.indices) > 0 {
            mem.copy(&buffer[data_write_pos], raw_data(m.mesh.indices), int(index_size))
            data_write_pos += int(index_size)
        }

        current_data_offset += vertex_size + index_size
    }

    return os.write_entire_file(CACHE_V3_MODEL_PATH, buffer)
}

cache_ensure_dir :: proc() {
    if !os.exists(DATA_PATH) {
        os.make_directory(DATA_PATH)
    }
}

// Asset info for cache building - path is full path, name is relative (subfolder/stem)
Cache_V3_Asset_Info :: struct {
    path: string,  // full path like "data/models/kenney_castle/bridge.glb"
    name: string,  // relative name like "kenney_castle/bridge"
}

// Rebuild cache from data folder
// Scans data/models and data/textures, stores names with subfolder path
// This is a blocking operation, call it from a hotkey
cache_v3_rebuild :: proc() {
    fmt.println("Building cache from data/ folder...")

    tex_infos := make([dynamic]Cache_V3_Asset_Info, context.temp_allocator)
    model_infos := make([dynamic]Cache_V3_Asset_Info, context.temp_allocator)

    // Scan models folder
    scan_folder_for_cache("data/models", []string{".glb", ".gltf"}, &model_infos)

    // Scan textures folder
    scan_folder_for_cache("data/textures", []string{".png", ".jpg", ".jpeg", ".tga", ".bmp"}, &tex_infos)

    // Also scan models folder for textures (embedded textures)
    scan_folder_for_cache("data/models", []string{".png", ".jpg", ".jpeg", ".tga", ".bmp"}, &tex_infos)

    fmt.println("  Found", len(tex_infos), "textures")
    fmt.println("  Found", len(model_infos), "models")

    // Load textures
    textures := make([dynamic]Cache_V3_Texture_Data_Named, context.temp_allocator)

    for info in tex_infos {
        fname_cstr := strings.clone_to_cstring(info.path, context.temp_allocator)
        img_w, img_h, img_ch: i32
        pixels := stbi.load(fname_cstr, &img_w, &img_h, &img_ch, 4)

        if pixels != nil {
            size := int(img_w * img_h * 4)
            pixel_copy := make([]u8, size, context.temp_allocator)
            mem.copy(raw_data(pixel_copy), pixels, size)
            stbi.image_free(pixels)

            append(&textures, Cache_V3_Texture_Data_Named{
                pixels = pixel_copy,
                width  = img_w,
                height = img_h,
                name   = info.name,
            })
            fmt.println("    Loaded texture:", info.name)
        } else {
            fmt.println("    Failed to load texture:", info.path)
        }
    }

    // Load models
    models := make([dynamic]Cache_V3_Model_Data_Named, context.temp_allocator)
    failed_models := 0

    for info in model_infos {
        geom, ok := gltf_load_single(info.path, false)
        if ok {
            append(&models, Cache_V3_Model_Data_Named{
                mesh = geom,
                name = info.name,
            })
            fmt.println("    Loaded model:", info.name)
        } else {
            fmt.println("    Failed to load model:", info.path)
            failed_models += 1
        }
    }

    if failed_models > 0 {
        fmt.println("  Failed to load", failed_models, "models.")
        fmt.println("  This is often caused by models exported with UniGLTF (Unity VRM exporter).")
    }

    fmt.println("  Total loaded:", len(textures), "textures,", len(models), "models")

    // Save to cache
    tex_ok := cache_v3_save_textures_named(textures[:])
    model_ok := cache_v3_save_models_named(models[:])

    if tex_ok && model_ok {
        fmt.println("Cache build complete!")
    } else {
        fmt.println("Cache build FAILED - textures:", tex_ok, "models:", model_ok)
    }
}

// Scan a folder and subfolders for files with given extensions
// Stores name as "subfolder/stem" or just "stem" for root files
scan_folder_for_cache :: proc(
    base_path: string,
    extensions: []string,
    infos: ^[dynamic]Cache_V3_Asset_Info,
) {
    handle, err := os.open(base_path)
    if err != os.ERROR_NONE {
        fmt.println("    Warning: Could not open folder:", base_path)
        return
    }
    defer os.close(handle)

    files, _ := os.read_dir(handle, -1, context.temp_allocator)

    for fi in files {
        if fi.is_dir {
            // Scan subfolder
            subfolder_path := strings.concatenate({base_path, "/", fi.name}, context.temp_allocator)
            scan_subfolder_for_cache(subfolder_path, fi.name, extensions, infos)
        } else {
            // File in root
            ext := strings.to_lower(filepath.ext(fi.name), context.temp_allocator)
            for e in extensions {
                if ext == e {
                    full_path := strings.concatenate({base_path, "/", fi.name}, context.temp_allocator)
                    append(infos, Cache_V3_Asset_Info{
                        path = full_path,
                        name = filepath.stem(fi.name),
                    })
                    break
                }
            }
        }
    }
}

// Scan a subfolder for files, storing names as "subfolder/stem"
scan_subfolder_for_cache :: proc(
    folder_path: string,
    subfolder_name: string,
    extensions: []string,
    infos: ^[dynamic]Cache_V3_Asset_Info,
) {
    handle, err := os.open(folder_path)
    if err != os.ERROR_NONE do return
    defer os.close(handle)

    files, _ := os.read_dir(handle, -1, context.temp_allocator)

    for fi in files {
        if fi.is_dir do continue

        ext := strings.to_lower(filepath.ext(fi.name), context.temp_allocator)
        for e in extensions {
            if ext == e {
                full_path := strings.concatenate({folder_path, "/", fi.name}, context.temp_allocator)
                // Name includes subfolder: "kenney_castle/bridge"
                name := strings.concatenate({subfolder_name, "/", filepath.stem(fi.name)}, context.temp_allocator)
                append(infos, Cache_V3_Asset_Info{
                    path = full_path,
                    name = name,
                })
                break
            }
        }
    }
}

