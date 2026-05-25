package warlock

import "core:fmt"
import "core:mem"
import "core:os"
import "core:strings"
import gl "vendor:OpenGL"
import stbrp "vendor:stb/rect_pack"
import stbtt "vendor:stb/truetype"

// Reload asset system after cache rebuild - resets streaming without creating new GL resources
// Use this instead of assets_init when reloading mid-run
assets_reload :: proc(a: ^Assets) {
    // Close any open file handles
    tex_stream_close(&a.tex_stream)
    mesh_stream_close(&a.mesh_stream)

    // Reset VAO (clears mesh tracking, keeps GL objects)
    vao_reset(a.vao)

    // Reset mesh count and texture count (keep default texture)
    a.mesh_count = 0
    a.texture_count = 1  // Keep DEFAULT_TEXTURE at index 0

    // Re-add primitives to VAO
    prim_names, prim_indices := primitives_init(a.vao, a.allocator)
    for i in 0..<len(prim_names) {
        a.meshes[a.mesh_count] = Mesh{
            name  = prim_names[i],
            index = prim_indices[i],
        }
        a.mesh_count += 1
    }

    // Reload cache TOC
    cache_v3_load_toc(&a.cache, a.allocator)

    // Clear and re-upload white pixel
    gl.BindTexture(gl.TEXTURE_2D_ARRAY, a.texture_id)
    white := [4]u8{255, 255, 255, 255}
    gl.TexSubImage3D(gl.TEXTURE_2D_ARRAY, 0, 0, 0, 0, 1, 1, 1,
        gl.RGBA, gl.UNSIGNED_BYTE, &white)
    gl.BindTexture(gl.TEXTURE_2D_ARRAY, 0)

    // Reset texture streaming
    texture_packer_reset(&a.tex_stream.packer)
    a.tex_stream.cache_index = 0
    a.tex_stream.current_layer = 0

    // Reserve the 1x1 white pixel at (0,0) so it won't be overwritten
    reserved: stbrp.Rect
    reserved.w = 1
    reserved.h = 1
    stbrp.pack_rects(&a.tex_stream.packer.pack_ctx, &reserved, 1)

    // Reopen texture cache file
    if file, err := os.open(CACHE_V3_TEXTURE_PATH); err == os.ERROR_NONE {
        a.tex_stream.file_handle = file
        a.tex_stream.file_open = true
    }

    // Reset mesh streaming
    a.mesh_stream.cache_index = 0
    if file, err := os.open(CACHE_V3_MODEL_PATH); err == os.ERROR_NONE {
        a.mesh_stream.file_handle = file
        a.mesh_stream.file_open = true
    }

    // Start streaming
    if a.cache.textures_valid || a.cache.models_valid {
        a.state = .Streaming
    } else {
        a.state = .Done
    }

    fmt.println("Assets reloaded - streaming", a.cache.texture_count, "textures and", a.cache.model_count, "models")
}

// Per-frame streaming tick - loads a few assets each frame
// budget: max number of textures to load this frame (1-2 recommended)
assets_tick :: proc(a: ^Assets, budget: int = 1) {
    if a.state != .Streaming do return

    textures_done := tex_stream_tick(a, budget)
    meshes_done := mesh_stream_tick(a)
    fonts_done := font_stream_tick(a)

    if textures_done && meshes_done && fonts_done {
        a.state = .Done
        tex_stream_close(&a.tex_stream)
        mesh_stream_close(&a.mesh_stream)
    }
}

// === Texture streaming internals ===

// Texture packer - packs textures into atlas, no GL calls
// Used by main thread (1 texture per frame) or async (pack until full)
Texture_Packer :: struct {
    pack_ctx: stbrp.Context,
    pack_nodes: []stbrp.Node,
    size: i32,
    is_full: bool,
}

texture_packer_init :: proc(packer: ^Texture_Packer, size: i32, allocator: mem.Allocator) {
    packer.size = size
    packer.is_full = false
    packer.pack_nodes = make([]stbrp.Node, 8192, allocator)
    stbrp.init_target(&packer.pack_ctx, size, size, raw_data(packer.pack_nodes), 8192)
}

texture_packer_reset :: proc(packer: ^Texture_Packer) {
    packer.is_full = false
    stbrp.init_target(&packer.pack_ctx, packer.size, packer.size, raw_data(packer.pack_nodes), 8192)
}

tex_stream_init :: proc(s: ^Tex_Stream, size: i32, allocator: mem.Allocator) {
    s.cache_index = 0
    s.current_layer = 0
    s.file_open = false

    // Init rect packer
    texture_packer_init(&s.packer, size, allocator)

    // Reserve the 1x1 white pixel at (0,0) so it won't be overwritten
    reserved: stbrp.Rect
    reserved.w = 1
    reserved.h = 1
    stbrp.pack_rects(&s.packer.pack_ctx, &reserved, 1)

    // Open cache file
    file, err := os.open(CACHE_V3_TEXTURE_PATH)
    if err == os.ERROR_NONE {
        s.file_handle = file
        s.file_open = true
    }
}

tex_stream_close :: proc(s: ^Tex_Stream) {
    if s.file_open {
        os.close(s.file_handle)
        s.file_open = false
    }
}

// Load up to 'budget' textures from cache, pack into atlas, upload to GPU
// Returns true when all textures are loaded
tex_stream_tick :: proc(a: ^Assets, budget: int) -> bool {
    s := &a.tex_stream
    cache := &a.cache

    if !cache.textures_valid do return true
    if !s.file_open do return true
    if s.current_layer >= ATLAS_LAYERS do return true
    if s.cache_index >= cache.texture_count do return true

    loaded := 0
    for loaded < budget && s.cache_index < cache.texture_count {
        // Load texture from cache
        pixels, img_w, img_h, ok := cache_v3_load_texture_from_handle(
            cache, s.file_handle, s.cache_index, context.temp_allocator)

        if !ok {
            s.cache_index += 1
            continue
        }

        name := cache.texture_names[s.cache_index]

        // Try to pack into current layer (no downscaling - use original size)
        rect: stbrp.Rect
        rect.w = stbrp.Coord(img_w)
        rect.h = stbrp.Coord(img_h)

        if stbrp.pack_rects(&s.packer.pack_ctx, &rect, 1) == 0 {
            // Layer full, move to next
            s.current_layer += 1
            if s.current_layer >= ATLAS_LAYERS {
                return true  // All layers full
            }
            texture_packer_reset(&s.packer)

            // Try again on new layer
            if stbrp.pack_rects(&s.packer.pack_ctx, &rect, 1) == 0 {
                // Texture too big even for empty layer, skip it
                s.cache_index += 1
                continue
            }
        }

        // Upload directly to GPU
        dst_x := i32(rect.x)
        dst_y := i32(rect.y)

        gl.BindTexture(gl.TEXTURE_2D_ARRAY, a.texture_id)
        gl.TexSubImage3D(gl.TEXTURE_2D_ARRAY, 0,
            dst_x, dst_y, i32(s.current_layer),
            img_w, img_h, 1,
            gl.RGBA, gl.UNSIGNED_BYTE,
            raw_data(pixels))
        gl.BindTexture(gl.TEXTURE_2D_ARRAY, 0)

        // Add to loaded textures
        if a.texture_count < MAX_TEXTURES {
            uv: [4]f32
            uv[0] = f32(img_w) / f32(s.packer.size)   // scale_x
            uv[1] = f32(img_h) / f32(s.packer.size)   // scale_y
            uv[2] = f32(dst_x) / f32(s.packer.size)   // offset_x
            uv[3] = f32(dst_y) / f32(s.packer.size)   // offset_y

            a.textures[a.texture_count] = Texture{
                name = name,  // points into cache, stable
                uv = uv,
                layer = s.current_layer,
            }
            a.texture_count += 1
        }

        s.cache_index += 1
        loaded += 1
    }

    return s.cache_index >= cache.texture_count
}

// === Mesh streaming internals ===

mesh_stream_init :: proc(s: ^Mesh_Stream) {
    s.cache_index = 0
    s.file_open = false

    file, err := os.open(CACHE_V3_MODEL_PATH)
    if err == os.ERROR_NONE {
        s.file_handle = file
        s.file_open = true
    }
}

mesh_stream_close :: proc(s: ^Mesh_Stream) {
    if s.file_open {
        os.close(s.file_handle)
        s.file_open = false
    }
}

// Load one mesh per frame from cache, upload to VAO
// Returns true when all meshes are loaded
mesh_stream_tick :: proc(a: ^Assets) -> bool {
    s := &a.mesh_stream
    cache := &a.cache

    if !cache.models_valid do return true
    if !s.file_open do return true
    if s.cache_index >= cache.model_count do return true

    // Load one mesh
    geom, ok := cache_v3_load_model(cache, s.cache_index, context.temp_allocator)
    if !ok {
        s.cache_index += 1
        return s.cache_index >= cache.model_count
    }

    name := cache.model_names[s.cache_index]

    // Add to VAO
    mesh_idx := vao_add_mesh(a.vao, geom)
    if mesh_idx >= 0 && a.mesh_count < MAX_MESHES {
        a.meshes[a.mesh_count] = Mesh{
            name = name,  // points into cache, stable
            index = mesh_idx,
        }
        a.mesh_count += 1
    }

    s.cache_index += 1
    return s.cache_index >= cache.model_count
}

// === Font streaming ===

// Load a default font synchronously at init time (small size for speed)
// Uses layer 0, so streamed fonts start at layer 1
load_default_font :: proc(a: ^Assets, allocator: mem.Allocator) {
    handle, err := os.open("data/fonts")
    if err != 0 do return
    defer os.close(handle)

    infos, read_err := os.read_dir(handle, -1)
    if read_err != 0 do return
    defer os.file_info_slice_delete(infos)

    // Find first TTF/OTF file
    for info in infos {
        if info.is_dir do continue

        name := info.name
        if len(name) < 4 do continue

        ext_start := strings.last_index(name, ".")
        if ext_start < 0 do continue

        ext := strings.to_lower(name[ext_start:], context.temp_allocator)
        if ext == ".ttf" || ext == ".otf" {
            filepath := strings.concatenate({"data/fonts/", name}, context.temp_allocator)

            // Load with small atlas and font size for speed
            font, pixels, ok := font_load_from_file(filepath, 512, allocator, 24.0)
            if !ok do continue

            // Upload to layer 0
            gl.BindTexture(gl.TEXTURE_2D_ARRAY, a.font_texture_id)
            gl.TexSubImage3D(gl.TEXTURE_2D_ARRAY, 0,
                0, 0, 0,
                font.w, font.h, 1,
                gl.RED, gl.UNSIGNED_BYTE, raw_data(pixels))
            gl.GenerateMipmap(gl.TEXTURE_2D_ARRAY)
            gl.BindTexture(gl.TEXTURE_2D_ARRAY, 0)

            font.layer = 0
            a.fonts[0] = font
            a.font_count = 1

            return
        }
    }
}

font_stream_init :: proc(s: ^Font_Stream, allocator: mem.Allocator) {
    s.font_files = make([dynamic]string, 0, 16, allocator)
    s.current = 0
    s.initialized = true

    // Scan fonts folder for TTF/OTF files
    scan_font_folder("data/fonts", &s.font_files, allocator)
}

scan_font_folder :: proc(dir: string, files: ^[dynamic]string, allocator: mem.Allocator) {
    handle, err := os.open(dir)
    if err != 0 do return
    defer os.close(handle)

    infos, read_err := os.read_dir(handle, -1)
    if read_err != 0 do return
    defer os.file_info_slice_delete(infos)

    for info in infos {
        if info.is_dir do continue

        name := info.name
        name_len := len(name)
        if name_len < 4 do continue

        // Check extension
        ext_start := strings.last_index(name, ".")
        if ext_start < 0 do continue

        ext := strings.to_lower(name[ext_start:], context.temp_allocator)
        if ext == ".ttf" || ext == ".otf" {
            full_path := strings.concatenate({dir, "/", name}, allocator)
            append(files, full_path)
        }
    }
}

// Load one font per frame, one layer per font
// Returns true when all fonts are loaded
font_stream_tick :: proc(a: ^Assets) -> bool {
    s := &a.font_stream

    if !s.initialized do return true
    if s.current >= len(s.font_files) do return true
    if a.font_count >= MAX_FONTS do return true

    filepath := s.font_files[s.current]

    // Load font into its own atlas layer
    font, pixels, ok := font_load_from_file(filepath, a.font_texture_size, a.allocator, FONT_SCALE)
    if !ok {
        s.current += 1
        return s.current >= len(s.font_files)
    }

    // Extract filename for name
    name := filepath
    if slash := strings.last_index(filepath, "/"); slash >= 0 {
        name = filepath[slash+1:]
    }
    if dot := strings.last_index(name, "."); dot >= 0 {
        name = name[:dot]
    }

    // Upload font bitmap to its own layer (one font per layer)
    layer := u32(a.font_count)

    gl.BindTexture(gl.TEXTURE_2D_ARRAY, a.font_texture_id)
    gl.TexSubImage3D(gl.TEXTURE_2D_ARRAY, 0,
        0, 0, i32(layer),
        font.w, font.h, 1,
        gl.RED, gl.UNSIGNED_BYTE, raw_data(pixels))
    gl.GenerateMipmap(gl.TEXTURE_2D_ARRAY)
    gl.BindTexture(gl.TEXTURE_2D_ARRAY, 0)

    font.name = strings.clone(name, a.allocator)
    font.layer = layer
    font.offset_x = 0
    font.offset_y = 0
    a.fonts[a.font_count] = font
    a.font_count += 1

    delete(pixels, context.temp_allocator)

    s.current += 1
    return s.current >= len(s.font_files)
}

// Load a font from TTF/OTF file, pack glyphs into atlas
font_load_from_file :: proc(filepath: string, atlas_size: i32, allocator: mem.Allocator, font_size: f32 = 64.0) -> (font: Font, pixels: []u8, ok: bool) {
    // Read TTF/OTF file
    ttf_data, read_ok := os.read_entire_file(filepath, allocator)
    if !read_ok do return {}, nil, false

    // Initialize font info
    if stbtt.InitFont(&font.info, raw_data(ttf_data), stbtt.GetFontOffsetForIndex(raw_data(ttf_data), 0)) == false {
        delete(ttf_data, allocator)
        return {}, nil, false
    }

    font.w = atlas_size
    font.h = atlas_size

    // Extract name from filepath
    name := filepath
    if slash := strings.last_index(filepath, "/"); slash >= 0 {
        name = filepath[slash+1:]
    }
    if dot := strings.last_index(name, "."); dot >= 0 {
        name = name[:dot]
    }
    font.name = strings.clone(name, allocator)

    // Allocate atlas pixels (temp - will be uploaded then freed)
    pixels = make([]u8, int(atlas_size * atlas_size), context.temp_allocator)

    // Pack font glyphs
    pack_ctx: stbtt.pack_context
    if stbtt.PackBegin(&pack_ctx, raw_data(pixels), atlas_size, atlas_size, 0, 1, nil) == 0 {
        delete(ttf_data, allocator)
        return {}, nil, false
    }

    first_char :: 0
    last_char :: FONT_RANGE
    char_count :: last_char - first_char

    font.packed_chars = make([]stbtt.packedchar, char_count, allocator)

    stbtt.PackFontRange(&pack_ctx, raw_data(ttf_data), 0, font_size,
        first_char, char_count, raw_data(font.packed_chars))

    stbtt.PackEnd(&pack_ctx)

    return font, pixels, true
}
