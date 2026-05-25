package warlock

import stbtt "vendor:stb/truetype"

// === Convenience functions for Visual ===

// Apply a texture to a Visual by query - assigns immediately if found, otherwise stores name for resolution
set_texture :: proc(a: ^Assets, v: ^Visual, query: string) {
    if tx, ok := get_texture(a, query); ok {
        v.texture = tx
    } else {
        v.texture.name = query
    }
}

// Apply a mesh to a Visual by query - assigns immediately if found, otherwise stores name for resolution
set_mesh :: proc(a: ^Assets, v: ^Visual, query: string) {
    if m, ok := get_mesh(a, query); ok {
        v.mesh = m
    } else {
        v.mesh.name = query
    }
}

// Apply both texture and mesh to a Visual
set_visual :: proc(a: ^Assets, v: ^Visual, mesh_query, texture_query: string) {
    set_mesh(a, v, mesh_query)
    set_texture(a, v, texture_query)
}


// Glyph info for rendering - UV coords and positioning
Glyph_Info :: struct {
    uv: [4]f32,        // [scale_x, scale_y, offset_x, offset_y] like textures
    size: [2]f32,      // width, height in pixels
    offset: [2]f32,    // x, y offset from cursor position
    advance: f32,      // how far to move cursor after this glyph
}

// Get glyph rendering info for a character from a font
// Uses GetPackedQuad for proper UV coordinate handling
get_glyph :: proc(font: ^Font, char: rune, atlas_size: f32) -> Glyph_Info {
    if font == nil do return {}

    xpos, ypos: f32 = 0, 0
    q: stbtt.aligned_quad

    stbtt.GetPackedQuad(
        raw_data(font.packed_chars),
        font.w, font.h,
        i32(char),
        &xpos, &ypos,
        &q,
        true)

    // UV coords from GetPackedQuad
    // Both scale values are negative (s0-s1, t0-t1) to work with shader's UV flip
    scale_x := q.s0 - q.s1
    scale_y := q.t0 - q.t1
    offset_x := q.s1
    offset_y := q.t1

    // Character dimensions
    char_width := q.x1 - q.x0
    char_height := q.y1 - q.y0

    return Glyph_Info{
        uv = {scale_x, scale_y, offset_x, offset_y},
        size = {char_width, char_height},
        offset = {q.x0, q.y0},
        advance = xpos,
    }
}

// Resolve a Glyph's font reference - looks up font by name, gets glyph info for letter
// Only resolves once - sets resolve=false after successful resolution
// Returns true if fully resolved, false if still waiting for assets
glyph_resolve :: proc(a: ^Assets, g: ^Glyph) -> bool {
    if !g.visual.resolve do return true  // Already resolved
    if g.visual.font == "" do return true  // No font needed

    font := get_font(a, g.visual.font)
    if font == nil do return false  // Font not loaded yet

    // Get glyph info for the letter
    info := get_glyph(font, g.letter, f32(a.font_texture_size))
    if info.uv == {} do return false  // Invalid glyph

    // Apply UV coords and layer to the texture
    g.visual.texture.uv = info.uv
    g.visual.texture.layer = font.layer

    // Update scale if it was set to zero (created before font was loaded)
    // Preserve the z scale and any uniform scaling factor
    if g.obj.scale.x == 0 || g.obj.scale.y == 0 {
        // Use z as the uniform scale factor (or 1 if also zero)
        uniform_scale := g.obj.scale.z if g.obj.scale.z > 0 else 1.0
        g.obj.scale.x = info.size[0] * uniform_scale
        g.obj.scale.y = info.size[1] * uniform_scale
    }

    // Resolve mesh too
    mesh_resolved := g.visual.mesh.name == ""
    if !mesh_resolved {
        if m, ok := get_mesh(a, g.visual.mesh.name); ok {
            g.visual.mesh = m
            mesh_resolved = true
        }
    }
    if mesh_resolved {
        g.visual.resolve = false
        return true
    }
    return false
}

// Resolve a Visual's string references to actual assets
// Only resolves once - sets resolve=false after successful resolution
// Returns true if fully resolved, false if still waiting for assets
visual_resolve :: proc(a: ^Assets, v: ^Visual) -> bool {
    if !v.resolve do return true  // Already resolved

    // Empty name = intentionally left empty, consider resolved
    mesh_resolved := v.mesh.name == ""
    texture_resolved := v.texture.name == ""

    if !mesh_resolved {
        if m, ok := get_mesh(a, v.mesh.name); ok {
            v.mesh = m
            mesh_resolved = true
        }
    }

    if !texture_resolved {
        if tx, ok := get_texture(a, v.texture.name); ok {
            v.texture = tx
            texture_resolved = true
        }
    }

    if mesh_resolved && texture_resolved {
        v.resolve = false
        return true
    }
    return false
}


// Unresolve a Visual - look up asset names from current indices
visual_unresolve :: proc(a: ^Assets, v: ^Visual) {
    // Find mesh name from index
    for i in 0..<a.mesh_count {
        if a.meshes[i].index == v.mesh.index {
            v.mesh.name = a.meshes[i].name
            break
        }
    }

    // Find texture name from layer and uv
    for i in 0..<a.texture_count {
        if a.textures[i].layer == v.texture.layer && a.textures[i].uv == v.texture.uv {
            v.texture.name = a.textures[i].name
            break
        }
    }
}
