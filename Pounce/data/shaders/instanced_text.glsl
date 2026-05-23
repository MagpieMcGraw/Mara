#version 330 core
layout (location = 0) in vec3 vertex;
layout (location = 8) in vec2 vertex_uv;

layout (location = 1) in mat4 mx;
layout (location = 5) in vec4 tex_coords;
layout (location = 7) in vec3 instance_color;
layout (location = 10) in uint instance_layer;

out vec2 tx_coords;
out vec3 v_color;
flat out uint v_layer;

void main()
{
    vec2 scale = vec2(tex_coords.xy);
    vec2 offset = vec2(tex_coords.zw);

    // Flip V only for text (stbtt packs with top-left origin, OpenGL uses bottom-left)
    vec2 flipped_uv = vec2(vertex_uv.x, 1.0 - vertex_uv.y);

    // Combine per-vertex UV (0-1 per face) with instance tex_coords (atlas selection)
    // Final atlas UV = flipped_uv * scale + offset
    tx_coords = vec2(offset + flipped_uv * scale);

    v_color = instance_color;
    v_layer = instance_layer;

    mat4 mvp_matrix = mx;
    gl_Position = mvp_matrix * vec4(vertex.xyz, 1.0);
}

#version 330 core

in vec2 tx_coords;
in vec3 v_color;
flat in uint v_layer;

out vec4 color;

uniform sampler2DArray base_text;

void main()
{
  // Font atlas is single-channel (GL_RED) - glyph data is in red channel
  float glyph = texture(base_text, vec3(tx_coords, float(v_layer))).r;
  if(glyph < 0.1)
    discard;
  // Apply color to the glyph
  color = vec4(v_color, glyph);
}