// Vertex (same as before, minus texture stuff)
#version 330 core
layout (location = 0) in vec3 vertex;
layout (location = 1) in mat4 mx;
layout (location = 7) in vec4 instance_color;

out vec4 v_color;

void main() {
    v_color = instance_color;
    gl_Position = mx * vec4(vertex, 1.0);
}

// Fragment
#version 330 core
in vec4 v_color;
out vec4 color;

void main() {
    color = v_color;
}
