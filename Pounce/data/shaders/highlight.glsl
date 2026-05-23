#version 330 core
layout (location = 0) in vec3 vertex;

layout (location = 1) in mat4 mx;
layout (location = 7) in vec3 instance_color;

out vec3 v_color;

void main()
{
    v_color = instance_color;
    gl_Position = mx * vec4(vertex.xyz, 1.0);
}

#version 330 core

in vec3 v_color;

out vec4 color;

void main()
{
    color = vec4(v_color, 1.0);
}
