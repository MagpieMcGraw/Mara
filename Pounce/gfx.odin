package warlock

import "base:intrinsics"
import "core:fmt"
import "core:mem"
import "core:strings"
import "core:math"
import "core:math/linalg"
import gl "vendor:OpenGL"

// Vertex data for meshes
Vertex :: struct {
	position: [3]f32,
	normal:   [3]f32,
	uv:       [2]f32,
}

// Mesh_Data represents raw mesh data (no OpenGL resources)
Mesh_Data :: struct {
	vertices: []Vertex,
	indices:  []u32,
}

// Clean up geometry resources
mesh_data_destroy :: proc(geometry: ^Mesh_Data) {
	delete(geometry.vertices)
	delete(geometry.indices)
}

// Instance data for instanced rendering
Instance :: struct {
	mvp_matrix: linalg.Matrix4f32,
	tex_coords: [4]f32,
	color: [3]f32,
	layer: u32,           // texture array layer index
}

// VAO_Mesh holds metadata about where geometry is in the VBO/EBO
VAO_Mesh :: struct {
	first_index: u32,
	index_count: u32,
	base_vertex: i32,
}

MAX_VAO_MESHES :: 512

// VAO_State tracks the state of a unified VAO buffer for incremental updates
VAO_State :: struct {
	vao:            u32,
	vertex_vbo:     u32,
	ebo:            u32,
	instance_vbo:   u32,

	// Current offsets (where next geometry will be written)
	vertex_offset:  int,
	index_offset:   int,

	// Capacity (pre-allocated sizes)
	max_vertices:   int,
	max_indices:    int,
	max_instances:  int,

	// Mesh tracking
	meshes:         [MAX_VAO_MESHES]VAO_Mesh,
	mesh_count:     int,
}

// Create a VAO with pre-allocated buffer space for vertices, indices, and instances
// Returns the VAO state which can be used for incremental geometry additions
vao_create :: proc(max_vertices: int, max_indices: int, max_instances: int) -> VAO_State {
	state: VAO_State
	state.max_vertices = max_vertices
	state.max_indices = max_indices
	state.max_instances = max_instances
	state.vertex_offset = 0
	state.index_offset = 0

	// Create OpenGL objects
	gl.GenVertexArrays(1, &state.vao)
	gl.GenBuffers(1, &state.vertex_vbo)
	gl.GenBuffers(1, &state.ebo)
	gl.GenBuffers(1, &state.instance_vbo)

	gl.BindVertexArray(state.vao)

	// Pre-allocate vertex buffer (no data yet)
	gl.BindBuffer(gl.ARRAY_BUFFER, state.vertex_vbo)
	gl.BufferData(gl.ARRAY_BUFFER,
				  max_vertices * size_of(Vertex),
				  nil,
				  gl.STATIC_DRAW)

	// Pre-allocate index buffer (no data yet)
	gl.BindBuffer(gl.ELEMENT_ARRAY_BUFFER, state.ebo)
	gl.BufferData(gl.ELEMENT_ARRAY_BUFFER,
				  max_indices * size_of(u32),
				  nil,
				  gl.STATIC_DRAW)

	// Vertex attributes (per-vertex)
	// Position (location 0)
	gl.EnableVertexAttribArray(0)
	gl.VertexAttribPointer(0, 3, gl.FLOAT, gl.FALSE, size_of(Vertex), 0)

	// Normal (location 6)
	gl.EnableVertexAttribArray(6)
	gl.VertexAttribPointer(6, 3, gl.FLOAT, gl.FALSE, size_of(Vertex), size_of([3]f32))

	// UV (location 8)
	gl.EnableVertexAttribArray(8)
	gl.VertexAttribPointer(8, 2, gl.FLOAT, gl.FALSE, size_of(Vertex), size_of([3]f32) + size_of([3]f32))

	// Setup instance buffer
	gl.BindBuffer(gl.ARRAY_BUFFER, state.instance_vbo)
	gl.BufferData(gl.ARRAY_BUFFER,
				  max_instances * size_of(Instance),
				  nil,
				  gl.DYNAMIC_DRAW)

	// Instance attributes (per-instance)
	stride := i32(size_of(Instance))

	// MVP Matrix (locations 1-4) - each column is a vec4
	for i in 0..<4 {
		loc := u32(1 + i)
		offset := uintptr(i * size_of(linalg.Vector4f32))
		gl.EnableVertexAttribArray(loc)
		gl.VertexAttribPointer(loc, 4, gl.FLOAT, gl.FALSE, stride, offset)
		gl.VertexAttribDivisor(loc, 1)
	}

	// Texture coords (location 5)
	gl.EnableVertexAttribArray(5)
	gl.VertexAttribPointer(5, 4, gl.FLOAT, gl.FALSE, stride, size_of(linalg.Matrix4f32))
	gl.VertexAttribDivisor(5, 1)

	// Color (location 7) - vec3
	gl.EnableVertexAttribArray(7)
	gl.VertexAttribPointer(7, 3, gl.FLOAT, gl.FALSE, stride, size_of(linalg.Matrix4f32) + size_of([4]f32))
	gl.VertexAttribDivisor(7, 1)

	// Layer (location 10) - uint, texture array layer index
	gl.EnableVertexAttribArray(10)
	gl.VertexAttribIPointer(10, 1, gl.UNSIGNED_INT, stride, size_of(linalg.Matrix4f32) + size_of([4]f32) + size_of([3]f32))
	gl.VertexAttribDivisor(10, 1)

	gl.BindVertexArray(0)

	return state
}

// Add a geometry to the VAO, returns the mesh index
// Returns -1 if there's not enough space
vao_add_mesh :: proc(state: ^VAO_State, geom: Mesh_Data) -> int {
	vertex_count := len(geom.vertices)
	index_count := len(geom.indices)

	// Check if we have space
	if state.vertex_offset + vertex_count > state.max_vertices {
		fmt.eprintln("VAO: Not enough vertex space!")
		return 0
	}
	if state.index_offset + index_count > state.max_indices {
		fmt.eprintln("VAO: Not enough index space!")
		return 0
	}

	// Create mesh metadata
	mesh := VAO_Mesh{
		first_index = u32(state.index_offset),
		index_count = u32(index_count),
		base_vertex = i32(state.vertex_offset),
	}

	// Upload vertex data at current offset
	gl.BindBuffer(gl.ARRAY_BUFFER, state.vertex_vbo)
	gl.BufferSubData(gl.ARRAY_BUFFER,
					 state.vertex_offset * size_of(Vertex),
					 vertex_count * size_of(Vertex),
					 raw_data(geom.vertices))

	// Upload index data at current offset
	gl.BindBuffer(gl.ELEMENT_ARRAY_BUFFER, state.ebo)
	gl.BufferSubData(gl.ELEMENT_ARRAY_BUFFER,
					 state.index_offset * size_of(u32),
					 index_count * size_of(u32),
					 raw_data(geom.indices))

	// Update offsets
	state.vertex_offset += vertex_count
	state.index_offset += index_count

	// Add to mesh list and return index
	if state.mesh_count >= MAX_VAO_MESHES {
		fmt.eprintln("VAO: Mesh limit reached!")
		return 0
	}
	mesh_index := state.mesh_count
	state.meshes[mesh_index] = mesh
	state.mesh_count += 1

	return mesh_index
}

// Add multiple geometries to the VAO at once
// Returns slice of mesh indices (caller should not free)
vao_add_meshes :: proc(state: ^VAO_State, geometries: []Mesh_Data) -> []int {
	indices := make([]int, len(geometries))
	for geom, i in geometries {
		indices[i] = vao_add_mesh(state, geom)
	}
	return indices
}

// Reset VAO state for reloading - clears offsets and mesh list but keeps GL resources
// Use this when reloading assets mid-run to avoid leaking GL objects
vao_reset :: proc(state: ^VAO_State) {
	state.vertex_offset = 0
	state.index_offset = 0
	state.mesh_count = 0
}

// DrawCommand for MultiDrawIndirect
DrawCommand :: struct {
	index_count: u32,      // Number of indices to draw
	instance_count: u32,   // Number of instances to draw
	first_index: u32,      // Starting index in the EBO
	base_vertex: i32,      // Offset added to each index (signed!)
	base_instance: u32,    // Starting instance in the instance buffer
}

// Mesh_Batch holds instances for a single mesh type during batching
Mesh_Batch :: struct {
	mesh_index: int,
	instances: [dynamic]Instance,
}

// DrawState bundles everything needed for one MDI draw call
DrawState :: struct {
	// Shader and texture
	shader: u32,
	texture: u32,

	// Reference to VAO state (for dynamic mesh access)
	vao_state: ^VAO_State,

	// OpenGL resources
	command_buffer: u32,

	// Per-mesh batches (one instance array per mesh type)
	batches: map[int]^Mesh_Batch,
	batch_allocator: mem.Allocator,

	// Total capacity across all batches
	instance_capacity: int,

	// Draw commands (owned by this DrawState)
	commands: []DrawCommand,
	command_count: int,
}


// Create a draw state
draw_state_create :: proc(
	shader: u32,
	vao_state: ^VAO_State,
	max_instances: int,
	max_commands: int,
	allocator: mem.Allocator,) -> DrawState
{
	// Allocate commands
	commands := make([]DrawCommand, max_commands, allocator)

	// Create persistent command buffer for MDI
	command_buffer: u32
	gl.GenBuffers(1, &command_buffer)
	gl.BindBuffer(gl.DRAW_INDIRECT_BUFFER, command_buffer)
	gl.BufferData(gl.DRAW_INDIRECT_BUFFER,
				  max_commands * size_of(DrawCommand),
				  nil,
				  gl.DYNAMIC_DRAW)
	gl.BindBuffer(gl.DRAW_INDIRECT_BUFFER, 0)

	return DrawState{
		shader = shader,
		vao_state = vao_state,
		command_buffer = command_buffer,
		batches = make(map[int]^Mesh_Batch, 64, allocator),
		batch_allocator = allocator,
		instance_capacity = max_instances,
		commands = commands,
		command_count = 0,
	}
}

// Bind all resources in the draw state
draw_state_bind :: proc(state: ^DrawState) {
	gl.UseProgram(state.shader)
	gl.ActiveTexture(gl.TEXTURE0)
	gl.BindTexture(gl.TEXTURE_2D_ARRAY, state.texture)
}

// Get or create a batch for a mesh_id
draw_state_get_batch :: proc(state: ^DrawState, mesh_id: int) -> ^Mesh_Batch {
	if batch, ok := state.batches[mesh_id]; ok {
		return batch
	}
	// Create new batch for this mesh
	batch := new(Mesh_Batch, state.batch_allocator)
	batch.mesh_index = mesh_id
	batch.instances = make([dynamic]Instance, 0, 256, state.batch_allocator)
	state.batches[mesh_id] = batch
	return batch
}

// Append instances from object array, batching by each object's visual.mesh.index
// If highlight_state is provided, highlighted objects are also added to that state
draw_state_append :: proc(
	state: ^DrawState,
	objects: ^Array($T),
	camera: Camera,
	highlight_state: ^DrawState = nil,
)
	where intrinsics.type_has_field(T, "obj") && intrinsics.type_has_field(T, "visual")
{
	if objects.last_item < 0 do return // empty array

	for i in 0..=objects.last_item {
		if !objects.items[i].obj.exists do continue

		obj := objects.items[i]
		mesh_id := obj.visual.mesh.index

		// Get or create batch for this mesh
		batch := draw_state_get_batch(state, mesh_id)

		mvp := opengl_create_mvp_matrix(
			obj.obj.pos,
			obj.obj.dir,
			obj.obj.scale,
			camera,
		)
		instance := Instance{
			mvp_matrix = mvp,
			tex_coords = obj.visual.texture.uv,
			color = obj.visual.color,
			layer = obj.visual.texture.layer,
		}
		append(&batch.instances, instance)

		// Add highlighted objects to highlight state (fixed offset, bright green)
		if highlight_state != nil && obj.obj.highlighted {
			highlight_batch := draw_state_get_batch(highlight_state, mesh_id)
			// Fixed offset gives consistent outline thickness regardless of object size/shape
			highlight_scale := obj.obj.scale + 0.3
			highlight_mvp := opengl_create_mvp_matrix(
				obj.obj.pos,
				obj.obj.dir,
				highlight_scale,
				camera,
			)
			append(&highlight_batch.instances, Instance{
				mvp_matrix = highlight_mvp,
				tex_coords = obj.visual.texture.uv,
				color = {0, 1, 0},  // bright green
				layer = obj.visual.texture.layer,
			})
		}
	}
}

// Reset all batches for next frame
draw_state_reset :: proc(state: ^DrawState) {
	for _, batch in state.batches {
		clear(&batch.instances)
	}
	state.command_count = 0
}

// Render draw state using MultiDrawIndirect
// Uploads each batch's instances sequentially, then issues one MDI call
draw_state_render :: proc(state: ^DrawState) {
	// Collect valid batches in a fixed order (to ensure command offsets match upload order)
	batch_order: [512]^Mesh_Batch
	batch_count := 0

	// Count total instances and build commands
	gpu_offset := 0
	state.command_count = 0

	skipped_count := 0
	for mesh_id, batch in state.batches {
		if len(batch.instances) == 0 do continue
		if mesh_id < 0 || mesh_id >= state.vao_state.mesh_count {
			skipped_count += 1
			continue
		}

		if state.command_count >= len(state.commands) {
			fmt.println("Warning: DrawState command buffer full!")
			break
		}

		// Remember this batch for upload loop
		batch_order[batch_count] = batch
		batch_count += 1

		mesh := state.vao_state.meshes[mesh_id]
		state.commands[state.command_count] = DrawCommand{
			index_count = mesh.index_count,
			instance_count = u32(len(batch.instances)),
			first_index = mesh.first_index,
			base_vertex = mesh.base_vertex,
			base_instance = u32(gpu_offset),
		}
		state.command_count += 1
		gpu_offset += len(batch.instances)
	}


	if state.command_count == 0 do return

	// Bind shader and textures
	draw_state_bind(state)

	// Upload instance data in the same order as commands were built
	gl.BindBuffer(gl.ARRAY_BUFFER, state.vao_state.instance_vbo)
	upload_offset := 0
	for i in 0..<batch_count {
		batch := batch_order[i]
		size := len(batch.instances) * size_of(Instance)
		gl.BufferSubData(gl.ARRAY_BUFFER,
						 upload_offset,
						 size,
						 raw_data(batch.instances[:]))
		upload_offset += size
	}

	// Upload command data
	gl.BindBuffer(gl.DRAW_INDIRECT_BUFFER, state.command_buffer)
	gl.BufferSubData(gl.DRAW_INDIRECT_BUFFER, 0,
					 state.command_count * size_of(DrawCommand),
					 raw_data(state.commands))

	// ONE DRAW CALL FOR EVERYTHING
	gl.BindVertexArray(state.vao_state.vao)
	gl.MultiDrawElementsIndirect(
		gl.TRIANGLES,
		gl.UNSIGNED_INT,
		nil,                         // offset (0 = start of buffer)
		i32(state.command_count),    // draw count
		0,                           // stride (0 = tightly packed)
	)

	gl.BindVertexArray(0)
	gl.BindBuffer(gl.DRAW_INDIRECT_BUFFER, 0)
}

// Create MVP matrix from transform and camera
opengl_create_mvp_matrix :: proc(pos: linalg.Vector3f32,
							dir: linalg.Quaternionf32,
							scale_factors: linalg.Vector3f32,
							camera: Camera) -> linalg.Matrix4f32
{
	rotation := linalg.matrix4_from_quaternion(dir)
	translation := linalg.matrix4_translate(pos)
	scale := linalg.matrix4_scale(scale_factors)

	model := linalg.mul(translation, linalg.mul(rotation, scale))
	mv_matrix := linalg.mul(camera.view_mx, model)
	mvp_matrix := linalg.mul(camera.proj_mx, mv_matrix)
	return mvp_matrix
}

// ============================================================================
// Primitive Generation
// Orientation: Z forward, X right, Y up
// ============================================================================

// Quad facing +Z (forward), 1x1 centered at origin
primitive_quad :: proc(allocator := context.allocator) -> Mesh_Data {
	vertices := make([]Vertex, 4, allocator)
	indices := make([]u32, 6, allocator)

	// Corners: bottom-left, bottom-right, top-right, top-left
	vertices[0] = Vertex{position = {-0.5, -0.5, 0}, normal = {0, 0, 1}, uv = {0, 0}}
	vertices[1] = Vertex{position = { 0.5, -0.5, 0}, normal = {0, 0, 1}, uv = {1, 0}}
	vertices[2] = Vertex{position = { 0.5,  0.5, 0}, normal = {0, 0, 1}, uv = {1, 1}}
	vertices[3] = Vertex{position = {-0.5,  0.5, 0}, normal = {0, 0, 1}, uv = {0, 1}}

	// Two triangles, CCW winding
	indices[0] = 0; indices[1] = 1; indices[2] = 2
	indices[3] = 0; indices[4] = 2; indices[5] = 3

	return Mesh_Data{vertices = vertices, indices = indices}
}

// Cube 1x1x1 centered at origin
primitive_cube :: proc(allocator := context.allocator) -> Mesh_Data {
	vertices := make([]Vertex, 24, allocator)  // 4 verts per face * 6 faces
	indices := make([]u32, 36, allocator)      // 6 indices per face * 6 faces

	h :: f32(0.5)

	// +Z face (front)
	vertices[0]  = Vertex{position = {-h, -h,  h}, normal = {0, 0, 1}, uv = {0, 0}}
	vertices[1]  = Vertex{position = { h, -h,  h}, normal = {0, 0, 1}, uv = {1, 0}}
	vertices[2]  = Vertex{position = { h,  h,  h}, normal = {0, 0, 1}, uv = {1, 1}}
	vertices[3]  = Vertex{position = {-h,  h,  h}, normal = {0, 0, 1}, uv = {0, 1}}

	// -Z face (back)
	vertices[4]  = Vertex{position = { h, -h, -h}, normal = {0, 0, -1}, uv = {0, 0}}
	vertices[5]  = Vertex{position = {-h, -h, -h}, normal = {0, 0, -1}, uv = {1, 0}}
	vertices[6]  = Vertex{position = {-h,  h, -h}, normal = {0, 0, -1}, uv = {1, 1}}
	vertices[7]  = Vertex{position = { h,  h, -h}, normal = {0, 0, -1}, uv = {0, 1}}

	// +X face (right)
	vertices[8]  = Vertex{position = { h, -h,  h}, normal = {1, 0, 0}, uv = {0, 0}}
	vertices[9]  = Vertex{position = { h, -h, -h}, normal = {1, 0, 0}, uv = {1, 0}}
	vertices[10] = Vertex{position = { h,  h, -h}, normal = {1, 0, 0}, uv = {1, 1}}
	vertices[11] = Vertex{position = { h,  h,  h}, normal = {1, 0, 0}, uv = {0, 1}}

	// -X face (left)
	vertices[12] = Vertex{position = {-h, -h, -h}, normal = {-1, 0, 0}, uv = {0, 0}}
	vertices[13] = Vertex{position = {-h, -h,  h}, normal = {-1, 0, 0}, uv = {1, 0}}
	vertices[14] = Vertex{position = {-h,  h,  h}, normal = {-1, 0, 0}, uv = {1, 1}}
	vertices[15] = Vertex{position = {-h,  h, -h}, normal = {-1, 0, 0}, uv = {0, 1}}

	// +Y face (top)
	vertices[16] = Vertex{position = {-h,  h,  h}, normal = {0, 1, 0}, uv = {0, 0}}
	vertices[17] = Vertex{position = { h,  h,  h}, normal = {0, 1, 0}, uv = {1, 0}}
	vertices[18] = Vertex{position = { h,  h, -h}, normal = {0, 1, 0}, uv = {1, 1}}
	vertices[19] = Vertex{position = {-h,  h, -h}, normal = {0, 1, 0}, uv = {0, 1}}

	// -Y face (bottom)
	vertices[20] = Vertex{position = {-h, -h, -h}, normal = {0, -1, 0}, uv = {0, 0}}
	vertices[21] = Vertex{position = { h, -h, -h}, normal = {0, -1, 0}, uv = {1, 0}}
	vertices[22] = Vertex{position = { h, -h,  h}, normal = {0, -1, 0}, uv = {1, 1}}
	vertices[23] = Vertex{position = {-h, -h,  h}, normal = {0, -1, 0}, uv = {0, 1}}

	// Indices for each face (CCW winding)
	for face in 0..<6 {
		base_v := u32(face * 4)
		base_i := face * 6
		indices[base_i + 0] = base_v + 0
		indices[base_i + 1] = base_v + 1
		indices[base_i + 2] = base_v + 2
		indices[base_i + 3] = base_v + 0
		indices[base_i + 4] = base_v + 2
		indices[base_i + 5] = base_v + 3
	}

	return Mesh_Data{vertices = vertices, indices = indices}
}

// Sphere with given subdivisions, radius 0.5 centered at origin
primitive_sphere :: proc(subdivisions: int = 16, allocator := context.allocator) -> Mesh_Data {
	rings := subdivisions
	sectors := subdivisions * 2

	vert_count := (rings + 1) * (sectors + 1)
	idx_count := rings * sectors * 6

	vertices := make([]Vertex, vert_count, allocator)
	indices := make([]u32, idx_count, allocator)

	radius :: f32(0.5)

	// Generate vertices
	vi := 0
	for r in 0..=rings {
		phi := math.PI * f32(r) / f32(rings)  // 0 to PI (top to bottom)
		y := radius * math.cos(phi)
		ring_radius := radius * math.sin(phi)

		for s in 0..=sectors {
			theta := math.TAU * f32(s) / f32(sectors)  // 0 to TAU
			x := ring_radius * math.sin(theta)
			z := ring_radius * math.cos(theta)

			normal := linalg.normalize(linalg.Vector3f32{x, y, z})
			u := f32(s) / f32(sectors)
			v := f32(r) / f32(rings)

			vertices[vi] = Vertex{
				position = {x, y, z},
				normal = {normal.x, normal.y, normal.z},
				uv = {u, v},
			}
			vi += 1
		}
	}

	// Generate indices
	ii := 0
	for r in 0..<rings {
		for s in 0..<sectors {
			cur := u32(r * (sectors + 1) + s)
			next := cur + u32(sectors + 1)

			// Two triangles per quad
			indices[ii + 0] = cur
			indices[ii + 1] = next
			indices[ii + 2] = cur + 1

			indices[ii + 3] = cur + 1
			indices[ii + 4] = next
			indices[ii + 5] = next + 1

			ii += 6
		}
	}

	return Mesh_Data{vertices = vertices, indices = indices}
}

// Cylinder with radius 0.5, height 1, centered at origin
// axis: X, Y, or Z determines which axis the cylinder extends along
// negative: if true, caps are flipped (top becomes bottom)
// Default: +Z axis (forward)
primitive_cylinder :: proc(segments: int = 16, axis: Axis = .Z, negative: bool = false, allocator := context.allocator) -> Mesh_Data {
	// Vertices: top cap center + ring, bottom cap center + ring, side top ring, side bottom ring
	vert_count := 2 + segments * 4  // 2 centers + 4 rings
	idx_count := segments * 3 * 2 + segments * 6  // top cap + bottom cap + sides

	vertices := make([]Vertex, vert_count, allocator)
	indices := make([]u32, idx_count, allocator)

	radius :: f32(0.5)
	half_h :: f32(0.5)

	// Swizzle function to map canonical Y-up cylinder to target axis
	// Canonical: Y is the cylinder axis, X and Z are the radial plane
	swizzle_pos :: proc(x, y, z: f32, axis: Axis, negative: bool) -> [3]f32 {
		yn := y if !negative else -y
		switch axis {
		case .X: return {yn, z, x}
		case .Y: return {x, yn, z}
		case .Z: return {x, z, yn}
		}
		return {x, yn, z}
	}

	swizzle_norm :: proc(nx, ny, nz: f32, axis: Axis, negative: bool) -> [3]f32 {
		nyn := ny if !negative else -ny
		switch axis {
		case .X: return {nyn, nz, nx}
		case .Y: return {nx, nyn, nz}
		case .Z: return {nx, nz, nyn}
		}
		return {nx, nyn, nz}
	}

	vi := 0

	// Top cap center
	vertices[vi] = Vertex{
		position = swizzle_pos(0, half_h, 0, axis, negative),
		normal = swizzle_norm(0, 1, 0, axis, negative),
		uv = {0.5, 0.5},
	}
	top_center := u32(vi)
	vi += 1

	// Top cap ring
	top_ring_start := u32(vi)
	for s in 0..<segments {
		theta := math.TAU * f32(s) / f32(segments)
		x := radius * math.sin(theta)
		z := radius * math.cos(theta)
		u := 0.5 + 0.5 * math.sin(theta)
		v := 0.5 + 0.5 * math.cos(theta)
		vertices[vi] = Vertex{
			position = swizzle_pos(x, half_h, z, axis, negative),
			normal = swizzle_norm(0, 1, 0, axis, negative),
			uv = {u, v},
		}
		vi += 1
	}

	// Bottom cap center
	vertices[vi] = Vertex{
		position = swizzle_pos(0, -half_h, 0, axis, negative),
		normal = swizzle_norm(0, -1, 0, axis, negative),
		uv = {0.5, 0.5},
	}
	bot_center := u32(vi)
	vi += 1

	// Bottom cap ring
	bot_ring_start := u32(vi)
	for s in 0..<segments {
		theta := math.TAU * f32(s) / f32(segments)
		x := radius * math.sin(theta)
		z := radius * math.cos(theta)
		u := 0.5 + 0.5 * math.sin(theta)
		v := 0.5 - 0.5 * math.cos(theta)
		vertices[vi] = Vertex{
			position = swizzle_pos(x, -half_h, z, axis, negative),
			normal = swizzle_norm(0, -1, 0, axis, negative),
			uv = {u, v},
		}
		vi += 1
	}

	// Side top ring (with outward normals)
	side_top_start := u32(vi)
	for s in 0..<segments {
		theta := math.TAU * f32(s) / f32(segments)
		x := radius * math.sin(theta)
		z := radius * math.cos(theta)
		nx := math.sin(theta)
		nz := math.cos(theta)
		u := f32(s) / f32(segments)
		vertices[vi] = Vertex{
			position = swizzle_pos(x, half_h, z, axis, negative),
			normal = swizzle_norm(nx, 0, nz, axis, negative),
			uv = {u, 1},
		}
		vi += 1
	}

	// Side bottom ring (with outward normals)
	side_bot_start := u32(vi)
	for s in 0..<segments {
		theta := math.TAU * f32(s) / f32(segments)
		x := radius * math.sin(theta)
		z := radius * math.cos(theta)
		nx := math.sin(theta)
		nz := math.cos(theta)
		u := f32(s) / f32(segments)
		vertices[vi] = Vertex{
			position = swizzle_pos(x, -half_h, z, axis, negative),
			normal = swizzle_norm(nx, 0, nz, axis, negative),
			uv = {u, 0},
		}
		vi += 1
	}

	// Indices
	ii := 0

	// Top cap triangles (CCW from above)
	for s in 0..<segments {
		next := (s + 1) % segments
		indices[ii + 0] = top_center
		indices[ii + 1] = top_ring_start + u32(next)
		indices[ii + 2] = top_ring_start + u32(s)
		ii += 3
	}

	// Bottom cap triangles (CCW from below)
	for s in 0..<segments {
		next := (s + 1) % segments
		indices[ii + 0] = bot_center
		indices[ii + 1] = bot_ring_start + u32(s)
		indices[ii + 2] = bot_ring_start + u32(next)
		ii += 3
	}

	// Side quads
	for s in 0..<segments {
		next := (s + 1) % segments
		t0 := side_top_start + u32(s)
		t1 := side_top_start + u32(next)
		b0 := side_bot_start + u32(s)
		b1 := side_bot_start + u32(next)

		indices[ii + 0] = t0
		indices[ii + 1] = b0
		indices[ii + 2] = b1

		indices[ii + 3] = t0
		indices[ii + 4] = b1
		indices[ii + 5] = t1

		ii += 6
	}

	return Mesh_Data{vertices = vertices, indices = indices}
}

// Pyramid with square base, apex pointing in specified direction
// axis: 0 = +X, 1 = +Y, 2 = +Z (default), negative values for opposite direction
Axis :: enum { X, Y, Z }

primitive_pyramid :: proc(axis: Axis = .Z, negative: bool = false, allocator := context.allocator) -> Mesh_Data {
	// 4 base corners + apex = 5 unique positions, but we need separate verts for normals
	// Base: 4 verts, 4 side faces: 3 verts each = 16 verts total
	vertices := make([]Vertex, 16, allocator)
	indices := make([]u32, 18, allocator)  // base: 6, sides: 3*4 = 12

	half :: f32(0.5)

	// Generate in canonical orientation (apex +Z), then swizzle
	apex_val := half if !negative else -half
	base_val := -half if !negative else half

	// Base corners and apex in canonical space (apex along axis)
	bl, br, fr, fl, apex: [3]f32
	switch axis {
	case .X:
		bl = {base_val, -half, -half}
		br = {base_val,  half, -half}
		fr = {base_val,  half,  half}
		fl = {base_val, -half,  half}
		apex = {apex_val, 0, 0}
	case .Y:
		bl = {-half, base_val, -half}
		br = { half, base_val, -half}
		fr = { half, base_val,  half}
		fl = {-half, base_val,  half}
		apex = {0, apex_val, 0}
	case .Z:
		bl = {-half, -half, base_val}
		br = { half, -half, base_val}
		fr = { half,  half, base_val}
		fl = {-half,  half, base_val}
		apex = {0, 0, apex_val}
	}

	// Base face normal points opposite to apex
	base_normal: [3]f32
	switch axis {
	case .X: base_normal = {-1, 0, 0} if !negative else {1, 0, 0}
	case .Y: base_normal = {0, -1, 0} if !negative else {0, 1, 0}
	case .Z: base_normal = {0, 0, -1} if !negative else {0, 0, 1}
	}

	vertices[0] = Vertex{position = bl, normal = base_normal, uv = {0, 0}}
	vertices[1] = Vertex{position = br, normal = base_normal, uv = {1, 0}}
	vertices[2] = Vertex{position = fr, normal = base_normal, uv = {1, 1}}
	vertices[3] = Vertex{position = fl, normal = base_normal, uv = {0, 1}}

	// Calculate face normals for sides
	calc_normal :: proc(a, b, c: [3]f32) -> [3]f32 {
		ab := linalg.Vector3f32{b[0]-a[0], b[1]-a[1], b[2]-a[2]}
		ac := linalg.Vector3f32{c[0]-a[0], c[1]-a[1], c[2]-a[2]}
		n := linalg.normalize(linalg.cross(ab, ac))
		return {n.x, n.y, n.z}
	}

	// Front face (+Z side)
	n_front := calc_normal(fl, fr, apex)
	vertices[4] = Vertex{position = fl, normal = n_front, uv = {0, 0}}
	vertices[5] = Vertex{position = fr, normal = n_front, uv = {1, 0}}
	vertices[6] = Vertex{position = apex, normal = n_front, uv = {0.5, 1}}

	// Right face (+X side)
	n_right := calc_normal(fr, br, apex)
	vertices[7] = Vertex{position = fr, normal = n_right, uv = {0, 0}}
	vertices[8] = Vertex{position = br, normal = n_right, uv = {1, 0}}
	vertices[9] = Vertex{position = apex, normal = n_right, uv = {0.5, 1}}

	// Back face (-Z side)
	n_back := calc_normal(br, bl, apex)
	vertices[10] = Vertex{position = br, normal = n_back, uv = {0, 0}}
	vertices[11] = Vertex{position = bl, normal = n_back, uv = {1, 0}}
	vertices[12] = Vertex{position = apex, normal = n_back, uv = {0.5, 1}}

	// Left face (-X side)
	n_left := calc_normal(bl, fl, apex)
	vertices[13] = Vertex{position = bl, normal = n_left, uv = {0, 0}}
	vertices[14] = Vertex{position = fl, normal = n_left, uv = {1, 0}}
	vertices[15] = Vertex{position = apex, normal = n_left, uv = {0.5, 1}}

	// Base indices (CCW from below)
	indices[0] = 0; indices[1] = 2; indices[2] = 1
	indices[3] = 0; indices[4] = 3; indices[5] = 2

	// Side indices
	indices[6] = 4;  indices[7] = 5;  indices[8] = 6    // front
	indices[9] = 7;  indices[10] = 8; indices[11] = 9   // right
	indices[12] = 10; indices[13] = 11; indices[14] = 12 // back
	indices[15] = 13; indices[16] = 14; indices[17] = 15 // left

	return Mesh_Data{vertices = vertices, indices = indices}
}

// Add all primitives to VAO and return their names/indices
// Call this during asset init, before loading models
primitives_init :: proc(vao: ^VAO_State, allocator := context.allocator) -> (names: []string, indices: []int) {
	Primitive :: struct {
		name: string,
		gen:  proc(allocator: mem.Allocator) -> Mesh_Data,
	}

	prims := []Primitive{
		{"quad",     proc(a: mem.Allocator) -> Mesh_Data { return primitive_quad(a) }},
		{"cube",     proc(a: mem.Allocator) -> Mesh_Data { return primitive_cube(a) }},
		{"sphere",   proc(a: mem.Allocator) -> Mesh_Data { return primitive_sphere(16, a) }},
		{"cylinder", proc(a: mem.Allocator) -> Mesh_Data { return primitive_cylinder(16, .Z, false, a) }},
		{"pyramid",  proc(a: mem.Allocator) -> Mesh_Data { return primitive_pyramid(.Z, false, a) }},
	}

	names = make([]string, len(prims), allocator)
	indices = make([]int, len(prims), allocator)

	for p, i in prims {
		mesh := p.gen(context.temp_allocator)
		idx := vao_add_mesh(vao, mesh)
		names[i] = p.name
		indices[i] = idx
	}

	return names, indices
}
