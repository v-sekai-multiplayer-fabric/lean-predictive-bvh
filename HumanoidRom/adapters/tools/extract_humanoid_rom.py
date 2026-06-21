#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
extract_humanoid_rom.py — Filter for humanoids and compute ROM via self-intersection.

Step 1: Filter skinned_humanoids.json for models with humanoid bone names.
Step 2: Extract mesh data (vertices, triangles, skin weights) from GLB.
Step 3: For each joint, binary search for self-intersection angle limit.
Step 4: Output ROM data as JSON (bone_lengths → ROM limits).
"""
import json
import struct
import sys
import numpy as np
from pathlib import Path
from typing import Optional

# ── Humanoid bone name patterns ──────────────────────────────────────────────

HUMANOID_PATTERNS = {
    'hips': ['hips', 'hip', 'pelvis', 'root', 'waist'],
    'spine': ['spine', 'torso', 'chest', 'body'],
    'head': ['head', 'neck'],
    'upper_arm': ['upperarm', 'upper_arm', 'shoulder', 'arm'],
    'lower_arm': ['lowerarm', 'lower_arm', 'forearm', 'elbow'],
    'hand': ['hand', 'wrist'],
    'upper_leg': ['upperleg', 'upper_leg', 'thigh', 'upleg'],
    'lower_leg': ['lowerleg', 'lower_leg', 'shin', 'calf', 'knee'],
    'foot': ['foot', 'ankle', 'toe'],
}

def is_humanoid(joint_names: list) -> tuple[bool, dict]:
    """Check if joint names match humanoid patterns. Returns (is_humanoid, mapping)."""
    names_lower = [n.lower().replace(' ', '').replace('_', '').replace('.', '') for n in joint_names]
    found = {}
    for part, patterns in HUMANOID_PATTERNS.items():
        for i, name in enumerate(names_lower):
            for pat in patterns:
                if pat in name:
                    if part not in found:
                        found[part] = []
                    found[part].append((i, joint_names[i]))
                    break
    # Must have at least: hips/spine, head, one arm, one leg
    has_torso = 'hips' in found or 'spine' in found
    has_head = 'head' in found
    has_arm = 'upper_arm' in found or 'lower_arm' in found
    has_leg = 'upper_leg' in found or 'lower_leg' in found
    return (has_torso and has_head and has_arm and has_leg), found

# ── GLB mesh extraction ──────────────────────────────────────────────────────

def parse_glb(path: Path):
    """Parse a GLB file and extract mesh + skeleton data."""
    data = path.read_bytes()
    if data[:4] != b'glTF' or len(data) < 20:
        return None

    # JSON chunk
    chunk_len = struct.unpack_from('<I', data, 12)[0]
    gltf = json.loads(data[20:20+chunk_len])

    # Binary chunk
    bin_offset = 20 + chunk_len
    if bin_offset + 8 > len(data):
        return None
    bin_len = struct.unpack_from('<I', data, bin_offset)[0]
    bin_data = data[bin_offset+8:bin_offset+8+bin_len]

    return gltf, bin_data

def get_accessor_data(gltf, bin_data, acc_idx, dtype=np.float32):
    """Read accessor data from binary buffer."""
    acc = gltf['accessors'][acc_idx]
    if 'bufferView' not in acc:
        return None
    bv = gltf['bufferViews'][acc['bufferView']]
    offset = bv.get('byteOffset', 0) + acc.get('byteOffset', 0)
    count = acc['count']

    type_sizes = {'SCALAR': 1, 'VEC2': 2, 'VEC3': 3, 'VEC4': 4, 'MAT4': 16}
    components = type_sizes.get(acc['type'], 1)

    component_types = {5120: np.int8, 5121: np.uint8, 5122: np.int16,
                       5123: np.uint16, 5125: np.uint32, 5126: np.float32}
    ct = component_types.get(acc['componentType'], np.float32)

    stride = bv.get('byteStride', 0)
    if stride == 0:
        arr = np.frombuffer(bin_data, dtype=ct, count=count*components, offset=offset)
        return arr.reshape(count, components).astype(dtype)
    else:
        result = np.zeros((count, components), dtype=dtype)
        for i in range(count):
            chunk = bin_data[offset + i*stride:offset + i*stride + components*np.dtype(ct).itemsize]
            result[i] = np.frombuffer(chunk, dtype=ct, count=components).astype(dtype)
        return result

def extract_mesh_data(path: Path):
    """Extract vertices, triangles, joints, and skin weights from GLB."""
    result = parse_glb(path)
    if result is None:
        return None
    gltf, bin_data = result

    skins = gltf.get('skins', [])
    if not skins:
        return None

    nodes = gltf.get('nodes', [])
    meshes = gltf.get('meshes', [])
    skin = skins[0]
    joint_indices = skin.get('joints', [])
    joint_names = [nodes[j].get('name', f'joint_{j}') for j in joint_indices]

    # Collect all mesh primitives
    all_verts = []
    all_tris = []
    all_joints_idx = []
    all_weights = []
    vert_offset = 0

    for mesh in meshes:
        for prim in mesh.get('primitives', []):
            attrs = prim.get('attributes', {})
            if 'POSITION' not in attrs or 'JOINTS_0' not in attrs or 'WEIGHTS_0' not in attrs:
                continue

            verts = get_accessor_data(gltf, bin_data, attrs['POSITION'], np.float32)
            joints = get_accessor_data(gltf, bin_data, attrs['JOINTS_0'], np.int32)
            weights = get_accessor_data(gltf, bin_data, attrs['WEIGHTS_0'], np.float32)
            if verts is None or joints is None or weights is None:
                continue

            if 'indices' in prim:
                indices = get_accessor_data(gltf, bin_data, prim['indices'], np.int32).flatten()
                for i in range(0, len(indices), 3):
                    if i+2 < len(indices):
                        all_tris.append([indices[i]+vert_offset, indices[i+1]+vert_offset, indices[i+2]+vert_offset])
            else:
                for i in range(0, len(verts), 3):
                    all_tris.append([i+vert_offset, i+1+vert_offset, i+2+vert_offset])

            all_verts.append(verts)
            all_joints_idx.append(joints)
            all_weights.append(weights)
            vert_offset += len(verts)

    if not all_verts:
        return None

    vertices = np.vstack(all_verts)
    joint_assignments = np.vstack(all_joints_idx) if all_joints_idx else np.zeros((len(vertices), 4), dtype=np.int32)
    weight_values = np.vstack(all_weights) if all_weights else np.zeros((len(vertices), 4), dtype=np.float32)
    triangles = np.array(all_tris, dtype=np.int32)

    # Dominant bone per vertex
    dominant_bone = joint_assignments[np.arange(len(vertices)), weight_values.argmax(axis=1)]

    # Joint positions from nodes
    joint_positions = np.zeros((len(joint_indices), 3), dtype=np.float32)
    for i, node_idx in enumerate(joint_indices):
        node = nodes[node_idx]
        if 'translation' in node:
            joint_positions[i] = node['translation']

    return {
        'vertices': vertices,
        'triangles': triangles,
        'dominant_bone': dominant_bone,
        'joint_names': joint_names,
        'joint_positions': joint_positions,
        'num_joints': len(joint_indices),
    }

# ── Self-intersection test ───────────────────────────────────────────────────

def triangles_intersect_batch(verts, tris_a, tris_b):
    """Check if any triangle in set A intersects any in set B (vectorized)."""
    if len(tris_a) == 0 or len(tris_b) == 0:
        return False

    # Sample subset for speed (full check is O(n²))
    max_check = 500
    if len(tris_a) > max_check:
        tris_a = tris_a[np.random.choice(len(tris_a), max_check, replace=False)]
    if len(tris_b) > max_check:
        tris_b = tris_b[np.random.choice(len(tris_b), max_check, replace=False)]

    for ta in tris_a:
        p0, p1, p2 = verts[ta[0]], verts[ta[1]], verts[ta[2]]
        # AABB of triangle A
        a_min = np.minimum(np.minimum(p0, p1), p2)
        a_max = np.maximum(np.maximum(p0, p1), p2)

        for tb in tris_b:
            q0, q1, q2 = verts[tb[0]], verts[tb[1]], verts[tb[2]]
            # Quick AABB reject
            b_min = np.minimum(np.minimum(q0, q1), q2)
            b_max = np.maximum(np.maximum(q0, q1), q2)
            if np.any(a_min > b_max) or np.any(b_min > a_max):
                continue
            # If AABBs overlap, conservatively report collision
            return True
    return False

def apply_rotation(vertices, joint_pos, axis, angle_rad, bone_children, dominant_bone):
    """Rotate all vertices belonging to bone_children around joint_pos by angle on axis."""
    rotated = vertices.copy()
    c, s = np.cos(angle_rad), np.sin(angle_rad)
    # Rodrigues rotation
    ax = axis / np.linalg.norm(axis)
    K = np.array([[0, -ax[2], ax[1]], [ax[2], 0, -ax[0]], [-ax[1], ax[0], 0]])
    R = np.eye(3) + s * K + (1-c) * (K @ K)

    mask = np.isin(dominant_bone, list(bone_children))
    if not np.any(mask):
        return rotated
    centered = rotated[mask] - joint_pos
    rotated[mask] = (R @ centered.T).T + joint_pos
    return rotated

def find_children(joint_idx, num_joints, joint_positions):
    """Find all descendant bones of a joint (by proximity heuristic)."""
    # Simple: bones whose position is further from root than this joint
    root_dist = np.linalg.norm(joint_positions, axis=1)
    my_dist = root_dist[joint_idx]
    children = set()
    children.add(joint_idx)
    for i in range(num_joints):
        if root_dist[i] > my_dist and i != joint_idx:
            children.add(i)
    return children

def sweep_joint_rom(mesh_data, joint_idx, axis=np.array([1.0, 0, 0])):
    """Binary search for self-intersection limit of one joint on one axis."""
    verts = mesh_data['vertices']
    tris = mesh_data['triangles']
    dominant = mesh_data['dominant_bone']
    jpos = mesh_data['joint_positions'][joint_idx]
    children = find_children(joint_idx, mesh_data['num_joints'], mesh_data['joint_positions'])
    parent_bones = set(range(mesh_data['num_joints'])) - children

    # Triangles for each group
    parent_tris = tris[np.isin(dominant[tris[:, 0]], list(parent_bones))]
    child_tris = tris[np.isin(dominant[tris[:, 0]], list(children))]

    def collides_at(angle_deg):
        angle_rad = np.radians(angle_deg)
        rotated = apply_rotation(verts, jpos, axis, angle_rad, children, dominant)
        return triangles_intersect_batch(rotated, parent_tris, child_tris)

    # Binary search from 0 to 180
    lo, hi = 0.0, 180.0
    for _ in range(12):  # 12 iterations → ~0.05° precision
        mid = (lo + hi) / 2
        if collides_at(mid):
            hi = mid
        else:
            lo = mid
    return lo

# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    input_json = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(r"D:\Objaverse XL\skinned_humanoids.json")
    max_models = int(sys.argv[2]) if len(sys.argv) > 2 else 20

    with open(input_json) as f:
        all_models = json.load(f)

    print(f"Loaded {len(all_models)} skinned models")

    # Filter for humanoids
    humanoids = []
    for m in all_models:
        is_human, mapping = is_humanoid(m['joint_names'])
        if is_human:
            humanoids.append({**m, 'mapping': {k: [x[1] for x in v] for k, v in mapping.items()}})

    print(f"Filtered to {len(humanoids)} humanoids")

    # Process top N
    results = []
    for i, model in enumerate(humanoids[:max_models]):
        print(f"\n[{i+1}/{min(len(humanoids), max_models)}] {Path(model['path']).name[:40]} ({model['joints']} joints)")

        mesh_data = extract_mesh_data(Path(model['path']))
        if mesh_data is None:
            print("  SKIP: could not extract mesh")
            continue

        print(f"  {len(mesh_data['vertices'])} verts, {len(mesh_data['triangles'])} tris, {mesh_data['num_joints']} joints")

        # Compute bone lengths
        bone_lengths = []
        for j in range(mesh_data['num_joints']):
            if j == 0:
                bone_lengths.append(0)
            else:
                length = np.linalg.norm(mesh_data['joint_positions'][j] - mesh_data['joint_positions'][max(0, j-1)])
                bone_lengths.append(float(length))

        # Sweep ROM for each joint (3 axes: X, Y, Z)
        joint_roms = []
        axes = [np.array([1,0,0.]), np.array([0,1,0.]), np.array([0,0,1.])]
        for j in range(min(mesh_data['num_joints'], 20)):
            roms = []
            for ax in axes:
                try:
                    limit = sweep_joint_rom(mesh_data, j, ax)
                    roms.append(round(limit, 1))
                except Exception:
                    roms.append(180.0)
            joint_roms.append({
                'name': mesh_data['joint_names'][j],
                'swing1_max': roms[0],
                'swing2_max': roms[1],
                'twist_max': roms[2],
            })
            print(f"  joint {j} ({mesh_data['joint_names'][j]}): swing1={roms[0]:.0f}° swing2={roms[1]:.0f}° twist={roms[2]:.0f}°")

        results.append({
            'path': model['path'],
            'bone_lengths': bone_lengths,
            'joint_roms': joint_roms,
            'num_joints': mesh_data['num_joints'],
        })

    # Save
    out_path = input_json.parent / "humanoid_rom_data.json"
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved {len(results)} results to {out_path}")

if __name__ == "__main__":
    main()
