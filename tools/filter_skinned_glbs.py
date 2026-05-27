#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
filter_skinned_glbs.py — Find GLBs with skeletons in Objaverse XL.
Extracts: joint count, bone hierarchy, vertex count, skin weights presence.
Filters for humanoid-like models (10-40 joints, has skin weights).
"""
import json
import struct
import sys
from pathlib import Path

def parse_glb_header(data: bytes):
    """Parse GLB header and extract JSON chunk."""
    if len(data) < 12 or data[:4] != b'glTF':
        return None
    version, length = struct.unpack_from('<II', data, 4)
    if version != 2:
        return None
    # First chunk should be JSON
    chunk_len, chunk_type = struct.unpack_from('<II', data, 12)
    if chunk_type != 0x4E4F534A:  # 'JSON'
        return None
    json_bytes = data[20:20+chunk_len]
    try:
        return json.loads(json_bytes)
    except json.JSONDecodeError:
        return None

def analyze_glb(path: Path):
    """Analyze a GLB file for skeleton/skin data."""
    try:
        data = path.read_bytes()
    except Exception:
        return None

    gltf = parse_glb_header(data)
    if gltf is None:
        return None

    skins = gltf.get('skins', [])
    nodes = gltf.get('nodes', [])
    meshes = gltf.get('meshes', [])

    if not skins:
        return None  # No skeleton

    # Count joints across all skins
    total_joints = 0
    joint_names = []
    for skin in skins:
        joints = skin.get('joints', [])
        total_joints += len(joints)
        for j in joints:
            if j < len(nodes):
                joint_names.append(nodes[j].get('name', f'joint_{j}'))

    # Count vertices
    total_verts = 0
    has_weights = False
    for mesh in meshes:
        for prim in mesh.get('primitives', []):
            attrs = prim.get('attributes', {})
            if 'WEIGHTS_0' in attrs:
                has_weights = True
            if 'POSITION' in attrs:
                acc_idx = attrs['POSITION']
                accessors = gltf.get('accessors', [])
                if acc_idx < len(accessors):
                    total_verts += accessors[acc_idx].get('count', 0)

    if not has_weights:
        return None  # No skin weights

    return {
        'path': str(path),
        'joints': total_joints,
        'vertices': total_verts,
        'skins': len(skins),
        'joint_names': joint_names[:30],  # cap for readability
    }

def main():
    data_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(r"D:\Objaverse XL\filtered")
    min_joints = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    max_joints = int(sys.argv[3]) if len(sys.argv) > 3 else 60

    glbs = sorted(data_dir.rglob("*.glb"))
    print(f"Scanning {len(glbs)} GLB files for skinned meshes...")

    results = []
    for i, path in enumerate(glbs):
        info = analyze_glb(path)
        if info and min_joints <= info['joints'] <= max_joints:
            results.append(info)
        if (i + 1) % 1000 == 0:
            print(f"  {i+1}/{len(glbs)} scanned, {len(results)} skinned humanoids found")

    print(f"\nFound {len(results)} skinned models with {min_joints}-{max_joints} joints")

    # Print top results
    results.sort(key=lambda x: x['joints'])
    for r in results[:20]:
        names_preview = ', '.join(r['joint_names'][:5])
        print(f"  {r['joints']:3d} joints, {r['vertices']:6d} verts: ...{Path(r['path']).name[:20]} [{names_preview}...]")

    # Save full list
    out = data_dir.parent / "skinned_humanoids.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved {len(results)} entries to {out}")

if __name__ == "__main__":
    main()
