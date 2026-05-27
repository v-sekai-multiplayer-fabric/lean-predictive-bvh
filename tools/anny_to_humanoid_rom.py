#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
anny_to_humanoid_rom.py — Convert ANNY ROM sweep to humanoid trait format.

Output matches E:\multiplayer-fabric-humanoid-project human_trait.gd:
  Per muscle: asymmetric [min_deg, max_deg] range
  Axes are bone-local: Front-Back, Left-Right/In-Out, Twist

Sweeps BOTH positive and negative rotation per bone's local axes.
"""
import sys
import json
import numpy as np
from pathlib import Path

try:
    import torch
    import anny
    HAS_ANNY = True
except ImportError:
    HAS_ANNY = False

# ── ANNY bone → Humanoid muscle mapping ──────────────────────────────────────
# Each entry: (anny_bone_name, humanoid_bone_name, muscles)
# muscles: list of (muscle_name, local_axis_index, axis_direction)
# axis_direction: which bone-local axis to rotate around
#   For ANNY rest pose: bone direction is along local Y (head→tail)
#   Front-Back = rotation around local X
#   Left-Right/In-Out = rotation around local Z
#   Twist = rotation around local Y (bone axis)

HUMANOID_MUSCLES = [
    ('spine03', 'Spine', [
        ('Spine Front-Back', 'x'),
        ('Spine Left-Right', 'z'),
        ('Spine Twist Left-Right', 'y'),
    ]),
    ('spine03', 'Chest', [
        ('Chest Front-Back', 'x'),
        ('Chest Left-Right', 'z'),
        ('Chest Twist Left-Right', 'y'),
    ]),
    ('head', 'Head', [
        ('Head Nod Down-Up', 'x'),
        ('Head Tilt Left-Right', 'z'),
        ('Head Turn Left-Right', 'y'),
    ]),
    ('upperleg01.L', 'Left Upper Leg', [
        ('Left Upper Leg Front-Back', 'x'),
        ('Left Upper Leg In-Out', 'z'),
        ('Left Upper Leg Twist In-Out', 'y'),
    ]),
    ('lowerleg01.L', 'Left Lower Leg', [
        ('Left Lower Leg Stretch', 'x'),
        ('Left Lower Leg Twist In-Out', 'y'),
    ]),
    ('foot.L', 'Left Foot', [
        ('Left Foot Up-Down', 'x'),
        ('Left Foot Twist In-Out', 'y'),
    ]),
    ('upperleg01.R', 'Right Upper Leg', [
        ('Right Upper Leg Front-Back', 'x'),
        ('Right Upper Leg In-Out', 'z'),
        ('Right Upper Leg Twist In-Out', 'y'),
    ]),
    ('lowerleg01.R', 'Right Lower Leg', [
        ('Right Lower Leg Stretch', 'x'),
        ('Right Lower Leg Twist In-Out', 'y'),
    ]),
    ('foot.R', 'Right Foot', [
        ('Right Foot Up-Down', 'x'),
        ('Right Foot Twist In-Out', 'y'),
    ]),
    ('upperarm01.L', 'Left Arm', [
        ('Left Arm Down-Up', 'x'),
        ('Left Arm Front-Back', 'z'),
        ('Left Arm Twist In-Out', 'y'),
    ]),
    ('lowerarm01.L', 'Left Forearm', [
        ('Left Forearm Stretch', 'x'),
        ('Left Forearm Twist In-Out', 'y'),
    ]),
    ('wrist.L', 'Left Hand', [
        ('Left Hand Down-Up', 'x'),
        ('Left Hand In-Out', 'z'),
    ]),
    ('upperarm01.R', 'Right Arm', [
        ('Right Arm Down-Up', 'x'),
        ('Right Arm Front-Back', 'z'),
        ('Right Arm Twist In-Out', 'y'),
    ]),
    ('lowerarm01.R', 'Right Forearm', [
        ('Right Forearm Stretch', 'x'),
        ('Right Forearm Twist In-Out', 'y'),
    ]),
    ('wrist.R', 'Right Hand', [
        ('Right Hand Down-Up', 'x'),
        ('Right Hand In-Out', 'z'),
    ]),
]


def get_bone_local_axes(model, bone_name):
    """Get bone-local coordinate frame from ANNY rest pose.
    Y = bone direction (head→tail), X = perpendicular, Z = cross(X,Y)."""
    labels = list(model.bone_labels)
    idx = labels.index(bone_name)
    output = model.forward(return_bone_ends=True)
    heads = output['rest_bone_heads'][0].detach().cpu().numpy()
    tails = output['rest_bone_tails'][0].detach().cpu().numpy()

    bone_dir = tails[idx] - heads[idx]
    length = np.linalg.norm(bone_dir)
    if length < 1e-6:
        return np.eye(3), heads[idx]

    y_axis = bone_dir / length
    # X axis: perpendicular to Y, prefer world-X if possible
    world_x = np.array([1, 0, 0.])
    if abs(np.dot(y_axis, world_x)) > 0.9:
        world_x = np.array([0, 0, 1.])
    x_axis = np.cross(y_axis, world_x)
    x_axis /= np.linalg.norm(x_axis)
    z_axis = np.cross(x_axis, y_axis)
    z_axis /= np.linalg.norm(z_axis)

    return np.column_stack([x_axis, y_axis, z_axis]), heads[idx]


def sweep_axis(model, bone_name, axis_world, joint_pos, children_mask,
               parent_faces_mask, child_faces_mask, verts, faces, direction=1):
    """Binary search for collision limit in one direction along one axis."""
    from anny_rom_sweep import apply_joint_rotation, check_intersection

    lo, hi = 0.0, 180.0
    for _ in range(12):
        mid = (lo + hi) / 2
        angle = direction * mid
        rotated = apply_joint_rotation(verts, joint_pos, axis_world,
                                        np.radians(angle), children_mask)
        if check_intersection(rotated, faces, parent_faces_mask, child_faces_mask):
            hi = mid
        else:
            lo = mid
    return direction * lo


def main():
    if not HAS_ANNY:
        print("ERROR: anny not installed")
        sys.exit(1)

    output_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("humanoid_rom.json")

    print("Loading ANNY model...")
    model = anny.create_fullbody_model()
    labels = list(model.bone_labels)
    parents = model.bone_parents

    # Import sweep functions
    sys.path.insert(0, str(Path(__file__).parent))
    from anny_rom_sweep import AnnyModel, apply_joint_rotation, check_intersection

    anny_model = AnnyModel()
    output = model.forward(return_bone_ends=True)
    verts = output['vertices'][0].detach().cpu().numpy()
    raw_faces = model.faces.cpu().numpy()
    faces = np.vstack([raw_faces[:, [0, 1, 2]], raw_faces[:, [0, 2, 3]]])

    # Bone assignment (walk hierarchy to nearest LabRCSF bone)
    bone_indices = model.vertex_bone_indices.cpu().numpy()
    bone_weights = model.vertex_bone_weights.cpu().numpy()
    dominant_full = bone_indices[np.arange(len(verts)), bone_weights.argmax(axis=1)]

    labr_set = set(anny_model.labr_indices)
    anny_to_labr = {}
    for full_idx in range(len(labels)):
        cur = full_idx
        while cur >= 0:
            if cur in labr_set:
                anny_to_labr[full_idx] = anny_model.labr_indices.index(cur)
                break
            cur = parents[cur]
        else:
            anny_to_labr[full_idx] = 0
    bone_assignments = np.array([anny_to_labr.get(d, 0) for d in dominant_full])

    joint_positions = output['rest_bone_heads'][0].detach().cpu().numpy()[anny_model.labr_indices]

    # Sweep each humanoid muscle
    results = {}
    for anny_bone, humanoid_name, muscles in HUMANOID_MUSCLES:
        labr_idx = anny_model.LABR_BONES.index(anny_bone)
        local_frame, jpos = get_bone_local_axes(model, anny_bone)

        children = anny_model.get_children(labr_idx)
        parent_bones = set(range(15)) - children
        child_verts = np.isin(bone_assignments, list(children))
        parent_faces_mask = np.isin(bone_assignments[faces[:, 0]], list(parent_bones))
        child_faces_mask = np.isin(bone_assignments[faces[:, 0]], list(children))

        print(f"\n{humanoid_name} (ANNY: {anny_bone}, labr_idx={labr_idx}):")

        for muscle_name, axis_letter in muscles:
            axis_map = {'x': local_frame[:, 0], 'y': local_frame[:, 1], 'z': local_frame[:, 2]}
            axis_world = axis_map[axis_letter]

            # Sweep positive direction
            pos_limit = sweep_axis(model, anny_bone, axis_world, jpos,
                                    child_verts, parent_faces_mask, child_faces_mask,
                                    verts, faces, direction=1)
            # Sweep negative direction
            neg_limit = sweep_axis(model, anny_bone, axis_world, jpos,
                                    child_verts, parent_faces_mask, child_faces_mask,
                                    verts, faces, direction=-1)

            results[muscle_name] = {
                'min': round(neg_limit, 1),
                'max': round(pos_limit, 1),
            }
            print(f"  {muscle_name}: [{neg_limit:.1f}°, +{pos_limit:.1f}°]")

    # Save as SQLite (long format for AutoGluon)
    import sqlite3
    db_path = output_path.with_suffix('.db')
    conn = sqlite3.connect(str(db_path))
    conn.execute('''CREATE TABLE IF NOT EXISTS rom_samples (
        body_id INTEGER,
        gender REAL,
        age REAL,
        weight REAL,
        height REAL,
        bone_len_0 REAL, bone_len_1 REAL, bone_len_2 REAL, bone_len_3 REAL,
        bone_len_4 REAL, bone_len_5 REAL, bone_len_6 REAL, bone_len_7 REAL,
        bone_len_8 REAL, bone_len_9 REAL, bone_len_10 REAL, bone_len_11 REAL,
        bone_len_12 REAL, bone_len_13 REAL, bone_len_14 REAL,
        muscle_name TEXT,
        min_deg REAL,
        max_deg REAL
    )''')
    conn.execute('DELETE FROM rom_samples')

    # Compute bone lengths
    bone_lengths = []
    for i in range(15):
        parent = anny_model.parent_map[i]
        if parent >= 0:
            length = float(np.linalg.norm(joint_positions[i] - joint_positions[parent]))
        else:
            length = 0.0
        bone_lengths.append(length)

    body_id = 0
    # Phenotype values (from the default forward call)
    gender = 0.5
    age = 30.0
    weight_val = 0.0
    height_val = 0.0

    for muscle_name, limits in results.items():
        conn.execute(
            'INSERT INTO rom_samples VALUES (?,?,?,?,?,' +
            ','.join(['?'] * 15) + ',?,?,?)',
            [body_id, gender, age, weight_val, height_val] +
            bone_lengths +
            [muscle_name, limits['min'], limits['max']]
        )
    conn.commit()

    # Also save JSON for reference
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nSaved {len(results)} muscles to {db_path} (SQLite)")
    print(f"Saved JSON to {output_path}")
    print(f"Schema: body_id, gender, age, weight, height, bone_len_0..14, muscle_name, min_deg, max_deg")
    print(f"Rows: {len(results)} (1 body × {len(results)} muscles)")
    conn.close()


if __name__ == "__main__":
    main()
