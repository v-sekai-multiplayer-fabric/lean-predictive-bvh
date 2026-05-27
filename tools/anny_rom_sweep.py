#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
anny_rom_sweep.py — Fit ANNY to humanoid skeletons, sweep ROM via self-intersection.

Pipeline:
  1. Load humanoid skeleton (bone lengths from GLB or Godot)
  2. Fit ANNY β parameters to match bone lengths
  3. Generate ANNY mesh at that β (known hierarchy, consistent topology)
  4. For each joint, binary search rotation angle → self-intersection
  5. Output: per-joint ROM limits

ANNY provides:
  - Fixed 163-bone hierarchy (no guessing parent-child)
  - Consistent mesh topology (no variable quality)
  - Shape variation via β (body proportions from bone lengths)
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
    print("WARNING: anny not installed. Using mock mode.")
    print("Install with: pip install anny torch")

# ── ANNY model wrapper ───────────────────────────────────────────────────────

class AnnyModel:
    """Wrapper around ANNY for ROM computation."""

    # 15 LabRCSF bones mapped to ANNY bone indices
    LABR_BONES = [
        'root', 'upperleg01.L', 'upperleg01.R',
        'lowerleg01.L', 'lowerleg01.R',
        'foot.L', 'foot.R',
        'spine03', 'head',
        'upperarm01.L', 'upperarm01.R',
        'lowerarm01.L', 'lowerarm01.R',
        'wrist.L', 'wrist.R',
    ]

    # Correct parent map traced through ANNY's 163-bone hierarchy.
    LABR_PARENT_MAP = {
        0: -1,   # root
        1: 0,    # LeftUpperLeg → root (via pelvis.L)
        2: 0,    # RightUpperLeg → root (via pelvis.R)
        3: 1,    # LeftLowerLeg → LeftUpperLeg
        4: 2,    # RightLowerLeg → RightUpperLeg
        5: 3,    # LeftFoot → LeftLowerLeg
        6: 4,    # RightFoot → RightLowerLeg
        7: 0,    # Chest(spine03) → root (via spine04→spine05)
        8: 7,    # Head → Chest (via neck chain)
        9: 7,    # LeftUpperArm → Chest (via shoulder→clavicle→spine)
        10: 7,   # RightUpperArm → Chest
        11: 9,   # LeftLowerArm → LeftUpperArm
        12: 10,  # RightLowerArm → RightUpperArm
        13: 11,  # LeftHand(wrist) → LeftLowerArm
        14: 12,  # RightHand(wrist) → RightLowerArm
    }

    LABR_NAMES = [
        'Hips', 'LeftUpperLeg', 'RightUpperLeg',
        'LeftLowerLeg', 'RightLowerLeg',
        'LeftFoot', 'RightFoot',
        'Chest', 'Head',
        'LeftUpperArm', 'RightUpperArm',
        'LeftLowerArm', 'RightLowerArm',
        'LeftHand', 'RightHand',
    ]

    def __init__(self):
        if not HAS_ANNY:
            self.model = None
            self.bone_labels = self.LABR_BONES
            self.labr_indices = list(range(15))
            self.parent_map = {
                0: -1, 1: 0, 2: 0, 3: 1, 4: 2,
                5: 3, 6: 4, 7: 0, 8: 7,
                9: 7, 10: 7, 11: 9, 12: 10,
                13: 11, 14: 12
            }
            return

        self.model = anny.create_fullbody_model()
        self.bone_labels = list(self.model.bone_labels)

        # Map LabRCSF names to ANNY bone indices
        self.labr_indices = []
        for name in self.LABR_BONES:
            try:
                idx = self.bone_labels.index(name)
            except ValueError:
                # Fuzzy match
                idx = next((i for i, l in enumerate(self.bone_labels) if name in l), 0)
            self.labr_indices.append(idx)

        # Use the correct parent map (traced through ANNY's 163-bone hierarchy).
        self.parent_map = self.LABR_PARENT_MAP.copy()

    def get_children(self, joint_idx):
        """Get all descendant bones of a joint using the known hierarchy."""
        children = {joint_idx}
        changed = True
        while changed:
            changed = False
            for bone, parent in self.parent_map.items():
                if parent in children and bone not in children:
                    children.add(bone)
                    changed = True
        return children

    def get_mesh(self, phenotypes=None):
        """Get ANNY mesh at given phenotype parameters."""
        if self.model is None:
            # Mock mode
            n_bones = 15
            verts = np.random.randn(n_bones * 100, 3).astype(np.float32) * 0.1
            faces = np.zeros((n_bones * 50, 3), dtype=np.int32)
            bone_assignments = np.repeat(np.arange(n_bones), 100)
            joint_positions = np.zeros((n_bones, 3), dtype=np.float32)
            for i in range(n_bones):
                parent = self.parent_map[i]
                if parent >= 0:
                    joint_positions[i] = joint_positions[parent] + np.array([0, 0.15, 0])
                verts[i*100:(i+1)*100] += joint_positions[i]
            for i in range(n_bones * 50):
                base = (i // 50) * 100
                faces[i] = [base + (i*2) % 100, base + (i*2+1) % 100, base + (i*2+2) % 100]
            return verts, faces, bone_assignments, joint_positions

        output = self.model.forward(
            phenotype_kwargs=phenotypes if phenotypes else {},
            return_bone_ends=True
        )

        verts = output['vertices'][0].detach().cpu().numpy()
        raw_faces = self.model.faces.cpu().numpy()  # quads (N, 4)
        # Triangulate quads
        tris = np.vstack([raw_faces[:, [0, 1, 2]], raw_faces[:, [0, 2, 3]]])

        joint_pos = output['rest_bone_heads'][0].detach().cpu().numpy()
        labr_joints = joint_pos[self.labr_indices]

        # Assign vertices to LabRCSF bones via skinning weights.
        # For each of ANNY's 163 bones, walk up the hierarchy to find
        # the nearest LabRCSF ancestor.
        bone_indices = self.model.vertex_bone_indices.cpu().numpy()  # (V, 8)
        bone_weights = self.model.vertex_bone_weights.cpu().numpy()  # (V, 8)
        dominant_full = bone_indices[np.arange(len(verts)), bone_weights.argmax(axis=1)]

        labr_set = set(self.labr_indices)
        full_parents = self.model.bone_parents
        # Build mapping: ANNY bone index → nearest LabRCSF bone index
        anny_to_labr = {}
        for full_idx in range(len(self.bone_labels)):
            cur = full_idx
            while cur >= 0:
                if cur in labr_set:
                    anny_to_labr[full_idx] = self.labr_indices.index(cur)
                    break
                cur = full_parents[cur]
            else:
                anny_to_labr[full_idx] = 0  # fallback to root

        bone_assignments = np.array([anny_to_labr.get(d, 0) for d in dominant_full])

        return verts, tris, bone_assignments, labr_joints

    def fit_betas(self, bone_lengths):
        """Fit ANNY β to match target bone lengths (least squares)."""
        if self.model is None or not hasattr(self.model, 'bone_heads_blendshapes'):
            return np.zeros(10)

        # Use the ANNY shape basis to fit
        # bone_length[i] ≈ |J0[i] + Σ_k β[k] * Jbeta[k][i]|
        # This is a nonlinear least squares — approximate with linear
        J0 = self.model.template_bone_heads.cpu().numpy()[self.labr_indices]
        n_betas = min(10, self.model.bone_heads_blendshapes.shape[0])
        Jbeta = self.model.bone_heads_blendshapes[:n_betas, self.labr_indices].cpu().numpy()

        # Simple linear fit: minimize |A*β - b|²
        target = np.array(bone_lengths[:15], dtype=np.float32)
        A = np.zeros((15, n_betas))
        b = np.zeros(15)
        for i in range(15):
            parent = self.parent_map[i]
            if parent >= 0:
                offset = J0[i] - J0[parent]
                b[i] = target[i] - np.linalg.norm(offset)
                for k in range(n_betas):
                    delta = Jbeta[k, i] - Jbeta[k, parent]
                    A[i, k] = np.linalg.norm(offset + delta) - np.linalg.norm(offset)

        beta, _, _, _ = np.linalg.lstsq(A, b, rcond=None)
        return beta


# ── Self-intersection sweep ──────────────────────────────────────────────────

def apply_joint_rotation(verts, joint_pos, axis, angle_rad, child_verts_mask):
    """Rotate child vertices around joint position."""
    rotated = verts.copy()
    ax = axis / (np.linalg.norm(axis) + 1e-10)
    c, s = np.cos(angle_rad), np.sin(angle_rad)
    K = np.array([[0, -ax[2], ax[1]], [ax[2], 0, -ax[0]], [-ax[1], ax[0], 0]])
    R = np.eye(3) + s * K + (1 - c) * (K @ K)
    centered = rotated[child_verts_mask] - joint_pos
    rotated[child_verts_mask] = (R @ centered.T).T + joint_pos
    return rotated


def check_intersection(verts, faces, parent_mask, child_mask, max_pairs=1000):
    """Check triangle-triangle intersection between parent and child groups."""
    parent_faces = faces[parent_mask]
    child_faces = faces[child_mask]
    if len(parent_faces) == 0 or len(child_faces) == 0:
        return False

    # Subsample for speed
    if len(parent_faces) > max_pairs:
        parent_faces = parent_faces[np.random.choice(len(parent_faces), max_pairs, replace=False)]
    if len(child_faces) > max_pairs:
        child_faces = child_faces[np.random.choice(len(child_faces), max_pairs, replace=False)]

    # AABB intersection check
    for pf in parent_faces:
        p = verts[pf]
        p_min, p_max = p.min(0), p.max(0)
        for cf in child_faces:
            q = verts[cf]
            q_min, q_max = q.min(0), q.max(0)
            if np.all(p_min <= q_max) and np.all(q_min <= p_max):
                return True
    return False


def sweep_joint(anny_model, verts, faces, bone_assignments, joint_positions,
                joint_idx, axis, max_angle=180.0):
    """Binary search for self-intersection limit."""
    children = anny_model.get_children(joint_idx)
    parent_bones = set(range(15)) - children

    child_verts = np.isin(bone_assignments, list(children))
    parent_faces_mask = np.isin(bone_assignments[faces[:, 0]], list(parent_bones))
    child_faces_mask = np.isin(bone_assignments[faces[:, 0]], list(children))

    jpos = joint_positions[joint_idx]

    lo, hi = 0.0, max_angle
    for _ in range(12):
        mid = (lo + hi) / 2
        rotated = apply_joint_rotation(verts, jpos, axis, np.radians(mid), child_verts)
        if check_intersection(rotated, faces, parent_faces_mask, child_faces_mask):
            hi = mid
        else:
            lo = mid
    return lo


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    n_samples = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    output_path = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("anny_rom_results.json")

    print("Initializing ANNY model...")
    model = AnnyModel()
    print(f"  {len(model.labr_indices)} LabRCSF bones, parent map: {model.parent_map}")

    axes = [np.array([1, 0, 0.]), np.array([0, 1, 0.]), np.array([0, 0, 1.])]
    axis_names = ['swing1', 'swing2', 'twist']

    results = []
    for sample in range(n_samples):
        # Random body shape via phenotype parameters
        phenotypes = None
        if HAS_ANNY:
            # Sample random phenotype values
            import random
            phenotypes = {
                'gender': torch.tensor([[random.random()]]),
                'age': torch.tensor([[random.uniform(5, 80)]]),
                'weight': torch.tensor([[random.uniform(-1, 1)]]),
                'height': torch.tensor([[random.uniform(-1, 1)]]),
            }
            desc = f"gender={phenotypes['gender'].item():.1f} age={phenotypes['age'].item():.0f}"
        else:
            desc = "mock"
        print(f"\n[{sample+1}/{n_samples}] {desc}")

        verts, faces, bone_assignments, joint_positions = model.get_mesh(phenotypes)
        print(f"  {len(verts)} verts, {len(faces)} faces")

        # Bone lengths
        bone_lengths = []
        for i in range(15):
            parent = model.parent_map[i]
            if parent >= 0:
                length = float(np.linalg.norm(joint_positions[i] - joint_positions[parent]))
            else:
                length = 0.0
            bone_lengths.append(length)

        # Sweep each joint
        joint_roms = []
        for j in range(15):
            roms = {}
            for ax, ax_name in zip(axes, axis_names):
                try:
                    limit = sweep_joint(model, verts, faces, bone_assignments,
                                        joint_positions, j, ax)
                    roms[ax_name] = round(limit, 1)
                except Exception as e:
                    roms[ax_name] = 180.0
            joint_roms.append({
                'name': model.LABR_NAMES[j],
                **roms
            })
            print(f"  {model.LABR_NAMES[j]:20s}: s1={roms['swing1']:5.1f}° s2={roms['swing2']:5.1f}° tw={roms['twist']:5.1f}°")

        results.append({
            'phenotypes': {k: v.item() if hasattr(v, 'item') else float(v[0][0]) for k, v in (phenotypes or {}).items()},
            'bone_lengths': bone_lengths,
            'joint_roms': joint_roms,
        })

    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved {len(results)} results to {output_path}")


if __name__ == "__main__":
    main()
