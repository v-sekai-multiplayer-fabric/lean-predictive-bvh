#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
Complete LabRCSF → ANNY bone mapping for ROM sweep.
"""

# LabRCSF CanonicalJoint → ANNY bone name
# Based on meshula/LabRCSF joints.csv + ANNY bone_labels
LABRCSF_TO_ANNY = {
    # Core body
    'Hips':                     'root',
    'Spine':                    'spine05',
    'Chest':                    'spine03',
    'Neck':                     'neck01',
    'Head':                     'head',
    'Jaw':                      'jaw',
    # Eyes
    'LeftEye':                  'eye.L',
    'RightEye':                 'eye.R',
    # Left shoulder + arm
    'LeftShoulder':             'clavicle.L',
    'LeftUpperArm':             'upperarm01.L',
    'LeftLowerArm':             'lowerarm01.L',
    'LeftHand':                 'wrist.L',
    # Left thumb
    'LeftThumbMetacarpal':      'metacarpal1.L',
    'LeftThumbProximal':        'finger1-1.L',
    'LeftThumbDistal':          'finger1-2.L',
    # Left index
    'LeftIndexProximal':        'finger2-1.L',
    'LeftIndexIntermediate':    'finger2-2.L',
    'LeftIndexDistal':          'finger2-3.L',
    # Left middle
    'LeftMiddleProximal':       'finger3-1.L',
    'LeftMiddleIntermediate':   'finger3-2.L',
    'LeftMiddleDistal':         'finger3-3.L',
    # Left ring
    'LeftRingProximal':         'finger4-1.L',
    'LeftRingIntermediate':     'finger4-2.L',
    'LeftRingDistal':           'finger4-3.L',
    # Left pinky
    'LeftPinkyProximal':        'finger5-1.L',
    'LeftPinkyIntermediate':    'finger5-2.L',
    'LeftPinkyDistal':          'finger5-3.L',
    # Right shoulder + arm
    'RightShoulder':            'clavicle.R',
    'RightUpperArm':            'upperarm01.R',
    'RightLowerArm':            'lowerarm01.R',
    'RightHand':                'wrist.R',
    # Right thumb
    'RightThumbMetacarpal':     'metacarpal1.R',
    'RightThumbProximal':       'finger1-1.R',
    'RightThumbDistal':         'finger1-2.R',
    # Right index
    'RightIndexProximal':       'finger2-1.R',
    'RightIndexIntermediate':   'finger2-2.R',
    'RightIndexDistal':         'finger2-3.R',
    # Right middle
    'RightMiddleProximal':      'finger3-1.R',
    'RightMiddleIntermediate':  'finger3-2.R',
    'RightMiddleDistal':        'finger3-3.R',
    # Right ring
    'RightRingProximal':        'finger4-1.R',
    'RightRingIntermediate':    'finger4-2.R',
    'RightRingDistal':          'finger4-3.R',
    # Right pinky
    'RightPinkyProximal':       'finger5-1.R',
    'RightPinkyIntermediate':   'finger5-2.R',
    'RightPinkyDistal':         'finger5-3.R',
    # Left leg
    'LeftUpperLeg':             'upperleg01.L',
    'LeftLowerLeg':             'lowerleg01.L',
    'LeftFoot':                 'foot.L',
    'LeftToes':                 'toe1-1.L',
    # Right leg
    'RightUpperLeg':            'upperleg01.R',
    'RightLowerLeg':            'lowerleg01.R',
    'RightFoot':                'foot.R',
    'RightToes':                'toe1-1.R',
}

# DOFs per joint type
# DOF types:
#   flexion   — bending in the sagittal plane (flex/extend)
#   abduction — spreading in the frontal plane (abduct/adduct)
#   rotation  — twist along the bone axis (internal/external)
#   linear    — translation along the bone axis (extend/retract, prismatic)
#
# Every joint has 'linear' for the prismatic/extensor DOF (bone length change).
# Rotational DOFs vary by joint type.
JOINT_DOFS = {
    # Core — no linear (rigid bones, not prismatic)
    'Hips':              ['flexion', 'abduction', 'rotation'],
    'Spine':             ['flexion', 'abduction', 'rotation', 'linear'],
    'Chest':             ['flexion', 'abduction', 'rotation', 'linear'],
    'Neck':              ['flexion', 'abduction', 'rotation'],
    'Head':              ['flexion', 'abduction', 'rotation'],
    'Jaw':               ['flexion'],
    'LeftEye':           ['flexion', 'abduction'],
    'RightEye':          ['flexion', 'abduction'],
    # Shoulders: 2 rotational + linear (clavicle can shrug/protract)
    'LeftShoulder':      ['flexion', 'abduction', 'linear'],
    'RightShoulder':     ['flexion', 'abduction', 'linear'],
    # Upper arms: ball-and-socket + linear (upper arm length varies with posture)
    'LeftUpperArm':      ['flexion', 'abduction', 'rotation', 'linear'],
    'RightUpperArm':     ['flexion', 'abduction', 'rotation', 'linear'],
    # Lower arms: hinge + pronation + linear
    'LeftLowerArm':      ['flexion', 'rotation', 'linear'],
    'RightLowerArm':     ['flexion', 'rotation', 'linear'],
    # Hands: 2 rotational (no linear — wrist doesn't telescope)
    'LeftHand':          ['flexion', 'abduction'],
    'RightHand':         ['flexion', 'abduction'],
    # Upper legs: ball-and-socket + linear
    'LeftUpperLeg':      ['flexion', 'abduction', 'rotation', 'linear'],
    'RightUpperLeg':     ['flexion', 'abduction', 'rotation', 'linear'],
    # Lower legs: hinge + twist + linear
    'LeftLowerLeg':      ['flexion', 'rotation', 'linear'],
    'RightLowerLeg':     ['flexion', 'rotation', 'linear'],
    # Feet: 2 rotational (no linear — feet don't telescope)
    'LeftFoot':          ['flexion', 'abduction'],
    'RightFoot':         ['flexion', 'abduction'],
    # Toes: flex only (no linear)
    'LeftToes':          ['flexion'],
    'RightToes':         ['flexion'],
}

# Fingers: flexion + abduction (spread, metacarpal/proximal only)
# No linear — finger bones don't telescope.
for side in ['Left', 'Right']:
    for finger in ['Thumb', 'Index', 'Middle', 'Ring', 'Pinky']:
        for segment in ['Metacarpal', 'Proximal', 'Intermediate', 'Distal']:
            name = f'{side}{finger}{segment}'
            if name in LABRCSF_TO_ANNY:
                if segment in ['Metacarpal', 'Proximal']:
                    JOINT_DOFS[name] = ['flexion', 'abduction']
                else:
                    JOINT_DOFS[name] = ['flexion']

def get_all_joints():
    """Return list of (labrcsf_name, anny_bone, dofs)."""
    result = []
    for labrcsf, anny in LABRCSF_TO_ANNY.items():
        dofs = JOINT_DOFS.get(labrcsf, ['flexion', 'abduction', 'rotation'])
        result.append((labrcsf, anny, dofs))
    return result

if __name__ == '__main__':
    joints = get_all_joints()
    print(f"{len(joints)} LabRCSF joints mapped to ANNY:")
    total_dofs = 0
    for labrcsf, anny, dofs in joints:
        total_dofs += len(dofs)
        print(f"  {labrcsf:30s} → {anny:20s} ({', '.join(dofs)})")
    print(f"\nTotal: {len(joints)} joints, {total_dofs} DOFs")
