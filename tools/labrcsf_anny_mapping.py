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
# Most joints: swing_x (front-back), swing_z (left-right), twist_y (along bone)
# Hinge joints (knee, elbow, fingers): swing_x only + twist_y
# Ball-and-socket (hip, shoulder): all 3
JOINT_DOFS = {
    # Core
    'Hips':              ['swing_x', 'swing_z', 'twist_y'],
    'Spine':             ['swing_x', 'swing_z', 'twist_y'],
    'Chest':             ['swing_x', 'swing_z', 'twist_y'],
    'Neck':              ['swing_x', 'swing_z', 'twist_y'],
    'Head':              ['swing_x', 'swing_z', 'twist_y'],
    'Jaw':               ['swing_x'],
    'LeftEye':           ['swing_x', 'swing_z'],
    'RightEye':          ['swing_x', 'swing_z'],
    # Shoulders: 2 DOF (elevation + protraction)
    'LeftShoulder':      ['swing_x', 'swing_z'],
    'RightShoulder':     ['swing_x', 'swing_z'],
    # Upper arms: ball-and-socket
    'LeftUpperArm':      ['swing_x', 'swing_z', 'twist_y'],
    'RightUpperArm':     ['swing_x', 'swing_z', 'twist_y'],
    # Lower arms: hinge + pronation
    'LeftLowerArm':      ['swing_x', 'twist_y'],
    'RightLowerArm':     ['swing_x', 'twist_y'],
    # Hands: 2 DOF (flex + deviation)
    'LeftHand':          ['swing_x', 'swing_z'],
    'RightHand':         ['swing_x', 'swing_z'],
    # Upper legs: ball-and-socket
    'LeftUpperLeg':      ['swing_x', 'swing_z', 'twist_y'],
    'RightUpperLeg':     ['swing_x', 'swing_z', 'twist_y'],
    # Lower legs: hinge + twist
    'LeftLowerLeg':      ['swing_x', 'twist_y'],
    'RightLowerLeg':     ['swing_x', 'twist_y'],
    # Feet: 2 DOF (dorsi/plantar + inversion)
    'LeftFoot':          ['swing_x', 'swing_z'],
    'RightFoot':         ['swing_x', 'swing_z'],
    # Toes: 1 DOF (flex)
    'LeftToes':          ['swing_x'],
    'RightToes':         ['swing_x'],
}

# Fingers: all have swing_x (flex) + swing_z (spread, proximal only)
for side in ['Left', 'Right']:
    for finger in ['Thumb', 'Index', 'Middle', 'Ring', 'Pinky']:
        for segment in ['Metacarpal', 'Proximal', 'Intermediate', 'Distal']:
            name = f'{side}{finger}{segment}'
            if name in LABRCSF_TO_ANNY:
                if segment in ['Metacarpal', 'Proximal']:
                    JOINT_DOFS[name] = ['swing_x', 'swing_z']
                else:
                    JOINT_DOFS[name] = ['swing_x']

def get_all_joints():
    """Return list of (labrcsf_name, anny_bone, dofs)."""
    result = []
    for labrcsf, anny in LABRCSF_TO_ANNY.items():
        dofs = JOINT_DOFS.get(labrcsf, ['swing_x', 'swing_z', 'twist_y'])
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
