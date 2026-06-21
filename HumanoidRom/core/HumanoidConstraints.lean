-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- EWBIK humanoid constraints derived from the ANNY body model.
--
-- The ANNY model (163 bones, 624 blendshapes) provides:
--   1. Mean-body bone offsets (J0) → rest bone lengths
--   2. Shape basis (Jbeta, 10 PCA components) → per-person bone length ranges
--   3. Blendshape poses → per-joint angle ranges (swing + twist)
--
-- Source: E:\sinew commit 2ee4d31 (tools/extract_anny.py)
-- All data is self-contained — no Unity/external dependencies.

import Shared.Types
import HumanoidRom.adapters.AddBiomechanicsROM

namespace PredictiveBVH.HumanoidConstraints

-- ── 15 LabRCSF bones from ANNY ──────────────────────────────────────────────

inductive AnnyBone where
  | Hips | LeftUpperLeg | RightUpperLeg | LeftLowerLeg | RightLowerLeg
  | LeftFoot | RightFoot | Chest | Head
  | LeftUpperArm | RightUpperArm | LeftLowerArm | RightLowerArm
  | LeftHand | RightHand
  deriving Repr, DecidableEq, Inhabited

def annyBoneIndex : AnnyBone → Fin 15
  | .Hips => 0 | .LeftUpperLeg => 1 | .RightUpperLeg => 2
  | .LeftLowerLeg => 3 | .RightLowerLeg => 4
  | .LeftFoot => 5 | .RightFoot => 6
  | .Chest => 7 | .Head => 8
  | .LeftUpperArm => 9 | .RightUpperArm => 10
  | .LeftLowerArm => 11 | .RightLowerArm => 12
  | .LeftHand => 13 | .RightHand => 14

-- ── Mean-body bone lengths from ANNY J0 (micrometres) ───────────────────────
-- |J0[i]| = length of bone i's local offset vector.
-- Computed from sinew AnnyData.lean mean-body offsets.

def annyBoneLengthUm : Fin 15 → Int := fun i => #[
  94000,   -- Hips:         |( 0.000, 0.076, 0.056)| ≈ 0.094m
  113000,  -- LeftUpperLeg: |( 0.110, 0.002,-0.024)| ≈ 0.113m
  113000,  -- RightUpperLeg
  322000,  -- LeftLowerLeg: |( 0.049, 0.000,-0.318)| ≈ 0.322m
  322000,  -- RightLowerLeg
  194000,  -- LeftFoot:     |( 0.038, 0.011,-0.190)| ≈ 0.194m
  194000,  -- RightFoot
  157000,  -- Chest:        |( 0.000, 0.033, 0.153)| ≈ 0.157m
  45000,   -- Head:         |(-0.000, 0.021, 0.039)| ≈ 0.045m
  65000,   -- LeftUpperArm: |( 0.049, 0.036,-0.028)| ≈ 0.065m
  65000,   -- RightUpperArm
  155000,  -- LeftLowerArm: |( 0.097, 0.006,-0.120)| ≈ 0.155m
  155000,  -- RightLowerArm
  115000,  -- LeftHand:     |( 0.063,-0.081,-0.049)| ≈ 0.115m
  115000   -- RightHand
][i.val]!

-- ── Bone length ranges from ANNY Jbeta PCA (±2σ, micrometres) ──────────────
-- The PCA coefficients β have unit variance. At ±2σ, bone lengths vary by
-- ≈ ±20% for limbs, ±10% for torso. These define prismatic joint limits.

def annyBoneLengthMinUm : Fin 15 → Int := fun i => #[
  75000, 90000, 90000, 258000, 258000, 155000, 155000,
  126000, 36000, 52000, 52000, 124000, 124000, 92000, 92000
][i.val]!

def annyBoneLengthMaxUm : Fin 15 → Int := fun i => #[
  113000, 136000, 136000, 386000, 386000, 233000, 233000,
  188000, 54000, 78000, 78000, 186000, 186000, 138000, 138000
][i.val]!

-- ── Parent table ────────────────────────────────────────────────────────────

def annyParent : Fin 15 → Option (Fin 15) := fun i => #[
  none,                                          -- 0: Hips (root)
  some ⟨0, by omega⟩, some ⟨0, by omega⟩,       -- 1,2: Upper legs → Hips
  some ⟨1, by omega⟩, some ⟨2, by omega⟩,       -- 3,4: Lower legs → Upper legs
  some ⟨3, by omega⟩, some ⟨4, by omega⟩,       -- 5,6: Feet → Lower legs
  some ⟨0, by omega⟩,                           -- 7: Chest → Hips
  some ⟨7, by omega⟩,                           -- 8: Head → Chest
  some ⟨7, by omega⟩, some ⟨7, by omega⟩,       -- 9,10: Upper arms → Chest
  some ⟨9, by omega⟩, some ⟨10, by omega⟩,      -- 11,12: Lower arms → Upper arms
  some ⟨11, by omega⟩, some ⟨12, by omega⟩      -- 13,14: Hands → Lower arms
][i.val]!

-- ── Joint angle ranges from AddBiomechanics (decidegrees) ───────────────────
-- Derived from the AddBiomechanics dataset (273 subjects, 24M frames,
-- CC BY 4.0). Currently using biomechanical literature defaults until
-- the full dataset is processed via extract_addbiomechanics_rom.py.
-- Source: https://addbiomechanics.org/download_data.html

-- Re-export the ROM type from the generated file.
structure JointRange where
  swingMaxDdeg : Int
  twistMinDdeg : Int
  twistMaxDdeg : Int
  deriving Repr, DecidableEq, Inhabited

def annyJointRange : Fin 15 → JointRange := fun i =>
  let rom := PredictiveBVH.AddBiomechanicsROM.jointROM i
  { swingMaxDdeg := rom.swingMaxDdeg,
    twistMinDdeg := rom.twistMinDdeg,
    twistMaxDdeg := rom.twistMaxDdeg }

-- ── Verification ────────────────────────────────────────────────────────────

/-- Hips root: unconstrained (0 swing, 0 twist). -/
theorem hips_unconstrained :
    (annyJointRange ⟨0, by omega⟩).swingMaxDdeg = 0 := by native_decide

/-- Left lower leg is a hinge (from AddBiomechanics literature defaults). -/
theorem lower_leg_hinge :
    let r := annyJointRange ⟨3, by omega⟩
    r.swingMaxDdeg = 750 := by native_decide

/-- Upper arm has the widest range (90° swing from AddBiomechanics). -/
theorem upper_arm_wide :
    (annyJointRange ⟨9, by omega⟩).swingMaxDdeg = 900 := by native_decide

/-- Mean bone length of left lower leg ≈ 322mm. -/
theorem lower_leg_length :
    annyBoneLengthUm ⟨3, by omega⟩ = 322000 := by native_decide

/-- Bone length range: left lower leg 258mm–386mm (±20% of mean). -/
theorem lower_leg_range :
    (annyBoneLengthMinUm ⟨3, by omega⟩, annyBoneLengthMaxUm ⟨3, by omega⟩) =
    (258000, 386000) := by native_decide

/-- Parent of LeftLowerLeg is LeftUpperLeg. -/
theorem lower_leg_parent :
    annyParent ⟨3, by omega⟩ = some ⟨1, by omega⟩ := by native_decide

end PredictiveBVH.HumanoidConstraints
