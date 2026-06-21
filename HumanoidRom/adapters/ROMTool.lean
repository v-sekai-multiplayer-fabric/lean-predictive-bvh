-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- ROM Tool specification: rest-pose skeleton → per-joint ROM limits.
--
-- Pipeline:
--   1. Input: skeleton rest pose (bone lengths + hierarchy)
--   2. Fit ANNY β from bone lengths (PCA inverse)
--   3. Forward-kinematics ANNY mesh at that β
--   4. For each joint, sweep angles with tapered capsule collision
--   5. Binary search to find self-intersection boundary
--   6. Output: per-joint swing/twist limits in decidegrees
--
-- The tool runs ONCE at skeleton import time.
-- Output is a JSON/resource that EWBIK loads at runtime.

import Shared.Types
import HumanoidRom.core.ROMSampling

namespace PredictiveBVH.ROMTool

open ROMSampling

-- ── Input: rest-pose skeleton ───────────────────────────────────────────────

structure RestBone where
  name     : String
  parentId : Option Nat
  length   : Int       -- micrometres
  deriving Repr, DecidableEq, Inhabited

structure RestSkeleton where
  bones : Array RestBone
  deriving Repr

-- ── ANNY β fitting ──────────────────────────────────────────────────────────
-- Given bone lengths, solve for the 10 PCA β coefficients that best
-- reconstruct those lengths from the ANNY shape basis:
--   bone_length[i] ≈ |J0[i] + Σ_k β[k] * Jbeta[k][i]|
--
-- This is a linear least-squares problem: minimize |A*β - b|²
-- where A[i][k] = |Jbeta[k][i]| (projected onto the bone direction)
-- and b[i] = bone_length[i] - |J0[i]|.

structure AnnyBeta where
  coeffs : Array Int   -- 10 PCA coefficients (× 1000 for precision)
  deriving Repr, DecidableEq, Inhabited

-- ── Output: per-joint ROM ───────────────────────────────────────────────────

structure JointROM where
  boneName     : String
  swingMaxDdeg : Int    -- max swing half-angle (decidegrees)
  twistMinDdeg : Int    -- min twist
  twistMaxDdeg : Int    -- max twist
  deriving Repr, DecidableEq, Inhabited

structure ROMResult where
  joints   : Array JointROM
  beta     : AnnyBeta       -- the fitted body shape
  bodyType : String         -- e.g. "child_5y", "adult_male_avg", "adult_female_tall"
  deriving Repr

-- ── Tool pipeline specification ─────────────────────────────────────────────

/-- The full pipeline: skeleton → β → mesh → collision → ROM.
    Each step is specified here; execution is in Python against ANNY. -/
structure ROMPipeline where
  -- Step 1: map skeleton bones to ANNY's 15 LabRCSF bones
  boneMapping : Array (Nat × Nat)   -- (skeleton_bone_idx, anny_bone_idx)
  -- Step 2: fit β (10 coefficients)
  fittedBeta : AnnyBeta
  -- Step 3: tapered capsules from ANNY mesh at this β
  capsules : Array TaperedCapsule
  -- Step 4: per-joint ROM from collision sweep
  result : ROMResult
  deriving Repr

-- ── Batch mode: sample ANNY population → ROM lookup table ───────────────────

/-- Sample N ANNY bodies, compute ROM for each, build a lookup table.
    The table maps β coefficients → ROM limits.
    At runtime, fit β from the character's skeleton, look up nearest entry. -/
structure ROMTableEntry where
  beta   : AnnyBeta
  joints : Array JointROM
  deriving Repr

/-- Nearest-neighbor lookup: find the table entry closest to the query β. -/
def lookupNearest (table : Array ROMTableEntry) (query : AnnyBeta) : Option ROMTableEntry :=
  if table.size == 0 then none
  else
    let distSq (a b : AnnyBeta) : Int :=
      (List.range (min a.coeffs.size b.coeffs.size)).foldl (fun acc i =>
        let d := a.coeffs[i]! - b.coeffs[i]!
        acc + d * d) 0
    let best := table.foldl (fun (bestEntry, bestDist) entry =>
      let d := distSq query entry.beta
      if d < bestDist then (entry, d) else (bestEntry, bestDist))
      (table[0]!, distSq query table[0]!.beta)
    some best.1

-- ── Verification ────────────────────────────────────────────────────────────

private def testTable : Array ROMTableEntry := #[
  { beta := { coeffs := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] },
    joints := #[{ boneName := "Hips", swingMaxDdeg := 0, twistMinDdeg := 0, twistMaxDdeg := 0 }] },
  { beta := { coeffs := #[1000, 0, 0, 0, 0, 0, 0, 0, 0, 0] },
    joints := #[{ boneName := "Hips", swingMaxDdeg := 0, twistMinDdeg := 0, twistMaxDdeg := 0 }] }
]

/-- Nearest lookup finds the closest β. -/
theorem lookup_finds_nearest :
    let query : AnnyBeta := { coeffs := #[900, 0, 0, 0, 0, 0, 0, 0, 0, 0] }
    match lookupNearest testTable query with
    | some entry => entry.beta.coeffs[0]! = 1000  -- closer to β₀=1000 than β₀=0
    | none => False := by native_decide

end PredictiveBVH.ROMTool
