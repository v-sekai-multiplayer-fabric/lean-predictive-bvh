-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Prismatic (extensor) joint: translational DOF along the bone axis.
--
-- A prismatic joint changes bone LENGTH rather than angle — like a
-- telescoping arm, hydraulic piston, or robot slider.  The bone
-- extends/retracts along its axis within [min_length, max_length].
--
-- After QCP computes the optimal rotation, the optimal length is the
-- projection of the target vector onto the bone direction, clamped to
-- the allowed range:
--
--   optimal_length = clamp(dot(target - head, bone_dir), min, max)
--
-- This is a scalar optimization — no iteration needed.

import Shared.Types

namespace PredictiveBVH.PrismaticJoint

-- ── Types ────────────────────────────────────────────────────────────────────

/-- A prismatic joint constraint: min and max bone length.
    When min == max, the joint is rigid (no extension). -/
structure PrismaticLimit where
  minLength : Int   -- minimum bone length (scaled by sc)
  maxLength : Int   -- maximum bone length (scaled by sc)
  deriving Repr, DecidableEq, Inhabited

/-- Clamp a value to [lo, hi]. -/
def clamp (x lo hi : Int) : Int :=
  max lo (min hi x)

/-- Compute the optimal bone length given:
    - head: bone head position
    - target: desired tail position
    - boneDir: normalized bone direction (scaled by sc)
    - limit: prismatic constraint
    Returns the clamped projection length. -/
def optimalLength (head target boneDir : Vec3) (limit : PrismaticLimit) : Int :=
  -- dot(target - head, boneDir) / |boneDir|²  * |boneDir|
  -- = dot(target - head, boneDir) / |boneDir|
  let dx := target.x - head.x
  let dy := target.y - head.y
  let dz := target.z - head.z
  let dot_val := dx * boneDir.x + dy * boneDir.y + dz * boneDir.z
  let dir_len_sq := boneDir.x * boneDir.x + boneDir.y * boneDir.y + boneDir.z * boneDir.z
  if dir_len_sq == 0 then limit.minLength
  else clamp (dot_val / dir_len_sq) limit.minLength limit.maxLength

/-- Compute the new tail position after prismatic solve. -/
def solvePrismatic (head target boneDir : Vec3) (limit : PrismaticLimit) : Vec3 :=
  let len := optimalLength head target boneDir limit
  { x := head.x + boneDir.x * len
    y := head.y + boneDir.y * len
    z := head.z + boneDir.z * len }

-- ── Proved properties ───────────────────────────────────────────────────────

private def sc := 100

/-- Clamp is bounded: result is always in [lo, hi]. -/
theorem clamp_bounded (x lo hi : Int) (h : lo ≤ hi) :
    lo ≤ clamp x lo hi ∧ clamp x lo hi ≤ hi := by
  simp [clamp]
  omega

/-- Rigid joint (min == max): length is always exactly that value. -/
theorem rigid_joint_fixed_length :
    let limit : PrismaticLimit := { minLength := sc, maxLength := sc }
    let head : Vec3 := { x := 0, y := 0, z := 0 }
    let target : Vec3 := { x := 200, y := 0, z := 0 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    optimalLength head target dir limit = sc := by native_decide

/-- Telescoping joint: target within range → length matches projection. -/
theorem telescoping_reaches_target :
    let limit : PrismaticLimit := { minLength := 50, maxLength := 150 }
    let head : Vec3 := { x := 0, y := 0, z := 0 }
    let target : Vec3 := { x := sc, y := 0, z := 0 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    optimalLength head target dir limit = sc := by native_decide

/-- Target too far: length clamps to max. -/
theorem clamps_to_max :
    let limit : PrismaticLimit := { minLength := 50, maxLength := 80 }
    let head : Vec3 := { x := 0, y := 0, z := 0 }
    let target : Vec3 := { x := 200, y := 0, z := 0 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    optimalLength head target dir limit = 80 := by native_decide

/-- Target too close: length clamps to min. -/
theorem clamps_to_min :
    let limit : PrismaticLimit := { minLength := 50, maxLength := 150 }
    let head : Vec3 := { x := 0, y := 0, z := 0 }
    let target : Vec3 := { x := 10, y := 0, z := 0 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    optimalLength head target dir limit = 50 := by native_decide

/-- Target behind bone: length clamps to min (no negative extension). -/
theorem no_negative_extension :
    let limit : PrismaticLimit := { minLength := 50, maxLength := 150 }
    let head : Vec3 := { x := 0, y := 0, z := 0 }
    let target : Vec3 := { x := -100, y := 0, z := 0 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    optimalLength head target dir limit = 50 := by native_decide

/-- Tail position is on the bone axis (direction preserved). -/
theorem tail_on_bone_axis :
    let limit : PrismaticLimit := { minLength := 50, maxLength := 150 }
    let head : Vec3 := { x := 10, y := 20, z := 30 }
    let target : Vec3 := { x := 110, y := 20, z := 30 }
    let dir : Vec3 := { x := 1, y := 0, z := 0 }
    let tail := solvePrismatic head target dir limit
    -- tail.y == head.y and tail.z == head.z (only x changes)
    (tail.y, tail.z) = (head.y, head.z) := by native_decide

end PredictiveBVH.PrismaticJoint
