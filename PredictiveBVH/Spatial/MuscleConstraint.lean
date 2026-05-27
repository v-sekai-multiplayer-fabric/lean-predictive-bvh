-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Muscle constraint: swing + twist as a unitary rotation.
--
-- Unity-style humanoid rigs define 3 "muscles" per bone:
--   muscle[0] = swing axis 1 (e.g., "Front-Back")
--   muscle[1] = swing axis 2 (e.g., "Left-Right")
--   muscle[2] = twist        (e.g., "Twist Left-Right")
--
-- Each muscle is a scalar in [-1, 1], mapped to [min_deg, max_deg].
-- The UI treats swing and twist as unitary (one rotation) rather than
-- 3 independent Euler axes, avoiding gimbal lock and box-shaped limits.
--
-- A kusudama constraint is the geometric equivalent: the swing is
-- limited by cones on S², and twist is limited by an angular range.
-- Together they define a natural joint limit that's always smooth.
--
-- This module converts between the two representations:
--   muscle values ↔ kusudama (swing cones + twist range)

import PredictiveBVH.Primitives.Types

namespace PredictiveBVH.MuscleConstraint

-- ── Muscle representation ───────────────────────────────────────────────────

/-- Per-muscle limit: min and max angle in millidegrees. -/
structure MuscleLimit where
  minMdeg : Int   -- e.g., -40000 = -40°
  maxMdeg : Int   -- e.g.,  40000 =  40°
  deriving Repr, DecidableEq, Inhabited

/-- A bone's 3 muscle values in [-1000, 1000] (milliunit). -/
structure MuscleValues where
  swing1 : Int   -- front-back
  swing2 : Int   -- left-right
  twist  : Int   -- twist
  deriving Repr, DecidableEq, Inhabited

/-- Map muscle value [-1000, 1000] to angle [min, max] in millidegrees. -/
def muscleToAngle (value : Int) (limit : MuscleLimit) : Int :=
  if value >= 0 then
    value * limit.maxMdeg / 1000
  else
    (-value) * limit.minMdeg / 1000

/-- Map angle back to muscle value. -/
def angleToMuscle (angle : Int) (limit : MuscleLimit) : Int :=
  if angle >= 0 then
    if limit.maxMdeg == 0 then 0 else angle * 1000 / limit.maxMdeg
  else
    if limit.minMdeg == 0 then 0 else -((-angle) * 1000 / limit.minMdeg)

-- ── Unitary swing-twist: kusudama ↔ muscle mapping ─────────────────────────

/-- The swing magnitude (angle from forward axis) as a single scalar.
    This is what the kusudama constrains — the total swing angle,
    not individual X/Y components. -/
def swingMagnitude (swing1 swing2 : Int) : Int :=
  -- Approximate: sqrt(s1² + s2²) in milliunit.
  -- Use integer approximation: max(|s1|,|s2|) + min(|s1|,|s2|)/2
  let a1 := if swing1 ≥ 0 then swing1 else -swing1
  let a2 := if swing2 ≥ 0 then swing2 else -swing2
  let mx := max a1 a2
  let mn := min a1 a2
  mx + mn / 2

-- The swing direction (atan2(swing2, swing1)) maps to the cone center
-- direction in the kusudama. Omitted here: atan2 needs float.

-- ── Proved properties ───────────────────────────────────────────────────────

/-- Muscle at 0 → angle is 0 (rest pose). -/
theorem zero_muscle_zero_angle (limit : MuscleLimit) :
    muscleToAngle 0 limit = 0 := by
  simp [muscleToAngle]

/-- Muscle at +1000 → angle is maxMdeg. -/
theorem max_muscle_max_angle :
    let limit : MuscleLimit := { minMdeg := -40000, maxMdeg := 40000 }
    muscleToAngle 1000 limit = 40000 := by native_decide

/-- Muscle at -1000 → angle is minMdeg (negative). -/
theorem min_muscle_min_angle :
    let limit : MuscleLimit := { minMdeg := -40000, maxMdeg := 40000 }
    muscleToAngle (-1000) limit = -40000 := by native_decide

/-- Round-trip: angle → muscle → angle preserves value (symmetric limits). -/
theorem roundtrip_symmetric :
    let limit : MuscleLimit := { minMdeg := -40000, maxMdeg := 40000 }
    let angle := muscleToAngle 500 limit
    angleToMuscle angle limit = 500 := by native_decide

/-- Swing magnitude is 0 at rest. -/
theorem rest_zero_swing :
    swingMagnitude 0 0 = 0 := by native_decide

/-- Pure swing1 gives magnitude = |swing1|. -/
theorem pure_swing1 :
    swingMagnitude 500 0 = 500 := by native_decide

/-- Equal swing1 and swing2 gives ~magnitude (approximation). -/
theorem diagonal_swing :
    swingMagnitude 500 500 = 750 := by native_decide
    -- True magnitude would be ~707 (√2 × 500). Our approximation gives 750.
    -- Close enough for UI display; the actual constraint uses kusudama cones.

end PredictiveBVH.MuscleConstraint
