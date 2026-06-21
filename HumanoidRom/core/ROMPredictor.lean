-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- ROM predictor: decision tree executable in pure Lean.
--
-- A decision tree trained on ANNY body samples maps β[10] → ROM[45].
-- The tree is exported from Python as Lean code — each internal node
-- splits on a β coefficient, each leaf stores the predicted ROM values.
--
-- Pipeline:
--   1. Python: sample 1000 ANNY bodies, compute ROM via self-intersection
--   2. Python: train sklearn DecisionTreeRegressor(max_depth=8)
--   3. Python: export tree as Lean code (tools/export_tree_to_lean.py)
--   4. Lean: evaluate — pure function, O(depth) per query, no external deps

import Shared.Types

namespace PredictiveBVH.ROMPredictor

-- ── Decision tree structure ─────────────────────────────────────────────────

/-- A decision tree node: either a split or a leaf. -/
inductive TreeNode where
  | leaf (values : Array Int)            -- ROM predictions (45 values, decidegrees)
  | split (feature : Nat)                -- which β coefficient to test (0..9)
          (threshold : Int)              -- split threshold (β × 1000)
          (left right : TreeNode)        -- left = β < threshold, right = β ≥ threshold
  deriving Repr, Inhabited

/-- Evaluate the decision tree on a β vector.
    Returns an array of 45 ROM values (15 joints × 3 DOF). -/
def predict (tree : TreeNode) (beta : Array Int) : (fuel : Nat) → Array Int
  | 0 => #[]
  | fuel + 1 =>
    match tree with
    | .leaf values => values
    | .split feature threshold left right =>
      let val := if feature < beta.size then beta[feature]! else 0
      if val < threshold then predict left beta fuel
      else predict right beta fuel

-- ── Placeholder tree (replaced by export_tree_to_lean.py after training) ────
-- This is a hand-crafted tree that demonstrates the structure.
-- It splits on β₀ (overall body size) to give rough child/adult ROM.

def placeholderTree : TreeNode :=
  .split 0 0  -- β₀ < 0 → smaller body (child-like)
    (.split 1 0  -- β₁ < 0 → lighter build
      (.leaf #[  -- Small + light: tighter ROM
        0, 0, 0,            -- Hips (root)
        500, -500, 500,     -- LeftUpperLeg
        500, -500, 500,     -- RightUpperLeg
        650, -50, 800,      -- LeftLowerLeg
        650, -50, 800,      -- RightLowerLeg
        300, -200, 200,     -- LeftFoot
        300, -200, 200,     -- RightFoot
        350, -350, 350,     -- Chest
        350, -350, 350,     -- Head
        800, -800, 800,     -- LeftUpperArm
        800, -800, 800,     -- RightUpperArm
        650, -50, 750,      -- LeftLowerArm
        650, -50, 750,      -- RightLowerArm
        350, -250, 250,     -- LeftHand
        350, -250, 250])    -- RightHand
      (.leaf #[  -- Small + heavy: tightest ROM (stocky child)
        0, 0, 0,
        450, -400, 450,
        450, -400, 450,
        600, -50, 750,
        600, -50, 750,
        250, -200, 200,
        250, -200, 200,
        300, -300, 300,
        300, -300, 300,
        700, -700, 700,
        700, -700, 700,
        600, -50, 700,
        600, -50, 700,
        300, -200, 200,
        300, -200, 200]))
    (.split 1 0  -- β₁ < 0 → lean adult
      (.leaf #[  -- Tall + lean: widest ROM
        0, 0, 0,
        600, -600, 600,
        600, -600, 600,
        750, -50, 900,
        750, -50, 900,
        350, -250, 250,
        350, -250, 250,
        400, -400, 400,
        400, -400, 400,
        900, -900, 900,
        900, -900, 900,
        750, -50, 850,
        750, -50, 850,
        400, -300, 300,
        400, -300, 300])
      (.leaf #[  -- Tall + heavy: moderate ROM (large adult)
        0, 0, 0,
        550, -500, 550,
        550, -500, 550,
        700, -50, 850,
        700, -50, 850,
        300, -200, 200,
        300, -200, 200,
        350, -350, 350,
        350, -350, 350,
        800, -800, 800,
        800, -800, 800,
        700, -50, 800,
        700, -50, 800,
        350, -250, 250,
        350, -250, 250]))

-- ── Convenience: predict ROM for a specific joint ───────────────────────────

structure JointROMPrediction where
  swingMaxDdeg : Int
  twistMinDdeg : Int
  twistMaxDdeg : Int
  deriving Repr, DecidableEq, Inhabited

def predictJoint (tree : TreeNode) (beta : Array Int) (jointIdx : Nat) : JointROMPrediction :=
  let rom := predict tree beta 20
  let base := jointIdx * 3
  if base + 2 < rom.size then
    { swingMaxDdeg := rom[base]!,
      twistMinDdeg := rom[base + 1]!,
      twistMaxDdeg := rom[base + 2]! }
  else
    { swingMaxDdeg := 0, twistMinDdeg := 0, twistMaxDdeg := 0 }

-- ── Verification ────────────────────────────────────────────────────────────

/-- Lean adult (β₀=500, β₁=-500) gets wide upper arm ROM (900 ddeg). -/
theorem lean_adult_wide_shoulder :
    let beta := #[500, -500, 0, 0, 0, 0, 0, 0, 0, 0]
    (predictJoint placeholderTree beta 9).swingMaxDdeg = 900 := by native_decide

/-- Stocky child (β₀=-500, β₁=500) gets tight upper arm ROM (700 ddeg). -/
theorem stocky_child_tight_shoulder :
    let beta := #[-500, 500, 0, 0, 0, 0, 0, 0, 0, 0]
    (predictJoint placeholderTree beta 9).swingMaxDdeg = 700 := by native_decide

/-- Large adult (β₀=500, β₁=500) gets moderate upper arm ROM (800 ddeg). -/
theorem large_adult_moderate_shoulder :
    let beta := #[500, 500, 0, 0, 0, 0, 0, 0, 0, 0]
    (predictJoint placeholderTree beta 9).swingMaxDdeg = 800 := by native_decide

/-- Hips are always unconstrained (0) regardless of body type. -/
theorem hips_always_zero :
    let rom1 := predictJoint placeholderTree #[-500, -500, 0, 0, 0, 0, 0, 0, 0, 0] 0
    let rom2 := predictJoint placeholderTree #[500, 500, 0, 0, 0, 0, 0, 0, 0, 0] 0
    rom1.swingMaxDdeg = 0 ∧ rom2.swingMaxDdeg = 0 := by native_decide

/-- Different body shapes give different ROM (the tree actually differentiates). -/
theorem body_shape_matters :
    let lean := predictJoint placeholderTree #[500, -500, 0, 0, 0, 0, 0, 0, 0, 0] 9
    let stocky := predictJoint placeholderTree #[-500, 500, 0, 0, 0, 0, 0, 0, 0, 0] 9
    lean.swingMaxDdeg ≠ stocky.swingMaxDdeg := by native_decide

end PredictiveBVH.ROMPredictor
