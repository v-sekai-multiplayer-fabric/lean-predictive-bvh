-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
-- Algorithm by Eron Gjoni
--
-- EWBIK skeleton decomposition into effector-groups.

import Shared.Types

namespace PredictiveBVH.EWBIKDecomposition

structure Bone where
  id     : Nat
  parent : Option Nat
  depth  : Nat
  deriving Repr, DecidableEq, Inhabited

structure Effector where
  id      : Nat
  boneId  : Nat
  opacity : Nat   -- 0..100
  deriving Repr, DecidableEq, Inhabited

structure WeightedBone where
  boneId : Nat
  weight : Nat
  deriving Repr, DecidableEq, Inhabited

-- ── Rootward traversal ──────────────────────────────────────────────────────

private def findBone (bones : Array Bone) (id : Nat) : Option Bone :=
  bones.find? (fun b => b.id == id)

private def findEffectorOpacity (effectors : Array Effector) (boneId : Nat)
    (selfBoneId : Nat) : Option Nat :=
  if boneId == selfBoneId then none
  else (effectors.find? (fun e => e.boneId == boneId)).map (·.opacity)

def collectBonesForEffector (eff : Effector) (bones : Array Bone)
    (effectors : Array Effector) : List WeightedBone :=
  let rec go (boneId : Nat) (weight : Nat) : (fuel : Nat) → List WeightedBone
    | 0 => []
    | fuel + 1 =>
      if weight == 0 then []
      else
        let decayed := match findEffectorOpacity effectors boneId eff.boneId with
          | some opacity => weight * (100 - opacity) / 100
          | none => weight
        let wb : WeightedBone := { boneId := boneId, weight := decayed }
        if decayed == 0 then [wb]
        else match findBone bones boneId with
          | some bone => match bone.parent with
            | some parentId => wb :: go parentId decayed fuel
            | none => [wb]
          | none => [wb]
  go eff.boneId 100 bones.size

-- ── Solve order ─────────────────────────────────────────────────────────────

def buildSolveOrder (perEffector : List (List Nat)) : List Nat :=
  let all := perEffector.flatten
  let rec dedup (xs : List Nat) (seen : List Nat) : List Nat :=
    match xs with
    | [] => []
    | x :: rest =>
      if seen.contains x then dedup rest seen
      else x :: dedup rest (x :: seen)
  termination_by xs.length
  dedup all []

-- ── Concrete verification ───────────────────────────────────────────────────

private def chain3 : Array Bone := #[
  { id := 0, parent := none,   depth := 0 },
  { id := 1, parent := some 0, depth := 1 },
  { id := 2, parent := some 1, depth := 2 }
]

private def eff1 : Array Effector := #[
  { id := 0, boneId := 2, opacity := 100 }
]

/-- Single effector at tip collects all 3 bones rootward. -/
theorem single_effector_3bones :
    (collectBonesForEffector eff1[0]! chain3 eff1).length = 3 := by native_decide

-- Two effectors: tip has 100% opacity, mid has 50% opacity.
private def eff2 : Array Effector := #[
  { id := 0, boneId := 2, opacity := 100 },
  { id := 1, boneId := 1, opacity := 50 }
]

/-- Tip effector still collects 3 bones (mid's opacity decays its weight but doesn't block). -/
theorem tip_with_mid_effector :
    (collectBonesForEffector eff2[0]! chain3 eff2).length = 3 := by native_decide

/-- Weight at root is decayed by mid's 50% opacity: 100 * 50/100 = 50. -/
theorem weight_decays_through_mid :
    let wbs := collectBonesForEffector eff2[0]! chain3 eff2
    (wbs.getLast!).weight = 50 := by native_decide

-- Mid effector with 100% opacity blocks the tip effector.
private def eff3 : Array Effector := #[
  { id := 0, boneId := 2, opacity := 100 },
  { id := 1, boneId := 1, opacity := 100 }
]

/-- 100% opacity mid effector blocks tip — tip only collects 2 bones (tip + mid). -/
theorem full_opacity_blocks :
    (collectBonesForEffector eff3[0]! chain3 eff3).length = 2 := by native_decide

/-- Mid effector itself collects 2 bones (mid + root). -/
theorem mid_effector_2bones :
    (collectBonesForEffector eff3[1]! chain3 eff3).length = 2 := by native_decide

/-- Solve order deduplicates shared bones. -/
theorem solve_order_dedup :
    buildSolveOrder [[2, 1], [1, 0]] = [2, 1, 0] := by native_decide

end PredictiveBVH.EWBIKDecomposition
