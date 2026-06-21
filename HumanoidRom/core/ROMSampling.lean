-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- ROM sampling: clinical bounds + ANNY self-intersection → joint limits.
-- Uses tapered capsules (frustums) for fast collision detection.

import Shared.Types

namespace PredictiveBVH.ROMSampling

-- ── Types ────────────────────────────────────────────────────────────────────

structure JointAxis where
  jointId     : Nat
  axisId      : Nat
  clinicalMin : Int   -- millidegrees
  clinicalMax : Int   -- millidegrees
  deriving Repr, DecidableEq, Inhabited

structure SampledLimit where
  jointId  : Nat
  axisId   : Nat
  validMin : Int
  validMax : Int
  deriving Repr, DecidableEq, Inhabited

-- ── Binary search ───────────────────────────────────────────────────────────

def binarySearchLimit (inside outside tolerance : Int)
    (collides : Int → Bool) : (fuel : Nat) → Int
  | 0 => inside
  | fuel + 1 =>
    if (outside - inside).natAbs < tolerance.natAbs then inside
    else
      let mid := (inside + outside) / 2
      if collides mid then
        binarySearchLimit inside mid tolerance collides fuel
      else
        binarySearchLimit mid outside tolerance collides fuel

def sampleAxis (axis : JointAxis) (collides : Int → Bool)
    (precision : Int) (maxIter : Nat) : SampledLimit :=
  let validMax :=
    if !collides axis.clinicalMax then axis.clinicalMax
    else binarySearchLimit 0 axis.clinicalMax precision collides maxIter
  let validMin :=
    if !collides axis.clinicalMin then axis.clinicalMin
    else binarySearchLimit 0 axis.clinicalMin precision collides maxIter
  { jointId := axis.jointId, axisId := axis.axisId,
    validMin := validMin, validMax := validMax }

-- ── Tapered capsule (frustum) collision ─────────────────────────────────────
-- A tapered capsule has different radii at each end: r0 at p0, r1 at p1.
-- This models limbs more accurately (thigh is wider at hip, narrower at knee).

structure TaperedCapsule where
  p0 : Vec3     -- axis start
  p1 : Vec3     -- axis end
  r0 : Int      -- radius at p0 (micrometres)
  r1 : Int      -- radius at p1 (micrometres)
  deriving Repr, DecidableEq, Inhabited

/-- Closest point parameter t ∈ [0,1] on segment (a0,a1) to point p.
    Returns t × 1000 (milliunits to stay integer). -/
private def closestParamOnSegment (a0 a1 p : Vec3) : Int :=
  let dx := a1.x - a0.x; let dy := a1.y - a0.y; let dz := a1.z - a0.z
  let lenSq := dx*dx + dy*dy + dz*dz
  if lenSq == 0 then 0
  else
    let px := p.x - a0.x; let py := p.y - a0.y; let pz := p.z - a0.z
    let dot := px*dx + py*dy + pz*dz
    let t1000 := dot * 1000 / lenSq
    max 0 (min 1000 t1000)

/-- Radius of tapered capsule at parameter t (0..1000 milliunits). -/
private def radiusAt (cap : TaperedCapsule) (t1000 : Int) : Int :=
  cap.r0 + (cap.r1 - cap.r0) * t1000 / 1000

/-- Point on segment at parameter t (0..1000). -/
private def pointAt (p0 p1 : Vec3) (t1000 : Int) : Vec3 :=
  { x := p0.x + (p1.x - p0.x) * t1000 / 1000
    y := p0.y + (p1.y - p0.y) * t1000 / 1000
    z := p0.z + (p1.z - p0.z) * t1000 / 1000 }

/-- Squared distance between two points. -/
private def distSq (a b : Vec3) : Int :=
  (a.x-b.x)*(a.x-b.x) + (a.y-b.y)*(a.y-b.y) + (a.z-b.z)*(a.z-b.z)

/-- Two tapered capsules collide iff at their closest approach, the
    distance between axes < sum of radii at those parameters.
    Approximate: sample 3 points per capsule (t=0, 0.5, 1). -/
def taperedCapsulesCollide (a b : TaperedCapsule) : Bool :=
  let aPts := #[a.p0, pointAt a.p0 a.p1 500, a.p1]
  let aRad := #[a.r0, radiusAt a 500, a.r1]
  let bPts := #[b.p0, pointAt b.p0 b.p1 500, b.p1]
  let bRad := #[b.r0, radiusAt b 500, b.r1]
  -- Check all 9 pairs — any collision means capsules intersect.
  (List.range 3).any fun i =>
    (List.range 3).any fun j =>
      let d := distSq aPts[i]! bPts[j]!
      let sumR := aRad[i]! + bRad[j]!
      d < sumR * sumR

-- ── Verification ────────────────────────────────────────────────────────────

private def collidesAbove45k (angle : Int) : Bool := decide (angle > 45000)

theorem no_collision_near_max :
    let r := binarySearchLimit 0 90000 100 (fun _ => false) 20
    r > 89000 := by native_decide

theorem always_collision_stays_zero :
    binarySearchLimit 0 90000 100 (fun _ => true) 20 = 0 := by native_decide

theorem binary_search_finds_45000 :
    binarySearchLimit 0 90000 100 collidesAbove45k 20 = 45000 := by native_decide

theorem distant_tapered_no_collision :
    let a : TaperedCapsule := { p0 := {x:=0,y:=0,z:=0}, p1 := {x:=100,y:=0,z:=0}, r0 := 15, r1 := 10 }
    let b : TaperedCapsule := { p0 := {x:=200,y:=0,z:=0}, p1 := {x:=300,y:=0,z:=0}, r0 := 15, r1 := 10 }
    taperedCapsulesCollide a b = false := by native_decide

theorem overlapping_tapered_collide :
    let a : TaperedCapsule := { p0 := {x:=0,y:=0,z:=0}, p1 := {x:=100,y:=0,z:=0}, r0 := 20, r1 := 15 }
    let b : TaperedCapsule := { p0 := {x:=110,y:=0,z:=0}, p1 := {x:=200,y:=0,z:=0}, r0 := 20, r1 := 10 }
    taperedCapsulesCollide a b = true := by native_decide

theorem taper_matters :
    let a : TaperedCapsule := { p0 := {x:=0,y:=0,z:=0}, p1 := {x:=100,y:=0,z:=0}, r0 := 30, r1 := 5 }
    let b : TaperedCapsule := { p0 := {x:=120,y:=0,z:=0}, p1 := {x:=200,y:=0,z:=0}, r0 := 5, r1 := 30 }
    -- Thin ends face each other: gap=20, sum of thin radii=10 → no collision
    taperedCapsulesCollide a b = false := by native_decide

end PredictiveBVH.ROMSampling
