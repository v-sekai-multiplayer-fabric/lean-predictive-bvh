-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- 6-star heading construction for QCP-based IK.
--
-- A transform (origin + 3 orthonormal axes) is encoded as 7 points.
-- QCP aligns tip headings to target headings, recovering both position
-- and rotation from the same algorithm.

import PredictiveBVH.Primitives.Types

namespace PredictiveBVH.StarHeadings

/-- A rigid transform: origin + 3 axis columns. -/
structure RigidTransform where
  origin : Vec3
  axisX  : Vec3
  axisY  : Vec3
  axisZ  : Vec3
  deriving Repr, DecidableEq

/-- Build 7 star headings from a transform, relative to a reference point. -/
def starHeadings (t : RigidTransform) (ref : Vec3) : Array Vec3 :=
  #[ { x := t.origin.x - ref.x, y := t.origin.y - ref.y, z := t.origin.z - ref.z }
   , { x := t.origin.x + t.axisX.x - ref.x, y := t.origin.y + t.axisX.y - ref.y, z := t.origin.z + t.axisX.z - ref.z }
   , { x := t.origin.x - t.axisX.x - ref.x, y := t.origin.y - t.axisX.y - ref.y, z := t.origin.z - t.axisX.z - ref.z }
   , { x := t.origin.x + t.axisY.x - ref.x, y := t.origin.y + t.axisY.y - ref.y, z := t.origin.z + t.axisY.z - ref.z }
   , { x := t.origin.x - t.axisY.x - ref.x, y := t.origin.y - t.axisY.y - ref.y, z := t.origin.z - t.axisY.z - ref.z }
   , { x := t.origin.x + t.axisZ.x - ref.x, y := t.origin.y + t.axisZ.y - ref.y, z := t.origin.z + t.axisZ.z - ref.z }
   , { x := t.origin.x - t.axisZ.x - ref.x, y := t.origin.y - t.axisZ.y - ref.y, z := t.origin.z - t.axisZ.z - ref.z }
   ]

-- ── Concrete verification ───────────────────────────────────────────────────

private def sc := 100

private def testTransform : RigidTransform :=
  { origin := { x := 50, y := 60, z := 70 }
    axisX  := { x := sc, y := 0,  z := 0 }
    axisY  := { x := 0,  y := sc, z := 0 }
    axisZ  := { x := 0,  y := 0,  z := sc } }

private def testRef : Vec3 := { x := 10, y := 20, z := 30 }

/-- Star headings produce exactly 7 points. -/
theorem heading_count :
    (starHeadings testTransform testRef).size = 7 := by native_decide

/-- The origin is recoverable: heading[0] + ref = transform.origin. -/
theorem origin_recoverable :
    let h := starHeadings testTransform testRef
    (h[0]!.x + testRef.x, h[0]!.y + testRef.y, h[0]!.z + testRef.z) =
    (testTransform.origin.x, testTransform.origin.y, testTransform.origin.z) := by native_decide

/-- X axis recoverable: (heading[1] - heading[2]) / 2 = axisX. -/
theorem axisX_recoverable :
    let h := starHeadings testTransform testRef
    ((h[1]!.x - h[2]!.x) / 2, (h[1]!.y - h[2]!.y) / 2, (h[1]!.z - h[2]!.z) / 2) =
    (testTransform.axisX.x, testTransform.axisX.y, testTransform.axisX.z) := by native_decide

/-- Y axis recoverable. -/
theorem axisY_recoverable :
    let h := starHeadings testTransform testRef
    ((h[3]!.x - h[4]!.x) / 2, (h[3]!.y - h[4]!.y) / 2, (h[3]!.z - h[4]!.z) / 2) =
    (testTransform.axisY.x, testTransform.axisY.y, testTransform.axisY.z) := by native_decide

/-- Z axis recoverable. -/
theorem axisZ_recoverable :
    let h := starHeadings testTransform testRef
    ((h[5]!.x - h[6]!.x) / 2, (h[5]!.y - h[6]!.y) / 2, (h[5]!.z - h[6]!.z) / 2) =
    (testTransform.axisZ.x, testTransform.axisZ.y, testTransform.axisZ.z) := by native_decide

/-- Completeness: two different transforms produce different star headings. -/
private def testTransform2 : RigidTransform :=
  { origin := { x := 50, y := 60, z := 70 }
    axisX  := { x := 0,  y := sc, z := 0 }   -- rotated 90° around Z
    axisY  := { x := -sc, y := 0, z := 0 }
    axisZ  := { x := 0,  y := 0,  z := sc } }

theorem different_rotation_different_headings :
    starHeadings testTransform testRef ≠ starHeadings testTransform2 testRef := by native_decide

/-- Same transform, different ref → different headings (ref is subtracted). -/
private def testRef2 : Vec3 := { x := 0, y := 0, z := 0 }

theorem different_ref_different_headings :
    starHeadings testTransform testRef ≠ starHeadings testTransform testRef2 := by native_decide

end PredictiveBVH.StarHeadings
