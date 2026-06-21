-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Model the C++ kusudama solver in Lean and find teleportation failures.
-- The solver: cone check → polygon contains → gnomonic 2D project.
-- Open chain: no last-to-first edge.

import HumanoidRom.core.SphericalPolygon

namespace PredictiveBVH.KusudamaShader

open PredictiveBVH.SphericalPolygon

private def sc : Int := 100

-- ── Octahedral grid ─────────────────────────────────────────────────────────

private def octaPoints : Array Vec3 := #[
  { x :=  sc, y :=  0,  z :=  0 },
  { x := -sc, y :=  0,  z :=  0 },
  { x :=  0,  y :=  sc, z :=  0 },
  { x :=  0,  y := -sc, z :=  0 },
  { x :=  0,  y :=  0,  z :=  sc },
  { x :=  0,  y :=  0,  z := -sc },
  { x :=  70, y :=  70, z :=  0 },
  { x :=  70, y := -70, z :=  0 },
  { x := -70, y :=  70, z :=  0 },
  { x := -70, y := -70, z :=  0 },
  { x :=  70, y :=  0,  z :=  70 },
  { x :=  70, y :=  0,  z := -70 },
  { x := -70, y :=  0,  z :=  70 },
  { x := -70, y :=  0,  z := -70 },
  { x :=  0,  y :=  70, z :=  70 },
  { x :=  0,  y :=  70, z := -70 },
  { x :=  0,  y := -70, z :=  70 },
  { x :=  0,  y := -70, z := -70 }
]

private def octaEdges : Array (Nat × Nat) := #[
  (0, 6), (0, 7), (0, 10), (0, 11),
  (1, 8), (1, 9), (1, 12), (1, 13),
  (2, 6), (2, 8), (2, 14), (2, 15),
  (3, 7), (3, 9), (3, 16), (3, 17),
  (4, 10), (4, 12), (4, 14), (4, 16),
  (5, 11), (5, 13), (5, 15), (5, 17),
  (6, 10), (6, 14), (7, 10), (7, 16),
  (8, 12), (8, 14), (9, 12), (9, 16),
  (6, 11), (6, 15), (7, 11), (7, 17),
  (8, 13), (8, 15), (9, 13), (9, 17),
  (10, 14), (10, 16), (12, 14), (12, 16),
  (11, 15), (11, 17), (13, 15), (13, 17)
]

-- ── Cone containment (matches C++ is_point_in_cone) ────────────────────────

structure ConeData where
  center : Vec3
  cosRadius : Int   -- cos(radius) * sc²  (avoid floating point)
  deriving Repr

private def inCone (p : Vec3) (c : ConeData) : Bool :=
  dot p c.center ≥ c.cosRadius

-- ── Open-chain polygon (no last-to-first edge) ─────────────────────────────

structure OpenPolygon where
  vertices : Array Vec3
  normals  : Array Vec3   -- n-1 normals for n vertices
  deriving Repr

private def mkOpenPoly (vs : Array Vec3) : OpenPolygon :=
  let sorted := vs  -- assume already in hull order for simplicity
  let n := sorted.size
  let normals := if n < 2 then #[] else
    (Array.range (n - 1)).map fun i =>
      cross sorted[i]! sorted[i + 1]!
  -- Orientation: check winding sum vs vertex sum
  let windingSum := normals.foldl (fun acc nm =>
    { x := acc.x + nm.x, y := acc.y + nm.y, z := acc.z + nm.z : Vec3 })
    { x := 0, y := 0, z := 0 }
  let vertSum := sorted.foldl (fun acc v =>
    { x := acc.x + v.x, y := acc.y + v.y, z := acc.z + v.z : Vec3 })
    { x := 0, y := 0, z := 0 }
  let fixedNormals := if dot windingSum vertSum < 0
    then normals.map neg else normals
  { vertices := sorted, normals := fixedNormals }

private def polyContains (p : Vec3) (poly : OpenPolygon) : Bool :=
  poly.normals.all fun n => dot p n ≥ 0

-- ── Gnomonic 2D projection (matches C++) ────────────────────────────────────
-- All in integer arithmetic scaled by sc.

private def gnomonicProject2D (p center u v : Vec3) : Int × Int :=
  let pdc := dot p center
  let d := if pdc == 0 then 1 else pdc
  -- Return (x * d_scale, y * d_scale) to avoid division.
  -- We compare distances, so uniform scaling is fine.
  (dot p u * sc / d, dot p v * sc / d)

private def segmentNearest2D (px py ax ay bx by_ : Int) : Int × Int :=
  let ex := bx - ax
  let ey := by_ - ay
  let elenSq := ex * ex + ey * ey
  if elenSq == 0 then (ax, ay)
  else
    let tpx := px - ax
    let tpy := py - ay
    let tNum := tpx * ex + tpy * ey
    if tNum ≤ 0 then (ax, ay)
    else if tNum ≥ elenSq then (bx, by_)
    else (ax + ex * tNum / elenSq, ay + ey * tNum / elenSq)

private def dist2DSq (x1 y1 x2 y2 : Int) : Int :=
  let dx := x1 - x2; let dy := y1 - y2
  dx * dx + dy * dy

private def polyProject (p : Vec3) (poly : OpenPolygon) : Vec3 :=
  let n := poly.vertices.size
  if n == 0 then p
  else
    -- Compute center
    let center := poly.vertices.foldl (fun acc v =>
      { x := acc.x + v.x, y := acc.y + v.y, z := acc.z + v.z : Vec3 })
      { x := 0, y := 0, z := 0 }
    let cLen := dot center center
    if cLen == 0 then p  -- degenerate
    else
      -- Basis (same as C++ get_any_perpendicular logic)
      let u : Vec3 := if center.x != 0 || center.y != 0
        then { x := -center.y, y := center.x, z := 0 }
        else { x := center.z, y := 0, z := -center.x }
      let v := cross center u
      -- Project input
      let (px, py) := gnomonicProject2D p center u v
      -- Project vertices
      let verts2d := poly.vertices.map fun vt => gnomonicProject2D vt center u v
      -- Find nearest edge (open chain)
      let init := (verts2d[0]!.1, verts2d[0]!.2, dist2DSq px py verts2d[0]!.1 verts2d[0]!.2)
      let best := (List.range (n - 1)).foldl (fun (bestX, bestY, bestD) i =>
        let (ax, ay) := verts2d[i]!
        let (bx, by_) := verts2d[i + 1]!
        let (cx, cy) := segmentNearest2D px py ax ay bx by_
        let d := dist2DSq px py cx cy
        if d < bestD then (cx, cy, d) else (bestX, bestY, bestD)
      ) init
      -- Inverse gnomonic: center * scale + u * x + v * y
      { x := center.x * sc + u.x * best.1 + v.x * best.2.1
        y := center.y * sc + u.y * best.1 + v.y * best.2.1
        z := center.z * sc + u.z * best.1 + v.z * best.2.1 }

-- ── Full solver (matches C++ _solve) ────────────────────────────────────────

private def solve (p : Vec3) (cones : Array ConeData) (poly : OpenPolygon) : Vec3 :=
  -- Step 1: inside any cone → accept
  if cones.any (inCone p) then p
  -- Step 2: inside polygon → accept
  else if polyContains p poly then p
  -- Step 3: gnomonic project
  else polyProject p poly

-- ── Scale-invariant non-expansive check ─────────────────────────────────────

private def angDistSq (a b : Vec3) : Int :=
  let ab := dot a b
  let aa := dot a a
  let bb := dot b b
  aa * bb - ab * ab

private def isExpansive (pi pj oi oj : Vec3) : Bool :=
  let inAng  := angDistSq pi pj
  let outAng := angDistSq oi oj
  let inNormSq  := dot pi pi * dot pj pj
  let outNormSq := dot oi oi * dot oj oj
  if outNormSq == 0 || inNormSq == 0 then false
  else outAng * inNormSq > inAng * outNormSq

-- ── Test: 4-cone square in +Z hemisphere ────────────────────────────────────

private def testCones : Array ConeData := #[
  { center := { x :=  71, y :=   0, z :=  71 }, cosRadius := 4500 },
  { center := { x :=   0, y :=  71, z :=  71 }, cosRadius := 4500 },
  { center := { x := -71, y :=   0, z :=  71 }, cosRadius := 4500 },
  { center := { x :=   0, y := -71, z :=  71 }, cosRadius := 4500 }
]

private def testPoly : OpenPolygon :=
  mkOpenPoly #[
    { x :=  71, y :=   0, z :=  71 },
    { x :=   0, y :=  71, z :=  71 },
    { x := -71, y :=   0, z :=  71 },
    { x :=   0, y := -71, z :=  71 }
  ]

private def countViolations (cones : Array ConeData) (poly : OpenPolygon) : Nat :=
  let center := poly.vertices.foldl (fun acc v =>
    { x := acc.x + v.x, y := acc.y + v.y, z := acc.z + v.z : Vec3 })
    { x := 0, y := 0, z := 0 }
  let outs := octaPoints.map fun p => solve p cones poly
  octaEdges.foldl (fun acc (i, j) =>
    let pi := octaPoints[i]!
    let pj := octaPoints[j]!
    if dot pi center ≤ 0 || dot pj center ≤ 0 then acc
    else if isExpansive pi pj outs[i]! outs[j]! then acc + 1 else acc
  ) 0

-- ── Diagnostic: find failures ───────────────────────────────────────────────

private def reportViolations (name : String) (cones : Array ConeData)
    (poly : OpenPolygon) : IO Unit := do
  let center := poly.vertices.foldl (fun acc v =>
    { x := acc.x + v.x, y := acc.y + v.y, z := acc.z + v.z : Vec3 })
    { x := 0, y := 0, z := 0 }
  let outs := octaPoints.map fun p => solve p cones poly
  let mut violations := 0
  for h : idx in [:octaEdges.size] do
    let (i, j) := octaEdges[idx]
    let pi := octaPoints[i]!
    let pj := octaPoints[j]!
    if dot pi center > 0 && dot pj center > 0 then
      if isExpansive pi pj outs[i]! outs[j]! then
        violations := violations + 1
        IO.println s!"{name} TELEPORT edge({i},{j})"
        IO.println s!"  in:  ({pi.x},{pi.y},{pi.z}) -> ({pj.x},{pj.y},{pj.z})"
        IO.println s!"  out: ({outs[i]!.x},{outs[i]!.y},{outs[i]!.z}) -> ({outs[j]!.x},{outs[j]!.y},{outs[j]!.z})"
        let inC := if cones.any (inCone pi) then "cone" else if polyContains pi poly then "poly" else "proj"
        let outC := if cones.any (inCone pj) then "cone" else if polyContains pj poly then "poly" else "proj"
        IO.println s!"  path: {inC} -> {outC}"
  IO.println s!"{name}: {violations} violations"

-- 6 cones: octahedron vertices
private def testCones6 : Array ConeData := #[
  { center := { x :=  sc, y :=  0, z :=  0 }, cosRadius := 4500 },
  { center := { x := -sc, y :=  0, z :=  0 }, cosRadius := 4500 },
  { center := { x :=  0, y :=  sc, z :=  0 }, cosRadius := 4500 },
  { center := { x :=  0, y := -sc, z :=  0 }, cosRadius := 4500 },
  { center := { x :=  0, y :=  0, z :=  sc }, cosRadius := 4500 },
  { center := { x :=  0, y :=  0, z := -sc }, cosRadius := 4500 }
]
private def testPoly6 : OpenPolygon :=
  mkOpenPoly #[
    { x :=  sc, y :=  0, z :=  0 },
    { x := -sc, y :=  0, z :=  0 },
    { x :=  0, y :=  sc, z :=  0 },
    { x :=  0, y := -sc, z :=  0 },
    { x :=  0, y :=  0, z :=  sc },
    { x :=  0, y :=  0, z := -sc }
  ]

-- 8 cones: cube vertices
private def testCones8 : Array ConeData := #[
  { center := { x :=  58, y :=  58, z :=  58 }, cosRadius := 2800 },
  { center := { x := -58, y :=  58, z :=  58 }, cosRadius := 2800 },
  { center := { x :=  58, y := -58, z :=  58 }, cosRadius := 2800 },
  { center := { x := -58, y := -58, z :=  58 }, cosRadius := 2800 },
  { center := { x :=  58, y :=  58, z := -58 }, cosRadius := 2800 },
  { center := { x := -58, y :=  58, z := -58 }, cosRadius := 2800 },
  { center := { x :=  58, y := -58, z := -58 }, cosRadius := 2800 },
  { center := { x := -58, y := -58, z := -58 }, cosRadius := 2800 }
]
private def testPoly8 : OpenPolygon :=
  mkOpenPoly #[
    { x :=  58, y :=  58, z :=  58 },
    { x := -58, y :=  58, z :=  58 },
    { x :=  58, y := -58, z :=  58 },
    { x := -58, y := -58, z :=  58 },
    { x :=  58, y :=  58, z := -58 },
    { x := -58, y :=  58, z := -58 },
    { x :=  58, y := -58, z := -58 },
    { x := -58, y := -58, z := -58 }
  ]

#eval! do
  reportViolations "square-4" testCones testPoly
  reportViolations "octa-6" testCones6 testPoly6
  reportViolations "cube-8" testCones8 testPoly8

end PredictiveBVH.KusudamaShader
