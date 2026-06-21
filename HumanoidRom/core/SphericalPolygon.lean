-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Spherical polygon constraint specification for kusudama joints.

import Shared.Types

namespace PredictiveBVH.SphericalPolygon

-- ── Primitives ───────────────────────────────────────────────────────────────

def dot (a b : Vec3) : Int :=
  a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : Vec3) : Vec3 :=
  { x := a.y * b.z - a.z * b.y
    y := a.z * b.x - a.x * b.z
    z := a.x * b.y - a.y * b.x }

def neg (v : Vec3) : Vec3 :=
  { x := -v.x, y := -v.y, z := -v.z }

-- ── Convex spherical polygon ─────────────────────────────────────────────────

structure ConvexPolygon where
  vertices : Array Vec3
  normals  : Array Vec3
  deriving Repr

def insidePoly (p : Vec3) (poly : ConvexPolygon) : Bool :=
  poly.normals.all fun n => dot p n ≥ 0

-- ── Projection ──────────────────────────────────────────────────────────────

def projectToGreatCircle (p v0 v1 : Vec3) : Vec3 :=
  let n := cross v0 v1
  let d := dot p n
  let nn := dot n n
  { x := p.x * nn - n.x * d
    y := p.y * nn - n.y * d
    z := p.z * nn - n.z * d }

def nearestOnArc (p v0 v1 : Vec3) : Vec3 × Int :=
  let proj := projectToGreatCircle p v0 v1
  let projLenSq := dot proj proj
  if projLenSq == 0 then
    let s0 := dot p v0
    let s1 := dot p v1
    if s0 ≥ s1 then (v0, s0) else (v1, s1)
  else
    let n := cross v0 v1
    let d0 := dot (cross v0 proj) n
    let d1 := dot (cross proj v1) n
    if d0 ≥ 0 && d1 ≥ 0 then
      (proj, dot p proj)
    else
      let s0 := dot p v0
      let s1 := dot p v1
      if s0 ≥ s1 then (v0, s0) else (v1, s1)

def projectToPoly (p : Vec3) (poly : ConvexPolygon) : Vec3 :=
  let n := poly.vertices.size
  if n == 0 then p
  else
    let init := nearestOnArc p poly.vertices[0]! poly.vertices[1 % n]!
    (List.range (n - 1)).foldl (fun (best : Vec3 × Int) idx =>
      let i := idx + 1
      let j := (i + 1) % n
      let cand := nearestOnArc p poly.vertices[i]! poly.vertices[j]!
      if cand.2 > best.2 then cand else best
    ) init |>.1

-- ── Order-independent polygon construction ──────────────────────────────────

private def atan2_approx (y x : Int) : Int :=
  if x > 0 then
    if y ≥ 0 then y * 1000 / (x + 1) else -((-y) * 1000 / (x + 1))
  else if x < 0 then
    if y ≥ 0 then 2000 - ((-y) * 1000 / ((-x) + 1))
    else -(2000 - (y * 1000 / ((-x) + 1)))
  else
    if y > 0 then 1000 else if y < 0 then -1000 else 0

def mkPolygon (vs : Array Vec3) (centroid : Vec3) : ConvexPolygon :=
  let n := vs.size
  if n < 2 then { vertices := vs, normals := #[] }
  else
    let u : Vec3 :=
      if centroid.x != 0 || centroid.y != 0 then { x := -centroid.y, y := centroid.x, z := 0 }
      else { x := centroid.z, y := 0, z := -centroid.x }
    let v := cross centroid u
    let withAngles := vs.map fun p => (atan2_approx (dot p v) (dot p u), p)
    let sorted := withAngles.insertionSort (fun a b => a.1 < b.1)
    let verts := sorted.map (·.2)
    let normals := (Array.range n).map fun i =>
      cross verts[i]! verts[(i + 1) % n]!
    let windingSum := normals.foldl (fun acc nm =>
      { x := acc.x + nm.x, y := acc.y + nm.y, z := acc.z + nm.z : Vec3 })
      { x := 0, y := 0, z := 0 }
    let vertSum := verts.foldl (fun acc v =>
      { x := acc.x + v.x, y := acc.y + v.y, z := acc.z + v.z : Vec3 })
      { x := 0, y := 0, z := 0 }
    let needsFlip := dot windingSum vertSum < 0
    let fixedNormals := if needsFlip then normals.map neg else normals
    { vertices := verts, normals := fixedNormals }

-- ── Test data ───────────────────────────────────────────────────────────────

private def scale := 1000
private def coneX  : Vec3 := { x :=  scale, y :=  0,     z := 0 }
private def coneY  : Vec3 := { x :=  0,     y :=  scale, z := 0 }
private def coneMX : Vec3 := { x := -scale, y :=  0,     z := 0 }
private def coneMY : Vec3 := { x :=  0,     y := -scale, z := 0 }
private def centroidZ : Vec3 := { x := 0, y := 0, z := scale }

def hullPoly : ConvexPolygon := mkPolygon #[coneX, coneY, coneMX, coneMY] centroidZ
def scrambledPoly : ConvexPolygon := mkPolygon #[coneX, coneMX, coneY, coneMY] centroidZ

/-- Per-cone dot products are equidistant at the south pole = teleport point. -/
theorem teleport_point_equidistant :
    (dot { x := 0, y := 0, z := -scale } coneX,
     dot { x := 0, y := 0, z := -scale } coneMX) = (0, 0) := by native_decide

end PredictiveBVH.SphericalPolygon
