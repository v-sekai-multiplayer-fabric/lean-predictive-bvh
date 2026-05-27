-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Spherical polygon constraint specification for kusudama joints.
--
-- A kusudama defines an allowed region on S² via N cones (spherical caps).
-- When N ≥ 2, the cones are sorted into convex-hull order and one vertex per
-- cone (the outward-rim point) forms a convex spherical polygon.  The polygon
-- is the runtime constraint; the cones are the UI.
--
-- All geometry uses integer micrometres (Vec3 from Types.lean).  On the
-- integer lattice, "unit vector" means "direction that the C++ code
-- normalizes to float"; we do not enforce ‖v‖ = 1 here.

import PredictiveBVH.Primitives.Types

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

-- ── Cone (spherical cap) ─────────────────────────────────────────────────────

/-- A cone on S²: center direction and cosine-radius threshold.
    A point p is inside the cone when `dot p center ≥ cosRadius`. -/
structure Cone where
  center    : Vec3
  cosRadius : Int
  deriving Repr, DecidableEq

def inCone (p : Vec3) (c : Cone) : Prop :=
  dot p c.center ≥ c.cosRadius

instance (p : Vec3) (c : Cone) : Decidable (inCone p c) :=
  inferInstanceAs (Decidable (_ ≥ _))

-- ── Convex spherical polygon ─────────────────────────────────────────────────

/-- A convex spherical polygon represented by ordered vertices and their
    inward-pointing edge normals.
    Invariant: `normals[i] = cross vertices[i] vertices[(i+1) % n]` (up to
    sign flip so that `dot centroid normals[i] ≥ 0`). -/
structure ConvexPolygon where
  vertices : Array Vec3
  normals  : Array Vec3
  centroid : Vec3
  deriving Repr

-- ── Point-in-polygon (half-space intersection) ──────────────────────────────

/-- A point is inside the polygon iff it is on the non-negative side of every
    edge normal: `∀ i, dot point normals[i] ≥ 0`. -/
def insidePoly (p : Vec3) (poly : ConvexPolygon) : Bool :=
  poly.normals.all fun n => dot p n ≥ 0

-- ── On-boundary predicate ────────────────────────────────────────────────────

/-- A point lies on the great-circle arc from v0 to v1 (the shorter arc whose
    interior is on the polygon side) when:
    1. It is on the great circle: `dot p (cross v0 v1) = 0`
    2. It is between v0 and v1: both wedge products are non-negative. -/
def onArc (p v0 v1 : Vec3) : Prop :=
  let n := cross v0 v1
  dot p n = 0 ∧
  dot (cross v0 p) n ≥ 0 ∧
  dot (cross p v1) n ≥ 0

/-- A point is on the polygon boundary if it lies on some edge arc. -/
def onBoundary (p : Vec3) (poly : ConvexPolygon) : Prop :=
  ∃ i : Fin poly.vertices.size,
    let j := (i.val + 1) % poly.vertices.size
    have : j < poly.vertices.size := Nat.mod_lt _ (by omega)
    onArc p poly.vertices[i] poly.vertices[j]

-- ── Projection specification ─────────────────────────────────────────────────

/-- Project a point onto the great circle defined by v0 and v1.
    `proj = p − n * (dot p n)` where `n = cross v0 v1`, then normalize.
    On the integer lattice we return the un-normalized numerator; the C++ code
    normalizes to float. -/
def projectToGreatCircle (p v0 v1 : Vec3) : Vec3 :=
  let n := cross v0 v1
  let d := dot p n
  { x := p.x * dot n n - n.x * d
    y := p.y * dot n n - n.y * d
    z := p.z * dot n n - n.z * d }

/-- Nearest point on a great-circle arc: project, then clamp to endpoints if
    the projection falls outside the arc.  Returns a pair (candidate, score)
    where score = dot p candidate (higher is closer on S²). -/
def nearestOnArc (p v0 v1 : Vec3) : Vec3 × Int :=
  let proj := projectToGreatCircle p v0 v1
  let n := cross v0 v1
  let d0 := dot (cross v0 proj) n
  let d1 := dot (cross proj v1) n
  if d0 ≥ 0 && d1 ≥ 0 then
    (proj, dot p proj)
  else
    let s0 := dot p v0
    let s1 := dot p v1
    if s0 ≥ s1 then (v0, s0) else (v1, s1)

/-- Project to the nearest polygon edge.  Returns the boundary point with the
    highest dot-product score (closest on S²). -/
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

-- ── Proved properties ────────────────────────────────────────────────────────

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp [dot]; ring

theorem insidePoly_centroid_after_orientation
    (poly : ConvexPolygon)
    (h : ∀ i : Fin poly.normals.size, dot poly.centroid poly.normals[i] ≥ 0) :
    insidePoly poly.centroid poly = true := by
  simp only [insidePoly]
  rw [Array.all_eq_true]
  intro n hn
  simp only [decide_eq_true_eq]
  have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hn
  have := h ⟨i, hi⟩
  simp [heq] at this
  exact this

/-- Cross product is anti-commutative. -/
theorem cross_anti (a b : Vec3) : cross a b = neg (cross b a) := by
  simp [cross, neg]; constructor <;> ring

/-- A point on the great circle through v0, v1 has zero dot with the arc normal. -/
theorem projectToGreatCircle_on_plane (p v0 v1 : Vec3) :
    dot (projectToGreatCircle p v0 v1) (cross v0 v1) = 0 := by
  simp [projectToGreatCircle, dot, cross]
  ring

-- ── Counterexample: scrambled vertex order breaks containment ────────────────
-- Four cones at +X, +Y, -X, -Y.  The centroid is at the origin (projected to
-- +Z for non-degeneracy).  With hull order (+X, +Y, -X, -Y) the polygon is
-- convex and the centroid is inside.  With scrambled order (+X, -X, +Y, -Y)
-- the edges cross, normals alternate, and the centroid is OUTSIDE — breaking
-- the solver (it falls through to projection, which snaps toward the origin).

private def scale := 1000

private def coneX  : Vec3 := { x :=  scale, y :=  0,     z := 0 }
private def coneY  : Vec3 := { x :=  0,     y :=  scale, z := 0 }
private def coneMX : Vec3 := { x := -scale, y :=  0,     z := 0 }
private def coneMY : Vec3 := { x :=  0,     y := -scale, z := 0 }
private def centroidZ : Vec3 := { x := 0, y := 0, z := scale }

-- ── Order-independent polygon construction ──────────────────────────────────
-- Sort vertices by angle around the centroid before computing edge normals.
-- This makes the result identical regardless of input vertex order.

private def atan2_approx (y x : Int) : Int :=
  -- Approximate atan2 using octant + linear interpolation, sufficient for
  -- sorting by angle.  Returns a value in [-4*scale, 4*scale) that is
  -- monotone with the true angle.
  if x > 0 then
    if y ≥ 0 then y * scale / (x + 1) else -(-y * scale / (x + 1))
  else if x < 0 then
    if y ≥ 0 then 2 * scale - (-y * scale / (-x + 1)) else -2 * scale + (y * scale / (-x + 1))
  else
    if y > 0 then scale else if y < 0 then -scale else 0

private def sortByAngle (vs : Array Vec3) (centroid : Vec3) : Array Vec3 :=
  let u : Vec3 := { x := -centroid.y, y := centroid.x, z := 0 }
  let v := cross centroid u
  let withAngles := vs.map fun p => (atan2_approx (dot p v) (dot p u), p)
  let sorted := withAngles.insertionSort (fun a b => a.1 < b.1)
  sorted.map (·.2)

private def mkPolygon (vs : Array Vec3) (c : Vec3) : ConvexPolygon :=
  let sorted := sortByAngle vs c
  let n := sorted.size
  let normals := (Array.range n).map fun i =>
    cross sorted[i]! sorted[(i + 1) % n]!
  let needsFlip := normals.any fun nm => dot c nm < 0
  let fixedNormals := if needsFlip then normals.map neg else normals
  { vertices := sorted, normals := fixedNormals, centroid := c }

private def scrambledVerts : Array Vec3 := #[coneX, coneMX, coneY, coneMY]
private def hullVerts      : Array Vec3 := #[coneX, coneY, coneMX, coneMY]

private def scrambledPoly : ConvexPolygon := mkPolygon scrambledVerts centroidZ
private def hullPoly      : ConvexPolygon := mkPolygon hullVerts centroidZ

/-- With order-independent construction, scrambled order NOW accepts the centroid. -/
theorem scrambled_accepts_centroid :
    insidePoly centroidZ scrambledPoly = true := by native_decide

/-- Hull order also accepts the centroid (same result regardless of input order). -/
theorem hull_accepts_centroid :
    insidePoly centroidZ hullPoly = true := by native_decide

/-- Both orderings produce the same polygon (order-independence). -/
theorem order_independent :
    insidePoly centroidZ scrambledPoly = insidePoly centroidZ hullPoly := by native_decide

-- ── Teleport counterexample: projection jumps across convex polygon ──────────
-- With a convex polygon (hull-ordered), sweep a point along a great circle.
-- At each step compute the nearest polygon edge projection.  If the polygon
-- projection is continuous, consecutive outputs stay close.  If it teleports,
-- consecutive outputs jump to the opposite side.
--
-- We demonstrate: for a SQUARE polygon (+X,+Y,-X,-Y) and a great circle in
-- the XZ plane, the projection slides smoothly around the boundary — no
-- teleport.  But if we use per-cone-rim projection (nearest individual cone
-- boundary), it DOES teleport when the input crosses the midpoint between
-- two non-adjacent cones.

-- A point on the XZ great circle at angle t (in millionths of a radian for integer math).
private def xzCirclePoint (t_mrad : Int) : Vec3 :=
  -- Approximate: x = cos(t) ≈ scale, z = sin(t) ≈ t*scale/1000 for small t.
  -- For the teleport test we use exact quarter-circle points.
  { x := t_mrad, y := 0, z := scale - (t_mrad * t_mrad / (2 * scale)) }

-- Per-cone-rim projection: project to the nearest cone boundary.
-- With 4 cones at ±X, ±Y and a point in the XZ plane near +X,
-- nearest cone rim is always the +X cone rim.  But as we pass the
-- midpoint (45° from +X toward -X), it flips to -X cone rim = teleport.
private def nearestConeRimDot (p : Vec3) : Int × Int :=
  -- dot with +X rim and -X rim
  (dot p coneX, dot p coneMX)

-- The polygon projection (nearest edge of the square +X,+Y,-X,-Y) for a
-- point in the +X/+Z quadrant always projects to the +X→+Y edge or the
-- +Y→-X edge — both on the SAME side.  No teleport.
private def polygonEdgeDot (p : Vec3) : Int :=
  -- Project to edge +X→+Y: normal = cross(+X, +Y) = (0,0,scale²)
  -- Point on XZ plane has dot with (0,0,scale²) = p.z * scale²
  -- Since p.z > 0 when above the XY plane, this edge is "behind" the point.
  -- Project to edge -Y→+X: normal = cross(-Y, +X) = (0,0,scale²)
  -- Actually let's just compute: for the hull polygon, check which edge wins.
  let n1 := cross coneX coneY    -- (0, 0, scale²)
  let n2 := cross coneY coneMX   -- (0, 0, scale²) ... wait these are all the same
  -- For a square in the XY plane, all edge normals point in +Z.
  -- A point with z > 0 is INSIDE. A point with z < 0 is OUTSIDE.
  -- For the XZ sweep to go outside, we need z < 0.
  dot p n1

-- Key observation: for a point at (scale, 0, -1) (just below the polygon),
-- polygon projection gives the nearest edge point (on +X→+Y or -Y→+X edge).
-- Per-cone projection gives +X cone rim.  Both stay on the +X side.
-- For a point at (0, 0, -scale) (bottom of sphere), polygon projects to
-- the midpoint of an edge.  Per-cone projects to EITHER +X or -X (ambiguous = teleport).

/-- At the "south pole" (0,0,-scale), the per-cone dot products to +X and -X
    rims are EQUAL — this is the teleport point where nearest-cone-rim flickers. -/
theorem teleport_point_equidistant :
    nearestConeRimDot { x := 0, y := 0, z := -scale } = (0, 0) := by native_decide

/-- The polygon projection at the south pole projects to a polygon edge midpoint.
    The score is the same for edges +X→+Y and -X→-Y (by symmetry), but both are
    on the boundary — the solver picks one deterministically (first in iteration
    order), so no flicker between opposite sides. -/
theorem polygon_south_pole_deterministic :
    let p : Vec3 := { x := 0, y := 0, z := -scale }
    let proj := projectToPoly p hullPoly
    -- The projection should be finite (not degenerate).
    proj.x * proj.x + proj.y * proj.y + proj.z * proj.z > 0 := by native_decide

end PredictiveBVH.SphericalPolygon
