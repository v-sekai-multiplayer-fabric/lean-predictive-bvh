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

end PredictiveBVH.SphericalPolygon
