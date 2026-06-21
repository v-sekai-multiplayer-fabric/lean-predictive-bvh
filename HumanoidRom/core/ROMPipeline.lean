-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- ROM Pipeline: directed task graph from mesh → joint limits.
-- Each node is a typed computation step. Edges are data dependencies.
--
-- Graph:
--
--   LoadMesh ──→ AssignBones ──→ BuildBVH ──→ SweepJoint ──→ CollectROM
--       │              │                           │
--       └── ExtractBoneLengths ──→ PredictROM ─────┘ (fast path)
--
-- Two paths:
--   ACCURATE: mesh → BVH → sweep all joints → exact ROM (slow, import-time)
--   FAST:     mesh → bone lengths → decision tree → predicted ROM (instant)

import HumanoidRom.core.MeshROM
import HumanoidRom.core.ROMSampling
import HumanoidRom.core.ROMPredictor

namespace PredictiveBVH.ROMPipeline

open MeshROM ROMSampling ROMPredictor

-- ── Task graph nodes ────────────────────────────────────────────────────────

/-- Each pipeline step has typed input and output. -/
inductive TaskId where
  | loadMesh            -- () → SkinnedMesh
  | assignBones         -- SkinnedMesh → SkinnedMesh (triangles get boneId)
  | extractBoneLengths  -- SkinnedMesh → Array Int (15 bone lengths)
  | buildBVH            -- SkinnedMesh → BVHTree (AABB hierarchy)
  | sweepJoint          -- (SkinnedMesh, BVH, jointIdx) → JointROMPrediction
  | collectROM          -- Array JointROMPrediction → ROMResult
  | predictROM          -- Array Int → ROMResult (fast path via decision tree)
  deriving Repr, DecidableEq, Inhabited

/-- A dependency edge: task B depends on task A. -/
structure Edge where
  src : TaskId
  dst : TaskId
  deriving Repr, DecidableEq

/-- The pipeline DAG. -/
def pipelineEdges : List Edge := [
  -- Accurate path
  { src :=.loadMesh,           dst :=.assignBones },
  { src :=.assignBones,        dst :=.buildBVH },
  { src :=.buildBVH,           dst :=.sweepJoint },
  { src :=.sweepJoint,         dst :=.collectROM },
  -- Fast path
  { src :=.loadMesh,           dst :=.extractBoneLengths },
  { src :=.extractBoneLengths, dst :=.predictROM }
]

-- ── Task implementations (specs) ────────────────────────────────────────────

/-- Assign each triangle to its dominant bone. -/
def assignBonesToTriangles (mesh : SkinnedMesh) : SkinnedMesh :=
  -- In practice: for each triangle, find the bone with highest
  -- average skin weight across its 3 vertices.
  -- Here: triangles already have boneId set (from NPZ import).
  mesh

/-- Extract bone lengths from joint positions. -/
def extractBoneLengths (mesh : SkinnedMesh) : Array Int :=
  mesh.bones.map fun bone =>
    match bone.parentId with
    | none => 0
    | some pid =>
      match mesh.bones.find? (fun b => b.id == pid) with
      | none => 0
      | some parent =>
        let dx := bone.headX - parent.headX
        let dy := bone.headY - parent.headY
        let dz := bone.headZ - parent.headZ
        -- Approximate length: max(|dx|,|dy|,|dz|) + min/2
        let ax := if dx ≥ 0 then dx else -dx
        let ay := if dy ≥ 0 then dy else -dy
        let az := if dz ≥ 0 then dz else -dz
        let mx := max ax (max ay az)
        let mn := min ax (min ay az)
        mx + mn / 2

/-- Sweep one joint to find its ROM via self-intersection. -/
def sweepJointROM (mesh : SkinnedMesh) (jointIdx : Nat)
    (collides : Int → Bool) : ROMSampling.SampledLimit :=
  ROMSampling.sampleAxis
    { jointId := jointIdx, axisId := 0,
      clinicalMin := -1800, clinicalMax := 1800 }  -- ±180° initial range
    collides 10 20  -- 10 mdeg precision, 20 binary search steps

/-- Fast path: predict ROM from bone lengths using the decision tree. -/
def predictFromBoneLengths (boneLengths : Array Int) : Array ROMPredictor.JointROMPrediction :=
  (List.range 15).toArray.map fun jointIdx =>
    ROMPredictor.predictJoint ROMPredictor.placeholderTree boneLengths jointIdx

-- ── Pipeline execution order ────────────────────────────────────────────────

/-- Topological sort of the task graph (the execution order). -/
def accuratePathOrder : List TaskId :=
  [.loadMesh, .assignBones, .buildBVH, .sweepJoint, .collectROM]

def fastPathOrder : List TaskId :=
  [.loadMesh, .extractBoneLengths, .predictROM]

-- ── Verification ────────────────────────────────────────────────────────────

/-- The pipeline has 6 edges. -/
theorem edge_count : pipelineEdges.length = 6 := by native_decide

/-- No self-loops in the pipeline. -/
theorem no_self_loops : pipelineEdges.all (fun e => e.src != e.dst) := by native_decide

/-- The accurate path has 5 steps. -/
theorem accurate_path_length : accuratePathOrder.length = 5 := by native_decide

/-- The fast path has 3 steps. -/
theorem fast_path_length : fastPathOrder.length = 3 := by native_decide

/-- Bone length extraction returns one length per bone. -/
theorem bone_lengths_count :
    let mesh : SkinnedMesh := {
      vertices := #[],
      triangles := #[],
      bones := #[
        { id := 0, parentId := none, headX := 0, headY := 0, headZ := 0 },
        { id := 1, parentId := some 0, headX := 0, headY := 100, headZ := 0 },
        { id := 2, parentId := some 1, headX := 0, headY := 200, headZ := 0 }
      ]
    }
    (extractBoneLengths mesh).size = 3 := by native_decide

end PredictiveBVH.ROMPipeline
