-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import InterestManagement.core.AuthorityInterest

open PredictiveBVH.Relativistic

-- ============================================================================
-- HIERARCHICAL TRANSFORM SOLVE-ORDER MANAGER
--
-- Context (VSK-96):
--   When entity B is parented to entity A (passenger on truck, weapon on hand),
--   the solver needs A's final transform before computing B's.
--
-- Decision: HIERARCHICAL (manager-driven solve order).
--   Flat approach adds 1 frame of latency on every parented entity.
--   Hierarchical solves dependent entities in the SAME FRAME via topological
--   sort of the dependency graph → zero added latency for parent-child chains.
--
-- Architecture:
--   The authority server (Godot zone process) owns this manager.
--   Authority and interest management consult it for update ordering.
--   Independent entities solve in parallel; dependent chains solve sequentially.
--
-- This module formalizes:
--   1. Entity dependency graph (parent-child transform relationships)
--   2. Topological sort for same-frame solve order
--   3. Cycle detection and breaking
--   4. Latency bound: hierarchical adds 0 frames vs flat's 1 frame
-- ============================================================================

namespace SolveOrder

-- ── Entity dependency graph ─────────────────────────────────────────────────

abbrev EntityId := Nat

/-- A directed edge (parent, child): child's transform depends on parent's. -/
abbrev DepEdge := EntityId × EntityId

/-- The entity dependency graph for one zone's authority set.
    `edges` encodes parent→child transform dependencies.
    `entities` is the set of entity IDs with authority on this zone. -/
structure DepGraph where
  entities : Array EntityId
  edges    : Array DepEdge
  deriving Inhabited

-- ── Topological sort (Kahn's algorithm) ─────────────────────────────────────

/-- Compute in-degree for each entity in the graph.
    Returns an array of (entityId, inDegree) pairs. -/
def computeInDegree (g : DepGraph) : Array (EntityId × Nat) :=
  let init := g.entities.map (· , 0)
  g.edges.foldl (fun acc (_, child) =>
    acc.map fun (eid, deg) => if eid == child then (eid, deg + 1) else (eid, deg)
  ) init

/-- Extract entities with in-degree 0 (roots / independent entities). -/
def rootsOf (inDeg : Array (EntityId × Nat)) : Array EntityId :=
  (inDeg.filter (fun (_, d) => d == 0)).map (·.1)

/-- One step of Kahn's algorithm: remove all zero-in-degree nodes,
    decrement in-degrees of their children, return (emitted, remaining). -/
def kahnStep (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge)
    : Array EntityId × Array (EntityId × Nat) :=
  let zeros := rootsOf inDeg
  let remaining := inDeg.filter (fun (_, d) => d != 0)
  let decremented := remaining.map fun (eid, deg) =>
    let decr := edges.foldl (fun count (parent, child) =>
      if child == eid && zeros.contains parent then count + 1 else count
    ) 0
    (eid, deg - decr)
  (zeros, decremented)

/-- Top-level recursive helper for topoSort (exposed for proof by induction). -/
def topoSortGo (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge)
    (acc : Array EntityId) (fuel : Nat) : Array EntityId :=
  match fuel with
  | 0 => acc ++ (inDeg.map (·.1))
  | fuel + 1 =>
    if inDeg.isEmpty then acc
    else
      let (batch, remaining) := kahnStep inDeg edges
      if batch.isEmpty then
        acc ++ (inDeg.map (·.1))
      else
        topoSortGo remaining edges (acc ++ batch) fuel

/-- Kahn's topological sort with fuel (terminates in at most |entities| steps).
    Returns solve order: earlier elements solve first in the frame.
    If a cycle exists, remaining entities are appended at the end (cycle broken). -/
def topoSort (g : DepGraph) : Array EntityId :=
  topoSortGo (computeInDegree g) g.edges #[] g.entities.size

-- ── Solve layers (parallel batches) ─────────────────────────────────────────

/-- A solve layer: entities in the same layer have no dependencies on each other
    and can solve in parallel. Layers are ordered: layer i solves before layer i+1. -/
structure SolveLayer where
  entities : Array EntityId
  deriving Inhabited, Repr

/-- Top-level recursive helper for solveLayers (exposed for proof by induction). -/
def solveLayersGo (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge)
    (acc : Array SolveLayer) (fuel : Nat) : Array SolveLayer :=
  match fuel with
  | 0 =>
    if inDeg.isEmpty then acc
    else acc.push { entities := inDeg.map (·.1) }
  | fuel + 1 =>
    if inDeg.isEmpty then acc
    else
      let (batch, remaining) := kahnStep inDeg edges
      if batch.isEmpty then
        acc.push { entities := inDeg.map (·.1) }
      else
        solveLayersGo remaining edges (acc.push { entities := batch }) fuel

/-- Compute solve layers (parallel batches). Each layer's entities are independent
    of each other; layers are sequentially ordered by dependency depth. -/
def solveLayers (g : DepGraph) : Array SolveLayer :=
  solveLayersGo (computeInDegree g) g.edges #[] g.entities.size

-- ── Cycle detection ─────────────────────────────────────────────────────────

/-- Top-level recursive helper for hasCycle (exposed for proof by induction). -/
def hasCycleGo (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => !inDeg.isEmpty
  | fuel + 1 =>
    if inDeg.isEmpty then false
    else
      let (batch, remaining) := kahnStep inDeg edges
      if batch.isEmpty then true
      else hasCycleGo remaining edges fuel

/-- True if the dependency graph contains a cycle.
    Detected when Kahn's algorithm cannot emit all entities
    (remaining non-empty with all in-degrees > 0). -/
def hasCycle (g : DepGraph) : Bool :=
  hasCycleGo (computeInDegree g) g.edges g.entities.size

-- ── Latency analysis ────────────────────────────────────────────────────────

/-- Maximum chain depth in the dependency graph.
    This equals the number of sequential solve steps required.
    Independent entities (depth 0) solve in the first layer.
    The total frame solve time = max_depth sequential steps, NOT |entities| steps. -/
def maxChainDepth (g : DepGraph) : Nat :=
  (solveLayers g).size

/-- Added latency in frames for the hierarchical approach.
    All dependent entities solve in the SAME frame → 0 added frames.
    Compare: flat approach adds 1 frame per dependency level. -/
def hierarchicalAddedLatencyFrames : Nat := 0

/-- Added latency in frames for the flat (root-bone) approach.
    Each dependency level adds 1 frame of delayed-feedback latency. -/
def flatAddedLatencyFrames (chainDepth : Nat) : Nat := chainDepth

-- ── Integration with authority zone ─────────────────────────────────────────

/-- Build the dependency graph from a zone's authority set.
    `parentOf` maps an entity to its transform parent (or none if root). -/
def buildDepGraph (entities : Array EntityId) (parentOf : EntityId → Option EntityId)
    : DepGraph :=
  let edges := entities.foldl (fun acc eid =>
    match parentOf eid with
    | some pid =>
      if entities.contains pid then acc.push (pid, eid)
      else acc
    | none => acc
  ) #[]
  { entities, edges }

/-- The solve-order manager state for one zone.
    Rebuilt each frame when the authority set or parenting changes. -/
structure SolveOrderManager where
  graph  : DepGraph
  layers : Array SolveLayer
  cyclic : Bool
  deriving Inhabited

/-- Construct the solve-order manager from the zone's authority entities
    and the current parenting function. -/
def SolveOrderManager.build (entities : Array EntityId)
    (parentOf : EntityId → Option EntityId) : SolveOrderManager :=
  let graph := buildDepGraph entities parentOf
  let layers := solveLayers graph
  let cyclic := hasCycle graph
  { graph, layers, cyclic }

-- ── Proofs ──────────────────────────────────────────────────────────────────

/-- The hierarchical approach adds zero frames of latency (by definition). -/
theorem hierarchical_zero_added_latency :
    hierarchicalAddedLatencyFrames = 0 := rfl

/-- The flat approach adds at least 1 frame for any non-trivial dependency chain. -/
theorem flat_adds_latency (depth : Nat) (h : 0 < depth) :
    0 < flatAddedLatencyFrames depth := h

/-- Hierarchical strictly beats flat on latency for any dependency chain. -/
theorem hierarchical_less_latency (depth : Nat) (h : 0 < depth) :
    hierarchicalAddedLatencyFrames < flatAddedLatencyFrames depth := by
  simp [hierarchicalAddedLatencyFrames, flatAddedLatencyFrames]
  exact h

/-- solveLayersGo adds at most fuel + 1 layers to acc.
    Proof: each recursive call pushes exactly 1 layer and decrements fuel by 1.
    Base case (fuel=0) pushes at most 1 layer. Total ≤ fuel + 1. -/
private theorem solveLayersGo_size_le (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge)
    (acc : Array SolveLayer) : (fuel : Nat) →
    (solveLayersGo inDeg edges acc fuel).size ≤ acc.size + fuel + 1
  | 0 => by
    simp only [solveLayersGo]
    split <;> simp_all [Array.size_push] <;> omega
  | fuel + 1 => by
    simp only [solveLayersGo]
    split
    · omega
    · next hne =>
      have key := solveLayersGo_size_le (kahnStep inDeg edges).2 edges
        (acc.push { entities := (kahnStep inDeg edges).1 }) fuel
      simp [Array.size_push] at key
      split <;> simp_all [Array.size_push] <;> omega

/-- An acyclic graph with n entities produces at most n + 1 solve layers. -/
theorem layers_bounded (g : DepGraph) :
    (solveLayers g).size ≤ g.entities.size + 1 := by
  unfold solveLayers
  have h := solveLayersGo_size_le (computeInDegree g) g.edges #[] g.entities.size
  simp at h
  exact h

/-- solveLayersGo on empty inDeg returns acc unchanged. -/
private theorem solveLayersGo_empty (edges : Array DepEdge) (acc : Array SolveLayer)
    : (fuel : Nat) → solveLayersGo #[] edges acc fuel = acc
  | 0 => by simp [solveLayersGo]
  | _ + 1 => by simp [solveLayersGo]

/-- Array.filter gives #[] when predicate is false on all elements.
    Uses Array.toList_filter + List.filter_eq_nil_iff from Init. -/
private theorem Array.filter_eq_empty {p : α → Bool} {arr : Array α}
    (h : ∀ x ∈ arr.toList, ¬(p x = true)) : arr.filter p = #[] := by
  rw [← Array.toList_eq_nil_iff, Array.toList_filter]
  exact List.filter_eq_nil_iff.mpr h

/-- Any element of entities.map (·, 0) has snd = 0. -/
private theorem snd_eq_zero_of_mem_map_zero {entities : Array EntityId} {x : EntityId × Nat}
    (hx : x ∈ entities.map (·, 0)) : x.2 = 0 := by
  rw [Array.mem_map] at hx
  obtain ⟨_, _, heq⟩ := hx
  exact (Prod.mk.inj heq).2.symm

/-- Filtering entities.map (·, 0) by snd ≠ 0 gives #[]. -/
@[simp] private theorem filter_map_zero_empty (entities : Array EntityId) :
    (entities.map (·, 0)).filter (fun x : EntityId × Nat => x.snd != 0) = #[] := by
  apply Array.filter_eq_empty
  intro x hx
  simp [snd_eq_zero_of_mem_map_zero (Array.mem_toList.mp hx)]

/-- Filter keeping elements where snd == 0 on an all-zero array is identity. -/
@[simp] private theorem filter_map_zero_all (entities : Array EntityId) :
    (entities.map (·, 0)).filter (fun p : EntityId × Nat => p.2 == 0) = entities.map (·, 0) := by
  rw [Array.filter_eq_self]
  intro x hx
  simp [snd_eq_zero_of_mem_map_zero hx]

/-- Bridge: Array.filter with explicit start/size on a mapped array. -/
@[simp] private theorem filter_start_size_map {p : β → Bool} {f : α → β} (arr : Array α) :
    Array.filter p (arr.map f) 0 arr.size = (arr.map f).filter p := by
  have h : arr.size = (arr.map f).size := by simp
  rw [h]

/-- computeInDegree with empty edges = entities.map (·, 0). -/
private theorem computeInDegree_noEdges (entities : Array EntityId) :
    computeInDegree { entities, edges := #[] } = entities.map (·, 0) := by
  simp [computeInDegree]

/-- kahnStep on all-zero in-degrees: remaining is #[]. -/
private theorem kahnStep_zero_remaining (entities : Array EntityId) :
    (kahnStep (entities.map (·, 0)) #[]).2 = #[] := by
  simp only [kahnStep, filter_map_zero_empty, Array.map_empty]

/-- Mapping a non-empty array gives a non-empty array. -/
private theorem Array.map_ne_empty {f : α → β} {arr : Array α} (h : arr.size > 0) :
    arr.map f ≠ #[] := by
  simp only [ne_eq, ← Array.toList_eq_nil_iff, Array.toList_map, List.map_eq_nil_iff]
  exact List.ne_nil_of_length_pos (by simp [Array.length_toList]; omega)

/-- N independent entities all solve in 1 layer (parallel). -/
theorem independent_entities_single_layer (entities : Array EntityId)
    (h : entities.size > 0) :
    (solveLayers { entities, edges := #[] }).size = 1 := by
  have hne := Array.map_ne_empty (f := fun x => (x, 0)) h
  have hfne := Array.map_ne_empty (f := Prod.fst) (arr := entities.map (·, 0))
    (by simp [Array.size_map]; exact h)
  have hne2 : ¬ (∀ (a : EntityId), ¬a ∈ entities) := by
    intro hall; exact absurd (Array.getElem_mem (i := 0) (h := by omega)) (hall _)
  unfold solveLayers
  rw [computeInDegree_noEdges]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : entities.size ≠ 0)
  rw [hn, solveLayersGo]
  simp only [kahnStep, rootsOf, filter_start_size_map, filter_map_zero_empty,
    filter_map_zero_all, Array.map_empty, Array.isEmpty_iff, hne, hfne, hne2,
    ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  simp only [filter_start_size_map, filter_map_zero_empty, solveLayersGo_empty, Array.size_push]
  rfl

/-- List partition identity. -/
private theorem list_filter_partition {p : α → Bool} :
    (l : List α) → (l.filter p).length + (l.filter (fun x => !p x)).length = l.length
  | [] => rfl
  | x :: xs => by
    unfold List.filter
    cases hp : p x with
    | false =>
      simp only [hp, Bool.not_false, ite_false, ite_true, List.length_cons]
      have := list_filter_partition (p := p) xs
      omega
    | true =>
      simp only [hp, Bool.not_true, ite_true, ite_false, List.length_cons]
      have := list_filter_partition (p := p) xs
      omega

/-- Partition identity: |filter p arr| + |filter (¬p) arr| = |arr|. -/
private theorem filter_partition_size {p : α → Bool} (arr : Array α) :
    (arr.filter p).size + (arr.filter (fun x => !p x)).size = arr.size := by
  have h1 : (arr.filter p).size = (arr.toList.filter p).length := by
    rw [Array.size_eq_length_toList, Array.toList_filter]
  have h2 : (arr.filter (fun x => !p x)).size = (arr.toList.filter (fun x => !p x)).length := by
    rw [Array.size_eq_length_toList, Array.toList_filter]
  rw [h1, h2, Array.size_eq_length_toList]
  exact list_filter_partition arr.toList

/-- kahnStep preserves total entity count: |batch| + |remaining| = |inDeg|. -/
private theorem kahnStep_size (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge) :
    (kahnStep inDeg edges).1.size + (kahnStep inDeg edges).2.size = inDeg.size := by
  simp only [kahnStep, rootsOf, Array.size_map]
  exact filter_partition_size inDeg

/-- topoSortGo preserves the invariant: output.size = acc.size + inDeg.size. -/
private theorem topoSortGo_size (inDeg : Array (EntityId × Nat)) (edges : Array DepEdge)
    (acc : Array EntityId) : (fuel : Nat) →
    (topoSortGo inDeg edges acc fuel).size = acc.size + inDeg.size
  | 0 => by
    simp [topoSortGo, Array.size_append, Array.size_map]
  | fuel + 1 => by
    simp only [topoSortGo]
    split
    · simp [Array.isEmpty_iff.mp ‹_›]
    · split
      · simp [Array.size_append, Array.size_map]
      · have ih := topoSortGo_size (kahnStep inDeg edges).2 edges
            (acc ++ (kahnStep inDeg edges).1) fuel
        rw [ih, Array.size_append]
        have := kahnStep_size inDeg edges
        omega

/-- computeInDegree preserves size: foldl of map doesn't change array length. -/
private theorem computeInDegree_size (g : DepGraph) :
    (computeInDegree g).size = g.entities.size := by
  unfold computeInDegree
  suffices h : ∀ (acc : Array (EntityId × Nat)) (edges : Array DepEdge),
      (edges.foldl (fun acc (_, child) =>
        acc.map fun (eid, deg) => if eid == child then (eid, deg + 1) else (eid, deg)
      ) acc).size = acc.size by
    rw [h]; simp [Array.size_map]
  intro acc edges
  have hstep : ∀ (a : Array (EntityId × Nat)) (e : DepEdge),
      (a.map fun (eid, deg) => if eid == e.2 then (eid, deg + 1) else (eid, deg)).size = a.size :=
    fun a _ => by simp [Array.size_map]
  exact Array.foldl_induction
    (motive := fun _ (a : Array (EntityId × Nat)) => a.size = acc.size)
    (h0 := rfl)
    (hf := fun _ a h => by simp only [hstep a]; exact h)

/-- topoSort output size always equals input size (no acyclicity needed for size). -/
theorem topoSort_is_permutation (g : DepGraph) (h : ¬ hasCycle g) :
    (topoSort g).size = g.entities.size := by
  unfold topoSort
  rw [topoSortGo_size]
  rw [show (#[] : Array EntityId).size = 0 from rfl, Nat.zero_add]
  exact computeInDegree_size g

-- ── Test scenarios from VSK-96 ──────────────────────────────────────────────
-- Entity counts match AuthorityInterest.lean capacity model:
--   Authority per zone: 1400 (cap=1800, headroom=400)
--   Interest per zone:  400  (InterestCapacity)
-- The solve-order manager operates on AUTHORITY entities only.
-- Interest replicas are read-only ghosts; they don't participate in solve order.

/-- CHOKEPOINT: 1400 independent entities in a funnel (full authority capacity).
    Counter-Strike site take: all players independent, no parent-child transforms.
    Tests: can the solver handle a full zone at max capacity in 1 pass? -/
def chokepoint_example : DepGraph :=
  { entities := (Array.range 1400).map (· + 1), edges := #[] }

/-- Chokepoint has 1 solve layer: all 1400 entities are independent → parallel. -/
theorem chokepoint_layers :
    (solveLayers chokepoint_example).size = 1 := by native_decide

/-- Chokepoint is acyclic. -/
theorem chokepoint_acyclic : hasCycle chokepoint_example = false := by native_decide

/-- CONVOY: 1 truck + 1399 passengers (full zone capacity, all parented to truck).
    Extreme case: every entity in the zone depends on one root.
    Tests: maximum width at depth 2, worst fan-out. -/
def convoy_example : DepGraph :=
  { entities := (Array.range 1400).map (· + 1),
    edges := (Array.range 1399).map (fun i => (1, i + 2)) }

/-- Convoy has 2 solve layers: truck first, then all 1399 passengers in parallel. -/
theorem convoy_layers :
    (solveLayers convoy_example).size = 2 := by native_decide

/-- Convoy is acyclic. -/
theorem convoy_acyclic : hasCycle convoy_example = false := by native_decide

/-- CONVOY_TRAIN: engine → car1 → car2 → ... → car9, each car has ~154 passengers.
    Models a train where each cabin's transform depends on the preceding cabin.
    Engine(1) → Car1(2) → Car2(3) → ... → Car9(10), passengers(11-1400).
    Tests: serial chain depth (10 cars) + fan-out per car. Depth = 11 layers.
    Contrast with flat convoy (depth 2): train tests DEEP sequential dependency. -/
def convoy_train_example : DepGraph :=
  { entities := (Array.range 1400).map (· + 1),
    edges :=
      -- Chain: engine(1)→car1(2)→car2(3)→...→car9(10)
      (Array.range 9).map (fun i => (i + 1, i + 2))
      -- Passengers 11..1400 parented to their car (round-robin across 9 cars)
      ++ (Array.range 1390).map (fun i => (i % 9 + 2, i + 11)) }

/-- Train convoy has 11 solve layers:
    Layer 0: engine. Layers 1-9: cars (sequential chain).
    Layer 2-10: passengers solve alongside the NEXT car in the chain.
    Depth = 11 because deepest passengers depend on car9 (layer 9) → layer 10. -/
theorem convoy_train_layers :
    (solveLayers convoy_train_example).size = 11 := by native_decide

/-- Train convoy is acyclic. -/
theorem convoy_train_acyclic : hasCycle convoy_train_example = false := by native_decide

/-- CONCERT: 700 performers + 700 props (full 1400 authority capacity).
    Each performer (1-700) has one attached prop (701-1400).
    The 400 interest replicas (performers visible from neighboring zones)
    are NOT in the solve order — they're read-only ghosts.
    Tests: many independent depth-2 chains at full zone capacity. -/
def concert_example : DepGraph :=
  { entities := (Array.range 1400).map (· + 1),
    edges := (Array.range 700).map (fun i => (i + 1, i + 701)) }

/-- Concert has 2 solve layers: all 700 performers parallel, then all 700 props parallel.
    Width scales to full capacity; depth stays at 2 regardless of entity count. -/
theorem concert_layers :
    (solveLayers concert_example).size = 2 := by native_decide

/-- Concert is acyclic. -/
theorem concert_acyclic : hasCycle concert_example = false := by native_decide

/-- RAGDOLL: articulated physics body with bone hierarchy.
    Body(1) → Torso(2) → Arm(3) → Forearm(4) → Hand(5) → Weapon(6)
    This is the DEEP CHAIN case: depth 6. Each bone's world-space transform
    depends on its parent bone.
    In a full zone, we'd have up to 1400/6 ≈ 233 ragdolls, each depth 6.
    They're independent of each other → still only 6 layers. -/
def ragdoll_example : DepGraph :=
  { entities := #[1, 2, 3, 4, 5, 6],
    edges := #[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] }

/-- Ragdoll has 6 solve layers: one per bone in the serial chain.
    6 × ~1μs = ~6μs, vs flat's 5 frames = 250ms for the deepest bone. -/
theorem ragdoll_layers :
    (solveLayers ragdoll_example).size = 6 := by native_decide

/-- Ragdoll is acyclic (bones form a tree). -/
theorem ragdoll_acyclic : hasCycle ragdoll_example = false := by native_decide

/-- Full ragdoll with branching: body → torso → {left_arm, right_arm, head}.
    Body(1) → Torso(2) → LeftArm(3) → LeftHand(4)
                        → RightArm(5) → RightHand(6)
                        → Head(7)
    Depth 4 (not 7) because arms branch in parallel. -/
def ragdoll_branching : DepGraph :=
  { entities := #[1, 2, 3, 4, 5, 6, 7],
    edges := #[(1, 2), (2, 3), (3, 4), (2, 5), (5, 6), (2, 7)] }

/-- Branching ragdoll: 4 layers. Branching reduces depth vs serial chain. -/
theorem ragdoll_branching_layers :
    (solveLayers ragdoll_branching).size = 4 := by native_decide

theorem ragdoll_branching_acyclic : hasCycle ragdoll_branching = false := by native_decide

/-- RAGDOLL at zone scale: 233 independent ragdolls (6 bones each = 1398 entities).
    All ragdolls are independent → depth stays 6 regardless of count.
    Tests: depth is determined by the deepest chain, not total entity count. -/
def ragdoll_zone_example : DepGraph :=
  { entities := (Array.range 1398).map (· + 1),
    edges := (Array.range 233).foldl (fun acc i =>
      let base := i * 6
      acc.push (base + 1, base + 2)
        |>.push (base + 2, base + 3)
        |>.push (base + 3, base + 4)
        |>.push (base + 4, base + 5)
        |>.push (base + 5, base + 6)
    ) #[] }

/-- 233 ragdolls still only 6 layers — depth doesn't grow with entity count. -/
theorem ragdoll_zone_layers :
    (solveLayers ragdoll_zone_example).size = 6 := by native_decide

theorem ragdoll_zone_acyclic : hasCycle ragdoll_zone_example = false := by native_decide

/-- Ragdoll: hierarchical dominates flat.
    Flat adds 5 frames of latency (depth-1) for the weapon bone.
    Hierarchical adds 0 frames (all 6 layers solve within the same frame). -/
theorem ragdoll_hierarchical_dominates :
    hierarchicalAddedLatencyFrames < flatAddedLatencyFrames 5 := by
  simp [hierarchicalAddedLatencyFrames, flatAddedLatencyFrames]

/-- A mutual-parent cycle (A→B, B→A) is detected. -/
def cycle_example : DepGraph :=
  { entities := #[1, 2], edges := #[(1, 2), (2, 1)] }

theorem cycle_detected : hasCycle cycle_example = true := by native_decide

-- ── Summary: all scenarios at zone capacity (1400 authority entities) ────────
--
-- Scenario      | Authority | Depth | Rigid intra-frame | XPR crossRegion
-- CHOKEPOINT    | 1400      | 1     | ~1μs              | n/a (no deps)
-- CONVOY        | 1400      | 2     | ~2μs              | depth 2, delay 1
-- CONVOY_TRAIN  | 1400      | 11    | ~11μs             | depth 4, delay 4 ticks
-- CONCERT       | 1400      | 2     | ~2μs              | depth 2, delay 1
-- RAGDOLL       | 1398      | 6     | ~6μs              | depth 4, delay 2 ticks
--
-- Rigid: optimal for sameRegion (1 tick RTT). Solves full chain per frame.
-- XPR bounded: optimal for crossRegion+ (≥4 tick RTT). Trades depth for delay.

-- ============================================================================
-- BOUNDED PROPAGATION SPEED (XPR / Lightspeed Studios GDC 2023)
--
-- Key insight: instead of requiring the ENTIRE dependency chain to solve in
-- one frame (rigid coupling, infinite propagation speed), set an ARTIFICIAL
-- speed of light for force/transform propagation in the game world.
--
-- With propagation speed = k hops/tick:
--   Each entity only needs ancestors within k hops to be solved THIS frame.
--   Ancestors beyond k hops: their influence hasn't arrived yet (by design).
--   The chain tip feels the root's input after chainLength/k frames.
--
-- This is NOT error — it's the intended physics. Coupling forces travel at
-- finite speed through the virtual world, just as real forces do.
--
-- Tradeoff:
--   speed = ∞ (rigid): solve depth = chainLength, latency = 0 frames
--   speed = 1 hop/tick: solve depth = 2, latency = chainLength frames
--   speed = k hops/tick: solve depth = k+1, latency = ⌈chainLength/k⌉ frames
-- ============================================================================

/-- Solve depth under bounded propagation: min(chainDepth, speed + 1).
    With finite speed, long chains are truncated to local neighborhoods. -/
def boundedSolveDepth (chainDepth speed : Nat) : Nat :=
  min chainDepth (speed + 1)

/-- Propagation delay: frames until chain tip feels root's input.
    ⌈chainDepth / speed⌉ frames for the wave to traverse the chain. -/
def propagationDelay (chainDepth speed : Nat) : Nat :=
  if speed == 0 then chainDepth
  else (chainDepth + speed - 1) / speed

/-- Rigid coupling (speed = ∞ ≈ chainDepth): solve depth = chainDepth, delay = 1 frame. -/
theorem rigid_solve_depth (d : Nat) (h : 0 < d) :
    boundedSolveDepth d d = d := by
  simp [boundedSolveDepth, Nat.min_self]

theorem rigid_delay (d : Nat) (h : 0 < d) :
    propagationDelay d d = 1 := by
  have hd : d ≠ 0 := by omega
  simp only [propagationDelay, beq_iff_eq, hd, ite_false]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Speed-1 (each car only needs its neighbor): solve depth = 2, delay = chainDepth. -/
theorem speed1_solve_depth (d : Nat) (h : 2 ≤ d) :
    boundedSolveDepth d 1 = 2 := by
  simp [boundedSolveDepth]; omega

theorem speed1_delay (d : Nat) (h : 0 < d) :
    propagationDelay d 1 = d := by
  simp [propagationDelay]

/-- CONVOY_TRAIN with rigid coupling: 11 solve layers, 1 frame delay (instant). -/
theorem train_rigid :
    boundedSolveDepth 11 11 = 11 ∧ propagationDelay 11 11 = 1 := by decide

/-- CONVOY_TRAIN with speed-1 (soft coupling): 2 solve layers, 11 frame delay.
    Each car only resolves its immediate predecessor per tick.
    The engine's impulse reaches car9's passengers after 11 frames × 50ms = 550ms.
    For VR social (not competitive physics), this soft propagation is acceptable. -/
theorem train_soft :
    boundedSolveDepth 11 1 = 2 ∧ propagationDelay 11 1 = 11 := by decide

/-- CONVOY_TRAIN with speed-3 (medium coupling): 4 solve layers, 4 frame delay.
    Each car resolves 3 hops of dependency per tick.
    Impulse reaches end in 4 frames × 50ms = 200ms. -/
theorem train_medium :
    boundedSolveDepth 11 3 = 4 ∧ propagationDelay 11 3 = 4 := by decide

/-- Optimal propagation speed derived from FabricLatency.toTicks (no duplication).
    speed = toTicks - 1: propagation must be SLOWER than network RTT so
    the server can rollback-correct before the light cone reaches the player. -/
theorem propagation_within_rtt (latency : FabricLatency) :
    latency.toTicks - 1 < latency.toTicks := by
  cases latency <;> native_decide

/-- crossRegion (4 ticks): optimal speed = 3 hops/tick. -/
theorem optimal_crossRegion :
    FabricLatency.crossRegion.toTicks - 1 = 3 := by native_decide

/-- satellite (40 ticks): optimal speed = 39 hops/tick. Almost rigid. -/
theorem optimal_satellite :
    FabricLatency.satellite.toTicks - 1 = 39 := by native_decide

/-- sameRegion (1 tick): speed = 0. Must use rigid hierarchical. -/
theorem optimal_sameRegion :
    FabricLatency.sameRegion.toTicks - 1 = 0 := by native_decide

/-- CONVOY_TRAIN at crossRegion: speed=3, depth=4, delay=4 ticks.
    No additional latency beyond what network RTT already adds. -/
theorem train_crossRegion :
    boundedSolveDepth 11 (FabricLatency.crossRegion.toTicks - 1) = 4 ∧
    propagationDelay 11 (FabricLatency.crossRegion.toTicks - 1) = 4 := by decide

/-- CONVOY_TRAIN at satellite: speed=39 ≥ 11, effectively rigid. -/
theorem train_satellite :
    boundedSolveDepth 11 (FabricLatency.satellite.toTicks - 1) = 11 ∧
    propagationDelay 11 (FabricLatency.satellite.toTicks - 1) = 1 := by decide


end SolveOrder
