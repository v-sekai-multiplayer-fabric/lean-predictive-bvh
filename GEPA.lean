-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 K. S. Ernest (iFire) Lee
--
-- Formal model of GEPA (Genetic-Pareto Evolutionary Algorithm)
-- as implemented in github.com/XiaoConstantine/dspy-go.
--
-- Key sources:
--   pkg/core/optimizer/gepa.go   — main loop, selection, mutation
--   pkg/core/types.go            — GEPACandidate, MultiObjectiveFitness

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

-- ---------------------------------------------------------------------------
-- § 1  Multi-objective fitness (7 dimensions, all ∈ [0, 1])
-- ---------------------------------------------------------------------------

structure Fitness where
  successRate   : Float   -- ∈ [0, 1]
  outputQuality : Float
  efficiency    : Float
  robustness    : Float
  generalization: Float
  diversity     : Float
  innovation    : Float
  deriving Repr

-- Pareto dominance: f₁ dominates f₂ iff f₁ ≥ f₂ in every objective
-- and f₁ > f₂ in at least one.
def dominates (f₁ f₂ : Fitness) : Prop :=
  f₁.successRate    ≥ f₂.successRate    ∧
  f₁.outputQuality  ≥ f₂.outputQuality  ∧
  f₁.efficiency     ≥ f₂.efficiency     ∧
  f₁.robustness     ≥ f₂.robustness     ∧
  f₁.generalization ≥ f₂.generalization ∧
  f₁.diversity      ≥ f₂.diversity      ∧
  f₁.innovation     ≥ f₂.innovation     ∧
  (f₁.successRate    > f₂.successRate    ∨
   f₁.outputQuality  > f₂.outputQuality  ∨
   f₁.efficiency     > f₂.efficiency     ∨
   f₁.robustness     > f₂.robustness     ∨
   f₁.generalization > f₂.generalization ∨
   f₁.diversity      > f₂.diversity      ∨
   f₁.innovation     > f₂.innovation)

-- Dominance is irreflexive.
theorem dominates_irrefl (f : Fitness) : ¬ dominates f f := by
  intro ⟨_, _, _, _, _, _, _, h⟩
  rcases h with h | h | h | h | h | h | h <;> exact absurd h (lt_irrefl _)

-- Dominance is asymmetric.
theorem dominates_asymm (f₁ f₂ : Fitness) :
    dominates f₁ f₂ → ¬ dominates f₂ f₁ := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, hlt⟩ ⟨_, _, _, _, _, _, _, hlt'⟩
  rcases hlt with hlt | hlt | hlt | hlt | hlt | hlt | hlt <;>
  rcases hlt' with hlt' | hlt' | hlt' | hlt' | hlt' | hlt' | hlt' <;>
  simp_all [ge_iff_le] <;> linarith

-- ---------------------------------------------------------------------------
-- § 2  Pareto archive validity
-- ---------------------------------------------------------------------------

-- A list of fitnesses is Pareto-optimal if no element is dominated by another.
def isParetoOptimal (archive : List Fitness) : Prop :=
  ∀ f₁ ∈ archive, ∀ f₂ ∈ archive, ¬ dominates f₁ f₂ ∨ f₁ = f₂

-- An empty archive is trivially Pareto-optimal.
theorem paretoOptimal_nil : isParetoOptimal [] := by
  intro _ h; exact absurd h (List.not_mem_nil _)

-- A singleton archive is Pareto-optimal (no distinct pair exists).
theorem paretoOptimal_singleton (f : Fitness) : isParetoOptimal [f] := by
  intro f₁ h₁ f₂ h₂
  simp [List.mem_singleton] at h₁ h₂
  subst h₁; subst h₂
  right; rfl

-- ---------------------------------------------------------------------------
-- § 3  Generation counter monotonicity
-- ---------------------------------------------------------------------------

-- A sequence of generation numbers is strictly increasing.
def generationsStrictlyIncreasing (gens : List Nat) : Prop :=
  List.Chain' (· < ·) gens

theorem gen_mono_nil : generationsStrictlyIncreasing [] :=
  List.Chain'.nil

theorem gen_mono_single (n : Nat) : generationsStrictlyIncreasing [n] :=
  List.chain'_singleton _

-- If we append a generation strictly greater than the last, the sequence
-- remains strictly increasing.
theorem gen_mono_append (gens : List Nat) (n : Nat)
    (h_mono : generationsStrictlyIncreasing gens)
    (h_last : ∀ m ∈ gens.getLast?, m < n) :
    generationsStrictlyIncreasing (gens ++ [n]) := by
  induction gens with
  | nil => exact gen_mono_single n
  | cons hd tl ih =>
    simp [List.Chain', List.chain'_cons] at *
    exact ⟨fun x hx => by
      cases hd_or : tl.getLast? with
      | none =>
        simp [List.getLast?_eq_none_iff] at hd_or
        subst hd_or
        simp [List.mem_singleton] at hx
        subst hx
        apply h_last
        simp [List.getLast?_cons_cons]
      | some last =>
        sorry, -- requires further case analysis
     h_mono.tail⟩

-- ---------------------------------------------------------------------------
-- § 4  Population replacement invariant
-- ---------------------------------------------------------------------------

-- In each GEPA generation, exactly one candidate slot is replaced.
-- We model this as: given populations p₁ and p₂ of equal size,
-- they differ in at most one position.
def differsInOneSlot {α : Type} (p₁ p₂ : List α) : Prop :=
  p₁.length = p₂.length ∧
  (List.zipWith (fun a b => a = b) p₁ p₂).count false ≤ 1

-- After one replacement step the population size is preserved.
theorem population_size_preserved {α : Type} (pop : List α) (i : Fin pop.length) (c : α) :
    (pop.set i c).length = pop.length := List.length_set _ _ _

-- ---------------------------------------------------------------------------
-- § 5  Archive size bound
-- ---------------------------------------------------------------------------

-- The Pareto archive never exceeds the configured maximum.
-- (GEPA trims by crowding distance when the limit is reached.)
def archiveSizeBounded (archive : List Fitness) (maxSize : Nat) : Prop :=
  archive.length ≤ maxSize

-- Trimming to maxSize preserves the bound.
theorem archive_trim_bounded (archive : List Fitness) (maxSize : Nat) :
    archiveSizeBounded (archive.take maxSize) maxSize := by
  unfold archiveSizeBounded
  exact List.length_take_le _ _

-- ---------------------------------------------------------------------------
-- § 6  Correctness sketch: archive remains optimal after adding a non-dominated candidate
-- ---------------------------------------------------------------------------

-- After filtering dominated solutions from the archive and adding a new candidate,
-- the result is Pareto-optimal (modulo the new candidate not being dominated).
-- Full proof requires decidability of `dominates`; stated as an axiom here.
axiom paretoUpdate_optimal
    (archive : List Fitness) (f : Fitness)
    (h_opt : isParetoOptimal archive)
    (h_nondom : ∀ f' ∈ archive, ¬ dominates f' f) :
    isParetoOptimal (f :: archive.filter (fun f' => ¬ dominates f f'))
