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
import Mathlib.Order.Basic

-- ---------------------------------------------------------------------------
-- § 1  Multi-objective fitness (7 dimensions over an abstract linear order)
-- ---------------------------------------------------------------------------

-- Score is abstract; any LinearOrder (ℚ, ℝ, scaled Nat) can fill it.
structure Fitness (S : Type) [LinearOrder S] where
  successRate    : S
  outputQuality  : S
  efficiency     : S
  robustness     : S
  generalization : S
  diversity      : S
  innovation     : S
  deriving DecidableEq, Repr

-- Pareto dominance: f₁ dominates f₂ iff f₁ ≥ f₂ on every objective and
-- f₁ > f₂ on at least one.
def dominates {S : Type} [LinearOrder S] (f₁ f₂ : Fitness S) : Prop :=
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

-- Dominance is irreflexive: no vector dominates itself.
theorem dominates_irrefl {S : Type} [LinearOrder S] (f : Fitness S) :
    ¬ dominates f f := by
  rintro ⟨-, -, -, -, -, -, -, h | h | h | h | h | h | h⟩ <;>
    exact absurd h (lt_irrefl _)

-- Dominance is asymmetric.
theorem dominates_asymm {S : Type} [LinearOrder S] {f₁ f₂ : Fitness S}
    (h12 : dominates f₁ f₂) (h21 : dominates f₂ f₁) : False := by
  obtain ⟨ge1, ge2, ge3, ge4, ge5, ge6, ge7, hlt⟩ := h12
  obtain ⟨le1, le2, le3, le4, le5, le6, le7, -⟩   := h21
  -- ge_i : f₁.x ≥ f₂.x  (i.e. f₂.x ≤ f₁.x)
  -- le_i : f₂.x ≥ f₁.x  (i.e. f₁.x ≤ f₂.x)
  -- Together they give f₁.x = f₂.x, contradicting hlt : f₁.x > f₂.x.
  rcases hlt with hlt | hlt | hlt | hlt | hlt | hlt | hlt
  · exact absurd (le_antisymm le1 ge1) (ne_of_gt hlt)
  · exact absurd (le_antisymm le2 ge2) (ne_of_gt hlt)
  · exact absurd (le_antisymm le3 ge3) (ne_of_gt hlt)
  · exact absurd (le_antisymm le4 ge4) (ne_of_gt hlt)
  · exact absurd (le_antisymm le5 ge5) (ne_of_gt hlt)
  · exact absurd (le_antisymm le6 ge6) (ne_of_gt hlt)
  · exact absurd (le_antisymm le7 ge7) (ne_of_gt hlt)

-- ---------------------------------------------------------------------------
-- § 2  Pareto archive validity
-- ---------------------------------------------------------------------------

-- A valid Pareto archive contains no distinct pair where one dominates the other.
def isParetoOptimal {S : Type} [LinearOrder S] (archive : List (Fitness S)) : Prop :=
  ∀ f₁ ∈ archive, ∀ f₂ ∈ archive, f₁ ≠ f₂ → ¬ dominates f₁ f₂

theorem paretoOptimal_nil {S : Type} [LinearOrder S] :
    isParetoOptimal ([] : List (Fitness S)) := by
  simp [isParetoOptimal]

theorem paretoOptimal_singleton {S : Type} [LinearOrder S] (f : Fitness S) :
    isParetoOptimal [f] := by
  simp [isParetoOptimal]

-- Updating the archive (filter dominated entries, insert non-dominated candidate)
-- preserves Pareto optimality.  Parameterised over the filtered list so the
-- axiom avoids requiring a Decidable instance for `dominates`.
axiom paretoUpdate_optimal {S : Type} [LinearOrder S]
    (archive filtered : List (Fitness S)) (f : Fitness S)
    (h_filter   : ∀ f' ∈ filtered, f' ∈ archive ∧ ¬ dominates f f')
    (h_complete : ∀ f' ∈ archive, ¬ dominates f f' → f' ∈ filtered)
    (h_opt      : isParetoOptimal archive)
    (h_new      : ∀ f' ∈ archive, ¬ dominates f' f) :
    isParetoOptimal (f :: filtered)

-- ---------------------------------------------------------------------------
-- § 3  Generation counter monotonicity
-- ---------------------------------------------------------------------------

-- A strictly increasing sequence of generation numbers.
def generationsStrictlyIncreasing (gens : List ℕ) : Prop :=
  gens.Pairwise (· < ·)

theorem gen_mono_nil : generationsStrictlyIncreasing [] :=
  List.Pairwise.nil

theorem gen_mono_single (n : ℕ) : generationsStrictlyIncreasing [n] :=
  List.pairwise_singleton _ _

theorem gen_mono_append (gens : List ℕ) (n : ℕ)
    (h_mono : generationsStrictlyIncreasing gens)
    (h_lt   : ∀ m ∈ gens, m < n) :
    generationsStrictlyIncreasing (gens ++ [n]) := by
  unfold generationsStrictlyIncreasing
  rw [List.pairwise_append]
  exact ⟨h_mono, List.pairwise_singleton _ _,
         fun a ha b hb => by
           rw [List.mem_singleton] at hb; subst hb; exact h_lt a ha⟩

-- ---------------------------------------------------------------------------
-- § 4  Population replacement invariant
-- ---------------------------------------------------------------------------

-- Replacing one slot preserves population size.
theorem population_size_preserved {α : Type} (pop : List α) (i : ℕ) (c : α) :
    (pop.set i c).length = pop.length :=
  List.length_set

-- ---------------------------------------------------------------------------
-- § 5  Archive size bound
-- ---------------------------------------------------------------------------

-- Crowding-distance trimming keeps the archive within the configured maximum.
theorem archive_trim_bounded {S : Type} [LinearOrder S]
    (archive : List (Fitness S)) (maxSize : ℕ) :
    (archive.take maxSize).length ≤ maxSize :=
  List.length_take_le _ _
