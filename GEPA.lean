-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 K. S. Ernest (iFire) Lee
--
-- Formal model of GEPA (Genetic Evolutionary Prompt Adaptation).
--
-- Implementation: Stanford dspy via dspex (hex.pm/packages/dspex).
-- Agrawal et al., "GEPA: Reflective Prompt Evolution Can Outperform
-- Reinforcement Learning", ICLR 2026 (arXiv:2507.19457).
-- Elixir entry point: Taskweft.GEPA.Compiler.compile/3
--                     wraps Dspy.Teleprompt.GEPA.compile!
--
-- §§ 1–5 model the multi-objective Pareto dominance structure used
-- internally by GEPA for instance-level diversity (candidate_selection_strategy
-- = "pareto").  The 7-dim Fitness structure maps to dspy-go's GEPACandidate
-- for reference; the production variant uses a single scalar per task.
--
-- §§ 6–8 model the round-monotonicity and selection correctness guarantees
-- of the outer optimization loop (evolve/reflect single-round API).

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

-- Dominance is transitive.
theorem dominates_trans {S : Type} [LinearOrder S] {f₁ f₂ f₃ : Fitness S}
    (h12 : dominates f₁ f₂) (h23 : dominates f₂ f₃) : dominates f₁ f₃ := by
  obtain ⟨ge1, ge2, ge3, ge4, ge5, ge6, ge7, hlt⟩ := h12
  obtain ⟨ge1', ge2', ge3', ge4', ge5', ge6', ge7', -⟩ := h23
  refine ⟨le_trans ge1' ge1, le_trans ge2' ge2, le_trans ge3' ge3,
          le_trans ge4' ge4, le_trans ge5' ge5, le_trans ge6' ge6,
          le_trans ge7' ge7, ?_⟩
  -- hlt : f₁.x > f₂.x = f₂.x < f₁.x; ge_i' : f₃.x ≤ f₂.x
  -- lt_of_le_of_lt : a ≤ b → b < c → a < c  ⟹  f₃.x < f₁.x = f₁.x > f₃.x
  rcases hlt with hlt | hlt | hlt | hlt | hlt | hlt | hlt
  · exact Or.inl (lt_of_le_of_lt ge1' hlt)
  · exact Or.inr (Or.inl (lt_of_le_of_lt ge2' hlt))
  · exact Or.inr (Or.inr (Or.inl (lt_of_le_of_lt ge3' hlt)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (lt_of_le_of_lt ge4' hlt))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lt_of_le_of_lt ge5' hlt)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lt_of_le_of_lt ge6' hlt))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (lt_of_le_of_lt ge7' hlt))))))

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
-- preserves Pareto optimality.  Parameterised over the filtered list to avoid
-- requiring a Decidable instance for `dominates`.
theorem paretoUpdate_optimal {S : Type} [LinearOrder S]
    (archive filtered : List (Fitness S)) (f : Fitness S)
    (h_filter   : ∀ f' ∈ filtered, f' ∈ archive ∧ ¬ dominates f f')
    (h_complete : ∀ f' ∈ archive, ¬ dominates f f' → f' ∈ filtered)
    (h_opt      : isParetoOptimal archive)
    (h_new      : ∀ f' ∈ archive, ¬ dominates f' f) :
    isParetoOptimal (f :: filtered) := by
  intro f₁ hf₁ f₂ hf₂ hne
  simp [List.mem_cons] at hf₁ hf₂
  rcases hf₁ with rfl | hf₁ <;> rcases hf₂ with rfl | hf₂
  · exact absurd rfl hne
  · exact (h_filter f₂ hf₂).2
  · intro hdom
    exact h_new f₁ (h_filter f₁ hf₁).1 hdom
  · exact h_opt f₁ (h_filter f₁ hf₁).1 f₂ (h_filter f₂ hf₂).1 hne

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

-- ===========================================================================
-- § 6  Stanford dspy GEPA — reflective mutation model
--
-- The Stanford variant (stanfordnlp/dspy) uses a *single* scalar score and
-- improves instructions via LM-driven reflective mutation rather than Pareto
-- selection.  The core loop per round:
--   1. Evaluate current candidate → collect (input, output, feedback) triples.
--   2. Propose new instruction per component using the reflective dataset.
--   3. Accept the proposal if its score ≥ current best; discard otherwise.
-- ===========================================================================

-- A candidate maps component name (String) to instruction text.
abbrev Candidate := String → String

-- A reflective example bundles the inputs, generated output, and text feedback
-- that the LM receives when proposing a new instruction.
structure ReflectiveExample where
  inputs   : String   -- serialised predictor inputs
  outputs  : String   -- serialised predictor outputs (or parse-failure message)
  feedback : String   -- evaluation feedback for this predictor invocation
  deriving Repr

-- Validity: every reflective example must carry non-empty feedback.
def validReflectiveExample (e : ReflectiveExample) : Prop :=
  e.feedback ≠ ""

-- A reflective dataset maps component names to their example lists.
abbrev ReflectiveDataset := String → List ReflectiveExample

-- ---------------------------------------------------------------------------
-- § 7  Round-monotonicity invariant
-- ---------------------------------------------------------------------------

-- A score history is non-decreasing (best score never regresses across rounds).
def scoresNonDecreasing {S : Type} [Preorder S] (scores : List S) : Prop :=
  scores.Pairwise (· ≤ ·)

theorem scores_mono_nil {S : Type} [Preorder S] :
    scoresNonDecreasing ([] : List S) :=
  List.Pairwise.nil

theorem scores_mono_single {S : Type} [Preorder S] (s : S) :
    scoresNonDecreasing [s] :=
  List.pairwise_singleton _ _

-- Appending a score ≥ every previous score preserves non-decreasingness.
theorem scores_mono_append {S : Type} [Preorder S] (scores : List S) (s : S)
    (h_mono : scoresNonDecreasing scores)
    (h_ge   : ∀ s' ∈ scores, s' ≤ s) :
    scoresNonDecreasing (scores ++ [s]) := by
  unfold scoresNonDecreasing
  rw [List.pairwise_append]
  exact ⟨h_mono, List.pairwise_singleton _ _,
         fun a ha b hb => by
           rw [List.mem_singleton] at hb; subst hb; exact h_ge a ha⟩

-- ---------------------------------------------------------------------------
-- § 8  Selection correctness
-- ---------------------------------------------------------------------------

-- A scored candidate list: (instruction-map, score) pairs.
abbrev ScoredCandidates (S : Type) := List (Candidate × S)

-- `isBestCandidate` characterises the winner: it is in the list and its
-- score upper-bounds every other entry.
def isBestCandidate {S : Type} [Preorder S] (candidates : ScoredCandidates S)
    (winner : Candidate) (winScore : S) : Prop :=
  (winner, winScore) ∈ candidates ∧
  ∀ c s, (c, s) ∈ candidates → s ≤ winScore

-- The winner's score upper-bounds all other scores.
theorem bestCandidate_maximal {S : Type} [Preorder S]
    (candidates : ScoredCandidates S) (w : Candidate) (ws : S)
    (h : isBestCandidate candidates w ws)
    (c : Candidate) (s : S) (hc : (c, s) ∈ candidates) :
    s ≤ ws :=
  h.2 c s hc

-- Accepting a proposed candidate only when score ≥ current best preserves
-- non-decreasingness: appending `proposed` to a non-decreasing history where
-- every prior score ≤ proposed produces a non-decreasing history.
theorem accept_preserves_monotonicity {S : Type} [Preorder S]
    (history : List S) (proposed : S)
    (h_hist : scoresNonDecreasing history)
    (h_best : ∀ s ∈ history, s ≤ proposed) :
    scoresNonDecreasing (history ++ [proposed]) :=
  scores_mono_append history proposed h_hist h_best
