/-
Copyright (c) 2026 PNP Labs.

Terminal-derived reference resolution for the HResolve support boundary.  For
every finite direct-wire candidate, the governed candidate family is now the
canonical enumeration of every seed in its terminal primitive-record
universe.  The saturation relation is derived from the candidate model, and
the exact and gain predicates are computed from the saturated extracted
support's residual slack.  Every governed seed therefore has exactly one of
the two constructive routes, with semantic-minimum or strict-equivalent-gain
evidence.

The residual reference minimum is exhaustive.  This module does not implement
the manuscript's HN grammar, BWL algorithm, ParseOrExit or H-disjointness,
construct blocker dependencies, prove a NoHereditary sidecar, establish a
polynomial resolver, complete HResolve or the no-lower ledger, prove
unconditional ZeroSlack or PCCMin, remove a project assumption, prove SAT in
P, or prove P = NP.
-/

import PNP.ResidualGainStopping
import PNP.ResidualTerminalCandidateSaturation
import PNP.ResidualTerminalHResolveCoverageLedger

namespace PNP
namespace DirectWire

/-! ## Duplicate-free terminal-derived family -/

private theorem terminalListSubsets_member_subset
    {alpha : Type} {item : alpha} {subset items : List alpha}
    (subsetMember : subset ∈ terminalListSubsets items)
    (itemMember : item ∈ subset) : item ∈ items := by
  induction items generalizing subset with
  | nil =>
      simp only [terminalListSubsets, List.mem_cons, List.not_mem_nil,
        or_false] at subsetMember
      subst subset
      exact False.elim (List.not_mem_nil itemMember)
  | cons head tail ih =>
      unfold terminalListSubsets at subsetMember
      cases List.mem_append.mp subsetMember with
      | inl tailSubset =>
          exact List.Mem.tail head (ih tailSubset itemMember)
      | inr prefixedSubset =>
          obtain ⟨tailPart, tailPartMember, prefixedEqual⟩ :=
            List.mem_map.mp prefixedSubset
          rw [← prefixedEqual] at itemMember
          cases List.mem_cons.mp itemMember with
          | inl atHead =>
              exact atHead ▸ List.Mem.head tail
          | inr inTailPart =>
              exact List.Mem.tail head (ih tailPartMember inTailPart)

private theorem terminalListSubsets_map_cons_nodup
    {alpha : Type} (head : alpha) {subsets : List (List alpha)}
    (distinct : subsets.Nodup) :
    (subsets.map fun subset => head :: subset).Nodup := by
  induction subsets with
  | nil => exact List.nodup_nil
  | cons subset subsets ih =>
      have split := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp member
        apply split.1
        exact List.cons.inj equal |>.2 ▸ otherMember
      · exact ih split.2

/-- The canonical subset enumeration is itself duplicate-free whenever its
    underlying record universe is duplicate-free. -/
theorem terminalListSubsets_nodup {alpha : Type} {items : List alpha}
    (distinct : items.Nodup) : (terminalListSubsets items).Nodup := by
  induction items with
  | nil =>
      exact List.nodup_cons.mpr
        ⟨(fun member => List.not_mem_nil member), List.nodup_nil⟩
  | cons head tail ih =>
      have split := List.nodup_cons.mp distinct
      let remaining := terminalListSubsets tail
      change (remaining ++ remaining.map (fun subset => head :: subset)).Nodup
      apply List.nodup_append.mpr
      refine ⟨ih split.2,
        terminalListSubsets_map_cons_nodup head (ih split.2), ?_⟩
      intro left leftMember right rightMember equal
      obtain ⟨rightTail, rightTailMember, rightEqual⟩ :=
        List.mem_map.mp rightMember
      have headInLeft : head ∈ left := by
        rw [equal, ← rightEqual]
        exact List.Mem.head rightTail
      exact split.1
        (terminalListSubsets_member_subset leftMember headInLeft)

/-- The HResolve candidate family is constructed from the complete canonical
    seed universe for the terminal dimensions.  No caller supplies a list. -/
def terminalHResolveSupportFamily
    (inputs gates outputs profileWidth : Nat) :
    TerminalHResolveFamily
      (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  ⟨allTerminalSupportSeeds inputs gates outputs profileWidth⟩

/-- The terminal-derived HResolve family has no duplicate candidates. -/
theorem terminalHResolveSupportFamily_nodup
    (inputs gates outputs profileWidth : Nat) :
    (terminalHResolveSupportFamily inputs gates outputs profileWidth).candidates.Nodup :=
  terminalListSubsets_nodup
    (allTerminalPrimitiveRecords_nodup inputs gates outputs profileWidth)

/-- Every Boolean-selected canonical terminal seed occurs in the derived
    HResolve family. -/
theorem canonicalTerminalSupportSeed_mem_terminalHResolveSupportFamily
    (inputs gates outputs profileWidth : Nat)
    (select : TerminalPrimitiveRecord inputs gates outputs profileWidth → Bool) :
    canonicalTerminalSupportSeed inputs gates outputs profileWidth select ∈
      (terminalHResolveSupportFamily
        inputs gates outputs profileWidth).candidates :=
  canonicalTerminalSupportSeed_mem
    inputs gates outputs profileWidth select

/-! ## Computed exact and gain semantics -/

/-- The actual saturated open-support implementation resolved at one
    canonical terminal seed.  Its saturation relation is candidate-derived. -/
def terminalHResolveSupportImplementation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  (extractSaturatedTerminalSupport candidate
      (terminalCandidateSaturationSystem candidate model) seed).extractedCandidate
    |>.toImplementation

/-- The computed exact route means zero exhaustive reference slack. -/
def TerminalHResolveSupportExact
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  residualSlack
    (terminalHResolveSupportImplementation candidate model seed) = 0

/-- The computed gain route means positive exhaustive reference slack. -/
def TerminalHResolveSupportGain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  0 < residualSlack
    (terminalHResolveSupportImplementation candidate model seed)

private instance terminalHResolveSupportExactDecidable
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    DecidablePred (TerminalHResolveSupportExact candidate model) :=
  fun seed => by
    unfold TerminalHResolveSupportExact
    infer_instance

private instance terminalHResolveSupportGainDecidable
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    DecidablePred (TerminalHResolveSupportGain candidate model) :=
  fun seed => by
    unfold TerminalHResolveSupportGain
    infer_instance

/-- Exact routing is precisely semantic minimality of the saturated extracted
    support. -/
theorem terminalHResolveSupportExact_iff_semanticallyMinimum
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalHResolveSupportExact candidate model seed ↔
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation candidate model seed) := by
  exact residualSlack_eq_zero_iff_minimum
    (terminalHResolveSupportImplementation candidate model seed)

/-- Gain routing is precisely existence of a strictly smaller semantically
    equivalent implementation for the saturated extracted support. -/
theorem terminalHResolveSupportGain_iff_exists_strictEquivalentGain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalHResolveSupportGain candidate model seed ↔
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation candidate model seed) next := by
  exact residualSlack_pos_iff_exists_strictEquivalentGain
    (terminalHResolveSupportImplementation candidate model seed)

/-- Every saturated extracted terminal support has exactly the exhaustive
    exact route or the exhaustive strict-gain route. -/
theorem terminalHResolveSupport_exact_or_gain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalHResolveSupportExact candidate model seed ∨
      TerminalHResolveSupportGain candidate model seed := by
  cases slackValue : residualSlack
      (terminalHResolveSupportImplementation candidate model seed) with
  | zero =>
      exact Or.inl slackValue
  | succ slack =>
      apply Or.inr
      unfold TerminalHResolveSupportGain
      rw [slackValue]
      exact Nat.zero_lt_succ slack

/-- Run the existing fixed-priority HResolve classifier with terminal-derived
    exact and gain predicates.  A blocker predicate is not supplied. -/
def terminalHResolveSupportClassify
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalHResolveRoute :=
  terminalHResolveClassify
    (TerminalHResolveSupportExact candidate model)
    (TerminalHResolveSupportGain candidate model)
    (fun _seed => False) seed

/-- The terminal-derived classifier's exact result has its computed semantic
    meaning. -/
theorem terminalHResolveSupportClassify_eq_exact_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalHResolveSupportClassify candidate model seed = .exact ↔
      TerminalHResolveSupportExact candidate model seed := by
  change terminalHResolveClassify
      (TerminalHResolveSupportExact candidate model)
      (TerminalHResolveSupportGain candidate model)
      (fun _seed => False) seed = .exact ↔
    TerminalHResolveSupportExact candidate model seed
  exact terminalHResolveClassify_eq_exact_iff
    (TerminalHResolveSupportExact candidate model)
    (TerminalHResolveSupportGain candidate model)
    (fun _seed => False) seed

/-- The terminal-derived classifier's gain result has its computed semantic
    meaning; positive slack already excludes the higher-priority exact route. -/
theorem terminalHResolveSupportClassify_eq_gain_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalHResolveSupportClassify candidate model seed = .gain ↔
      TerminalHResolveSupportGain candidate model seed := by
  change terminalHResolveClassify
      (TerminalHResolveSupportExact candidate model)
      (TerminalHResolveSupportGain candidate model)
      (fun _seed => False) seed = .gain ↔
    TerminalHResolveSupportGain candidate model seed
  rw [terminalHResolveClassify_eq_gain_iff]
  constructor
  · exact fun routed => routed.2
  · intro gain
    refine ⟨?_, gain⟩
    intro exact
    unfold TerminalHResolveSupportExact at exact
    unfold TerminalHResolveSupportGain at gain
    rw [exact] at gain
    exact Nat.not_lt_zero 0 gain

/-- The derived classifier never falls through to a blocker or unresolved
    result because exact and positive Nat slack are exhaustive. -/
theorem terminalHResolveSupportClassify_constructive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalHResolveSupportClassify candidate model seed = .exact ∨
      terminalHResolveSupportClassify candidate model seed = .gain := by
  cases terminalHResolveSupport_exact_or_gain candidate model seed with
  | inl exact =>
      exact Or.inl
        ((terminalHResolveSupportClassify_eq_exact_iff
          candidate model seed).2 exact)
  | inr gain =>
      exact Or.inr
        ((terminalHResolveSupportClassify_eq_gain_iff
          candidate model seed).2 gain)

/-- Named M170 endpoint: every member of the mechanically derived governed
    support universe receives an exact semantic-minimum route or a genuine
    strict-equivalent-gain route. -/
theorem terminal_hresolve_support_resolver_constructive_complete
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (terminalHResolveSupportFamily
        inputs gates outputs profileWidth).candidates.Nodup ∧
      ∀ seed,
        seed ∈ (terminalHResolveSupportFamily
          inputs gates outputs profileWidth).candidates →
        (terminalHResolveSupportClassify candidate model seed = .exact ∧
          IsSemanticallyMinimum
            (terminalHResolveSupportImplementation candidate model seed)) ∨
        (terminalHResolveSupportClassify candidate model seed = .gain ∧
          ∃ next, StrictEquivalentGain
            (terminalHResolveSupportImplementation candidate model seed) next) := by
  refine ⟨terminalHResolveSupportFamily_nodup
    inputs gates outputs profileWidth, ?_⟩
  intro seed _governed
  cases terminalHResolveSupport_exact_or_gain candidate model seed with
  | inl exact =>
      exact Or.inl ⟨
        (terminalHResolveSupportClassify_eq_exact_iff
          candidate model seed).2 exact,
        (terminalHResolveSupportExact_iff_semanticallyMinimum
          candidate model seed).1 exact⟩
  | inr gain =>
      exact Or.inr ⟨
        (terminalHResolveSupportClassify_eq_gain_iff
          candidate model seed).2 gain,
        (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
          candidate model seed).1 gain⟩

end DirectWire
end PNP
