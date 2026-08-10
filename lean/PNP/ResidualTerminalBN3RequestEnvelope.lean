/-
Copyright (c) 2026 PNP Labs.

Candidate-derived finite BN3 request envelopes.  Starting from the successful
computed BCEL anchor-nucleus result, this module uses the nucleus's canonical
primitive-record order as one request-atom identity space for every proper
cut.  Activation is exact list membership, so it is monotone, stable under
extensional transport, represented by an exact singleton minimal consumer,
and accounted without duplicates.  One definition then selects the canonical
full or quotient BN2 basis at every proper cut and proves every selected basis
side-tight and coherent.

The construction is finite and exhaustive.  Its proper-cut enumeration uses
all subsets of the computed nucleus and therefore carries no polynomial
runtime claim.  It does not derive the terminal dependency system, turn local
routes into the manuscript's complete global outcome system, construct BN4 to
BN6, prove selector completeness, ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalBCELAnchorNucleus

namespace PNP
namespace DirectWire

/-! ## Canonical finite request atoms -/

/-- Every list emitted by the canonical subset enumerator is a sublist of its
    source.  This is the order-preservation fact used by the BN3 atom ledger. -/
theorem terminalListSubsets_sublist
    {alpha : Type} (items subset : List alpha)
    (member : subset ∈ terminalListSubsets items) :
    List.Sublist subset items := by
  induction items generalizing subset with
  | nil =>
      simp [terminalListSubsets] at member
      subst subset
      exact List.Sublist.slnil
  | cons head tail ih =>
      unfold terminalListSubsets at member
      cases List.mem_append.mp member with
      | inl tailMember =>
          exact List.Sublist.cons head (ih subset tailMember)
      | inr headMember =>
          obtain ⟨rest, restMember, equal⟩ := List.mem_map.mp headMember
          subst subset
          exact List.Sublist.cons_cons head (ih rest restMember)

/-- The successful nucleus's primitive records are the one canonical request
    identity space used at every cut. -/
def TerminalComputedBCELAnchorNucleus.requestAtoms
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  result.nucleus.anchors

/-- Candidate-derived request identities are duplicate-free. -/
theorem TerminalComputedBCELAnchorNucleus.requestAtoms_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) :
    result.requestAtoms.Nodup := by
  exact problem.anchorRecords_nodup.sublist
    (terminalListSubsets_sublist problem.anchorRecords result.requestAtoms <| by
      simpa [TerminalComputedBCELAnchorNucleus.requestAtoms,
        TerminalBCELAnchorProblem.allAnchorSubfamilies] using
        result.nucleus.governed)

/-! ## Stable monotone activation and exact minimal consumers -/

/-- One request atom is active on exactly the cuts containing its canonical
    primitive-record identity. -/
def TerminalBN3RequestPredicate
    {alpha : Type} (atom : alpha) (cut : List alpha) : Prop :=
  atom ∈ cut

private def terminalBN3RequestPredicateDecidable
    {alpha : Type} [DecidableEq alpha]
    (atom : alpha) (cut : List alpha) :
    Decidable (TerminalBN3RequestPredicate atom cut) := by
  unfold TerminalBN3RequestPredicate
  infer_instance

/-- Executable request activation. -/
def terminalBN3RequestPredicateBool
    {alpha : Type} [DecidableEq alpha]
    (atom : alpha) (cut : List alpha) : Bool :=
  @decide (TerminalBN3RequestPredicate atom cut)
    (terminalBN3RequestPredicateDecidable atom cut)

/-- Boolean activation is exact. -/
theorem terminalBN3RequestPredicateBool_eq_true_iff
    {alpha : Type} [DecidableEq alpha]
    (atom : alpha) (cut : List alpha) :
    terminalBN3RequestPredicateBool atom cut = true ↔
      TerminalBN3RequestPredicate atom cut := by
  letI : Decidable (TerminalBN3RequestPredicate atom cut) :=
    terminalBN3RequestPredicateDecidable atom cut
  unfold terminalBN3RequestPredicateBool
  exact decide_eq_true_iff

/-- Request activation is monotone under cut inclusion. -/
theorem terminalBN3RequestPredicate_monotone
    {alpha : Type} (atom : alpha) (left right : List alpha)
    (included : ∀ record, record ∈ left -> record ∈ right)
    (active : TerminalBN3RequestPredicate atom left) :
    TerminalBN3RequestPredicate atom right :=
  included atom active

/-- The predicate is stable under every transport preserving canonical atom
    membership; no selected basis participates in its identity. -/
theorem terminalBN3RequestPredicate_stable
    {alpha : Type} (atom : alpha) (left right : List alpha)
    (transport : ∀ record, record ∈ left ↔ record ∈ right) :
    TerminalBN3RequestPredicate atom left ↔
      TerminalBN3RequestPredicate atom right :=
  transport atom

/-- The exact minimal consumer for a membership request is its singleton atom
    list. -/
def terminalBN3MinimalConsumer
    {alpha : Type} (atom : alpha) : List alpha :=
  [atom]

/-- A request is active exactly when its singleton minimal consumer is
    contained in the cut. -/
theorem terminalBN3MinimalConsumer_exact
    {alpha : Type} (atom : alpha) (cut : List alpha) :
    TerminalBN3RequestPredicate atom cut ↔
      ∀ record, record ∈ terminalBN3MinimalConsumer atom -> record ∈ cut := by
  simp [TerminalBN3RequestPredicate, terminalBN3MinimalConsumer]

/-! ## Exact duplicate-free incidence ledger -/

/-- Active atoms in the canonical nucleus order. -/
def TerminalComputedBCELAnchorNucleus.activeRequestAtoms
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  result.requestAtoms.filter
    (fun atom => terminalBN3RequestPredicateBool atom cut)

/-- The active ledger contains exactly nucleus atoms whose predicate is true. -/
theorem TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    atom ∈ result.activeRequestAtoms cut ↔
      atom ∈ result.requestAtoms ∧ TerminalBN3RequestPredicate atom cut := by
  simp [TerminalComputedBCELAnchorNucleus.activeRequestAtoms,
    terminalBN3RequestPredicateBool_eq_true_iff]

/-- Filtering a duplicate-free identity space cannot double count an atom. -/
theorem TerminalComputedBCELAnchorNucleus.activeRequestAtoms_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (result.activeRequestAtoms cut).Nodup :=
  result.requestAtoms_nodup.sublist List.filter_sublist

/-- On every canonical proper cut the active ledger accounts for exactly the
    cut's atoms, with no omitted or extra identity. -/
theorem TerminalComputedBCELAnchorNucleus.mem_activeRequestAtoms_iff_properCut
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed result.requestAtoms cut)
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    atom ∈ result.activeRequestAtoms cut ↔ atom ∈ cut := by
  rw [result.mem_activeRequestAtoms_iff cut atom]
  constructor
  · exact fun accounted => accounted.2
  · intro active
    refine ⟨?_, active⟩
    exact (terminalListSubsets_sublist result.requestAtoms cut proper.1).subset
      active

/-! ## One canonical side-tight basis family across all proper cuts -/

/-- Select the canonical full or quotient BN2 basis for one cut.  The same
    definition, atom identities, observer, projection, and ambient
    implementation type are used across the complete proper-cut family. -/
def TerminalComputedBCELAnchorNucleus.canonicalRequestBasis
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (mode : TerminalOptimumCoherenceMode)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalFourCornerImplementationBasis (inputs + gates) gates :=
  (problem.cutCarrier result.requestAtoms cut).canonicalImplementationBasis
    problem.observe mode

/-- The canonical selection function jointly realizes every proper cut with a
    checked side-tight coherent basis in either comparison mode. -/
theorem TerminalComputedBCELAnchorNucleus.canonicalRequestBasis_jointlySideTight
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (mode : TerminalOptimumCoherenceMode)
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed result.requestAtoms cut) :
    (result.canonicalRequestBasis mode cut).IsTightCoherent
      (problem.cutCarrier result.requestAtoms cut) problem.observe mode := by
  have localResult := result.properCutLocalConclusion cut proper
  unfold TerminalComputedBCELAnchorNucleus.canonicalRequestBasis
  apply TerminalFourCornerCarrier.canonicalImplementationBasis_isTightCoherent
  cases mode with
  | full => exact localResult.noRoutes.1
  | quotient => exact localResult.noRoutes.2

/-! ## Proof-bearing finite BN3 envelope and total classifier -/

/-- Exact finite BN3 boundary produced from one successful computed BCEL
    nucleus.  Every field refers to canonical definitions above rather than a
    caller-supplied request system, basis family, or incidence certificate. -/
structure TerminalComputedBN3RequestEnvelope
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) : Prop where
  requestAtomsNodup : result.requestAtoms.Nodup
  properCutsComplete : ∀ cut,
    cut ∈ allTerminalBCELProperCutSeeds result.requestAtoms ↔
      TerminalBCELProperCutSeed result.requestAtoms cut
  predicatesMonotone : ∀
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)),
    (∀ record, record ∈ left -> record ∈ right) ->
      TerminalBN3RequestPredicate atom left ->
        TerminalBN3RequestPredicate atom right
  predicatesStable : ∀
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)),
    (∀ record, record ∈ left ↔ record ∈ right) ->
      (TerminalBN3RequestPredicate atom left ↔
        TerminalBN3RequestPredicate atom right)
  minimalConsumersExact : ∀
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)),
    TerminalBN3RequestPredicate atom cut ↔
      ∀ record, record ∈ terminalBN3MinimalConsumer atom -> record ∈ cut
  activeAtomsExact : ∀ cut,
    TerminalBCELProperCutSeed result.requestAtoms cut ->
      ∀ atom, atom ∈ result.activeRequestAtoms cut ↔ atom ∈ cut
  activeAtomsNodup : ∀ cut, (result.activeRequestAtoms cut).Nodup
  jointSideTightRealizability : ∀ mode cut,
    TerminalBCELProperCutSeed result.requestAtoms cut ->
      (result.canonicalRequestBasis mode cut).IsTightCoherent
        (problem.cutCarrier result.requestAtoms cut) problem.observe mode

/-- Assemble the finite BN3 envelope from the computed successful nucleus;
    callers provide no additional request or realization certificate. -/
theorem TerminalComputedBCELAnchorNucleus.computedBN3RequestEnvelope
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) :
    TerminalComputedBN3RequestEnvelope result := by
  exact
    { requestAtomsNodup := result.requestAtoms_nodup
      properCutsComplete := mem_allTerminalBCELProperCutSeeds_iff
        result.requestAtoms
      predicatesMonotone := terminalBN3RequestPredicate_monotone
      predicatesStable := terminalBN3RequestPredicate_stable
      minimalConsumersExact := terminalBN3MinimalConsumer_exact
      activeAtomsExact := result.mem_activeRequestAtoms_iff_properCut
      activeAtomsNodup := result.activeRequestAtoms_nodup
      jointSideTightRealizability :=
        result.canonicalRequestBasis_jointlySideTight }

/-- Total finite BN3 outcome.  Existing proof-bearing BCEL failures are
    preserved exactly; only the successful branch constructs an envelope. -/
inductive TerminalBN3RequestEnvelopeOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  | insufficient (failure : TerminalBCELInsufficientNucleusFailure problem)
  | algebraFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELAnchorAlgebraFailure problem nucleus.anchors)
  | cutDefectFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutDefectFailure problem nucleus.anchors
        (problem.familyDefect nucleus.anchors))
  | cutRouteFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutRouteFailure problem nucleus.anchors)
  | ready (result : TerminalComputedBCELAnchorNucleus problem)
      (envelope : TerminalComputedBN3RequestEnvelope result)

/-- Run the existing complete finite BCEL classifier and construct the BN3
    envelope only on its proof-bearing successful branch. -/
def classifyTerminalBN3RequestEnvelope
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    TerminalBN3RequestEnvelopeOutcome problem :=
  match classifyTerminalBCELAnchorNucleus problem wholePositive with
  | .insufficient failure => .insufficient failure
  | .algebraFailure nucleus first failure =>
      .algebraFailure nucleus first failure
  | .cutDefectFailure nucleus first failure =>
      .cutDefectFailure nucleus first failure
  | .cutRouteFailure nucleus first failure =>
      .cutRouteFailure nucleus first failure
  | .ready result => .ready result result.computedBN3RequestEnvelope

/-- No sixth unclassified finite BN3 case exists. -/
theorem classifyTerminalBN3RequestEnvelope_exhaustive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    Nonempty (TerminalBN3RequestEnvelopeOutcome problem) :=
  ⟨classifyTerminalBN3RequestEnvelope problem wholePositive⟩

end DirectWire
end PNP
