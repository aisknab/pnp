/-
Copyright (c) 2026 PNP Labs.

Checked BCEL activation routing for the BN6/HB PCCMin boundary.

M194 still accepts a function from positive residual slack to constant
activation on a supplied grouped BN6 family. This module binds that family to
the primitive-record carrier of an existing checked finite BCEL-ready nucleus
and classifies the complete finite linkage. A mismatch is retained as an exact
carrier, cut-value, or proper-cut activation route. Only the coherent branch
derives constant activation and enters M194's conditional ZeroSlack proof.

The terminal problem, checked ready certificate, grouped family, payloads,
table, claims, ranks, route-clear equation, dependency data, and HB closure
remain supplied. The mismatch routes are not compiled to gains or decreasing
global routes, the finite cut scan may be exponential, and no unconditional
ZeroSlack, polynomial PCCMin, CNFSAT-in-P, root theorem, or P = NP result is
claimed.
-/

import PNP.PCCMinCheckedPacketBN6HBZeroSlackBridge
import PNP.ResidualTerminalFiniteBCELReady

namespace PNP
namespace DirectWire

/-! ## Same-candidate BCEL and Packet data -/

/-- M195 data before deciding the BCEL/Packet activation boundary. Packet
anchors are the exact terminal primitive-record type, so the carrier comparison
does not trust an independent anchor map or bijection. -/
structure PCCMinCheckedPacketBN6BCELHBData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat) where
  problem : TerminalFiniteSaturatePositiveProblem candidate model
  terminalReady : TerminalFiniteBCELReadyCertificate problem
  family : TerminalBN6GroupedFamily
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
  rawTable : TerminalPacketTypedRealizerTable
    candidate.toImplementation family rankCount
  claimsAccepted :
    rawTable.withComputedPacketSelectorFaithfulness.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    rawTable.withComputedPacketSelectorFaithfulness.environment = true
  routesClear : family.checkPacketSelectorRoutesClear
    rawTable.environment.rankOf = true

/-- The canonical BCEL carrier computed by the checked ready branch. -/
def PCCMinCheckedPacketBN6BCELHBData.bcelCarrier
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  data.terminalReady.result.nucleus.anchors

/-- The positive projection defect of the computed BCEL nucleus. -/
def PCCMinCheckedPacketBN6BCELHBData.bcelDefect
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) : Nat :=
  data.problem.anchorProblem.toProblem.familyDefect data.bcelCarrier

/-! ## Complete finite activation-linkage classifier -/

/-- Exact successful BCEL/Packet linkage. Every governed nonempty proper
Packet cut has the computed BCEL nucleus defect as its activation weight. -/
structure PCCMinCheckedPacketBN6BCELActivationCoherent
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) : Prop where
  carrierBinding : data.family.carrier = data.bcelCarrier
  cutValueBinding : data.family.cutValue = data.bcelDefect
  activationBinding : ∀ cut, cut.Sublist data.family.carrier → cut ≠ [] →
    cut ≠ data.family.carrier →
      data.family.activationWeight cut = data.bcelDefect

/-- Exact first-priority obstruction when the finite BCEL and Packet objects
do not form the constant-activation boundary required by BN6. -/
inductive PCCMinCheckedPacketBN6BCELActivationRoute
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) where
  | carrierMismatch
      (mismatch : data.family.carrier ≠ data.bcelCarrier)
  | cutValueMismatch
      (carrierBinding : data.family.carrier = data.bcelCarrier)
      (mismatch : data.family.cutValue ≠ data.bcelDefect)
  | activationMismatch
      (carrierBinding : data.family.carrier = data.bcelCarrier)
      (cutValueBinding : data.family.cutValue = data.bcelDefect)
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist data.family.carrier)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.family.carrier)
      (mismatch : data.family.activationWeight cut ≠ data.bcelDefect)

/-- Total result of the finite BCEL/Packet comparison. -/
inductive PCCMinCheckedPacketBN6BCELActivationClassification
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) where
  | coherent
      (evidence : PCCMinCheckedPacketBN6BCELActivationCoherent data)
  | routed
      (route : PCCMinCheckedPacketBN6BCELActivationRoute data)

/-- Every canonical nonempty proper Packet cut, in deterministic subset order. -/
private def pccminCheckedPacketBN6BCELProperCuts
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) :
    List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  (terminalListSubsets data.family.carrier).filter fun cut =>
    decide (cut ≠ [] ∧ cut ≠ data.family.carrier)

private theorem mem_pccminCheckedPacketBN6BCELProperCuts_iff
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    cut ∈ pccminCheckedPacketBN6BCELProperCuts data ↔
      cut.Sublist data.family.carrier ∧ cut ≠ [] ∧
        cut ≠ data.family.carrier := by
  unfold pccminCheckedPacketBN6BCELProperCuts
  constructor
  · intro member
    have parts := List.mem_filter.mp member
    have proper : cut ≠ [] ∧ cut ≠ data.family.carrier :=
      of_decide_eq_true parts.2
    exact ⟨terminalListSubsets_sublist data.family.carrier cut parts.1,
      proper.1, proper.2⟩
  · intro proper
    exact List.mem_filter.mpr
      ⟨terminalV53_sublist_mem_terminalListSubsets proper.1,
        decide_eq_true ⟨proper.2.1, proper.2.2⟩⟩

/-- The first proper Packet cut whose activation weight misses the computed
BCEL defect. -/
private def firstPCCMinCheckedPacketBN6BCELActivationMismatch?
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) :
    Option (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  (pccminCheckedPacketBN6BCELProperCuts data).find? fun cut =>
    decide (data.family.activationWeight cut ≠ data.bcelDefect)

private theorem firstPCCMinCheckedPacketBN6BCELActivationMismatch?_sound
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (found : firstPCCMinCheckedPacketBN6BCELActivationMismatch? data =
      some cut) :
    (cut.Sublist data.family.carrier ∧ cut ≠ [] ∧
      cut ≠ data.family.carrier) ∧
      data.family.activationWeight cut ≠ data.bcelDefect := by
  have member : cut ∈ pccminCheckedPacketBN6BCELProperCuts data :=
    List.mem_of_find?_eq_some found
  have expanded :
      (pccminCheckedPacketBN6BCELProperCuts data).find? (fun candidateCut =>
        decide (data.family.activationWeight candidateCut ≠
          data.bcelDefect)) = some cut := by
    simpa only [firstPCCMinCheckedPacketBN6BCELActivationMismatch?]
      using found
  have mismatchChecked : decide
      (data.family.activationWeight cut ≠ data.bcelDefect) = true :=
    @List.find?_some
      (List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (fun candidateCut => decide
        (data.family.activationWeight candidateCut ≠ data.bcelDefect))
      cut (pccminCheckedPacketBN6BCELProperCuts data) expanded
  exact ⟨
    (mem_pccminCheckedPacketBN6BCELProperCuts_iff data cut).1 member,
    of_decide_eq_true mismatchChecked⟩

private theorem firstPCCMinCheckedPacketBN6BCELActivationMismatch?_eq_none_all
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount)
    (noneFound : firstPCCMinCheckedPacketBN6BCELActivationMismatch? data =
      none) :
    ∀ cut, cut.Sublist data.family.carrier → cut ≠ [] →
      cut ≠ data.family.carrier →
        data.family.activationWeight cut = data.bcelDefect := by
  intro cut included nonempty proper
  by_cases activationMatches :
      data.family.activationWeight cut = data.bcelDefect
  · exact activationMatches
  · have member : cut ∈ pccminCheckedPacketBN6BCELProperCuts data :=
      (mem_pccminCheckedPacketBN6BCELProperCuts_iff data cut).2
        ⟨included, nonempty, proper⟩
    have mismatchChecked : decide
        (data.family.activationWeight cut ≠ data.bcelDefect) = true :=
      decide_eq_true activationMatches
    have someMismatch :
        (firstPCCMinCheckedPacketBN6BCELActivationMismatch?
          data).isSome = true :=
      (List.find?_isSome).mpr ⟨cut, member, mismatchChecked⟩
    rw [noneFound] at someMismatch
    exact Bool.noConfusion someMismatch

/-- Compare the exact carrier, declared cut value, and every canonical proper
cut. No caller result or coherence proof is accepted. -/
def classifyPCCMinCheckedPacketBN6BCELActivation
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) :
    PCCMinCheckedPacketBN6BCELActivationClassification data := by
  by_cases carrierMatches : data.family.carrier = data.bcelCarrier
  · by_cases cutValueMatches : data.family.cutValue = data.bcelDefect
    · match found :
        firstPCCMinCheckedPacketBN6BCELActivationMismatch? data with
      | none =>
          exact .coherent
            { carrierBinding := carrierMatches
              cutValueBinding := cutValueMatches
              activationBinding :=
                firstPCCMinCheckedPacketBN6BCELActivationMismatch?_eq_none_all
                  data found }
      | some cut =>
          have sound :=
            firstPCCMinCheckedPacketBN6BCELActivationMismatch?_sound
              data cut found
          exact .routed (.activationMismatch carrierMatches cutValueMatches
            cut sound.1.1 sound.1.2.1 sound.1.2.2 sound.2)
    · exact .routed (.cutValueMismatch carrierMatches cutValueMatches)
  · exact .routed (.carrierMismatch carrierMatches)

/-- Every arbitrary finite input has exactly one proof-bearing classifier
result at this boundary. -/
theorem classifyPCCMinCheckedPacketBN6BCELActivation_exhaustive
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) :
    Nonempty (PCCMinCheckedPacketBN6BCELActivationClassification data) :=
  ⟨classifyPCCMinCheckedPacketBN6BCELActivation data⟩

/-! ## Coherent branch into M194 -/

/-- The coherent carrier inherits the checked BCEL nucleus lower bound. -/
theorem PCCMinCheckedPacketBN6BCELActivationCoherent.carrierAtLeastTwo
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount}
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    2 ≤ data.family.carrier.length := by
  rw [coherent.carrierBinding]
  exact data.terminalReady.anchorSizeAtLeastTwo

/-- Complete finite activation agreement is exactly the BN6 constant-activation
premise, now derived without a positive-slack callback. -/
theorem PCCMinCheckedPacketBN6BCELActivationCoherent.constantActivation
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount}
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    data.family.ConstantActivation := by
  intro cut included nonempty proper
  exact (coherent.activationBinding cut included nonempty proper).trans
    coherent.cutValueBinding.symm

/-- On every computed BCEL proper cut, coherent Packet activation equals the
machine-checked projection-excess equation of the ready nucleus. -/
theorem PCCMinCheckedPacketBN6BCELActivationCoherent.activation_eq_projectionExcess
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount}
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed data.bcelCarrier cut) :
    Int.ofNat (data.family.activationWeight cut) =
      ((data.problem.anchorProblem.toProblem.cutCarrier
        data.terminalReady.result.nucleus.anchors cut).optimizationCorners
          data.problem.anchorProblem.toProblem.observe).projectionExcess := by
  have includedBCEL : cut.Sublist data.bcelCarrier :=
    terminalListSubsets_sublist data.bcelCarrier cut proper.1
  have includedFamily : cut.Sublist data.family.carrier := by
    rw [coherent.carrierBinding]
    exact includedBCEL
  have notFull : cut ≠ data.family.carrier := by
    intro equal
    have equalLength : cut.length = data.bcelCarrier.length := by
      calc
        cut.length = data.family.carrier.length := congrArg List.length equal
        _ = data.bcelCarrier.length :=
          congrArg List.length coherent.carrierBinding
    exact (Nat.ne_of_lt proper.2.2) equalLength
  have activation := coherent.activationBinding cut includedFamily
    proper.2.1 notFull
  calc
    Int.ofNat (data.family.activationWeight cut) =
        Int.ofNat data.bcelDefect := congrArg Int.ofNat activation
    _ = ((data.problem.anchorProblem.toProblem.cutCarrier
          data.terminalReady.result.nucleus.anchors cut).optimizationCorners
            data.problem.anchorProblem.toProblem.observe).projectionExcess := by
      simpa only [PCCMinCheckedPacketBN6BCELHBData.bcelDefect,
        PCCMinCheckedPacketBN6BCELHBData.bcelCarrier]
        using (data.terminalReady.properCutConstantEquation cut proper).symm

/-- Build M194's exact checked Packet/HB data after deriving both of its BCEL
fields from the coherent classifier branch. -/
def PCCMinCheckedPacketBN6BCELActivationCoherent.toBN6HBZeroSlackData
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount}
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    PCCMinCheckedPacketBN6HBZeroSlackData candidate.toImplementation
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) rankCount where
  family := data.family
  rawTable := data.rawTable
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  routesClear := data.routesClear
  carrierAtLeastTwo := coherent.carrierAtLeastTwo
  constantActivationOfPositiveSlack := fun _positive =>
    coherent.constantActivation

/-! ## Route-or-ZeroSlack result -/

/-- Total terminal result after complete selector silence. An activation
linkage failure remains a typed route rather than being mislabeled ZeroSlack. -/
inductive PCCMinCheckedPacketBN6BCELRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | activationRoute
      (route : PCCMinCheckedPacketBN6BCELActivationRoute data)

/-- Run the total activation classifier. Only its coherent branch is allowed
to reuse M194's checked-HB ZeroSlack contradiction. -/
def PCCMinCheckedPacketBN6BCELHBData.routeOrZeroSlackOfSilence
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle rankCount,
          data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
              data.claimsAccepted selector = .blocked reason) :
    PCCMinCheckedPacketBN6BCELRouteOrZeroSlack data :=
  match classifyPCCMinCheckedPacketBN6BCELActivation data with
  | .coherent coherent =>
      .zeroSlack (coherent.toBN6HBZeroSlackData.zeroSlackOfSilence silence)
  | .routed route => .activationRoute route

/-- Public M195 endpoint: exact-rank selector silence yields either genuine
zero residual slack or the first exact BCEL/Packet activation-linkage route.
No opaque constant-activation callback or supplied classifier result occurs in
the theorem surface. -/
theorem pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle rankCount,
          data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
              data.claimsAccepted selector = .blocked reason) :
    residualSlack candidate.toImplementation = 0 ∨
      data.family.carrier ≠ data.bcelCarrier ∨
      (data.family.carrier = data.bcelCarrier ∧
        data.family.cutValue ≠ data.bcelDefect) ∨
      ∃ cut,
        data.family.carrier = data.bcelCarrier ∧
        data.family.cutValue = data.bcelDefect ∧
        cut.Sublist data.family.carrier ∧ cut ≠ [] ∧
        cut ≠ data.family.carrier ∧
        data.family.activationWeight cut ≠ data.bcelDefect := by
  exact match data.routeOrZeroSlackOfSilence silence with
    | .zeroSlack result => Or.inl result.sound
    | .activationRoute route => by
        right
        cases route with
        | carrierMismatch mismatch => exact Or.inl mismatch
        | cutValueMismatch carrierBinding mismatch =>
            exact Or.inr (Or.inl ⟨carrierBinding, mismatch⟩)
        | activationMismatch carrierBinding cutValueBinding cut included
            nonempty proper mismatch =>
            exact Or.inr (Or.inr ⟨cut, carrierBinding, cutValueBinding,
              included, nonempty, proper, mismatch⟩)

end DirectWire
end PNP
