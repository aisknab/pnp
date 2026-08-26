/-
Copyright (c) 2026 PNP Labs.

Canonical sparse constant-cut basis at the checked BN6/BCEL/HB PCCMin
boundary.

M198 identifies canonical grouped activation exactly with the direct raw
positive-cell crossing ledger, but its inherited M195 classifier still scans
every proper carrier subset.  The V53 basis classifier replaces that scan with
the exact two-anchor, three-singleton, or four-plus full-span basis.  An
accepted basis constructs the existing M194 constant-activation input; a
rejected basis remains one typed structural route.

The terminal problem, raw positive cells and payloads, checked realizer table,
claims, ranks, dependency table, route-clear result, and HB closure remain
supplied.  A basis route is not a verified gain or globally decreasing
transition.  No complete polynomial bound, unconditional ZeroSlack, PCCMin,
CNFSAT-in-P, root theorem, or P = NP result is claimed.
-/

import PNP.PCCMinCheckedPacketBN6BCELCanonicalCutLedger
import PNP.ResidualTerminalV53CanonicalConstantCutBasis

namespace PNP
namespace DirectWire

/-! ## Exact raw-ledger reflection -/

/-- Every hypergraph cut queried by the canonical basis is exactly the direct
    crossing-mass sum of the supplied raw positive cells. -/
theorem PCCMinCheckedPacketBN6BCELPositiveCells.groupedHypergraph_cutWeight_eq_raw
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount)
    (cut : List (TerminalPrimitiveRecord
      inputs gates outputs profileWidth)) :
    positiveCells.groupedCells.family.hypergraph.cutWeight cut =
      terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors positiveCells.cells cut := by
  calc
    positiveCells.groupedCells.family.hypergraph.cutWeight cut =
        positiveCells.groupedCells.family.activationWeight cut :=
      positiveCells.groupedCells.family.cutWeight_eq_activationWeight cut
    _ = terminalBN6PositiveCellsActivationWeight
          terminalReady.result.nucleus.anchors positiveCells.cells cut :=
      positiveCells.groupedFamily_activationWeight_eq_raw cut

/-! ## Accepted basis into constant activation -/

/-- A complete V53 proper-cut equation is exactly the activation equation
    required by the grouped BN6 family. -/
theorem TerminalBN6GroupedFamily.constantActivation_of_hypergraphConstantProperCuts
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (constant : family.hypergraph.ConstantProperCuts) :
    family.ConstantActivation := by
  intro cut included nonempty proper
  rw [← family.cutWeight_eq_activationWeight cut]
  exact constant cut ⟨included, nonempty, proper⟩

/-- Install an accepted canonical basis in M194's exact checked Packet/HB
    boundary.  Positive slack is used only to match the inherited interface;
    the constant equation itself comes from the basis. -/
def PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.toBN6HBZeroSlackDataOfCanonicalCutBasis
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount)
    (basis : data.positiveCells.groupedCells.family.hypergraph.CanonicalConstantCutBasis) :
    PCCMinCheckedPacketBN6HBZeroSlackData candidate.toImplementation
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) rankCount where
  family := data.positiveCells.groupedCells.family
  rawTable := data.rawTable
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  routesClear := data.routesClear
  carrierAtLeastTwo := by
    change 2 ≤ data.positiveCells.groupedCells.family.carrier.length
    rw [data.positiveCells.groupedFamily_carrier]
    exact data.terminalReady.anchorSizeAtLeastTwo
  constantActivationOfPositiveSlack := fun _positive =>
    data.positiveCells.groupedCells.family.constantActivation_of_hypergraphConstantProperCuts
      ((terminalV53_canonicalConstantCutBasis_iff_constantProperCuts
        data.positiveCells.groupedCells.family.hypergraph (by
          change 2 ≤ data.positiveCells.groupedCells.family.carrier.length
          rw [data.positiveCells.groupedFamily_carrier]
          exact data.terminalReady.anchorSizeAtLeastTwo)).1 basis)

/-- The accepted basis supplies the exact family constant-activation equation
    independently of residual slack. -/
theorem PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.constantActivation_of_canonicalCutBasis
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount)
    (basis : data.positiveCells.groupedCells.family.hypergraph.CanonicalConstantCutBasis) :
    data.positiveCells.groupedCells.family.ConstantActivation := by
  apply data.positiveCells.groupedCells.family.constantActivation_of_hypergraphConstantProperCuts
  exact (terminalV53_canonicalConstantCutBasis_iff_constantProperCuts
    data.positiveCells.groupedCells.family.hypergraph (by
      change 2 ≤ data.positiveCells.groupedCells.family.carrier.length
      rw [data.positiveCells.groupedFamily_carrier]
      exact data.terminalReady.anchorSizeAtLeastTwo)).1 basis

/-! ## Typed route or conditional ZeroSlack -/

/-- Total checked result of the canonical basis boundary. -/
inductive PCCMinCheckedPacketBN6BCELCanonicalCutBasisRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | basisRoute
      (route : TerminalV53CanonicalConstantCutBasisRoute
        data.positiveCells.groupedCells.family.hypergraph)

/-- Run the sparse basis classifier.  Only its proved coherent branch may
    enter the checked Packet/HB ZeroSlack contradiction. -/
def PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.canonicalCutBasisRouteOrZeroSlackOfSilence
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
        data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
            data.claimsAccepted selector = .blocked reason) :
    PCCMinCheckedPacketBN6BCELCanonicalCutBasisRouteOrZeroSlack data :=
  match classifyTerminalV53CanonicalConstantCutBasis
      data.positiveCells.groupedCells.family.hypergraph with
  | .coherent basis =>
      .zeroSlack
        ((data.toBN6HBZeroSlackDataOfCanonicalCutBasis basis
          ).zeroSlackOfSilence silence)
  | .routed route => .basisRoute route

/-- Public M199 endpoint: complete exact-rank selector silence yields genuine
    zero residual slack or one inhabited typed sparse-basis obstruction.  The
    classifier does not enumerate the carrier powerset. -/
theorem pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
        data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
            data.claimsAccepted selector = .blocked reason) :
    residualSlack candidate.toImplementation = 0 ∨
      Nonempty (TerminalV53CanonicalConstantCutBasisRoute
        data.positiveCells.groupedCells.family.hypergraph) := by
  exact match data.canonicalCutBasisRouteOrZeroSlackOfSilence silence with
    | .zeroSlack result => Or.inl result.sound
    | .basisRoute route => Or.inr ⟨route⟩

end DirectWire
end PNP
