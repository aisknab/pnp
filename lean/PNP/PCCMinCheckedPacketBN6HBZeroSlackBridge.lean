/-
Copyright (c) 2026 PNP Labs.

BN6 computed-faithfulness closure for the checked Packet/HB PCCMin boundary.

M193 derives the final rank-parametric ZeroSlack contradiction from checked
Packet silence and checked HB closure, but still accepts a direct function
from positive residual slack to a faithful canonical selector.  This module
moves that remaining premise to the manuscript's earlier BCEL boundary.
Positive slack supplies constant activation for an arbitrary finite grouped
family; the general BN6 theorem constructs the positive Packet conclusion;
and the route-clear computed-faithfulness table constructs the faithful
selector consumed by M193.

The grouped family, carrier lower bound, constant-activation bridge, payloads,
rank assignment, route-clear check, realizer claims, dependency table, HB
activity semantics, HResolve, BudgetResolve, and normalizer remain supplied.
This module therefore does not prove manuscript-wide SaturatePositive or
BCELReady, unconditional ZeroSlack, a polynomial PCCMin construction, CNFSAT
in P, the eligible root theorem, or P = NP.
-/

import PNP.PCCMinCheckedPacketHBZeroSlackBridge
import PNP.ResidualTerminalPacketSelectorFaithfulnessTable

namespace PNP
namespace DirectWire

/-! ## BN6-derived positive-slack contradiction data -/

/-- Exact M194 terminal data.  The raw table supplies ranks, activity bits,
and checked claims, while its faithfulness component is replaced by the
canonical payload computation before it reaches the M193 contradiction. -/
structure PCCMinCheckedPacketBN6HBZeroSlackData
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom : Type) [DecidableEq Atom]
    (rankCount : Nat) where
  family : TerminalBN6GroupedFamily Atom
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
  rawTable : TerminalPacketTypedRealizerTable current family rankCount
  claimsAccepted :
    rawTable.withComputedPacketSelectorFaithfulness.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    rawTable.withComputedPacketSelectorFaithfulness.environment = true
  routesClear : family.checkPacketSelectorRoutesClear
    rawTable.environment.rankOf = true
  carrierAtLeastTwo : 2 ≤ family.carrier.length
  constantActivationOfPositiveSlack : 0 < residualSlack current →
    family.ConstantActivation

/-- Positive residual slack reaches the general, arbitrary-family BN6 Packet
classification through the still-explicit constant-activation boundary. -/
theorem PCCMinCheckedPacketBN6HBZeroSlackData.positivePacketOfPositiveSlack
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (positive : 0 < residualSlack current) :
    TerminalBN6PacketConclusion data.family :=
  terminalBN6_hypergraph_packet data.family data.carrierAtLeastTwo
    (data.constantActivationOfPositiveSlack positive)

/-- The positive Packet and the executable route-clear equation construct a
faithful selector in the canonicalized table.  No arbitrary faithfulness
callback or independent table-binding premise is accepted. -/
theorem PCCMinCheckedPacketBN6HBZeroSlackData.faithfulOfPositiveSlack
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (positive : 0 < residualSlack current) :
    ∃ handle : data.family.PacketSelectorHandle,
      data.rawTable.withComputedPacketSelectorFaithfulness.environment.faithful
        handle = true :=
  (data.positivePacketOfPositiveSlack positive
    ).existsFaithfulHandle_of_computedTable data.rawTable data.routesClear

/-- Build M193's exact checked Packet/HB boundary after deriving its only
positive-slack field through BN6 and computed payload faithfulness. -/
def PCCMinCheckedPacketBN6HBZeroSlackData.toCheckedPacketHBZeroSlackData
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount) :
    PCCMinCheckedPacketHBZeroSlackData current Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount) where
  family := data.family
  rankCount := rankCount
  table := data.rawTable.withComputedPacketSelectorFaithfulness
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  faithfulOfPositiveSlack := data.faithfulOfPositiveSlack

/-- Complete rank-row silence now forces ZeroSlack through constant
activation, general BN6, computed selector faithfulness, and checked HB. -/
def PCCMinCheckedPacketBN6HBZeroSlackData.zeroSlackOfSilence
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle rankCount,
          data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
              data.claimsAccepted selector = .blocked reason) :
    ZeroSlackResult current :=
  data.toCheckedPacketHBZeroSlackData.zeroSlackOfSilence silence

/-- The constructed result exposes the exact zero-slack equation. -/
theorem PCCMinCheckedPacketBN6HBZeroSlackData.zeroSlackOfSilence_sound
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle rankCount,
          data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
              data.claimsAccepted selector = .blocked reason) :
    residualSlack current = 0 :=
  (data.zeroSlackOfSilence silence).sound

/-! ## Rank-ordered oracle and total recursive builder -/

/-- HResolve and BudgetResolve remain explicit.  The terminal branch carries
only the earlier constant-activation bridge, not a faithful-selector oracle. -/
structure PCCMinCheckedPacketBN6HBZeroSlackOraclePlan
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom : Type) [DecidableEq Atom]
    (rankCount : Nat) where
  NoHereditary : Type
  NoBudget : Type
  hResolve : PCCMinResolverOutcome current NoHereditary
  budgetResolve : NoHereditary → PCCMinResolverOutcome current NoBudget
  selectorData : NoHereditary → NoBudget →
    PCCMinCheckedPacketBN6HBZeroSlackData current Atom rankCount

/-- Reuse M193 after constructing its positive-slack selector through BN6. -/
def PCCMinCheckedPacketBN6HBZeroSlackOraclePlan.toCheckedPacketHBZeroSlackOraclePlan
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinCheckedPacketBN6HBZeroSlackOraclePlan
      current Atom rankCount) :
    PCCMinCheckedPacketHBZeroSlackOraclePlan current Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount) where
  NoHereditary := plan.NoHereditary
  NoBudget := plan.NoBudget
  hResolve := plan.hResolve
  budgetResolve := plan.budgetResolve
  selectorData := fun noHereditary noBudget =>
    (plan.selectorData noHereditary noBudget
      ).toCheckedPacketHBZeroSlackData

/-- A total builder supplies the BN6/HB bridge for every implementation
reached by the existing well-founded loop. -/
structure PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder where
  Atom : {inputs outputs : Nat} →
    Implementation inputs outputs → Type
  atomDecidableEq : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      DecidableEq (Atom current)
  rankCount : {inputs outputs : Nat} →
    Implementation inputs outputs → Nat
  build : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      @PCCMinCheckedPacketBN6HBZeroSlackOraclePlan inputs outputs current
        (Atom current) (atomDecidableEq current) (rankCount current)

/-- Convert the BN6/HB builder to M193's total builder without exposing an
independent payload or faithfulness function. -/
def PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder.toCheckedPacketHBZeroSlackOracleBuilder
    (builder : PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder) :
    PCCMinCheckedPacketHBZeroSlackOracleBuilder where
  Atom := builder.Atom
  Payload := fun current =>
    TerminalPacketSelectorFaithfulnessPayload (builder.rankCount current)
  atomDecidableEq := builder.atomDecidableEq
  build := fun current =>
    letI : DecidableEq (builder.Atom current) :=
      builder.atomDecidableEq current
    (builder.build current).toCheckedPacketHBZeroSlackOraclePlan

/-- Run normalization followed by the BN6-derived checked Packet/HB oracle
and the existing well-founded exact loop. -/
def runPCCMinNormalizeCheckedPacketBN6HBZeroSlackLoop
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  runPCCMinNormalizeCheckedPacketHBZeroSlackLoop normalizer
    builder.toCheckedPacketHBZeroSlackOracleBuilder current

/-- Public M194 endpoint: positive slack reaches a canonical faithful selector
through the supplied constant-activation boundary, general BN6, and executable
route-clear payload checks.  Constant activation and the remaining terminal
construction and runtime obligations are deliberately still open. -/
theorem pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinNormalizeCheckedPacketBN6HBZeroSlackLoop
        normalizer builder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations ≤ residualSlack current := by
  exact pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete
    normalizer builder.toCheckedPacketHBZeroSlackOracleBuilder current

end DirectWire
end PNP
