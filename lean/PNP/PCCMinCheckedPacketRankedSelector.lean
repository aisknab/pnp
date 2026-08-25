/-
Copyright (c) 2026 PNP Labs.

Checked data-only Packet selector construction for the rank-ordered PCCOracle.

M191 accepted arbitrary selector rows and a proof-bearing realizer function.
This module derives every row from the canonical Packet-handle list and the
table-owned finite rank, and it converts a claim into a gain or typed blocker
only after the complete data-only table checker accepts.

The grouped family, rank assignment, claims, HResolve, BudgetResolve,
normalizer, blocker semantics, and complete-silence-to-ZeroSlack implication
remain supplied.  This module proves no encoded-size or runtime bound.
-/

import PNP.PCCMinRankOrderedOracle
import PNP.ResidualTerminalPacketTypedRealizerContract

namespace PNP
namespace DirectWire

/-! ## Complete data-only claim checking -/

/-- Validate the data-only claim at every canonical Packet handle.  Unlike the
earlier faithful-row checker, this is the exact executable boundary needed by
an oracle that may visit every rank row. -/
def TerminalPacketTypedRealizerTable.checkEveryClaim
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    (table.claim handle).check table.environment handle

/-- Complete-table acceptance is exactly claim validity at every canonical
Packet handle. -/
theorem TerminalPacketTypedRealizerTable.checkEveryClaim_eq_true_iff
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkEveryClaim = true ↔
      ∀ handle : family.PacketSelectorHandle,
        (table.claim handle).Valid table.environment handle := by
  constructor
  · intro accepted handle
    have checked := (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
    exact ((table.claim handle).check_eq_true_iff
      table.environment handle).mp checked
  · intro allValid
    apply List.all_eq_true.mpr
    intro handle _member
    exact ((table.claim handle).check_eq_true_iff
      table.environment handle).mpr (allValid handle)

/-- Convert one accepted data-only row to the proof-bearing M191 outcome.
Gain evidence is reconstructed from the checked unit-charge blueprint; the
blocked branch retains the exact stored typed reason. -/
def TerminalPacketTypedRealizerTable.checkedOutcome
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkEveryClaim = true)
    (handle : family.PacketSelectorHandle) :
    PCCMinRankedRealizerOutcome current
      (TerminalPacketTypedRealizerBot
        family.PacketSelectorHandle rankCount) :=
  match claimEquation : table.claim handle with
  | .gain blueprint =>
      .gain blueprint.next (by
        have claimValid :=
          (table.checkEveryClaim_eq_true_iff.mp accepted) handle
        have blueprintValid : blueprint.Valid := by
          simpa [TerminalPacketTypedRealizerClaim.Valid, claimEquation]
            using claimValid
        exact blueprintValid.chargeSurplusRealization.strictEquivalentGain)
  | .bot reason => .blocked reason

/-! ## Canonical exact-rank rows -/

/-- Derive one selector row by filtering the exhaustive canonical handle list
with the table-owned rank map. -/
def TerminalPacketTypedRealizerTable.selectorsAtRank
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount) : List family.PacketSelectorHandle :=
  family.packetSelectorHandles.filter fun handle =>
    decide (table.environment.rankOf handle = rank)

/-- Membership in a derived row is exactly equality with the table-owned
rank.  Canonical handle coverage is not a caller premise. -/
theorem TerminalPacketTypedRealizerTable.mem_selectorsAtRank_iff
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    handle ∈ table.selectorsAtRank rank ↔
      table.environment.rankOf handle = rank := by
  simp [TerminalPacketTypedRealizerTable.selectorsAtRank,
    family.mem_packetSelectorHandles]

/-- Every canonical Packet handle occurs in its exact assigned row. -/
theorem TerminalPacketTypedRealizerTable.mem_assignedSelectorRank
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    handle ∈ table.selectorsAtRank (table.environment.rankOf handle) :=
  (table.mem_selectorsAtRank_iff
    (table.environment.rankOf handle) handle).mpr rfl

/-! ## Checked Packet selector plan -/

/-- Data needed to construct one M191 selector plan.  The final field remains
the explicit mathematical ZeroSlack boundary; rows and realizer outcomes are
no longer caller-supplied proof-bearing functions. -/
structure PCCMinCheckedPacketSelectorData
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom Payload : Type) [DecidableEq Atom] where
  family : TerminalBN6GroupedFamily Atom Payload
  rankCount : Nat
  table : TerminalPacketTypedRealizerTable current family rankCount
  claimsAccepted : table.checkEveryClaim = true
  zeroSlackOfSilence :
    (∀ rank selector, selector ∈ table.selectorsAtRank rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          family.PacketSelectorHandle rankCount,
        table.checkedOutcome claimsAccepted selector = .blocked reason) →
      ZeroSlackResult current

/-- Construct the exact M191 selector interface from checked data. -/
def PCCMinCheckedPacketSelectorData.toRankedSelectorPlan
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketSelectorData current Atom Payload) :
    PCCMinRankedSelectorPlan current where
  rankCount := data.rankCount
  Selector := data.family.PacketSelectorHandle
  Bot := TerminalPacketTypedRealizerBot
    data.family.PacketSelectorHandle data.rankCount
  selectorsAt := data.table.selectorsAtRank
  realize := fun _rank selector =>
    data.table.checkedOutcome data.claimsAccepted selector
  zeroSlackOfSilence := data.zeroSlackOfSilence

/-- The constructed plan contains every canonical handle in its assigned
rank row. -/
theorem PCCMinCheckedPacketSelectorData.canonical_handle_covered
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketSelectorData current Atom Payload)
    (handle : data.family.PacketSelectorHandle) :
    handle ∈ data.toRankedSelectorPlan.selectorsAt
      (data.table.environment.rankOf handle) :=
  data.table.mem_assignedSelectorRank handle

/-! ## Rank-ordered oracle and total recursive builder -/

/-- HResolve and BudgetResolve retain their proof-bearing M191 contracts, but
the selector stage after both negative outcomes is now checked Packet data. -/
structure PCCMinCheckedPacketRankOrderedOraclePlan
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom Payload : Type) [DecidableEq Atom] where
  NoHereditary : Type
  NoBudget : Type
  hResolve : PCCMinResolverOutcome current NoHereditary
  budgetResolve : NoHereditary → PCCMinResolverOutcome current NoBudget
  selectorData : NoHereditary → NoBudget →
    PCCMinCheckedPacketSelectorData current Atom Payload

/-- Forget only the checked-data implementation detail and reuse the M191
rank-ordered control-flow theorem. -/
def PCCMinCheckedPacketRankOrderedOraclePlan.toRankOrderedOraclePlan
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinCheckedPacketRankOrderedOraclePlan
      current Atom Payload) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := plan.NoHereditary
  NoBudget := plan.NoBudget
  hResolve := plan.hResolve
  budgetResolve := plan.budgetResolve
  selectorPlan := fun noHereditary noBudget =>
    (plan.selectorData noHereditary noBudget).toRankedSelectorPlan

/-- A total builder supplies checked Packet data for every implementation
reached by the well-founded loop.  Its atom and payload carriers may depend on
the current implementation. -/
structure PCCMinCheckedPacketRankOrderedOracleBuilder where
  Atom : {inputs outputs : Nat} →
    Implementation inputs outputs → Type
  Payload : {inputs outputs : Nat} →
    Implementation inputs outputs → Type
  atomDecidableEq : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      DecidableEq (Atom current)
  build : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      @PCCMinCheckedPacketRankOrderedOraclePlan inputs outputs current
        (Atom current) (Payload current) (atomDecidableEq current)

/-- Convert the checked data-backed builder to the M191 total builder. -/
def PCCMinCheckedPacketRankOrderedOracleBuilder.toRankOrderedOracleBuilder
    (builder : PCCMinCheckedPacketRankOrderedOracleBuilder) :
    PCCMinRankOrderedOracleBuilder where
  build := fun current =>
    letI : DecidableEq (builder.Atom current) :=
      builder.atomDecidableEq current
    (builder.build current).toRankOrderedOraclePlan

/-- Run normalization followed by checked Packet-backed rank-ordered oracle
construction and the existing well-founded exact loop. -/
def runPCCMinNormalizeCheckedPacketRankOrderedOracleLoop
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketRankOrderedOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  runPCCMinNormalizeRankOrderedOracleLoop normalizer
    builder.toRankOrderedOracleBuilder current

/-- Public M192 endpoint: every rank row and realizer outcome consumed by the
selector scan comes from an exhaustive checker-accepted data-only Packet
table.  Family/table construction and the ZeroSlack closure remain supplied,
so this theorem makes no unconditional or polynomial-runtime claim. -/
theorem pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketRankOrderedOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinNormalizeCheckedPacketRankOrderedOracleLoop
        normalizer builder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current := by
  exact pccmin_normalize_rank_ordered_oracle_loop_checked_complete
    normalizer builder.toRankOrderedOracleBuilder current

end DirectWire
end PNP
