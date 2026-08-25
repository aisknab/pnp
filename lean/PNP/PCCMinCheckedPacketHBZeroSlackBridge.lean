/-
Copyright (c) 2026 PNP Labs.

Checked HB closure for the Packet-backed rank-ordered PCCOracle.

M192 still accepted an opaque function that turned complete selector silence
into `ZeroSlackResult`.  This module reconstructs the final contradiction from
the pinned manuscript's Sections 15 and 16.  Complete rank-row silence is
converted to the executable selector-silence check; checked HB no-outcome
closure then proves that every canonical selector is nonfaithful.  The sole
remaining mathematical bridge states exactly that positive residual slack
would yield a faithful canonical selector.

The grouped family, rank assignment, claims, dependency table, HB activity
semantics, positive-slack-to-faithful-selector bridge, HResolve, BudgetResolve,
and normalizer remain supplied.  This module therefore does not prove
unconditional ZeroSlack, construct PCCMin from an encoded input, establish a
polynomial bound, put SAT in P, create the eligible root theorem, or prove
P = NP.
-/

import PNP.PCCMinCheckedPacketRankedSelector
import PNP.ResidualTerminalHBExecutableSelectorSilenceInduction

namespace PNP
namespace DirectWire

/-! ## Complete-table silence -/

/-- Checking every canonical claim is stronger than the earlier faithful-row
checker used by the executable selector-silence induction. -/
theorem TerminalPacketTypedRealizerTable.checkFaithful_of_checkEveryClaim
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkEveryClaim = true) :
    table.checkFaithful = true := by
  unfold TerminalPacketTypedRealizerTable.checkFaithful
    checkTerminalPacketFaithfulRealizerClaims
  apply List.all_eq_true.mpr
  intro handle handleMember
  have allChecked : family.packetSelectorHandles.all (fun candidate =>
      (table.claim candidate).check table.environment candidate) = true := by
    simpa only [TerminalPacketTypedRealizerTable.checkEveryClaim] using accepted
  have rowChecked :
      (table.claim handle).check table.environment handle = true :=
    (List.all_eq_true.mp allChecked) handle handleMember
  cases table.environment.faithful handle <;>
    simp [rowChecked]

/-- A checked M192 outcome can be blocked only when the stored data-only claim
is one of the three typed bottom constructors. -/
theorem TerminalPacketTypedRealizerTable.claim_eq_bot_of_checkedOutcome_blocked
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkEveryClaim = true)
    (handle : family.PacketSelectorHandle)
    (reason : TerminalPacketTypedRealizerBot
      family.PacketSelectorHandle rankCount)
    (blocked : table.checkedOutcome accepted handle = .blocked reason) :
    ∃ storedReason : TerminalPacketTypedRealizerBot
        family.PacketSelectorHandle rankCount,
      table.claim handle = .bot storedReason := by
  unfold TerminalPacketTypedRealizerTable.checkedOutcome at blocked
  split at blocked
  · cases blocked
  · rename_i storedReason claimEquation
    exact ⟨storedReason, claimEquation⟩

/-- Silence in every exact rank row is exactly strong enough to activate the
existing executable all-handle selector-silence induction. -/
theorem TerminalPacketTypedRealizerTable.checkSelectorSilent_of_rankedOutcomeSilence
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkEveryClaim = true)
    (silence : ∀ rank selector, selector ∈ table.selectorsAtRank rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          family.PacketSelectorHandle rankCount,
        table.checkedOutcome accepted selector = .blocked reason) :
    table.checkSelectorSilent = true := by
  apply table.checkSelectorSilent_eq_true_iff.mpr
  refine ⟨table.checkFaithful_of_checkEveryClaim accepted, ?_⟩
  intro handle
  obtain ⟨reason, blocked⟩ := silence
    (table.environment.rankOf handle) handle
    (table.mem_assignedSelectorRank handle)
  exact table.claim_eq_bot_of_checkedOutcome_blocked
    accepted handle reason blocked

/-! ## Positive-slack contradiction data -/

/-- Exact remaining input to the final rank-parametric ZeroSlack
contradiction.  Unlike M192's opaque closure callback, each field is a named
checker result or the single load-bearing positive-slack bridge from the
manuscript. -/
structure PCCMinCheckedPacketHBZeroSlackData
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom Payload : Type) [DecidableEq Atom] where
  family : TerminalBN6GroupedFamily Atom Payload
  rankCount : Nat
  table : TerminalPacketTypedRealizerTable current family rankCount
  claimsAccepted : table.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    table.environment = true
  faithfulOfPositiveSlack : 0 < residualSlack current →
    ∃ handle : family.PacketSelectorHandle,
      table.environment.faithful handle = true

/-- Exact-rank oracle silence yields the executable selector-silence checker
equation stored by the manuscript boundary. -/
theorem PCCMinCheckedPacketHBZeroSlackData.selectorSilenceAccepted
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketHBZeroSlackData current Atom Payload)
    (silence : ∀ rank selector,
      selector ∈ data.table.selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle data.rankCount,
          data.table.checkedOutcome data.claimsAccepted selector =
            .blocked reason) :
    data.table.checkSelectorSilent = true :=
  data.table.checkSelectorSilent_of_rankedOutcomeSilence
    data.claimsAccepted silence

/-- Selector silence and accepted HB closure exclude every faithful canonical
handle, including every handle that the positive-slack bridge could return. -/
theorem PCCMinCheckedPacketHBZeroSlackData.noFaithfulOfSilence
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketHBZeroSlackData current Atom Payload)
    (silence : ∀ rank selector,
      selector ∈ data.table.selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle data.rankCount,
          data.table.checkedOutcome data.claimsAccepted selector =
            .blocked reason) :
    ∀ handle : data.family.PacketSelectorHandle,
      data.table.environment.faithful handle = false :=
  data.table.noFaithful_of_selectorSilent data.dependencyTable
    (data.selectorSilenceAccepted silence) data.hbClosureAccepted

/-- Checked selector silence, checked HB closure, and the exact
positive-slack-to-faithful-selector bridge force residual slack to be zero. -/
def PCCMinCheckedPacketHBZeroSlackData.zeroSlackOfSilence
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketHBZeroSlackData current Atom Payload)
    (silence : ∀ rank selector,
      selector ∈ data.table.selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle data.rankCount,
          data.table.checkedOutcome data.claimsAccepted selector =
            .blocked reason) :
    ZeroSlackResult current := by
  have noFaithful := data.noFaithfulOfSilence silence
  have notPositive : ¬0 < residualSlack current := by
    intro positive
    obtain ⟨handle, faithful⟩ := data.faithfulOfPositiveSlack positive
    rw [noFaithful handle] at faithful
    contradiction
  have slackZero : residualSlack current = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  exact
    { minimum := (residualSlack_eq_zero_iff_minimum current).mp slackZero }

/-- The constructed result exposes the exact zero-slack conclusion. -/
theorem PCCMinCheckedPacketHBZeroSlackData.zeroSlackOfSilence_sound
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketHBZeroSlackData current Atom Payload)
    (silence : ∀ rank selector,
      selector ∈ data.table.selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            data.family.PacketSelectorHandle data.rankCount,
          data.table.checkedOutcome data.claimsAccepted selector =
            .blocked reason) :
    residualSlack current = 0 :=
  (data.zeroSlackOfSilence silence).sound

/-- Build M192's selector interface while deriving, rather than accepting,
its silence-to-ZeroSlack field. -/
def PCCMinCheckedPacketHBZeroSlackData.toCheckedPacketSelectorData
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketHBZeroSlackData current Atom Payload) :
    PCCMinCheckedPacketSelectorData current Atom Payload where
  family := data.family
  rankCount := data.rankCount
  table := data.table
  claimsAccepted := data.claimsAccepted
  zeroSlackOfSilence := data.zeroSlackOfSilence

/-! ## Rank-ordered oracle and total recursive builder -/

/-- HResolve and BudgetResolve remain explicit, but the terminal branch now
derives ZeroSlack from checked Packet/HB data and the precise positive-slack
bridge. -/
structure PCCMinCheckedPacketHBZeroSlackOraclePlan
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Atom Payload : Type) [DecidableEq Atom] where
  NoHereditary : Type
  NoBudget : Type
  hResolve : PCCMinResolverOutcome current NoHereditary
  budgetResolve : NoHereditary → PCCMinResolverOutcome current NoBudget
  selectorData : NoHereditary → NoBudget →
    PCCMinCheckedPacketHBZeroSlackData current Atom Payload

/-- Reuse the M192 checked Packet plan after constructing its ZeroSlack
closure from the checked HB bridge. -/
def PCCMinCheckedPacketHBZeroSlackOraclePlan.toCheckedPacketOraclePlan
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinCheckedPacketHBZeroSlackOraclePlan
      current Atom Payload) :
    PCCMinCheckedPacketRankOrderedOraclePlan current Atom Payload where
  NoHereditary := plan.NoHereditary
  NoBudget := plan.NoBudget
  hResolve := plan.hResolve
  budgetResolve := plan.budgetResolve
  selectorData := fun noHereditary noBudget =>
    (plan.selectorData noHereditary noBudget).toCheckedPacketSelectorData

/-- A total builder supplies the checked HB bridge for every implementation
reached by the well-founded loop. -/
structure PCCMinCheckedPacketHBZeroSlackOracleBuilder where
  Atom : {inputs outputs : Nat} →
    Implementation inputs outputs → Type
  Payload : {inputs outputs : Nat} →
    Implementation inputs outputs → Type
  atomDecidableEq : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      DecidableEq (Atom current)
  build : {inputs outputs : Nat} →
    (current : Implementation inputs outputs) →
      @PCCMinCheckedPacketHBZeroSlackOraclePlan inputs outputs current
        (Atom current) (Payload current) (atomDecidableEq current)

/-- Convert the checked HB builder to the M192 total builder. -/
def PCCMinCheckedPacketHBZeroSlackOracleBuilder.toCheckedPacketOracleBuilder
    (builder : PCCMinCheckedPacketHBZeroSlackOracleBuilder) :
    PCCMinCheckedPacketRankOrderedOracleBuilder where
  Atom := builder.Atom
  Payload := builder.Payload
  atomDecidableEq := builder.atomDecidableEq
  build := fun current =>
    letI : DecidableEq (builder.Atom current) :=
      builder.atomDecidableEq current
    (builder.build current).toCheckedPacketOraclePlan

/-- Run normalization followed by the checked Packet/HB rank-ordered oracle
and the existing well-founded exact loop. -/
def runPCCMinNormalizeCheckedPacketHBZeroSlackLoop
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketHBZeroSlackOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  runPCCMinNormalizeCheckedPacketRankOrderedOracleLoop normalizer
    builder.toCheckedPacketOracleBuilder current

/-- Public M193 endpoint: the final silence-to-ZeroSlack step is derived from
checked all-rank Packet silence, checked HB closure, and the explicit
positive-slack-to-faithful-selector boundary.  The latter boundary and all
terminal construction and runtime obligations remain open. -/
theorem pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinCheckedPacketHBZeroSlackOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinNormalizeCheckedPacketHBZeroSlackLoop
        normalizer builder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current := by
  exact pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete
    normalizer builder.toCheckedPacketOracleBuilder current

end DirectWire
end PNP
