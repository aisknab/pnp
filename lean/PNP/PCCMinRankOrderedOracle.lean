/-
Copyright (c) 2026 PNP Labs.

Rank-ordered reconstruction of the manuscript's PCCOracle control flow.

The oracle runs HResolve first, BudgetResolve only after a proof-bearing
NoHereditary outcome, and then every supplied selector at every canonical
finite rank.  A selector gain returns immediately.  ZeroSlack is available
only after the scan has retained a typed blocker equation for every selector
in every rank row.

This module does not construct HResolve, BudgetResolve, the rank rows,
selectors, realizer claims, blocker meanings, the ZeroSlack closure, or the
normalizer.  It makes their control-flow and completeness interface exact and
turns a total family of such plans into the total oracle consumed by the
well-founded PCCMin loop.  It proves no encoded-size or runtime bound.
-/

import PNP.PCCMinNormalizeOracleComposition

namespace PNP
namespace DirectWire

/-! ## Proof-bearing component outcomes -/

/-- The three manuscript outcomes of HResolve or BudgetResolve.  The
`noRoute` payload is positive evidence supplied to the next stage; it is not
an unresolved result. -/
inductive PCCMinResolverOutcome {inputs outputs : Nat}
    (current : Implementation inputs outputs) (NoRoute : Type) : Type where
  | exact (result : ExactMinimumResult current)
  | gain (next : Implementation inputs outputs)
      (verified : StrictEquivalentGain current next)
  | noRoute (evidence : NoRoute)

/-- One proof-bearing selector-realizer result.  A non-gain result must carry
a typed blocker value; there is no silent or unchecked constructor. -/
inductive PCCMinRankedRealizerOutcome {inputs outputs : Nat}
    (current : Implementation inputs outputs) (Bot : Type) : Type where
  | gain (next : Implementation inputs outputs)
      (verified : StrictEquivalentGain current next)
  | blocked (reason : Bot)

/-! ## Canonical finite rank scan -/

/-- Input-relative selector rows and their total realizer.  The final field is
the exact remaining mathematical boundary: complete typed silence, together
with any HResolve/BudgetResolve evidence captured when this plan was built,
must prove genuine ZeroSlack. -/
structure PCCMinRankedSelectorPlan {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  rankCount : Nat
  Selector : Type
  Bot : Type
  selectorsAt : Fin rankCount -> List Selector
  realize : (rank : Fin rankCount) -> Selector ->
    PCCMinRankedRealizerOutcome current Bot
  zeroSlackOfSilence :
    (forall rank selector, selector ∈ selectorsAt rank ->
      exists reason : Bot, realize rank selector = .blocked reason) ->
      ZeroSlackResult current

/-- Exact result of scanning one selector row.  The silent branch remembers
a blocker equation for every selector in that exact row. -/
inductive PCCMinSelectorRowScanOutcome {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current)
    (rank : Fin plan.rankCount)
    (selectors : List plan.Selector) : Type where
  | gain
      (selector : plan.Selector)
      (member : selector ∈ selectors)
      (next : Implementation inputs outputs)
      (verified : StrictEquivalentGain current next)
  | silent
      (allBlocked : forall selector, selector ∈ selectors ->
        exists reason : plan.Bot,
          plan.realize rank selector = .blocked reason)

/-- Scan one rank row from left to right, returning the first proof-bearing
gain or an exact typed-blocker ledger for the complete row. -/
def scanPCCMinSelectorRow {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current)
    (rank : Fin plan.rankCount) :
    (selectors : List plan.Selector) ->
      PCCMinSelectorRowScanOutcome plan rank selectors
  | [] => .silent (by simp)
  | head :: tail =>
      match chosen : plan.realize rank head with
      | .gain next verified =>
          .gain head (List.Mem.head tail) next verified
      | .blocked reason =>
          match scanPCCMinSelectorRow plan rank tail with
          | .gain selector member next verified =>
              .gain selector (List.Mem.tail head member) next verified
          | .silent allTailBlocked =>
              .silent (by
                intro selector member
                rcases List.mem_cons.mp member with headEquation | tailMember
                · subst selector
                  exact ⟨reason, chosen⟩
                · exact allTailBlocked selector tailMember)

/-- Exact result of scanning a supplied rank list.  The silent branch retains
a complete blocker ledger for every selector in every listed rank. -/
inductive PCCMinRankListScanOutcome {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current)
    (ranks : List (Fin plan.rankCount)) : Type where
  | gain
      (rank : Fin plan.rankCount)
      (rankMember : rank ∈ ranks)
      (selector : plan.Selector)
      (selectorMember : selector ∈ plan.selectorsAt rank)
      (next : Implementation inputs outputs)
      (verified : StrictEquivalentGain current next)
  | silent
      (allBlocked : forall rank, rank ∈ ranks ->
        forall selector, selector ∈ plan.selectorsAt rank ->
          exists reason : plan.Bot,
            plan.realize rank selector = .blocked reason)

/-- Scan rank rows in the supplied order and selectors in their row order. -/
def scanPCCMinRankList {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current) :
    (ranks : List (Fin plan.rankCount)) ->
      PCCMinRankListScanOutcome plan ranks
  | [] => .silent (by simp)
  | rank :: remainingRanks =>
      match scanPCCMinSelectorRow plan rank (plan.selectorsAt rank) with
      | .gain selector selectorMember next verified =>
          .gain rank (List.Mem.head remainingRanks)
            selector selectorMember next verified
      | .silent allRankBlocked =>
          match scanPCCMinRankList plan remainingRanks with
          | .gain laterRank rankMember selector selectorMember next verified =>
              .gain laterRank (List.Mem.tail rank rankMember)
                selector selectorMember next verified
          | .silent allLaterBlocked =>
              .silent (by
                intro queriedRank rankMember selector selectorMember
                rcases List.mem_cons.mp rankMember with rankEquation |
                    laterMember
                · subst queriedRank
                  exact allRankBlocked selector selectorMember
                · exact allLaterBlocked queriedRank laterMember
                    selector selectorMember)

/-- Complete outcome of scanning the canonical finite rank list `allFin`.
The silent branch quantifies over every finite rank, not merely a supplied
prefix. -/
inductive PCCMinRankedSelectorScanOutcome {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current) : Type where
  | gain
      (rank : Fin plan.rankCount)
      (selector : plan.Selector)
      (selectorMember : selector ∈ plan.selectorsAt rank)
      (next : Implementation inputs outputs)
      (verified : StrictEquivalentGain current next)
  | silent
      (allBlocked : forall rank selector,
        selector ∈ plan.selectorsAt rank ->
          exists reason : plan.Bot,
            plan.realize rank selector = .blocked reason)

/-- Execute the complete canonical rank-ordered selector scan. -/
def scanPCCMinRankedSelectors {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankedSelectorPlan current) :
    PCCMinRankedSelectorScanOutcome plan :=
  match scanPCCMinRankList plan (allFin plan.rankCount) with
  | .gain rank _rankMember selector selectorMember next verified =>
      .gain rank selector selectorMember next verified
  | .silent allBlocked =>
      .silent (fun rank selector selectorMember =>
        allBlocked rank (mem_allFin rank) selector selectorMember)

/-! ## HResolve/BudgetResolve/selector orchestration -/

/-- One complete manuscript-faithful oracle plan for `current`.  BudgetResolve
is constructed only from the actual NoHereditary evidence, and the selector
plan only from both actual negative resolver outcomes. -/
structure PCCMinRankOrderedOraclePlan {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  NoHereditary : Type
  NoBudget : Type
  hResolve : PCCMinResolverOutcome current NoHereditary
  budgetResolve : NoHereditary -> PCCMinResolverOutcome current NoBudget
  selectorPlan : NoHereditary -> NoBudget ->
    PCCMinRankedSelectorPlan current

/-- Run HResolve, then BudgetResolve, then the canonical rank-ordered selector
scan.  ZeroSlack is returned only through the complete-silence closure. -/
def PCCMinRankOrderedOraclePlan.route {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (plan : PCCMinRankOrderedOraclePlan current) :
    PCCMinOracleOutcome current :=
  match plan.hResolve with
  | .exact result => .exact result
  | .gain next verified => .gain next verified
  | .noRoute noHereditary =>
      match plan.budgetResolve noHereditary with
      | .exact result => .exact result
      | .gain next verified => .gain next verified
      | .noRoute noBudget =>
          let selectors := plan.selectorPlan noHereditary noBudget
          match scanPCCMinRankedSelectors selectors with
          | .gain _rank _selector _member next verified =>
              .gain next verified
          | .silent allBlocked =>
              .zeroSlack (selectors.zeroSlackOfSilence allBlocked)

/-- A total plan builder constructs the complete ordered component interface
for every finite direct-wire implementation.  This is still a supplied
construction boundary and carries no complexity claim. -/
structure PCCMinRankOrderedOracleBuilder where
  build : {inputs outputs : Nat} ->
    (current : Implementation inputs outputs) ->
      PCCMinRankOrderedOraclePlan current

/-- Convert the separated manuscript stages into the total-oracle interface
used by the existing well-founded loop. -/
def PCCMinRankOrderedOracleBuilder.toTotalOracle
    (builder : PCCMinRankOrderedOracleBuilder) : PCCMinTotalOracle where
  route := fun current => (builder.build current).route

/-- Run NormalizeOrGain followed by the reconstructed rank-ordered oracle. -/
def runPCCMinNormalizeRankOrderedOracleLoop
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinRankOrderedOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  runPCCMinNormalizeOracleLoop normalizer builder.toTotalOracle current

/-- Public M191 endpoint: arbitrary finite rank rows are exhausted in
canonical rank order after the two resolver stages, and the resulting total
oracle composes with normalization and the checked well-founded exact loop.

The builder, normalizer, blockers, and ZeroSlack closure remain supplied.  The
theorem therefore does not prove unconditional ZeroSlack, construct the exact
PCCMin algorithm, establish polynomial runtime, or close a weighted progress
checkpoint. -/
theorem pccmin_normalize_rank_ordered_oracle_loop_checked_complete
    (normalizer : PCCMinTotalNormalizer)
    (builder : PCCMinRankOrderedOracleBuilder)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinNormalizeRankOrderedOracleLoop normalizer builder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current := by
  exact pccmin_normalize_oracle_loop_checked_complete
    normalizer builder.toTotalOracle current

end DirectWire
end PNP
