/-
Copyright (c) 2026 PNP Labs.

Data-only typed output validation for the finite Packet selector-realizer
contract.  A supplied executable environment assigns each selector one
canonical finite-rank index and supplies Boolean faithfulness, hereditary-
blocker activity, and budget-blocker activity tables.  A realizer claim is
either one unit-charge replacement blueprint or one of the three public bot
forms from the pinned manuscript: HN, budget, or a lower-rank faithful seed.

The checker accepts gain claims only through the existing exact-occurrence and
semantic-equivalence blueprint validator.  It accepts HN and budget bots only
when the named table entry is active at a rank no greater than the current
selector rank, and seed bots only when the named selector is faithful at a
strictly smaller rank.  The faithful-table checker covers an arbitrary finite
selector list; the final specialization covers every canonical handle in an
arbitrary supplied finite grouped BN6 family.

The selector family, rank assignment, faithfulness predicate, realizer claims,
and blocker tables remain explicit inputs.  Finite indices are not the
manuscript rank tuple.  This module does not construct blueprints or blockers
from terminal data, prove selector faithfulness or compatibility, establish
blocker semantics or HB acyclicity, derive global selector silence, prove
polynomial enumeration or runtime, prove ZeroSlack or PCCMin, put SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketUnitChargeBlueprintRealizer

namespace PNP
namespace DirectWire

/-! ## Executable finite-rank environment -/

/-- Input-relative executable tables used to validate typed realizer claims.
    The rank carrier is arbitrary and finite; its canonical order is the order
    on `Fin rankCount`. -/
structure TerminalPacketTypedRealizerEnvironment
    (Selector : Type) (rankCount : Nat) where
  rankOf : Selector -> Fin rankCount
  faithful : Selector -> Bool
  hnActive : Fin rankCount -> Bool
  budgetActive : Fin rankCount -> Bool

/-! ## Three public typed bot forms -/

/-- A realizer bot names exactly one hereditary rank, budget rank, or proposed
    lower-rank selector.  It contains no proof that the named reason is valid. -/
inductive TerminalPacketTypedRealizerBot
    (Selector : Type) (rankCount : Nat) : Type where
  | hn (rank : Fin rankCount)
  | budget (rank : Fin rankCount)
  | lowerSeed (selector : Selector)

/-- Exact proposition enforced for one typed bot relative to the supplied
    executable environment and current selector. -/
def TerminalPacketTypedRealizerBot.Valid
    {Selector : Type} {rankCount : Nat}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (bot : TerminalPacketTypedRealizerBot Selector rankCount) : Prop :=
  match bot with
  | .hn rank =>
      rank ≤ environment.rankOf selector ∧ environment.hnActive rank = true
  | .budget rank =>
      rank ≤ environment.rankOf selector ∧
        environment.budgetActive rank = true
  | .lowerSeed lower =>
      environment.rankOf lower < environment.rankOf selector ∧
        environment.faithful lower = true

/-- Executable fail-closed validator for one typed bot. -/
def TerminalPacketTypedRealizerBot.check
    {Selector : Type} {rankCount : Nat}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (bot : TerminalPacketTypedRealizerBot Selector rankCount) : Bool :=
  match bot with
  | .hn rank =>
      decide (rank ≤ environment.rankOf selector) &&
        environment.hnActive rank
  | .budget rank =>
      decide (rank ≤ environment.rankOf selector) &&
        environment.budgetActive rank
  | .lowerSeed lower =>
      decide (environment.rankOf lower < environment.rankOf selector) &&
        environment.faithful lower

/-- The Boolean bot checker recognizes exactly active bounded-rank HN or budget
    reasons and faithful strictly lower-rank seed reasons. -/
theorem TerminalPacketTypedRealizerBot.check_eq_true_iff
    {Selector : Type} {rankCount : Nat}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (bot : TerminalPacketTypedRealizerBot Selector rankCount) :
    bot.check environment selector = true ↔ bot.Valid environment selector := by
  cases bot <;>
    simp [TerminalPacketTypedRealizerBot.check,
      TerminalPacketTypedRealizerBot.Valid, Bool.and_eq_true,
      decide_eq_true_eq]

/-! ## Data-only gain-or-bot claims -/

/-- One unchecked realizer row.  The gain branch carries only a replacement
    blueprint; the bot branch carries only one typed reason. -/
inductive TerminalPacketTypedRealizerClaim
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (Selector : Type) (rankCount : Nat) : Type where
  | gain (blueprint : TerminalPacketUnitChargeBlueprint current)
  | bot (reason : TerminalPacketTypedRealizerBot Selector rankCount)

/-- Exact proposition checked for one gain-or-bot claim. -/
def TerminalPacketTypedRealizerClaim.Valid
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) : Prop :=
  match claim with
  | .gain blueprint => blueprint.Valid
  | .bot reason => reason.Valid environment selector

/-- Executable fail-closed validator for one gain-or-bot claim. -/
def TerminalPacketTypedRealizerClaim.check
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) : Bool :=
  match claim with
  | .gain blueprint => blueprint.check
  | .bot reason => reason.check environment selector

/-- The row checker accepts exactly a valid charge-derived blueprint or one
    valid typed bot. -/
theorem TerminalPacketTypedRealizerClaim.check_eq_true_iff
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) :
    claim.check environment selector = true ↔
      claim.Valid environment selector := by
  cases claim with
  | gain blueprint =>
      exact blueprint.check_eq_true_iff
  | bot reason =>
      exact reason.check_eq_true_iff environment selector

/-- Public logical meaning of one checked claim.  The gain branch includes the
    derived strict gain; the other branches expose exactly the checked typed
    blocker facts. -/
def TerminalPacketTypedRealizerClaim.Sound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) : Prop :=
  (∃ blueprint : TerminalPacketUnitChargeBlueprint current,
    claim = .gain blueprint ∧ blueprint.Valid ∧
      StrictEquivalentGain current blueprint.next) ∨
  (∃ rank : Fin rankCount,
    claim = .bot (.hn rank) ∧
      rank ≤ environment.rankOf selector ∧
      environment.hnActive rank = true) ∨
  (∃ rank : Fin rankCount,
    claim = .bot (.budget rank) ∧
      rank ≤ environment.rankOf selector ∧
      environment.budgetActive rank = true) ∨
  (∃ lower : Selector,
    claim = .bot (.lowerSeed lower) ∧
      environment.rankOf lower < environment.rankOf selector ∧
      environment.faithful lower = true)

/-- Proof-bearing evidence reconstructed only after one data-only claim has
    passed its checker.  Equality fields tie the evidence to the exact claim. -/
inductive TerminalPacketTypedRealizerEvidence
    {Selector : Type} {rankCount inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) : Type where
  | gain
      (blueprint : TerminalPacketUnitChargeBlueprint current)
      (claimEquation : claim = .gain blueprint)
      (valid : blueprint.Valid) :
      TerminalPacketTypedRealizerEvidence current environment selector claim
  | hn
      (rank : Fin rankCount)
      (claimEquation : claim = .bot (.hn rank))
      (rankBound : rank ≤ environment.rankOf selector)
      (active : environment.hnActive rank = true) :
      TerminalPacketTypedRealizerEvidence current environment selector claim
  | budget
      (rank : Fin rankCount)
      (claimEquation : claim = .bot (.budget rank))
      (rankBound : rank ≤ environment.rankOf selector)
      (active : environment.budgetActive rank = true) :
      TerminalPacketTypedRealizerEvidence current environment selector claim
  | lowerSeed
      (lower : Selector)
      (claimEquation : claim = .bot (.lowerSeed lower))
      (rankStrict : environment.rankOf lower < environment.rankOf selector)
      (faithful : environment.faithful lower = true) :
      TerminalPacketTypedRealizerEvidence current environment selector claim

/-- Acceptance reconstructs exactly one proof-bearing gain or typed bot
    evidence value; no proof field occurs in the checked claim itself. -/
def TerminalPacketTypedRealizerClaim.evidenceOfCheck
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount)
    (checked : claim.check environment selector = true) :
    TerminalPacketTypedRealizerEvidence current environment selector claim := by
  have valid := (claim.check_eq_true_iff environment selector).1 checked
  cases claim with
  | gain blueprint =>
      change blueprint.Valid at valid
      exact .gain blueprint rfl valid
  | bot reason =>
      cases reason with
      | hn rank =>
          change rank ≤ environment.rankOf selector ∧
            environment.hnActive rank = true at valid
          exact .hn rank rfl valid.1 valid.2
      | budget rank =>
          change rank ≤ environment.rankOf selector ∧
            environment.budgetActive rank = true at valid
          exact .budget rank rfl valid.1 valid.2
      | lowerSeed lower =>
          change environment.rankOf lower < environment.rankOf selector ∧
            environment.faithful lower = true at valid
          exact .lowerSeed lower rfl valid.1 valid.2

/-- Checked evidence exposes only a genuine charge-derived gain, an active
    bounded HN bot, an active bounded budget bot, or a faithful strictly
    lower-rank selector. -/
theorem TerminalPacketTypedRealizerEvidence.sound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {environment : TerminalPacketTypedRealizerEnvironment Selector rankCount}
    {selector : Selector}
    {claim : TerminalPacketTypedRealizerClaim current Selector rankCount}
    (evidence : TerminalPacketTypedRealizerEvidence
      current environment selector claim) :
    claim.Sound environment selector := by
  unfold TerminalPacketTypedRealizerClaim.Sound
  cases evidence with
  | gain blueprint claimEquation valid =>
      exact Or.inl ⟨blueprint, claimEquation, valid,
        valid.chargeSurplusRealization.strictEquivalentGain⟩
  | hn rank claimEquation rankBound active =>
      exact Or.inr (Or.inl ⟨rank, claimEquation, rankBound, active⟩)
  | budget rank claimEquation rankBound active =>
      exact Or.inr (Or.inr (Or.inl
        ⟨rank, claimEquation, rankBound, active⟩))
  | lowerSeed lower claimEquation rankStrict faithful =>
      exact Or.inr (Or.inr (Or.inr
        ⟨lower, claimEquation, rankStrict, faithful⟩))

/-! ## Arbitrary finite faithful-selector table validation -/

/-- Check every selector in one arbitrary finite list.  Nonfaithful rows are
    outside the manuscript's conditional typed-bot obligation; every faithful
    row must pass its exact gain-or-typed-bot checker. -/
def checkTerminalPacketFaithfulRealizerClaims
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (selectors : List Selector)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (claim : Selector ->
      TerminalPacketTypedRealizerClaim current Selector rankCount) : Bool :=
  selectors.all (fun selector =>
    !environment.faithful selector ||
      (claim selector).check environment selector)

/-- Faithful-table acceptance gives exact checked evidence for every faithful
    selector present in the supplied finite list. -/
def checkTerminalPacketFaithfulRealizerClaims_handle
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (selectors : List Selector)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (claim : Selector ->
      TerminalPacketTypedRealizerClaim current Selector rankCount)
    (accepted : checkTerminalPacketFaithfulRealizerClaims
      selectors environment claim = true)
    (selector : Selector)
    (selectorMember : selector ∈ selectors)
    (faithful : environment.faithful selector = true) :
    TerminalPacketTypedRealizerEvidence current environment selector
      (claim selector) := by
  have rowChecked := (List.all_eq_true.mp accepted) selector selectorMember
  have claimChecked :
      (claim selector).check environment selector = true := by
    simpa [faithful] using rowChecked
  exact (claim selector).evidenceOfCheck environment selector claimChecked

/-- Every faithful selector in an accepted arbitrary finite table has only the
    four public checked outcomes. -/
theorem checkTerminalPacketFaithfulRealizerClaims_sound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (selectors : List Selector)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (claim : Selector ->
      TerminalPacketTypedRealizerClaim current Selector rankCount)
    (accepted : checkTerminalPacketFaithfulRealizerClaims
      selectors environment claim = true)
    (selector : Selector)
    (selectorMember : selector ∈ selectors)
    (faithful : environment.faithful selector = true) :
    (claim selector).Sound environment selector := by
  exact TerminalPacketTypedRealizerEvidence.sound
    (checkTerminalPacketFaithfulRealizerClaims_handle selectors environment
      claim accepted selector selectorMember faithful)

/-! ## Canonical Packet-handle specialization -/

/-- One explicit typed-realizer table over all canonical handles of a supplied
    finite grouped BN6 family. -/
structure TerminalPacketTypedRealizerTable
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom Payload)
    (rankCount : Nat) where
  environment : TerminalPacketTypedRealizerEnvironment
    family.PacketSelectorHandle rankCount
  claim : (handle : family.PacketSelectorHandle) ->
    TerminalPacketTypedRealizerClaim current
      family.PacketSelectorHandle rankCount

/-- Validate every faithful canonical handle in the supplied family. -/
def TerminalPacketTypedRealizerTable.checkFaithful
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  checkTerminalPacketFaithfulRealizerClaims family.packetSelectorHandles
    table.environment table.claim

/-- Accepted canonical-family validation covers every faithful handle, using
    the existing exhaustive input-relative handle enumeration. -/
def TerminalPacketTypedRealizerTable.checkFaithful_handle
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkFaithful = true)
    (handle : family.PacketSelectorHandle)
    (faithful : table.environment.faithful handle = true) :
    TerminalPacketTypedRealizerEvidence current table.environment handle
      (table.claim handle) :=
  checkTerminalPacketFaithfulRealizerClaims_handle
    family.packetSelectorHandles table.environment table.claim accepted
    handle (family.mem_packetSelectorHandles handle) faithful

/-- Named finite Packet interface: every faithful canonical handle in an
    accepted table yields a checked gain or exactly one permitted typed bot. -/
theorem terminalBN6_packet_typed_realizer_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkFaithful = true)
    (handle : family.PacketSelectorHandle)
    (faithful : table.environment.faithful handle = true) :
    (table.claim handle).Sound table.environment handle :=
  (table.checkFaithful_handle accepted handle faithful).sound

end DirectWire
end PNP
