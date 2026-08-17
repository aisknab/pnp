/-
Copyright (c) 2026 PNP Labs.

Canonical rank-tag reflection for the Packet selector-faithfulness payload.
The typed-realizer table already owns one authoritative finite rank for every
canonical handle. The computation below copies that rank into the source
payload and retains the exact ten-coordinate residual-rank descent comparison
from the preceding milestone. A caller-supplied payload rank can therefore no
longer manufacture the `.rank` failure route.

The grouped family, rank map, before/after residual ranks, first seven payload
Booleans, exact-route Boolean, realizer claims, blocker activity, and
dependency rows remain explicit inputs. This module does not construct those
data from a terminal candidate, prove the external manuscript semantics of the
remaining fields, map their routes into a complete global outcome system,
construct a no-lower ledger, prove complete route silence or unconditional HB
negative closure, establish ZeroSlack or PCCMin, prove polynomial runtime, put
SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketDescentRouteReflection

namespace PNP
namespace DirectWire

/-! ## Canonical finite rank and exact residual descent -/

/-- Preserve every unresolved payload field, copy the authoritative expected
    finite rank into `rankTag`, and compute the final descent bit from the exact
    residual-rank relation. Both caller-controlled duplicate fields are
    deliberately ignored. -/
def TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  { payload.withComputedDescent before after with
    rankTag := expectedRank }

/-- The projection changes exactly the duplicate rank tag and the executable
    descent field; all unresolved fields are preserved byte-for-field. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_fields
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).colourChecked =
        payload.colourChecked ∧
      (payload.withComputedRankDescent expectedRank before after
        ).frontierChecked = payload.frontierChecked ∧
      (payload.withComputedRankDescent expectedRank before after).chargeChecked =
        payload.chargeChecked ∧
      (payload.withComputedRankDescent expectedRank before after
        ).obligationChecked = payload.obligationChecked ∧
      (payload.withComputedRankDescent expectedRank before after
        ).activationChecked = payload.activationChecked ∧
      (payload.withComputedRankDescent expectedRank before after
        ).directionChecked = payload.directionChecked ∧
      (payload.withComputedRankDescent expectedRank before after).budgetChecked =
        payload.budgetChecked ∧
      (payload.withComputedRankDescent expectedRank before after).rankTag =
        expectedRank ∧
      (payload.withComputedRankDescent expectedRank before after
        ).exactRouteClear = payload.exactRouteClear ∧
      (payload.withComputedRankDescent expectedRank before after
        ).strictDescentClear = terminalResidualRankLTBool after before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Canonical acceptance no longer needs a separately supplied rank equality;
    it contains the exact residual-rank descent witness. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_valid_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).Valid
        expectedRank ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.exactRouteClear = true ∧
        after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_true_iff]

/-- The canonical rank tag makes the exact `.rank` failure proposition
    impossible for every payload and every finite rank. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_rank_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).FailureAt
        expectedRank .rank ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- The executable first-route classifier can never return the duplicate
    finite-rank mismatch route after canonicalization. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_firstRoute_ne_some_rank
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).firstRoute
        expectedRank ≠ some .rank := by
  intro found
  have failure :=
    ((payload.withComputedRankDescent expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .rank).1 found
  exact ((payload.withComputedRankDescent_failureAt_rank_iff_false
    expectedRank before after).1 failure).elim

/-- Exact final-route adequacy after both canonical projections. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_failureAt_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).FailureAt
        expectedRank .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.exactRouteClear = true ∧
        ¬after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_false_iff]

/-- The only remaining final route is the exact reflected nondecreasing
    transition after all unresolved earlier fields accept. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent_firstRoute_eq_some_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedRankDescent expectedRank before after).firstRoute
        expectedRank = some .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.exactRouteClear = true ∧
        ¬after.LexLT before := by
  calc
    (payload.withComputedRankDescent expectedRank before after).firstRoute
          expectedRank = some .descent ↔
        (payload.withComputedRankDescent expectedRank before after).FailureAt
          expectedRank .descent :=
      (payload.withComputedRankDescent expectedRank before after
        ).firstRoute_eq_some_iff_failureAt expectedRank .descent
    _ ↔ _ := payload.withComputedRankDescent_failureAt_descent_iff
      expectedRank before after

/-- Acceptance still exposes actual descent after rank canonicalization. -/
theorem TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedRankDescent_check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank)
    (accepted : (payload.withComputedRankDescent expectedRank before after
      ).check expectedRank = true) :
    after.LexLT before := by
  have valid :=
    (payload.withComputedRankDescent expectedRank before after
      ).check_eq_true_iff expectedRank |>.1 accepted
  rcases (payload.withComputedRankDescent_valid_iff expectedRank before after).1
      valid with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, _exactRoute, descent⟩
  exact descent

/-! ## Canonical grouped-family computation -/

/-- Canonical source payload with its finite rank copied from the authoritative
    handle-rank map and its final bit computed from supplied residual ranks. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  (family.packetSelectorPayloadAtom handle).payload.withComputedRankDescent
    (rankOf handle) (beforeRank handle) (afterRank handle)

/-- Faithfulness computed from the same canonical rank and residual descent. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedRankDescent rankOf beforeRank
    afterRank handle).check (rankOf handle)

/-- First route computed from the same doubly canonicalized payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedRankDescent rankOf beforeRank
    afterRank handle).firstRoute (rankOf handle)

/-- Exact earliest failure of the doubly canonicalized source payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedRankDescent rankOf beforeRank
    afterRank handle).FailureAt (rankOf handle) route

/-- Grouped-family first-route equality and exact canonicalized failure
    coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedRankDescent_eq_some_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedRankDescent rankOf
        beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedRankDescent rankOf
        beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedRankDescent rankOf beforeRank
    afterRank handle).firstRoute_eq_some_iff_failureAt (rankOf handle) route

/-- No canonical grouped-family handle can report the duplicate rank route. -/
theorem TerminalBN6GroupedFamily.computedRankDescent_firstRoute_ne_some_rank
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedRankDescent rankOf
        beforeRank afterRank handle ≠ some .rank :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedRankDescent_firstRoute_ne_some_rank
      (rankOf handle) (beforeRank handle) (afterRank handle)

/-- A final canonicalized route proves that the supplied residual transition
    does not decrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedRankDescent_firstRoute_descent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedRankDescent rankOf
        beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  change
    ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedRankDescent (rankOf handle) (beforeRank handle)
        (afterRank handle)).firstRoute (rankOf handle) = some .descent at found
  rcases ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedRankDescent_firstRoute_eq_some_descent_iff
        (rankOf handle) (beforeRank handle) (afterRank handle)).1 found with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, _exactRoute, notDescent⟩
  exact notDescent

/-! ## Canonicalized HB table and total outcome -/

/-- Rebuild only table faithfulness from the canonical finite rank and exact
    residual descent. Rank assignment, claims, and blocker activity are
    retained exactly. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorRankDescentFaithfulness
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful :=
          family.packetSelectorPayloadFaithfulWithComputedRankDescent
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Canonicalization preserves every nonfaithfulness table input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorRankDescentFaithfulness_preserves
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (rank : Fin rankCount) :
    (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
      afterRank).environment.rankOf handle = table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt table's faithfulness bit is definitionally the canonical
    rank-tag and residual-descent computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorRankDescentFaithfulness_faithful
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
      afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedRankDescent
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces every positive Packet to expose an exact
    canonicalized failure. The duplicate rank route is excluded, and a final
    descent route carries actual nondecrease. -/
theorem TerminalBN6PacketConclusion.existsRankTagReflectedFirstRouteFailure_of_selectorSilence
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .rank ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
      afterRank).noFaithful_of_selectorSilent dependencyTable silenceAccepted
        closureAccepted handle
  rw [table.withComputedPacketSelectorRankDescentFaithfulness_faithful
    beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedRankDescent
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedRankDescent_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedRankDescent_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  refine ⟨handle, route, found, failure, notRank, ?_⟩
  by_cases isDescent : route = .descent
  · subst route
    exact Or.inr
      (family.not_rankDescent_of_computedRankDescent_firstRoute_descent
        table.environment.rankOf beforeRank afterRank handle found)
  · exact Or.inl isDescent

/-- Named milestone endpoint: positive Packet plus executable HB silence gives
    one exact non-rank field route; a final descent route proves the supplied
    ten-coordinate transition is nondecreasing. -/
theorem terminalBN6_packet_rank_tag_reflected_hb_first_route_failure
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorRankDescentFaithfulness beforeRank
        afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .rank ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsRankTagReflectedFirstRouteFailure_of_selectorSilence table
    dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
