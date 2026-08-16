/-
Copyright (c) 2026 PNP Labs.

Rank-reflected semantics for the final Packet selector-faithfulness field.
The canonical computation below preserves the first nine supplied payload
inputs and replaces only `strictDescentClear` by the executable comparison on
the exact ten-coordinate `TerminalResidualRank`.  Thus a final `.descent`
failure carries the kernel proposition that the supplied after-rank does not
strictly precede the supplied before-rank.

The before/after ranks and their handle assignment remain explicit inputs, as
do the first nine payload fields, the grouped family, realizer claims, blocker
activity, and dependency rows.  This module does not derive those data from a
terminal candidate, map the other nine routes into the complete global outcome
system, construct a no-lower ledger, prove complete route silence or
unconditional HB negative closure, establish ZeroSlack or PCCMin, prove
polynomial runtime, put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorFirstRouteSemantics

namespace PNP
namespace DirectWire

/-! ## Rank-reflected payload -/

/-- Preserve every earlier Packet field and compute the final descent check
    from the exact residual-rank relation.  A caller-supplied value of
    `strictDescentClear` is deliberately ignored. -/
def TerminalPacketSelectorFaithfulnessPayload.withComputedDescent
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (before after : TerminalResidualRank) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  { payload with
    strictDescentClear := terminalResidualRankLTBool after before }

/-- The projection changes exactly one field, and that field is the executable
    view of `after.LexLT before`. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_fields
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedDescent before after).colourChecked =
        payload.colourChecked ∧
      (payload.withComputedDescent before after).frontierChecked =
        payload.frontierChecked ∧
      (payload.withComputedDescent before after).chargeChecked =
        payload.chargeChecked ∧
      (payload.withComputedDescent before after).obligationChecked =
        payload.obligationChecked ∧
      (payload.withComputedDescent before after).activationChecked =
        payload.activationChecked ∧
      (payload.withComputedDescent before after).directionChecked =
        payload.directionChecked ∧
      (payload.withComputedDescent before after).budgetChecked =
        payload.budgetChecked ∧
      (payload.withComputedDescent before after).rankTag = payload.rankTag ∧
      (payload.withComputedDescent before after).exactRouteClear =
        payload.exactRouteClear ∧
      (payload.withComputedDescent before after).strictDescentClear =
        terminalResidualRankLTBool after before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Rank-reflected validity contains a proof of actual lexicographic descent,
    rather than trust in the original Boolean field. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_valid_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedDescent before after).Valid expectedRank ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag = expectedRank ∧
        payload.exactRouteClear = true ∧
        after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_true_iff]

/-- Exact final-route adequacy: every earlier field accepted and the supplied
    transition is genuinely nondecreasing in `RankWF`. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_failureAt_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedDescent before after).FailureAt expectedRank
        .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag = expectedRank ∧
        payload.exactRouteClear = true ∧
        ¬after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_false_iff]

/-- The executable first-route classifier reports `.descent` exactly at the
    reflected nondecreasing transition after the complete earlier prefix. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedDescent_firstRoute_eq_some_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedDescent before after).firstRoute expectedRank =
        some .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag = expectedRank ∧
        payload.exactRouteClear = true ∧
        ¬after.LexLT before := by
  calc
    (payload.withComputedDescent before after).firstRoute expectedRank =
          some .descent ↔
        (payload.withComputedDescent before after).FailureAt expectedRank
          .descent :=
      (payload.withComputedDescent before after
        ).firstRoute_eq_some_iff_failureAt expectedRank .descent
    _ ↔ _ := payload.withComputedDescent_failureAt_descent_iff
      expectedRank before after

/-- Acceptance of the rank-reflected payload exposes the actual decreasing
    relation for the supplied ranks. -/
theorem TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedDescent_check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank)
    (accepted : (payload.withComputedDescent before after).check expectedRank =
      true) :
    after.LexLT before := by
  have valid :=
    (payload.withComputedDescent before after
      ).check_eq_true_iff expectedRank |>.1 accepted
  rcases (payload.withComputedDescent_valid_iff expectedRank before after).1
      valid with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, _rank, _exactRoute, descent⟩
  exact descent

/-! ## Canonical grouped-family computation -/

/-- Canonical source payload with its last field recomputed from the supplied
    per-handle residual ranks. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  (family.packetSelectorPayloadAtom handle).payload.withComputedDescent
    (beforeRank handle) (afterRank handle)

/-- Faithfulness computed from the rank-reflected canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle
    ).check (rankOf handle)

/-- First route computed from the same rank-reflected canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle
    ).firstRoute (rankOf handle)

/-- Exact earliest failure of the rank-reflected canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle
    ).FailureAt (rankOf handle) route

/-- Grouped-family first-route equality and exact reflected failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedDescent_eq_some_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedDescent rankOf beforeRank
        afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedDescent rankOf
        beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle
    ).firstRoute_eq_some_iff_failureAt (rankOf handle) route

/-- A final reflected route is proof that the supplied transition does not
    decrease the exact residual rank. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computed_firstRoute_descent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found : family.packetSelectorPayloadFirstRouteWithComputedDescent rankOf
      beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  change
    (family.packetSelectorPayloadWithComputedDescent beforeRank afterRank handle
      ).firstRoute (rankOf handle) = some .descent at found
  rcases ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedDescent_firstRoute_eq_some_descent_iff
        (rankOf handle) (beforeRank handle) (afterRank handle)).1 found with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, _rank, _exactRoute, notDescent⟩
  exact notDescent

/-! ## Rank-reflected HB table and total outcome -/

/-- Rebuild only the table's faithfulness function from rank-reflected
    canonical payloads.  Rank assignment, claims, and blocker activity are
    retained exactly. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorDescentFaithfulness
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
        faithful := family.packetSelectorPayloadFaithfulWithComputedDescent
          table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Rank-reflected canonicalization preserves every nonfaithfulness input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorDescentFaithfulness_preserves
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
    (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
      ).environment.rankOf handle = table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).environment.hnActive rank = table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).environment.budgetActive rank = table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt table's faithfulness bit is definitionally the reflected
    canonical payload computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorDescentFaithfulness_faithful
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
      ).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedDescent
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces every positive Packet to expose an exact
    reflected failure.  A final `.descent` route is accompanied by actual
    nondecrease; all other constructors are explicitly earlier routes. -/
theorem TerminalBN6PacketConclusion.existsRankReflectedFirstRouteFailure_of_selectorSilence
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
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
      ).noFaithful_of_selectorSilent dependencyTable silenceAccepted
        closureAccepted handle
  rw [table.withComputedPacketSelectorDescentFaithfulness_faithful
    beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedDescent beforeRank afterRank
      handle).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedDescent_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  refine ⟨handle, route, found, failure, ?_⟩
  by_cases isDescent : route = .descent
  · subst route
    exact Or.inr
      (family.not_rankDescent_of_computed_firstRoute_descent
        table.environment.rankOf beforeRank afterRank handle found)
  · exact Or.inl isDescent

/-- Named milestone endpoint: positive Packet plus executable HB silence gives
    an earlier exact field route or a proof that the supplied final transition
    is not decreasing in the ten-coordinate `RankWF` relation. -/
theorem terminalBN6_packet_rank_reflected_hb_first_route_failure
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
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorDescentFaithfulness beforeRank afterRank
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsRankReflectedFirstRouteFailure_of_selectorSilence table
    dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
