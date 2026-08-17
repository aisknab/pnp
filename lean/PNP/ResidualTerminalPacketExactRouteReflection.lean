/-
Copyright (c) 2026 PNP Labs.

Canonical internal exact-route reflection for the Packet
selector-faithfulness payload. Every canonical handle already materializes one
exact input-relative grouped cell and one original positive payload atom, with
proofs of group membership, footprint equality, atom membership, and positive
mass. The computation below marks that internal handle-to-source route clear by
construction, copies the typed-realizer table's authoritative finite rank, and
retains the exact ten-coordinate residual-rank descent comparison.

The seven semantic payload Booleans, grouped family, rank map, before/after
residual ranks, realizer claims, blocker activity, and dependency rows remain
explicit inputs. Internal source-route exactness is not a proof of external
manuscript exact-minimum semantics. This module does not derive the remaining
fields from a terminal candidate, map their routes into a complete global
outcome system, construct a no-lower ledger, prove complete route silence or
unconditional HB negative closure, establish ZeroSlack or PCCMin, prove
polynomial runtime, put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketRankRouteReflection

namespace PNP
namespace DirectWire

/-! ## Canonical source route, finite rank, and residual descent -/

/-- Preserve every unresolved semantic field, mark the already canonical
    handle-to-source route clear, copy the authoritative expected finite rank,
    and compute the final descent bit from the exact residual-rank relation.
    The three caller-controlled duplicate fields are deliberately ignored. -/
def TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  { payload.withComputedRankDescent expectedRank before after with
    exactRouteClear := true }

/-- The projection changes exactly the internal route bit, duplicate rank tag,
    and executable descent field. The seven semantic fields are preserved. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_fields
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).colourChecked = payload.colourChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).frontierChecked = payload.frontierChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).chargeChecked = payload.chargeChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).obligationChecked = payload.obligationChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).activationChecked = payload.activationChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).directionChecked = payload.directionChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).budgetChecked = payload.budgetChecked ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).rankTag = expectedRank ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).exactRouteClear = true ∧
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).strictDescentClear = terminalResidualRankLTBool after before := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Canonical acceptance no longer needs separate exact-route or rank-equality
    premises and still contains the exact residual-rank descent witness. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_valid_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).Valid expectedRank ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_true_iff]

/-- Canonical rank reflection makes the `.rank` failure proposition
    impossible. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_failureAt_rank_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).FailureAt expectedRank .rank ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Canonical source realization makes the internal `.exactRoute` failure
    proposition impossible. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_failureAt_exactRoute_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).FailureAt expectedRank .exactRoute ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- The executable classifier cannot return the duplicate finite-rank route. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_firstRoute_ne_some_rank
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).firstRoute expectedRank ≠ some .rank := by
  intro found
  have failure :=
    ((payload.withComputedExactRouteRankDescent expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .rank).1 found
  exact ((payload.withComputedExactRouteRankDescent_failureAt_rank_iff_false
    expectedRank before after).1 failure).elim

/-- The executable classifier cannot return the canonical internal-route
    failure. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_firstRoute_ne_some_exactRoute
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).firstRoute expectedRank ≠ some .exactRoute := by
  intro found
  have failure :=
    ((payload.withComputedExactRouteRankDescent expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .exactRoute).1 found
  exact ((payload.withComputedExactRouteRankDescent_failureAt_exactRoute_iff_false
      expectedRank before after).1 failure).elim

/-- Exact final-route adequacy after all three canonical projections. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_failureAt_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).FailureAt expectedRank .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        ¬after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_false_iff]

/-- The only final route is reflected nondecrease after all seven semantic
    fields accept. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent_firstRoute_eq_some_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).firstRoute expectedRank = some .descent ↔
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        ¬after.LexLT before := by
  calc
    (payload.withComputedExactRouteRankDescent expectedRank before after
        ).firstRoute expectedRank = some .descent ↔
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).FailureAt expectedRank .descent :=
      (payload.withComputedExactRouteRankDescent expectedRank before after
        ).firstRoute_eq_some_iff_failureAt expectedRank .descent
    _ ↔ _ := payload.withComputedExactRouteRankDescent_failureAt_descent_iff
      expectedRank
        before after

/-- Acceptance still exposes actual descent after all three canonical
    projections. -/
theorem TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedExactRouteRankDescent_check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank)
    (accepted : (payload.withComputedExactRouteRankDescent expectedRank before
      after).check expectedRank = true) :
    after.LexLT before := by
  have valid :=
    (payload.withComputedExactRouteRankDescent expectedRank before after
      ).check_eq_true_iff expectedRank |>.1 accepted
  rcases (payload.withComputedExactRouteRankDescent_valid_iff expectedRank
      before after).1 valid with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, descent⟩
  exact descent

/-! ## Canonical grouped-family source realization -/

/-- The internal route marked clear by the projection already has exact source
    evidence: the selected grouped cell is original, its footprint is the
    decoded footprint, and the selected positive atom is original. -/
theorem TerminalBN6GroupedFamily.packetSelectorCanonicalSourceRoute
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorCell handle ∈ family.groups ∧
      (family.packetSelectorCell handle).footprint =
        family.packetSelectorFootprint handle ∧
      family.packetSelectorPayloadAtom handle ∈
        (family.packetSelectorCell handle).atoms ∧
      0 < (family.packetSelectorPayloadAtom handle).mass :=
  ⟨family.packetSelectorCell_mem_groups handle,
    family.packetSelectorCell_footprint handle,
    family.packetSelectorPayloadAtom_mem handle,
    (family.packetSelectorPayloadAtom handle).massPositive⟩

/-- Canonical source payload with internal route, finite rank, and residual
    descent all reflected from their authoritative inputs. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedExactRouteRankDescent (rankOf handle) (beforeRank handle)
      (afterRank handle)

/-- Faithfulness computed from the same canonical source route, rank, and
    residual descent. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedExactRouteRankDescent rankOf
    beforeRank afterRank handle).check (rankOf handle)

/-- First route computed from the same triply canonicalized payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedExactRouteRankDescent rankOf
    beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Exact earliest failure of the triply canonicalized source payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedExactRouteRankDescent rankOf
    beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- Grouped-family route equality and exact canonicalized failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent_eq_some_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedExactRouteRankDescent
        rankOf beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedExactRouteRankDescent rankOf
    beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
      (rankOf handle) route

/-- No canonical grouped-family handle can report the duplicate rank route. -/
theorem TerminalBN6GroupedFamily.computedExactRouteRankDescent_firstRoute_ne_some_rank
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .rank :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedExactRouteRankDescent_firstRoute_ne_some_rank
      (rankOf handle) (beforeRank handle) (afterRank handle)

/-- No canonical grouped-family handle can report the reflected internal-route
    failure. -/
theorem TerminalBN6GroupedFamily.computedExactRouteRankDescent_firstRoute_ne_some_exactRoute
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .exactRoute :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedExactRouteRankDescent_firstRoute_ne_some_exactRoute
      (rankOf handle) (beforeRank handle) (afterRank handle)

/-- A final canonicalized route proves that the supplied residual transition
    does not decrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedExactRouteRankDescent_firstRoute_descent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  change
    ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedExactRouteRankDescent (rankOf handle)
        (beforeRank handle) (afterRank handle)).firstRoute
          (rankOf handle) = some .descent at found
  rcases ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedExactRouteRankDescent_firstRoute_eq_some_descent_iff
        (rankOf handle) (beforeRank handle) (afterRank handle)).1 found with
    ⟨_colour, _frontier, _charge, _obligation, _activation, _direction,
      _budget, notDescent⟩
  exact notDescent

/-! ## Canonicalized HB table and total outcome -/

/-- Rebuild only table faithfulness from the canonical source route, finite
    rank, and exact residual descent. Other executable inputs are retained. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorExactRouteRankDescentFaithfulness
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
          family.packetSelectorPayloadFaithfulWithComputedExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Canonicalization preserves every nonfaithfulness table input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorExactRouteRankDescentFaithfulness_preserves
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
    (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt table's faithfulness bit is definitionally the triply
    canonical computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorExactRouteRankDescentFaithfulness_faithful
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedExactRouteRankDescent
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces every positive Packet to expose an exact
    canonicalized failure. Both duplicate routes are excluded, and a final
    descent route carries actual nondecrease. -/
theorem TerminalBN6PacketConclusion.existsExactRouteReflectedFirstRouteFailure_of_selectorSilence
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
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorExactRouteRankDescentFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedExactRouteRankDescent
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent_eq_some_iff
        table.environment.rankOf beforeRank afterRank handle route).1 found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedExactRouteRankDescent_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedExactRouteRankDescent_firstRoute_ne_some_exactRoute
        table.environment.rankOf beforeRank afterRank handle found
  refine ⟨handle, route, found, failure, notRank, notExactRoute, ?_⟩
  by_cases isDescent : route = .descent
  · subst route
    exact Or.inr
      (family.not_rankDescent_of_computedExactRouteRankDescent_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
  · exact Or.inl isDescent

/-- Named milestone endpoint: positive Packet plus executable HB silence gives
    one exact non-rank, non-exact-route failure; a final descent route proves
    the supplied ten-coordinate transition is nondecreasing. -/
theorem terminalBN6_packet_exact_route_reflected_hb_first_route_failure
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
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsExactRouteReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
