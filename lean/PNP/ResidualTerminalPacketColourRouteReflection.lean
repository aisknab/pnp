/-
Copyright (c) 2026 PNP Labs.

Canonical grouped-footprint colour reflection for the Packet
selector-faithfulness payload. Every canonical handle already decodes to one
grouped footprint proved to lie in the family carrier and to have
selector-relevant size. The computation below derives an executable colour
check from the size fact while retaining carrier-sublist evidence separately,
along with the earlier positive-charge, internal-source, authoritative-rank,
and ten-coordinate residual-descent reflections.

This internal colour check means only canonical grouped-footprint eligibility;
it is not an external manuscript colour equivalence. The five remaining
semantic payload Booleans, grouped-family construction, rank map, before/after
residual ranks, realizer claims, blocker activity, and dependency rows remain
explicit inputs. This module does not derive those inputs from a terminal
candidate, map every route into a complete global outcome system, construct a
no-lower ledger, prove complete route silence or unconditional HB negative
closure, establish ZeroSlack or PCCMin, prove polynomial runtime, put SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketChargeRouteReflection

namespace PNP
namespace DirectWire

/-! ## Computed colour, positive charge, source route, rank, and descent -/

/-- Replace the caller's colour bit with one executable canonical-footprint
    check and retain the positive-charge, exact-route, rank, and descent
    projections. -/
def TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  { payload.withComputedChargeExactRouteRankDescent expectedRank before after with
    colourChecked := colourCheck }

/-- The projection changes exactly colour, positive charge, the internal route
    bit, duplicate rank tag, and executable descent field. Five semantic fields
    are preserved. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_fields
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank
      before after).colourChecked = colourCheck ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).frontierChecked = payload.frontierChecked ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).chargeChecked = true ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).obligationChecked = payload.obligationChecked ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).activationChecked = payload.activationChecked ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).directionChecked = payload.directionChecked ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).budgetChecked = payload.budgetChecked ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).rankTag = expectedRank ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).exactRouteClear = true ∧
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).strictDescentClear = terminalResidualRankLTBool after before := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Acceptance depends on the computed colour check and five unresolved fields;
    charge, exact route, rank, and descent are already reflected. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_valid_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).Valid expectedRank ↔
      colourCheck = true ∧
        payload.frontierChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_true_iff]

/-- The colour route is exactly failure of the executable canonical-footprint
    check supplied to the projection. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_colour_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank
      before after).FailureAt expectedRank .colour ↔ colourCheck = false := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent]

/-- Canonical positive source mass makes the `.charge` failure proposition
    impossible. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).FailureAt expectedRank .charge ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Canonical rank reflection makes the `.rank` failure proposition
    impossible. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_rank_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).FailureAt expectedRank .rank ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Canonical source realization makes the internal `.exactRoute` failure
    proposition impossible. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).FailureAt expectedRank .exactRoute ↔ False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- An accepted canonical-footprint check excludes the colour route. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank)
    (colourAccepted : colourCheck = true) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank
      before after).firstRoute expectedRank ≠ some .colour := by
  intro found
  have failure :=
    ((payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank
      before after).firstRoute_eq_some_iff_failureAt expectedRank .colour).1 found
  have rejected :=
    (payload.withComputedColourChargeExactRouteRankDescent_failureAt_colour_iff
      colourCheck expectedRank before after).1 failure
  simp [colourAccepted] at rejected

/-- The executable classifier cannot return a source-charge failure. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute expectedRank ≠ some .charge := by
  intro found
  have failure :=
    ((payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .charge).1 found
  exact ((payload.withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false
    colourCheck expectedRank before after).1 failure).elim

/-- The executable classifier cannot return the duplicate finite-rank route. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute expectedRank ≠ some .rank := by
  intro found
  have failure :=
    ((payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .rank).1 found
  exact ((payload.withComputedColourChargeExactRouteRankDescent_failureAt_rank_iff_false
    colourCheck expectedRank before after).1 failure).elim

/-- The executable classifier cannot return the canonical internal-route
    failure. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute expectedRank ≠ some .exactRoute := by
  intro found
  have failure :=
    ((payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute_eq_some_iff_failureAt expectedRank .exactRoute).1 found
  exact ((payload.withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
      colourCheck expectedRank before after).1 failure).elim

/-- Exact final-route adequacy after all five canonical projections. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_failureAt_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).FailureAt expectedRank .descent ↔
      colourCheck = true ∧
        payload.frontierChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        ¬after.LexLT before := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    terminalResidualRankLTBool_eq_false_iff]

/-- The final route is reflected nondecrease after the computed colour check
    and all five remaining semantic fields accept. -/
theorem TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent_firstRoute_eq_some_descent_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank) :
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).firstRoute expectedRank = some .descent ↔
      colourCheck = true ∧
        payload.frontierChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        ¬after.LexLT before := by
  calc
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).firstRoute expectedRank = some .descent ↔
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).FailureAt expectedRank .descent :=
      (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
        ).firstRoute_eq_some_iff_failureAt expectedRank .descent
    _ ↔ _ := payload.withComputedColourChargeExactRouteRankDescent_failureAt_descent_iff
      colourCheck expectedRank
        before after

/-- Acceptance still exposes actual descent after all five canonical
    projections. -/
theorem TerminalPacketSelectorFaithfulnessPayload.rankDescent_of_withComputedColourChargeExactRouteRankDescent_check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (colourCheck : Bool)
    (expectedRank : Fin rankCount)
    (before after : TerminalResidualRank)
    (accepted : (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before
      after).check expectedRank = true) :
    after.LexLT before := by
  have valid :=
    (payload.withComputedColourChargeExactRouteRankDescent colourCheck expectedRank before after
      ).check_eq_true_iff expectedRank |>.1 accepted
  rcases (payload.withComputedColourChargeExactRouteRankDescent_valid_iff colourCheck expectedRank
      before after).1 valid with
    ⟨_colour, _frontier, _obligation, _activation, _direction,
      _budget, descent⟩
  exact descent

/-! ## Canonical grouped-family source realization -/

/-- Executable internal colour check: the decoded footprint must have
    selector-relevant size. Carrier-sublist membership remains a separate
    proof below rather than being hidden behind proposition-level `decide`. -/
def TerminalBN6GroupedFamily.packetSelectorCanonicalColourCheck
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) : Bool :=
  decide (2 ≤ (family.packetSelectorFootprint handle).length)

/-- Every canonical handle earns the internal colour check from the proofs
    already carried by its exact finite handle. -/
theorem TerminalBN6GroupedFamily.packetSelectorCanonicalColourEligibility
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorFootprint handle).Sublist family.carrier ∧
      family.packetSelectorCanonicalColourCheck handle = true := by
  exact ⟨family.packetSelectorFootprint_sublist_carrier handle, by
    simp [TerminalBN6GroupedFamily.packetSelectorCanonicalColourCheck,
      family.packetSelectorFootprint_large handle]⟩

/-- Canonical source payload with internal route, finite rank, and residual
    descent all reflected from their authoritative inputs. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent
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
    |>.withComputedColourChargeExactRouteRankDescent
      (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
      (beforeRank handle)
      (afterRank handle)

/-- Faithfulness computed from the same canonical source route, rank, and
    residual descent. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedColourChargeExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent rankOf
    beforeRank afterRank handle).check (rankOf handle)

/-- First route computed from the same five-way canonicalized payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent rankOf
    beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Exact earliest failure of the five-way canonicalized source payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent rankOf
    beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- Grouped-family route equality and exact canonicalized failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent_eq_some_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent rankOf
    beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
      (rankOf handle) route

/-- No canonical grouped-family handle can report failure of its proved
    grouped-footprint colour check. -/
theorem TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .colour :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
      (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
      (beforeRank handle) (afterRank handle)
      (family.packetSelectorCanonicalColourEligibility handle).2

/-- No canonical grouped-family handle can report a source-charge failure. -/
theorem TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .charge :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
      (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
      (beforeRank handle) (afterRank handle)

/-- No canonical grouped-family handle can report the duplicate rank route. -/
theorem TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .rank :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
      (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
      (beforeRank handle) (afterRank handle)

/-- No canonical grouped-family handle can report the reflected internal-route
    failure. -/
theorem TerminalBN6GroupedFamily.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .exactRoute :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
      (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
      (beforeRank handle) (afterRank handle)

/-- A final canonicalized route proves that the supplied residual transition
    does not decrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedColourChargeExactRouteRankDescent_firstRoute_descent
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  change
    ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedColourChargeExactRouteRankDescent
        (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
        (beforeRank handle) (afterRank handle)).firstRoute
          (rankOf handle) = some .descent at found
  rcases ((family.packetSelectorPayloadAtom handle).payload
      |>.withComputedColourChargeExactRouteRankDescent_firstRoute_eq_some_descent_iff
        (family.packetSelectorCanonicalColourCheck handle) (rankOf handle)
        (beforeRank handle) (afterRank handle)).1 found with
    ⟨_colour, _frontier, _obligation, _activation, _direction,
      _budget, notDescent⟩
  exact notDescent

/-! ## Canonicalized HB table and total outcome -/

/-- Rebuild only table faithfulness from the canonical source route, finite
    rank, and exact residual descent. Other executable inputs are retained. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
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
          family.packetSelectorPayloadFaithfulWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Canonicalization preserves every nonfaithfulness table input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness_preserves
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
    (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt table's faithfulness bit is definitionally the five-way
    canonical computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness_faithful
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedColourChargeExactRouteRankDescent
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces every positive Packet to expose an exact
    canonicalized failure. Grouped-footprint colour, source charge, and both
    duplicate routes are excluded; a final descent route carries actual
    nondecrease. -/
theorem TerminalBN6PacketConclusion.existsColourReflectedFirstRouteFailure_of_selectorSilence
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
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedColourChargeExactRouteRankDescent
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent_eq_some_iff
        table.environment.rankOf beforeRank afterRank handle route).1 found
  have notColour : route ≠ .colour := by
    intro isColour
    subst route
    exact family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
      table.environment.rankOf beforeRank afterRank handle found
  have notCharge : route ≠ .charge := by
    intro isCharge
    subst route
    exact family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
      table.environment.rankOf beforeRank afterRank handle found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
        table.environment.rankOf beforeRank afterRank handle found
  refine ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, ?_⟩
  by_cases isDescent : route = .descent
  · subst route
    exact Or.inr
      (family.not_rankDescent_of_computedColourChargeExactRouteRankDescent_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
  · exact Or.inl isDescent

/-- Named milestone endpoint: positive Packet plus executable HB silence gives
    one exact non-colour, non-charge, non-rank, non-exact-route failure; a final
    descent route proves the supplied ten-coordinate transition is
    nondecreasing. -/
theorem terminalBN6_packet_colour_reflected_hb_first_route_failure
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
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsColourReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
