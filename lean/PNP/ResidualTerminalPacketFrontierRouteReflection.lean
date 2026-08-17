/-
Copyright (c) 2026 PNP Labs.

Typed frontier-signature reflection for the Packet selector-faithfulness
payload. The current Packet boundary accepts a free Boolean
`frontierChecked`. This module replaces that input at the active
canonical-payload interface with executable equality of an explicit source
frontier signature and an explicit selector frontier signature.

The construction remains uniform over arbitrary finite grouped BN6 families,
arbitrary finite rank carriers, and arbitrary frontier types with decidable
equality. It retains the previously computed grouped-footprint colour,
positive source charge, canonical source route, table-owned rank, and exact
ten-coordinate residual-descent checks. A returned frontier route therefore
carries a typed signature inequality rather than only a rejected Boolean.

Both frontier signatures, the grouped family, rank map, before/after residual
ranks, realizer claims, blocker activity, and dependency rows remain explicit
inputs. Equality of the supplied signatures is not a construction of either
signature from terminal data, a binding to a BN5 coordinate, or the
manuscript's full frontier-faithful comparison theorem. The obligation,
activation, direction, and budget fields remain explicit Booleans. This
module does not establish complete route silence, unconditional HB negative
closure, ZeroSlack, PCCMin, polynomial runtime, SAT in P, remove a project
assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketColourRouteReflection

namespace PNP
namespace DirectWire

/-! ## Typed frontier payload and executable equality -/

/-- The selected positive source payload together with the two typed frontier
    signatures compared by the Packet selector boundary. -/
structure TerminalPacketSelectorTypedFrontierPayload
    (rankCount : Nat) (Frontier : Type) where
  checks : TerminalPacketSelectorFaithfulnessPayload rankCount
  sourceFrontier : Frontier
  selectorFrontier : Frontier
deriving DecidableEq

/-- Executable equality of the source and selector frontier signatures. -/
def TerminalPacketSelectorTypedFrontierPayload.frontierCheck
    {rankCount : Nat} {Frontier : Type} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorTypedFrontierPayload rankCount Frontier) :
    Bool :=
  decide (payload.sourceFrontier = payload.selectorFrontier)

/-- The executable frontier checker accepts exactly typed signature equality. -/
theorem TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_true_iff
    {rankCount : Nat} {Frontier : Type} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorTypedFrontierPayload rankCount Frontier) :
    payload.frontierCheck = true ↔
      payload.sourceFrontier = payload.selectorFrontier := by
  simp [TerminalPacketSelectorTypedFrontierPayload.frontierCheck]

/-- Rejection is exactly typed frontier-signature inequality. -/
theorem TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_false_iff
    {rankCount : Nat} {Frontier : Type} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorTypedFrontierPayload rankCount Frontier) :
    payload.frontierCheck = false ↔
      payload.sourceFrontier ≠ payload.selectorFrontier := by
  simp [TerminalPacketSelectorTypedFrontierPayload.frontierCheck]

/-! ## Canonical grouped-family computation -/

/-- Compute frontier equality while retaining the canonical colour, charge,
    source-route, finite-rank, and residual-descent projections. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  { ((family.packetSelectorPayloadAtom handle).payload.checks
      |>.withComputedColourChargeExactRouteRankDescent
        (family.packetSelectorCanonicalColourCheck handle)
        (rankOf handle) (beforeRank handle) (afterRank handle)) with
    frontierChecked :=
      (family.packetSelectorPayloadAtom handle).payload.frontierCheck }

/-- Every output field is either computed from its authoritative input or
    preserved from the selected source payload. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_fields
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    let computed :=
      family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle
    computed.colourChecked =
        family.packetSelectorCanonicalColourCheck handle ∧
      computed.frontierChecked = source.frontierCheck ∧
      computed.chargeChecked = true ∧
      computed.obligationChecked = source.checks.obligationChecked ∧
      computed.activationChecked = source.checks.activationChecked ∧
      computed.directionChecked = source.checks.directionChecked ∧
      computed.budgetChecked = source.checks.budgetChecked ∧
      computed.rankTag = rankOf handle ∧
      computed.exactRouteClear = true ∧
      computed.strictDescentClear =
        terminalResidualRankLTBool (afterRank handle) (beforeRank handle) := by
  simp [
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Validity now depends on exact typed frontier equality and the four
    unresolved semantic fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_valid_iff
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).Valid (rankOf handle) ↔
      source.sourceFrontier = source.selectorFrontier ∧
        source.checks.obligationChecked = true ∧
        source.checks.activationChecked = true ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        (afterRank handle).LexLT (beforeRank handle) := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_true_iff]

/-- Canonical grouped-footprint eligibility makes the colour route
    impossible at this typed frontier boundary. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_colour_iff_false
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .colour ↔
      False := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- A frontier failure is exactly inequality of the two supplied typed
    signatures. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_frontier_iff
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .frontier ↔
      source.sourceFrontier ≠ source.selectorFrontier := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Canonical positive source mass makes the charge route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_charge_iff_false
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .charge ↔
      False := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent]

/-- Table-owned rank reflection makes the rank route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_rank_iff_false
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .rank ↔
      False := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- Canonical source realization makes the internal exact-route failure
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .exactRoute ↔
      False := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- The final route retains exact nondecrease semantics after the typed
    frontier check and the four unresolved fields accept. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_descent_iff
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .descent ↔
      source.sourceFrontier = source.selectorFrontier ∧
        source.checks.obligationChecked = true ∧
        source.checks.activationChecked = true ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        ¬(afterRank handle).LexLT (beforeRank handle) := by
  simp [
    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_false_iff]

/-! ## Exact first-route semantics -/

/-- Faithfulness computed from the typed frontier and the five previously
    canonicalized fields. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
    rankOf beforeRank afterRank handle).check (rankOf handle)

/-- First route from the same typed-frontier canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
    rankOf beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Exact failure proposition for the same typed-frontier payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
    rankOf beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- Route equality and exact typed-frontier failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
    rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
      (rankOf handle) route

/-- The frontier route now means exactly typed signature inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some .frontier ↔
      source.sourceFrontier ≠ source.selectorFrontier := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some .frontier ↔
      (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .frontier :=
      (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .frontier
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_frontier_iff
        rankOf beforeRank afterRank handle

/-- Equal typed signatures exclude the frontier route. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_ne_some_frontier_of_eq
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (equal :
      (family.packetSelectorPayloadAtom handle).payload.sourceFrontier =
        (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .frontier := by
  intro found
  exact
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff
      rankOf beforeRank afterRank handle).1 found equal

/-- No canonical typed-frontier payload can report colour failure. -/
theorem TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .colour := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      rankOf beforeRank afterRank handle .colour).1 found
  exact
    ((family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_colour_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical typed-frontier payload can report source-charge failure. -/
theorem TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .charge := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      rankOf beforeRank afterRank handle .charge).1 found
  exact
    ((family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_charge_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical typed-frontier payload can report duplicate rank failure. -/
theorem TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .rank := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      rankOf beforeRank afterRank handle .rank).1 found
  exact
    ((family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_rank_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical typed-frontier payload can report the internal source-route
    failure. -/
theorem TerminalBN6GroupedFamily.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle ≠ some .exactRoute := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      rankOf beforeRank afterRank handle .exactRoute).1 found
  exact
    ((family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- A final route still proves exact ten-coordinate nondecrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_descent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      rankOf beforeRank afterRank handle .descent).1 found
  exact
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_failureAt_descent_iff
      rankOf beforeRank afterRank handle).1 failure |>.2.2.2.2.2

/-- Accepted typed-frontier faithfulness retains actual residual descent. -/
theorem TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (accepted :
      family.packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent
        rankOf beforeRank afterRank handle = true) :
    (afterRank handle).LexLT (beforeRank handle) := by
  have valid :=
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      rankOf beforeRank afterRank handle).check_eq_true_iff (rankOf handle)
      |>.1 accepted
  exact
    (family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent_valid_iff
      rankOf beforeRank afterRank handle).1 valid |>.2.2.2.2.2

/-! ## Canonicalized HB table and positive-Packet endpoint -/

/-- Rebuild table faithfulness from the typed frontier equality and all
    previously canonicalized fields. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful :=
          family.packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Typed-frontier canonicalization preserves every nonfaithfulness table
    input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness_preserves
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (rank : Fin rankCount) :
    (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt faithfulness bit is definitionally the typed-frontier
    computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness_faithful
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedTypedFrontierColourChargeExactRouteRankDescent
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces a positive Packet to expose exact failure
    evidence. A frontier route carries typed inequality; a final descent route
    carries exact nondecrease. -/
theorem TerminalBN6PacketConclusion.existsTypedFrontierReflectedFirstRouteFailure_of_selectorSilence
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedTypedFrontierColourChargeExactRouteRankDescent
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  have notColour : route ≠ .colour := by
    intro isColour
    subst route
    exact family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
      table.environment.rankOf beforeRank afterRank handle found
  have notCharge : route ≠ .charge := by
    intro isCharge
    subst route
    exact family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
      table.environment.rankOf beforeRank afterRank handle found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
      table.environment.rankOf beforeRank afterRank handle found
  have frontierMeaning :
      route ≠ .frontier ∨
        (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorFrontier := by
    by_cases isFrontier : route = .frontier
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent_eq_some_frontier_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isFrontier
  have descentMeaning :
      route ≠ .descent ∨
        ¬(afterRank handle).LexLT (beforeRank handle) := by
    by_cases isDescent : route = .descent
    · subst route
      exact Or.inr
        (family.not_rankDescent_of_computedTypedFrontierColourChargeExactRouteRankDescent_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
    · exact Or.inl isDescent
  exact ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, frontierMeaning, descentMeaning⟩

/-- Named milestone endpoint: a positive Packet under executable HB silence
    exposes one exact non-colour, non-charge, non-rank, non-exact-route
    failure. Frontier means typed inequality and descent means nondecrease. -/
theorem terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsTypedFrontierReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
