/-
Copyright (c) 2026 PNP Labs.

BN4 activation-exact reflection for the Packet selector-faithfulness payload.
The complete BN5 coordinates already retain the nested BN4 activation keys.
This module compares their activation atoms directly instead of accepting an
independent `activationChecked` Boolean at the active canonical-payload
interface.

The construction is uniform over arbitrary finite grouped BN6 families,
finite rank carriers, and all coordinate-field types with the required
decidable equalities. It retains computed BN5 frontier and obligation checks,
grouped-footprint colour, positive source charge, the canonical source route,
the table-owned rank, and exact ten-coordinate residual descent. Equality is
proved equivalent to equality of the induced BN4 activation predicate on
every cut, so an activation route carries failure of that exact boundary.

Both complete BN5 coordinates, the grouped family, rank map, residual ranks,
realizer claims, blocker activity, and dependency rows remain explicit inputs.
This module does not construct those coordinates from terminal data, prove a
BN5 matching edge, derive the grouped family, or discharge external full-mode
obligations. Direction and budget remain explicit Booleans. It does not
establish complete route silence, unconditional HB negative closure,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, remove a project assumption,
or prove P = NP.
-/

import PNP.ResidualTerminalPacketBN5ObligationRouteReflection

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection : Type}
variable [DecidableEq Anchor]

/-! ## Exact BN4 activation comparison -/

/-- Executable equality of the activation atoms in the nested BN4 keys. -/
def TerminalPacketSelectorBN5ObligationPayload.activationCheck
    {rankCount : Nat} [DecidableEq ActivationAtom]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) : Bool :=
  decide
    (payload.sourceCoordinate.key.atom =
      payload.selectorCoordinate.key.atom)

/-- Activation acceptance is exactly equality of the two BN4 activation
    atoms. -/
theorem TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_true_iff
    {rankCount : Nat} [DecidableEq ActivationAtom]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.activationCheck = true ↔
      payload.sourceCoordinate.key.atom =
        payload.selectorCoordinate.key.atom := by
  simp [TerminalPacketSelectorBN5ObligationPayload.activationCheck]

/-- Activation rejection is exactly inequality of the two BN4 activation
    atoms. -/
theorem TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_false_iff
    {rankCount : Nat} [DecidableEq ActivationAtom]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.activationCheck = false ↔
      payload.sourceCoordinate.key.atom ≠
        payload.selectorCoordinate.key.atom := by
  simp [TerminalPacketSelectorBN5ObligationPayload.activationCheck]

/-- The executable comparison accepts exactly when the canonical BN4
    activation predicates agree on every cut. -/
theorem TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_true_iff_activation
    {rankCount : Nat} [DecidableEq ActivationAtom]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.activationCheck = true ↔
      ∀ cut,
        (TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.sourceCoordinate.key.atom) cut ↔
          TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.selectorCoordinate.key.atom)
              cut) := by
  rw [payload.activationCheck_eq_true_iff,
    ← terminalBN4ActivationCode_eq_iff]
  exact terminalBN4ActivationCode_eq_iff_activation _ _

/-- Rejection is precisely failure of extensional equality of the two BN4
    activation predicates. -/
theorem TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_false_iff_not_activation
    {rankCount : Nat} [DecidableEq ActivationAtom]
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.activationCheck = false ↔
      ¬ ∀ cut,
        (TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.sourceCoordinate.key.atom) cut ↔
          TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.selectorCoordinate.key.atom)
              cut) := by
  constructor
  · intro rejected equivalent
    have accepted : payload.activationCheck = true :=
      payload.activationCheck_eq_true_iff_activation.mpr equivalent
    simp [accepted] at rejected
  · intro notEquivalent
    cases checked : payload.activationCheck with
    | false => rfl
    | true =>
        exact False.elim
          (notEquivalent
            (payload.activationCheck_eq_true_iff_activation.mp checked))

/-! ## Canonical grouped-family computation -/

variable [DecidableEq ActivationAtom] [DecidableEq Frontier]
  [DecidableEq Obligation]

/-- Compute the BN5 frontier, obligation, and nested BN4 activation equalities
    while retaining every previously canonicalized Packet field. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorFaithfulnessPayload rankCount :=
  let source := (family.packetSelectorPayloadAtom handle).payload
  { (source.checks.withComputedColourChargeExactRouteRankDescent
      (family.packetSelectorCanonicalColourCheck handle)
      (rankOf handle) (beforeRank handle) (afterRank handle)) with
    frontierChecked := source.frontierCheck
    obligationChecked := source.obligationCheck
    activationChecked := source.activationCheck }

/-- Every output field is computed from its authoritative input or preserved
    from the selected source payload. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_fields
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    let computed := family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle
    computed.colourChecked =
        family.packetSelectorCanonicalColourCheck handle ∧
      computed.frontierChecked = source.frontierCheck ∧
      computed.chargeChecked = true ∧
      computed.obligationChecked = source.obligationCheck ∧
      computed.activationChecked = source.activationCheck ∧
      computed.directionChecked = source.checks.directionChecked ∧
      computed.budgetChecked = source.checks.budgetChecked ∧
      computed.rankTag = rankOf handle ∧
      computed.exactRouteClear = true ∧
      computed.strictDescentClear =
        terminalResidualRankLTBool (afterRank handle) (beforeRank handle) := by
  simp [
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent]

/-- Validity depends on exact BN5 frontier and obligation equality, exact BN4
    activation equality, the two unresolved fields, and residual descent. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_valid_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).Valid (rankOf handle) ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.sourceCoordinate.key.atom =
          source.selectorCoordinate.key.atom ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        (afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.Valid,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_true_iff]

/-- Canonical grouped-footprint eligibility makes the colour route
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_colour_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .colour ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- A frontier failure is exactly inequality of the two BN5 frontier fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .frontier ↔
      source.sourceCoordinate.frontier ≠
        source.selectorCoordinate.frontier := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Canonical positive source mass makes the charge route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_charge_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .charge ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent]

/-- An obligation failure occurs after frontier acceptance and is exactly
    inequality of the two BN5 obligation fields. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .obligation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation ≠
          source.selectorCoordinate.obligation := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- An activation failure occurs after both earlier BN5 equalities and is
    exactly inequality of the nested BN4 activation atoms. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_activation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt
        (rankOf handle) .activation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.sourceCoordinate.key.atom ≠
          source.selectorCoordinate.key.atom := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2]

/-- Table-owned rank reflection makes the rank route impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_rank_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .rank ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- Canonical source realization makes the internal exact-route failure
    impossible. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_exactRoute_iff_false
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .exactRoute ↔
      False := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent]

/-- The final route retains exact nondecrease semantics after both BN5 checks,
    exact BN4 activation, and the two unresolved fields accept. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_descent_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).FailureAt (rankOf handle) .descent ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.sourceCoordinate.key.atom =
          source.selectorCoordinate.key.atom ∧
        source.checks.directionChecked = true ∧
        source.checks.budgetChecked = true ∧
        ¬(afterRank handle).LexLT (beforeRank handle) := by
  simp [TerminalPacketSelectorFaithfulnessPayload.FailureAt,
    TerminalBN6GroupedFamily.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes,
    TerminalPacketSelectorBN5ObligationPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.toTypedFrontier,
    TerminalPacketSelectorTypedFrontierPayload.frontierCheck,
    TerminalPacketSelectorBN5ObligationPayload.obligationCheck,
    TerminalPacketSelectorBN5ObligationPayload.activationCheck,
    TerminalPacketSelectorFaithfulnessPayload.withComputedColourChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedChargeExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedExactRouteRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedRankDescent,
    TerminalPacketSelectorFaithfulnessPayload.withComputedDescent,
    (family.packetSelectorCanonicalColourEligibility handle).2,
    terminalResidualRankLTBool_eq_false_iff]

/-! ## Exact first-route semantics -/

/-- Faithfulness computed from the two BN5 fields, the BN4 activation field,
    and all previously canonicalized fields. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
    rankOf beforeRank afterRank handle).check (rankOf handle)

/-- First route from the same BN5-bound canonical payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
    rankOf beforeRank afterRank handle).firstRoute (rankOf handle)

/-- Exact failure proposition for the same BN5-bound payload. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
    rankOf beforeRank afterRank handle).FailureAt (rankOf handle) route

/-- Route equality and exact BN5-bound failure coincide. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some route ↔
      family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle route :=
  (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
    rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
      (rankOf handle) route

/-- The frontier route means exactly BN5 frontier inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_frontier_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .frontier ↔
      source.sourceCoordinate.frontier ≠
        source.selectorCoordinate.frontier := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .frontier ↔
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).FailureAt
          (rankOf handle) .frontier :=
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .frontier
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_frontier_iff
        rankOf beforeRank afterRank handle

/-- The obligation route means accepted BN5 frontier equality followed by
    BN5 obligation inequality. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_obligation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .obligation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation ≠
          source.selectorCoordinate.obligation := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .obligation ↔
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).FailureAt
          (rankOf handle) .obligation :=
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .obligation
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_obligation_iff
        rankOf beforeRank afterRank handle

/-- The activation route means accepted BN5 frontier and obligation fields
    followed by inequality of the nested BN4 activation atoms. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_activation_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    let source := (family.packetSelectorPayloadAtom handle).payload
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .activation ↔
      source.sourceCoordinate.frontier = source.selectorCoordinate.frontier ∧
        source.sourceCoordinate.obligation =
          source.selectorCoordinate.obligation ∧
        source.sourceCoordinate.key.atom ≠
          source.selectorCoordinate.key.atom := by
  calc
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .activation ↔
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).FailureAt
          (rankOf handle) .activation :=
      (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle).firstRoute_eq_some_iff_failureAt
          (rankOf handle) .activation
    _ ↔ _ :=
      family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_activation_iff
        rankOf beforeRank afterRank handle

/-- No canonical BN5-bound payload can report colour failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_colour
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle ≠ some .colour := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .colour).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_colour_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report source-charge failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_charge
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle ≠ some .charge := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .charge).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_charge_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report duplicate rank failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_rank
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle ≠ some .rank := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .rank).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_rank_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- No canonical BN5-bound payload can report internal source-route failure. -/
theorem TerminalBN6GroupedFamily.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_exactRoute
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle ≠ some .exactRoute := by
  intro found
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .exactRoute).1 found
  exact
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_exactRoute_iff_false
      rankOf beforeRank afterRank handle).1 failure).elim

/-- A final route proves exact ten-coordinate nondecrease. -/
theorem TerminalBN6GroupedFamily.not_rankDescent_of_computedBN5FrontierObligationActivationRoutes_firstRoute_descent
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = some .descent) :
    ¬(afterRank handle).LexLT (beforeRank handle) := by
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      rankOf beforeRank afterRank handle .descent).1 found
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_failureAt_descent_iff
      rankOf beforeRank afterRank handle).1 failure |>.2.2.2.2.2

/-- Accepted BN5-bound faithfulness retains actual residual descent. -/
theorem TerminalBN6GroupedFamily.rankDescent_of_packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (accepted :
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes
        rankOf beforeRank afterRank handle = true) :
    (afterRank handle).LexLT (beforeRank handle) := by
  have valid :=
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      rankOf beforeRank afterRank handle).check_eq_true_iff (rankOf handle)
      |>.1 accepted
  exact
    (family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes_valid_iff
      rankOf beforeRank afterRank handle).1 valid |>.2.2.2.2.2

/-! ## Canonicalized HB table and positive-Packet endpoint -/

/-- Rebuild table faithfulness from both BN5 equalities and all previously
    canonicalized fields. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful :=
          family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf beforeRank afterRank
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- BN5-bound canonicalization preserves every nonfaithfulness table input. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness_preserves
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (rank : Fin rankCount) :
    (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
      beforeRank afterRank).environment.rankOf handle =
        table.environment.rankOf handle ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).environment.hnActive rank =
          table.environment.hnActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).environment.budgetActive rank =
          table.environment.budgetActive rank ∧
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).claim handle = table.claim handle := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The rebuilt faithfulness bit is definitionally the BN5-bound
    computation. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness_faithful
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
      beforeRank afterRank).environment.faithful handle =
      family.packetSelectorPayloadFaithfulWithComputedBN5FrontierObligationActivationRoutes
        table.environment.rankOf beforeRank afterRank handle :=
  rfl

/-- Executable HB silence forces a positive Packet to expose exact BN5 field
    evidence or an exact later route. -/
theorem TerminalBN6PacketConclusion.existsBN4ActivationReflectedFirstRouteFailure_of_selectorSilence
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.key.atom)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
      beforeRank afterRank).noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted handle
  rw [table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness_faithful
      beforeRank afterRank handle] at computedRejected
  obtain ⟨route, found⟩ :=
    ((family.packetSelectorPayloadWithComputedBN5FrontierObligationActivationRoutes
      table.environment.rankOf beforeRank afterRank handle
      ).exists_firstRoute_iff_check_eq_false
        (table.environment.rankOf handle)).2 computedRejected
  have failure :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_iff
      table.environment.rankOf beforeRank afterRank handle route).1 found
  have notColour : route ≠ .colour := by
    intro isColour
    subst route
    exact family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_colour
      table.environment.rankOf beforeRank afterRank handle found
  have notCharge : route ≠ .charge := by
    intro isCharge
    subst route
    exact family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_charge
      table.environment.rankOf beforeRank afterRank handle found
  have notRank : route ≠ .rank := by
    intro isRank
    subst route
    exact family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_rank
      table.environment.rankOf beforeRank afterRank handle found
  have notExactRoute : route ≠ .exactRoute := by
    intro isExactRoute
    subst route
    exact family.computedBN5FrontierObligationActivationRoutes_firstRoute_ne_some_exactRoute
      table.environment.rankOf beforeRank afterRank handle found
  have frontierMeaning :
      route ≠ .frontier ∨
        (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier := by
    by_cases isFrontier : route = .frontier
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_frontier_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isFrontier
  have obligationMeaning :
      route ≠ .obligation ∨
        ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation) := by
    by_cases isObligation : route = .obligation
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_obligation_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isObligation
  have activationMeaning :
      route ≠ .activation ∨
        ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
          (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation =
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation ∧
          (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.key.atom ≠
            (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.key.atom) := by
    by_cases isActivation : route = .activation
    · subst route
      exact Or.inr
        ((family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes_eq_some_activation_iff
          table.environment.rankOf beforeRank afterRank handle).1 found)
    · exact Or.inl isActivation
  have descentMeaning :
      route ≠ .descent ∨
        ¬(afterRank handle).LexLT (beforeRank handle) := by
    by_cases isDescent : route = .descent
    · subst route
      exact Or.inr
        (family.not_rankDescent_of_computedBN5FrontierObligationActivationRoutes_firstRoute_descent
          table.environment.rankOf beforeRank afterRank handle found)
    · exact Or.inl isDescent
  exact ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, frontierMeaning, obligationMeaning, activationMeaning,
    descentMeaning⟩

/-- Named milestone endpoint: a positive Packet under executable HB silence
    exposes exact BN5 frontier/obligation evidence or an exact later route. -/
theorem terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5ObligationPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorCoordinate.key.atom)) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsBN4ActivationReflectedFirstRouteFailure_of_selectorSilence
    table dependencyTable beforeRank afterRank silenceAccepted closureAccepted

end DirectWire
end PNP
