import PNP.ResidualTerminalPacketSelectorFirstRouteSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace FirstRouteSemanticsRegression

private def acceptedPayload :
    TerminalPacketSelectorFaithfulnessPayload 2 where
  colourChecked := true
  frontierChecked := true
  chargeChecked := true
  obligationChecked := true
  activationChecked := true
  directionChecked := true
  budgetChecked := true
  rankTag := 0
  exactRouteClear := true
  strictDescentClear := true

/-! ## Every closed route constructor has its exact earliest-field meaning -/

example :
    ({ acceptedPayload with colourChecked := false }).firstRoute 0 = some .colour ∧
      ({ acceptedPayload with colourChecked := false }).FailureAt 0 .colour := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt]

example :
    ({ acceptedPayload with frontierChecked := false }).firstRoute 0 = some .frontier ∧
      ({ acceptedPayload with frontierChecked := false }).FailureAt 0 .frontier := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with chargeChecked := false }).firstRoute 0 = some .charge ∧
      ({ acceptedPayload with chargeChecked := false }).FailureAt 0 .charge := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with obligationChecked := false }).firstRoute 0 = some .obligation ∧
      ({ acceptedPayload with obligationChecked := false }).FailureAt 0 .obligation := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with activationChecked := false }).firstRoute 0 = some .activation ∧
      ({ acceptedPayload with activationChecked := false }).FailureAt 0 .activation := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with directionChecked := false }).firstRoute 0 = some .direction ∧
      ({ acceptedPayload with directionChecked := false }).FailureAt 0 .direction := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with budgetChecked := false }).firstRoute 0 = some .budget ∧
      ({ acceptedPayload with budgetChecked := false }).FailureAt 0 .budget := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with rankTag := (1 : Fin 2) }).firstRoute 0 = some .rank ∧
      ({ acceptedPayload with rankTag := (1 : Fin 2) }).FailureAt 0 .rank := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with exactRouteClear := false }).firstRoute 0 = some .exactRoute ∧
      ({ acceptedPayload with exactRouteClear := false }).FailureAt 0 .exactRoute := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

example :
    ({ acceptedPayload with strictDescentClear := false }).firstRoute 0 = some .descent ∧
      ({ acceptedPayload with strictDescentClear := false }).FailureAt 0 .descent := by
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
    TerminalPacketSelectorFaithfulnessPayload.FailureAt, acceptedPayload]

/-! ## Generic and grouped-family contracts -/

example
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    payload.firstRoute expectedRank = some route ↔
      payload.FailureAt expectedRank route :=
  payload.firstRoute_eq_some_iff_failureAt expectedRank route

example
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.check expectedRank = false ↔
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        payload.FailureAt expectedRank route :=
  payload.check_eq_false_iff_exists_failureAt expectedRank

example
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    {left right : TerminalPacketSelectorFaithfulnessRoute}
    (leftFailure : payload.FailureAt expectedRank left)
    (rightFailure : payload.FailureAt expectedRank right) :
    left = right :=
  payload.failureAt_unique expectedRank leftFailure rightFailure

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom
  (TerminalPacketSelectorFaithfulnessPayload rankCount)}

example
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRoute rankOf handle = some route ↔
      family.packetSelectorPayloadFailureAt rankOf handle route :=
  family.packetSelectorPayloadFirstRoute_eq_some_iff_failureAt
    rankOf handle route

example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted :
      (table.withComputedPacketSelectorFaithfulness
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorFaithfulness
        ).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRoute
            table.environment.rankOf handle = some route ∧
          family.packetSelectorPayloadFailureAt
            table.environment.rankOf handle route :=
  terminalBN6_packet_computed_faithfulness_hb_first_route_failure
    conclusion table dependencyTable silenceAccepted closureAccepted

end FirstRouteSemanticsRegression
end DirectWire
end PNP
