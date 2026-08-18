import PNP.ResidualTerminalPacketDirectionRouteReflection

namespace PNP
namespace DirectWire
namespace PacketDirectionRouteReflectionRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev ActivationPayload (rankCount : Nat) :=
  TerminalPacketSelectorBN5ObligationPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5DirectionPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate (activation frontier obligation : Nat) : Coordinate :=
  { key :=
      { atom := activation
        semanticSignature := 2
        transportType := 3 }
    frontier := frontier
    chargeOwner := 4
    obligation := obligation
    originKernel := 5
    modeProjection := 6 }

def baseChecks : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { colourChecked := false
    frontierChecked := false
    chargeChecked := false
    obligationChecked := false
    activationChecked := false
    directionChecked := false
    budgetChecked := true
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := false }

def activationPayload
    (activation frontier obligation : Nat) : ActivationPayload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate activation frontier obligation }

def equalDirections : Payload 2 :=
  { checks := activationPayload 1 7 11
    sourceDirection := 13
    selectorDirection := 13 }

def unequalFrontiers : Payload 2 :=
  { checks := activationPayload 1 8 11
    sourceDirection := 13
    selectorDirection := 13 }

def unequalObligations : Payload 2 :=
  { checks := activationPayload 1 7 12
    sourceDirection := 13
    selectorDirection := 13 }

def unequalActivations : Payload 2 :=
  { checks := activationPayload 9 7 11
    sourceDirection := 13
    selectorDirection := 13 }

def unequalDirections : Payload 2 :=
  { checks := activationPayload 1 7 11
    sourceDirection := 13
    selectorDirection := 14 }

example : equalDirections.directionCheck = true := by
  rfl

example : unequalDirections.directionCheck = false := by
  rfl

example : equalDirections.sourceDirection = equalDirections.selectorDirection :=
  (equalDirections.directionCheck_eq_true_iff).1 rfl

example : unequalDirections.sourceDirection ≠ unequalDirections.selectorDirection :=
  (unequalDirections.directionCheck_eq_false_iff).1 rfl

example : equalDirections.checks.frontierCheck = true := by
  rfl

example : unequalFrontiers.checks.frontierCheck = false := by
  rfl

example : equalDirections.checks.obligationCheck = true := by
  rfl

example : unequalObligations.checks.obligationCheck = false := by
  rfl

example : equalDirections.checks.activationCheck = true := by
  rfl

example : unequalActivations.checks.activationCheck = false := by
  rfl

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle = some .frontier ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier ≠
        (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_frontier_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle = some .obligation ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_obligation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle = some .activation ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_activation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle = some .direction ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceDirection ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorDirection :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes_eq_some_direction_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle ≠ some .colour :=
  family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_colour
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle ≠ some .charge :=
  family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_charge
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle ≠ some .rank :=
  family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_rank
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle ≠ some .exactRoute :=
  family.computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_ne_some_exactRoute
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionRoutes_firstRoute_descent
    rankOf before after handle found

example
    {Anchor : Type} [DecidableEq Anchor]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor (Payload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionRoutes
            table.environment.rankOf before after handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom)) ∧
          (route ≠ .direction ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceCoordinate.key.atom =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorCoordinate.key.atom ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceDirection ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorDirection)) ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_direction_reflected_hb_first_route_failure
    conclusion table dependencyTable before after silenceAccepted
      closureAccepted

end PacketDirectionRouteReflectionRegression
end DirectWire
end PNP
