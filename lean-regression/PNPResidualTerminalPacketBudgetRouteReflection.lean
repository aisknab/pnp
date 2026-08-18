import PNP.ResidualTerminalPacketBudgetRouteReflection

namespace PNP
namespace DirectWire
namespace PacketBudgetRouteReflectionRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev ActivationPayload (rankCount : Nat) :=
  TerminalPacketSelectorBN5ObligationPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat

abbrev DirectionPayload (rankCount : Nat) :=
  TerminalPacketSelectorBN5DirectionPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

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
    budgetChecked := false
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := false }

def activationPayload
    (activation frontier obligation : Nat) : ActivationPayload 2 :=
  { checks := baseChecks
    sourceCoordinate := coordinate 1 7 11
    selectorCoordinate := coordinate activation frontier obligation }

def directionPayload
    (activation frontier obligation direction : Nat) : DirectionPayload 2 :=
  { checks := activationPayload activation frontier obligation
    sourceDirection := 13
    selectorDirection := direction }

def equalBudgets : Payload 2 :=
  { checks := directionPayload 1 7 11 13
    sourceBudget := 17
    selectorBudget := 17 }

def unequalFrontiers : Payload 2 :=
  { checks := directionPayload 1 8 11 13
    sourceBudget := 17
    selectorBudget := 17 }

def unequalObligations : Payload 2 :=
  { checks := directionPayload 1 7 12 13
    sourceBudget := 17
    selectorBudget := 17 }

def unequalActivations : Payload 2 :=
  { checks := directionPayload 9 7 11 13
    sourceBudget := 17
    selectorBudget := 17 }

def unequalDirections : Payload 2 :=
  { checks := directionPayload 1 7 11 14
    sourceBudget := 17
    selectorBudget := 17 }

def unequalBudgets : Payload 2 :=
  { checks := directionPayload 1 7 11 13
    sourceBudget := 17
    selectorBudget := 18 }

example : equalBudgets.budgetCheck = true := by
  rfl

example : unequalBudgets.budgetCheck = false := by
  rfl

example : equalBudgets.sourceBudget = equalBudgets.selectorBudget :=
  (equalBudgets.budgetCheck_eq_true_iff).1 rfl

example : unequalBudgets.sourceBudget ≠ unequalBudgets.selectorBudget :=
  (unequalBudgets.budgetCheck_eq_false_iff).1 rfl

example : equalBudgets.checks.directionCheck = true := by
  rfl

example : unequalDirections.checks.directionCheck = false := by
  rfl

example : equalBudgets.checks.checks.frontierCheck = true := by
  rfl

example : unequalFrontiers.checks.checks.frontierCheck = false := by
  rfl

example : equalBudgets.checks.checks.obligationCheck = true := by
  rfl

example : unequalObligations.checks.checks.obligationCheck = false := by
  rfl

example : equalBudgets.checks.checks.activationCheck = true := by
  rfl

example : unequalActivations.checks.checks.activationCheck = false := by
  rfl

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .frontier ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier ≠
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_frontier_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .obligation ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_obligation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .activation ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_activation_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .direction ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceDirection ≠
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorDirection :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_direction_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .budget ↔
      (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom =
          (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom ∧
        (family.packetSelectorPayloadAtom handle).payload.checks.sourceDirection =
          (family.packetSelectorPayloadAtom handle).payload.checks.selectorDirection ∧
        (family.packetSelectorPayloadAtom handle).payload.sourceBudget ≠
          (family.packetSelectorPayloadAtom handle).payload.selectorBudget :=
  family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_budget_iff
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle ≠ some .colour :=
  family.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_colour
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle ≠ some .charge :=
  family.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_charge
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle ≠ some .rank :=
  family.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_rank
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle ≠ some .exactRoute :=
  family.computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_ne_some_exactRoute
    rankOf before after handle

example
    {Anchor : Type} [DecidableEq Anchor]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor (Payload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedBN5FrontierObligationActivationDirectionBudgetRoutes_firstRoute_descent
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
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf before after handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier ≠
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier) ∧
          (route ≠ .obligation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation)) ∧
          (route ≠ .activation ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom)) ∧
          (route ≠ .direction ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceDirection ≠
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorDirection)) ∧
          (route ≠ .budget ∨
            ((family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.frontier =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.frontier ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.obligation =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.obligation ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.checks.sourceCoordinate.key.atom =
                (family.packetSelectorPayloadAtom handle).payload.checks.checks.selectorCoordinate.key.atom ∧
              (family.packetSelectorPayloadAtom handle).payload.checks.sourceDirection =
                (family.packetSelectorPayloadAtom handle).payload.checks.selectorDirection ∧
              (family.packetSelectorPayloadAtom handle).payload.sourceBudget ≠
                (family.packetSelectorPayloadAtom handle).payload.selectorBudget)) ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_budget_reflected_hb_first_route_failure
    conclusion table dependencyTable before after silenceAccepted
      closureAccepted

end PacketBudgetRouteReflectionRegression
end DirectWire
end PNP
