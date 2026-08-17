import PNP.ResidualTerminalPacketChargeRouteReflection

namespace PNP
namespace DirectWire
namespace PacketChargeRouteReflectionRegression

def forgedRoutePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { colourChecked := true
    frontierChecked := true
    chargeChecked := false
    obligationChecked := true
    activationChecked := true
    directionChecked := true
    budgetChecked := true
    rankTag := 1
    exactRouteClear := false
    strictDescentClear := true }

def colourFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with colourChecked := false }

def frontierFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with frontierChecked := false }

def chargeFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with chargeChecked := false }

def obligationFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with obligationChecked := false }

def activationFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with activationChecked := false }

def directionFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with directionChecked := false }

def budgetFailurePayload : TerminalPacketSelectorFaithfulnessPayload 2 :=
  { forgedRoutePayload with budgetChecked := false }

def beforeRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 1

def smallerAfterRank : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).rankTag = 0 := by
  rfl

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).exactRouteClear = true := by
  rfl

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).chargeChecked = true := by
  rfl

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).firstRoute 0 = some .descent := by
  rfl

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .rank :=
  forgedRoutePayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_rank
    0 beforeRank beforeRank

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .charge :=
  forgedRoutePayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_charge
    0 beforeRank beforeRank

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .exactRoute :=
  forgedRoutePayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
      0 beforeRank beforeRank

example :
    ¬(forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).FailureAt 0 .exactRoute := by
  intro routeFailure
  exact ((forgedRoutePayload.withComputedChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
      0 beforeRank beforeRank).1 routeFailure).elim

example :
    ¬(forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      beforeRank).FailureAt 0 .charge := by
  intro routeFailure
  exact ((forgedRoutePayload.withComputedChargeExactRouteRankDescent_failureAt_charge_iff_false
      0 beforeRank beforeRank).1 routeFailure).elim

example :
    (forgedRoutePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = none := by
  rfl

example :
    (colourFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .colour := by
  rfl

example :
    (frontierFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .frontier := by
  rfl

example :
    (chargeFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 ≠ some .charge :=
  chargeFailurePayload.withComputedChargeExactRouteRankDescent_firstRoute_ne_some_charge
    0 beforeRank smallerAfterRank

example :
    (obligationFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .obligation := by
  rfl

example :
    (activationFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .activation := by
  rfl

example :
    (directionFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .direction := by
  rfl

example :
    (budgetFailurePayload.withComputedChargeExactRouteRankDescent 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .budget := by
  rfl

example : smallerAfterRank.LexLT beforeRank := by
  apply forgedRoutePayload.rankDescent_of_withComputedChargeExactRouteRankDescent_check
      (expectedRank := 0) beforeRank smallerAfterRank
  rfl

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent
        rankOf before after handle ≠ some .charge :=
  family.computedChargeExactRouteRankDescent_firstRoute_ne_some_charge rankOf
    before after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent
        rankOf before after handle ≠ some .rank :=
  family.computedChargeExactRouteRankDescent_firstRoute_ne_some_rank rankOf before
    after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent
        rankOf before after handle ≠ some .exactRoute :=
  family.computedChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute rankOf
    before after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle)
    (found :
      family.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedChargeExactRouteRankDescent_firstRoute_descent
    rankOf before after handle found

example
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorChargeExactRouteRankDescentFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorChargeExactRouteRankDescentFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedChargeExactRouteRankDescent
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedChargeExactRouteRankDescent
            table.environment.rankOf before after handle route ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_charge_reflected_hb_first_route_failure conclusion
    table dependencyTable before after silenceAccepted closureAccepted

end PacketChargeRouteReflectionRegression
end DirectWire
end PNP
