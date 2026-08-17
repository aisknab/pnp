import PNP.ResidualTerminalPacketColourRouteReflection

namespace PNP
namespace DirectWire
namespace PacketColourRouteReflectionRegression

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
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).rankTag = 0 := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).exactRouteClear = true := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).chargeChecked = true := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).firstRoute 0 = some .descent := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .rank :=
  forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank
    true 0 beforeRank beforeRank

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .charge :=
  forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    true 0 beforeRank beforeRank

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).firstRoute 0 ≠ some .exactRoute :=
  forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute
      true 0 beforeRank beforeRank

example :
    ¬(forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).FailureAt 0 .exactRoute := by
  intro routeFailure
  exact ((forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_failureAt_exactRoute_iff_false
      true 0 beforeRank beforeRank).1 routeFailure).elim

example :
    ¬(forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      beforeRank).FailureAt 0 .charge := by
  intro routeFailure
  exact ((forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_failureAt_charge_iff_false
      true 0 beforeRank beforeRank).1 routeFailure).elim

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = none := by
  rfl

example :
    (colourFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = none := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent false 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .colour := by
  rfl

example :
    (forgedRoutePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 ≠ some .colour :=
  forgedRoutePayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour
    true 0 beforeRank smallerAfterRank rfl

example :
    (frontierFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .frontier := by
  rfl

example :
    (chargeFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 ≠ some .charge :=
  chargeFailurePayload.withComputedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge
    true 0 beforeRank smallerAfterRank

example :
    (obligationFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .obligation := by
  rfl

example :
    (activationFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .activation := by
  rfl

example :
    (directionFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .direction := by
  rfl

example :
    (budgetFailurePayload.withComputedColourChargeExactRouteRankDescent true 0 beforeRank
      smallerAfterRank).firstRoute 0 = some .budget := by
  rfl

example : smallerAfterRank.LexLT beforeRank := by
  apply forgedRoutePayload.rankDescent_of_withComputedColourChargeExactRouteRankDescent_check
      (colourCheck := true) (expectedRank := 0) beforeRank smallerAfterRank
  rfl

example
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorCanonicalColourCheck handle = true :=
  (family.packetSelectorCanonicalColourEligibility handle).2

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .colour :=
  family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_colour rankOf
    before after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .charge :=
  family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_charge rankOf
    before after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .rank :=
  family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_rank rankOf before
    after handle

example
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (before after : family.PacketSelectorHandle → TerminalResidualRank)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf before after handle ≠ some .exactRoute :=
  family.computedColourChargeExactRouteRankDescent_firstRoute_ne_some_exactRoute rankOf
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
      family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
        rankOf before after handle = some .descent) :
    ¬(after handle).LexLT (before handle) :=
  family.not_rankDescent_of_computedColourChargeExactRouteRankDescent_firstRoute_descent
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
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorColourChargeExactRouteRankDescentFaithfulness
        before after).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf before after handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedColourChargeExactRouteRankDescent
            table.environment.rankOf before after handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_colour_reflected_hb_first_route_failure conclusion
    table dependencyTable before after silenceAccepted closureAccepted

end PacketColourRouteReflectionRegression
end DirectWire
end PNP
