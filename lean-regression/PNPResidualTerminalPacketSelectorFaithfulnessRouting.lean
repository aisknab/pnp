import PNP.ResidualTerminalPacketSelectorFaithfulnessRouting

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom
  (TerminalPacketSelectorFaithfulnessPayload rankCount)}

/-! ## Exact payload checks and first-failure routes -/

/-- Payload acceptance is exactly the complete data-only validity boundary. -/
example
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.check expectedRank = true ↔ payload.Valid expectedRank :=
  payload.check_eq_true_iff expectedRank

/-- Accepted payloads expose no route, while every exposed typed route rejects
    the same payload/rank pair. -/
example
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (accepted : payload.check expectedRank = true) :
    payload.firstRoute expectedRank = none :=
  payload.firstRoute_eq_none_of_check expectedRank accepted

example
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (route : TerminalPacketSelectorFaithfulnessRoute)
    (found : payload.firstRoute expectedRank = some route) :
    payload.check expectedRank = false :=
  payload.check_eq_false_of_firstRoute expectedRank route found

/-! ## Exhaustive family and HB-table binding -/

/-- Route-clear acceptance covers every canonical handle in the arbitrary
    finite supplied family. -/
example
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (accepted : family.checkPacketSelectorRoutesClear rankOf = true) :
    ∀ handle : family.PacketSelectorHandle,
      family.packetSelectorPayloadFaithful rankOf handle = true :=
  (family.checkPacketSelectorRoutesClear_eq_true_iff rankOf).mp accepted

/-- Binding acceptance says exactly that the existing HB table uses the
    computed payload result at every canonical handle. -/
example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkPacketSelectorFaithfulnessBinding = true) :
    ∀ handle : family.PacketSelectorHandle,
      table.environment.faithful handle =
        family.packetSelectorPayloadFaithful table.environment.rankOf handle :=
  (table.checkPacketSelectorFaithfulnessBinding_eq_true_iff).mp accepted

/-! ## Positive Packet witness and contradiction -/

/-- Every existing positive BN6 Packet conclusion supplies a canonical handle
    through all three seed branches. -/
example
    (conclusion : TerminalBN6PacketConclusion family) :
    Nonempty family.PacketSelectorHandle :=
  conclusion.existsPacketSelectorHandle

/-- Route clearance plus exact binding converts that Packet handle into one
    environment-faithful handle. -/
example
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true)
    (bindingAccepted : table.checkPacketSelectorFaithfulnessBinding = true) :
    ∃ handle : family.PacketSelectorHandle,
      table.environment.faithful handle = true :=
  conclusion.existsFaithfulHandle_of_routesClear table routesClear
    bindingAccepted

/-- The named milestone theorem composes computed Packet faithfulness with the
    accepted executable HB selector-silence induction. -/
example
    (conclusion : TerminalBN6PacketConclusion family)
    (realizerTable : TerminalPacketTypedRealizerTable
      current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      realizerTable.environment.rankOf = true)
    (bindingAccepted :
      realizerTable.checkPacketSelectorFaithfulnessBinding = true)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) : False :=
  terminalBN6_packet_selector_faithfulness_hb_contradiction conclusion
    realizerTable dependencyTable routesClear bindingAccepted silenceAccepted
    closureAccepted

end DirectWire
end PNP
