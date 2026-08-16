/-
Copyright (c) 2026 PNP Labs.

Canonical construction of the Packet faithfulness component used by the
finite typed-realizer and HB selector-silence tables.  The preceding routing
boundary computes faithfulness from the first positive source payload behind
each canonical handle, but an otherwise independent table could still supply
a different Boolean faithfulness function and then require a separate binding
check.  This module removes that independent choice: it rebuilds the table
with exactly the computed payload function while preserving its rank map,
realizer claims, and HN/BUD activity tables.

Consequently the binding checker accepts by construction, and a route-clear
positive Packet contradicts accepted executable HB selector silence without a
caller-supplied binding premise.  The construction is uniform over an
arbitrary finite grouped BN6 family and arbitrary finite rank count.

The grouped family, ten payload checks, rank assignment, realizer claims,
blocker activity, dependency rows, and finite-to-exact rank map remain explicit
inputs.  This module does not derive those data from a terminal candidate,
prove the external semantics or compatibility of payload fields, establish
complete route silence or unconditional HB negative closure, construct
positive residual slack, prove ZeroSlack or PCCMin, establish encoded-size or
polynomial-runtime bounds, put SAT in P, remove a project assumption, or prove
P = NP.
-/

import PNP.ResidualTerminalPacketSelectorFaithfulnessRouting

namespace PNP
namespace DirectWire

/-! ## Canonical faithfulness-table construction -/

/-- Replace the independently supplied faithfulness function by the canonical
    payload computation.  Every other executable input is retained exactly. -/
def TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    TerminalPacketTypedRealizerTable current family rankCount :=
  { environment :=
      { rankOf := table.environment.rankOf
        faithful := family.packetSelectorPayloadFaithful
          table.environment.rankOf
        hnActive := table.environment.hnActive
        budgetActive := table.environment.budgetActive }
    claim := table.claim }

/-- Canonicalization preserves the supplied finite rank assignment exactly. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_rankOf
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.environment.rankOf handle =
      table.environment.rankOf handle :=
  rfl

/-- Canonicalization preserves every HN activity entry exactly. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_hnActive
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount) :
    table.withComputedPacketSelectorFaithfulness.environment.hnActive rank =
      table.environment.hnActive rank :=
  rfl

/-- Canonicalization preserves every budget activity entry exactly. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_budgetActive
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (rank : Fin rankCount) :
    table.withComputedPacketSelectorFaithfulness.environment.budgetActive rank =
      table.environment.budgetActive rank :=
  rfl

/-- Canonicalization preserves each realizer claim exactly. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_claim
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.claim handle =
      table.claim handle :=
  rfl

/-- The rebuilt table's faithfulness bit is definitionally the canonical
    source-payload computation at the preserved rank. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_faithful
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) :
    table.withComputedPacketSelectorFaithfulness.environment.faithful handle =
      family.packetSelectorPayloadFaithful table.environment.rankOf handle :=
  rfl

/-- The exhaustive binding checker accepts the rebuilt table without any
    caller-supplied compatibility witness. -/
theorem TerminalPacketTypedRealizerTable.withComputedPacketSelectorFaithfulness_binding
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    (table.withComputedPacketSelectorFaithfulness
      ).checkPacketSelectorFaithfulnessBinding = true := by
  apply (table.withComputedPacketSelectorFaithfulness
    ).checkPacketSelectorFaithfulnessBinding_eq_true_iff.2
  intro handle
  rfl

/-! ## Binding-free positive Packet witness and HB contradiction -/

/-- Route clearance converts every positive Packet branch into a faithful
    handle in the canonicalized table, with no independent binding premise. -/
theorem TerminalBN6PacketConclusion.existsFaithfulHandle_of_computedTable
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true) :
    ∃ handle : family.PacketSelectorHandle,
      (table.withComputedPacketSelectorFaithfulness
        ).environment.faithful handle = true := by
  exact conclusion.existsFaithfulHandle_of_routesClear
    table.withComputedPacketSelectorFaithfulness routesClear
    table.withComputedPacketSelectorFaithfulness_binding

/-- Named binding-free Packet-to-HB contradiction.  Selector silence and HB
    closure are checked against the canonicalized table itself, so its
    faithfulness entries cannot diverge from the source payload computation. -/
theorem terminalBN6_packet_computed_faithfulness_hb_contradiction
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorFaithfulness
        ).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorFaithfulness
        ).environment = true) : False :=
  terminalBN6_packet_selector_faithfulness_hb_contradiction conclusion
    table.withComputedPacketSelectorFaithfulness dependencyTable routesClear
    table.withComputedPacketSelectorFaithfulness_binding silenceAccepted
    closureAccepted

end DirectWire
end PNP
