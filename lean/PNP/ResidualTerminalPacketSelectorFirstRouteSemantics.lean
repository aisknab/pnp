/-
Copyright (c) 2026 PNP Labs.

Exact earliest-field semantics for the canonical Packet selector first-route
classifier. The preceding module proves that every rejected payload returns a
route. This module proves the stronger route-indexed statement: each of the ten
route constructors is returned exactly when every earlier field accepted and
the field named by that constructor failed.

The result is uniform over arbitrary payload ranks and arbitrary finite grouped
BN6 families. It lifts through the positive-Packet outcome forced by the
canonicalized HB table, so the returned handle and route carry both the
executable classifier equality and its exact earliest-field failure proof.

These are semantics of the existing data-only Boolean fields. This module does
not construct those fields from terminal data, prove their external manuscript
meaning, map a reported failure into a decreasing complete global outcome
system, establish unconditional HB negative closure or ZeroSlack, prove PCCMin
or polynomial runtime, put SAT in P, remove a project assumption, or prove
P = NP.
-/

import PNP.ResidualTerminalPacketSelectorFirstRouteOutcome

namespace PNP
namespace DirectWire

/-! ## Exact route-indexed failure propositions -/

/-- Exact earliest failed condition named by one route. Every field before the
    named route accepted; the named field itself failed. -/
def TerminalPacketSelectorFaithfulnessPayload.FailureAt
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    TerminalPacketSelectorFaithfulnessRoute -> Prop
  | .colour =>
      payload.colourChecked = false
  | .frontier =>
      payload.colourChecked = true ∧
        payload.frontierChecked = false
  | .charge =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = false
  | .obligation =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = false
  | .activation =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = false
  | .direction =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = false
  | .budget =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = false
  | .rank =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag ≠ expectedRank
  | .exactRoute =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag = expectedRank ∧
        payload.exactRouteClear = false
  | .descent =>
      payload.colourChecked = true ∧
        payload.frontierChecked = true ∧
        payload.chargeChecked = true ∧
        payload.obligationChecked = true ∧
        payload.activationChecked = true ∧
        payload.directionChecked = true ∧
        payload.budgetChecked = true ∧
        payload.rankTag = expectedRank ∧
        payload.exactRouteClear = true ∧
        payload.strictDescentClear = false

/-- The executable first route is exactly its route-indexed earliest failed
    condition. This characterizes all ten constructors in one theorem. -/
theorem TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_some_iff_failureAt
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    payload.firstRoute expectedRank = some route ↔
      payload.FailureAt expectedRank route := by
  by_cases colour : payload.colourChecked = true
  · by_cases frontier : payload.frontierChecked = true
    · by_cases charge : payload.chargeChecked = true
      · by_cases obligation : payload.obligationChecked = true
        · by_cases activation : payload.activationChecked = true
          · by_cases direction : payload.directionChecked = true
            · by_cases budget : payload.budgetChecked = true
              · by_cases rank : payload.rankTag = expectedRank
                · by_cases exactRoute : payload.exactRouteClear = true
                  · by_cases descent : payload.strictDescentClear = true
                    · cases route <;>
                        simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                          TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                          colour, frontier, charge, obligation, activation,
                          direction, budget, rank, exactRoute, descent]
                    · cases route <;>
                        simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                          TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                          colour, frontier, charge, obligation, activation,
                          direction, budget, rank, exactRoute, descent]
                  · cases route <;>
                      simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                        TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                        colour, frontier, charge, obligation, activation,
                        direction, budget, rank, exactRoute]
                · cases route <;>
                    simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                      TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                      colour, frontier, charge, obligation, activation,
                      direction, budget, rank]
              · cases route <;>
                  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                    TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                    colour, frontier, charge, obligation, activation,
                    direction, budget]
            · cases route <;>
                simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                  TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                  colour, frontier, charge, obligation, activation, direction]
          · cases route <;>
              simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                TerminalPacketSelectorFaithfulnessPayload.FailureAt,
                colour, frontier, charge, obligation, activation]
        · cases route <;>
            simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
              TerminalPacketSelectorFaithfulnessPayload.FailureAt,
              colour, frontier, charge, obligation]
      · cases route <;>
          simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
            TerminalPacketSelectorFaithfulnessPayload.FailureAt,
            colour, frontier, charge]
    · cases route <;>
        simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
          TerminalPacketSelectorFaithfulnessPayload.FailureAt,
          colour, frontier]
  · cases route <;>
      simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
        TerminalPacketSelectorFaithfulnessPayload.FailureAt, colour]

/-- At most one exact earliest-failure proposition can hold for one payload. -/
theorem TerminalPacketSelectorFaithfulnessPayload.failureAt_unique
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    {left right : TerminalPacketSelectorFaithfulnessRoute}
    (leftFailure : payload.FailureAt expectedRank left)
    (rightFailure : payload.FailureAt expectedRank right) :
    left = right := by
  have leftFound :=
    (payload.firstRoute_eq_some_iff_failureAt expectedRank left).2 leftFailure
  have rightFound :=
    (payload.firstRoute_eq_some_iff_failureAt expectedRank right).2 rightFailure
  rw [leftFound] at rightFound
  exact Option.some.inj rightFound

/-- Checker rejection is exactly the existence of one exact earliest failed
    payload condition, not merely an uninterpreted route tag. -/
theorem TerminalPacketSelectorFaithfulnessPayload.check_eq_false_iff_exists_failureAt
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.check expectedRank = false ↔
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        payload.FailureAt expectedRank route := by
  constructor
  · intro rejected
    obtain ⟨route, found⟩ :=
      (payload.exists_firstRoute_iff_check_eq_false expectedRank).2 rejected
    exact ⟨route,
      (payload.firstRoute_eq_some_iff_failureAt expectedRank route).1 found⟩
  · rintro ⟨route, failure⟩
    have found :=
      (payload.firstRoute_eq_some_iff_failureAt expectedRank route).2 failure
    exact payload.check_eq_false_of_firstRoute expectedRank route found

/-! ## Canonical grouped-family semantics -/

/-- Exact earliest failed condition for the canonical positive source payload
    behind one input-relative handle. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFailureAt
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) : Prop :=
  (family.packetSelectorPayloadAtom handle).payload.FailureAt
    (rankOf handle) route

/-- The canonical grouped-family first route is exactly the earliest failed
    condition of that handle's original positive source payload. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_some_iff_failureAt
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle)
    (route : TerminalPacketSelectorFaithfulnessRoute) :
    family.packetSelectorPayloadFirstRoute rankOf handle = some route ↔
      family.packetSelectorPayloadFailureAt rankOf handle route :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.firstRoute_eq_some_iff_failureAt (rankOf handle) route

/-! ## Positive Packet/HB exact failure outcome -/

/-- Canonical HB selector silence forces a positive Packet to expose not only a
    route tag but the exact earliest failed condition named by that route. -/
theorem TerminalBN6PacketConclusion.existsFirstRouteFailure_of_computedTableSelectorSilence
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
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
            table.environment.rankOf handle route := by
  obtain ⟨handle, route, found⟩ :=
    conclusion.existsFirstRoute_of_computedTableSelectorSilence table
      dependencyTable silenceAccepted closureAccepted
  exact ⟨handle, route, found,
    (family.packetSelectorPayloadFirstRoute_eq_some_iff_failureAt
      table.environment.rankOf handle route).1 found⟩

/-- Named milestone endpoint: the canonical positive-Packet/HB outcome carries
    one exact earliest-field failure proof without route-clear or binding
    premises. -/
theorem terminalBN6_packet_computed_faithfulness_hb_first_route_failure
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
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
  conclusion.existsFirstRouteFailure_of_computedTableSelectorSilence table
    dependencyTable silenceAccepted closureAccepted

end DirectWire
end PNP
