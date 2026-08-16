/-
Copyright (c) 2026 PNP Labs.

Total first-route outcome for the canonical Packet selector-faithfulness
boundary.  The preceding routing module defines a fail-closed first-route
classifier and proves its soundness in one direction.  This module proves the
missing completeness direction: a canonical payload is accepted exactly when
its first route is absent, and every rejected payload exposes one of the ten
closed typed routes.

Every positive BN6 Packet therefore supplies either a faithful canonical
handle or a handle with a concrete first route.  After canonicalizing the HB
faithfulness table, accepted executable selector silence rules out the faithful
case, so a positive Packet must expose a first route without a route-clear
premise.

The grouped family, payload field Booleans, finite rank assignment, realizer
claims, blocker activity, dependency rows, and finite-to-exact rank map remain
explicit inputs.  This module does not prove the external semantics of a route,
show that any reported route decreases a complete global outcome system,
construct the inputs from terminal data, establish complete route silence or
unconditional HB negative closure, prove ZeroSlack or PCCMin, establish
encoded-size or polynomial-runtime bounds, put SAT in P, remove a project
assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorFaithfulnessTable

namespace PNP
namespace DirectWire

/-! ## Total payload first-route classification -/

/-- A payload has no first route exactly when its complete data-only checker
    accepts at the expected finite rank. -/
theorem TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_none_iff_check_eq_true
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.firstRoute expectedRank = none ↔
      payload.check expectedRank = true := by
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
                    · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                        TerminalPacketSelectorFaithfulnessPayload.check,
                        colour, frontier, charge, obligation, activation,
                        direction, budget, rank, exactRoute, descent]
                    · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                        TerminalPacketSelectorFaithfulnessPayload.check,
                        colour, frontier, charge, obligation, activation,
                        direction, budget, rank, exactRoute, descent]
                  · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                      TerminalPacketSelectorFaithfulnessPayload.check,
                      colour, frontier, charge, obligation, activation,
                      direction, budget, rank, exactRoute]
                · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                    TerminalPacketSelectorFaithfulnessPayload.check,
                    colour, frontier, charge, obligation, activation,
                    direction, budget, rank]
              · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                  TerminalPacketSelectorFaithfulnessPayload.check,
                  colour, frontier, charge, obligation, activation,
                  direction, budget]
            · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
                TerminalPacketSelectorFaithfulnessPayload.check,
                colour, frontier, charge, obligation, activation, direction]
          · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
              TerminalPacketSelectorFaithfulnessPayload.check,
              colour, frontier, charge, obligation, activation]
        · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
            TerminalPacketSelectorFaithfulnessPayload.check,
            colour, frontier, charge, obligation]
      · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
          TerminalPacketSelectorFaithfulnessPayload.check,
          colour, frontier, charge]
    · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
        TerminalPacketSelectorFaithfulnessPayload.check, colour, frontier]
  · simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute,
      TerminalPacketSelectorFaithfulnessPayload.check, colour]

/-- Rejection is equivalent to the existence of one concrete first route.
    Because `firstRoute` is ordered, the witness is the earliest failed field. -/
theorem TerminalPacketSelectorFaithfulnessPayload.exists_firstRoute_iff_check_eq_false
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    (∃ route : TerminalPacketSelectorFaithfulnessRoute,
      payload.firstRoute expectedRank = some route) ↔
      payload.check expectedRank = false := by
  constructor
  · rintro ⟨route, found⟩
    exact payload.check_eq_false_of_firstRoute expectedRank route found
  · intro rejected
    cases found : payload.firstRoute expectedRank with
    | none =>
        have accepted :=
          (payload.firstRoute_eq_none_iff_check_eq_true expectedRank).mp found
        rw [accepted] at rejected
        contradiction
    | some route =>
        exact ⟨route, rfl⟩

/-! ## Canonical grouped-family outcomes -/

/-- The lifted canonical payload has no route exactly when its computed
    faithfulness bit is true. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_none_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRoute rankOf handle = none ↔
      family.packetSelectorPayloadFaithful rankOf handle = true :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.firstRoute_eq_none_iff_check_eq_true (rankOf handle)

/-- The lifted computed faithfulness bit is false exactly when its canonical
    source payload exposes one concrete first route. -/
theorem TerminalBN6GroupedFamily.exists_packetSelectorPayloadFirstRoute_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    (∃ route : TerminalPacketSelectorFaithfulnessRoute,
      family.packetSelectorPayloadFirstRoute rankOf handle = some route) ↔
      family.packetSelectorPayloadFaithful rankOf handle = false :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.exists_firstRoute_iff_check_eq_false (rankOf handle)

/-! ## Positive Packet and canonical HB outcomes -/

/-- Every positive Packet exposes a canonical handle whose computed payload is
    either faithful or reports its first typed failure route. -/
theorem TerminalBN6PacketConclusion.existsFaithfulOrFirstRoute
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (rankOf : family.PacketSelectorHandle -> Fin rankCount) :
    ∃ handle : family.PacketSelectorHandle,
      family.packetSelectorPayloadFaithful rankOf handle = true ∨
        ∃ route : TerminalPacketSelectorFaithfulnessRoute,
          family.packetSelectorPayloadFirstRoute rankOf handle = some route := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  refine ⟨handle, ?_⟩
  cases accepted : family.packetSelectorPayloadFaithful rankOf handle with
  | false =>
      exact Or.inr
        ((family.exists_packetSelectorPayloadFirstRoute_iff rankOf handle).2
          accepted)
  | true =>
      exact Or.inl rfl

/-- Once the canonicalized table passes executable selector silence and HB
    active-dependency closure, a positive Packet cannot take the faithful side
    of the total outcome and must expose a first typed route. -/
theorem TerminalBN6PacketConclusion.existsFirstRoute_of_computedTableSelectorSilence
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
          table.environment.rankOf handle = some route := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedRejected :=
    (table.withComputedPacketSelectorFaithfulness
      ).noFaithful_of_selectorSilent dependencyTable silenceAccepted
        closureAccepted handle
  rw [table.withComputedPacketSelectorFaithfulness_faithful handle] at computedRejected
  obtain ⟨route, found⟩ :=
    (family.exists_packetSelectorPayloadFirstRoute_iff
      table.environment.rankOf handle).2 computedRejected
  exact ⟨handle, route, found⟩

/-- Named milestone endpoint: under the canonical table and accepted
    executable HB silence, every positive Packet produces a concrete typed
    first-failure route without assuming route-clear acceptance. -/
theorem terminalBN6_packet_computed_faithfulness_hb_first_route
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
          table.environment.rankOf handle = some route :=
  conclusion.existsFirstRoute_of_computedTableSelectorSilence table
    dependencyTable silenceAccepted closureAccepted

end DirectWire
end PNP
