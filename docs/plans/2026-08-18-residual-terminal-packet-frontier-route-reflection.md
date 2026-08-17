# Typed Packet frontier-signature route reflection milestone

## Objective

Replace the free Boolean `frontierChecked` input at the current Packet
selector-faithfulness boundary with executable equality of two explicit typed
frontier signatures carried by the selected source payload. Preserve the
already computed grouped-footprint colour, positive source charge, canonical
source route, table-owned finite rank, and exact ten-coordinate residual
descent checks.

## Legacy anchor and dependency edge

The pinned manuscript's Section 13 Pair packet seed checks the frontier field
and routes its first mismatch. Section 11 states that BN5 and BN6 retain a
typed frontier signature in every positive packet atom. The current Lean
boundary retains only a caller-supplied Boolean for this field. This milestone
closes that local interface edge by making `.frontier` mean inequality of
the explicit source and selector frontier signatures.

## Unbounded abstraction

Define a payload wrapper over an arbitrary type `Frontier` with decidable
equality. The wrapper carries the current ten-field faithfulness payload, one
source frontier signature, and one selector frontier signature. All theorems
range over arbitrary finite grouped BN6 families, arbitrary finite rank
carriers, and arbitrary typed frontier values. No carrier size, selector
position, or concrete frontier instance is fixed.

## Exact theorem interface

The primary field theorem will expose the exact executable proposition:

```lean
theorem TerminalPacketSelectorTypedFrontierPayload.frontierCheck_eq_true_iff
    {rankCount : Nat} {Frontier : Type} [DecidableEq Frontier]
    (payload : TerminalPacketSelectorTypedFrontierPayload rankCount Frontier) :
    payload.frontierCheck = true ↔
      payload.sourceFrontier = payload.selectorFrontier
```

The named milestone endpoint will have this boundary:

```lean
theorem terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure
    {Atom Frontier : Type} [DecidableEq Atom] [DecidableEq Frontier]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorTypedFrontierPayload rankCount Frontier)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (silenceAccepted :
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorTypedFrontierColourChargeExactRouteRankDescentFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedTypedFrontierColourChargeExactRouteRankDescent
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧
          (route ≠ .frontier ∨
            (family.packetSelectorPayloadAtom handle).payload.sourceFrontier ≠
              (family.packetSelectorPayloadAtom handle).payload.selectorFrontier) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle))
```

## Regression and hostile evidence

- Accept equal typed frontier signatures and reject unequal signatures.
- Prove both Boolean directions and exact `.frontier` first-route semantics.
- Prove canonical colour, charge, rank, and internal exact-route failures
  remain excluded.
- Preserve exact failure evidence at the positive-Packet/HB endpoint; a
  frontier route must carry typed inequality and a descent route must carry
  ten-coordinate nondecrease.
- Audit every declaration in the new module for assumptions and prohibit
  shortcuts, fixed carrier bounds, project axioms, and claim widening.
- Pin only the reviewed public theorem interface in the compiled inventory
  and publication map.

## Conservative claim boundary

The two frontier signatures, grouped family, finite rank map, before/after
residual ranks, realizer claims, HN/BUD activity, dependency rows, and
finite-to-exact rank map remain explicit inputs. Executable equality proves
only equality of those supplied typed signatures. This milestone does not
derive either signature from terminal supports, bind it to a BN5 coordinate,
construct a frontier transport, or prove the manuscript's full
frontier-faithful comparison theorem.

The obligation, activation, direction, and budget Booleans remain explicit.
The result does not construct the grouped family or selector realizer from
terminal data, establish complete route silence or unconditional HB negative
closure, construct the no-lower ledger, prove ZeroSlack or PCCMin, establish
polynomial generation or runtime, put SAT in P, remove a project assumption,
or prove P = NP.

## Release gates

Run source-shape and focused Lean checks first, then the focused regression,
axiom transcript, hostile Node audit, generated inventory/publication checks,
full remote verification, and exact-head clean-clone reproduction. Publish
through a focused draft PR, require every normal check, merge manually, and
reproduce the exact merge before the full-surface PNPLabs synchronization and
production gates.
