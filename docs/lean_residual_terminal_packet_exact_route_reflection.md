# Lean canonical Packet exact-route reflection

This milestone removes a second caller-controlled duplicate from the active
Packet selector-faithfulness route. For every canonical selector handle, the
grouped-family interface already proves that its selected cell belongs to the
family, has exactly the decoded footprint, contains the selected original
payload atom, and gives that atom positive mass. The canonical payload now
marks this internal handle-to-cell-to-payload route clear by construction.

The same projection also copies the typed-realizer table's authoritative
finite handle rank and computes residual descent from the exact ten-coordinate
`RankWF` comparison. It ignores the caller's copies of `exactRouteClear`,
`rankTag`, and `strictDescentClear` while preserving the seven semantic Boolean
fields.

## Kernel-checked result

`PNP.ResidualTerminalPacketExactRouteReflection` proves uniformly over an
arbitrary finite grouped BN6 family and arbitrary finite rank carrier that:

- canonical acceptance needs only the seven retained semantic fields and an
  actual decreasing residual-rank transition;
- `.exactRoute` and `.rank` are impossible failure propositions and impossible
  executable first routes after canonicalization;
- a final `.descent` route is equivalent to acceptance of all seven preceding
  semantic fields plus actual nondecrease;
- the grouped-family first route retains the exact earliest failure proof;
- rebuilding the typed-realizer table preserves its rank map, realizer claims,
  and HN/BUD activity; and
- a positive Packet under accepted executable selector silence and checked HB
  active-dependency closure yields one exact non-`.exactRoute`, non-`.rank`
  failure, with a proof of nondecrease when that route is `.descent`.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_exact_route_reflected_hb_first_route_failure
```

The axiom transcript covers all 24 public declarations. The reviewed milestone
theorems use only the permitted Lean-standard `propext` and `Quot.sound`
closure where needed; no project axiom, `sorry`, `admit`, or
`Classical.choice` enters the milestone theorem boundary.

## Exact claim boundary

The reflected route is internal and input-relative. It says that the canonical
handle really selects an original positive payload atom from its exact grouped
source cell and footprint. This internal route is not an external exact minimum
and does not prove the manuscript's broader exact-minimum or selector-
compatibility semantics.

The seven remaining routes still correspond to supplied Boolean fields. Their
external manuscript meanings and their integration into a complete,
proof-bearing global outcome system remain open. The grouped family, rank map,
before/after residual ranks, realizer claims, blocker activity, and dependency
rows also remain explicit inputs rather than data constructed from a terminal
candidate.

Accordingly, this milestone does not construct the no-lower ledger, prove that
a decreasing transition exists, establish complete route silence or
unconditional HB negative closure, prove unconditional `ZeroSlack` or PCCMin,
derive encoded-size or polynomial-runtime bounds, put SAT in P, remove a
project assumption, or prove `P = NP`.

## Evidence

- Source: `lean/PNP/ResidualTerminalPacketExactRouteReflection.lean`
- Axiom transcript:
  `lean-audit/PNPResidualTerminalPacketExactRouteReflectionAxiomAudit.lean`
- Regression:
  `lean-regression/PNPResidualTerminalPacketExactRouteReflection.lean`
- Hostile/source audit:
  `audits/lean-residual-terminal-packet-exact-route-reflection0.test.mjs`
- Publication map: `publication/FORMAL_PUBLICATION_MAP.json`

The generated theorem inventory, formal reconstruction status, canonical
report, and public mirrors bind the milestone to the compiled declarations and
retain the five unresolved global blockers. PNPLabs consumes those exact
checked-in artefacts as publication evidence; it does not rebuild Lean.
