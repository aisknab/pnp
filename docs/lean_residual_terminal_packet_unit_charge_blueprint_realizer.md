# Lean residual terminal Packet unit-charge blueprint realizer

`PNP.ResidualTerminalPacketUnitChargeBlueprintRealizer` connects finite Packet
replacement data to the generic charge-surplus kernel without accepting a
gate-count inequality or gain proof.

## What is formalized

A `TerminalPacketUnitChargeBlueprint` contains only:

- a replacement direct-wire implementation;
- an occurrence-level pairing between current and replacement gate indices;
  and
- the unmatched current-gate indices.

The support and replacement charge ledgers are not inputs. Lean derives them
canonically as `List.range current.gateCount` and
`List.range next.gateCount`, with every occurrence assigned unit weight.

The executable validator checks all of the following:

- the pairing plus unmatched remainder is an exact permutation of every
  current gate occurrence;
- the pairing covers every replacement gate occurrence exactly once;
- the unmatched remainder is nonempty; and
- the replacement is semantically equivalent to the current implementation.

The occurrence comparison uses a proved recursive remove-first Boolean
algorithm rather than Lean's generic `Decidable (List.Perm ...)` path. Its
axiom transcript therefore contains no `Classical.choice`. Validator
acceptance mechanically constructs the generic
`TerminalPacketChargeSurplusRealization`, a genuine `StrictEquivalentGain`,
and strict reference-residual descent.

The module also validates every original blueprint payload behind every
canonical handle in one supplied explicit grouped BN6 family. It preserves the
complete pair, balanced-triple, and full-span Packet conclusion literally. A
successful result retains the exact source handle and atom. The unresolved
result proves only that no blueprint in that supplied family passed this
validator.

## Fail-closed boundary

The grouped family, replacement blueprints, candidate implementations,
pairing, and unmatched occurrence lists remain explicit inputs. The validator
does not derive them from terminal data, serialize an encoded-circuit-bounded
selector family, or prove manuscript-level selector faithfulness or
compatibility.

In particular, supplied-family validator silence is not `BotHN`, `BotBUD`, a
lower-rank `BotSeed`, global gain absence, semantic minimality, or ZeroSlack.
The milestone does not close HB/rank routing, establish polynomial generation
or runtime, complete global PkgC or PCCMin, put CNF-SAT in P, remove a project
assumption, or prove `P = NP`.

## Reproduce the focused checks

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketUnitChargeBlueprintRealizerAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketUnitChargeBlueprintRealizer.lean
node --test audits/lean-residual-terminal-packet-unit-charge-blueprint-realizer0.test.mjs
```
