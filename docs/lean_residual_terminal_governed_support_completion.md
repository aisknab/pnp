# Governed terminal support completion in Lean

`lean/PNP/ResidualTerminalGovernedSupportCompletion.lean` reconstructs the
next bounded layer of the raw, completed, and saturated support calculus in
§2 and §3 of the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

The manuscript describes a completed support as its selected records, incoming
boundary, ordered outgoing interface, and profile frontier. Earlier Lean
milestones already computed the saturated record set and its exact physical
boundary and interface. This milestone combines that computed physical boundary
with the record closure and partitions every selected profile coordinate among
the ten terminal profile roles.

## Plain-language result

Consider a finite Boolean circuit and a finite set of bookkeeping rules. A
starting list of records may force other records to be included. Lean already
computes that closure. It can now package the result as one governed completed
support with no caller-written list of boundary wires or profile coordinates.

For every completed support, Lean computes:

- the circuit wires that enter its selected gates;
- the selected gates whose values leave the support;
- the selected profile coordinates in each of the ten terminal profile roles;
- whether every stated dependency is retained; and
- whether the physical boundary and interface account for every crossing wire.

The ten roles are carrier, origin, kernel, obligation, prefix, direction,
saturation, budget, charge, and frontier. Lean proves that each selected
profile coordinate belongs to exactly its computed role, no role list has a
duplicate, distinct role lists are disjoint, and the ten lists together cover
exactly the selected profile records.

This is an all-finite construction. It works for every finite direct-wire
candidate, every explicit dependency system, every finite seed list, and every
corner of the previously constructed saturated support square. It is not a
sequence of hard-coded profile coordinates.

## Technical construction

`TerminalGovernedCompletedSupport` stores only the selected primitive records.
Its other data are computed projections:

```text
physical  = completeTerminalPhysicalSupport(candidate, records)
profiles(role)
          = all finite profile coordinates filtered by
            profile(coordinate) in records and computedRole(coordinate) = role
frontier  = (physical.boundary, physical.interface, profiles)
```

`Governed` is closure under every labelled edge in the explicit
`TerminalSaturationSystem`. `Compatible` is the conjunction of that closure
with the exact physical compatibility predicate proved by the earlier
completion module.

For an arbitrary finite seed,
`completeSaturatedTerminalGovernedSupport` first runs the executable terminal
saturation and then computes the combined frontier. Lean proves that the
retained list is exactly the executable closure and that the result is governed
and physically compatible.

For a `TerminalSaturatedSupportSquare`, `governedCompleted` applies the same
construction to each computed meet, left, right, and join record list. The
result keeps the exact corner records. Closure and physical compatibility are
transported from the square theorems, while profile membership is recomputed
from that exact corner. If one selected record directly requires a profile
record, the closure theorem places that coordinate in its unique computed role
list.

The dependency system remains explicit caller data. It is operational input,
not a caller certificate that the result is closed or complete. The boundary,
interface, profile partition, closure proof, and compatibility proof are all
computed or kernel checked.

## Regression and axiom boundary

The regression uses a one-gate circuit and a ten-coordinate profile. A
ten-edge chain exercises every terminal saturation rule kind and reaches one
coordinate in every terminal profile role. The two square seeds produce a
full chain on the left and join corners and a five-role suffix on the right and
meet corners.

The checks cover all ten role memberships, a deliberately absent role,
universal exact membership for every corner, complete coverage, disjointness,
the exact physical boundary and interface of all four corners, direct required
profile routing, and compatibility of both the square and standalone saturated
completion.

The axiom transcript lists all 33 new public declarations and nine reused
saturation, finite-enumeration, physical-completion, and square interfaces
exactly once. The compiled closure permits only `propext` and `Quot.sound`.
The hostile audit rejects altered role coverage, fixed profile tables, caller
certificates, host lookup, omitted saturation or physical compatibility,
project axioms, `Classical.choice`, `sorry`, `admit`, native shortcuts, and
downstream overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalGovernedSupportCompletionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalGovernedSupportCompletion.lean
node --test audits/lean-residual-terminal-governed-support-completion0.test.mjs
```

## Generated publication evidence

The compiled inventory coordinate is
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-106`. Its 14,564,176-byte canonical
JSON records 24,405 public declarations, 13,134 theorems, 6,945
assumption-free theorems, 14,576 excluded private declarations, 222
source-closure modules, four unchanged project assumptions, and 2,240 reviewed
milestone candidates. Its SHA-256 digest is
`38c53b1e3e80059332ff62f135ffebcf04d6b5e39e158f0f48965295894c6e8d`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-106` contains 86 milestones. Eighty-three
are earned and the same three global milestones remain unearned. Its
726,779-byte JSON has file SHA-256 digest
`3b27c4f934c3897bb71584846005e93a4816b63f4f8750a6884d18f1aedfe7ce`,
canonical-object digest
`ae76920ca1f242f3668ff2d0d7427252f4e9fffa48ba1e3d595b15c7506abfbc`,
and source-closure digest
`b4be2de72b2909cd9e47f0748e061f03041fbecbac1360e5797e89fef18404f6`.

Reconstruction-status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-106` occupies 1,798,304 bytes and
has SHA-256 digest
`5e6356f2b13da0161b4b0fb0ea299b504bfef54f7670f3a4371d1b19df26d10f`.
The canonical report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-106`. Its 191,295-byte
TeX has digest
`1dc4a81c1f7a9805405019d1298f5324aaf39f599a4b58433bf72ceeb97a5a9c`;
the deterministic 75-page, 432,609-byte PDF has digest
`04683262a3cd12a893f7d1d67c750502f52f40a9c8bf7755912b3ebbff76d5fb`.
All values above are recorded from the generated artifacts.

## What remains open

This milestone does not derive the explicit dependency system from an
arbitrary circuit. It classifies selected profile records by their ten computed
roles, but does not yet prove the manuscript's frontier pushout or route the
first completion obstruction to every named outcome.

It is not yet a projection-compatible square and does not prove carrier or
profile transport, projection commutation, side-tight four-corner minima, or
BN2 square legitimacy. It does not prove `SaturatePositive`, Package E,
`BCELReady`, BN2 through BN6, complete residual routing, ZeroSlack, PCCMin,
polynomial runtime, SAT in P, removal of a project assumption, or `P = NP`.

The next earned milestone must consume this governed all-finite completion to
prove a named frontier-pushout, obstruction-routing, or projection-square
obligation. Repeating another fixed profile width would be regression evidence,
not theorem progress.
