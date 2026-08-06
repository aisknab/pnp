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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-107`. Its 14,824,236-byte canonical
JSON records 24,464 public declarations, 13,166 theorems, 6,953
assumption-free theorems, 14,594 excluded private declarations, 223
source-closure modules, four unchanged project assumptions, and 2,263 reviewed
milestone candidates. Its SHA-256 digest is
`7e0e7feb895f6ea1c677314b1c2bd8b2ec5f33e826219b0421301e198984720e`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-107` contains 87 milestones. Eighty-four
are earned and the same three global milestones remain unearned. Its
733,234-byte JSON has file SHA-256 digest
`84fe388d393239530a12a76cf14a262c1fdf35e2e1089ced0e90e981aa1c8f09`,
canonical-object digest
`24969820f0798b07a7bb8821d8773179165726f3212e4bb39a686543d25781a7`,
and source-closure digest
`4f08c63941db8fd92e7a33e8f16f698929247d968ae6fce45f4406f8e0aa02fb`.

Reconstruction-status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-107` occupies 1,816,951 bytes and
has SHA-256 digest
`b793312d1177ceaaadb41dda0adafc9c3c5735ed0f19a2b74050faedd97e0685`.
The canonical report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-107`. Its 192,373-byte
TeX has digest
`6536c56f5fa0f8c0c8141f214b7f040f2f942b82748652084a5d9ebbafaef435`;
the deterministic 76-page, 434,167-byte PDF has digest
`2bdea0fd4e18e25d08a7b66cf30820d8db83893cc4ab50e14cc8bbcd30b1a264`.
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
