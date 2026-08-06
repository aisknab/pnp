# Governed terminal frontier pushout

`lean/PNP/ResidualTerminalFrontierPushout.lean` reconstructs the next
all finite dependency edge in §3 of the pinned legacy manuscript.  The
manuscript writes the frontier law schematically as

\[
  Front_{A∨B} = Front_A \star_{Front_{A∧B}} Front_B.
\]

The Lean theorem proves this law for every finite direct-wire candidate,
every explicit terminal dependency system, and every computed saturated
support square.  It is one general theorem over arbitrary finite sizes.  The
milestone is not a collection of fixed gate coordinates or a repeatable
finite-prefix extension.

## Computed gluing

Each square corner already has a governed completion containing:

- the selected saturated terminal records;
- a canonical incoming physical boundary;
- a canonical ordered outgoing interface; and
- selected profile coordinates partitioned by the ten terminal roles.

The new `terminalGovernedFrontierPushout` reads only the completed left and
right sides.  It does not inspect or accept the join frontier as an input.
It computes three components:

1. `terminalBoundaryFrontierPushout` scans the complete finite wire universe.
   A wire from either side boundary survives exactly when it remains external
   to the combined left-plus-right record list.
2. `terminalInterfaceFrontierPushout` scans every gate in canonical order.
   A side-interface producer survives exactly when the combined support still
   has an external consumer for it or the producer is a global output.
3. `terminalProfileFrontierPushout` scans every profile coordinate and takes
   the role-preserving union of the two side lists.

All three computed lists have exact membership theorems and no-duplicate
theorems.  No caller-provided frontier, schedule lookup, host computation, or
correctness certificate appears in the construction.

## Exact square laws

For a `TerminalSaturatedSupportSquare`, Lean proves:

- the independently completed join boundary equals the computed boundary
  gluing;
- the independently completed join interface equals the computed interface
  gluing;
- a coordinate is in the meet profile for a role exactly when it is in both
  side profiles for that same role;
- a coordinate is in the join profile for a role exactly when it is in either
  side profile for that same role; and
- the complete governed join frontier equals the combined pushout.

The exported theorem is
`TerminalSaturatedSupportSquare.governed_frontier_pushout`.  Its first
conjunct is the complete frontier equality.  Its second conjunct is the exact
meet overlap for every terminal role and every finite profile coordinate.

## Retained and internalized coordinates

The side-disposition theorems make the physical meaning explicit.

- A left or right boundary wire is `retained` when it remains on the exterior
  of the union.  If it is `internalized`, it is a gate wire selected by the
  opposite side.
- A side-interface producer is `retained` when it remains externally visible.
  If it is `internalized`, the combined support has no external consumer for
  it and it is not a global output.

These statements distinguish genuine gluing from simple list concatenation.
The regression includes an adjacent-gate example where a left output becomes
an internal wire after joining the right side, a shared profile coordinate,
an empty square, and retention caused only by the candidate's global output.

## Legacy anchor and remaining boundary

This closes the §3 governed frontier-pushout edge after saturated square
closure and governed support completion.  It remains faithful to the pinned
legacy carrier convention: the dependency system is still explicit input,
physical ports come from the actual direct-wire program, and profiles retain
their computed terminal roles.

The milestone does **not** prove projection compatibility for the square, BN2
square legitimacy, side-tight four-corner minima, obstruction routing,
`SaturatePositive`, `BCELReady`, Package E, ZeroSlack, PCCMin, polynomial
runtime, SAT in P, or P = NP.  Those remain downstream obligations.  In
particular, the current result cannot be substituted for the manuscript's
later projection-compatible-square and positivity arguments.

## Audit and reproduction

The closed audit covers all 25 public declarations in the new module plus 14
reused finite-universe, physical-semantics, square, and governed-profile
interfaces.  The only permitted closure is the approved Lean-standard set
`propext` and `Quot.sound`; project axioms, `Classical.choice`, `sorry`,
`admit`, native decision shortcuts, host lookup, and caller certificates are
rejected.

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFrontierPushoutAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFrontierPushout.lean
node --test audits/lean-residual-terminal-frontier-pushout0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-06-107` records
24,464 declarations, 13,166 theorem-kind declarations, 6,953 assumption-free
theorems, 14,594 excluded private declarations, 223 source-closure modules,
and 2,263 reviewed milestone candidates. Its 14,824,236 canonical bytes have
SHA-256
`7e0e7feb895f6ea1c677314b1c2bd8b2ec5f33e826219b0421301e198984720e`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-06-107`
contains 87 milestones: 84 earned and the same three global milestones
unearned. Its 733,234 bytes pin all 2,263 reviewed theorem types and have file
SHA-256
`84fe388d393239530a12a76cf14a262c1fdf35e2e1089ced0e90e981aa1c8f09`,
canonical-object digest
`24969820f0798b07a7bb8821d8773179165726f3212e4bb39a686543d25781a7`,
and source-closure digest
`4f08c63941db8fd92e7a33e8f16f698929247d968ae6fce45f4406f8e0aa02fb`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-107`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-FRONTIER-PUSHOUT-106`,
occupies 1,816,951 bytes and has SHA-256
`b793312d1177ceaaadb41dda0adafc9c3c5735ed0f19a2b74050faedd97e0685`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-107` has a
192,373-byte TeX source with SHA-256
`6536c56f5fa0f8c0c8141f214b7f040f2f942b82748652084a5d9ebbafaef435`
and a deterministic 76-page, 434,167-byte A4 PDF with SHA-256
`2bdea0fd4e18e25d08a7b66cf30820d8db83893cc4ab50e14cc8bbcd30b1a264`.

The publication gate remains false. All four project assumptions, six
blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.
