# Compiled Lean theorem inventory and publication gate

The current formal-publication inputs are generated from the compiled Lean environment, not by
parsing Lean source text. After `lake build PNP`, `lean-audit/PNPTheoremInventory.lean` traverses
`Lean.Environment.constants` for the public `PNP.*` declarations in the explicit `PNP` import
closure. It calls `Lean.collectAxioms` for each included declaration and emits a canonical,
lexically ordered JSON inventory.

The generated inventory is mirrored byte-for-byte at:

- [`status/LEAN_THEOREM_INVENTORY.json`](../status/LEAN_THEOREM_INVENTORY.json), the status-side
  mirror; and
- [`public/pnp-theorem-inventory.json`](../public/pnp-theorem-inventory.json), the public mirror.

The inventory records the pinned toolchain and root module, declaration kinds, each declaration's
compiled axiom closure, the source-module closure, configured detailed milestone theorem types,
excluded private compiler auxiliaries, and the four disclosed project-specific axioms. Declaration,
theorem, assumption-free-theorem, module, and excluded-private counts are generated from the
compiled environment and are intentionally not copied into this prose. Deterministic ordering and canonical JSON encoding
make the two mirrors and their digest reproducible. This inventory is evidence about the compiled
environment; it does **not** establish `P = NP` or make an abstract theorem publication-eligible.

## Separate concrete publication gate

[`publication/FORMAL_PUBLICATION_MAP.json`](../publication/FORMAL_PUBLICATION_MAP.json) defines a
separate, fail-closed publication gate. Its compatibility declaration is
`PNP.Main.p_eq_np`, and its required concrete target is `PNP.Main.ConcretePEqualsNP`. The existing
abstract proposition `PNP.PEqualsNP` uses witness-level code handles and is explicitly ineligible
for publication.

The gate requires all of its concrete-model, declaration-kind, exact-type, compiled-kernel
fingerprint, axiom-closure, source-closure, and standard-axiom-allowlist checks to pass. In this
migration step the expected target type, target value, compatibility-root type, axiom-closure, and
source-closure fingerprints are intentionally `null`. An unset fingerprint fails its configured
subcheck; two unset values never count as a match. `PNP.Main.ConcretePEqualsNP` now exists as an
axiom-free definition for mutual inclusion in the finite charged-pipeline model, but its activation
fingerprints remain unset. The compatibility/root theorem `PNP.Main.p_eq_np` is absent, and the
pipeline still lacks a proved end-to-end compiler/refinement to the raw machine kernel. The local
framed simulator lifts a supplied exact `n`-step successful raw execution from an already
represented configuration to exactly `3 * n` successful work steps. It also extracts a `k ≤ F`
exact prefix from an ordinary `F`-fuel raw run; conditional on a designated-halting endpoint, work
fuel `3 * F` and compiled fuel `18 * F` reach the representation and encoding. The full fuels are
at-most budgets, not successful-step counts or input-size bounds. This proves no termination result
and does not classify a stuck nonhalting stop as a verdict. A separate executable machine now
frames every literal raw bitstring, including empty and odd inputs, at exact branch costs and the
uniform compiled bound `6 * m * m + 39 * m + 75`, leaving only representation-permitted exterior
garbage. That theorem ends in the framer's accepting state; the renamed bridge and complete
compiler theorems remain canonical-pair-only. A
third literal finite machine now reaches a represented `Tape.handoffTarget` from an already
represented internal tape in exactly `2 * n + 4` work steps and `12 * n + 24` compiled steps for
logical output length `n`. A namespace layer proves injective three-stage
state renaming, ordered first-match preservation, lookup isolation in the literal concatenated rule
table, and transport of the three exact local traces. The bridge layer then adds exact launches and
verdict-indexed handoff copies, preserves accept/reject for supplied exact target runs, leaves a
supplied stuck nonhalting endpoint as timeout at the exact prefix budget, and compiles the cumulative
trace from canonical paired raw input at six times its work cost. A fourth reviewed module now
proves terminal packing and ordinary raw `machineOutput` equality with a local quadratic bound,
and a fifth reviewed terminal-bridge module places two disjoint packer copies in an extended rule
table and proves exact accepting/rejecting launches and output equality from represented handoff
endpoints under a local `18*n^2 + 36*n + 12` bound. The earlier ordinary-input trace has not been
transported into that extended machine. The combined development supplies no target termination,
external-input-size polynomial, complete composition/precomposition `RawRefinement`, or class
result.
The inventory now also binds the six reviewed sequential-namespace theorems for disjoint
whole-component images, isolated lookup, and accept/reject launches. Those fingerprints establish
only that local namespace milestone; no end-to-end two-machine execution or refinement theorem is
present.
Consequently the gate
is false, and every theorem-emission field derived from it remains false or `null`.

The direct CNF development does not change that fail-closed result. It defines one finite raw
machine that directly consumes `BitString.pair input certificate`, proves universal accept/reject
correctness and no timeout under an explicit polynomial bound, constructs a `.paired`
`PolynomialTimeVerifier CNFSAT`, and proves
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT`. This establishes `CNFSAT ∈ NP`.
It does not establish `CNFSAT ∈ P`, NP-hardness, NP-completeness, or `P = NP`, and it is not the
missing general compiler/refinement for arbitrary charged pipelines.

The reviewed Cook--Levin builder boundary now emits all four populated clauses of the first
scheduled constraint, traverses every remaining padding opportunity in that constraint, and emits
the second constraint's separator and complete first positive literal through its width-selected
successor. Three further finite opportunity machines reuse one reviewed 93-rule optional appender.
At tape width one all three positions are padding and emit no token; at every wider width they append
the first three unary `T` tokens of the second literal. The newest table has `5644` literal rules
plus twenty-four inherited/generated unary-evaluator rule counts, preserves
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else 3))`, and retains
`FormulaVariableSlotBound + 1 + FormulaClauseSlotsPerConstraint * FormulaTokensPerClause + 10`.
Direct lookup and the specification cursor prove that the following slot is padding at width one
and the fourth unary `T` at wider widths. Exact compiled execution is bounded by the predecessor
polynomial plus `636 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The newest 82-declaration audit covers all 66 new public
declarations, fourteen reused optional-appender interfaces, and two strengthened schedule
boundaries with exactly 37 empty, 12 `propext`, and 33 `propext`/`Quot.sound` closures. This is
still not a general dynamic raw formula cursor or arbitrary schedule decoder; the following
padding-or-fourth-unary slot, the rest of the second constraint, a complete builder,
construction-runtime `RawRefinement`, and a concrete `PolynomialReduction` remain absent.

The current four project-specific axioms remain visible as an independent inventory:

```text
PNP.CheckPCCPackexp
PNP.GeneratePCCPack
PNP.LockedNANDThreshold
PNP.ResidualBandExactMinimization
```

They are not on the publication gate's permitted Lean-standard axiom allowlist. `PNP.SAT` is now a
plain legacy witness-model label, not an axiom and not an alias for `PNP.Concrete.CNFSAT`.

## Reviewed intermediate milestone bindings

Intermediate milestone credit has a separate evidence boundary from theorem publication. Every
configured candidate must have its reviewed per-name, domain-separated compiled kernel-type
SHA-256 in the publication map, use only the fixed permitted Lean-standard axiom closure, and match
by exact declaration name and theorem kind. The milestone source-closure hash must also match. That closure
covers all modules under `lean/**/*.lean` plus `lean-toolchain`, `lakefile.lean`,
`lake-manifest.json`, and the compiled inventory probe. A same-name theorem with a weakened type,
or a change to any Lean source or pin, revokes milestone credit until the reviewed map is
deliberately updated. These non-null milestone pins are independent of the intentionally null
concrete-gate activation fingerprints.

## Deterministic publication outputs

The formal status, public status mirror, TeX report, and PDF report are generated from the checked
inventory and publication map. The root
[`canonical_proof_report.pdf`](../canonical_proof_report.pdf) is the current concise formal
reconstruction report. It is a non-activation report, not the historical claim manuscript. The
historical 56-page claim artifact is available only through the pinned legacy source coordinate;
its immutable coordinates are recorded under [`archive/legacy-v0/`](../archive/legacy-v0/README.md).

The PDF check performs two builds in the same installed environment and requires identical bytes,
then compares those bytes with the committed PDF and renders every page through Poppler. The hosted
runner's TeX and Poppler package versions are not cryptographically pinned, so this is a
same-environment determinism and fail-closed exact-byte check, not a universal cross-toolchain
reproducibility claim.

Check the committed outputs without rewriting them:

```bash
lake build PNP
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
node pcc-formal-reconstruction-status0.mjs --json --no-write
npm run report:check
```

Regeneration uses the corresponding commands without `--check`, followed by
`npm run report:build`. A successful inventory, status, or PDF check is not proof verification and
cannot activate theorem emission while the concrete gate remains false.
