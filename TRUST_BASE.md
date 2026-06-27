# PNP explicit trust base

The repository is being organized so that a verifier can run one command, inspect a small trust base, and decide exactly what the current public-review stack claims.

The current command is:

```bash
npm run pnp:verify
```

The trust base is intentionally **not empty**. The current goal is to make each remaining assumption explicit, versioned, executable where possible, and reducible over time.

Machine-readable coordinate:

```text
PNP-TRUST-BASE-2026-06-27-01
```

Machine-readable file:

```text
trust-base/TRUST_BASE.json
```

Audit command:

```bash
node pcc-trust-base0.mjs --json
```

## Current boundary

The trust-base ledger does not activate the public theorem gate:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Assumptions still outside the repository acceptance result

### 1. JavaScript runtime correctness for the checked fragment

The Node.js runtime is assumed to correctly execute the ES module fragment used by the checkers. This includes deterministic JSON parsing, file IO, process exit codes, object and array semantics, and integer-safe arithmetic where the checkers guard it.

Represented by:

```text
package.json
pcc-verifier-frag0.mjs
scripts/pnp-verify-all.mjs
scripts/cross-verify.mjs
```

Reduction plan: add second-runtime replay for more checker families and bounded integer validation at checker boundaries.

### 2. SHA256 collision resistance for artifact identity

SHA256 digests are assumed collision resistant for artifact identity, checksum ledgers, and replay labels. Digest equality is not supposed to replace semantic equality; the checker surface should follow digest lookups with canonical-byte or full-key comparison where required.

Represented by:

```text
pcc-verifier-frag0.mjs
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS
trust-base/SHA256SUMS
```

Reduction plan: add independent SHA256 implementation comparison and canonical-byte replay checks across runtimes.

### 3. Git object integrity and checkout fidelity

The checkout being verified is assumed to faithfully represent the intended Git object graph and file contents for the commit under review.

Represented by:

```text
PNP_STATUS.json
.github/workflows/pnp-verify-all.yml
scripts/pnp-verify-all.mjs
```

Reduction plan: add fresh-clone verification and detached commit/hash manifest checks.

### 4. Formal semantics of NAND direct-wire words

The mathematical interpretation of NAND direct-wire syntax, open carriers, boundary tuples, output tuples, evaluation, replacement, and size is assumed to match the checker-visible semantics used by the proof stack.

Represented by:

```text
canonical_proof_report.tex
kernel/PNP_MINIMAL_KERNEL.json
report-bindings/REPORT_THEOREM_BINDINGS.json
pcc-verifier-frag0.mjs
```

Reduction plan: materialize an executable NAND direct-wire semantics spec and exhaustive small-model tests.

### 5. SAT-to-locked-NAND encoding theorem

The locked NAND construction is assumed to correctly encode SAT into the stated exact-minimum threshold condition over residual slack.

Represented by:

```text
canonical_proof_report.tex
pcc-gpack0.mjs
pcc-final-framework0.mjs
pcc-global-final-sat-reduction-semantic0.mjs
kernel/PNP_MINIMAL_KERNEL.json
```

Reduction plan: add SAT encoding truth-table verification for small CNF/NAND instances and a dedicated locked-NAND semantics ledger.

### 6. PCC checker inference rules and proof-kernel soundness

The PCC-K primitive rules, Sigma registry, reflection registry, proof-DAG discipline, and checker implementations are assumed sound for the proof objects they accept.

Represented by:

```text
pcc-kimpl0.mjs
pcc-global-proof-dag0.mjs
pcc-check-pcc-pack-exp0.mjs
kernel/PNP_MINIMAL_KERNEL.json
report-bindings/REPORT_THEOREM_BINDINGS.json
```

Reduction plan: add checker totality fuzzing, negative mutation generation, and independent replay of a core checker subset.

### 7. Complexity implication: SAT in P implies P equals NP

The standard complexity-theory implication from a polynomial-time SAT decision procedure to P = NP is assumed, including the NP-completeness of SAT and the polynomial-time reductions defining NP-completeness.

Represented by:

```text
canonical_proof_report.tex
pcc-global-final-complexity-semantic0.mjs
kernel/PNP_MINIMAL_KERNEL.json
```

Reduction plan: create a machine-readable complexity ledger binding SAT is NP-complete, SAT in P, and P = NP as explicit proof objects.

## What this file does not claim

This file does not say the trust base is empty. It does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`. It does not activate public theorem emission. It makes the current assumptions inspectable so the project can shrink them deliberately.
