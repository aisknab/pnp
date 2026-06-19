# Minimal Reviewer Examples

## Purpose

These examples are the smallest executable demonstrations of the repository's main checker concepts. They are onboarding fixtures, not proof evidence.

Each script contains:

- a human-readable passing input;
- a deliberately malformed or unsafe failing input;
- the expected certificate or checker result;
- exact assertions for the acceptance or named rejection;
- a statement of what the example proves and does not prove.

The examples primarily use synthetic constructors already exercised by the repository's tests. They do not replace the sealed package, the canonical report, the mathematical argument, or an independent checker-soundness review.

## Requirements

```text
Node.js 20 or newer
repository checkout containing the source modules and proof-artifacts directory
```

No network access or external package is required by these examples.

## Run all examples

```bash
npm run examples:minimal
```

Equivalent direct command:

```bash
node examples/minimal/run-all.mjs
```

Expected final line:

```text
Minimal reviewer examples passed: 8/8.
```

A passing example and its expected negative case both cause the script to exit successfully. A script exits nonzero when its accepted result, rejection coordinate, path, or reason differs from the documented expectation.

## Example index

| Script | Core concept | Passing result | Deliberate failing result |
| --- | --- | --- | --- |
| `01-locked-nand.mjs` | Locked NAND slot separation and threshold record | `CheckGPack0` accepts | Cross-family slot reuse rejects at `CheckGPack0.slotAlloc` |
| `02-residual-slack.mjs` | Residual-slack bound and exact SAT comparator | Framework and SAT decision accept | Bound `5` rejects at `CheckFinalFrameworkMatch0.slack` |
| `03-mode-firewall.mjs` | Quotient comparison versus full constructive use | Quotient projection-defect use is allowed | Quotient replacement equality rejects with `Mode.Promotion` |
| `04-no-hidden-minimization.mjs` | Theorem-only minimum references versus executable calls | Assumption-only reference and declared `PCCMin` call pass | Executable alias to `minimumEquivalent` rejects with `HiddenMin.ExecCall` |
| `05-canonical-parser.mjs` | Canonical parsing and full byte consumption | Canonical name parses | One trailing byte rejects with `Parse.TrailingBytes` |
| `06-zero-slack.mjs` | `ZeroSlack` as a required exactness obligation | Package-sufficiency record accepts | `zeroSlackSound=false` rejects at the exact theorem field |
| `07-pccpack.mjs` | `PCCPack` core boundary | Synthetic package accepts | Embedding `AcceptRun` in the core rejects |
| `08-release-seal.mjs` | SHA-256 artefact identity | Listed release-seal bytes match | A one-byte in-memory mutation does not match |

## 01. Locked NAND

### Human-readable input

Passing case: the synthetic two-gate NAND source has globally disjoint slot families `X`, `T`, `O`, `R`, `L`, and `z`.

Failing case: `O[0]` is replaced with `X[0]`, so one carrier slot belongs to two families.

### Expected certificate

An accepted `GPack0NF` containing:

```text
fullWordSize = baseline + 4
residualSlackMax = 4
```

### Checker command

```bash
node examples/minimal/01-locked-nand.mjs
```

### Expected output

The JSON output contains one `accept` result and one named rejection:

```text
coord: CheckGPack0.slotAlloc
path:  SlotAlloc.families.O.0
reason: SlotAlloc slots must be globally unique
```

### What it proves

It demonstrates that the current GPack checker accepts its synthetic valid record and rejects this explicit separation violation.

### What it does not prove

It does not prove the macro truth tables, baseline distinctness, trace equivalence, SAT preservation, residual-slack theorem, or locked-NAND threshold for all inputs.

## 02. Residual slack and SAT threshold

### Human-readable input

Passing case: Package O and Package G use the same definition

```text
Lambda(C) = size(C) - mu(C)
```

and the locked word has size `baseline + 4`. The SAT decision uses exact minimum size greater than the baseline.

Failing case: the framework claims a residual-slack maximum of `5`.

### Expected certificate

Accepted framework and SAT-decision normal forms using the same minimum notion and comparator:

```text
minSize > baseline
```

### Checker command

```bash
node examples/minimal/02-residual-slack.mjs
```

### Expected output

```text
coord: CheckFinalFrameworkMatch0.slack
path:  SlackMap.lockedResidualSlackMax
reason: locked residual slack must be an integer at most four
```

### What it proves

It demonstrates that the displayed bound and comparator are checked in these synthetic records.

### What it does not prove

It does not compute `mu(C)`, prove `Lambda(W_phi) <= 4`, or prove that the exact threshold characterizes satisfiability.

## 03. Mode firewall

### Human-readable input

Passing case: quotient-mode information is consumed by `ProjectionDefect`, a comparison-only operation.

Failing case: the same quotient-mode equality is consumed as `ReplacementEquality`, which requires full-mode evidence.

### Expected certificate

The comparison returns `ok`. The constructive use returns:

```text
Mode.Promotion
```

### Checker command

```bash
node examples/minimal/03-mode-firewall.mjs
```

### What it proves

It demonstrates the core consumer classification for one allowed and one forbidden use.

### What it does not prove

It does not establish that every caller uses this firewall, every mode annotation is correct, or every full lift and obligation discharge is mathematically sound.

## 04. No-hidden minimization

### Human-readable input

Passing case:

- `minimumEquivalent` appears only in a theorem definition;
- `PCCMin` appears as the declared residual-band executable procedure.

Failing case: executable alias `minEq` resolves to forbidden `minimumEquivalent`.

### Expected certificate

The theorem-only occurrence passes. The executable alias rejects at its exact path with:

```text
HiddenMin.ExecCall
```

### Checker command

```bash
node examples/minimal/04-no-hidden-minimization.mjs
```

### What it proves

It demonstrates occurrence-class and alias handling in the minimal core scanner.

### What it does not prove

It does not prove repository-wide coverage of JavaScript control flow, dynamic property access, callbacks, imports, generated templates, or equivalent exhaustive searches implemented without a forbidden name.

## 05. Canonical parser

### Human-readable input

Passing case: canonical encoded UTF-8 name `review`.

Failing case: the same bytes followed by one extra byte.

### Expected certificate

One parsed `Name` value with the entire input consumed.

### Checker command

```bash
node examples/minimal/05-canonical-parser.mjs
```

### Expected output

```text
Parse.TrailingBytes
```

### What it proves

It demonstrates exact top-level byte consumption for this minimal input.

### What it does not prove

It does not prove parser correctness for all record types, Unicode inputs, canonical maps, proof nodes, or a complete materialized package.

## 06. ZeroSlack

### Human-readable input

Passing case: the synthetic package-sufficiency theorem contains the named residual-band fields, including:

```text
zeroSlackSound = true
zeroSlackContradictionFromPositiveSlack = true
zeroSlackFinalClosureComplete = true
```

Failing case: `zeroSlackSound` is changed to `false`.

### Expected certificate

An accepted `PackSufficiency0NF` for the passing case. The failing case rejects with:

```text
coord: CheckPackSufficiency0.PackSufficiencyTheorem
path:  PackSufficiencyTheorem.residualBandMinimization.zeroSlackSound
reason: residualBandMinimization must certify zeroSlackSound
```

### Checker command

```bash
node examples/minimal/06-zero-slack.mjs
```

### What it proves

It demonstrates that the checker requires the named `ZeroSlack` field and reports a specific failure.

### What it does not prove

It does not derive the positive-slack contradiction, prove route completeness, validate the HB blocker argument, or establish that assertion-shaped fields have sound underlying proofs.

## 07. PCCPack

### Human-readable input

Passing case: a synthetic package has the declared core, manifest, kernel, rows, proof DAG, local packages, firewalls, GPack, final integration, and package-sufficiency theorem. The core excludes its acceptance run.

Failing case: an `AcceptRun` object is inserted into the core package.

### Expected certificate

An accepted `PackSufficiency0NF` with the declared phase order and theorem identifiers.

### Checker command

```bash
node examples/minimal/07-pccpack.mjs
```

### Expected output

```text
coord: CheckPackSufficiency0.core
path:  AcceptRun
reason: PCCPack0 core package must not contain AcceptRun
```

### What it proves

It demonstrates the package/run separation and the configured synthetic package checks.

### What it does not prove

It does not show that the synthetic package is the sealed release package, that each phase predicate is mathematically sufficient, or that the package theorem implies `P = NP`.

## 08. Release seal

### Human-readable input

Passing case: the committed `release-seal.json` bytes from the sealed bundle.

Failing case: the same bytes with the first byte changed in memory.

### Expected certificate

The SHA-256 value listed for `release-seal.json` in the bundle's `SHA256SUMS` ledger.

### Checker command

```bash
node examples/minimal/08-release-seal.mjs
```

### What it proves

It demonstrates that the current file bytes match the listed digest and a one-byte mutation does not.

### What it does not prove

It does not prove the contents of the seal, the checker, the generated records, or the mathematical theorem. A hash check is an artefact-identity check only.

## Relationship to later work

These fixtures are examples, not the complete negative-test programme. The next step adds dedicated negative tests for each major invariant and requires every malformed case to fail for a stable, named reason.
