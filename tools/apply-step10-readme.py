#!/usr/bin/env python3
from pathlib import Path

readme = Path('README.md')
text = readme.read_text(encoding='utf-8')
marker = '## Public RunAll0 entry point\n'
if marker not in text:
    raise SystemExit(f'missing README marker: {marker!r}')

tail = text[text.index(marker):]

prefix = '''# pnp

**Public source and checker repository for a claimed proof that `P = NP`.**

This repository contains the JavaScript checker stack, package generator, materialized certificate and replay records, sealed release artefacts, canonical report, tests, and reviewer documentation for a proposed SAT-to-exact-NAND-minimization route. The claim is extraordinary and has not received independent mathematical validation.

## Read this first

| Question | Current answer |
| --- | --- |
| **What is this repository?** | Source code, finite certificate records, checker and replay machinery, tests, release artefacts, and audit documentation for the author's claimed `P = NP` result. |
| **What extraordinary claim is being made?** | The report claims a deterministic polynomial-time SAT algorithm by reducing SAT to exact minimization of specially locked multi-output NAND words with residual slack at most four, then applying a claimed polynomial exact minimizer for that residual band. |
| **What is the current verification status?** | The frozen 7072f8d release records internal checker acceptance, replay closure, final certificate/release-gate/report acceptance, and 1,121 passing tests. No independent reviewer has confirmed theorem correctness, checker soundness, generated-package completeness, or the mathematical implication to `P = NP`. See [EXTERNAL_REVIEW_STATUS.md](./EXTERNAL_REVIEW_STATUS.md). |
| **What can a hash check establish?** | That retrieved bytes match a published checksum ledger, subject to the hash implementation and collision assumptions. It does **not** establish theorem correctness, checker soundness, or correct generation. |
| **What can the checker establish?** | That the supplied records satisfy the predicates implemented by the named checker and its linkage rules. Checker acceptance does **not** independently establish that those predicates are mathematically sufficient or correctly implemented. |
| **What remains for external reviewers?** | The locked-NAND SAT bridge; residual-band completeness and `ZeroSlack`; the proof kernel, Sigma schemas, and reflection mappings; parser/canonicalization; no-hidden-minimization coverage; polynomial runtime and certificate-size bounds; and clean-room reproduction. |
| **How do I run the smallest verification?** | Run `npm ci` and `npm run examples:minimal`. This executes eight scoped pass/fail onboarding fixtures; it is not a proof verification. |
| **Where should reviewers start?** | Start with [docs/reviewer_guide.md](./docs/reviewer_guide.md), then [docs/proof_pipeline.md](./docs/proof_pipeline.md), [docs/terminology_crosswalk.md](./docs/terminology_crosswalk.md), and [docs/trust_model.md](./docs/trust_model.md). |

## Claim boundary

The repository records the following conditional claim:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

The generator is untrusted. The evidential object is the materialized package as interpreted by the checker, followed by the recorded acceptance, replay, certificate, and release linkage. This boundary is an internal repository claim and must not be paraphrased as external acceptance or consensus.

## Quick start for reviewers

Requirements: Node.js 20 or newer and npm 10 or newer.

```bash
git clone https://github.com/aisknab/pnp.git
cd pnp
npm ci
npm run examples:minimal
npm run test:negative
```

The two reviewer suites should exit successfully only when their accepted fixtures and named rejection cases match the documented expectations. They demonstrate narrow implementation behavior; they do not validate the general mathematics.

Run the current-tree validation suite with:

```bash
npm run validate
```

For the frozen 7072f8d release, use the pinned tags and procedure in [docs/reproducibility.md](./docs/reproducibility.md). Current `main` contains later reviewer documentation, examples, negative tests, and source comments, so its test inventory should not be confused with the frozen 1,121-test release.

## What each verification layer means

| Layer | Command or artefact | What success establishes | What success does not establish |
| --- | --- | --- | --- |
| Minimal examples | `npm run examples:minimal` | Eight documented pass/fail fixtures behave as expected. | General theorem correctness or checker completeness. |
| Named negative tests | `npm run test:negative` | Eight major malformed cases fail at their named checker coordinates. | Absence of other defects or fail-open paths. |
| Current test suite | `npm test` | The finite current-tree test suite passes in the selected environment. | Exhaustive correctness or polynomial asymptotics. |
| Public checker smoke | `npm run smoke` | The public `RunAll0` implementation path returns its recorded result for the supplied repository fixture. | Independent checker soundness or validation of every mathematical implication. |
| Release checksums | `SHA256SUMS` and `SHA256SUMS.sha256` | Published artefact bytes match the sealed ledger. | Correctness of the artefact contents. |
| Independent audit | Reviewer derivations, counterexamples, clean-room checkers, and reproduction logs | Evidence about mathematics, checker soundness, complexity, and provenance at the audited boundary. | Broader claims outside the audit's stated scope. |

## Frozen release coordinates

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

The canonical report is available as [PDF](./canonical_proof_report.pdf) and [TeX](./canonical_proof_report.tex). It states the author's mathematical claim; publication in this repository is not independent validation.

## Reviewer map

- [Reviewer guide](./docs/reviewer_guide.md): neutral overview, audit paths, and fast falsification checklist.
- [Proof pipeline](./docs/proof_pipeline.md): standard terminology, mathematical route, executable evidence route, and hidden-search risks.
- [Terminology crosswalk](./docs/terminology_crosswalk.md): formal definitions and standard-language mappings for bespoke terms.
- [Trust model](./docs/trust_model.md): mathematical, parser, checker, runtime, build, seal, report, and website trust boundaries.
- [Audit questions](./docs/audit_questions.md): claim-by-claim worksheet with concrete refutation criteria.
- [Reproducibility protocol](./docs/reproducibility.md): fresh-clone, checksum, pinned-test, regeneration, and comparison instructions.
- [Minimal examples](./examples/minimal/README.md): eight small accepted/rejected demonstrations.
- [External review status](./EXTERNAL_REVIEW_STATUS.md): public record of substantive feedback and what has not been independently verified.

## Install and library usage

Use the lockfile-preserving installation command:

```bash
npm ci
```

The primary library module is [`pcc-core.mjs`](./pcc-core.mjs). It exports codec helpers, canonicalization utilities, digest functions, row-key validation helpers, route checks, and a minimal bootstrap context.

```js
import {
  makeMinimalBootstrapContext,
  name,
  digestObject0,
} from '@aisknab/pnp';

const ctx = makeMinimalBootstrapContext();
const digest = digestObject0(ctx, name('example'));
```

Useful top-level commands:

```bash
npm run check
npm run examples:minimal
npm run test:negative
npm test
npm run validate
```

'''

new_text = prefix + tail

required = [
    'What is this repository?',
    'What extraordinary claim is being made?',
    'What is the current verification status?',
    'What can a hash check establish?',
    'What can the checker establish?',
    'What remains for external reviewers?',
    'How do I run the smallest verification?',
    'Where should reviewers start?',
    'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
    '## Public RunAll0 entry point',
]
for item in required:
    if item not in new_text:
        raise SystemExit(f'missing required README content: {item}')

for forbidden in [
    'P = NP is established',
    'P = NP has been proved',
    'unconditional P = NP',
    'the proof of P = NP is complete',
]:
    if forbidden in new_text:
        raise SystemExit(f'forbidden overclaiming wording: {forbidden}')

readme.write_text(new_text, encoding='utf-8')
print(f'updated {readme}: {len(text)} -> {len(new_text)} characters')
