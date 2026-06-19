# Trust Model

## Purpose and scope

This document identifies the components that must be trusted, checked, reproduced, or independently replaced when evaluating the repository's claim.

The public claim boundary is:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The source/checker release discussed here is:

```text
source tag:    final-pnp-proof-report-hardened-7072f8d
source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:  final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

This document is reviewer guidance added on `main`. It does not alter the pinned source/checker revision, theorem statements, certificate semantics, checker logic, generated package, or sealed artefact bundle.

## Trust vocabulary

The **Trusted?** column below is scoped to the current repository's evidence chain.

- **Yes** means the current claim relies on that component without another repository component proving the component itself correct. It is part of the current trusted computing or mathematical base and therefore requires direct audit or independent replacement.
- **No** means the component is intended to be adversarial or untrusted; a downstream checker must validate it before relying on it.
- **Partially** means only a narrow property is trusted, such as byte identity, deterministic execution, or toolchain semantics. It must not be credited with a stronger property.

A component may be trusted for execution while remaining untrusted for theorem correctness. For example, SHA-256 is used to identify bytes, not to prove mathematics.

## Properties that must remain separate

| Property | Question | Appropriate evidence |
| --- | --- | --- |
| Mathematical correctness | Do the definitions and implications really establish the claimed theorem? | Independent proof review, counterexample search, and formal or conventional derivation. |
| Checker soundness | Does acceptance imply the exact mathematical statement assigned to the checker? | Source audit, rule-by-rule audit, differential implementation, or formal verification. |
| Implementation conformance | Does the implementation behave according to its documented predicates? | Unit, negative, mutation, integration, and differential tests. |
| Reproducibility | Can an independent environment retrieve and run the pinned release? | Fresh clone, pinned toolchain, preserved transcript, and regenerated records. |
| Artefact identity | Are these the same bytes named by the release? | SHA-256, byte counts, immutable tags, and checksum ledgers. |
| External acceptance | Has an independent expert or institution validated the result? | Public independent review. Internal tests and silence from reviewers do not count. |

## What common checks establish

| Observation | What it establishes | What it does not establish |
| --- | --- | --- |
| `sha256sum -c SHA256SUMS` succeeds | The checked files match the listed digests, subject to the hash implementation and collision assumptions. | Mathematical correctness, checker soundness, or correct generation. |
| `npm test` succeeds | The finite test suite passed under the current runtime and environment. | Exhaustive correctness, absence of untested bugs, or theorem validity. |
| `npm run validate` succeeds | Syntax checking and the repository test suite pass. | Independent reproduction of the sealed artefact context or mathematical acceptance. |
| `CheckGPack0` accepts | The GPack satisfies the predicates implemented by `CheckGPack0`. | Independent proof that the locked-NAND threshold theorem is true. |
| `CheckPCCPackexp0` accepts | The package satisfies the implemented top-level package predicates and linkage requirements. | That those predicates are sufficient or mathematically sound. |
| `CheckFinalPNPProofReport0` accepts | The final release-gate, certificate, replay, linkage, and exact theorem fields satisfy the implemented final-report checks. | That the underlying mathematical implication is correct. |
| The PDF states a theorem | The publication makes that claim. | That the claim has been independently proved or accepted. |
| The website browser check succeeds | The downloaded public file matches the digest embedded or published by the website. | That the file's contents are mathematically correct. |

## Mathematical and specification boundaries

| Component | Input | Output | Trusted? yes/no/partially | Why it must be trusted | How to independently verify or replace it | Failure mode | Relevant tests |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Standard complexity-theory background | Definitions of `P`, `NP`, SAT, reductions, and SAT NP-completeness | Standard implications used by the final argument | **Yes**, as mathematical background | The final inference uses SAT NP-completeness and the standard meaning of polynomial-time decision. | Compare against standard textbooks; formalize the final complexity-theory implication in an independent proof assistant. | Nonstandard input encoding, uniformity convention, or polynomial-time model is silently used. | No finite repository test can establish standard mathematical facts. |
| Repository mathematical definitions | Direct-wire words, carriers, size/charge, equivalence, minimum, residual slack, full/quotient modes, package schemas | The formal problem and theorem statements that the checker is supposed to represent | **Yes**, as the specification surface | A checker can only be judged relative to exact definitions. If the definitions drift, the accepted theorem may not be the public theorem. | Read `canonical_proof_report.tex` alongside [terminology_crosswalk.md](terminology_crosswalk.md); rewrite the definitions independently and compare models and edge cases. | Two modules use different size, output, carrier, minimum, or slack conventions. | Framework-match and final-integration tests; parser/type tests do not prove semantic agreement. |
| Mathematical lemmas and theorem implications | Definitions plus hypotheses and intermediate claims | Locked-NAND threshold, residual-band exact minimisation, package sufficiency, and final `P = NP` implication | **Yes**, unless independently re-proved | These implications are the mathematical core. Checker acceptance matters only if the encoded implications are sound and complete. | Conventional line-by-line proof review; independent formalization; brute-force small cases; search for a missing hypothesis or counterexample. | A theorem is false, circular, uses an unproved completeness claim, or has a stronger conclusion than its premises justify. | Tests can detect encoded inconsistencies but cannot prove general mathematical implications. `test/pcc-gpack0.test.mjs` covers finite GPack predicates only. |
| Theorem-to-record specification | Mathematical theorem statements and package contracts | Record schemas, required fields, reflection targets, and checker predicates | **Yes**, as a refinement boundary | The implementation checks records, not prose directly. The record predicate must be equivalent to the stated theorem obligations. | Build a theorem-to-field matrix; compare every field and allowed value with the theorem statement; independently implement the predicate. | A record contains assertion-shaped booleans without evidence, or omits a theorem hypothesis. | Package, global-DAG, reflection, GPack, and final-integration tests; mutation tests should remove each required field. |
| Reflection registry | Accepted checker records and theorem identifiers | Kernel conclusions assigning mathematical meaning to checker acceptance | **Yes**, within the current proof-kernel design | Reflection is where implementation-level acceptance becomes a mathematical theorem node. | Audit every checker-to-theorem mapping; replace with explicit derivations or a second independently implemented reflection checker. | A checker for a weaker property is reflected to a stronger theorem. | Kernel/Sigma/reflection tests; `test/pcc-global-proof-dag0.test.mjs`; package-sufficiency tests. |

## Generated data and executable checker boundaries

| Component | Input | Output | Trusted? yes/no/partially | Why it must be trusted | How to independently verify or replace it | Failure mode | Relevant tests |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Package generator `GeneratePCCPack()` | Source modules, schedules, templates, and generation configuration | A materialized `PCCPack` candidate | **No** | The report explicitly treats the generator as untrusted. Its output must survive independent checking. | Ignore the generator and check the committed package directly; write a second generator and compare canonical package semantics. | Generator omits a hard case, emits stale records, or includes assertion fields unrelated to actual evidence. | Generator determinism, acceptance-run, materialized-package, and replay tests. |
| Generated certificates and proof artefacts | Generator output and source data | GPack, local packages, rows, proof DAG, final integration, certificates, release records | **No** | Certificates are claims supplied to checkers. Trusting them would make checking circular. | Mutate each field; run owning checker; write independent parsers/checkers; inspect proof references and derivations. | A malformed, incomplete, stale, or self-asserting certificate is accepted. | `test/pcc-gpack0.test.mjs`; local-package, row, proof-DAG, materialized-package, final-certificate, and negative tests. |
| Parser and canonical codec | Untrusted bytes | Typed values or deterministic parse rejection | **Yes**, for byte-to-object meaning | Every later checker operates on parsed objects. Parser ambiguity or ignored bytes changes the object being proved about. | Implement a clean-room parser; differential-fuzz both parsers; formally specify the codec; test malformed and boundary encodings. | Ambiguous parse, trailing-byte acceptance, noncanonical integer/name encoding, duplicate map key, or type confusion. | `test/pcc-core.test.mjs`; `test/pcc-core.negative.test.mjs`; verifier-fragment tests. |
| Normal-form and serialization code | Typed values | Canonical normal forms and canonical byte strings | **Yes**, for canonical identity and replay | Row identity, hashes, duplicate detection, and replay depend on canonicalization. | Independent serializer; round-trip and idempotence proofs; property-based differential testing. | Two encodings for one value, one normal form for two distinct values, or non-idempotent normalization. | Core, verifier-fragment, row-key, duplicate-row, and replay tests. |
| Core structural utilities | Typed rows, modes, routes, proof references, and identifier occurrences | Row keys, route decisions, mode decisions, hash-index resolutions, and hidden-min results | **Yes**, for their implemented predicates | They are reused across package checkers and can create systemic unsoundness. | Independently implement `ComputeRowKey0`, duplicate checking, route priority, mode use, proof-reference resolution, and no-min scanning. | Selected route hidden in identity, quotient promoted to full, digest used as equality, or hidden minimization survives expansion. | `test/pcc-core.test.mjs`; `test/pcc-core.negative.test.mjs`; row and global-firewall tests. |
| Package-specific checker implementation | Untrusted package/certificate records | Accept/reject records and normal forms | **Yes**, for the current executable claim | The final claim relies on these predicates enforcing every package theorem obligation. | Audit each checker against its theorem; write an independent checker in another language; use mutation coverage for every field and branch. | Missing condition, wrong comparison, unchecked boolean, integer overflow, incomplete coverage, or fail-open behavior. | Package-specific tests such as `test/pcc-gpack0.test.mjs`, `test/pcc-local-packages0.test.mjs`, row-family tests, and materialized checker tests. |
| Proof kernel primitive rules | Typed proof nodes and premises | Derived judgments | **Yes** | Unsound primitive rules make all higher proof objects unreliable. | Give small-step mathematical semantics to each rule; verify the kernel; recheck proof DAGs with an independent kernel. | Unsound substitution, transport, induction, arithmetic, Hall, or finite-exhaustion rule. | Kernel conformance, Sigma, bootstrap, global-proof-DAG, and negative proof-reference tests. |
| Sigma schemas | Schema identifier, substitutions, and side conditions | Instantiated theorem judgments | **Yes** | A schema may encode infinitely many theorem instances. An overbroad matcher can admit false instances. | Independently validate substitution and side conditions; expand critical instances into primitive proofs. | Variable capture, missing side condition, or unintended theorem instance. | Sigma-registry and kernel-conformance tests; global-proof-DAG tests. |
| No-hidden-minimization scanner | Expanded executable artefacts and identifier classifications | Acceptance or a named forbidden executable occurrence | **Yes**, for the claim that the algorithm does not invoke exact minimization | The claimed polynomial algorithm would be circular if it called the optimization problem it purports to solve. | Independently expand macros, aliases, templates, and imports; perform AST-level call-graph analysis; inspect dynamic property access and generated code. | Alias, string indirection, imported wrapper, dynamic call, or omitted executable field hides exact search. | `test/pcc-core.negative.test.mjs`; `test/pcc-gpack0.test.mjs`; global-firewall, local-package, row, and package-expansion negative tests. |
| Mode, import, constructive, and exact-route firewalls | Mode labels, imports, obligations, routes, and proof edges | Permission or rejection for cross-boundary use | **Yes** | These boundaries prevent projected comparisons, tokens, sidecars, and bounds-only records from acting as constructive proofs. | Independent information-flow/type audit; enumerate all consumers of quotient, token, sidecar, and exact-route values. | Quotient equality becomes full replacement, forbidden package cycle is admitted, token is used as proof, or obligation is dropped. | `test/pcc-core.negative.test.mjs`; `test/pcc-global-firewalls0.test.mjs`; local-package and global-DAG tests. |
| Polynomial-bound checkers | Schedules, table sizes, selector universes, arithmetic cells, proof-size and runtime records | Accepted finite/polynomial bounds or rejection | **Yes**, for the polynomial-time conclusion | Correctness without polynomial bounds would not establish SAT in `P`. | Derive symbolic asymptotic bounds independently; measure generated sizes; inspect bit complexity and hidden enumeration. | Unary/binary size confusion, exponential table, unbounded recursion, oversized certificate, or runtime integers smuggled into state. | Schedule, bounds, row-generation, selector, package-sufficiency, and final SAT-bound tests. |
| Acceptance run and replay | Generated package, environment record, transcript, checker outputs, and canonical bytes | Accepted/rejected run and deterministic replay record | **Yes**, for linkage and replay semantics | The final certificate relies on one package and one ordered checker execution being linked exactly. | Re-run from a fresh clone; compare canonical bytes; independently replay phase order and first-failure behavior. | Stale package, digest-only linkage, skipped phase, modified transcript, or verdict detached from checker output. | `test/pcc-accept-run0.test.mjs`; replay, generated-accept-run, final-verdict, and final-acceptance-replay tests. |
| Final certificate, release gate, and proof-report checkers | Accepted package/replay records, release audit, theorem fields, and linkage digests | Final accepted release records and conditional public conclusion | **Yes**, for final publication linkage | These checkers prevent a public theorem field from being emitted before the recorded acceptance chain closes. | Independently validate every link and exact theorem string; mutate each record/digest/status field. | Theorem drift, stale release gate, missing replay, wrong package, changed antecedent, or public conclusion emitted on reject. | `test/pcc-final-pnp-certificate0.test.mjs`; release-gate tests; `test/pcc-final-proof-report0.test.mjs`. |

## Runtime, build, provenance, and publication boundaries

| Component | Input | Output | Trusted? yes/no/partially | Why it must be trusted | How to independently verify or replace it | Failure mode | Relevant tests |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Node.js runtime and JavaScript semantics | Source modules and input bytes/objects | Executed checker results | **Partially** | The implementation relies on Node's module loader, `BigInt`, `TextDecoder`, `TextEncoder`, filesystem behavior, and `node:crypto`. | Re-run on multiple supported Node 20+ builds; use a pinned container; reimplement critical checkers in another language/runtime. | Runtime bug, platform-dependent behavior, unsafe numeric conversion, Unicode difference, or module-resolution drift. | Entire `npm test` suite across multiple runtime versions; parser and arithmetic boundary tests. |
| Standard-library SHA-256 implementation | Canonical bytes | 32-byte digest | **Partially**, for byte identity/indexing only | Release seals and many internal indexes use SHA-256. Mathematical soundness is explicitly not based on digest equality. | Compare with independent SHA-256 implementations; verify full-key or canonical-byte comparison after lookups. | Wrong digest implementation, collision, digest-only equality, or hashing noncanonical bytes. | Core digest tests; hash-protocol tests; release checksum verification; replay linkage tests. |
| Build/install environment | Git checkout, Node/npm, lockfile, environment variables, filesystem, and OS | Installed dependencies, generated outputs, and test run | **Partially** | Reproduction requires deterministic source selection and sufficiently stable platform behavior. | Fresh container/VM; record versions and environment; disable undeclared network access; compare regenerated semantic fields. | Mutable dependency, local file leakage, locale/time dependence, path-dependent digests, or unrecorded tool. | `npm ci`; `npm run validate`; release-audit and regeneration commands in `REPRODUCE.md`. |
| `package.json` scripts | Working tree and runtime | Commands such as `test`, `validate`, `runall`, and release writers | **Partially** | Reviewers rely on the scripts to invoke the intended entry points, but scripts are convenience wrappers rather than proof rules. | Read the script definitions; invoke underlying Node files directly; record exact commands. | A script omits a test, points to a stale entry point, or mutates source/artefacts. | Script smoke tests where present; manual comparison with direct commands. |
| Test suite | Source and fixtures | Pass/fail evidence for finite cases | **No**, as proof evidence; **partially** as implementation evidence | Tests improve confidence and detect regressions but are not exhaustive. | Add mutation testing, coverage, fuzzing, property tests, independent fixtures, and differential implementations. | All tests pass while an untested branch or false theorem remains. | `node --test`; currently run through `npm test` and `npm run validate`. |
| CI service and workflow | Repository event, checkout configuration, runner image, secrets, and workflow definition | Public or private logs, statuses, and uploaded artefacts | **No**, as a theorem source | CI can provide reproducible execution evidence, but it is not part of the mathematical argument. At the time this document was written, no `.github/workflows/ci.yml` was present on `main`; local `npm run validate` is the explicit validation command. | Add a public workflow with pinned action SHAs and a clean clone; reproduce locally; preserve logs and environment metadata. | Shallow/wrong checkout, mutable action, cached state, secret-dependent path, skipped tests, or green status for a different commit. | Workflow self-tests after CI is added; local commands remain authoritative for reproduction. |
| Git repository and annotated tags | Commits, refs, tag objects, and remote hosting | Immutable-looking source and artefact coordinates | **Partially**, for provenance | Reviewers need stable coordinates for exact source and artefact bytes. Git naming alone does not prove correctness. | Verify tag object and peeled commit hashes; clone from independent mirrors; archive bundles; use signed tags if available. | Retagging, missing objects, wrong remote, default-branch drift, or reviewer audits `main` instead of the pinned release. | Cross-ref checks in `REPRODUCE.md`; manual `git rev-parse`; release manifest checks. |
| Release seal and `SHA256SUMS` | Named files and expected hashes/byte counts | Identity-verification result | **Partially**, for artefact identity only | The seal identifies the exact published bundle. It is deliberately outside the mathematical proof of correctness. | Recompute with independent tools; compare manifest and ledger; obtain files from multiple sources. | Missing file, stale manifest, self-referential checksum error, hash mismatch, or seal wording overstated as theorem validation. | Shell `sha256sum -c`; release-audit/seal tests; bundle validation described in `REPRODUCE.md`. |
| Published PDF/TeX report | Mathematical prose, theorem statements, release metadata, and source references | Human-readable claim and review map | **No**, as executable proof evidence | The report is the specification and explanation surface; it can be wrong, stale, or stronger than code. | Compare each theorem with source predicates and generated records; compile TeX independently; record errata. | Prose/code mismatch, stale access/release information, missing hypothesis, or accepted-record status overstated. | Documentation checks once added; current source and checker tests do not validate all prose claims. |
| Website and browser verification flow | Hosted HTML/JS, downloaded report, published digest | User-facing file check and review navigation | **No**, as theorem or checker evidence | The website is a convenience layer outside the pinned source/checker release. | Clone and inspect `aisknab/pnplabs`; compute hashes locally; follow pinned Git refs rather than website state. | Website drift, stale JavaScript, wrong digest, compromised host, or wording that implies mathematical verification. | PNP Labs site tests and seal checks in its separate repository; not part of `pnp` checker acceptance. |
| Human release operator | Source selection, tag creation, publication, and status wording | Published refs, bundles, and public descriptions | **Partially** | Someone chooses what to publish and can make provenance or wording mistakes even when checkers are correct. | Two-person release review; scripted release; signed provenance; compare expected and actual refs; publish machine-readable manifests. | Wrong tag, omitted file, stale report, accidental overclaim, or private/unreviewed material published. | Release checklist and automated coordinate checks; no test can eliminate all operator error. |

## Minimal current trusted base

For a reviewer to accept the current executable implication without replacing components, the following remain inside the effective trusted base:

1. the mathematical definitions and every claimed theorem implication;
2. the exact mapping from theorem obligations to record fields and reflection targets;
3. parser, type checker, canonical normal form, and serializer correctness;
4. proof-kernel primitive rules, Sigma instantiation, and reflection correctness;
5. package-specific checker logic, coverage claims, firewalls, and polynomial-bound checks;
6. acceptance/replay/final-linkage checker correctness;
7. the relevant semantics of Node.js and its standard library;
8. Git and SHA-256 only for the limited provenance and byte-identity properties for which they are used.

The generator, generated certificates, tests, CI, PDF, website, and release prose are not substitutes for those items.

## How to reduce the trusted base

A high-value independent verification programme should proceed in this order:

1. **Freeze the byte-level specification.** Publish the complete type, codec, normal-form, and row-key schemas independently of the JavaScript implementation.
2. **Build a clean-room parser and structural checker.** Use another language and no shared source code. Differentially check all sealed objects.
3. **Audit the kernel and reflection layer.** Reduce package theorem acceptance to a small, explicit set of primitive rules and exact reflection statements.
4. **Audit one claim-critical chain first.** Start with locked NAND: macro truth tables, baseline distinctness, trace equivalence, zero-output convention, final-lock separation, threshold, and residual slack at most four.
5. **Audit the residual-band completeness chain.** Check every route from positive residual slack through BCELReady, BN2–BN6, selectors, realizer, HB, and ZeroSlack.
6. **Prove polynomial bounds independently.** Include bit complexity, table sizes, selector counts, certificate sizes, and all dynamic-program state spaces.
7. **Run clean-room reproduction.** Use only public repositories and pinned refs; retain commands, versions, timings, and output hashes.
8. **Formalize the final theorem bridge.** State exactly what package acceptance implies and prove that implication independently of release machinery.

## Failure classification

When reporting a defect, classify it at the narrowest boundary:

- **mathematical defect**: a definition, lemma, reduction, completeness claim, or complexity bound is false;
- **specification defect**: checker predicates do not match the stated theorem;
- **checker defect**: implementation accepts an input violating its intended predicate;
- **parser/codec defect**: bytes are ambiguous, noncanonical, or inconsistently decoded;
- **provenance defect**: tags, hashes, manifests, or bundle paths identify the wrong bytes;
- **reproducibility defect**: documented public commands do not reproduce the stated implementation result;
- **presentation defect**: PDF or website wording is stale, ambiguous, or overclaims the evidence.

A hash mismatch is normally a provenance defect, not a mathematical refutation. A passing hash check is normally provenance evidence, not a mathematical validation.

## Change-control boundary

Documentation changes on `main` do not retroactively change the pinned source/checker or artefact releases. A change to any of the following should require a new source/checker release and, where applicable, new generated artefacts and seals:

- mathematical definitions or theorem statements;
- certificate schemas or semantics;
- parser or canonical encoding;
- proof-kernel rules or reflection mappings;
- checker predicates;
- package generation affecting checked bytes;
- final theorem, antecedent, or linkage semantics.

Pure reviewer documentation may be released separately, but it must say which immutable source and artefact revisions it describes.
