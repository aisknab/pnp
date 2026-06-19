# Proof and Checker Pipeline

## Purpose and review boundary

This document explains the claimed proof and checker pipeline in conventional complexity-theory and software-assurance terms before introducing repository-specific package names.

It describes what the repository claims and where the corresponding assertions are represented. It does not establish that any mathematical implication, checker predicate, complexity bound, or reflection rule is sound.

The release-specific source coordinates are:

```text
source tag:    final-pnp-proof-report-hardened-7072f8d
source commit: 7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:  final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
```

Reviewer documentation on `main`, including this file, is not itself part of the pinned theorem/checker release.

## 1. Problem statement in standard terms

`P` is the class of decision problems solvable by a deterministic polynomial-time algorithm. `NP` is the class of decision problems for which a proposed positive answer can be verified in polynomial time. SAT is NP-complete.

A proof that SAT has a deterministic polynomial-time decision algorithm would imply:

```text
SAT is in P
=> every language in NP reduces to a language in P
=> NP is contained in P
=> P = NP
```

The repository claims such a SAT algorithm by reducing SAT to an exact circuit-minimisation problem on a restricted family of multi-output NAND circuits, then claiming a polynomial-time exact minimiser for those instances.

The logical route is:

1. convert a Boolean formula or circuit to NAND;
2. build a restricted NAND minimisation instance and an integer threshold;
3. compute the exact minimum size of that instance;
4. decide SAT by comparing the exact minimum with the threshold;
5. prove that every step, including the exact minimisation, runs in polynomial time.

The checker and release machinery are a second layer. They are intended to establish that a finite package encoding the mathematical route satisfies the predicates implemented by the repository. Checker acceptance is not a substitute for auditing the mathematical route or the checker predicates.

## 2. Claimed mathematical route

For a NAND circuit `phi`, the repository constructs a locked multi-output NAND direct-wire word `W_phi` and a baseline `B_phi`.

The claimed threshold theorem is:

```text
phi is unsatisfiable  => mu(W_phi) = B_phi
phi is satisfiable    => B_phi + 1 <= mu(W_phi) <= B_phi + 4
```

Therefore:

```text
phi is satisfiable iff mu(W_phi) > B_phi
```

The constructed word has size `B_phi + 4`, so the claimed residual slack is:

```text
Lambda(W_phi) = size(W_phi) - mu(W_phi) <= 4
```

The repository then claims that its residual-band algorithm, called `PCCMin`, computes an exact minimum in polynomial time whenever the starting residual slack is logarithmically bounded. Since the locked instance has residual slack at most four, the claimed SAT algorithm is:

```text
M = PCCMin(W_phi)
return SAT iff size(M) > B_phi
```

The final complexity-theory step is standard only if all preceding statements hold uniformly and in polynomial time.

## 3. Mathematical pipeline and executable evidence pipeline

```mermaid
flowchart TD
  subgraph M[Claimed mathematical and algorithmic pipeline]
    A[Boolean formula or circuit] --> B[Polynomial conversion to NAND]
    B --> C[Build locked multi-output NAND word W_phi]
    C --> D[Compute baseline B_phi]
    C --> E[Prove locked threshold and residual slack at most 4]
    D --> F[Exact residual-band minimiser PCCMin]
    E --> F
    F --> G[Obtain exact minimum mu(W_phi)]
    G --> H[Compare mu(W_phi) with B_phi]
    H --> I[SAT decision in polynomial time]
    I --> J[P = NP via SAT NP-completeness]
  end

  subgraph X[Executable certificate, checker, and release pipeline]
    K[GeneratePCCPack0: untrusted generator] --> L[Materialised PCCPack]
    L --> M1[Structural, kernel, row, package, firewall, GPack, and final checks]
    M1 --> N[CheckPCCPackexp0 acceptance record]
    N --> O[Acceptance run and canonical-byte replay]
    O --> P[Final certificate and release gate]
    P --> Q[CheckFinalPNPProofReport0]
    Q --> R[Conditional public conclusion record]
    R --> S[Release seal and SHA-256 ledgers]
  end

  E -. encoded by GPack and proof DAG .-> M1
  F -. encoded by local packages, ZeroSlack, and package sufficiency .-> M1
  J -. encoded by final framework, reflection, and final theorem records .-> P

  T[Independent review required] -. audits mathematics .-> M
  T -. audits checker soundness .-> X
```

The final seal authenticates published bytes. It does not validate any mathematical arrow.

## 4. Stage-by-stage audit map

| Stage | Conventional claim | Repository terms | Where correctness is asserted | Where polynomial time is asserted | Primary implementation and tests | A decisive refutation would be |
| --- | --- | --- | --- | --- | --- | --- |
| 1. Input and NAND conversion | Every supported Boolean input is converted to an equisatisfiable NAND circuit with polynomial blow-up. | `PreNAND`, `NandConversion` | Report §§17–18; `GPack.PreNAND`; `SATDecision.NandConversion`. | `SATBounds.Converter`; final polynomial-bound records. | `pcc-gpack0.mjs`; `pcc-final-framework0.mjs`; `test/pcc-gpack0.test.mjs`; `test/pcc-final-framework0.test.mjs`. | An input whose conversion changes satisfiability, changes the declared output, or has super-polynomial size. |
| 2. Locked instance construction | The NAND circuit is transformed into one restricted multi-output NAND instance with a computable baseline. | Locked NAND, `G-Sep+`, `G-Coh`, macro tables, `BaselineCert` | Report §17 and Appendix A; GPack certificates; locked-NAND proof-DAG nodes. | `BoundsCert`, `SATBounds.LockedBuilder`, public schedule. | `pcc-gpack0.mjs::CheckGPack0`; `computeLockedNANDBaseline0`; G row-family checker; GPack tests. | A slot collision, false macro truth table, collapsed exposed output, incorrect baseline, or input-dependent super-polynomial construction. |
| 3. Threshold theorem | Exact minimum equals the baseline in the unsatisfiable case and exceeds it in the satisfiable case. | `BaselineDistinct`, `TraceEquivalence`, `ZeroOutputConvention`, `FinalLockSeparation`, `G.ThresholdCert.proof` | Report Theorem 17.2 and Lemmas 17.3–17.7; `GlobalProofDAG` G nodes; `FinalIntegration` G linkage. | The threshold construction itself must be polynomial; the theorem is otherwise a correctness statement. | `pcc-gpack0.mjs`; `pcc-global-proof-dag0.mjs`; `pcc-final-framework0.mjs`; their negative tests. | A satisfiable instance with minimum at the baseline, an unsatisfiable instance above the baseline, a baseline output that is constant/projection/duplicate, or a final output not separated by the fresh lock. |
| 4. Residual-slack bridge | The locked instance is within four gates of its exact minimum. | `Lambda(C)`, residual band, `SlackMap` | Report Theorem 17.2; GPack threshold record; final framework match. | The bound four is used to limit the number of descent steps. | `pcc-gpack0.mjs`; `pcc-final-framework0.mjs`; residual-slack negative tests. | A constructed instance with residual slack above four or a mismatch in the size/minimum convention used by G and O. |
| 5. Exact minimisation in the residual band | A deterministic algorithm returns an exact equivalent minimum when residual slack is bounded. | `PCCMin`, `PCCOracle`, `ZeroSlack`, packages E through O | Report §§2–16, especially Theorems 16.1–16.2; `PackSufficiencyTheorem.residualBandMinimization`; proof-DAG package nodes. | Each verified gain lowers residual slack; all local tables, DPs, selectors, ledgers, and certificates are claimed polynomial. | `pcc-local-packages0.mjs`; `pcc-pack-sufficiency0.mjs`; `pcc-global-proof-dag0.mjs`; local-package and package-sufficiency tests. | A positive-slack circuit that reaches `ZeroSlack`, an unhandled route, an invalid gain, an exact route without proof, a circular HN/BUD blocker, or any super-polynomial subroutine/state space. |
| 6. Framework compatibility | The minimiser and locked construction use exactly the same syntax, outputs, charges, carrier constants, minimum notion, and residual-slack definition. | Package O/G framework match, `SyntaxMap`, `ChargeMap`, `CarrierMap`, `OutputMap`, `MinMap`, `SlackMap` | Report §§18.4 and 20.6; `CheckFinalFrameworkMatch0`. | The bridge must preserve the already-claimed polynomial bounds. | `pcc-final-framework0.mjs`; `test/pcc-final-framework0.test.mjs`. | O minimises a different model from G, uses a different output convention, or treats profile data/constants differently. |
| 7. SAT decision | Exact minimum above the baseline means SAT; equality means UNSAT. | `SATDecision`, `DecisionRule`, `PCCMinBridge` | Report §18.4; `CheckSATDecision0`; `CheckFinal0`. | `CheckSATBounds0`; final polynomial-bound record. | `pcc-final-framework0.mjs`; `pcc-final0.mjs`; final-framework and final tests. | Approximate rather than exact minimisation is accepted, comparator direction is wrong, or the decision record is not bound to the accepted GPack. |
| 8. Package sufficiency | The finite package contains every required theorem, row, rule, bound, and linkage needed for the route. | `PCCPack`, `CheckPackSufficiency0`, proof DAG, reflection, firewalls | `PackSufficiencyTheorem`; global proof DAG; reflection registry; local and global checkers. | Bounds ledgers, schedule, row generation, and package theorem all claim finite polynomial checking. | `pcc-pack-sufficiency0.mjs`; `pcc-global-proof-dag0.mjs`; `pcc-global-firewalls0.mjs`; `pcc-rows0.mjs`; package tests. | A required theorem is represented only by an assertion-shaped field, a missing premise still accepts, a reflection maps a weaker checker to a stronger theorem, or coverage is incomplete. |
| 9. Materialised package acceptance | The actual generated package bytes satisfy the concrete top-level checker and public claim boundary. | `GeneratePCCPack0`, `CheckConcreteMaterializedPCCPack0`, `CheckPCCPackexp0` | Concrete package checker and record-alignment checks. | Checker runtime must be polynomial in package/input size; generation is explicitly untrusted. | `pcc-generate-pcc-pack0.mjs`; `pcc-pack-concrete-materialized0.mjs`; `pcc-check-pcc-pack-exp0.mjs`; materialised tests. | Checker acceptance can be obtained with missing concrete coverage, mismatched records, noncanonical JSON, or a changed claim boundary. |
| 10. Replay and publication | The accepted package is the package replayed and named by the final certificate, release gate, and report. | `AcceptRun`, replay, final certificate, release gate, final proof report | Acceptance-run, canonical-byte replay, final linkage, exact theorem fields. | Replay and checking are claimed polynomial over finite artefacts. | `pcc-accept-run0.mjs`; `pcc-final-acceptance-replay0.mjs`; certificate, release-gate, and proof-report modules/tests. | Digest-only substitution, skipped phase, stale package, theorem drift, reject run emitting a public conclusion, or mismatched canonical bytes. |
| 11. Release identity | Published files are the files named by the release. | artefact tag, `release-seal.json`, `SHA256SUMS` | File hashes, sizes, paths, tag/commit coordinates. | Not part of the SAT runtime claim. | Sealed artefact directory; `REPRODUCE.md`; independent `sha256sum`. | Missing/mismatched bytes or stale coordinates. A successful hash is not evidence against a mathematical counterexample. |

## 5. Where correctness is asserted

The route has several distinct correctness obligations. A reviewer should not treat a single top-level `accept` as proving all of them automatically.

### 5.1 Semantics and replacement correctness

The base framework claims that a compatible subcircuit can be replaced by a smaller same-frontier circuit without changing the global Boolean function. Package E is intended to make each constructive saving explicit and checkable.

Review targets:

- exact input and output semantics of direct-wire NAND words;
- compatibility of support boundaries;
- same-frontier equality;
- charge ownership and size accounting;
- obligation creation and discharge;
- transport of gains through normalization and splice.

Primary artefacts:

```text
canonical_proof_report.tex §§2–6
pcc-local-packages0.mjs
pcc-global-proof-dag0.mjs
pcc-global-firewalls0.mjs
```

### 5.2 Locked-NAND reduction correctness

The reduction requires all of these claims:

1. NAND conversion preserves satisfiability.
2. Macro truth tables are correct.
3. slot families are disjoint and locks are fresh;
4. every baseline output is distinct, nonconstant, and nonprojection;
5. the prefix covers every distinguished check exactly as claimed;
6. the trace predicate is equivalent to a valid NAND evaluation;
7. unsatisfiability makes the final output identically zero on the whole carrier;
8. satisfiability makes the fresh-lock output distinct from the baseline;
9. the baseline formula and four-gate overhead are exact.

The checker records these through GPack fields, G proof-DAG nodes, row coverage, and final G linkage. A reviewer must still verify that the implemented predicates prove the mathematical statements rather than merely restating them as booleans.

### 5.3 Residual-band minimisation correctness

The central completeness chain is:

```text
positive residual slack
=> positive residual witness
=> saturated BCEL-ready positive nucleus
=> BN2–BN6 packet
=> faithful selector
=> verified gain or typed blocker
=> blocker/rank contradiction
=> ZeroSlack is impossible under positive slack
```

The exact-minimisation theorem also relies on hereditary and budget exact routes. The highest-risk correctness points are completeness claims: every positive residual state must enter some governed case, every failed route must be named, every negative sidecar must be total, and all mutual blocker dependencies must be well-founded.

Primary artefacts:

```text
canonical_proof_report.tex §§7–16
pcc-local-packages0.mjs
pcc-global-proof-dag0.mjs
pcc-pack-sufficiency0.mjs
```

### 5.4 Checker-to-theorem correctness

The repository uses package theorem records, a proof kernel, Sigma instances, and reflection records to assign mathematical meaning to checker acceptance. This refinement boundary is part of the trusted base.

A reviewer must compare, field by field:

```text
mathematical theorem
<-> record schema and required evidence
<-> checker predicate
<-> reflection conclusion
<-> final proof-DAG edge
```

A test that mutates one boolean field demonstrates only that the checker reads that field. It does not demonstrate that the field has an independently justified derivation.

### 5.5 Final complexity-theory implication

The final implication requires:

```text
accepted exact minimiser for the locked instances
+ correct locked threshold
+ polynomial construction and minimisation
+ standard SAT NP-completeness
=> P = NP
```

`pcc-final-framework0.mjs`, `pcc-final0.mjs`, and the final proof-DAG nodes encode this bridge. The final theorem is valid only if the earlier mathematical and checker-soundness obligations are valid.

## 6. Where polynomial time is asserted

Polynomiality is not established merely by storing `polynomial: true` or an exponent in a record. The reviewer must derive each bound from the actual data structures and control flow.

| Polynomiality claim | Repository assertion surface | What must be independently checked |
| --- | --- | --- |
| Boolean-to-NAND conversion | `PreNAND`; `SATDecision.NandConversion`; `SATBounds.Converter` | Output size and runtime as functions of the original input encoding; preservation of the declared output. |
| Locked-word construction | GPack bounds; `SATBounds.LockedBuilder` | Number of slots, macro instances, prefix nodes, outputs, records, and proof objects; bit length of counts. |
| Finite-table evaluation | public schedule, FT rows, truth evaluator | Whether boundary arity is truly fixed/schedule-bounded independently of input; cost of `2^beta`; total number of rows generated. |
| Branch/cycle and unary routing | BC and UN transition systems | State alphabet size, graph size, transition composition, cycle/branch checks, and whether any radius or alphabet grows with input. |
| HN and BUD exact routes | hereditary grammar and budget DP | Grammar/state-graph size, numeric bit complexity, reconstruction cost, and ParseOrExit coverage. |
| BCEL-ready nucleus | residual witness and anchor construction | Whether finding a minimal positive subset enumerates exponentially many anchor subsets; whether anchors are polynomially bounded; how positivity is tested without an exact-minimum oracle. |
| BN2–BN6 | side-tight bases, antichains, matching, cancellation, hypergraph cells | Number and size of bases, minimal-consumer antichains, request atoms, matching graphs, integer masses, and packet cells. |
| Selector enumeration | `K2`, `K3`, `Ksp`; claimed bound `|C|^3 (log |C|)^O(1)` | Handle/payload bit lengths, construction time, duplicate control, and proof that every packet has a selector without exponentially large payload. |
| Realizer and verified gain | Package R and E | Decoder runtime, support/replacement size, charge-ledger size, and verifier runtime. |
| ZeroSlack certificate | rank list, selector-silence logs, sidecars, blocker graph, contradiction DAG | Number of ranks/selectors/candidates, total negative evidence, canonical encoding size, and verification time. |
| Number of descent iterations | global slack law and residual band | Every nonterminal step must lower the same integer residual measure by at least one; normalization must not reset or hide the measure. |
| Package checking | schedule, rows, proof DAG, parser, hashes | Total package byte size, parser/canonicalization cost, proof-DAG traversal, and all integer-operation bit costs. |
| Final SAT algorithm | `CheckSATBounds0`; `Final.PolynomialBound` | A uniform polynomial bound from original input length through conversion, construction, minimisation, and comparison. |

The source contains claimed example exponents in bound records, including converter, minimiser, and final exponents. Those numeric fields are audit targets, not independent derivations.

## 7. Where exact minimisation enters

Exact minimisation appears in several logically different places.

### 7.1 Mathematical definitions

The report defines:

```text
mu(C)      = minimum size of an equivalent closed circuit
mu*(F)     = minimum size of a same-frontier open realization
Lambda(C)  = size(C) - mu(C)
```

These are legitimate mathematical definitions. Mentioning them in theorem statements is not an executable algorithm.

### 7.2 The locked threshold

The SAT reduction is stated directly in terms of the exact value `mu(W_phi)`. An approximation is insufficient because the satisfiable and unsatisfiable cases differ by as little as one gate.

### 7.3 Exact subroutes

HN and BUD are claimed to return exact minima for governed subclasses. Their dynamic programs and completeness conditions must be audited independently. An `ExactRoute` token is not enough; the route must resolve to evidence that the final checker recognizes as an exact minimum.

### 7.4 ZeroSlack

`ZeroSlack` is intended to certify that the current circuit has no positive residual slack. It is an indirect exact-minimum certificate: if sound, `Lambda(C)=0` implies the current circuit is minimum.

This is the most important place to distinguish a derivation from assertion-shaped fields. The certificate must prove that every gain, exact route, selector, hereditary case, budget case, and blocker has been handled soundly and completely.

### 7.5 `PCCMin`

The claimed executable minimiser repeatedly applies verified gains and returns on an exact route or sound `ZeroSlack`. Its polynomial runtime depends on two facts:

1. every nonterminal gain strictly decreases the same residual measure;
2. the starting residual slack is bounded.

### 7.6 SAT comparison

The final decision uses the exact size returned by `PCCMin`:

```text
SAT iff exact_minimum > baseline
```

Any approximate, heuristic, promise-only, or unverified minimum invalidates the comparator.

## 8. Where hidden search or exponential work could enter

| Risk surface | Why it is dangerous | Claimed control | Reviewer inspection target |
| --- | --- | --- | --- |
| Aliases and wrappers around minimisation | A forbidden operation can be renamed. | Expand aliases before classifying executable identifiers. | Alias tables, imported bindings, generated templates, and every call site. |
| Dynamic property access, computed strings, callbacks, or reflection | A syntactic name blacklist may not see a semantically equivalent call. | Restricted first-order executable language is claimed. | Prove the implementation actually forbids or models these JavaScript features; inspect all dynamic dispatch. |
| Reimplementation of exhaustive minimisation without a forbidden name | A brute-force search can avoid names such as `argmin`. | Bounds, finite schedules, and package-specific algorithms are claimed to restrict the computation. | Loop bounds, recursive calls, candidate generation, truth-table enumeration, and search trees. |
| Truth-vector enumeration | `2^beta` is exponential in `beta`. | `beta` is claimed schedule-bounded. | Prove `beta` is a fixed constant or suitably logarithmic and cannot depend privately on input size. |
| Minimal positive nucleus | Selecting an inclusion-minimal positive subset may require checking all anchor subsets. | Finite anchors, rank descent, and certificates are claimed. | Concrete algorithm, number of subsets examined, positivity predicate, and certificate size. |
| Minimal-consumer antichains | A monotone function may have exponentially many minimal true sets. | Schedule-bounded finite request systems and compressed antichain codes are claimed. | Worst-case antichain cardinality and encoding; construction versus mere assertion. |
| All-cut identities | Enumerating all cuts is exponential in anchor count. | BN4 claims activation equality by canonical active-antichain code rather than cut enumeration. | Proof that code equality is equivalent to activation equality and that codes remain polynomial size. |
| Matching and restoration universes | Matching is polynomial only in an explicitly polynomial graph. | BN5/PkgC use finite matching graphs. | Size and construction cost of both vertex sets and all edges. |
| HN/BUD dynamic programs | Dynamic programming can have exponentially many states. | Accepted finite grammars and envelope bounds are claimed. | State-key width, transition count, payload size, and dependence on schedule/runtime integers. |
| Selector universe | Triple and spine payloads can hide large descriptions. | Claimed polynomial selector bound and finite payload alphabets. | Actual handle count, payload encoding length, generation time, and completeness proof. |
| ZeroSlack negative evidence | Exhaustively proving absence can be larger than the object being checked. | Claimed polynomial-size sidecars, rank lists, selector logs, and proof DAG. | Exact candidate counts and whether one certificate entry covers a class soundly rather than listing exponential cases. |
| Integer arithmetic | Unit-cost arithmetic can hide exponential bit complexity. | Runtime integers are placed in arithmetic cells. | Maximum bit length and cost of addition, comparison, multiplication, encoding, and Presburger checks. |
| Package generation | A fixed package can hide unrecorded precomputation, and an input-dependent package can destroy uniformity. | Generator is untrusted; checker validates materialized output. | Whether the SAT algorithm uses one fixed finite package, how it is accessed, and whether any input-dependent proof search occurs before checking. |
| Canonicalization and hashing | Runtime is linear or worse in object byte size; object size may already be exponential. | Polynomial package and certificate bounds are claimed. | Total bytes, recursion depth, sorting costs, map/set canonicalization, and duplicate resolution. |

## 9. How the checker attempts to rule out hidden minimisation

The repository's control is layered.

### 9.1 Forbidden identifier set

The source includes forbidden names such as:

```text
mu, mu*, mu#, Can, argmin, maxG,
minimumEquivalent, optimalCircuit, exactMinSearch,
canonicalMinimizer, maximizeGain
```

The exact source uses mathematical Unicode names for some entries.

### 9.2 Occurrence classification

Identifier occurrences are intended to be classified as definition/import, sound import, executable call, theorem-only assumption, or emitted token. Forbidden names reject only when they occur in an executable position.

This distinction is necessary: the mathematical definition of `mu` may appear in a theorem, while an executable call to an exact minimiser would be circular.

### 9.3 Expansion before scanning

The package and final records claim expansion of:

```text
macros
aliases
generated templates
imports
```

before the no-hidden-minimisation scan.

### 9.4 Repeated enforcement points

The no-min rule appears at several levels rather than only once:

```text
pcc-core.mjs::CheckNoHiddenMin0
pcc-global-firewalls0.mjs::CheckGlobalFirewalls0
pcc-global-proof-dag0.mjs::CheckGlobalProofDAG0
pcc-gpack0.mjs::CheckGPack0
pcc-final-framework0.mjs
pcc-final0.mjs
pcc-pack-sufficiency0.mjs::CheckPackSufficiency0
pcc-check-pcc-pack-exp0.mjs::CheckPCCPackexp0
pcc-accept-run0.mjs
```

Negative fixtures include executable `minimumEquivalent` occurrences and expanded GPack artefacts.

### 9.5 Supporting controls

The scanner is supplemented by:

- an acyclic import graph and forbidden import edges;
- mode firewalls preventing quotient comparisons from becoming full replacements;
- route-priority checks preventing a constructive gain from being downgraded;
- canonical row keys and duplicate-conflict rejection;
- typed proof references and proof-DAG acyclicity;
- polynomial bounds and schedule checks;
- canonical-byte replay rather than digest-only equality.

### 9.6 Limit of the control

A name-based or AST-shape scanner does not by itself prove polynomial time or absence of exact search. It is sound only if:

1. the executable language is completely identified;
2. all aliases, imports, templates, generated code, and dynamic dispatch are expanded or forbidden;
3. semantically equivalent brute-force search is caught by complexity-bound checks;
4. theorem-only minimum fields cannot be consumed as executable oracle results;
5. every executable module used by the decision path is included in the scan.

These are independent audit obligations.

## 10. Artefacts a reviewer must inspect

### 10.1 Pinned source and artefact coordinates

```bash
git fetch --tags --force
git checkout final-pnp-proof-report-hardened-7072f8d
git rev-parse HEAD

# Expected source commit:
# 7072f8d0bda6d44d240f9bb3fad624fd357e1278
```

For release identity:

```bash
git checkout final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
B=proof-artifacts/final-pnp-proof-report-hardened-7072f8d
sha256sum -c "$B/SHA256SUMS"
sha256sum -c "$B/SHA256SUMS.sha256"
```

### 10.2 Inspection map

| Review question | Required artefacts |
| --- | --- |
| What problem and circuit model are being solved? | `canonical_proof_report.tex` §§1–5; `pcc-core.mjs`; [terminology_crosswalk.md](terminology_crosswalk.md). |
| Does local replacement preserve global semantics and size accounting? | Report §6; `pcc-local-packages0.mjs`; charge/obligation/mode modules and tests. |
| Is every finite/local route complete and polynomial? | Report §§7–15; local-package records; rows; schedule; package-specific tests. |
| Is `ZeroSlack` sound and polynomial-size? | Report §16; `pcc-pack-sufficiency0.mjs`; `pcc-local-packages0.mjs`; `pcc-global-proof-dag0.mjs`; related tests. |
| Does the locked construction preserve SAT and produce the exact threshold? | Report §17 and Appendix A; `pcc-gpack0.mjs`; `test/pcc-gpack0.test.mjs`; G proof-DAG nodes. |
| Do O and G use the same formal framework? | `pcc-final-framework0.mjs`; `test/pcc-final-framework0.test.mjs`. |
| Is the SAT comparator exact and polynomial? | Report §18.4; `CheckSATDecision0`; `CheckSATBounds0`; `pcc-final0.mjs`; their tests. |
| Does package acceptance cover every required theorem and row? | `pcc-pack-sufficiency0.mjs`; `pcc-rows0.mjs`; `pcc-global-proof-dag0.mjs`; `pcc-global-firewalls0.mjs`; package tests. |
| Can hidden minimisation or exponential work enter? | `pcc-core.mjs`; all `FORBIDDEN_EXEC_SYMBOLS` lists; no-min records; import graph; bounds/schedule modules; negative tests. |
| Is the generator genuinely untrusted? | `pcc-generate-pcc-pack0.mjs`; materialized package checkers; acceptance-run and replay modules. |
| Is the accepted package the package named by the final report? | `pcc-check-pcc-pack-exp0.mjs`; `pcc-accept-run0.mjs`; final replay/certificate/release-gate/proof-report modules and tests. |
| Do hashes identify the intended files? | sealed artefact tag, `release-seal.json`, `SHA256SUMS`, `SHA256SUMS.sha256`, and `REPRODUCE.md`. |
| What remains in the trusted base? | [trust_model.md](trust_model.md). |

### 10.3 Minimum evidence for a stage to count as reviewed

For each stage, a reviewer should record:

```text
mathematical statement:
input and output model:
source theorem/section:
record schema:
checker function:
reflection or proof-DAG node:
positive test:
negative or mutation test:
polynomial bound:
independent derivation or counterexample search:
remaining assumption:
```

A source pointer plus a passing test is not a complete review result.

## 11. Recommended validation order

1. Freeze the input model, output convention, size measure, and exact-minimum definition.
2. Audit parser, canonical encoding, row identity, proof-reference resolution, and hash-as-index discipline.
3. Audit the locked-NAND construction and threshold independently on small exhaustive instances.
4. Audit the O/G framework match.
5. Audit the residual-band completeness chain, beginning with Terminal MuBridge and `ZeroSlack`.
6. Derive every claimed polynomial bound from actual loops, state spaces, and encoded sizes.
7. Audit proof-kernel rules and reflection mappings.
8. Audit package coverage and final proof-DAG dependencies.
9. Reproduce the materialized package acceptance and canonical-byte replay.
10. Verify release hashes last; they identify the reviewed bytes but do not validate them.

## 12. Interpretation boundary

This pipeline document does not claim that:

- the locked-NAND reduction is correct;
- `PCCMin` is exact or polynomial;
- the no-hidden-minimisation scan is complete;
- checker acceptance implies the stated mathematical theorem;
- the sealed package has received independent mathematical validation;
- a passing test suite or SHA-256 ledger proves `P = NP`.

It identifies the complete claimed route and the points at which a reviewer can falsify or independently validate it.
