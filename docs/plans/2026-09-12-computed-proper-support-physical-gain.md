# M238 plan: computed proper-support physical gain

This is a pre-implementation specification, not an earned release claim.
Preparation is pinned to verified M237 feature
`cb8743df9db8482afddb2da828f42580e9b3317a`, tree
`e31864a41626ce0f3d75a47366642ac2eed7c4a3`.
All four M237 PR workflows passed and M237 is merged at
`bd5ad3bce884167c7ba5efdfab8fca6acd2eb3d9`, with that same source tree.
This branch is reanchored to the actual merge. Its independent exact-merge
reproduction passed; all post-merge workflows remain release prerequisites
before publishing M238.

## Manuscript anchor and missing dependency

The manuscript pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json)
defines compatible replacement and the Global slack law in section 2.
The support calculus in section 3 and the verified-gain outcomes used by
RW-SaturatePositive in section 10 require an actual same-function smaller
descendant, not just an assertion that a local support has positive slack.

The existing production search
`findTerminalCandidateProperPositiveSupport` computes a proper positive seed.
M237 computes the surrounding physical context and transports arbitrary
equivalent replacements. The remaining edge is to produce the whole replacement
from that search result and prove its exact physical size and slack descent.

Connect these existing computations into one total optional physical gain step.
Use the existing exhaustive reference-minimum witness; do not introduce another
minimizer or supply a seed, replacement, frame, ownership map or correctness
certificate as an algorithm input. This is the physical gain-realization edge,
not a complete named full-profile route or a polynomial PCCMin iteration.

## Unbounded construction and exact interfaces

Quantify over arbitrary `inputs gates outputs profileWidth : Nat`,
`candidate : Candidate inputs gates outputs`, and
`model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate`.

Use these shared names for computed definitions, not new premises:

```lean
system := terminalCandidateSaturationSystem candidate model
support seed := extractSaturatedTerminalSupport candidate system seed
gain seed := terminalSupportLocalGain candidate system seed
context seed := terminalCandidateSaturatePhysicalContext candidate model seed
replacement seed :=
  ((context seed).plug (support seed).extractedCandidate.referenceMinimumReplacement).toImplementation
```

Define
`terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed`
to return that `Implementation inputs outputs`.
Define `findTerminalCandidatePhysicalGain candidate model` by mapping this
construction over the existing production proper-positive search. Its result
type is `Option (Implementation inputs outputs)`. Returning `none` must not
mean that the whole candidate is minimal.

The five planned public theorem interfaces are:

1. `terminalCandidateSaturatePhysicalMinimumReplacement_equivalent`:
   for every seed, the computed replacement's complete ordered Boolean output
   word is equivalent to the original candidate at every input valuation.
2. `terminalCandidateSaturatePhysicalMinimumReplacement_size_gain`:
   for every seed,
   `(replacement seed).gateCount + gain seed = gates`.
   There is no positivity, properness, supplied partition or size-bound premise.
3. `terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain`:
   for every seed,
   `residualSlack (replacement seed) + gain seed =
     residualSlack candidate.toImplementation`.
4. `findTerminalCandidatePhysicalGain_sound`:
   if the actual search returns `some result`, derive a canonical seed selected
   by `findTerminalCandidateProperPositiveSupport`, its properness and positive
   gain, equality of `result` with its computed replacement, whole-circuit
   equivalence, the exact size/slack equations above, and strict decrease of
   both physical gate count and physical residual slack.
5. `findTerminalCandidatePhysicalGain_eq_none_iff`:
   the actual search returns `none` exactly when no seed in
   `allTerminalSupportSeeds inputs gates outputs profileWidth` is both proper
   and positive for the candidate-derived system.

The search equality in the soundness theorem is an observation of the actual
algorithm output, not a caller-supplied replacement-correctness certificate.
Use the existing exact search-failure theorem; do not weaken the failure result
to a finite fixture or strengthen it to ZeroSlack.

## Proof and regression order

1. Define the computed reference replacement through M237's context. Prove
   equivalence using the already audited minimum witness and replacement law.
2. Derive exact physical gate-count accounting from M237's selected/complement
   partition and the reference-minimum bound.
3. Transport minimum invariance and exact framed slack accounting to the
   original candidate, deriving the exact whole-circuit slack equation.
4. Compose the production search, then prove success and failure contracts with
   no alternative enumeration, injected seed or replacement certificate.
5. Add arbitrary-dimension permanent theorem applications and executable
   regressions. Include empty and zero-width candidates, a real proper positive
   prefix whose removal shrinks the whole candidate, repeated outputs and input
   bypasses, and a globally redundant double-negation candidate with no proper
   positive saturated support. The latter protects the difference between
   proper-support search failure and global minimality; it is not a claim that
   the manuscript's other named routes fail.

The arbitrary-dimension theorems, explicit-root axiom audit and all permanent
regressions now pass. A rich complete-search fixture was too expensive and its
failed run is discarded. Bounded prefix checks isolated the complete exhaustive
search; the richer fixed-seed replacement, output and slack checks passed.
The final regression retains those cases and uses a smaller circuit for the
complete seed-search/minimum/context pipeline. This does not change a theorem
statement or replace the general proof with a finite-instance claim.

Do not change the previous saturation executor, support extractor, observer,
reference minima, classifier, physical charge ledger or M237 context to make
this theorem easier. Keep a new module `PNP.ResidualTerminalPhysicalGain`.
If the general construction fails, report the actual missing edge; do not add a
correctness premise, weaken the algorithm statement or substitute a finite case.

## Consumer and verification matrix

| Producer | Consumers to reconcile before expensive verification | First check |
| --- | --- | --- |
| Computed gain and five universal contracts | Source contracts, permanent Lean regressions, explicit root and strict axiom transcript | Exact module build and focused hostile/source checks |
| Reviewed theorem names | Lean inventory list, JavaScript required names, publication row and fingerprint keys | Exact name-set equality before inventory extraction |
| Audit package script | Closed package-script contract and durable verification list | Focused package-script assertion |
| Status fields and coordinate | Both exact status contracts, boolean mutation lists and generated mirrors | Current acceptance and focused changed-contract cases |
| Compiled evidence | Canonical/public inventories, publication map, progress history, current core docs and report | Structured field delta and compiled hostile checks |
| Added workflow shell block | Exact extracted script after explicit root | Shell syntax and exact command execution |

Run all processing in the isolated remote checkout. Preserve successful evidence
for unchanged source, inputs, toolchain and trust boundary. Use one standard
union of required test files, with no unproved selection wrapper or duplicate
standalone global status-mutation run. Persist the raw child exit and summary
before aggregate assertions. Require final terminal success, normal PR checks,
independent exact-object verification, and all exact-merge post-merge checks.

Initialize clone-local commit metadata from the established project identity
during setup; deployment-key authentication and Git author metadata are separate
preflights. Before a new clone writes, verify its dedicated repository identity,
origin, fresh fetch and dry-run push.

## Remaining obligations and progress

The observer/profile model remains supplied. The search enumerates all canonical
record subsets and reference implementations; it is an exhaustive finite
reference construction, not a polynomial encoded-size or runtime algorithm.

Whole Boolean equivalence is not full-profile replacement compatibility,
obligation transport, the complete materializer charge universe, fixed global
ownership, full-minimum growth, or a named route's complete rank theorem.
No input-derived complete terminal family, global route coverage, unconditional
SaturatePositive/BCELReady/ZeroSlack, complete polynomial PCCMin, deterministic
CNFSAT in P or eligible root theorem follows.

M237's reviewed ledger reports formal artefact coverage of 213 of 215 current
scoped rows earned, risk-weighted proof completion estimate 40%, uncertainty
20% to 40%, and global gates closed 0 of 5. Project-specific axioms are absent,
but the eligible root remains absent and the publication gate is false.
No fixed weighted checkpoint or global gate change is anticipated for M238.

Publication decision: defer. This establishes the physical reference
gain-realization subcomponent, not a complete full-profile/global or polynomial
route. Preserve the coherent M231 PNPLabs source pin. Continue meaningful core
submilestone and release notifications independently of website cadence.
