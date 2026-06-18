# Reviewer Outreach Targets: 7072f8d Residual-Hardened PNP Release

Status: **target list for hostile external review outreach**.

Use this as a targeting guide, not as an endorsement list. Contact people one at a time, using only their current official institutional profile, homepage, or contact form. Do not mass-email. Do not describe the release as Clay-prize-ready; describe it as a sealed, checker-gated, external-review-ready candidate.

## Email subject

```text
Hostile review request: checker-gated P=NP proof package, 7072f8d frozen release
```

## One-paragraph opener

```text
I am seeking hostile external review of a frozen, checker-gated P=NP proof package. The public theorem boundary is CheckPCCPackexp(GeneratePCCPack())=accept => P = NP. The 7072f8d release is sealed, validated, and reproducible, but I am not representing it as settled; I am asking independent experts to try to break it. The review packet includes a hostile checklist, reproduction guide, canonical PDF, and sealed artifact tags.
```

## Send order

```text
1. review/final_external_review_cover_7072f8d.md
2. review/hostile_review_checklist_7072f8d.md
3. review/submission_readiness_memo_7072f8d.md
4. REPRODUCE.md
5. REVIEWER_MAP.md
6. canonical_proof_report.pdf
7. repository tags:
   - final-pnp-proof-report-hardened-7072f8d
   - final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
   - final-pnp-proof-report-docs-hardened-7072f8d-sealed
```

## Priority 1: complexity-theory gatekeepers

These are the first people to contact for the final implication, SAT/P-vs-NP boundary, and whether the proof route is even plausible as a complexity-theoretic object.

| Target | Why | Official contact route to use |
|---|---|---|
| Scott Aaronson | Computational complexity, quantum complexity, highly experienced at evaluating extraordinary P vs NP claims. | Official homepage / blog: `https://www.scottaaronson.com/`, `https://scottaaronson.blog/` |
| Ryan Williams | Circuit lower bounds and algorithms-vs-circuits; relevant to the locked NAND and lower-bound framing. | MIT/CSAIL homepage: `https://people.csail.mit.edu/rrw/` |
| Russell Impagliazzo | Complexity theory, average-case complexity, proof complexity/cryptographic hardness context. | UCSD homepage: `https://cseweb.ucsd.edu/~russell/` |
| Avi Wigderson | Complexity theory, randomness, circuit/proof complexity; broad field authority. | IAS homepage: `https://www.math.ias.edu/~avi` |
| Sanjeev Arora | PCP/NP-hardness/computational complexity; coauthor of a standard complexity text. | Princeton homepage: `https://www.cs.princeton.edu/~arora/` |

## Priority 2: proof complexity / Boolean-function lower bounds

Ask these reviewers to attack locked NAND, proof DAG, proof complexity, and no-hidden-minimization discipline.

| Target | Why | Official contact route to use |
|---|---|---|
| Toniann Pitassi | Proof complexity and computational complexity; ideal for proof-obligation sufficiency. | Columbia CS profile / homepage, starting from department directory. |
| Alexander Razborov | Natural proofs, circuit lower bounds, proof complexity. | University of Chicago / personal academic profile. |
| Sam Buss | Bounded arithmetic and proof complexity. | UCSD homepage: `https://math.ucsd.edu/~sbuss/` |
| Paul Beame | Proof complexity, circuit complexity, algorithms. | University of Washington homepage: `https://homes.cs.washington.edu/~beame/` |
| Jan Krajíček | Proof complexity and bounded arithmetic. | Charles University / personal academic profile. |

## Priority 3: formal methods / proof engineering

Ask these reviewers to attack the executable proof-report stack, replay discipline, no-hidden-minimization scans, artifact seals, and formalization strategy.

| Target | Why | Official contact route to use |
|---|---|---|
| Jeremy Avigad | Formal mathematics, proof assistants, mathematical logic. | CMU homepage: `http://www.andrew.cmu.edu/user/avigad/` |
| Kevin Buzzard | Formalization of mathematics in Lean; skeptical formal-methods review. | Imperial profile / homepage: `https://www.imperial.ac.uk/people/k.buzzard/` |
| Leonardo de Moura | Lean and Z3 architect; proof-system / checker architecture. | Lean FRO / professional profile. |
| Tobias Nipkow | Isabelle/HOL and theorem proving. | TU Munich / Isabelle profile. |
| Thomas Hales | Formal proof verification and large mathematical proof projects. | University of Pittsburgh / Flyspeck-related profile. |

## Priority 4: combinatorics / hypergraph / finite rigidity

Ask these reviewers to attack V53/V54, BN2-BN6, selector packets, and finite request envelopes.

| Target | Why | Official contact route to use |
|---|---|---|
| Noga Alon | Extremal combinatorics and theoretical computer science. | Princeton / personal academic homepage. |
| Gil Kalai | Combinatorics, discrete geometry, skeptical public mathematical review style. | Hebrew University / personal homepage or blog. |
| László Lovász | Graph theory, combinatorics, complexity interface. | Official academic profile. |
| Timothy Gowers | Broad mathematical reviewer and public proof-discussion experience. | Cambridge / personal homepage or blog. |

## Outreach policy

1. Contact no more than three people in the first wave.
2. Start with one complexity theorist, one proof-complexity person, and one proof-engineering person.
3. Ask for a hostile read of only one slice, not the whole proof.
4. Offer a short call only after they accept the premise of reviewing.
5. Track all replies in `review/reviewer_response_log_7072f8d.md`.
6. If any reviewer reports a substantive defect, freeze outreach and triage the defect before contacting more people.

## First wave recommendation

```text
1. Ryan Williams — locked NAND / circuit lower-bound framing.
2. Toniann Pitassi or Sam Buss — proof-complexity and proof-obligation sufficiency.
3. Jeremy Avigad or Kevin Buzzard — proof-engineering and formalization-readiness.
```

If one of them declines, ask for a referral to a suitable person for that exact attack surface.

## Issue tracking format

```text
reviewer:
area:
claim attacked:
file / theorem / checker:
minimal counterexample or missing obligation:
expected acceptance behavior:
actual acceptance behavior:
suggested patch:
status:
```
