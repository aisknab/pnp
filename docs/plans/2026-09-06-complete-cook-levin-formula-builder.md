# M230 plan: complete all-input Cook-Levin formula builder

Status: planned and not earned. The current published mathematical coordinate
remains M229. This work may span several implementation and verification phases;
none of the component phases alone earns the complete-builder checkpoint.

## Starting evidence and selection

The verified starting point is core merge
`3676a3f291193221e4ee3537aaf6023fba95ace0`, tree
`c3dec3c8d169780bc507ed247bd9e3aebdedd430`.

M229 derives a physical zero/positive body-remainder split for every post-header
coordinate, with a fixed machine, compiled execution and a source-size polynomial
bound. Its body endpoints remain incomplete. M216 already proves semantic
iteration over the complete schedule and an aggregate staged-work bound, but
does not connect those stages as one actual machine run. Reproving those semantic
facts or adding a fixed coordinate does not discharge the remaining obligation.

The selected load-bearing target is the existing fixed checkpoint
`reductions-complete-cook-levin-builder`: complete all-input polynomial formula
construction and its packaged reduction. The immediate implementation boundary
is deriving clause occupancy and every token request from the actual input and
retained workspace, then preserving that workspace across the full loop.

The current tracker remains 35/100 with uncertainty 20% to 40%, formal artefact
coverage 205/207, and 0/5 global gates closed. Do not edit those values to mark a
plan or component implementation as earned.

## Exact legacy anchor

Use the manuscript pinned by
[`archive/legacy-v0/ARCHIVE.json`](../../archive/legacy-v0/ARCHIVE.json), document
tag `final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

The relevant dependency is the introduction's use of SAT NP-completeness and the
section headed **Final SAT decision**, including **Accepted package implies
P=NP**. Reconstructing that transport in the selected finite-machine complexity
model requires a concrete polynomial reduction from each bounded-certificate
verifier language to CNFSAT. The existing formula semantics establish the answer
equivalence, but not an executable polynomial construction.

Anchor precision: the manuscript's **TraceEquivalence** lemma concerns the NAND
circuit trace and lock slots. It is not itself a Cook-Levin formula-builder
theorem. This plan does not use that lemma as authority for the missing builder.
The historical accepted package and checker remain specification/provenance
evidence, not a premise replacing any Lean theorem.

Preserve the existing canonical formula, token encoding, variable layout and
answer-independent schedule. A different presentation of the same machine
construction must preserve the exact output interface below. Do not change the
mathematical route merely because its implementation is difficult.

## Unbounded abstraction and intended theorem types

For a fixed `PolynomialTimeVerifier language`, construct one finite program
independently of the source input and any accepting certificate. On every input
bitstring it must output exactly the canonical encoded verifier-tableau formula.

Planned interfaces in `PNP.Concrete.CookLevin`:

```lean
def formulaBuilder {language : Language}
    (verifier : PolynomialTimeVerifier language) : PolynomialTimeFunction

theorem formulaBuilder_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula

def polynomialReduction {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    PolynomialReduction language CNFSAT

theorem cook_levin_formula_builder_checked_complete {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    ∀ input, (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula
```

These are target interfaces, not declarations that already exist. The
`PolynomialTimeFunction` must contain a closed finite `FunctionProgram` and
proofs of total halting, charged polynomial runtime and polynomial output size.
The existing recursive `FunctionProgram.RawRefinement` compiler must apply to
that complete program. A semantic function, staged correct output, supplied
selector or caller-supplied construction theorem is not an implementation.

The reduction's correctness should reuse
`VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language` after proving
the output equality. This preserves the existing CNFSAT language and concrete
complexity model.

## Implementation phases

1. **Reuse audit and physical selection.** Locate and reuse existing general
   clause-count, direct-slot, token-decoding, arithmetic, machine-graph and
   schedule lemmas. Derive clause occupancy and all separator, sign, unary
   variable, terminator and padding requests from source-derived data. Cover
   every constraint family and every coordinate. Do not supply a constraint,
   selected clause, route, request, verdict or correctness certificate as an
   additional endpoint input. Any auxiliary object must itself be constructed
   from the fixed verifier and source input with the required size/work bounds.
2. **One physical successor.** Prove actual tape equality from the end of a
   selected iteration to the next iteration's entry. Preserve the input and
   builder prefix; reset scratch state; advance the coordinate; and append
   exactly the selected token or leave output unchanged for padding. Do not
   replace a physical handoff by rebuilding a semantic configuration externally.
3. **Literal complete loop.** Connect the complete header, repeated body step
   and Finish endpoint in one finite program. Prove a loop invariant for an
   arbitrary processed prefix and instantiate the verifier-derived full
   schedule length. Reuse M216's semantic prefix theorem where its premises
   are actually realized by the physical execution.
4. **Polynomial closure and reduction.** Bound the entire construction,
   workspace, encoded output and execution by polynomials in source input size.
   Include selection, scratch recovery and iteration overhead. Establish the
   exact raw output, package the polynomial-time function, and reuse the existing
   semantic answer equivalence to construct the reduction.
5. **Checkpoint review and publication.** Audit the exact endpoint type and all
   public dependency closures. Review the builder checkpoint and any separately
   proved concrete NP-completeness transport checkpoint by ID and evidence.
   Award only discharged checkpoints, with the required score-change rationale.
   Register and publish the milestone only after the complete target passes.

If a general phase fails, keep the milestone in progress and record the exact
remaining obligation. Do not replace it with another fixed-slot result, a
supplied-data theorem, an axiom, `sorry`, `admit`, or a weakened endpoint.

## Source and expectation preflight

Prepare each producer change and its consumers together, before its first
verification command. Reconcile the entire affected family after any discovered
stale expectation, not just the first failing assertion.

| Changed contract | Expectations prepared with the change | First evidence |
| --- | --- | --- |
| Physical selector and successor | Intended all-input theorem type, literal fixtures for every route family, workspace preservation and negative staging/claim cases | Changed module, focused Lean regression and public-declaration axiom probe |
| Complete loop and encoded output | Arbitrary-prefix invariant, zero/full boundary cases, timeout and exact-output regressions | Loop module and focused root-import regression |
| Complete polynomial construction | Encoded-input-size bounds covering selection, handoff, loop and output; mutations that omit a phase or use semantic-only execution | Complete builder and reduction tests |
| Theorem registration | Root imports, reviewed declaration names, required-name contract, fingerprint key set and milestone entry | Name-set comparison before compiled inventory extraction |
| Generated evidence and progress | Generator inputs, canonical ledger state and history, status/mirror fields and all current documentation consumers | Generate after successful compilation, then targeted check mode |
| Publication and workflows | Source pins, current-value fixtures, all latest-milestone trust-layer mutations and embedded workflow assertions | Focused positive and negative publication preflight before a broad audit |

Keep historical milestone snapshots fixed. Derive current values from canonical
data, but retain independent theorem/type, axiom, security and hostile-mutation
invariants. Do not invent future declaration counts, digests or score changes.

## Verification ownership and release

All processing runs on the configured remote builder. Reuse the exact starting
tree's verified build cache; rebuild modified dependency chains and the root
before audits import them. Run focused checks first. Delay generated inventory,
status and report work until the proof source and expectation inputs stabilize.

The core repository owns Lean compilation, regressions, axiom auditing, compiled
inventory and proof-report generation. Require its normal PR and post-merge
checks and exact-merge verification. PNPLabs then verifies the exact core pin,
byte-identical mirrors, conservative claims, generated pages, links, browser
behavior, hostile publication cases and release provenance. It must not repeat
the core Lean build or regenerate the proof report. Deploy only the verified
site merge and independently verify production.

Send concise progress notifications for meaningful completed phases and
actionable blockers. Keep proof estimate, artefact coverage and global gates
separate. A phase completion is not an earned full-builder checkpoint.

## Remaining project obligations

Even a complete Cook-Levin reduction does not provide a deterministic SAT
algorithm. The unconditional residual-band minimizer, global ZeroSlack,
PCCMin exactness and total polynomial/certificate bounds, deterministic CNFSAT
membership in P, required final model linkage and the exact eligible root theorem
remain separate obligations. Publication stays fail-closed until its own exact
root/type/fingerprint/axiom requirements pass.
