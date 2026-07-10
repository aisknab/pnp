# Formal reconstruction notice

**Effective: 10 July 2026**

## Current status

The target theorem is `P = NP`. It is **not currently established by this repository**.

Public theorem emission is disabled while the project is reconstructed around a concrete,
assumption-audited Lean theorem. The active machine-readable status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json).

Use `node pcc-formal-reconstruction-status0.mjs --json` to verify the active status boundary. The
current `npm run pnp:verify` command checks that boundary, the closed active package surface, the
pinned legacy-v0 archive identity, and the small current-authority suite. It cannot be configured to
execute the historical replay; replay acceptance does not change formal-reconstruction status.

Use `node pcc-formal-public-surface0.mjs --json` to verify that superseded activation, release,
materialized, and theorem-checker routes are absent from the active package exports, scripts, and bins.

## Why the earlier activation was withdrawn

The legacy JavaScript stack checks the shape, linkage, digests, and declared fields of finite
records. Several central mathematical obligations are represented by assertion-bearing fields
or trust objects rather than derivations of the named propositions. Acceptance of those records
therefore does not establish the mathematical truth of the locked-NAND reduction, residual-band
minimizer, ZeroSlack theorem, or final complexity conclusion.

The current Lean development makes parts of the intended route explicit and proves several local
Boolean identities. It does not yet provide the required concrete complexity model, executable SAT
development, complete locked-NAND threshold theorem, residual-band exact minimizer, ZeroSlack
proof, or polynomial runtime and certificate-size bounds. It also does not expose a root theorem
`PNP.Main.p_eq_np` with an acceptable axiom audit.

The repository now pins `leanprover/lean4:v4.31.0` and builds the explicit `PNP` library root. That
root imports every tracked Lean source module. `PNP.Main.rootTheoremStatus` is assumption-free data
recording that the theorem is not released; it is not the target theorem. The current conditional
bridge still depends on five disclosed project-specific axioms: `PNP.SAT`,
`PNP.LockedNANDThreshold`, `PNP.ResidualBandExactMinimization`, `PNP.GeneratePCCPack`, and
`PNP.CheckPCCPackexp`.

The first concrete foundation is now checked in `PNP.DirectWire`: intrinsically topological direct-wire
NAND programs, total Boolean evaluation, gate-count size, ordered output wiring, and elementary
projection/constant/repeated-output/NAND/NOT/AND laws. Its dedicated axiom audit is clean. This does
not by itself discharge any of the seven machine-recorded activation blockers: the concrete
complexity model, concrete SAT, locked-NAND threshold, residual-band minimizer, ZeroSlack,
polynomial bounds, and the root theorem/axiom audit remain incomplete.

The next constructive layer enumerates every well-typed direct-wire implementation at fixed input,
gate, and output widths, including the unique empty output tuple and both orders of every NAND input
pair. Its completeness theorems and certificate are axiom-free. The enumerator is intentionally not
canonical or claimed duplicate-free.

Finite Boolean tuples now give an executable decision procedure exactly equivalent to pointwise
`DirectWire.Equivalent`. A deterministic exhaustive scan from zero gates through a supplied target
selects an equivalent witness, proves its selected size is no greater than the target, and proves a
lower bound against every equivalent direct-wire candidate at every gate count. The resulting
empty-context reference minimum is invariant under semantic equivalence, and its residual slack is
zero exactly for a semantically minimum implementation. This is a finite reference computation: no
polynomial or practical-runtime bound is claimed, and it is not the asserted residual-band
minimizer used by the historical route.

Serial composition also provides one concrete environment/support/continuation frame. Within that
frame, equivalent support implementations can be replaced, and the corresponding additive global
slack identity is proved. This does not cover arbitrary support subsets, support profiles, or the
locked-NAND family. Accordingly the broad replacement/slack status fields remain false, and the
same seven substantive activation blockers remain.

The locked-NAND local bridge now contains six intrinsically typed direct-wire candidates with
honest gate/output widths: equality `10/10`, constant one `2/2`, constant zero `3/3`, trace
`18/18`, prefix conjunction `2/2`, and final conjunction `4/1`. Their internal programs are proved
constant-free. A general semantic theorem sends nonconstant, nonprojection, pairwise-distinct
outputs injectively to gates. Finite truth-signature proofs discharge those conditions for the five
square local candidates and establish exact empty-context reference minima of 10, 2, 3, 18, and 2.
The one-output final conjunction is excluded from that exactness claim.

Locked-baseline arithmetic is also derived from the actual typed program: an `m`-gate program has
`2m` source occurrences, `3m` trace-plus-source checks, and baseline
`18m + 10w_= + 3w_0 + 2w_1 + 2(3m-1)`, followed by four displayed final gates. The report word is
multi-output: its baseline coordinates plus one final coordinate remain exposed. Global candidate
construction and cross-instance `BaselineDistinct` are still absent, so the locked builder,
threshold, residual-slack-at-most-four bound, and polynomiality fields remain false.

The legacy synthetic `m = 2` fixture is quarantined because its real four program sources conflict
with metadata claiming six occurrences. Honest program-derived baseline/displayed counts are
`86/90`; counts made consistent with that metadata are `95/99`; and the stored hybrid values are
`91/95`. The typed Lean accounting, not this inconsistent seed, is current authority. See
[`lean_locked_nand_baseline.md`](./lean_locked_nand_baseline.md) for the full local proof boundary.

A further axiom-free module now proves the conditional semantic threshold deduction from an
explicit six-field package: `baselineCandidate`, `fullCandidate`, `baselineConditions`,
`initialOutputsPreserved`, `unsatisfiableFinalZero`, and `satisfiableFinalConditions`. From those
proof-bearing premises it derives the baseline lower bound, conditional residual slack at most
four, unsatisfiable minimum exactly at the baseline, satisfiable minimum between baseline plus one
and baseline plus four, and the corresponding conditional iff.

This is not the report locked-NAND threshold theorem. The six fields are not instantiated for a
source circuit. In particular, the arbitrary proposition and natural-number parameters are not
identified with circuit SAT and `lockedBaselineCount`; no global carrier layout, cross-instance
`BaselineDistinct`, `TraceEquivalence`, derived whole-carrier final-output laws, answer-independent
uniform builder, or polynomial bound is supplied. The module is not connected to the abstract
`PNP.LockedNANDThreshold` language.

The historical hostile review named `DirectWireOutputLowerBound`, `MacroDistinct`,
`TraceEquivalence`, `ZeroOutputConvention`, and `FinalLockSeparation`. The general output lower
bound was discharged in the preceding layer, and the model-level free-zero append convention is
now formalized. Global `MacroDistinct`, `TraceEquivalence`, and `FinalLockSeparation` remain
missing, as do all six concrete premise instantiations above. See
[`lean_locked_nand_threshold_boundary.md`](./lean_locked_nand_threshold_boundary.md).

## The only acceptable future activation gate

Public theorem emission may be reconsidered only when all of the following are mechanically true:

1. an exactly pinned Lean environment builds the explicit root target;
2. `PNP.Main.p_eq_np` exists and proves the concrete target theorem;
3. the root theorem's dependency closure contains no `sorry` or `admit` placeholders;
4. no PNP-specific axiom or trust parameter assumes any substantive part of the result;
5. SAT, P, NP, reductions, machines, correctness, and cost are concrete;
6. the SAT decider is executable and its polynomial bound is proved in the selected machine model;
7. the locked-NAND, residual-band, and ZeroSlack obligations are proved rather than asserted; and
8. public status and paper claims are generated from the checked Lean theorem inventory.

External review can provide useful independent audit evidence, but it is not a mathematical premise
and is not part of this gate.

## Historical material

The previous assertion-checker stack, sealed report, and activated coordinates remain available
for auditability. They are historical evidence about what the implemented checkers accepted. They
are not current theorem-status authority.

This notice supersedes the following coordinates as proof or publication authority:

```text
PNP-ACTIVATED-STATUS-2026-07-05-01
PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

Their files and Git history remain inspectable as subordinate legacy assertion-checker evidence.
The byte-exact source, artifact, and document coordinates are recorded under
[`archive/legacy-v0/`](../archive/legacy-v0/README.md). They must not be used to infer current theorem
status.
