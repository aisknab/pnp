# Formal reconstruction notice

**Effective: 12 July 2026**

## Current status

The target theorem is `P = NP`. It is **not currently established by this repository**.

Public theorem emission is disabled while the project is reconstructed around a concrete,
assumption-audited Lean theorem. The active machine-readable status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json).
It and the current canonical report are derived from the deterministic compiled-environment
inventory mirrored at [`status/LEAN_THEOREM_INVENTORY.json`](../status/LEAN_THEOREM_INVENTORY.json)
and [`public/pnp-theorem-inventory.json`](../public/pnp-theorem-inventory.json).

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

The current Lean development makes parts of the intended route explicit and now defines an
axiom-free finite charged-pipeline interface for P, bounded-certificate NP, and polynomial
many-one reductions. It does not yet prove that every such pipeline compiles or refines to the raw
single-tape machine kernel. A new local layer preserves the raw interpreter's first matching rule
and lifts every supplied exact chain of `n` successful raw transitions from an already represented
boundary frame to exactly `3 * n` successful work transitions. From an ordinary raw `run` with
fuel `F`, it extracts an exact prefix of length `k ≤ F` reaching the same endpoint. If that endpoint
is designated halting, `workRun` with fuel `3 * F` and compiled-machine `run` with fuel `18 * F`
reach its representation and encoding. This is conditional padding, not a termination result: the
full budgets are not successful-transition counts or input-size bounds, and a stuck nonhalting stop
is not classified as a verdict. A separate finite framer starts its compiled machine at literal
canonical `BitString.pair` input, reaches a represented boundary frame, and halts accepting under an
exact quadratic raw-input-length budget. Its public theorem is restricted to paired input and
permits blanked source cells as exterior garbage. An additional axiom-free namespace layer now
injectively retags the framer, lifted simulator, and handoff into pairwise-disjoint state images,
proves first-match lookup isolation for one concatenated finite rule table, and transports each
existing exact stage-local trace. A bridge-first finite work machine now adds one exact
symbol-preserving framer-to-simulator launch and separate accept/reject launches into two disjoint
verdict-indexed handoff copies. For every supplied exact target run it composes the three stages,
preserves bounded accept/reject classification, leaves a supplied stuck nonhalting endpoint as
timeout at the exact prefix budget, and compiles from ordinary canonical paired raw input at exactly
six times the cumulative work cost. It does not prove target termination or turn the supplied
source-transition count and final output length into an external-input-size polynomial. The
development also includes the executable internal handoff machine: from an already represented logical
tape `raw`, it reaches an accepting representation of `raw.handoffTarget` in exactly
`2 * raw.outputBits.length + 4` work steps and `12 * raw.outputBits.length + 24` compiled steps.
The local handoff theorem begins at an encoded internal work configuration; the cumulative bridge
theorem begins at ordinary paired `startConfig`. Its two-track encoded endpoint is not an ordinary
raw-visible `machineOutput` layout; a separate terminal packer or de-tagger remains necessary.
The development also provides one direct raw-machine instance: a universally
correct polynomial-time verifier for canonically encoded finite CNF formulae and bounded assignment
certificates, proving `PNP.Concrete.CNFSAT ∈ NP`. It does not provide a deterministic polynomial-time
decider proving `CNFSAT ∈ P`, concrete NP-hardness or NP-completeness, the complete locked-NAND
threshold theorem, the residual-band exact minimizer, ZeroSlack, the remaining end-to-end
polynomial bounds, or a root theorem `PNP.Main.p_eq_np` with an acceptable axiom audit.

The repository now pins `leanprover/lean4:v4.31.0` and builds the explicit `PNP` library root. That
root imports every tracked Lean source module. `PNP.Main.rootTheoremStatus` is assumption-free data
recording that the theorem is not released; it is not the target theorem. The current conditional
bridge still depends on four disclosed project-specific axioms: `PNP.LockedNANDThreshold`,
`PNP.ResidualBandExactMinimization`, `PNP.GeneratePCCPack`, and `PNP.CheckPCCPackexp`. The legacy
`PNP.SAT` value is now an ordinary non-authoritative label, not an axiom and not an alias for
`PNP.Concrete.CNFSAT`.

The root now also imports an axiom-free concrete foundation: canonical bitstring framing and pair
decoding, natural-polynomial bound syntax, a finite rule-list single-tape machine, fuel-bounded
execution, and proof-bearing deterministic runtime witnesses. Above it, finite function and
decision pipeline syntax carries polynomial runtime, output-size, certificate-size, and handoff
bounds. Lean constructs P contained in NP, reduction identity/composition/transport, and the
NP-complete-in-P implication. Boundary geometry and the local simulator now discharge exact finite
configuration runs, including marker growth across arbitrary exterior garbage, exact-prefix
extraction, and the conditional designated-halting padding described above.
The separate paired-input framer supplies an executable canonical-input-to-frame trace with exact
work and compiled raw budgets. The state-namespace layer gives it, the simulator, and the internal
handoff pairwise-disjoint images in one lookup-isolated concatenated rule table and proves that the
three established exact traces survive renaming. The stage-bridge layer connects supplied exact
target runs into one verdict-preserving internal execution with explicit cumulative work and raw
costs. The internal handoff still does not provide terminal raw output de-tagging. This remains a
charged interpreter interface without a complete external-size compiler or refinement theorem to
one raw machine. See
[`lean_concrete_complexity.md`](./lean_concrete_complexity.md) and
[`lean_pipeline_stage_bridges.md`](./lean_pipeline_stage_bridges.md).

The concrete CNF layer separately defines canonical formula and assignment codecs, propositional
CNF semantics, a Boolean certificate checker, a finite work machine, and its compiled raw machine.
Lean proves for every raw formula/certificate pair that the compiled machine accepts exactly when
the checker returns true, rejects exactly when it returns false, and cannot time out at the explicit
polynomial fuel bound. The resulting `.paired` `PolynomialTimeVerifier` proves
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT`. This is a bounded-certificate NP
membership theorem, not a deterministic decision procedure and not a hardness result.

## Compiled inventory and current publication boundary

`lean-audit/PNPTheoremInventory.lean` traverses `Lean.Environment.constants` after the explicit
`PNP` root has compiled and calls `Lean.collectAxioms` for every included public `PNP.*`
declaration. It does not infer declarations or dependencies by parsing Lean source. The canonical,
lexically ordered JSON output records declaration kinds and compiled axiom closures, and its status
and public copies must be byte-identical. See
[`lean_theorem_inventory.md`](./lean_theorem_inventory.md) for the inventory contract and check
commands.

Every earned intermediate milestone row requires its configured detailed theorem candidates to
match by exact name and theorem kind, have empty axiom closures, preserve their per-name
domain-separated kernel-type SHA-256 values, and match the pinned closure over every
`lean/**/*.lean` file plus the Lean/Lake pins and inventory probe. Type or source drift revokes
milestone credit until reviewed pins change.

Declaration, theorem, module, excluded-private, and reviewed-candidate counts are emitted by the
compiled inventory and are intentionally not duplicated here. The current Lean source closure has
exactly four project-specific axioms; the generated inventory and publication outputs must be
regenerated and byte-checked after source-closure changes before they may describe the revision.

Inventory generation is deliberately separate from theorem publication. The concrete gate expects
the compatibility theorem `PNP.Main.p_eq_np` to have the exact concrete target
`PNP.Main.ConcretePEqualsNP`. The target now exists as an axiom-free **definition** aliasing mutual
inclusion for the finite charged-pipeline classes; it is not a proof. The compatibility/root theorem
`PNP.Main.p_eq_np` remains absent. The existing witness-handle proposition `PNP.PEqualsNP` is
abstract and explicitly publication-ineligible.

The expected kernel fingerprints for the concrete target type and value, compatibility-root type,
axiom closure, and source closure are intentionally `null` in this migration step. Unset
fingerprints fail closed; `null` never matches `null`. The standard-complexity-model eligibility
check is also false. Therefore the gate does not pass and every theorem-emission field derived
from it remains false or `null`.

The root `canonical_proof_report.tex` and `canonical_proof_report.pdf` now form the generated,
concise nine-page formal-reconstruction report. They replace the historical claim manuscript at the
root and make the non-activation boundary explicit. The historical 56-page claim artifact is
available only from the pinned legacy source coordinate recorded under
[`archive/legacy-v0/`](../archive/legacy-v0/README.md).

The direct CNF verifier closes one formerly abstract obligation—concrete NP membership for
`PNP.Concrete.CNFSAT`—and the bridge milestone closes exact internal stage launch for supplied
target runs. They do not discharge the remaining publication blockers. In particular, terminal
output de-tagging, ordinary `machineOutput` equality, complete composition refinement with an
external-input-size polynomial bound, a
deterministic polynomial-time CNF-SAT decider,
concrete NP-hardness/NP-completeness, locked-NAND threshold, residual-band minimizer, ZeroSlack,
the remaining end-to-end polynomial bounds, and the root theorem/axiom audit remain incomplete.

The first concrete foundation is now checked in `PNP.DirectWire`: intrinsically topological direct-wire
NAND programs, total Boolean evaluation, gate-count size, ordered output wiring, and elementary
projection/constant/repeated-output/NAND/NOT/AND laws. Its dedicated axiom audit is clean. This does
not by itself discharge any of those publication blockers.

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
same substantive activation blockers remain.

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

The residual-route layer now performs one honest executable operation: it scans an explicit finite
list of typed implementations for the first strictly smaller semantically equivalent candidate.
Every returned gain is proved equivalent, smaller, and strictly descending in reference residual
slack. Exact-minimum and ZeroSlack result constructors require Lean proofs of semantic minimality;
the executable scanner itself can return only `gain` or `unresolved`.

This scan is deliberately fail-closed. `unresolved` excludes gains only in the caller-supplied
list. Lean contains an empty-list regression whose current implementation has residual slack one,
so unresolved cannot establish global minimality or zero slack. Candidate-list completeness, the
BCEL/HN/BUD/selector contradiction, a complete PCCMin loop, and every polynomial runtime claim
remain absent. The residual-band, ZeroSlack, and polynomial blockers therefore remain unchanged.

## The only acceptable future activation gate

Public theorem emission may be reconsidered only when all of the following are mechanically true:

1. an exactly pinned Lean environment builds the explicit root target;
2. `PNP.Main.p_eq_np` exists and proves the concrete target theorem;
3. the root theorem's dependency closure contains no `sorry` or `admit` placeholders;
4. no PNP-specific axiom or trust parameter assumes any substantive part of the result;
5. SAT, P, NP, reductions, machines, correctness, and cost are concrete, with the charged-pipeline
   semantics proved adequate for the selected raw machine model;
6. a deterministic SAT decider is executable and its polynomial bound is proved in the selected
   machine model (the current `CNFSAT ∈ NP` verifier is insufficient);
7. the locked-NAND, residual-band, and ZeroSlack obligations are proved rather than asserted; and
8. public status and paper claims are generated from the checked Lean theorem inventory.

The separate concrete gate enforces this boundary. Merely adding a declaration with the right name,
relying on abstract `PNP.PEqualsNP`, or leaving an expected fingerprint unset cannot activate it.

Check the current non-activation outputs with:

```bash
lake build PNP
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
node pcc-formal-reconstruction-status0.mjs --json --no-write
npm run report:check
```

External review can provide useful independent audit evidence, but it is not a mathematical premise
and is not part of this gate.

## Historical material

The previous assertion-checker stack, 56-page claim report, and activated coordinates remain
available at the pinned legacy coordinates for auditability. They are historical evidence about
what the implemented checkers accepted. They are not current theorem-status or report authority.

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
