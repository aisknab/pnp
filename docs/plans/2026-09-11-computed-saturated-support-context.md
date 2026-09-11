# M237 plan: computed saturated-support replacement contexts

This is a pre-implementation specification, not an earned release claim.
Preparation began at M236 feature `ffa1971703cc507ea9e3d1e0d927871d091ae579`.
The working branch is now based on actual M236 merge
`a41c3e3f628825ed3e9cbbe243124f42bf7cebab`, with unchanged tree
`57200eab75d2a667f6f4479ada9d730afa9b4ca9`. M236's exact-merge reproduction
and all four post-merge checks have passed. Preserve its theorem types, charge
ledger and publication pins.

## Manuscript anchor and missing dependency

The manuscript pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json)
states Compatible replacement and the Global slack law in section 2. Section 3
requires computed support saturation and completion; section 4 requires exact
physical charge accounting. These are prerequisites for the later support-gain
and residual-descent arguments, not interchangeable bookkeeping conventions.

[NANDComposition](../../lean/PNP/NANDComposition.lean) already proves
`compatibleReplacement_framed`, and [NANDSlack](../../lean/PNP/NANDSlack.lean)
proves `framedGlobalSlackLaw`. Both require a concrete serial frame as input.
They do not derive that frame from an arbitrary computed terminal support.
M236 now derives the complete physical charge ledger of that support, but it
does not reconstruct its surrounding circuit or transport a replacement back
into the original candidate.

Close that construction edge: compute a real frame around every production
saturated physical support, prove that plugging the unchanged extracted support
reconstructs the original Boolean function and gate count, and then transport
arbitrary equivalent replacements and the physical global slack inequality.
Do not replace this by another fixed gate pattern or a supplied frame.

## Unbounded computed construction

Quantify over arbitrary natural-number input, gate, output and profile widths,
arbitrary direct-wire candidates, executable candidate models and seed lists.
The model still supplies profile observations; it does not supply a context,
charge partition, reconstruction proof or compatibility certificate.

Use the following shared notation for actual computed terms, not new premises:

```lean
records := terminalSaturateRecords
  (terminalCandidateSaturationSystem candidate model) seed
support := extractTerminalSupport candidate records
complementRecords := terminalPhysicalComplementRecords records
complement := extractTerminalSupport candidate complementRecords
charges := terminalSaturatePhysicalCharges
  (terminalCandidateSaturationSystem candidate model) seed
context := terminalCandidateSaturatePhysicalContext candidate model seed
```

`terminalPhysicalComplementRecords` enumerates exactly those original physical
gates not selected by `records`; it does not invent profile charges. Reuse the
existing support extractor for both halves. Do not write a second circuit
compiler or change the executor, extractor, minima or old classifier.

The computed context must have the exact type

```lean
FramedContext inputs support.boundary.length support.interface.length
  inputs outputs 0 complement.gateCount
```

Its zero-gate environment forwards the support's primary-input boundary and
all original inputs as bypass wires. Its continuation uses the extracted
complement program, rebinding complement boundary ports to the support's actual
interface outputs or bypass inputs and reconstructing the original output word.

The zero-gate environment is justified by production saturation, not assumed:
actual gate-source closure forces every selected gate's physical predecessors
into the selected set, so no selected support boundary is an external gate.
Complement boundary gates are therefore actual selected-support interface
ports. Every original gate output consumed outside a half must be exposed by
that half's existing interface computation.

Retain actual interface order and multiplicity of the original output tuple.
Any total lookup fallback must be proved unreachable in the relevant physical
boundary/output case. An arbitrary constant fallback is not a substitute for
that proof.

## Exact universal theorem obligations

Each theorem below has the common parameters

```lean
{inputs gates outputs profileWidth : Nat}
(candidate : Candidate inputs gates outputs)
(model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate)
(seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
```

The abbreviations above expand to computed definitions. No public theorem may
accept a caller-supplied frame, fan-in-closure proof, exact charge equation or
whole-circuit equivalence certificate.

1. `terminalCandidateSaturate_boundary_isInput`:

   ```lean
   ∀ wire, wire ∈ support.boundary →
     ∃ input : Fin inputs, wire = TerminalSupportWire.input input
   ```

   Derive this from the actual candidate-source dependency rule and computed
   saturation closure, not from an additional closure premise.

2. `terminalCandidateSaturatePhysicalContext_size`:

   for every `replacementGates : Nat` and
   `replacement : Candidate support.boundary.length replacementGates
      support.interface.length`,

   ```lean
   (context.plug replacement).program.size + charges.length =
     gates + replacementGates
   ```

   This exact physical partition equation must hold regardless of replacement
   semantics or whether its size is smaller. Preserve all inherited seed gates.

3. `terminalCandidateSaturatePhysicalContext_equivalent`:

   ```lean
   Equivalent (context.plug support.extractedCandidate).program
     (context.plug support.extractedCandidate).directWireWord
     candidate.program candidate.directWireWord
   ```

   Prove reconstruction using the existing two extraction semantics theorems
   and actual physical boundary bindings.

4. `terminalCandidateSaturatePhysicalContext_replace_equivalent`:

   for every replacement of the exact extracted boundary/interface type,

   ```lean
   Equivalent replacement.program replacement.directWireWord
     support.extractedCandidate.program
     support.extractedCandidate.directWireWord →
   Equivalent (context.plug replacement).program
     (context.plug replacement).directWireWord
     candidate.program candidate.directWireWord
   ```

   The middle-word equivalence is the manuscript replacement lemma's stated
   premise. Whole-circuit preservation must be derived, never supplied.

5. `terminalCandidateSaturatePhysicalSupport_slack_le`:

   ```lean
   residualSlack support.extractedCandidate.toImplementation ≤
     residualSlack candidate.toImplementation
   ```

   Transport `framedGlobalSlackLaw` through the computed reconstruction and
   exact size equation. The reference minimum remains the existing finite
   Boolean reference construction, not a new polynomial-time minimizer.

## Implementation and proof order

1. Establish constructive lookup specifications needed for the existing
   extracted interface, then derive production gate-source closure and the
   input-only support boundary theorem.
2. Compute the physical complement and prove exact selected/complement
   membership, disjointness and gate-count partition. Connect support size to
   M236's complete computed charge ledger.
3. Construct the zero-gate environment and the continuation by rebinding the
   unchanged complement extractor. Prove each boundary and output binding is
   available and has the intended value.
4. Prove reconstruction for every input/output valuation, then derive exact
   size accounting and compatible replacement through the existing frame law.
5. Derive the physical global slack bound using minimum invariance and the
   existing constructive frame arithmetic.

Keep low-level lookup and partition facts in the new module where practical.
If an existing private extractor helper prevents a needed specification, expose
only a small proved interface; do not change its computation or theorem claim.
Use a new module `PNP.ResidualTerminalSaturatedSupportContext`.

A failed general construction stops this milestone. Record the smallest formal
failure and its manuscript dependency; do not substitute a finite example,
require the caller to provide the frame, add an assumption, weaken replacement
equivalence, or treat difficulty as permission to change the manuscript route.

## Regression and consumer preflight

Permanent regressions must apply all five interfaces at arbitrary dimensions
and exercise empty/full supports, repeated seeds, zero dimensions, constants,
original input bypasses, noncontiguous fan-in-closed selected gates, selected
gates consumed by several outside gates, repeated global outputs, and both
smaller and larger equivalent replacements. Include a raw nonclosed support
whose external-gate boundary prevents the zero-environment claim; the public
constructor must use computed saturation rather than silently accepting it.

| Producer | Consumers to reconcile together | First check |
| --- | --- | --- |
| Computed frame and five exact contracts | Permanent general/hostile Lean regression, explicit root, strict axiom audit and source contracts | Exact module build and cheap focused source/rejection cases |
| Reviewed theorem names | Lean inventory producer, JavaScript required names, publication row and fingerprint keys | Name-set equality before inventory extraction |
| New npm audit entry | Closed package-script fixture and durable test list | Focused script contract |
| Status fields and coordinate | Both exact status contracts, all boolean mutation lists and generator coordinates | Cheap current-status acceptance plus changed-contract rejection cases |
| Actual compiled fingerprints and status | Canonical/public mirrors, fixed progress history, current core docs and report | Structured field delta, compiled hostile cases, generated-byte checks |
| New workflow shell block | Exact extracted shell block and built prerequisites | Remote shell syntax check and execution |

Keep expensive global status-mutation loops inside the complete suite rather
than running them separately as a supposedly cheap preflight. Use one union of
required test files. Any proposed selection filter must first prove its behavior
with a tiny native-runner fixture; do not rely on a regular-expression check
alone. Persist raw process exit status and test summary before additional
aggregation assertions. A failed aggregate run is not release evidence.

Run all processing on the configured remote builder in an isolated checkout.
Preserve successful exact-source evidence, but require terminal zero results for
all required phases. After the source stabilizes, regenerate inventory, status,
progress, documentation and report, then finish normal PR and exact-merge gates.
Do not run a second PNP Lean build for a deferred website update.

## Explicit remaining limits and progress

This is a physical Boolean support-replacement and slack theorem for actual
production saturated supports. It does not claim arbitrary raw supports are
serializable, reconstruct the complete manuscript profile/materializer charge
universe, derive a fixed global ownership map, preserve every full-profile
obligation, or close manuscript-level full/quotient minimum-growth conditions.

The executable profile observer remains supplied and the reference influence
and minimization constructions remain exhaustive. No input-derived complete
terminal family, global route coverage, unconditional SaturatePositive,
BCELReady or ZeroSlack, complete polynomial PCCMin, deterministic CNFSAT in P,
or eligible root theorem is earned by these physical laws alone.

M236 is fully verified: merged, independently reproduced, and all four
post-merge workflows passed. Its source ledger reports formal artefact coverage
of 212 of 214 current scoped publication rows earned; risk-weighted proof
completion estimate 40%; uncertainty 20% to 40%; global gates closed 0 of 5.
M237's five universal theorems now build through the explicit root with only
`propext` and `Quot.sound` in their axiom closures. The generated M237 ledger
records 213 of 215 current scoped rows earned, with the same 40% risk-weighted
estimate, 20% to 40% uncertainty, and 0 of 5 global gates closed. No fixed
checkpoint has changed. M237's own release checks remain required.

Publication decision: defer. Keep the coherent M231 PNPLabs source pin unless
a genuinely larger verified capability changes the public bottom line. The
physical subcomponent alone does not complete the full-profile/global theorem.
Continue meaningful verified submilestone and release notifications independently.
