# M259: computed full-field zero/unary descent closure

## Named manuscript dependency

Reconstruct the computational zero/unary slice of the full-span policy's
"Whole-span cheaper word gives descent" lemma and the NormalizeOrGain/PCCMin
gain-restart edge in the manuscript pinned by
[the immutable archive manifest](../../archive/legacy-v0/ARCHIVE.json).
Section 6.1 governs proper-support R7 gains; the full-span policy explicitly
requires cheaper whole-span words to be strict residual descents instead of
local VerifyDW gains.

This milestone is one complete composition and stopping theorem, not a sequence
of selected circuit fixtures or a claim that all manuscript routes are covered.
The physical normalizer and proper-support discovery are already constructed.
The missing edges are the source-derived whole-span branch, completeness over
all zero/unary supports without a properness restriction, and common stopping
after repeatedly rechecking these computations.

## Baseline and release boundary

Development base: M258 commit ca20efac5c68570f2b5da9648f3c42848ca923bb,
tree bc1de6eed8c7eee56874505d8278986e8cbaa125. Its explicit root,
36 exact type/axiom interfaces, 18 guarded runtime fixtures, inventory,
publication/status/progress, report and complete 1,696-test suite passed.

Cycle preflight found core main at M252 merge
9c88e7b627880426137c0ceeaa61f3ede28df5cf. Its independent exact-merge check
and three normal post-merge checks passed; the last Lean workflow is active.
M253 through M258 are verified, unpublished commits selected for one cohesive
release PR. Every replayed milestone tree must equal its verified original;
the batch still needs its own normal PR, post-merge and exact-object gates.
M259 does not expand that pending release.

PNPLabs main remains 3d62ceb5ab14d51b39bd1a89307dbfb8d5a55226,
the coherent M231 publication. Development formal artefact coverage is 234/236.
Risk-weighted proof completion is 40%, uncertainty 20% to 40%, with 0/5 global
gates, no project-specific axioms, an absent eligible root and a false
publication gate. No M259 credit is earned before the whole planned result.

## General construction and exact branch distinction

Use a new module lean/PNP/NANDWireZeroUnaryClosure.lean and namespace
PNP.DirectWire.WireZeroUnaryClosure. Keep every input, gate, ordinary-output
and computational-field dimension arbitrary. Preserve all inherited proof
source bytes.

Derive the whole physical support from the original gate indices. Compute its
actual incoming boundary and completed frontier, not all declared inputs.
Use the already proved zero/unary constructor and successful arbitrary-support
compiler. Return a whole-span descent only when the resulting complete
replacement has strictly fewer gates. No replacement, open-function agreement,
rank, compiler result, candidate family or success certificate is a search input.

Keep proper-support and whole-span results as distinct typed branches.
The proper branch must retain a nonempty original exterior. The whole-span
branch must have exactly zero exterior and must never be labelled a proper
local VerifyDW gain. Both return the actual full-field-preserving carrier.

Combine M258 proper-support search with the whole-span branch. For any arbitrary
finite physical support, at most one actual incoming wire, and any strictly
smaller equivalent complete local open word, prove that this combined search
succeeds. A support with positive exterior uses M258. Zero exterior implies
that every original gate is selected; physical extraction congruence transfers
the complete open function and local saving to the derived whole support.

## Computed closure and required theorem

Run the existing physical normalization closure with all computational fields
exposed, then run the combined search. On a successful result restart on its
actual expanded carrier. Stop only after physical normalization is quiet and
both zero/unary gain branches are absent on that same final carrier.

The execution and its trace are computed from the initial carrier alone.
Every normalization trace and local descent must be the actual constructor
result, not a supplied optimizer or proof-only transition.

Required general interface:

    run_checked (carrier : WireCarrier inputs outputs fields) :
      let execution := run carrier
      Equivalent execution.result.implementation.candidate.program
          execution.result.implementation.candidate.directWireWord
          carrier.implementation.candidate.program
          carrier.implementation.candidate.directWireWord
      ∧ (forall valuation field,
          execution.result.fieldValue valuation field =
            carrier.fieldValue valuation field)
      ∧ PhysicalNormalizationQuiescent execution.result.exposed
      ∧ nextGain execution.result = none
      ∧ execution.result.implementation.gateCount + execution.trace.savedGates =
          carrier.implementation.gateCount
      ∧ execution.trace.gainIterations <= execution.trace.savedGates

Termination must use a strict decrease of the actual physical gate count,
including the preceding nonincreasing normalization. Prove exact telescoping
charge, preservation of every full field, and the iteration bound from actual
savings. Derive the residual-slack bound through semantic invariance, not by
executing an exhaustive reference minimum.

Prove the final absence of every strictly smaller equivalent complete local
word on every zero/unary support, proper or whole-span. Prove operational
idempotence of this complete closure. A failure to derive the general common
stopping theorem stops the milestone; do not publish a supplied-stop theorem,
a finite run or only the new whole-span branch as its completed result.

## Independent regressions and negative boundary

Use guarded tiny runtime instances only as test evidence. Include proper gains,
whole-span-only gains, mixed normalization and descent, no gain, empty
dimensions, hidden selected and exterior fields, repeated fields and unused
declared inputs. Check exact trace savings, branch labels, whole-span zero
exterior, common final stopping and re-execution.

Retain a checked nonminimum common fixed point. A candidate to verify is the
two-input absorption circuit NAND(NAND(x,x), NAND(x,y)), whose output is x:
its two-boundary interaction must not be labelled globally minimal merely
because the zero/unary routes and physical passes are quiet. If that specific
fixture takes an actual supported route, select a genuinely checked negative
example; never weaken the general stopping contract to retain a fixture.

The new result is not all boundary widths, the full manuscript carrier,
noncomputational record histories, arbitrary obligation DAGs, all R5-R8 rules,
all-trace N1-N10 Pull/Expand, complete Package E, global routing,
unconditional SaturatePositive, BCELReady or ZeroSlack, exact general PCCMin
or uniformly polynomial encoded-size construction, runtime, output and
certificate bounds. A gate/iteration bound is not a total runtime theorem.

## Source, expectations and verification order

Prepare exact source signatures, full-field/cost contracts and hostile mutations
with each implementation layer. Compile small leaf/projection and axiom checks
before broad execution. Bound every runtime fixture before adding it to the
durable suite; retain exact guards and expected branch results.

Reconcile the root imports, reviewed-name producers/consumers, package-script
fixture and exact workflow block before inventory sealing. Derive fingerprints
and counts from successful explicit-root compilation. Then update the current
status, progress history, documentation and report, run focused publication
mutations and one combined deduplicated core suite. Do not rebuild unchanged
proof modules or run Lean for the website.

## Progress, publication and cleanup

No fixed weighted checkpoint or global gate is expected to close. Keep the
40% estimate and 20% to 40% uncertainty unless a fixed checkpoint changes with
the required compiled evidence and rationale.

Publication decision: defer a separate PNPLabs cycle for M259. The already
selected M253-M258 capability release and major site batch remain independently
gated. Do not alter the coherent public source pin while core release checks
are pending. Continue meaningful verified submilestone notifications.

Retain only the named active verification and release artifacts, and remove
their exact task directories after final release or diagnosis.
