# M240 plan: exact independent materializer cost beside an arbitrary circuit

This is a pre-implementation specification, not an earned result.
Preparation uses verified M239 source commit
`aea6eb9f83edc02a8670d8247f43e86b2341f46a`, tree
`3478580e827608bbe78d675658e2b889787102d1`. M239 is not yet published.
Reanchor to its actual merge and require all predecessor release checks
before publishing M240.

## Manuscript anchor and dependency edge

The pinned [manuscript](../../archive/legacy-v0/ARCHIVE.json) section 4
defines the weight of a computational materializer as its actual NAND size.
Section 10, RW-SaturatePositive, requires transparent additions to increase
the support and every full realization by the same forced cost.

M235 and M236 established actual physical insertion and charge accounting,
but correctly did not infer forced minimum growth from physical size alone.
M239 established full-profile acceptance of an actual gain, not transparency
of every materializer addition. The next result should supply a genuine
minimum-cost theorem for an explicit independent computational materializer
construction, not another classifier of a supplied cost equation.

Prove exact additivity when an arbitrary circuit is accompanied by an
arbitrary finite bank of independent NAND outputs on fresh primary inputs.
These are real computational inputs and outputs, not free proof/profile data.
This is a reusable forced-cost subcase within the existing direct-wire model;
it does not replace the manuscript's profile system, materializer universe,
terminalization, or global routing.

## Construction and exact target

Define, without a correctness-certificate input:

```text
appendIndependentNandMaterializers
  (candidate : Candidate inputs gates outputs) (count : Nat) :
  Candidate (inputs + (count + count)) (gates + count) (outputs + count)
```

Retain the original outputs in order and append one NAND of each disjoint
fresh input pair. Use existing input renaming and program composition.
Define all coordinate maps and exact Boolean semantics, including count zero.

The required main theorem is:

```text
referenceMinimum
  (appendIndependentNandMaterializers candidate count).toImplementation
  = referenceMinimum candidate.toImplementation + count
```

It must hold for every finite candidate and every count, without assuming
that the original candidate is minimum or its outputs are distinct,
nonconstant, or nontrivial. Derive exact preservation of the original
physical residual slack as a consequence.

## Lower-bound proof, not only an output-count bound

Reuse the existing semantic output-gate injection theorem for the appended
bank. Prove its nonconstancy, non-projection and pairwise-distinct conditions
from the explicit independent Boolean construction.

For any competing implementation of the combined function, its bank outputs
must select distinct actual gates. Restrict the fresh inputs to false.
Those designated output gates then all compute true independently of the
original inputs. Construct a gate-erasure/rebinding transformation that
removes exactly those gates while preserving the original output function
under this restriction. Do not assume the competitor has the canonical
program shape or that its bank gates are a contiguous suffix.

The resulting implementation of the original function has at most the
competitor's gate count minus count. This supplies the additive lower bound.
The upper bound appends the explicit bank to the attained minimum witness
for the original function.

A theorem giving only count <= combined minimum, an additivity result only
for an already-minimal original candidate, or a fixed one/two-bank example
does not complete this milestone. If the general lower bound cannot be
proved, do not replace it with a smaller earned prefix.

## Producer and expectation map

- Construction, semantics, erasure and exact minimum/slack interfaces:
  changed dependency build, arbitrary-dimension Lean applications and bounded
  execution cases, followed by explicit-root axiom and type audits.
- Public theorem names: update both inventory producers, exact fingerprints,
  publication row, status fields, all boolean mutation lists and durable
  workflow assertions together.
- Compiled/generated values: derive inventory, source closure, counts,
  coordinates and report metadata only after the proof source stabilizes;
  update the complete consumer family before broad checks.
- Current documentation and progress: consume the canonical ledger, preserve
  historical rows and distinguish coverage from weighted completion.
- Verification: targeted checks first, existing report reproduction once,
  one deduplicated union of required tests, normal PR/post-merge checks and
  independent exact-object reproduction. Reuse unchanged core proof evidence
  at the PNPLabs boundary.

## Regression boundaries

Use minimal bounded cases and universal theorem applications:
zero bank size; zero original inputs/outputs/gates; original constant outputs,
repeated outputs and primary-input bypasses; genuine one- and two-bank
construction; a noncanonical equivalent implementation whose bank-output
gates are not a suffix; and erasure through consumers of a designated gate.

Protect freshness and distinctness. Repeating an existing output or using
nonfresh input pairs must not receive an unjustified extra lower-bound unit.
Execution is test evidence, never native proof authority. Do not run large
exhaustive reference-minimum evaluations merely to test the universal theorem.

## Remaining obligations and progress

This result will cover independent physical Boolean materializers only.
It will not derive every manuscript profile materializer or its global owner,
prove transparency of every actual saturation step, settle quotient costs
or obligation discharge, or route all rejected profile changes.

The existing profile observers, influence search and reference minima remain
unchanged. No unconditional SaturatePositive, BCELReady or ZeroSlack, full
polynomial PCCMin, deterministic CNFSAT in P or eligible root is claimed.
A finite reference minimum is not a polynomial-time algorithm.

M239's reviewed baseline is formal artefact coverage 215 of 217, risk-weighted
proof completion estimate 40%, uncertainty 20% to 40%, global gates closed
0 of 5, no project-specific axioms, absent eligible root and false publication
gate. No fixed weighted checkpoint or global gate is expected to change.

Publication decision: defer. A forced-cost theorem for this constructed
subcase alone does not change the published global bottom line. Keep the
coherent M231 PNPLabs source pin; send meaningful verified submilestone and
release notifications independently.
