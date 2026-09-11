# Independent NAND materializer exact minimum-cost additivity

M240 proves a genuine forced-cost result beside an arbitrary original circuit.
Appending an arbitrary bank of independent fresh-input NAND outputs raises
the exhaustive semantic minimum by exactly the bank size and preserves the
original physical residual slack. Physical gate growth alone is not used as
a substitute for a semantic lower bound.

## Exact construction and theorem boundary

The [materializer-cost module](../lean/PNP/ResidualIndependentMaterializerCost.lean)
defines `appendIndependentNandMaterializers`. For a candidate with arbitrary
finite input, gate and output widths and a natural bank size, it retains all
original ordered outputs and appends the NAND of each disjoint fresh input pair.
Both halves of the fresh input bank are genuine Boolean primary inputs.

```text
referenceMinimum (appendIndependentNandMaterializers candidate count).toImplementation
  = referenceMinimum candidate.toImplementation + count

residualSlack (appendIndependentNandMaterializers candidate count).toImplementation
  = residualSlack candidate.toImplementation
```

No original-minimality assumption is required. Original outputs may be constant,
repeated or direct primary-input wires. A competing implementation may use any
gate order, topology, sharing pattern or gate count.

The seven general interfaces are:

- `appendIndependentNandMaterializers_size`: exact physical gate count.
- `appendIndependentNandMaterializers_original`: complete original ordered
  output semantics under projection to the original inputs.
- `appendIndependentNandMaterializers_materializer`: exact NAND semantics
  for every fresh pair and appended output.
- `appendIndependentNandMaterializers_lower_bound`: every equivalent competitor
  pays at least the original semantic minimum plus the bank size.
- `appendIndependentNandMaterializers_equivalent`: appending the bank preserves
  complete Boolean equivalence between original implementations.
- `appendIndependentNandMaterializers_referenceMinimum`: exact minimum additivity,
  using both the derived lower bound and an attained-witness construction.
- `appendIndependentNandMaterializers_residualSlack`: unchanged physical
  residual slack, even when the original circuit has redundant gates.

## Why the lower bound is additive

Each fresh NAND output is nonconstant, not a positive input projection and
different from the other bank outputs. The existing direct-wire output-gate
injection therefore selects distinct actual gates in any equivalent competitor.

Set the fresh inputs to false. Every selected gate now computes true for
every valuation of the original inputs. A recursive erasure/rebinding
transformation removes exactly those gates, substitutes their constant values,
and translates both inputs of every retained gate and every retained output.
The designated gates need not form a suffix, and later gates may consume them.

Projecting the rewritten candidate to the original outputs gives an
implementation of the original Boolean function. Its retained gate count,
plus the number of erased gates, is the competitor's original gate count.
The original minimum is no larger than this retained implementation, yielding
the full additive lower bound rather than just a bank-output-count bound.

For the other direction, append the same explicit bank to the attained minimum
witness of the original function. The complete-equivalence theorem supplies
the matching upper bound. Subtracting the new minimum from the new physical
size gives exact residual-slack preservation.

## Manuscript linkage and limits

The [plan](plans/2026-09-12-independent-materializer-cost.md) records the
pre-implementation boundary and the pinned [manuscript](../archive/legacy-v0/ARCHIVE.json)
section 4 computational materializer weight and section 10 RW-SaturatePositive
forced-cost dependency. Earlier physical insertion and charge accounting do
not by themselves establish minimum growth; this result supplies one proved
independent computational subcase.

This is an independent physical Boolean materializer forced-cost subcase,
not transparency of every manuscript profile materializer or every actual
saturation step. The construction does not replace the existing profile system,
materializer universe, ownership convention or terminalization.

Freshness and distinctness cannot be discarded from this theorem. Repeating
an existing output or reusing its original input pair can share one NAND
rather than incur an additional unit. Complete profile-derived materializers,
fixed global ownership, full-profile and quotient minimum bounds, obligation
discharge, terminal-family derivation and global rank-decreasing routes remain
open.

Reference minima remain exhaustive finite constructions, not a polynomial-time
algorithm. No encoded-size or runtime theorem for complete PCCMin is inferred
from finiteness or from this gate-count equation.

## Regression and assumption evidence

The [permanent regressions](../lean-regression/PNPResidualIndependentMaterializerCost.lean)
apply every interface at arbitrary dimensions. They include zero bank size,
zero original dimensions, a deliberately non-minimal original circuit with
repeated constant and primary-input outputs, and one- and two-bank execution.

An equivalent competitor has its fresh NAND gate first and uses retained
consumers of that gate in the original output. A separate repeated/nonfresh
output example rejects an unjustified two-unit lower bound. The regressions
do not perform a large exhaustive reference-minimum evaluation.

Runtime execution is test evidence, not theorem authority. General statements,
the noncanonical equivalence and the negative lower-bound example remain
kernel checked.

The [explicit-root axiom audit](../lean-audit/PNPResidualIndependentMaterializerCostAxiomAudit.lean)
checks all seven interfaces. The physical-size theorem has no axioms; the
original-output theorem uses only `Quot.sound`; the other five use only
`propext` and `Quot.sound`. No project-specific axiom, classical choice,
`sorry`, or native-execution proof authority is introduced.

The [source and compiled contracts](../audits/lean-residual-independent-materializer-cost0.test.mjs)
reject a finite-only bank, an original-minimality premise, an output-count-only
substitute, reused fresh coordinates, incomplete rewiring, supplied minima,
axiom-backed declarations and exact compiled-type drift.

## Remaining proof burden and progress

No unconditional SaturatePositive, BCELReady or ZeroSlack, complete polynomial
PCCMin, deterministic CNFSAT in P or eligible root theorem follows.
The publication gate remains false. No fixed checkpoint or global gate closes.

Formal artefact coverage: 216 of 218 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Both measures come from the [canonical progress ledger](../status/PROOF_PROGRESS.json).
Neither is confidence that `P = NP` is true, a probability of success, or a
time-remaining estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin.
This proved forced-cost subcase alone does not change the published global
bottom line. Meaningful verified core submilestone and release notifications
continue independently.
