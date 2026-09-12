# M253: computed original-accounted frontier replacement

## Legacy anchor and the missing edge

Use the manuscript pinned by archive/legacy-v0/ARCHIVE.json, especially section 2
compatible support extraction/replacement, section 4 unique physical ownership
and exact matched materializer charges, section 5's full/quotient firewall,
and section 6.1's strict proper-support and full-discharge requirements.

M252 proves a computational word-level lift with matched charges, but its
reference lift can exceed the original. Its no-net-gain fixture demonstrates
why a saving against that larger reference is insufficient. The next edge is
an actual original-circuit completion: derive a visible support and its full
physical frontier, retain each exterior gate exactly once, and compare the
replacement with that extracted support while accounting against the original.

This is not a renaming of the M252 premise. The completed frontier may require
additional observed wires. The local agreement needed here is equality of the
complete extracted open function, not merely equality of ordinary outputs and
kept fields. Never infer the stronger agreement from the weaker one.

## Inputs and derived objects

Use a finite WireCarrier inputs outputs fields and a Boolean keep mask.
No support set, frontier, gate-owner map, materializer weight, topological order,
successful compiler result or full-result correctness certificate is supplied.

Use namespace PNP.DirectWire.WireFrontierLift and new source
lean/PNP/NANDWireFrontierLift.lean. Reuse existing checked interfaces and preserve
inherited theorem statements and proof sources.

1. Form the M251 masked carrier, without treating its normalization as the mode
   projection. Expose its ordinary outputs and masked computational fields.
2. Compute records from that candidate's actual output-dependency cone.
   Establish that its program is the original program and that the cone is
   predecessor closed. Ordinary and kept gate-valued observations are retained.
3. Extract those records from the original carrier's fully exposed word.
   This derives the complete boundary and interface, including retained gate
   values needed by exterior consumers and forgotten computational fields.
4. Derive the complement with ArbitrarySupportSplice.exterior. Its list entries
   are original physical gates, with no duplicated or fictional ownership.
5. The computed cone has no external gate-valued boundary ports. Derive
   PrimaryBoundary and graph well-foundedness from the actual sources and mask.
   Run the existing literal compiler and eliminate its impossible failure branch
   constructively. Do not accept an order or compilation certificate as input.
6. Expand a replacement Candidate with the exact extracted input/output arity
   into the original exterior, recovering the complete WireCarrier.
7. Under equality with the complete extracted open function, derive all ordinary
   output and field equalities and actual expanded-source full-value discharges.

The exterior is a physical charged completion, not a claim that it is the
smallest hidden-field materializer. A returned complete circuit retains each
original exterior gate once. No semantic minimizer runs.

## Exact accounting and general theorem boundary

Write pulled carrier keep for the extracted support, exteriorCharge for the
number of original exterior gates, and expanded carrier keep replacement for
the actual compiled full carrier. replacementGates is the Candidate's gate
dimension.

Required general identities, for every finite dimension and every well-typed
replacement, are:

- original gate count = pulled gate count + exteriorCharge;
- expanded gate count = replacementGates + exteriorCharge;
- original-minus-pulled and expanded-minus-replacement agree as exact integers;
- expansion is strictly smaller than the original iff replacementGates is
  strictly smaller than pulled gate count;
- the compiler succeeds from the computed primary-only boundary, independently
  of semantic agreement.

The central semantic theorem has the following exact shape:

```lean
theorem expanded_field
    {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate
      (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field
```

The central cost theorem has the following exact shape:

```lean
theorem matched_original_charge
    {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : Candidate
      (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (carrier.implementation.gateCount : Int) -
        (pulled carrier keep).gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacementGates
```

Derive a checked proper-gain query using both
pulled.gateCount < original.gateCount and replacementGates < pulled.gateCount,
under the exact local sameOpen premise. Return a proof-bearing result with
strict properness, actual equivalent strict gain, every computational field
preserved and exact cost. Do not report a whole-support saving as a proper
Package E certificate.

All-input local agreement is an explicit mathematical premise. This component
does not search for an equivalent replacement or prove agreement by evaluating
a few runtime assignments.

## Regression and hostile evidence

- Reuse the structural shape of M252's tautology example, with a retained lost
  field represented on the completed frontier. The original reference must not
  be inflated by duplicating the same materializer.
- Include a proper support inside a larger circuit with nonzero exterior charge,
  shared ordinary/lost values and an actual net gain. Verify every original
  output and ordered field and the exact selected/exterior partition.
- Include a replacement matching ordinary outputs but not a forgotten retained
  frontier wire. Kernel-check that its full-frontier agreement is false.
- Cover all-kept/all-forgotten masks, repeated/reordered computational sources,
  constant/input-only fields, no ordinary outputs, empty dimensions and a whole
  support. The proper-gain query must reject a whole support and non-strict size.
- Keep finite runs as regressions, not theorem authority. The exported theorems
  quantify over arbitrary finite dimensions and all valuations.
- Reject supplied supports, observers, orders, weights, success or full-result
  certificates; wrong frontier values; doubled/omitted exterior charges; weak or
  finite-only types; extra axioms; stale fingerprints; and widened claims.

If a general construction or proof fails, stop at that exact boundary. Do not
replace the target with a fixed example, weaker theorem, caller-supplied
conclusion or undocumented extra premise.

## Remaining blockers and publication decision

This derives the computational physical frontier completion for one actual
mask-derived predecessor cone. It is not the Pull/Expand map for every
arbitrary support across all N1-N10 traces. The full manuscript carrier,
noncomputational profile records, R6/R7 and general obligation DAGs, complete
Package E, route coverage, unconditional SaturatePositive/BCELReady/ZeroSlack,
exact polynomial PCCMin, deterministic SAT and the eligible root remain open.
A physical gate-count identity is not a total encoded-size polynomial runtime,
output-size or certificate-size theorem.

The verified M252 development state is 228/230 formal artefact rows, a 40%
risk-weighted proof estimate, uncertainty 20-40%, 0/5 global gates, no project
axioms, absent eligible root and false publication gate. No fixed weighted
checkpoint is expected to close. Derive any new coverage from the canonical
ledger; do not preselect inventory totals or award proof-completion credit.

Publication decision: defer PNPLabs. This input-derived computational component
does not change the coherent M231 public bottom line. Notify on meaningful
verified substeps independently of website cadence.

## Verification and release

Update source, exact theorem types, root imports, regression, axiom audit,
reviewed-name producers, package fixtures and durable workflow together before
running their targeted checks. Run the cheap source/root contracts first.
Run only isolated package-field checks while status is unsealed; root-export
mutation tests require the newly generated status.

Build the explicit root, execute the exact extracted workflow block, freeze the
Lean sources, seal type fingerprints and inventory, then derive status/progress
and current core documentation. Use ordinary separated words in narrow report
scope text; avoid long unbreakable slash chains.

Reuse unchanged checks. Run affected publication contracts, one successful
report reproduction and one combined deduplicated core suite. Preserve normal
PR, post-merge and exact-object boundaries. Release after the actual fully earned
M252 merge by reanchoring one commit without changing its verified tree.
Use an independent source/toolchain-matched checkout and clean all task-created
temporary artifacts after full release.
