# Lean locked-NAND direct candidates and local baselines

Four assumption-free Lean modules now connect the report's local locked-NAND gadgets to the
direct-wire reference-minimum model. This is a local baseline result, not the global locked-NAND
reduction or threshold theorem.

## Typed direct-wire candidates

`lean/PNP/LockedNANDDirect.lean` realizes the six displayed gadgets as intrinsically topological
`DirectWire.Candidate` values. Their output widths are honest: every internal gate is exposed for
the five square gadgets, while the final conjunction has one output.

| Candidate | Inputs | Gates | Outputs |
| --- | ---: | ---: | ---: |
| `equalityDirect` | 3 | 10 | 10 |
| `constantOneDirect` | 2 | 2 | 2 |
| `constantZeroDirect` | 2 | 3 | 3 |
| `traceDirect` | 4 | 18 | 18 |
| `prefixAndDirect` | 2 | 2 | 2 |
| `finalConjunctionDirect` | 3 | 4 | 1 |

Lean proves the direct candidates agree with the existing Boolean macro semantics. It also checks
the internal source syntax of every candidate and proves that no internal program uses a carrier
constant. That property concerns the gadget programs; boundary inputs may still represent values
supplied by a surrounding construction.

## Semantic output lower bound

`lean/PNP/DirectWireBaseline.lean` defines `BaselineOutputConditions`: every output is
nonconstant, is not a positive input projection, and is semantically distinct from every other
output. Under those conditions, each output must be wired to a different internal gate, so Lean
proves

```lean
theorem outputCount_le_gateCount : outputs ≤ gates
```

For a square candidate with `gates = outputs`, this gives exact empty-context
`referenceMinimum`. The theorem remains conditional on an actual candidate and actual semantic
conditions; it is not a metadata-based distinctness assertion.

`lean/PNP/LockedNANDLocalBaseline.lean` discharges those conditions by finite truth-signature
checks for the five square candidates. Consequently, their exact reference minima are respectively
10, 2, 3, 18, and 2 gates. The four-gate final conjunction is intentionally excluded: its single
output yields only the general lower bound `1 ≤ gates`, not a four-gate minimum.

## Source-derived accounting

`lean/PNP/LockedNANDBaseline.lean` classifies every source occurrence directly from a typed NAND
program. Inputs and earlier gates contribute equality occurrences; `false` and `true` carrier
sources contribute zero and one occurrences. For an `m`-gate program, Lean proves that the actual
source count is `2m`, the trace-plus-source distinguished-check count is `3m`, and the prefix-node
count is `3m - 1` using natural subtraction at the zero boundary.

The formalized report baseline is therefore

```text
B = 18m + 10w_= + 3w_0 + 2w_1 + 2(3m - 1),
```

where the three occurrence counts are derived from the program, not accepted as external
metadata. The displayed construction has `B + 4` gates.

The module also proves a conditional global accounting lemma: if a real square candidate with
exactly `B` gates and `B` outputs is constructed and satisfies `BaselineOutputConditions`, its
reference minimum is `B`. Constructing that candidate and proving cross-instance output
distinctness remain open.

## Multi-output convention

The report threshold word is an ordered multi-output word: its `B` baseline coordinates plus one
final coordinate remain exposed. The four-gate final conjunction adds four gates but only that one
final coordinate. A legacy single-output synthetic seed is not the report construction and cannot
be used to replace this convention.

## Quarantined legacy `m = 2` fixture

The historical synthetic fixture mixes incompatible occurrence sources. Its two actual gates have
the four sources `[x0, x1, g0, x2]`, all equality-class occurrences, while its metadata claims four
equality, one zero, and one one occurrence. These lead to three different totals:

| Interpretation | Source counts `(w_=, w_0, w_1)` | Prefix gates | Baseline `B` | Displayed `B + 4` |
| --- | --- | ---: | ---: | ---: |
| Honest program-derived | `(4, 0, 0)` | 10 | 86 | 90 |
| Consistent with the six metadata occurrences | `(4, 1, 1)` | 14 | 95 | 99 |
| Stored hybrid: metadata macro costs, program-derived prefix | `(4, 1, 1)` | 10 | 91 | 95 |

The fixture is therefore quarantined as internally inconsistent. None of its stored values is
theorem authority for the typed source-derived Lean accounting.

## Exact proof boundary

The four module-specific axiom transcripts cover every explicit declaration and report no axioms.
They establish typed local candidates, constant-free internal syntax, the general semantic output
lower bound, source-derived arithmetic, conditional square-baseline exactness, and five exact local
macro minima.

They do not establish a global locked-NAND builder, cross-instance `BaselineDistinct`, carrier
freshness, the locked-NAND threshold equivalence, residual slack at most four, polynomial
construction/runtime, SAT correctness, or `P = NP`. All seven recorded reconstruction blockers and
all five disclosed project-specific axioms remain.
