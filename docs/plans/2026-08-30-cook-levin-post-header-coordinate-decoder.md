# Cook-Levin arbitrary-slot post-header coordinate-decoder milestone

## Legacy anchor

The pinned manuscript's final complexity transport uses the standard Cook-Levin
construction. In the active concrete model that construction must eventually be
one uniform polynomial-time raw formula builder. M208 supplied an all-input
complete-schedule controller, and M209 supplied one fixed raw comparator that
routes every natural token coordinate at the exact header boundary. M209 names
the next missing dependency explicitly: decode its post-header remainder into
the clause rectangle and within-clause token coordinate without returning to a
fixed schedule prefix.

## Unbounded abstraction

The M210 theorem ranges over every `PolynomialTimeVerifier`, every raw input,
both tableau input modes, and every coordinate below the complete direct token
schedule. No clause number, constraint, literal, token position, input length,
tableau width, decoded token, or successful route certificate is fixed or
supplied as proof authority.

The generic rectangle decoder ranges over arbitrary finite rectangle dimensions
and every natural coordinate. It is structurally recursive in the outer extent,
returns exact finite outer and inner coordinates precisely inside the rectangle,
and proves the reconstruction equation
`outer * width + inner = coordinate`.

## Exact theorem boundary

Add `PNP.Concrete.CookLevin.BuilderArbitrarySlotPostHeaderDecoder` with:

1. a generic executable `rectangleCoordinate?` and exact
   inside/outside, reconstruction, and direct-block lookup theorems;
2. a typed post-header route with exactly three outcomes: one clause/within-clause
   token coordinate, the unique final `Finish` coordinate, or out of range;
3. exact route characterizations proving that a body result carries the unique
   rectangle coordinate and that `Finish` occurs exactly at the rectangle bound;
4. an exact equation reducing `postHeaderSlotDirect` to the selected
   `clauseTokenBlockSlotDirect`, `Finish`, or `none` result;
5. an exact full-coordinate equation extending M209's outer route through the
   header, body, and final-token cases;
6. a decoder for M209's literal raw-router result configuration, proving that
   every reject result exposes exactly `coordinate - firstBodySlot` and every
   accept result exposes no post-header remainder; and
7. the public endpoint
   `cook_levin_arbitrary_slot_post_header_decoder_checked_complete` for every
   coordinate in `Fin terminalSlot`.

## Downstream blockers

M210 is the complete semantic clause/within-clause coordinate decoder and exact
direct token selector. It does not make the generic rectangle recursion a raw
finite machine, run a clause/within-clause divider in the literal work machine,
emit the selected body token on raw tape, integrate body emission into the M208
cursor loop, append the final odd zero bit, provide builder
`FunctionProgram.RawRefinement`, or package the concrete
`PolynomialReduction`.

Concrete CNF-SAT NP-hardness and NP-completeness, deterministic `CNFSAT in P`,
the locked-NAND-to-residual-band route, the residual-band minimizer,
unconditional ZeroSlack, polynomial PCCMin, the eligible root theorem, and the
publication gate remain open.

## Conservative progress decision

This closes one non-repeatable all-coordinate decoder dependency but does not
close the fixed complete-builder checkpoint or any global proof gate. The
risk-weighted proof-completion estimate therefore remains 35 percent with the
20 to 40 percent uncertainty range. Formal artefact coverage is regenerated
from the authoritative publication ledger after the new row is reconciled.

## Regression and hostile evidence

- Compile the generic decoder's exact inside/outside and reconstruction laws,
  body/finish/out-of-range routes, direct token equation, and raw-router
  remainder extraction.
- Exercise empty rectangles, zero width, first and last body positions, the
  unique finish coordinate, and an out-of-range coordinate.
- Exercise both tableau input modes and coordinates on both sides of the
  problem-derived header boundary.
- Derive the axiom transcript from every public declaration in the module.
- Reject fixed clause or token coordinates, materialized schedule lookup,
  caller-supplied decoder correctness, `Finish` at any nonterminal coordinate,
  out-of-range acceptance, a missing reconstruction equation, or wording that
  calls the semantic decoder a complete raw formula builder.

## Release gates

Run the focused Lean regression and axiom audit first, followed by the focused
hostile audit. Reconcile the root import, reviewed theorem-name interface,
compiled inventory, publication map, formal status, canonical report,
proof-progress ledger, durable workflow, and current documentation. Run one
complete capped remote verification, publish a focused draft PR, require every
normal check, merge manually, and reproduce the exact merge from a fresh clean
remote checkout. Synchronize that exact core merge into PNPLabs, perform its full
publication-surface audit without rebuilding Lean, merge and reproduce the site
commit, deploy it through the narrow deployer, and independently verify
production provenance and bytes.
