# Concrete CNF-to-NAND polynomial reduction

This milestone turns the existing pure CNF-to-NAND transformation into one
literal, finite, all-input machine and packages it as a polynomial many-one
reduction.

The source language is the repository's strict canonical encoding of CNF
formulas. The first target language is strict encoded NAND satisfiability.
Malformed source words reject and produce the empty output; successfully
decoded source words produce exactly the bytes returned by
`CNFToNAND.compileEncodedCNFToNAND`.

## Legacy anchor and dependency edge

The canonical manuscript pinned by `archive/legacy-v0/ARCHIVE.json` begins
its “Final SAT decision” construction by converting an arbitrary Boolean
formula or circuit to a NAND circuit, before constructing the locked-NAND
instance. The semantic compiler milestone proved that transformation
extensionally. This milestone closes the missing executable edge: arbitrary
encoded CNF input to exact encoded NAND output, with one finite machine,
an input-length polynomial, and reduction packaging.

The manuscript remains the intended construction route, while Lean remains
the theorem authority. A failed exact trace, output equality, or polynomial
bound would stop this milestone rather than being replaced by a finite
prefix, a weakened theorem, or a new assumption.

## Executable architecture

`CNFToNANDCompilerMachine` is a fixed three-node
`WorkMachineProgramGraph`:

1. `CNFSourceParser` validates an arbitrary source bitstring.
2. `CNFToNANDCarrierEncoder` materializes the decoded formula as an inert
   retained carrier.
3. `CNFToNANDController` traverses that carrier twice: first to count the
   exact target gates and then to emit the strict NAND circuit.

The graph contains no formula-indexed rule lookup. A formula appears only as
a proof index when establishing the path taken by the fixed table. Every
transition is selected from the current finite state and one of the nine
work symbols, and every bitstring reaches a halted outcome within the common
polynomial.

The count pass reconstructs the exact gate-count identity already proved for
the pure compiler. The emission pass follows the same postfix compilation
plan and emits the strict version-zero header, every topologically ordered
gate, and the final output reference. The reached output is therefore
byte-for-byte equal to the pure transformation, including the empty-formula,
empty-clause, negative-literal, and out-of-range-literal cases.

## Polynomial and compiled boundary

`CNFToNANDCompilerPolynomialBound` gives one closed
`NatPolynomial` in the original encoded source length. It covers:

- the total parser;
- canonical carrier construction;
- the complete count and emission controller;
- all three outer graph bridges.

The generic work-machine compiler charges six raw transitions for every work
transition. The resulting compiled machine is proved never to time out at
that polynomial on any bitstring. Its output-size field reuses the separately
proved `CNFToNAND.cnfToNANDOutputSizePolynomial`.

`CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction` is a
proof-bearing `PolynomialTimeFunction` whose exact output theorem is:

```lean
cnfToNANDPolynomialTimeFunction.output bits =
  CNFToNAND.compileEncodedCNFToNAND bits
```

Its program is a literal machine leaf, so
`CNFToNANDCompilerCompiled.cnfToNANDRawRefinement` retains the same table as
an exact `FunctionProgram.RawRefinement`. No caller supplies a decoded
formula, schedule, execution certificate, or trust flag.

## Reductions

`CNFToNAND.cnfToNANDPolynomialReduction` packages the machine function and
the existing all-bitstring semantic theorem as:

```lean
PolynomialReduction CNFSAT LockedNAND.EncodedNANDSAT
```

It is then composed with
`LockedNAND.strictLockedNANDPolynomialReduction` to obtain:

```lean
PolynomialReduction
  CNFSAT
  LockedNAND.EncodedLockedNANDThreshold
```

The composed function outputs exactly
`CNFToNAND.buildLockedNANDFromCNF bits`. Its raw refinement is constructed
from the two leaf refinements by the repository's generic literal sequential
compiler.

## Trust and claim boundary

The milestone audit checks every new public declaration and the reused
parser/emitter/reduction interfaces. Project axioms, `Classical.choice`,
`sorry`, `admit`, native or SAT decision shortcuts, host-side schedule
lookup, and caller-provided execution certificates are rejected.

This milestone establishes a concrete polynomial reduction. It does not
itself decide CNF-SAT in deterministic polynomial time, discharge the
remaining report-level locked-NAND threshold assumption, complete the
global ZeroSlack/PCCMin obligations, or establish `PNP.Main.p_eq_np`. The
concrete publication gate remains false.

## Mechanically generated publication evidence

The complete axiom transcript covers 1,316 declarations: 864 have empty
closure, 151 use only `propext`, and 301 use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom.

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-03-96` records 23,615 declarations,
12,830 theorems, 6,788 assumption-free theorems, 14,273 excluded private
declarations, 211 source-closure modules, and 2,103 reviewed milestone
candidates. Its 13,460,106 canonical bytes have SHA-256
`71165b553da0c375a19769cb9a7da02b20927d79cf47204d07e86ae14533c5fe`;
the Lean source-closure SHA-256 is
`23ebbd4f1251d92adb3c0a1d60cf63b52683a41f39a84375c87b0781d2f522ac`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-03-96` contains 76 milestones: 73
earned and three deliberately unearned. It pins 2,103 theorem types. Its
685,582 bytes have SHA-256
`69e15a77f4df72b6a0c3e1c2dce69cb9f156344d8b432524a0ab954106aaa27d`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-03-96`, paired with
public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-03-RESIDUAL-GAIN-STOPPING-SPECIFICATION-95`,
records this reduction boundary as earned. Its 1,684,244 bytes have SHA-256
`251b3b184c7195f8a951d474701610a3650a2d42d98193ebb515cbcb16c4597f`.
All four project assumptions, all six blockers, unset activation
fingerprints, the absence of `PNP.Main.p_eq_np`, and the false concrete
publication gate remain unchanged.

Canonical-report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-03-96` has a
179,212-byte TeX source with SHA-256
`824cc9ee94e1b4598fba805eaea52b246cc471a3a2644a5faf295a392dfb25d9`
and a deterministic 70-page, 422,655-byte A4 PDF with SHA-256
`c177248af36860a452cc4b5683fea11c9e3ba1de0e2d1830e9cb7b51a7bc36d7`.

## Verification surface

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCNFToNANDPolynomialReductionAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFToNANDPolynomialReduction.lean
node --test \
  audits/lean-concrete-cnf-to-nand-polynomial-reduction0.test.mjs
```

The complete root build, focused audit/regression, hostile mutations,
generated-publication checks, and clean-clone reproduction run on the
configured resource-limited `pnpbuilder` host.
