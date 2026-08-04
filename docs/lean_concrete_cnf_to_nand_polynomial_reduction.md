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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-101` records 24,054 declarations,
12,985 theorems, 6,903 assumption-free theorems, 14,317 excluded private
declarations, 216 source-closure modules, and 2,152 reviewed milestone
candidates. Its 13,748,432 canonical bytes have SHA-256
`58d8118f3aef8976a3f1bdb2063a6d08baa7f2fe01e7393881fc9776f738aac9`;
the Lean source-closure SHA-256 is
`5cb2ae9d032d09c08f34424ccdf0b67452d75b8a933b60114c5267cc69385a7f`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-101` contains 81 milestones: 77
earned and three deliberately unearned. It pins 2,152 theorem types. Its
701,078 bytes have SHA-256
`a86df7f8d45a5430bc1b7cc67dfac31e8663a9e81ed24abc0f25a2cd299b0b7c`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-101`, paired with
public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-04-RESIDUAL-TERMINAL-SATURATION-100`,
records this reduction boundary as earned. Its 1,725,364 bytes have SHA-256
`ada16fd663a00a8ff6a10ba29693df2b0a13fe3cf6b68ec7521da9259d5de235`.
All four project assumptions, all six blockers, unset activation
fingerprints, the absence of `PNP.Main.p_eq_np`, and the false concrete
publication gate remain unchanged.

Canonical-report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-101` has a
185,272-byte TeX source with SHA-256
`f1d9b3f85b0ee7414ab9e40a9e1095f153f208ab9e121f5fd8aa3efef46d7c4a`
and a deterministic 73-page, 428,831-byte A4 PDF with SHA-256
`654dc634d86e7ebf2633c4d7d67d4cbf36a10c57bede51b4f8cf246fd169fefb`.

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
