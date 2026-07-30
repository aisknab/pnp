# Concrete CNF-to-NAND semantic compiler

## Plain-language outcome

This milestone fills in a missing translation step. The repository already
had one exact language for Boolean formulas in conjunctive normal form (CNF)
and another exact language for circuits made only from NAND gates. Lean now
checks a single general translator between them.

The translator does not ask whether the formula has a solution and then
choose an answer. It reads the formula's structure and builds a circuit from
that structure. Lean proves that the original formula has a satisfying
assignment exactly when the generated NAND circuit does.

The proof covers every formula size, not a fixed collection of examples. It
also covers easily mishandled boundary cases:

- an empty formula is true;
- an empty clause is false;
- both positive and negative out-of-range literals are false;
- repeated literals and multiple clauses retain their ordinary meaning; and
- malformed external formula bytes produce an empty, rejecting output.

## Technical construction

`PNP.Concrete.CNFToNAND` compiles the decoded `CNFFormula` through a private
typed Boolean-expression layer. Inputs are indexed by `Fin`, and the
intermediate NAND `Program` is intrinsically topological. Program fragments
are combined with `Program.appendSubstituted`; negation, conjunction, and
disjunction use only NAND gates:

- `not a` is `nand a a`;
- `a and b` is a NAND followed by self-NAND; and
- `a or b` is a NAND of the separately negated inputs.

The final result is normalized so its output is always a gate, including
input-only and constant formulas. `compileFormula_wellFormed` proves that its
raw strict-v0 representation is well formed, and
`decodeValidCircuit_encode_compileFormula` proves that the strict decoder
accepts its canonical bytes.

For every typed valuation,
`compiledFormulaCircuit_eval_eq_true_iff` identifies the circuit output with
the independently defined CNF satisfaction relation. This is lifted first to
decoded satisfiability, then to the exact encoded languages:

```text
CNFSAT bits
  ↔ EncodedNANDSAT (compileEncodedCNFToNAND bits)
```

Strict decoder canonicality is proved in the reverse direction as
`encodeCNF_of_decodeEncodedCNF`. It prevents the successful branch from
quietly accepting a noncanonical alternate encoding. The malformed branch is
fixed to `[]`, and `empty_not_encodedNANDSAT` proves that this branch rejects.

The exact generated gate count is

```text
valid negative literals
+ 3 × all literal occurrences
+ 2 × clauses
+ 1 when the formula has no clauses.
```

The external serialized-output theorem is total over all input bitstrings:

```text
size (compileEncodedCNFToNAND bits)
  ≤ 4 × ((5 × (n + 1)) × (15 × (n + 1)) + 19 × (n + 1)),
```

where `n = size bits`. The proof derives formula mass from the strict decoder
and derives serialized circuit size from typed sources and gates; it accepts
no caller-supplied size certificate. The displayed bound is quadratic in
`n`.

Finally, `buildLockedNANDFromCNF_correct` composes this semantic compiler with
the already-proved strict locked-NAND builder:

```text
CNFSAT bits
  ↔ EncodedLockedNANDThreshold (buildLockedNANDFromCNF bits).
```

## Legacy anchor and exact boundary

The construction follows the CNF-to-NAND and locked-NAND dependency route in
the canonical legacy manuscript pinned by `archive/legacy-v0/ARCHIVE.json`.
That manuscript supplies the intended route; Lean remains the authority for
whether each step is valid. If Lean exposes a contradiction or missing
premise, the implementation must stop or replace that step rather than force
the legacy claim.

This milestone is deliberately a semantic compiler and output-size theorem.
It does not yet implement the compiler as a finite work machine, provide a
`FunctionProgram.RawRefinement`, construct a `PolynomialTimeFunction`, or
package a `PolynomialReduction CNFSAT EncodedNANDSAT`. It therefore does not
by itself establish CNFSAT NP-hardness transport, a deterministic
polynomial-time CNFSAT decider, the abstract report-level locked-NAND
premise, ZeroSlack/PCCMin, or P = NP.

## Verification surface

The public module, all 25 new declarations, and 16 reused boundaries are
covered by:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCNFToNANDAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFToNAND.lean
node --test audits/lean-concrete-cnf-to-nand0.test.mjs
```

The audit permits only the established Lean-standard `propext` and
`Quot.sound` closure. It rejects project axioms, `Classical.choice`,
placeholders, native/SAT shortcuts, host-side lookup, caller certificates,
and finite-machine or complexity-class overclaims. The measured transcript
has 16 declarations with empty closure, 11 using only `propext`, and 14 using
only `propext` and `Quot.sound`.

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-31-93` records 21,020 declarations,
11,477 theorems, 5,987 assumption-free theorems, 11,970 excluded private
declarations, 186 source-closure modules, and 2,053 reviewed milestone
candidates. Its 12,933,372 canonical bytes have SHA-256
`576816bd782378cd1d19ad1de76485b82896e6f141853946b6e0ad7df1fefa82`.
The exact Lean source closure has SHA-256
`daed8c40eb6416b42d6b78d87b118b8033bbb5f3e857874c3d1ee45cf89e8876`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-07-31-93` contains 73 milestones: 70
earned and three deliberately unearned. It pins 2,053 theorem types; its
671,083 bytes have SHA-256
`c821adfcb65b9bce9c894b5debf99b9ba661457d865e9fed4ecedfd5ff3db88b`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-31-93`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-07-31-CNF-TO-NAND-SEMANTIC-COMPILER-92`,
records this semantic boundary as earned. Its 1,646,904 bytes have SHA-256
`1fa05f578f1291018c07f3fea452ff970c5bb00950f9382f13956358c94e17ae`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-31-93` has a
171,476-byte TeX source with SHA-256
`505442a00b5b3ebf40a173ee22faf86bc0eb6a12a921899a670a23fc54c6e67d`
and a deterministic 67-page, 415,380-byte A4 PDF with SHA-256
`e042bd2d3263b541adb57295c925aaef4ef38fef7b4cfe7d192d45f772593e49`.

The concrete publication gate remains false, all four disclosed project
assumptions and all six blockers remain, the activation fingerprints remain
unset, and `PNP.Main.p_eq_np` remains absent.
