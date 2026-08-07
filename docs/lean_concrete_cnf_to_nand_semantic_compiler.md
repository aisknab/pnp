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

The same construction is now also exposed as a finite postfix action plan.
Its only actions are `push`, `negate`, and `nand`.
`executeFormulaPlan_exact` proves that executing that plan produces the
original typed compiler circuit exactly, while `emitFormulaPlan_exact`
identifies its serialized bytes. The plan has a closed structural length
formula and a linear bound in the length of any successfully decoded source
word. This is the semantic schedule implemented by the downstream literal
work-machine controller; it is not a host-side oracle or executable lookup.

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

This milestone is deliberately the semantic compiler and output-size layer.
Those theorems alone do not provide a finite work machine,
`FunctionProgram.RawRefinement`, `PolynomialTimeFunction`, or packaged
`PolynomialReduction CNFSAT EncodedNANDSAT`; the subsequent
[all-input polynomial-reduction milestone](./lean_concrete_cnf_to_nand_polynomial_reduction.md)
now supplies those executable interfaces. Neither layer establishes a
deterministic polynomial-time CNFSAT decider, the abstract report-level
locked-NAND premise, ZeroSlack/PCCMin, or P = NP.

## Verification surface

The public module, all 52 declarations, and 16 reused boundaries are
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
and finite-machine or complexity-class overclaims. The measured 68-entry
transcript has 28 declarations with empty closure, 19 using only `propext`,
and 21 using only `propext` and `Quot.sound`.

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-07-109` records 24,583 declarations,
13,218 theorems, 6,971 assumption-free theorems, 14,595 excluded private
declarations, 225 source-closure modules, and 2,299 reviewed milestone
candidates. Its 15,014,491 canonical bytes have SHA-256
`d1743c46154588f40b4f04f5f1a0e02fdd043aa1b62c7f01e5c667d408357212`.
The exact Lean source closure has SHA-256
`c13bb497e99007317cf71871ac88dc94c21645caa70c82770690833f05a2494d`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-07-109` contains 89 milestones: 85
earned and three deliberately unearned. It pins 2,299 theorem types; its
744,575 bytes have SHA-256
`b628ea8684a56e748da90d753b054cce50428af9d213ff8928d0492b82f9cd1f`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-109`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-SIDE-TIGHT-MINIMUM-108`,
records this semantic boundary as earned. Its 1,849,193 bytes have SHA-256
`a29d10e7bc211b2c919910624557941898dc1f2888eb5cd6fc10ba00a6e89abb`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-109` has a
194,451-byte TeX source with SHA-256
`2c4421043189beee57aaf5d2bc6e14aa27584904739dadedbdb40fda4c88555c`
and a deterministic 76-page, 435,428-byte A4 PDF with SHA-256
`3495459a678fdf52d06553ffe2bff603438f037e282b8c257711eb855a0760b3`.

The concrete publication gate remains false, all four disclosed project
assumptions and all six blockers remain, the activation fingerprints remain
unset, and `PNP.Main.p_eq_np` remains absent.
