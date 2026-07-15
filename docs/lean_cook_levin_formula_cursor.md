# Direct Cook--Levin formula cursor

`lean/PNP/Concrete/CookLevinFormulaCursor.lean` adds coordinate-driven lookup
and a fuelled specification cursor for the rectangular Cook--Levin formula
schedule. It is a specification milestone toward a raw formula builder. It is
not a raw finite machine, a constant-time slot interpreter, a construction
runtime theorem, or a polynomial reduction.

## Direct coordinate hierarchy

The executable definitions decode one requested coordinate without first
constructing the complete constraint program, clause list, token stream, or
encoded formula. The hierarchy is:

1. recursive direct lookup over finite variable-width blocks;
2. direct local-clause lookup, including pairwise exactly-one clauses;
3. direct unary, literal, clause, and token-bit lookup;
4. direct shape, initial-row, control, and preservation constraint regions;
5. direct fixed clause and token rectangles; and
6. a direct raw-bit slot plus the canonical final zero bit.

The direct definitions do not reference `problem.program`, `problem.formula`,
`problem.encodedFormula`, any materialized formula schedule, `encodeCNFTokens`,
or `encodeCNF`. Those canonical objects occur only in correctness theorems.
Small local three-constraint control blocks and preservation blocks remain
ordinary Lean specification data; this milestone makes no raw execution-cost
claim about evaluating them.

Every layered decoder preserves nested option semantics exactly:

- outer `none` means the requested coordinate is outside the schedule;
- `some none` means the coordinate is valid padding; and
- `some (some value)` means the coordinate is populated.

## Earned endpoint theorems

For every concrete verifier-tableau problem and natural coordinate, Lean
proves the direct constraint, clause, token, and bit decoders equal the
corresponding canonical schedule lookup:

```text
formulaConstraintSlotDirect_eq :
  problem.formulaConstraintSlotDirect index =
    problem.formulaConstraintSchedule[index]?

formulaClauseSlotDirect_eq :
  problem.formulaClauseSlotDirect index =
    problem.formulaClauseSchedule[index]?

formulaTokenSlotDirect_eq :
  problem.formulaTokenSlotDirect index =
    problem.formulaTokenSchedule[index]?

formulaBitSlotDirect_eq :
  problem.formulaBitSlotDirect index =
    problem.formulaBitSchedule[index]?
```

The direct raw-bit opportunity count is exactly the existing external encoded
formula-size polynomial:

```text
formulaBitSlotCountDirect_eq_polynomial :
  problem.formulaBitSlotCountDirect =
    (encodedFormulaSizePolynomial problem.verifier).eval
      (BitString.size problem.input)
```

`FormulaBitCursor.run_prefix` proves exact bounded-prefix behavior from every
valid starting coordinate. The terminal and boundary results include:

```text
FormulaBitCursor.run_full :
  FormulaBitCursor.run problem problem.formulaBitSlotCountDirect
      FormulaBitCursor.initial =
    (problem.formulaBitSchedule,
      ⟨problem.formulaBitSlotCountDirect⟩)

FormulaBitCursor.step_at_end :
  FormulaBitCursor.step problem
      ⟨problem.formulaBitSlotCountDirect⟩ = none

FormulaBitCursor.run_one_step_short :
  FormulaBitCursor.run problem (problem.formulaBitSlotCountDirect - 1)
      FormulaBitCursor.initial =
    (problem.formulaBitSchedule.take
      (problem.formulaBitSlotCountDirect - 1),
      ⟨problem.formulaBitSlotCountDirect - 1⟩)

FormulaBitCursor.run_excess :
  FormulaBitCursor.run problem
      (problem.formulaBitSlotCountDirect + extra)
      FormulaBitCursor.initial =
    (problem.formulaBitSchedule,
      ⟨problem.formulaBitSlotCountDirect⟩)

FormulaBitCursor.run_full_emit_eq_encodedFormula :
  FormulaSchedule.emit
      (FormulaBitCursor.run problem problem.formulaBitSlotCountDirect
        FormulaBitCursor.initial).1 =
    problem.encodedFormula
```

Thus exact fuel consumes every direct schedule opportunity, one-step-short
fuel stops at the final opportunity, the next exact step reaches the terminal
cursor, excess fuel does not change the result, and filtering populated output
bits yields the canonical encoded formula.

## Audit and exact boundary

All 129 explicit declarations are listed in
`lean-audit/PNPConcreteCookLevinFormulaCursorAxiomAudit.lean`. Their compiled
closures use only `propext` and `Quot.sound` where Lean library proofs require
them. They use no project axiom, `Classical.choice`, `sorry`, `admit`, oracle,
SAT call, minimization shortcut, or caller-supplied certificate.

The regression file covers empty, one-bit, odd, and even source inputs across
both verifier input modes. It checks populated padding, valid empty padding,
out-of-range lookup, exact full fuel, one-step-short fuel, terminal behavior,
excess fuel, the external size polynomial, and exact emitted output. A hostile
source audit rejects canonical-data dependencies, collapsed padding states,
final-bit drift, terminal drift, endpoint removal, and theorem overclaim.

This milestone does not provide a raw finite-machine formula builder, a raw
runtime/output polynomial, a `FunctionProgram.RawRefinement`, a concrete
`PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or P = NP. The
concrete publication gate remains false.
