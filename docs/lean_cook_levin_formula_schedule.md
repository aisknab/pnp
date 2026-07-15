# Rectangular Cook--Levin formula schedule

`lean/PNP/Concrete/CookLevinFormulaSchedule.lean` formalizes a finite,
answer-independent schedule for the concrete Cook--Levin formula already proved
correct in the preceding modules. It is a specification milestone toward an
executable formula builder; it is not itself a raw-machine implementation or a
runtime theorem.

## Exact schedule

`FormulaSchedule.pad` preserves a populated list and appends explicit empty
slots. `FormulaSchedule.emit` removes those empty slots without reordering the
populated entries. The concrete schedule then allocates fixed rectangles for:

- all one-hot shape constraints;
- input-only and paired-certificate initialization;
- every state, position, symbol, and bounded-time control opportunity;
- every bounded-time preservation opportunity;
- a fixed clause rectangle for each constraint slot;
- a fixed token rectangle for each clause slot; and
- two bit slots per token plus the canonical final zero bit.

The lookup definitions `formulaConstraintSlot`, `formulaClauseSlot`,
`formulaTokenSlot`, and `formulaBitSlot` expose total access to already-bounded
slots. The schedule definitions do not derive their entries from
`problem.program`, `problem.formula`, `problem.encodedFormula`, or
`encodeCNFTokens`; those existing canonical objects occur only in correctness
statements and proofs.

## Earned endpoint theorems

For every concrete verifier-tableau problem, Lean proves:

```text
formulaConstraintSchedule_length :
  problem.formulaConstraintSchedule.length =
    problem.formulaConstraintSlotCount

formulaConstraintSchedule_emit_eq_program :
  FormulaSchedule.emit problem.formulaConstraintSchedule = problem.program

formulaClauseSchedule_length :
  problem.formulaClauseSchedule.length = problem.formulaClauseSlotCount

formulaClauseSchedule_emit_eq_formulaClauses :
  BoundedClauses.emit (FormulaSchedule.emit problem.formulaClauseSchedule) =
    problem.formula.clauses

formulaTokenSchedule_length :
  problem.formulaTokenSchedule.length =
    (problem.formulaVariableSlotBound + 1) +
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1

formulaBitSchedule_length :
  problem.formulaBitSchedule.length =
    (encodedFormulaSizePolynomial problem.verifier).eval
      (BitString.size problem.input)

formulaBitSchedule_emit_eq_encodedFormula :
  FormulaSchedule.emit problem.formulaBitSchedule = problem.encodedFormula
```

Thus the number of raw bit opportunities is exactly the previously proved
external polynomial, while filtering the populated opportunities yields the
exact canonical encoded formula.

## Audit and boundary

The 79 explicit declarations are covered by
`lean-audit/PNPConcreteCookLevinFormulaScheduleAxiomAudit.lean`. Their closures
use only `propext` and `Quot.sound` where Lean's library proofs require them;
there is no project axiom, `Classical.choice`, `sorry`, `admit`, oracle, SAT
call, or minimization shortcut. The regression file checks empty, one-bit, odd,
and even source inputs across both verifier input modes. A hostile source audit
rejects schedule-order, padding, dependency, endpoint, and overclaim mutations.

This milestone does not interpret a slot as a constant-time operation, provide
a cursor/state machine that emits the slots, prove a construction-runtime
polynomial, construct a `FunctionProgram.RawRefinement`, package a concrete
`PolynomialReduction`, establish CNFSAT NP-completeness or CNFSAT in P, or prove
P = NP. The concrete publication gate therefore remains false.
