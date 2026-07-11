/-
Copyright (c) 2026 PNP Labs.

Raw-machine refinement contracts for the finite charged-pipeline interface.

This module pins the exact semantic obligations for a future composite
pipeline compiler and proves the two machine-leaf cases.  It deliberately
does not define composition or precomposition constructors: those require a
real boundary-marked tape simulation and output handoff, not rule-list
concatenation.
-/

import PNP.Concrete.Complexity

namespace PNP.Concrete

namespace FunctionProgram

/-- A raw single-machine implementation of a finite function pipeline.

The semantic and halting clauses are conditional on the charged interpreter's
`Halts` predicate.  This is the condition supplied by every
`PolynomialTimeFunction`; it avoids silently turning a timed-out leaf into an
output claim. -/
structure RawRefinement (source : FunctionProgram) where
  machine : Machine
  timeBound : NatPolynomial
  haltsWithin : ∀ input, source.Halts input →
    boundedDecide machine
      (timeBound.eval (BitString.size input)) input ≠ .timeout
  output_eq : ∀ input, source.Halts input →
    machineOutput machine
      (timeBound.eval (BitString.size input)) input = source.eval input

namespace RawRefinement

/-- A function-program machine leaf is already an exact raw implementation of
itself at the same polynomial budget. -/
def ofMachine (machine : Machine) (stepBound : NatPolynomial) :
    RawRefinement (.machine machine stepBound) :=
  { machine := machine
    timeBound := stepBound
    haltsWithin := by
      intro input halts
      exact halts
    output_eq := by
      intro input _
      rfl }

/-- Raw output inherits the proved output-size bound of a polynomial function
witness whenever a refinement of its complete program is supplied. -/
theorem output_size_le (function : PolynomialTimeFunction)
    (refinement : RawRefinement function.program) (input : BitString) :
    BitString.size
        (machineOutput refinement.machine
          (refinement.timeBound.eval (BitString.size input)) input) ≤
      function.outputSizeBound.eval (BitString.size input) := by
  rw [refinement.output_eq input (function.haltsWithin input)]
  exact function.output_size_le input

end RawRefinement

end FunctionProgram

namespace DecisionProgram

/-- A raw single-machine implementation of a finite decision pipeline.

Exact verdict equality rules out treating timeout as rejection.  As for the
function contract, refinement is required only on inputs for which the source
pipeline's proof-bearing halting predicate holds. -/
structure RawRefinement (source : DecisionProgram) where
  machine : Machine
  timeBound : NatPolynomial
  haltsWithin : ∀ input, source.Halts input →
    boundedDecide machine
      (timeBound.eval (BitString.size input)) input ≠ .timeout
  verdict_eq : ∀ input, source.Halts input →
    boundedDecide machine
      (timeBound.eval (BitString.size input)) input = source.verdict input

namespace RawRefinement

/-- A decision-program machine leaf is already an exact raw implementation of
itself at the same polynomial budget. -/
def ofMachine (machine : Machine) (stepBound : NatPolynomial) :
    RawRefinement (.machine machine stepBound) :=
  { machine := machine
    timeBound := stepBound
    haltsWithin := by
      intro input halts
      exact halts
    verdict_eq := by
      intro input _
      rfl }

end RawRefinement

end DecisionProgram

namespace PolynomialTimeDecider

/-- An exact raw refinement converts a charged polynomial-time decider into
the raw `PolynomialTimeMachine` interface without changing its language. -/
def toMachine {language : Language}
    (decision : PolynomialTimeDecider language)
    (refinement : DecisionProgram.RawRefinement decision.program) :
    PolynomialTimeMachine language :=
  { machine := refinement.machine
    timeBound := refinement.timeBound
    haltsWithin := by
      intro input
      exact refinement.haltsWithin input (decision.haltsWithin input)
    accepts_iff := by
      intro input
      rw [refinement.verdict_eq input (decision.haltsWithin input)]
      exact decision.accepts_iff input }

end PolynomialTimeDecider

end PNP.Concrete
