/-
Copyright (c) 2026 PNP Labs.

Raw-machine refinement contracts and recursive compilers for the finite
charged-pipeline interface.

Every composite is implemented by the literal two-machine compiler.  The
proof recursively consumes only the child refinements and the source
interpreter's own halting evidence.
-/

import PNP.Concrete.PipelineSequentialCompiler

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

/-- Compose two already proved function refinements using one literal finite
sequential machine.  Either first-machine verdict launches the second machine;
only the raw output is passed between them. -/
def compose {first second : FunctionProgram}
    (firstRefinement : RawRefinement first)
    (secondRefinement : RawRefinement second) :
    RawRefinement (.compose first second) :=
  { machine := PipelineSequentialCompiler.sequentialMachine
      firstRefinement.machine secondRefinement.machine
    timeBound := PipelineSequentialCompiler.sequentialRawTimeBound
      firstRefinement.timeBound secondRefinement.timeBound
    haltsWithin := by
      intro input halts
      rcases halts with ⟨firstHalts, secondHalts⟩
      have hFirst := firstRefinement.haltsWithin input firstHalts
      have hFirstOutput := firstRefinement.output_eq input firstHalts
      have hSecond : boundedDecide secondRefinement.machine
          (secondRefinement.timeBound.eval (BitString.size
            (machineOutput firstRefinement.machine
              (firstRefinement.timeBound.eval (BitString.size input)) input)))
          (machineOutput firstRefinement.machine
            (firstRefinement.timeBound.eval (BitString.size input)) input) ≠
          .timeout := by
        rw [hFirstOutput]
        exact secondRefinement.haltsWithin (first.eval input) secondHalts
      rw [(PipelineSequentialCompiler.sequential_correct
        firstRefinement.machine secondRefinement.machine
        firstRefinement.timeBound secondRefinement.timeBound input
        hFirst hSecond).1]
      exact hSecond
    output_eq := by
      intro input halts
      rcases halts with ⟨firstHalts, secondHalts⟩
      have hFirst := firstRefinement.haltsWithin input firstHalts
      have hFirstOutput := firstRefinement.output_eq input firstHalts
      have hSecond : boundedDecide secondRefinement.machine
          (secondRefinement.timeBound.eval (BitString.size
            (machineOutput firstRefinement.machine
              (firstRefinement.timeBound.eval (BitString.size input)) input)))
          (machineOutput firstRefinement.machine
            (firstRefinement.timeBound.eval (BitString.size input)) input) ≠
          .timeout := by
        rw [hFirstOutput]
        exact secondRefinement.haltsWithin (first.eval input) secondHalts
      rw [(PipelineSequentialCompiler.sequential_correct
        firstRefinement.machine secondRefinement.machine
        firstRefinement.timeBound secondRefinement.timeBound input
        hFirst hSecond).2]
      rw [hFirstOutput]
      exact secondRefinement.output_eq (first.eval input) secondHalts }

/-- Structurally compile every finite function-program tree to one raw
single-tape machine. -/
def compile : (source : FunctionProgram) → RawRefinement source
  | .machine machine stepBound => ofMachine machine stepBound
  | .compose first second => compose (compile first) (compile second)

/-- The recursive compiler inherits its exact conditional halting contract. -/
theorem compile_haltsWithin (source : FunctionProgram) (input : BitString)
    (halts : source.Halts input) :
    boundedDecide (compile source).machine
      ((compile source).timeBound.eval (BitString.size input)) input ≠
      .timeout :=
  (compile source).haltsWithin input halts

/-- The recursive compiler preserves the interpreter's exact output. -/
theorem compile_output_eq (source : FunctionProgram) (input : BitString)
    (halts : source.Halts input) :
    machineOutput (compile source).machine
      ((compile source).timeBound.eval (BitString.size input)) input =
      source.eval input :=
  (compile source).output_eq input halts

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

/-- Precompose an already proved decision refinement with an already proved
function refinement using the literal two-machine compiler. -/
def precompose {preprocessor : FunctionProgram} {decision : DecisionProgram}
    (preprocessorRefinement : FunctionProgram.RawRefinement preprocessor)
    (decisionRefinement : RawRefinement decision) :
    RawRefinement (.precompose preprocessor decision) :=
  { machine := PipelineSequentialCompiler.sequentialMachine
      preprocessorRefinement.machine decisionRefinement.machine
    timeBound := PipelineSequentialCompiler.sequentialRawTimeBound
      preprocessorRefinement.timeBound decisionRefinement.timeBound
    haltsWithin := by
      intro input halts
      rcases halts with ⟨preprocessorHalts, decisionHalts⟩
      have hPreprocessor := preprocessorRefinement.haltsWithin input
        preprocessorHalts
      have hPreprocessorOutput := preprocessorRefinement.output_eq input
        preprocessorHalts
      have hDecision : boundedDecide decisionRefinement.machine
          (decisionRefinement.timeBound.eval (BitString.size
            (machineOutput preprocessorRefinement.machine
              (preprocessorRefinement.timeBound.eval
                (BitString.size input)) input)))
          (machineOutput preprocessorRefinement.machine
            (preprocessorRefinement.timeBound.eval
              (BitString.size input)) input) ≠ .timeout := by
        rw [hPreprocessorOutput]
        exact decisionRefinement.haltsWithin (preprocessor.eval input)
          decisionHalts
      rw [(PipelineSequentialCompiler.sequential_correct
        preprocessorRefinement.machine decisionRefinement.machine
        preprocessorRefinement.timeBound decisionRefinement.timeBound input
        hPreprocessor hDecision).1]
      exact hDecision
    verdict_eq := by
      intro input halts
      rcases halts with ⟨preprocessorHalts, decisionHalts⟩
      have hPreprocessor := preprocessorRefinement.haltsWithin input
        preprocessorHalts
      have hPreprocessorOutput := preprocessorRefinement.output_eq input
        preprocessorHalts
      have hDecision : boundedDecide decisionRefinement.machine
          (decisionRefinement.timeBound.eval (BitString.size
            (machineOutput preprocessorRefinement.machine
              (preprocessorRefinement.timeBound.eval
                (BitString.size input)) input)))
          (machineOutput preprocessorRefinement.machine
            (preprocessorRefinement.timeBound.eval
              (BitString.size input)) input) ≠ .timeout := by
        rw [hPreprocessorOutput]
        exact decisionRefinement.haltsWithin (preprocessor.eval input)
          decisionHalts
      rw [(PipelineSequentialCompiler.sequential_correct
        preprocessorRefinement.machine decisionRefinement.machine
        preprocessorRefinement.timeBound decisionRefinement.timeBound input
        hPreprocessor hDecision).1]
      rw [hPreprocessorOutput]
      exact decisionRefinement.verdict_eq (preprocessor.eval input)
        decisionHalts }

/-- Structurally compile every finite decision-program tree to one raw
single-tape machine. -/
def compile : (source : DecisionProgram) → RawRefinement source
  | .machine machine stepBound => ofMachine machine stepBound
  | .precompose preprocessor decision =>
      precompose (FunctionProgram.RawRefinement.compile preprocessor)
        (compile decision)

/-- The recursive decision compiler inherits its conditional halting
contract. -/
theorem compile_haltsWithin (source : DecisionProgram) (input : BitString)
    (halts : source.Halts input) :
    boundedDecide (compile source).machine
      ((compile source).timeBound.eval (BitString.size input)) input ≠
      .timeout :=
  (compile source).haltsWithin input halts

/-- The recursive decision compiler preserves the interpreter's exact
verdict, including timeout exclusion rather than timeout-as-rejection. -/
theorem compile_verdict_eq (source : DecisionProgram) (input : BitString)
    (halts : source.Halts input) :
    boundedDecide (compile source).machine
      ((compile source).timeBound.eval (BitString.size input)) input =
      source.verdict input :=
  (compile source).verdict_eq input halts

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

/-- Compile the complete charged decision tree recursively and expose it as
one raw polynomial-time machine for the same language. -/
def compileToMachine {language : Language}
    (decision : PolynomialTimeDecider language) :
    PolynomialTimeMachine language :=
  toMachine decision
    (DecisionProgram.RawRefinement.compile decision.program)

/-- The recursively compiled raw machine accepts exactly the source
language. -/
theorem compileToMachine_accepts_iff {language : Language}
    (decision : PolynomialTimeDecider language) (input : BitString) :
    boundedDecide (compileToMachine decision).machine
        ((compileToMachine decision).timeBound.eval (BitString.size input))
        input = .accept ↔
      language input :=
  (compileToMachine decision).accepts_iff input

end PolynomialTimeDecider

end PNP.Concrete
