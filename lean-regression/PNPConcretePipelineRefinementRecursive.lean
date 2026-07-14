import PNP

namespace PNP.Concrete.PipelineRefinementRecursiveRegression

def identityLeaf : FunctionProgram :=
  .machine immediateAcceptMachine (.constant 0)

def identityTwice : FunctionProgram :=
  .compose identityLeaf identityLeaf

def identityThrice : FunctionProgram :=
  .compose identityTwice identityLeaf

theorem identityLeaf_halts (input : BitString) :
    identityLeaf.Halts input := by
  exact Verdict.noConfusion

theorem identityTwice_halts (input : BitString) :
    identityTwice.Halts input := by
  exact ⟨identityLeaf_halts input, identityLeaf_halts input⟩

theorem identityThrice_halts (input : BitString) :
    identityThrice.Halts input := by
  exact ⟨identityTwice_halts input, identityLeaf_halts input⟩

/-- Structural function compilation preserves arbitrary empty, odd, even,
and otherwise malformed raw words through nested composition. -/
example (input : BitString) :
    machineOutput (FunctionProgram.RawRefinement.compile identityThrice).machine
        ((FunctionProgram.RawRefinement.compile identityThrice).timeBound.eval
          (BitString.size input)) input = input := by
  rw [FunctionProgram.RawRefinement.compile_output_eq identityThrice input
    (identityThrice_halts input)]
  change machineOutput immediateAcceptMachine 0
      (machineOutput immediateAcceptMachine 0
        (machineOutput immediateAcceptMachine 0 input)) = input
  rw [machineOutput_immediateAccept_zero,
    machineOutput_immediateAccept_zero,
    machineOutput_immediateAccept_zero]

def rejectLeaf : DecisionProgram :=
  .machine immediateRejectMachine (.constant 0)

def nestedReject : DecisionProgram :=
  .precompose identityLeaf (.precompose identityTwice rejectLeaf)

theorem rejectLeaf_halts (input : BitString) : rejectLeaf.Halts input := by
  exact Verdict.noConfusion

theorem nestedReject_halts (input : BitString) : nestedReject.Halts input := by
  exact ⟨identityLeaf_halts input,
    identityTwice_halts (identityLeaf.eval input),
    rejectLeaf_halts (identityTwice.eval (identityLeaf.eval input))⟩

/-- Structural decision compilation traverses nested preprocessing and keeps
the terminal decision verdict exact. -/
example (input : BitString) :
    boundedDecide (DecisionProgram.RawRefinement.compile nestedReject).machine
        ((DecisionProgram.RawRefinement.compile nestedReject).timeBound.eval
          (BitString.size input)) input = .reject := by
  rw [DecisionProgram.RawRefinement.compile_verdict_eq nestedReject input
    (nestedReject_halts input)]
  rfl

def polynomialNestedReject : PolynomialTimeDecider (fun _ => False) :=
  PolynomialTimeDecider.precompose PolynomialTimeFunction.identity
    (PolynomialTimeDecider.ofMachine rejectAllPolynomialTime)

/-- A complete charged decider now compiles directly to one raw polynomial-
time machine with unchanged language semantics. -/
example (input : BitString) :
    boundedDecide (PolynomialTimeDecider.compileToMachine
        polynomialNestedReject).machine
        ((PolynomialTimeDecider.compileToMachine
          polynomialNestedReject).timeBound.eval (BitString.size input))
        input ≠ .accept := by
  intro hAccept
  have hLanguage := (PolynomialTimeDecider.compileToMachine_accepts_iff
    polynomialNestedReject input).1 hAccept
  exact hLanguage

end PNP.Concrete.PipelineRefinementRecursiveRegression
