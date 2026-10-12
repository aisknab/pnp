/-
Copyright (c) 2026 PNP Labs.

All-input polynomial accounting for the complete frontend-record routine.
Each phase is charged against a proved bound on its actual register contents;
the bound does not assume a well-formed record or successful candidate.
-/
import PNP.Concrete.NormalizerOutputPostprocess

namespace PNP.Concrete.NormalizerBlocks.OutputPostprocess
open BitRegister
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store

def preparedSize : NatPolynomial := .add .variable OutputLoader.bound
def checkBudget : NatPolynomial := SourceCheck.sourceFuel.substitute preparedSize
def checkedSize : NatPolynomial := .add preparedSize checkBudget
def dispatchBudget : NatPolynomial := OutputBranches.dispatchBound.substitute checkedSize
def validBudget : NatPolynomial := .add OutputLoader.bound (.add checkBudget dispatchBudget)
def sourceFuel : NatPolynomial := .add validBudget (.constant 6)
def resultSize : NatPolynomial := .add .variable sourceFuel

theorem preparedSize_eval (n : Nat) : preparedSize.eval n = n+OutputLoader.bound.eval n := rfl
theorem checkBudget_eval (n : Nat) :
    checkBudget.eval n = SourceCheck.sourceFuel.eval (preparedSize.eval n) :=
  NatPolynomial.eval_substitute _ _ _
theorem checkedSize_eval (n : Nat) : checkedSize.eval n = preparedSize.eval n+checkBudget.eval n := rfl
theorem dispatchBudget_eval (n : Nat) :
    dispatchBudget.eval n = OutputBranches.dispatchBound.eval (checkedSize.eval n) :=
  NatPolynomial.eval_substitute _ _ _
theorem validBudget_eval (n : Nat) :
    validBudget.eval n = OutputLoader.bound.eval n+(checkBudget.eval n+dispatchBudget.eval n) := rfl
theorem sourceFuel_eval (n : Nat) : sourceFuel.eval n = validBudget.eval n+6 := rfl
theorem resultSize_eval (n : Nat) : resultSize.eval n = n+sourceFuel.eval n := rfl

theorem ready_bounded (input : BitString) :
    (OutputLoader.ready input).store.Bounded (preparedSize.eval input.length) := by
  rw [preparedSize_eval,← OutputLoader.loaded_initial]
  exact OutputLoader.loaded_bounded (initial input) input.length (OutputLoader.initial_bounded input)
private theorem ready_input (input : BitString) :
    (OutputLoader.ready input).registers.input = OutputLoader.checkerInput input := rfl
theorem checkerInput_length (input : BitString) :
    (OutputLoader.checkerInput input).length ≤ preparedSize.eval input.length := by
  have size := Store.get_length_le (OutputLoader.ready input).store (0 : Fin 38) (ready_bounded input)
  rw [store_input,ready_input] at size
  exact size
theorem checkSteps_bound (input : BitString) :
    SourceCheck.sourceSteps (OutputLoader.checkerInput input) ≤ checkBudget.eval input.length := by
  rw [checkBudget_eval]
  have steps := SourceCheck.sourceSteps_bound (OutputLoader.checkerInput input)
  have size := NatPolynomial.eval_mono SourceCheck.sourceFuel (checkerInput_length input)
  omega
theorem checked_bounded (input : BitString) :
    (checked input).store.Bounded (checkedSize.eval input.length) := by
  have work := (check_exec input).bounded (preparedSize.eval input.length) (ready_bounded input)
  apply Store.bounded_mono work
  rw [checkedSize_eval]
  exact Nat.add_le_add_left (checkSteps_bound input) _
theorem dispatchSteps_bound (input : BitString) :
    OutputBranches.dispatchFuel (checker input) (width input) ≤ dispatchBudget.eval input.length := by
  rw [dispatchBudget_eval]
  exact OutputBranches.dispatchFuel_bound (checker input) (width input) _ (checked_bounded input)
theorem validSteps_bound (input : BitString) : validSteps input ≤ validBudget.eval input.length := by
  rw [validBudget_eval]
  exact Nat.add_le_add
    (OutputLoader.fuel_bound (initial input) input.length (OutputLoader.initial_bounded input))
    (Nat.add_le_add (checkSteps_bound input) (dispatchSteps_bound input))
theorem sourceSteps_bound (input : BitString) : sourceSteps input+1 ≤ sourceFuel.eval input.length := by
  rw [sourceFuel_eval]
  have work := validSteps_bound input
  cases tag : input.headD false <;>
    simp only [sourceSteps,tag,Bool.false_eq_true,ite_false,ite_true] <;> omega
theorem result_bounded (input : BitString) :
    (result input).store.Bounded (resultSize.eval input.length) := by
  have work := (block_exec input).bounded input.length (OutputLoader.initial_bounded input)
  apply Store.bounded_mono work
  rw [resultSize_eval]
  have steps := sourceSteps_bound input
  exact Nat.add_le_add_left (by omega : sourceSteps input ≤ sourceFuel.eval input.length) input.length
theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  have work := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input+1)+(sourceFuel.eval input.length-(sourceSteps input+1)) := by omega
  rw [split,BitRegister.run_add,closed_run,BitRegister.run_accepted]
theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 38 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection,CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run,store_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length+sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

end PNP.Concrete.NormalizerBlocks.OutputPostprocess
