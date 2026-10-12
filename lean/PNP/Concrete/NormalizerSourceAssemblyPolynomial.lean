/-
Copyright (c) 2026 PNP Labs.

The checker derives its own cache, candidate and first failure, then dispatches
to complete equation assembly. One polynomial bounds literal finite-tape
execution on every raw input. No-failure preserves the checked state; model
recovery and final output-packet composition are separate downstream steps.
-/
import PNP.Concrete.NormalizerSourceAssemblyDispatch

namespace PNP.Concrete.NormalizerBlocks.SourceAssembly
open BitRegister

def initial (input : BitString) : State := extended (CutDriver.initial input)
def checked (input : BitString) : State := extended (SourceCheck.result input)
def check : Block 38 := liftCheck SourceCheck.block
theorem check_exec (input : BitString) :
    Exec check (initial input).store (SourceCheck.sourceSteps input) (checked input).store :=
  liftCheck_exec _ _ _ _ (SourceCheck.block_exec input)

def block : Block 38 := .seq check dispatch
def program : Program 38 := block.program 0 8
def result (input : BitString) : State := dispatched (checked input)
def sourceSteps (input : BitString) : Nat :=
  SourceCheck.sourceSteps input+dispatchSteps (checked input)
theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (check_exec input) (dispatch_exec (checked input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(initial input).store⟩ := by
  have core : (Store.empty 36).set (0 : Fin 36) input = (CutDriver.initial input).store := by
    simpa only [BitRegister.initial,CutDriver.program,Block.program] using
      congrArg BitRegister.Configuration.store (CutDriver.initial_registers input)
  change ⟨.running 0,(Store.empty 38).set (0 : Fin 38) input⟩ =
    (⟨.running 0,(extended (CutDriver.initial input)).store⟩ : BitRegister.Configuration 38)
  rw [extended_store,← core]
  rfl
theorem initial_bounded (input : BitString) : (initial input).store.Bounded input.length :=
  extended_bounded _ _ (CutDriver.initial_bounded input)
theorem store_output (r : State) : r.store.get (8 : Fin 38) = r.registers.output := rfl
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input+1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8
theorem checked_bounded (input : BitString) :
    (checked input).store.Bounded (SourceCheck.resultSize.eval input.length) :=
  extended_bounded _ _ (SourceCheck.result_bounded input)

def dispatchInputFuel : NatPolynomial := dispatchBound.substitute SourceCheck.resultSize
def sourceFuel : NatPolynomial := .add (.add SourceCheck.sourceFuel dispatchInputFuel) (.constant 1)
def resultSize : NatPolynomial := .add .variable sourceFuel
theorem dispatchInputFuel_eval (n : Nat) :
    dispatchInputFuel.eval n = dispatchBound.eval (SourceCheck.resultSize.eval n) :=
  NatPolynomial.eval_substitute _ _ _
theorem sourceFuel_eval (n : Nat) :
    sourceFuel.eval n = SourceCheck.sourceFuel.eval n+dispatchInputFuel.eval n+1 := rfl
theorem resultSize_eval (n : Nat) : resultSize.eval n = n+sourceFuel.eval n := rfl
theorem dispatchSteps_input_bound (input : BitString) :
    dispatchSteps (checked input) ≤ dispatchInputFuel.eval input.length := by
  rw [dispatchInputFuel_eval]
  exact dispatchSteps_bound (checked input) _ (checked_bounded input)
theorem sourceSteps_bound (input : BitString) :
    sourceSteps input+1 ≤ sourceFuel.eval input.length := by
  have first := SourceCheck.sourceSteps_bound input
  have branch := dispatchSteps_input_bound input
  rw [sourceFuel_eval]
  unfold sourceSteps
  omega
theorem result_bounded (input : BitString) :
    (result input).store.Bounded (resultSize.eval input.length) := by
  have executed := (block_exec input).bounded input.length (initial_bounded input)
  apply Store.bounded_mono (store := (result input).store) executed
  rw [resultSize_eval]
  have work := sourceSteps_bound input
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
theorem result_recovery (input : BitString) :
    (result input).recovery = recovery (SourceCheck.result input) :=
  (dispatched_recovery (checked input)).trans (extended_recovery _)
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

end PNP.Concrete.NormalizerBlocks.SourceAssembly
