/-
Copyright (c) 2026 PNP Labs.

Complete finite-tape cut-range selection with a total encoded-input polynomial.
The output is the increasing source range filtered by actual reached nodes.
Both vertex kinds use the same construction; neither takes a supplied answer.
-/
import PNP.Concrete.NormalizerCutSelectionLoader

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister

def loadBuffer : Block 24 := .action (.copy 3 23)
def bufferLoaded (r : State) : State := r.withRegisters {r.registers with excess := r.buffer}
theorem loadBuffer_exec (r : State) : Exec loadBuffer r.store 1 (bufferLoaded r).store := .action _ _
def finish : Block 24 := .seq loadBuffer (liftCore ClauseQuery.pack)
def finished (r : State) : State := (bufferLoaded r).withRegisters (ClauseQuery.packed (bufferLoaded r).registers)
def finishFuel (r : State) : Nat := 4 * r.buffer.length + 13
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have checked := Exec.seq (loadBuffer_exec r) <|
    liftCore_exec _ (bufferLoaded r) _ _ (ClauseQuery.pack_exec _)
  have cost : finishFuel r = 1 + (4 * r.buffer.length + 12) := by unfold finishFuel; omega
  rw [cost]
  exact checked
theorem finished_output (r : State) :
    (finished r).registers.output = r.buffer.reverse ++ [true,false] := rfl

def block (tag : Bool) : Block 24 := .seq (front tag) finish
def program (tag : Bool) : Program 24 := (block tag).program 0 8
def result (tag : Bool) (input : BitString) : State := finished (scanned tag input)
def sourceSteps (tag : Bool) (input : BitString) : Nat := frontSteps tag input + finishFuel (scanned tag input)
def sourceFuel : NatPolynomial := .add (.mul (.constant 5) frontFuel) (.linear 4 14)
theorem sourceFuel_eval (size : Nat) : sourceFuel.eval size = 5 * frontFuel.eval size + (4 * size + 14) := rfl

theorem block_exec (tag : Bool) (input : BitString) :
    Exec (block tag) (initial input).store (sourceSteps tag input) (result tag input).store :=
  Exec.seq (front_exec tag input) (finish_exec (scanned tag input))
theorem initial_store (input : BitString) :
    (initial input).store = .cons input (Store.empty 23) := rfl
theorem initial_registers (tag : Bool) (input : BitString) :
    BitRegister.initial (program tag) input = ⟨.running 0,(initial input).store⟩ := rfl
theorem closed_run (tag : Bool) (input : BitString) :
    BitRegister.run (program tag) (sourceSteps tag input + 1) (BitRegister.initial (program tag) input) =
      ⟨.accepted,(result tag input).store⟩ := by
  rw [initial_registers]
  exact (block_exec tag input).program_run 0 8

theorem sourceSteps_bound (tag : Bool) (input : BitString) :
    sourceSteps tag input + 1 ≤ sourceFuel.eval input.length := by
  have initialBound : (initial input).store.Bounded input.length := by
    rw [initial_store]
    exact ⟨Nat.le_refl _, Store.empty_bounded 23 input.length⟩
  have bounded := (front_exec tag input).bounded input.length initialBound
  have buffer := Store.get_length_le (scanned tag input).store (23 : Fin 24) bounded
  change (scanned tag input).buffer.length ≤ input.length + frontSteps tag input at buffer
  have front := frontSteps_bound tag input
  rw [sourceFuel_eval]
  unfold sourceSteps finishFuel
  omega

theorem padded_run (tag : Bool) (input : BitString) :
    BitRegister.run (program tag) (sourceFuel.eval input.length) (BitRegister.initial (program tag) input) =
      ⟨.accepted,(result tag input).store⟩ := by
  have bound := sourceSteps_bound tag input
  have split : sourceFuel.eval input.length =
      (sourceSteps tag input + 1) + (sourceFuel.eval input.length - (sourceSteps tag input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]
theorem acceptsWithin (tag : Bool) : CompilerIO.AcceptsWithin (program tag) sourceFuel := by
  intro input
  change (BitRegister.run (program tag) (sourceFuel.eval input.length)
    (BitRegister.initial (program tag) input)).control = .accepted
  rw [padded_run]

def polynomial (tag : Bool) : PolynomialTimeFunction :=
  CompilerIO.compilePolynomial (program tag) sourceFuel (acceptsWithin tag)
theorem polynomial_program (tag : Bool) :
    (polynomial tag).program =
      .machine (CompilerIO.rawMachine (program tag)) (CompilerIO.runtimePolynomial 24 sourceFuel) :=
  CompilerIO.compilePolynomial_program (program tag) sourceFuel (acceptsWithin tag)
private theorem polynomial_projection (tag : Bool) (input : BitString) :
    (polynomial tag).output input =
      (CompilerIO.compilePolynomial (program tag) sourceFuel (acceptsWithin tag)).output input := rfl
theorem polynomial_output (tag : Bool) (input : BitString) :
    (polynomial tag).output input = (result tag input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run (program tag) (sourceFuel.eval input.length)
    (BitRegister.initial (program tag) input)).store.get 8 = _
  rw [padded_run]
  rfl
theorem polynomial_accepts (tag : Bool) (input : BitString) :
    boundedDecide (CompilerIO.rawMachine (program tag))
      ((CompilerIO.runtimePolynomial 24 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts (program tag) sourceFuel (acceptsWithin tag) input
theorem polynomial_output_length (tag : Bool) (input : BitString) :
    ((polynomial tag).output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le (program tag) sourceFuel (acceptsWithin tag) input

theorem result_canonical (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    (result tag (encode count trace)).registers.output =
      SearchVertices.encodeVertices (selected tag trace count 0) := by
  rw [result, finished_output, scanned_buffer, List.reverse_reverse]
  exact (UnseenData.encoded_prefix (selected tag trace count 0)).symm
theorem polynomial_canonical (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    (polynomial tag).output (encode count trace) =
      SearchVertices.encodeVertices (selected tag trace count 0) := by
  rw [polynomial_output, result_canonical]
private theorem machine_projection (tag : Bool) (input : BitString) :
    (polynomial tag).output input = machineOutput (CompilerIO.rawMachine (program tag))
      ((CompilerIO.runtimePolynomial 24 sourceFuel).eval input.length) input := rfl
theorem machine_output (tag : Bool) (input : BitString) :
    machineOutput (CompilerIO.rawMachine (program tag))
      ((CompilerIO.runtimePolynomial 24 sourceFuel).eval input.length) input = (polynomial tag).output input :=
  (machine_projection tag input).symm
theorem machine_canonical (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    machineOutput (CompilerIO.rawMachine (program tag))
      ((CompilerIO.runtimePolynomial 24 sourceFuel).eval (encode count trace).length) (encode count trace) =
      SearchVertices.encodeVertices (selected tag trace count 0) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CutSelection
