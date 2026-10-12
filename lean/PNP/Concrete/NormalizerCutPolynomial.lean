/-
Copyright (c) 2026 PNP Labs.

Complete finite-tape cut construction from original encoded width/formula.
One polynomial covers matching, terminal trace, both selections and the
four-field output packet. Runtime and output size hold on every raw input;
canonical correctness requires no supplied intermediate data.
-/
import PNP.Concrete.NormalizerCutPack

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister

def block : Block 36 := .seq prepareBlock pack
def program : Program 36 := block.program 0 8
def result (input : BitString) : State := packed (prepared input)
def sourceSteps (input : BitString) : Nat := prepareSteps input + packFuel (prepared input)
def sourceFuel : NatPolynomial := .add prepareFuel (.add (.mul (.constant 36) prepareSize) (.constant 46))
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = prepareFuel.eval size + (36 * prepareSize.eval size + 46) := rfl
theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (prepare_exec input) (pack_exec (prepared input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(initial input).store⟩ := by
  have core : (Store.empty 33).set (0 : Fin 33) input = (MatchingDriver.initial input).store := by
    simpa only [BitRegister.initial, MatchingDriver.program, Block.program] using
      congrArg Configuration.store (MatchingDriver.initial_registers input)
  dsimp only [program, Block.program, BitRegister.initial, initial, State.store, State.frame]
  rw [← core]
  rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem State.get_output (r : State) : r.store.get (8 : Fin 36) = r.registers.output := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]
attribute [local irreducible] State.store

theorem sourceSteps_bound (input : BitString) :
    sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have construction := prepareSteps_bound input
  have packing := packFuel_bound (prepared input) (prepareSize.eval input.length) (prepared_bounded input)
  rw [sourceFuel_eval]
  unfold sourceSteps
  omega
theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input + 1) + (sourceFuel.eval input.length - (sourceSteps input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]
theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 36 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run, State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem result_data (width : Nat) (formula : List (List CNFLiteral)) :
    Canonical width formula (result (MatchingDriver.encode width formula)) := by
  have data := prepared_canonical width formula
  have frame := packed_frame (prepared (MatchingDriver.encode width formula))
  exact ⟨frame.1.trans data.widthRead, frame.2.1.trans data.formulaRead,
    frame.2.2.1.trans data.matchingRead, frame.2.2.2.1.trans data.traceRead,
    frame.2.2.2.2.1.trans data.clausesRead, frame.2.2.2.2.2.trans data.variablesRead⟩
def canonicalPacket (width : Nat) (formula : List (List CNFLiteral)) : BitString :=
  let matching := MatchingLoop.fullTable width formula
  let trace := Search.traceValue width formula matching
  packet (MatchingTable.encode matching) (TraceData.encode trace)
    (SearchVertices.encodeVertices (CutSelection.selected true trace formula.length 0))
    (SearchVertices.encodeVertices (CutSelection.selected false trace width 0))
theorem result_canonical (width : Nat) (formula : List (List CNFLiteral)) :
    (result (MatchingDriver.encode width formula)).registers.output = canonicalPacket width formula := by
  have data := prepared_canonical width formula
  rw [result, packed_output, data.matchingRead, data.traceRead, data.clausesRead, data.variablesRead]
  rfl
theorem polynomial_canonical (width : Nat) (formula : List (List CNFLiteral)) :
    polynomial.output (MatchingDriver.encode width formula) = canonicalPacket width formula := by
  rw [polynomial_output, result_canonical]
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (width : Nat) (formula : List (List CNFLiteral)) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval (MatchingDriver.encode width formula).length)
      (MatchingDriver.encode width formula) = canonicalPacket width formula := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CutDriver
