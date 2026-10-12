/-
Copyright (c) 2026 PNP Labs.

All source-cache tables and runtime dimensions are constructed from the
original encoded formula. Earlier preparation, owners and modes are reused.
The complete state is retained for system assembly; the output port is the
slot table, not the final normalized packet or a satisfiability decision.
-/
import PNP.Concrete.NormalizerSourceCacheDimensions

namespace PNP.Concrete.NormalizerBlocks.SourceCacheDriver
open BitRegister

def derive : Block 36 := .seq deriveSlots finishData
def derived (r : State) : State := dataFinished (slotsDerived r)
def deriveSteps (r : State) : Nat := slotsSteps r + finishSteps (slotsDerived r)
theorem derive_exec (r : State) : Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (deriveSlots_exec r) (finishData_exec (slotsDerived r))
theorem derived_frame (r : State) :
    (derived r).core.width = r.core.width ∧ (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧ (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧ (derived r).variables = r.variables := by
  have before := slotsDerived_frame r
  have after := dataFinished_frame (slotsDerived r)
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_dimensions (r : State) :
    columns (derived r) = List.replicate (ClauseCount.count r.variables) true ∧
    rows (derived r) = List.replicate (ClauseCount.count r.clauses) true := by
  have after := dataFinished_fields (slotsDerived r)
  rw [(slotsDerived_frame r).2.2.2.2.2] at after
  rw [(slotsDerived_frame r).2.2.2.2.1] at after
  exact ⟨after.1,after.2.1⟩
theorem derived_cache (r : State) :
    slots (derived r) = (slotsDerived r).registers.output ∧
    modes (derived r) = r.registers.output ∧
    owners (derived r) = owners r ∧ literals (derived r) = literals r ∧
    (derived r).registers.output = slots (derived r) := by
  have after := dataFinished_fields (slotsDerived r)
  have before := slotsDerived_cache r
  exact ⟨after.2.2.1,after.2.2.2.1.trans before.1,
    after.2.2.2.2.1.trans before.2.1,after.2.2.2.2.2.1.trans before.2.2,
    after.2.2.2.2.2.2.trans after.2.2.1.symm⟩
theorem derived_slots (r : State) (modeData : MatchingTable.Entries) (ownerData : List CNFLiteral)
    (modeRead : r.registers.output = MatchingTable.encode modeData)
    (ownerRead : owners r = SearchVertices.encodeVertices ownerData) :
    slots (derived r) = MatchingTable.encode (CacheSlots.values modeData ownerData) :=
  (derived_cache r).1.trans (slotsDerived_output r modeData ownerData modeRead ownerRead)
def deriveBound : NatPolynomial := .add slotsBound (.linear 12 9)
theorem deriveBound_eval (n : Nat) : deriveBound.eval n = slotsBound.eval n + (12 * n + 9) := rfl
attribute [local irreducible] CutDriver.State.store

theorem selection_bounds (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    r.variables.length ≤ n ∧ r.clauses.length ≤ n := by
  have variables := Store.get_length_le r.store (35 : Fin 36) (bound := n) bounded
  have clauses := Store.get_length_le r.store (34 : Fin 36) (bound := n) bounded
  rw [CutDriver.State.get_variables] at variables
  rw [CutDriver.State.get_clauses] at clauses
  exact ⟨variables,clauses⟩
theorem deriveSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    deriveSteps r ≤ deriveBound.eval n := by
  have slot := slotsSteps_bound r n bounded
  have finish := finishSteps_bound (slotsDerived r)
  rw [(slotsDerived_frame r).2.2.2.2.2,(slotsDerived_frame r).2.2.2.2.1] at finish
  have sizes := selection_bounds r n bounded
  rw [deriveBound_eval]
  unfold deriveSteps
  omega

def block : Block 36 := .seq ModeCacheDriver.block derive
def program : Program 36 := block.program 0 8
def result (input : BitString) : CutDriver.State := derived (ModeCacheDriver.result input)
def sourceSteps (input : BitString) : Nat :=
  ModeCacheDriver.sourceSteps input + deriveSteps (ModeCacheDriver.result input)
theorem block_exec (input : BitString) :
    Exec block (CutDriver.initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (ModeCacheDriver.block_exec input) (derive_exec (ModeCacheDriver.result input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(CutDriver.initial input).store⟩ := by
  simpa only [program, CutDriver.program, Block.program, BitRegister.initial] using
    CutDriver.initial_registers input
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8


def deriveInputFuel : NatPolynomial := deriveBound.substitute ModeCacheDriver.resultSize
def sourceFuel : NatPolynomial :=
  .add (.add ModeCacheDriver.sourceFuel deriveInputFuel) (.constant 1)
def resultSize : NatPolynomial := .add (.linear 1 0) sourceFuel
theorem deriveInputFuel_eval (size : Nat) :
    deriveInputFuel.eval size = deriveBound.eval (ModeCacheDriver.resultSize.eval size) :=
  NatPolynomial.eval_substitute _ _ _
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = ModeCacheDriver.sourceFuel.eval size + deriveInputFuel.eval size + 1 := rfl
theorem resultSize_eval (size : Nat) : resultSize.eval size = size + sourceFuel.eval size := by
  change (1 * size + 0) + sourceFuel.eval size = _
  rw [Nat.one_mul, Nat.add_zero]
theorem deriveSteps_input_bound (input : BitString) :
    deriveSteps (ModeCacheDriver.result input) ≤ deriveInputFuel.eval input.length := by
  rw [deriveInputFuel_eval]
  exact deriveSteps_bound (ModeCacheDriver.result input)
    (ModeCacheDriver.resultSize.eval input.length) (ModeCacheDriver.result_bounded input)
theorem sourceSteps_bound (input : BitString) :
    sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  rw [sourceFuel_eval]
  have prepared := ModeCacheDriver.sourceSteps_bound input
  have owners := deriveSteps_input_bound input
  unfold sourceSteps
  omega
theorem result_bounded (input : BitString) :
    (result input).store.Bounded (resultSize.eval input.length) := by
  have executed := (block_exec input).bounded input.length (CutDriver.initial_bounded input)
  apply Store.bounded_mono (store := (result input).store) executed
  rw [resultSize_eval]
  have bound := sourceSteps_bound input
  exact Nat.add_le_add_left (by omega : sourceSteps input ≤ sourceFuel.eval input.length) input.length
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
  rw [padded_run, CutDriver.State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem result_data (width : Nat) (formula : List (List CNFLiteral)) :
    CutDriver.Canonical width formula (result (MatchingDriver.encode width formula)) := by
  have data := ModeCacheDriver.result_data width formula
  have frame := derived_frame (ModeCacheDriver.result (MatchingDriver.encode width formula))
  exact ⟨frame.1.trans data.widthRead,frame.2.1.trans data.formulaRead,
    frame.2.2.1.trans data.matchingRead,frame.2.2.2.1.trans data.traceRead,
    frame.2.2.2.2.1.trans data.clausesRead,frame.2.2.2.2.2.trans data.variablesRead⟩
theorem result_dimensions (input : BitString) :
    columns (result input) = List.replicate (ClauseCount.count (ModeCacheDriver.result input).variables) true ∧
    rows (result input) = List.replicate (ClauseCount.count (ModeCacheDriver.result input).clauses) true :=
  derived_dimensions (ModeCacheDriver.result input)
theorem result_cache (input : BitString) :
    modes (result input) = (ModeCacheDriver.result input).registers.output ∧
    owners (result input) = ModeCacheDriver.owners (ModeCacheDriver.result input) ∧
    literals (result input) = ModeCacheDriver.literals (ModeCacheDriver.result input) ∧
    (result input).registers.output = slots (result input) :=
  (derived_cache (ModeCacheDriver.result input)).2
theorem polynomial_slots (input : BitString) : polynomial.output input = slots (result input) := by
  rw [polynomial_output,(result_cache input).2.2.2]
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_slots (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = slots (result input) := by
  rw [machine_output,polynomial_slots]

end PNP.Concrete.NormalizerBlocks.SourceCacheDriver
