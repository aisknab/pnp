/-
Copyright (c) 2026 PNP Labs.

Coefficient branching reads the actual candidate assignment at the literal's
decoded index. The saved sign is scratch data, not a supplied truth premise.
-/
import PNP.Concrete.NormalizerCoefficientAnchor

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

def prepareTruth : Routine where
  block := .seq (.action (.copy 4 8)) (.action (.copy 0 19))
  result r := r.withRegisters {r.registers with sign := r.registers.output, input := r.assignment}
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def bitRoutine : Routine where
  block := liftCore BitLookup.read
  result r := r.withRegisters (BitLookup.result r.registers)
  fuel r := BitLookup.fuel r.registers
  bound := .linear 3 4
  exec r := liftCore_exec _ r _ _ (BitLookup.read_exec _)
  cost r n bounded := by
    have index := Store.get_length_le r.store (1 : Fin 24) bounded
    change r.registers.target.length ≤ n at index
    change 3 * r.registers.target.length + 4 ≤ 3 * n + 4
    omega
def compareSign (sign : Bool) : Routine where
  block := liftCache (CandidateTruth.compareCase sign)
  result r := r.withCore (CandidateTruth.caseCompared sign r.core)
  fuel _ := 3
  bound := .constant 3
  exec r := liftCache_exec _ r _ _ (CandidateTruth.compareCase_exec sign _)
  cost _ _ _ := Nat.le_refl 3
def compareTruth : Routine := Routine.choose 4 (compareSign false) (compareSign true)
theorem compareTruth_result (r : State) :
    compareTruth.result r = r.withRegisters {r.registers with output :=
      [decide (ForwardEdge.present r.registers.output = ForwardEdge.present r.registers.sign)]} := by
  rw [compareTruth,Routine.choose_result]
  change (if ForwardEdge.present r.registers.sign then
    (compareSign true).result r else (compareSign false).result r) = _
  cases ForwardEdge.present r.registers.sign <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

def truthAtLiteral : Routine := Routine.seq prepareTruth (Routine.seq bitRoutine compareTruth)
theorem truthAtLiteral_result (r : State) :
    truthAtLiteral.result r =
      let prepared := prepareTruth.result r
      let bit := bitRoutine.result prepared
      bit.withRegisters {bit.registers with output :=
        [decide (r.assignment[r.registers.target.length]?.getD false =
          ForwardEdge.present r.registers.output)]} := by
  change compareTruth.result (bitRoutine.result (prepareTruth.result r)) = _
  rw [compareTruth_result]
  have read := BitLookup.result_output (prepareTruth.result r).registers
  change (bitRoutine.result (prepareTruth.result r)).registers.output = _ at read
  rw [read]
  rfl
theorem truthAtLiteral_output (r : State) :
    (truthAtLiteral.result r).registers.output =
      [decide (r.assignment[r.registers.target.length]?.getD false =
        ForwardEdge.present r.registers.output)] := by
  rw [truthAtLiteral_result]
  rfl
theorem truthAtLiteral_data (r : State) : (truthAtLiteral.result r).data = r.data := by
  rw [truthAtLiteral_result]
  rfl
theorem truthAtLiteral_buffers (r : State) :
    (truthAtLiteral.result r).count = r.count ∧ (truthAtLiteral.result r).buffer = r.buffer := by
  rw [truthAtLiteral_result]
  exact ⟨rfl,rfl⟩
theorem truthAtLiteral_indices (r : State) :
    (truthAtLiteral.result r).variableIndex = r.variableIndex ∧
    (truthAtLiteral.result r).auxiliary = r.auxiliary := by
  rw [truthAtLiteral_result]
  exact ⟨rfl,rfl⟩

attribute [local irreducible] truthAtLiteral readVariable
def literalTruth (position : Nat) : Routine :=
  Routine.seq (readVariable .row position) truthAtLiteral
theorem literalTruth_data (position : Nat) (r : State) :
    ((literalTruth position).result r).data = r.data :=
  Routine.seq_data _ _ (readVariable_data .row position) truthAtLiteral_data r
theorem literalTruth_buffers (position : Nat) (r : State) :
    ((literalTruth position).result r).count = r.count ∧
    ((literalTruth position).result r).buffer = r.buffer := by
  have first := readVariable_buffers .row position r
  have second := truthAtLiteral_buffers ((readVariable .row position).result r)
  exact ⟨second.1.trans first.1,second.2.trans first.2⟩
theorem literalTruth_canonical (r : State) (formula : List (List CNFLiteral))
    (row : Nat) (leading : List CNFLiteral) (lit : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.core.formula = GraphQuery.clauseData formula)
    (rowRead : r.row = List.replicate row true)
    (clauseRead : formula[row]?.getD [] = leading ++ lit::rest) :
    ((literalTruth leading.length).result r).variableIndex = List.replicate lit.variableIndex true ∧
    ((literalTruth leading.length).result r).registers.output =
      [decide (r.assignment[lit.variableIndex]?.getD false = lit.positive)] := by
  have litRead := readLiteral_canonical .row r formula row leading lit rest formulaRead rowRead clauseRead
  have captured := readVariable_canonical .row r formula row leading lit rest formulaRead rowRead clauseRead
  have target : ((readVariable .row leading.length).result r).registers.target =
      List.replicate lit.variableIndex true := by
    unfold readVariable
    exact litRead.1
  have kept := readVariable_data .row leading.length r
  constructor
  · exact (truthAtLiteral_indices ((readVariable .row leading.length).result r)).1.trans captured.1
  · change (truthAtLiteral.result ((readVariable .row leading.length).result r)).registers.output = _
    rw [truthAtLiteral_output,target,captured.2,List.length_replicate]
    rw [show ((readVariable .row leading.length).result r).assignment = r.assignment from congrArg Data.assignment kept]
    rfl

end PNP.Concrete.NormalizerBlocks.Coefficient
