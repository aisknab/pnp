/-
Copyright (c) 2026 PNP Labs.

Concrete literal reads for coefficient formulas and the complete anchor
coefficient list. Every anchor index comes from the actual failed-row
literal, rather than a supplied semantic value.
-/
import PNP.Concrete.NormalizerCoefficientEll
import PNP.Concrete.NormalizerCandidateClause

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
attribute [local irreducible] ellTerms extraRow

def loadIndexRoutine (index : Index) : Routine where
  block := loadIndex index
  result := indexLoaded index
  fuel _ := 1
  bound := .constant 1
  exec := loadIndex_exec index
  cost _ _ _ := Nat.le_refl 1
def positionRoutine (position : Nat) : Routine where
  block := liftCache (CandidateTruth.setPosition position)
  result r := r.withCore (CandidateTruth.positioned position r.core)
  fuel _ := position+1
  bound := .constant (position+1)
  exec r := liftCache_exec _ r _ _ (CandidateTruth.setPosition_exec position _)
  cost _ _ _ := Nat.le_refl _
def literalRoutine : Routine where
  block := liftDense CacheLiteral.read
  result r := r.withDense (CacheLiteral.result r.core.core)
  fuel r := CacheLiteral.fuel r.core.core
  bound := CacheLiteral.bound
  exec r := liftDense_exec _ r _ _ (CacheLiteral.read_exec _)
  cost r n bounded := CacheLiteral.fuel_bound r.core.core n
    (Store.get_length_le r.store (13 : Fin 24) bounded)
    (Store.get_length_le r.store (15 : Fin 24) bounded)
    (Store.get_length_le r.store (14 : Fin 24) bounded)
def readLiteral (index : Index) (position : Nat) : Routine :=
  Routine.seq (loadIndexRoutine index) (Routine.seq (positionRoutine position) literalRoutine)
def literalPrepared (index : Index) (position : Nat) (r : State) : DenseClauses.State :=
  {r.core.core with index := indexWord index r, remaining := List.replicate position true}
theorem readLiteral_result (index : Index) (position : Nat) (r : State) :
    (readLiteral index position).result r =
      r.withDense (CacheLiteral.result (literalPrepared index position r)) := rfl
theorem readLiteral_data (index : Index) (position : Nat) (r : State) :
    ((readLiteral index position).result r).data = r.data := by
  rw [readLiteral_result]
  exact congrArg (fun formula => Data.mk formula r.core.matching r.core.counter r.core.target
    r.assignment r.failed r.row) (CacheLiteral.result_fields (literalPrepared index position r)).1
theorem readLiteral_buffers (index : Index) (position : Nat) (r : State) :
    ((readLiteral index position).result r).count = r.count ∧
    ((readLiteral index position).result r).buffer = r.buffer := by
  rw [readLiteral_result]
  have h := CacheLiteral.result_fields (literalPrepared index position r)
  exact ⟨h.2.2.2.1,h.2.2.2.2⟩
theorem readLiteral_canonical (index : Index) (r : State) (formula : List (List CNFLiteral))
    (row : Nat) (leading : List CNFLiteral) (lit : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.core.formula = GraphQuery.clauseData formula)
    (rowRead : indexWord index r = List.replicate row true)
    (clauseRead : formula[row]?.getD [] = leading ++ lit::rest) :
    ((readLiteral index leading.length).result r).registers.target = List.replicate lit.variableIndex true ∧
    ((readLiteral index leading.length).result r).registers.output = [lit.positive] := by
  rw [readLiteral_result]
  exact CacheLiteral.canonical (literalPrepared index leading.length r) formula row leading lit rest
    formulaRead rowRead rfl clauseRead
def captureVariable : Routine where
  block := .action (.copy 21 1)
  result r := {r with variableIndex := r.registers.target}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def readVariable (index : Index) (position : Nat) : Routine :=
  Routine.seq (readLiteral index position) captureVariable
theorem readVariable_data (index : Index) (position : Nat) (r : State) :
    ((readVariable index position).result r).data = r.data :=
  Routine.seq_data _ _ (readLiteral_data index position) (by intro r; rfl) r
theorem readVariable_buffers (index : Index) (position : Nat) (r : State) :
    ((readVariable index position).result r).count = r.count ∧
    ((readVariable index position).result r).buffer = r.buffer := readLiteral_buffers index position r
theorem readVariable_canonical (index : Index) (r : State) (formula : List (List CNFLiteral))
    (row : Nat) (leading : List CNFLiteral) (lit : CNFLiteral) (rest : List CNFLiteral)
    (formulaRead : r.core.core.formula = GraphQuery.clauseData formula)
    (rowRead : indexWord index r = List.replicate row true)
    (clauseRead : formula[row]?.getD [] = leading ++ lit::rest) :
    ((readVariable index leading.length).result r).variableIndex = List.replicate lit.variableIndex true ∧
    ((readVariable index leading.length).result r).registers.output = [lit.positive] :=
  readLiteral_canonical index r formula row leading lit rest formulaRead rowRead clauseRead

def anchorEll : Routine := Routine.seq (readVariable .failed 0) ellTerms
def bTerms : Routine := Routine.seq extraRow anchorEll
theorem anchorEll_data (r : State) : (anchorEll.result r).data = r.data :=
  Routine.seq_data _ _ (readVariable_data .failed 0) ellTerms_data r
theorem bTerms_data (r : State) : (bTerms.result r).data = r.data :=
  Routine.seq_data _ _ extraRow_data anchorEll_data r
theorem anchorEll_emits (r : State) (formula : List (List CNFLiteral))
    (owners slots modes : MatchingTable.Entries) (failed owner : Nat) (lit : CNFLiteral)
    (rest : List CNFLiteral)
    (formulaRead : r.core.core.formula = GraphQuery.clauseData formula)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (failedRead : r.failed = List.replicate failed true)
    (clauseRead : formula[failed]?.getD [] = lit::rest)
    (found : MatchingTable.read owners lit.variableIndex = some owner) :
    Emits r (anchorEll.result r) (ellRows owner (MatchingTable.read slots lit.variableIndex)
      (MatchingTable.read modes owner)) := by
  let before := (readVariable .failed 0).result r
  have litRead := readVariable_canonical .failed r formula failed [] lit rest formulaRead failedRead clauseRead
  have kept := readVariable_data .failed 0 r
  have ownerRead := (congrArg Data.owners kept).trans ownerTable
  have slotRead := (congrArg Data.slots kept).trans slotTable
  have modeRead := (congrArg Data.modes kept).trans modeTable
  have emitted := ellTerms_emits before owners slots modes lit.variableIndex owner
    ownerRead slotRead modeRead litRead.1 found
  have quiet := readVariable_buffers .failed 0 r
  exact emits_trans r before (anchorEll.result r) [] _
    (emits_none _ _ quiet.1 quiet.2) emitted
theorem bTerms_emits (r : State) (formula : List (List CNFLiteral))
    (owners slots modes : MatchingTable.Entries) (failed owner : Nat) (lit : CNFLiteral)
    (rest : List CNFLiteral)
    (formulaRead : r.core.core.formula = GraphQuery.clauseData formula)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (failedRead : r.failed = List.replicate failed true)
    (clauseRead : formula[failed]?.getD [] = lit::rest)
    (found : MatchingTable.read owners lit.variableIndex = some owner) :
    Emits r (bTerms.result r) ((failed,false)::ellRows owner
      (MatchingTable.read slots lit.variableIndex) (MatchingTable.read modes owner)) := by
  have extra := extraRow_buffers r failed failedRead
  have kept := extraRow_data r
  have formulas := (congrArg Data.literals kept).trans formulaRead
  have ownersRead := (congrArg Data.owners kept).trans ownerTable
  have slotsRead := (congrArg Data.slots kept).trans slotTable
  have modesRead := (congrArg Data.modes kept).trans modeTable
  have failedIndex := (congrArg Data.failed kept).trans failedRead
  have tail := anchorEll_emits (extraRow.result r) formula owners slots modes failed owner lit rest
    formulas ownersRead slotsRead modesRead failedIndex clauseRead found
  exact emits_trans r (extraRow.result r) (bTerms.result r) [(failed,false)] _
    (emits_one _ _ _ extra.1 extra.2) tail

end PNP.Concrete.NormalizerBlocks.Coefficient
