/-
Copyright (c) 2026 PNP Labs.

Ordered coefficient-stream semantics and source ell terms. Composition
preserves row order, duplicate rows and the exact unary count prefix.
-/
import PNP.Concrete.NormalizerCoefficientBasicRows

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
abbrev Row := Nat × Bool
def stream : List Row → BitString
  | [] => []
  | row::rest => CoefficientRow.bits row.1 row.2 ++ stream rest
theorem stream_append (xs ys : List Row) : stream (xs++ys) = stream xs ++ stream ys := by
  induction xs with
  | nil => rfl
  | cons row rest ih =>
      rw [List.cons_append,stream,stream,ih,List.append_assoc]
def Emits (before after : State) (rows : List Row) : Prop :=
  after.count = List.replicate rows.length true ++ before.count ∧
  after.buffer = (stream rows).reverse ++ before.buffer
theorem emits_none (before after : State) (count : after.count = before.count)
    (buffer : after.buffer = before.buffer) : Emits before after [] := ⟨count,buffer⟩
theorem emits_one (before after : State) (row : Row)
    (count : after.count = true::before.count)
    (buffer : after.buffer = (CoefficientRow.bits row.1 row.2).reverse ++ before.buffer) :
    Emits before after [row] := by
  exact ⟨count,by simpa only [stream,List.append_nil] using buffer⟩
theorem replicate_sum (n m : Nat) :
    List.replicate (n+m) true = List.replicate n true ++ List.replicate m true := by
  induction n with
  | zero => simp only [Nat.zero_add,List.replicate_zero,List.nil_append]
  | succ n ih =>
      rw [Nat.succ_add,List.replicate_succ,List.replicate_succ,ih]
      rfl
theorem emits_trans (a b c : State) (xs ys : List Row)
    (first : Emits a b xs) (second : Emits b c ys) : Emits a c (xs++ys) := by
  constructor
  · rw [List.length_append]
    calc c.count = List.replicate ys.length true ++ (List.replicate xs.length true ++ a.count) := by
            rw [second.1,first.1]
         _ = List.replicate (ys.length+xs.length) true ++ a.count := by
            rw [replicate_sum,List.append_assoc]
         _ = List.replicate (xs.length+ys.length) true ++ a.count := by
            rw [Nat.add_comm ys.length xs.length]
  · rw [second.2,first.2,stream_append,List.reverse_append,List.append_assoc]

theorem variableRow_indices (r : State) :
    (variableRow.result r).variableIndex = r.variableIndex ∧
    (variableRow.result r).auxiliary = r.auxiliary := by
  rw [variableRow_result]
  exact ⟨rfl,rfl⟩
theorem auxiliaryRow_indices (r : State) :
    (auxiliaryRow.result r).variableIndex = r.variableIndex ∧
    (auxiliaryRow.result r).auxiliary = r.auxiliary := by
  rw [auxiliaryRow_result]
  exact ⟨rfl,rfl⟩
theorem variableRow_emits (r : State) (owners slots : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    Emits r (variableRow.result r) [(owner,OrdinalTest.ordinalMatches 2 (MatchingTable.read slots v))] := by
  have h := variableRow_buffers r owners slots v owner ownerTable slotTable selected found
  exact emits_one _ _ _ h.1 h.2
theorem auxiliaryRow_emits (r : State) (modes : MatchingTable.Entries) (i : Nat)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (selected : r.auxiliary = List.replicate i true) :
    Emits r (auxiliaryRow.result r) [(i,!OrdinalTest.ordinalMatches 2 (MatchingTable.read modes i))] := by
  have h := auxiliaryRow_buffers r modes i modeTable selected
  exact emits_one _ _ _ h.1 h.2

def stashAuxiliary : Routine where
  block := .seq (.action (.copy 23 8)) (.action (.pop 23))
  result r := {r with auxiliary := r.registers.output.tail}
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def captureOwner : Routine := Routine.seq (queryRoutine .owner .variableIndex) stashAuxiliary
theorem captureOwner_data (r : State) : (captureOwner.result r).data = r.data :=
  Routine.seq_data _ _ (queried_data .owner .variableIndex) (by intro r; rfl) r
theorem captureOwner_buffers (r : State) :
    (captureOwner.result r).count = r.count ∧ (captureOwner.result r).buffer = r.buffer := ⟨rfl,rfl⟩
theorem captureOwner_variable (r : State) : (captureOwner.result r).variableIndex = r.variableIndex := rfl
theorem captureOwner_index (r : State) (owners : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    (captureOwner.result r).auxiliary = List.replicate owner true := by
  have read := query_canonical .owner .variableIndex r owners v ownerTable selected
  rw [found] at read
  change (queried .owner .variableIndex r).registers.output.tail = _
  rw [read]
  rfl
def ownerAuxiliary : Routine := Routine.seq captureOwner auxiliaryRow
theorem ownerAuxiliary_data (r : State) : (ownerAuxiliary.result r).data = r.data :=
  Routine.seq_data _ _ captureOwner_data auxiliaryRow_data r
theorem ownerAuxiliary_emits (r : State) (owners modes : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    Emits r (ownerAuxiliary.result r) [(owner,!OrdinalTest.ordinalMatches 2 (MatchingTable.read modes owner))] := by
  have captured := captureOwner_index r owners v owner ownerTable selected found
  have kept := captureOwner_data r
  have modeRead : (captureOwner.result r).core.target = MatchingTable.encode modes :=
    (congrArg Data.modes kept).trans modeTable
  have emitted := auxiliaryRow_emits (captureOwner.result r) modes owner modeRead captured
  have unchanged := captureOwner_buffers r
  exact emits_trans r (captureOwner.result r) (ownerAuxiliary.result r) [] _
    (emits_none _ _ unchanged.1 unchanged.2) emitted

attribute [local irreducible] variableRow auxiliaryRow captureOwner ownerAuxiliary

def doubleEll : Routine := Routine.seq variableRow ownerAuxiliary
def ellTerms : Routine :=
  Routine.seq (queryOrdinal .slot .variableIndex 1) (Routine.choose 8 variableRow doubleEll)
def ellRows (owner : Nat) (slot mode : Option Nat) : List Row :=
  if OrdinalTest.ordinalMatches 1 slot then
    [(owner,OrdinalTest.ordinalMatches 2 slot),(owner,!OrdinalTest.ordinalMatches 2 mode)]
  else [(owner,OrdinalTest.ordinalMatches 2 slot)]
theorem doubleEll_data (r : State) : (doubleEll.result r).data = r.data :=
  Routine.seq_data _ _ variableRow_data ownerAuxiliary_data r
theorem ellTerms_data (r : State) : (ellTerms.result r).data = r.data :=
  Routine.seq_data _ _ (queryOrdinal_data .slot .variableIndex 1)
    (Routine.choose_data 8 _ _ variableRow_data doubleEll_data) r
theorem doubleEll_emits (r : State) (owners slots modes : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    Emits r (doubleEll.result r)
      [(owner,OrdinalTest.ordinalMatches 2 (MatchingTable.read slots v)),
       (owner,!OrdinalTest.ordinalMatches 2 (MatchingTable.read modes owner))] := by
  have first := variableRow_emits r owners slots v owner ownerTable slotTable selected found
  have kept := variableRow_data r
  have ownerRead := (congrArg Data.owners kept).trans ownerTable
  have modeRead := (congrArg Data.modes kept).trans modeTable
  have index := (variableRow_indices r).1.trans selected
  have second := ownerAuxiliary_emits (variableRow.result r) owners modes v owner ownerRead modeRead index found
  exact emits_trans r (variableRow.result r) (doubleEll.result r) _ _ first second
theorem ellTerms_emits (r : State) (owners slots modes : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    Emits r (ellTerms.result r)
      (ellRows owner (MatchingTable.read slots v) (MatchingTable.read modes owner)) := by
  let before := (queryOrdinal .slot .variableIndex 1).result r
  have read := queryOrdinal_output .slot .variableIndex 1 r slots v slotTable selected
  have flag : ForwardEdge.present before.registers.output = OrdinalTest.ordinalMatches 1 (MatchingTable.read slots v) := by
    rw [read]
    rfl
  have kept := queryOrdinal_data .slot .variableIndex 1 r
  have ownerRead := (congrArg Data.owners kept).trans ownerTable
  have slotRead := (congrArg Data.slots kept).trans slotTable
  have modeRead := (congrArg Data.modes kept).trans modeTable
  have index := (queryOrdinal_indices .slot .variableIndex 1 r).1.trans selected
  have unchanged := queryOrdinal_buffers .slot .variableIndex 1 r
  have quiet : Emits r before [] := emits_none _ _ unchanged.1 unchanged.2
  change Emits r ((Routine.choose 8 variableRow doubleEll).result before) _
  rw [choose_output_result,flag]
  cases h : OrdinalTest.ordinalMatches 1 (MatchingTable.read slots v)
  · simp only [Bool.false_eq_true,ite_false,ellRows,h]
    exact emits_trans r before (variableRow.result before) [] _
      quiet (variableRow_emits before owners slots v owner ownerRead slotRead index found)
  · simp only [ite_true,ellRows,h]
    exact emits_trans r before (doubleEll.result before) [] _
      quiet (doubleEll_emits before owners slots modes v owner ownerRead slotRead modeRead index found)

end PNP.Concrete.NormalizerBlocks.Coefficient
