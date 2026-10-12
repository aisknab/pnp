/-
Copyright (c) 2026 PNP Labs.

Source variable, auxiliary and extra rows. Row indices and branch tags
come from actual cache reads. The emitted bytes and row counts are proved
for arbitrary source indices and optional mode entries.
-/
import PNP.Concrete.NormalizerCoefficientRoutine

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence

theorem choose_output_result (onFalse onTrue : Routine) (r : State) :
    (Routine.choose 8 onFalse onTrue).result r =
      if ForwardEdge.present r.registers.output then onTrue.result r else onFalse.result r := rfl
def queryOrdinal (kind : CoefficientCache.Kind) (index : Index) (value : Nat) : Routine :=
  Routine.seq (queryRoutine kind index) (ordinalRoutine value)
theorem queryOrdinal_data (kind : CoefficientCache.Kind) (index : Index) (value : Nat) (r : State) :
    ((queryOrdinal kind index value).result r).data = r.data :=
  Routine.seq_data _ _ (queried_data kind index) (by intro r; rfl) r
theorem queryOrdinal_buffers (kind : CoefficientCache.Kind) (index : Index) (value : Nat) (r : State) :
    ((queryOrdinal kind index value).result r).count = r.count ∧
    ((queryOrdinal kind index value).result r).buffer = r.buffer := by
  cases kind <;> exact ⟨rfl,rfl⟩
theorem queryOrdinal_indices (kind : CoefficientCache.Kind) (index : Index) (value : Nat) (r : State) :
    ((queryOrdinal kind index value).result r).variableIndex = r.variableIndex ∧
    ((queryOrdinal kind index value).result r).auxiliary = r.auxiliary := ⟨rfl,rfl⟩
theorem queryOrdinal_output (kind : CoefficientCache.Kind) (index : Index) (value : Nat)
    (r : State) (entries : MatchingTable.Entries) (i : Nat)
    (table : CoefficientCache.table kind r.core = MatchingTable.encode entries)
    (selected : indexWord index r = List.replicate i true) :
    ((queryOrdinal kind index value).result r).registers.output =
      [OrdinalTest.ordinalMatches value (MatchingTable.read entries i)] :=
  OrdinalTest.canonical value (queried kind index r).registers _
    (query_canonical kind index r entries i table selected)

theorem indexEmitted_buffers (index : Index) (tag : Bool) (r : State) :
    (indexEmitted index tag r).count = true::r.count ∧
    (indexEmitted index tag r).buffer =
      (CoefficientRow.bits (indexWord index r).length tag).reverse ++ r.buffer :=
  emitted_buffers tag (rowLoaded index r)
theorem answerEmitted_buffers (tag : Bool) (r : State) :
    (answerEmitted tag r).count = true::r.count ∧
    (answerEmitted tag r).buffer =
      (CoefficientRow.bits r.registers.output.tail.length tag).reverse ++ r.buffer :=
  emitted_buffers tag (answerLoaded r)

def ownerRow (tag : Bool) : Routine :=
  Routine.seq (queryRoutine .owner .variableIndex) (emitAnswerRoutine tag)
theorem ownerRow_data (tag : Bool) (r : State) : ((ownerRow tag).result r).data = r.data :=
  Routine.seq_data _ _ (queried_data .owner .variableIndex) (by intro r; rfl) r
theorem ownerRow_buffers (tag : Bool) (r : State) (owners : MatchingTable.Entries) (v owner : Nat)
    (table : r.core.matching = MatchingTable.encode owners)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    ((ownerRow tag).result r).count = true::r.count ∧
    ((ownerRow tag).result r).buffer = (CoefficientRow.bits owner tag).reverse ++ r.buffer := by
  have read := query_canonical .owner .variableIndex r owners v table selected
  rw [found] at read
  have emit := answerEmitted_buffers tag (queried .owner .variableIndex r)
  have kept := queried_buffers .owner .variableIndex r
  change (answerEmitted tag (queried .owner .variableIndex r)).count = _ ∧
    (answerEmitted tag (queried .owner .variableIndex r)).buffer = _
  rw [emit.1,emit.2,read,kept.1,kept.2]
  simp only [TableOwner.answer,List.tail_cons,List.length_replicate,and_self]

def variableRow : Routine :=
  Routine.seq (queryOrdinal .slot .variableIndex 2) (Routine.choose 8 (ownerRow false) (ownerRow true))
theorem variableRow_result (r : State) :
    variableRow.result r =
      (ownerRow (ForwardEdge.present ((queryOrdinal .slot .variableIndex 2).result r).registers.output)).result
        ((queryOrdinal .slot .variableIndex 2).result r) := by
  rw [variableRow,Routine.seq_result,choose_output_result]
  cases ForwardEdge.present ((queryOrdinal .slot .variableIndex 2).result r).registers.output <;> rfl
theorem variableRow_data (r : State) : (variableRow.result r).data = r.data :=
  Routine.seq_data _ _ (queryOrdinal_data .slot .variableIndex 2)
    (Routine.choose_data 8 _ _ (ownerRow_data false) (ownerRow_data true)) r
theorem variableRow_buffers (r : State) (owners slots : MatchingTable.Entries) (v owner : Nat)
    (ownerTable : r.core.matching = MatchingTable.encode owners)
    (slotTable : r.core.counter = MatchingTable.encode slots)
    (selected : r.variableIndex = List.replicate v true)
    (found : MatchingTable.read owners v = some owner) :
    (variableRow.result r).count = true::r.count ∧
    (variableRow.result r).buffer =
      (CoefficientRow.bits owner (OrdinalTest.ordinalMatches 2 (MatchingTable.read slots v))).reverse ++ r.buffer := by
  let before := (queryOrdinal .slot .variableIndex 2).result r
  have read := queryOrdinal_output .slot .variableIndex 2 r slots v slotTable selected
  have flag : ForwardEdge.present before.registers.output = OrdinalTest.ordinalMatches 2 (MatchingTable.read slots v) := by
    rw [read]
    rfl
  have table : before.core.matching = MatchingTable.encode owners :=
    (congrArg Data.owners (queryOrdinal_data .slot .variableIndex 2 r)).trans ownerTable
  have index : before.variableIndex = List.replicate v true :=
    (queryOrdinal_indices .slot .variableIndex 2 r).1.trans selected
  have emitted := ownerRow_buffers (OrdinalTest.ordinalMatches 2 (MatchingTable.read slots v))
    before owners v owner table index found
  rw [(queryOrdinal_buffers .slot .variableIndex 2 r).1,
    (queryOrdinal_buffers .slot .variableIndex 2 r).2] at emitted
  rw [variableRow_result]
  change ((ownerRow (ForwardEdge.present before.registers.output)).result before).count = _ ∧
    ((ownerRow (ForwardEdge.present before.registers.output)).result before).buffer = _
  rw [flag]
  exact emitted

def auxiliaryRow : Routine := Routine.seq (queryOrdinal .mode .auxiliary 2)
  (Routine.choose 8 (emitIndexRoutine .auxiliary true) (emitIndexRoutine .auxiliary false))
theorem auxiliaryRow_result (r : State) :
    auxiliaryRow.result r =
      indexEmitted .auxiliary (!ForwardEdge.present ((queryOrdinal .mode .auxiliary 2).result r).registers.output)
        ((queryOrdinal .mode .auxiliary 2).result r) := by
  rw [auxiliaryRow,Routine.seq_result,choose_output_result]
  cases ForwardEdge.present ((queryOrdinal .mode .auxiliary 2).result r).registers.output <;> rfl
theorem auxiliaryRow_data (r : State) : (auxiliaryRow.result r).data = r.data :=
  Routine.seq_data _ _ (queryOrdinal_data .mode .auxiliary 2)
    (Routine.choose_data 8 _ _ (by intro r; rfl) (by intro r; rfl)) r
theorem auxiliaryRow_buffers (r : State) (modes : MatchingTable.Entries) (i : Nat)
    (modeTable : r.core.target = MatchingTable.encode modes)
    (selected : r.auxiliary = List.replicate i true) :
    (auxiliaryRow.result r).count = true::r.count ∧
    (auxiliaryRow.result r).buffer =
      (CoefficientRow.bits i (!OrdinalTest.ordinalMatches 2 (MatchingTable.read modes i))).reverse ++ r.buffer := by
  let before := (queryOrdinal .mode .auxiliary 2).result r
  have read := queryOrdinal_output .mode .auxiliary 2 r modes i modeTable selected
  have flag : ForwardEdge.present before.registers.output = OrdinalTest.ordinalMatches 2 (MatchingTable.read modes i) := by
    rw [read]
    rfl
  have index : before.auxiliary = List.replicate i true :=
    (queryOrdinal_indices .mode .auxiliary 2 r).2.trans selected
  have emitted := indexEmitted_buffers .auxiliary (!OrdinalTest.ordinalMatches 2 (MatchingTable.read modes i)) before
  change (indexEmitted .auxiliary _ before).count = true::before.count ∧
    (indexEmitted .auxiliary _ before).buffer = (CoefficientRow.bits before.auxiliary.length _).reverse ++ before.buffer at emitted
  rw [index,List.length_replicate,(queryOrdinal_buffers .mode .auxiliary 2 r).1,
    (queryOrdinal_buffers .mode .auxiliary 2 r).2] at emitted
  rw [auxiliaryRow_result]
  change (indexEmitted .auxiliary (!ForwardEdge.present before.registers.output) before).count = _ ∧
    (indexEmitted .auxiliary (!ForwardEdge.present before.registers.output) before).buffer = _
  rw [flag]
  exact emitted

def extraRow : Routine := emitIndexRoutine .failed false
theorem extraRow_data (r : State) : (extraRow.result r).data = r.data := rfl
theorem extraRow_buffers (r : State) (failed : Nat) (index : r.failed = List.replicate failed true) :
    (extraRow.result r).count = true::r.count ∧
    (extraRow.result r).buffer = (CoefficientRow.bits failed false).reverse ++ r.buffer := by
  have emitted := indexEmitted_buffers .failed false r
  change (extraRow.result r).count = _ ∧ (extraRow.result r).buffer =
    (CoefficientRow.bits r.failed.length false).reverse ++ r.buffer at emitted
  rw [index,List.length_replicate] at emitted
  exact emitted

end PNP.Concrete.NormalizerBlocks.Coefficient
