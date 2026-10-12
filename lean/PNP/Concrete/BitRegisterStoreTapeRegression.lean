import PNP.Concrete.BitRegisterStoreTape

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Operation

example : workRunExact? (pushAt 1 true) 20
    ⟨(pushAt 1 true).startState, (Store.cons [true] (Store.cons [false, true] .nil)).tape [] 0⟩ =
    some ⟨(pushAt 1 true).acceptState,
      (Store.cons [true] (Store.cons [true, false, true] .nil)).tape [] 0⟩ :=
  Store.push_run (Store.cons [true] (Store.cons [false, true] .nil)) 1 true [] 0
example : workRunExact? (popAt 0) 26
    ⟨(popAt 0).startState, (Store.cons [true] (Store.cons [false, true] .nil)).tape [] 0⟩ =
    some ⟨(popAt 0).acceptState,
      (Store.cons [] (Store.cons [false, true] .nil)).tape [] 1⟩ :=
  Store.pop_run (Store.cons [true] (Store.cons [false, true] .nil)) 0 [] 0
example : workRunExact? (clearAt 1) 55
    ⟨(clearAt 1).startState, (Store.cons [true] (Store.cons [false, true] .nil)).tape [] 2⟩ =
    some ⟨(clearAt 1).acceptState, (Store.cons [true] (Store.cons [] .nil)).tape [] 4⟩ :=
  Store.clear_run (Store.cons [true] (Store.cons [false, true] .nil)) 1 [] 2
example : workRunExact? (clearAt 0) 8
    ⟨(clearAt 0).startState, (Store.cons [] .nil).tape [] 7⟩ =
    some ⟨(clearAt 0).acceptState, (Store.cons [] .nil).tape [] 7⟩ :=
  Store.clear_run (Store.cons [] .nil) 0 [] 7
example {count : Nat} (store : Store count) (index : Fin count) :
    bankSpan ((Store.cons [] store).beforeFields index.succ) ((Store.cons [] store).get index.succ)
      (fieldCells ((Store.cons [] store).afterFields index.succ)) = (Store.cons [] store).span + 2 :=
  Store.bankSpan_selected (Store.cons [] store) index.succ
example {count : Nat} (store : Store count) (index : Fin count) (value : BitString)
    (outside : List WorkSymbol) (slack : Nat) :
    (store.set index value).tape outside slack =
      atBoundary (store.beforeFields index) value (fieldCells (store.afterFields index)) outside slack :=
  Store.set_tape_boundary store index value outside slack

#print axioms Operation.fieldWord_append
#print axioms Store.fields_length
#print axioms Store.fields_encode
#print axioms Store.beforeFields_length
#print axioms Store.fields_set_split
#print axioms Store.fields_split
#print axioms Store.span_split
#print axioms Store.bankSpan_selected
#print axioms Store.tape_initial
#print axioms Store.set_tape_boundary
#print axioms Store.tape_boundary
#print axioms Store.push_run
#print axioms Store.pop_run
#print axioms Store.clear_run
#print axioms Store.push_raw_run
#print axioms Store.pop_raw_run
#print axioms Store.clear_raw_run
#print axioms Store.pushSteps_le
#print axioms Store.popSteps_le
#print axioms Store.clearSteps_le
