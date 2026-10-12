import PNP.Concrete.BitRegisterInspection

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Operation

example : workRunExact? (emptyAt 0) 8
    ⟨(emptyAt 0).startState, (Store.cons [] .nil).tape [] 2⟩ =
    some ⟨(emptyAt 0).acceptState, (Store.cons [] .nil).tape [] 2⟩ :=
  Store.empty_run (Store.cons [] .nil) 0 [] 2
example : workRunExact? (emptyAt 1) 13
    ⟨(emptyAt 1).startState, (Store.cons [true] (Store.cons [false] .nil)).tape [] 0⟩ =
    some ⟨(emptyAt 1).rejectState, (Store.cons [true] (Store.cons [false] .nil)).tape [] 0⟩ :=
  Store.empty_run (Store.cons [true] (Store.cons [false] .nil)) 1 [] 0
example : workRunExact? (headAt 1) 11
    ⟨(headAt 1).startState, (Store.cons [] (Store.cons [true, false] .nil)).tape [] 3⟩ =
    some ⟨(headAt 1).acceptState, (Store.cons [] (Store.cons [true, false] .nil)).tape [] 3⟩ :=
  Store.head_run (Store.cons [] (Store.cons [true, false] .nil)) 1 true [false] rfl [] 3
example : workRunExact? (headAt 0) 8
    ⟨(headAt 0).startState, (Store.cons [false, true] .nil).tape [WorkSymbol.oneOne] 4⟩ =
    some ⟨(headAt 0).rejectState, (Store.cons [false, true] .nil).tape [WorkSymbol.oneOne] 4⟩ :=
  Store.head_run (Store.cons [false, true] .nil) 0 false [true] rfl [WorkSymbol.oneOne] 4

-- Empty head inspection is not silently treated as a zero branch.
example : workRunExact? (headAt 0) 4
    ⟨(headAt 0).startState, (Store.cons [] .nil).tape [] 0⟩ = none := by rfl
example {count : Nat} (store : Store count) (index : Fin count) :
    store.inspectSteps index ≤ 3 * (store.span + 2) :=
  Store.inspectSteps_le store index

#print axioms Operation.headBit_wellFormed
#print axioms Operation.inspectGraph_wellFormed
#print axioms Operation.inspectAt_wellFormed
#print axioms Operation.inspect_accept_run
#print axioms Operation.inspect_reject_run
#print axioms Operation.emptyAt_wellFormed
#print axioms Operation.headAt_wellFormed
#print axioms Operation.emptyAt_run
#print axioms Operation.headAt_run
#print axioms Operation.inspectSteps_le
#print axioms Store.empty_run
#print axioms Store.head_run
#print axioms Store.empty_raw_run
#print axioms Store.head_raw_run
#print axioms Store.inspectSteps_le
