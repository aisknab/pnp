import PNP.Concrete.BitRegisterCanonical

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Mutation
open PNP.Concrete.BitRegister.Operation

example : workRunExact? (pushAt 0 true) 11
    ⟨(pushAt 0 true).startState, atBoundary [] [] [] [] 0⟩ =
    some ⟨(pushAt 0 true).acceptState, atBoundary [] [true] [] [] 0⟩ :=
  pushAt_run [] true [] [] [] 0
example : workRunExact? (pushAt 1 false) 22
    ⟨(pushAt 1 false).startState, atBoundary [[true]] [true] [.separator, .markedOne] [] 3⟩ =
    some ⟨(pushAt 1 false).acceptState, atBoundary [[true]] [false, true] [.separator, .markedOne] [] 2⟩ :=
  pushAt_run [[true]] false [true] [.separator, .markedOne] [] 3
example : workRunExact? (popAt 0) 8
    ⟨(popAt 0).startState, atBoundary [] [] [] [] 0⟩ =
    some ⟨(popAt 0).acceptState, atBoundary [] [] [] [] 0⟩ :=
  popAt_run [] [] [] [] 0
example : workRunExact? (popAt 0) 14
    ⟨(popAt 0).startState, atBoundary [] [true] [] [] 0⟩ =
    some ⟨(popAt 0).acceptState, atBoundary [] [] [] [] 1⟩ :=
  popAt_run [] [true] [] [] 0
example : workRunExact? (clearAt 0) 40
    ⟨(clearAt 0).startState, atBoundary [] [false, true] [] [] 0⟩ =
    some ⟨(clearAt 0).acceptState, atBoundary [] [] [] [] 2⟩ :=
  clearAt_run [] [false, true] [] [] 0
example (before : List BitString) (bits : BitString) (after : List Cell) :
    pushAtSteps before bits after ≤ 3 * bankSpan before bits after + 2 :=
  pushAtSteps_le before bits after
example (before : List BitString) (bits : BitString) (after : List Cell) :
    popAtSteps before bits after ≤ 4 * bankSpan before bits after :=
  popAtSteps_le before bits after
example (before : List BitString) (bits : BitString) (after : List Cell) :
    clearAtSteps before bits after ≤
      9 * bankSpan before bits after * bankSpan before bits after +
        15 * bankSpan before bits after + 8 :=
  clearAtSteps_le before bits after

#print axioms insert_wellFormed
#print axioms pop_wellFormed
#print axioms home_cursor_run
#print axioms insert_register_run
#print axioms pushFront_wellFormed
#print axioms pushFront_run
#print axioms pushAt_wellFormed
#print axioms popAt_wellFormed
#print axioms clearAt_wellFormed
#print axioms pushAt_run
#print axioms popAt_run
#print axioms clearAt_run
#print axioms pushAt_raw_run
#print axioms popAt_raw_run
#print axioms clearAt_raw_run
#print axioms pushAtSteps_le
#print axioms popAtSteps_le
#print axioms clearAtSteps_le
