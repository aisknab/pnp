import PNP.Concrete.BitRegisterOperations

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Mutation
open PNP.Concrete.BitRegister.Operation

example : workRunExact? pop 5 ⟨pop.startState, cursor [] [] [] [] 0⟩ =
    some ⟨pop.acceptState, atBoundary [] [] [] [] 0⟩ :=
  pop_run [] [] [] [] 0
example : workRunExact? pop 6 ⟨pop.startState, cursor [[]] [] [] [] 2⟩ =
    some ⟨pop.acceptState, atBoundary [[]] [] [] [] 2⟩ :=
  pop_run [[]] [] [] [] 2
example : workRunExact? pop 11 ⟨pop.startState, cursor [] [true] [] [] 0⟩ =
    some ⟨pop.acceptState, atBoundary [] [] [] [] 1⟩ :=
  pop_run [] [true] [] [] 0
example : workRunExact? pop 12 ⟨pop.startState, cursor [[]] [false] [] [] 0⟩ =
    some ⟨pop.acceptState, atBoundary [[]] [] [] [] 1⟩ :=
  pop_run [[]] [false] [] [] 0
example : workRunExact? pop 23 ⟨pop.startState, cursor [] [false, true] [.markedZero, .markedOne] [] 3⟩ =
    some ⟨pop.acceptState, atBoundary [] [true] [.markedZero, .markedOne] [] 4⟩ :=
  pop_run [] [false, true] [.markedZero, .markedOne] [] 3

example : workRunExact? (seek 0) 0
    ⟨(seek 0).startState, TapePrimitive.focus [] [Store.separator]⟩ =
    some ⟨(seek 0).acceptState, TapePrimitive.focus [] [Store.separator]⟩ :=
  seek_run [] [] [Store.separator]
example : workRunExact? (seek 1) 2
    ⟨(seek 1).startState, TapePrimitive.focus [] [Store.separator, rightBoundary]⟩ =
    some ⟨(seek 1).acceptState, TapePrimitive.focus [Store.separator] [rightBoundary]⟩ :=
  seek_run [[]] [] [rightBoundary]
example : workRunExact? (seek 1) 4
    ⟨(seek 1).startState, TapePrimitive.focus []
      [Store.bitSymbol false, Store.bitSymbol true, Store.separator, rightBoundary]⟩ =
    some ⟨(seek 1).acceptState, TapePrimitive.focus
      [Store.separator, Store.bitSymbol true, Store.bitSymbol false] [rightBoundary]⟩ :=
  seek_run [[false, true]] [] [rightBoundary]
example : workStep? pop ⟨pop.startState, TapePrimitive.focus [] [rightBoundary]⟩ = none := by
  rfl

#print axioms bitCells_length
#print axioms bitCells_symbols
#print axioms fieldWord_cons
#print axioms reverseOnto_append
#print axioms chain_wellFormed
#print axioms seek_wellFormed
#print axioms seek_run
#print axioms enter_run
#print axioms seekFromBoundary_wellFormed
#print axioms seekFromBoundary_run
#print axioms home_wellFormed
#print axioms home_run
#print axioms popGraph_wellFormed
#print axioms pop_empty_run
#print axioms erase_register_run
#print axioms pop_nonempty_run
#print axioms pop_run
#print axioms pop_raw_run
