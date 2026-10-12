import PNP.Concrete.BitRegisterClear

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.Mutation
open PNP.Concrete.BitRegister.Operation

example : workRunExact? (clear 0) 5 ⟨(clear 0).startState, cursor [] [] [] [] 0⟩ =
    some ⟨(clear 0).acceptState, atBoundary [] [] [] [] 0⟩ :=
  clear_run [] [] [] [] 0
example : workRunExact? (clear 0) 19 ⟨(clear 0).startState, cursor [] [true] [] [] 0⟩ =
    some ⟨(clear 0).acceptState, atBoundary [] [] [] [] 1⟩ :=
  clear_run [] [true] [] [] 0
example : workRunExact? (clear 0) 37 ⟨(clear 0).startState, cursor [] [false, true] [] [] 0⟩ =
    some ⟨(clear 0).acceptState, atBoundary [] [] [] [] 2⟩ :=
  clear_run [] [false, true] [] [] 0
example : workRunExact? (clear 1) 23 ⟨(clear 1).startState, cursor [[]] [false] [] [] 2⟩ =
    some ⟨(clear 1).acceptState, atBoundary [[]] [] [] [] 3⟩ :=
  clear_run [[]] [false] [] [] 2
example : workRunExact? (clear 0) 53
    ⟨(clear 0).startState, cursor [] [false, true] [.markedZero, .markedOne] [WorkSymbol.oneOne] 3⟩ =
    some ⟨(clear 0).acceptState,
      atBoundary [] [] [.markedZero, .markedOne] [WorkSymbol.oneOne] 5⟩ :=
  clear_run [] [false, true] [.markedZero, .markedOne] [WorkSymbol.oneOne] 3

-- The same finite machine works for every input length and bit pattern.
example (bits : BitString) (slack : Nat) :
    workRunExact? (clear 1) (clearSteps [[false, true]] bits [.separator, .one])
      ⟨(clear 1).startState, cursor [[false, true]] bits [.separator, .one] [] slack⟩ =
    some ⟨(clear 1).acceptState,
      atBoundary [[false, true]] [] [.separator, .one] [] (slack + bits.length)⟩ :=
  clear_run [[false, true]] bits [.separator, .one] [] slack
example (before : List BitString) (bits : BitString) (after : List Cell) :
    clearSteps before bits after ≤
      9 * bankSpan before bits after * bankSpan before bits after +
        13 * bankSpan before bits after + 5 :=
  clearSteps_le_polynomial before bits after

-- A right boundary is not a valid register delimiter.
example : workStep? (clear 0)
    ⟨(clear 0).startState, TapePrimitive.focus [] [rightBoundary]⟩ = none := by rfl

#print axioms clearGraph_wellFormed
#print axioms clear_wellFormed
#print axioms clear_empty_run
#print axioms clear_iteration
#print axioms clear_run
#print axioms clear_raw_run
#print axioms clearSteps_eq
#print axioms fieldCells_length_ge
#print axioms clearSteps_le_polynomial
#print axioms clearRawSteps_le_polynomial
