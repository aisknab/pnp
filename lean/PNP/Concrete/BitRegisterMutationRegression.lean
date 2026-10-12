import PNP.Concrete.BitRegisterMutation

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.TapePrimitive
open PNP.Concrete.BitRegister.Mutation

example : (insert false).rules.length = 42 := rfl
example : eraseCell.rules.length = 24 := rfl

example : workRunExact? (insert true) 5
    ⟨0, focus [WorkSymbol.blankZero] [Store.separator, rightBoundary]⟩ =
    some ⟨1, focus [WorkSymbol.blankZero]
      [Store.bitSymbol true, Store.separator, rightBoundary]⟩ := rfl

example : workRunExact? (insert false) 5
    ⟨0, focus [WorkSymbol.blankZero] [Store.separator, rightBoundary, WorkSymbol.blank]⟩ =
    some ⟨1, focus [WorkSymbol.blankZero]
      [Store.bitSymbol false, Store.separator, rightBoundary]⟩ := rfl

example : workRunExact? (insert true) 5
    ⟨0, focus [WorkSymbol.blankZero]
      [Store.separator, rightBoundary, WorkSymbol.blank, WorkSymbol.blank]⟩ =
    some ⟨1, focus [WorkSymbol.blankZero]
      [Store.bitSymbol true, Store.separator, rightBoundary, WorkSymbol.blank]⟩ := rfl

example : workRunExact? (insert false) 7
    ⟨0, focus [Store.separator, WorkSymbol.blankZero]
      [WorkSymbol.zeroOne, Store.separator, rightBoundary]⟩ =
    some ⟨1, focus [Store.separator, WorkSymbol.blankZero]
      [Store.bitSymbol false, WorkSymbol.zeroOne, Store.separator, rightBoundary]⟩ := rfl

example : workRunExact? (insert true) 7
    ⟨0, focus [WorkSymbol.blankZero]
      [WorkSymbol.oneOne, Store.separator, rightBoundary]⟩ =
    some ⟨1, focus [WorkSymbol.blankZero]
      [Store.bitSymbol true, WorkSymbol.oneOne, Store.separator, rightBoundary]⟩ := rfl

example : workStep? (insert true) ⟨0, focus [] [rightBoundary]⟩ = none := rfl
example : workStep? (insert false) ⟨0, focus [] [anchor]⟩ = none := rfl

example : workRunExact? eraseCell 8
    ⟨0, focus [WorkSymbol.blankZero]
      [Store.bitSymbol true, Store.separator, rightBoundary]⟩ =
    some ⟨1, ⟨[], WorkSymbol.blankZero,
      [Store.separator, rightBoundary, WorkSymbol.blank]⟩⟩ := rfl

example : workRunExact? eraseCell 9
    ⟨0, focus [Store.separator, WorkSymbol.blankZero]
      [Store.bitSymbol false, Store.separator, rightBoundary]⟩ =
    some ⟨1, ⟨[], WorkSymbol.blankZero,
      [Store.separator, Store.separator, rightBoundary, WorkSymbol.blank]⟩⟩ := rfl

example : workRunExact? eraseCell 8
    ⟨0, focus [WorkSymbol.blankZero]
      [Store.bitSymbol false, Store.separator, rightBoundary, WorkSymbol.blank]⟩ =
    some ⟨1, ⟨[], WorkSymbol.blankZero,
      [Store.separator, rightBoundary, WorkSymbol.blank, WorkSymbol.blank]⟩⟩ := rfl

example : workStep? eraseCell ⟨0, focus [] [WorkSymbol.blankZero]⟩ = none := rfl

#print axioms exact_one
#print axioms traverse_left
#print axioms insert_initial_step
#print axioms insert_carry_step
#print axioms insert_finish_carry
#print axioms insert_drain
#print axioms insert_return_step
#print axioms insert_return
#print axioms insert_stop
#print axioms insert_run
#print axioms insert_raw_run
#print axioms erase_initial_step
#print axioms erase_shift_three
#print axioms erase_finish_shift
#print axioms erase_drain
#print axioms erase_return_step
#print axioms erase_return
#print axioms erase_stop
#print axioms erase_run
#print axioms erase_raw_run
