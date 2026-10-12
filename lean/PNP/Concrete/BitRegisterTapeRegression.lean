import PNP.Concrete.BitRegisterTape

open PNP.Concrete
open PNP.Concrete.BitRegister
open PNP.Concrete.BitRegister.TapePrimitive

example : workRunExact? skip 1 ⟨0, focus [] [Store.separator]⟩ =
    some ⟨1, focus [Store.separator] []⟩ := rfl
example : workRunExact? skip 2
    ⟨0, focus [] [Store.bitSymbol true, Store.separator]⟩ =
    some ⟨1, focus [Store.separator, Store.bitSymbol true] []⟩ := rfl
example : workRunExact? skip 3
    ⟨0, focus [] [Store.bitSymbol false, Store.bitSymbol true, Store.separator]⟩ =
    some ⟨1, focus [Store.separator, Store.bitSymbol true, Store.bitSymbol false] []⟩ := rfl
example : workRunExact? skip 0 ⟨0, focus [] [Store.separator]⟩ =
    some ⟨0, focus [] [Store.separator]⟩ := rfl
example : workRunExact? skip 2 ⟨0, focus [] [Store.separator]⟩ = none := rfl
example : workStep? skip ⟨0, focus [] [WorkSymbol.zeroZero]⟩ = none := rfl
example : workRunExact? rewind 2
    ⟨0, { left := [WorkSymbol.blankZero], head := Store.separator, right := [WorkSymbol.zeroZero] }⟩ =
    some ⟨1, { left := [], head := WorkSymbol.blankZero, right := [Store.separator, WorkSymbol.zeroZero] }⟩ := rfl
example : workRunExact? rewind 3
    ⟨0, { left := [Store.bitSymbol false, WorkSymbol.blankZero], head := Store.bitSymbol true, right := [Store.separator] }⟩ =
    some ⟨1, { left := [], head := WorkSymbol.blankZero, right := [Store.bitSymbol false, Store.bitSymbol true, Store.separator] }⟩ := rfl
example : workStep? rewind ⟨0, focus [] [WorkSymbol.zeroZero]⟩ = none := rfl
example : workStep? headBit ⟨0, focus [] [Store.separator]⟩ = none := rfl
example : workRunExact? isEmpty 1 ⟨0, focus [] [Store.separator]⟩ =
    some ⟨1, focus [] [Store.separator]⟩ := rfl
example : workRunExact? headBit 1 ⟨0, focus [] [Store.bitSymbol false]⟩ =
    some ⟨2, focus [] [Store.bitSymbol false]⟩ := rfl

#print axioms skip_bit_step
#print axioms skip_separator_step
#print axioms skip_run
#print axioms skip_raw_run
#print axioms bitWord_data
#print axioms store_data
#print axioms rewind_symbol_step
#print axioms rewind_run
#print axioms rewind_raw_run
#print axioms isEmpty_run
#print axioms headBit_run
