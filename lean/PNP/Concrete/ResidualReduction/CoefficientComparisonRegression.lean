import PNP.Concrete.ResidualReduction.CoefficientComparison

namespace PNP.Concrete.ResidualReduction.CoefficientComparison.Regression
open PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction

example : compareCarry [] [] true = true := rfl
example : compareCarry [] [] false = false := rfl
example : compareCarry [true, false] [false, true] true = true := rfl
example : compareCarry [false, true] [true, false] true = false := rfl
example : compareCarry [true, false, false] [true] true = true := rfl
example : compareCarry [] [false, false, true] false = true := rfl
example : compareCarry [true] [] true = false := rfl
example : normalBits (n := 0) true = normalBits (n := 0) false := rfl
example : normalBits (n := 2) (true, false, true) = [true, false] := rfl

example : (BitRegister.run program (fuel [] [] + 1)
    ⟨.running 0, store [] [] false⟩).store.get 2 = [true] := rfl
example : (BitRegister.run program (fuel [true, false] [false, true] + 1)
    ⟨.running 0, store [true, false] [false, true] false⟩).store.get 2 = [true] := rfl
example : (BitRegister.run program (fuel [true] [] + 1)
    ⟨.running 0, store [true] [] true⟩).store.get 2 = [false] := rfl

example (xs ys : BitString) (initial : Bool) :
    Exec comparison (store xs ys initial) (fuel xs ys)
      (store [] [] (decide (binaryValue xs ≤ binaryValue ys))) :=
  comparison_exec xs ys initial

example (xs ys : BitString) : fuel xs ys ≤ 7 * (xs.length + ys.length) + 4 :=
  fuel_bound xs ys

example {n : Nat} (a b : Affine n) : fuel (normalBits a) (normalBits b) ≤ 14 * n + 4 :=
  normal_fuel_bound a b

end PNP.Concrete.ResidualReduction.CoefficientComparison.Regression
