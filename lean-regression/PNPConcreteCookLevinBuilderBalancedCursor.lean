import PNP.Concrete.CookLevinBuilderBalancedCursor

namespace PNP.Concrete.CookLevinBuilderBalancedCursorRegression

open CookLevin CookLevin.BuilderBalancedCursor

example : rules.length = 18 := rfl
example : machine.acceptState ≠ machine.rejectState := by decide
example : steps 0 0 0 = 8 := rfl
example : steps 0 0 1 = 12 := rfl
example : steps 0 2 3 = 20 := rfl

-- Literal execution checks include zero, one and multiple remaining units.
example : workRunExact? machine 8 (initialConfiguration .blank [] [] 0 0 []) =
    some (exhaustedConfiguration .blank [] [] 0 []) := by decide
example : workRunExact? machine 12 (initialConfiguration .blank [] [] 0 1 []) =
    some (advancedConfiguration .blank [] [] 0 0 []) := by decide
example : workRunExact? machine 20 (initialConfiguration .oneBlank [.zeroBlank] [] 2 3
    [unitSymbol, endSymbol, separatorSymbol]) =
    some (advancedConfiguration .oneBlank [.zeroBlank] [] 2 2
      [unitSymbol, endSymbol, separatorSymbol]) := by decide

example : workStep? machine (initialConfiguration unitSymbol [] [] 0 1 []) = none := by decide
example : workRunExact? machine 20 (initialConfiguration .blank [] [.blank] 0 1 []) = none := by decide

example (wordPrefix : List WorkSymbol) (index remaining : Nat) :
    (word wordPrefix index (remaining + 1)).length =
      (word wordPrefix (index + 1) remaining).length ∧
    index + (remaining + 1) = (index + 1) + remaining :=
  balanced_span wordPrefix index remaining

example (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index remaining : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    workRunExact? machine (steps wordPrefix.length index (remaining + 1))
        (initialConfiguration head sourceTail wordPrefix index (remaining + 1) tail) =
      some (advancedConfiguration head sourceTail wordPrefix index remaining tail) :=
  advance_workRunExact head sourceTail wordPrefix index remaining tail hHead hPrefix

example (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    workRunExact? machine (steps wordPrefix.length index 0)
        (initialConfiguration head sourceTail wordPrefix index 0 tail) =
      some (exhaustedConfiguration head sourceTail wordPrefix index tail) :=
  exhausted_workRunExact head sourceTail wordPrefix index tail hHead hPrefix

example (prefixLength index remaining : Nat) :
    6 * steps prefixLength index remaining ≤ 12 * (prefixLength + index + remaining + 2) + 36 :=
  compiled_steps_le prefixLength index remaining

end PNP.Concrete.CookLevinBuilderBalancedCursorRegression
