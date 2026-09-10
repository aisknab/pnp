import PNP.Concrete.CookLevinBuilderRegisterAccess

namespace PNP.Concrete.CookLevinBuilderRegisterAccessRegression

open CookLevin.BuilderUnaryPolynomial
  (unitSymbol separatorSymbol scratchEndSymbol registerMarkSymbol registerWord)
open CookLevin.BuilderRegisterAccess

example : seekRules.length = 7 := seekRules_length

example : (machine 0).rules.length = 106 := by decide

example : workStep? seekMachine
    { state := 2, tape := { left := [], head := WorkSymbol.blank, right := [] } } = none := by decide

example : workStep? seekMachine
    { state := 0, tape := { left := [], head := registerMarkSymbol, right := [] } } = none := by decide

example :
    workRunExact? seekMachine 3 (seekInitialConfiguration .blank [] [] [registerMarkSymbol]) =
      some (seekFinalConfiguration .blank [] [] [registerMarkSymbol]) := by decide

example (values : List Nat) :
    CookLevin.BuilderBalancedCursor.RegisterSymbols (registerWord values) :=
  registerWord_symbols values

example : workSteps [] 0 [] = 12 := by decide

example : workSteps [separatorSymbol, unitSymbol] 2 [0] = 49 := by decide

example :
    workRunExact? (machine 0) 12 (initialConfiguration .blank [] [] 0 [] []) =
      some (finalConfiguration .blank [] [] 0 [] []) := by decide

example :
    workRunExact? (machine 1) 49
        (initialConfiguration .oneBlank [registerMarkSymbol, scratchEndSymbol]
          [separatorSymbol, unitSymbol] 2 [0] [scratchEndSymbol, unitSymbol, registerMarkSymbol]) =
      some (finalConfiguration .oneBlank [registerMarkSymbol, scratchEndSymbol]
        [separatorSymbol, unitSymbol] 2 [0] [scratchEndSymbol, unitSymbol, registerMarkSymbol]) := by decide

example :
    (finalConfiguration .zeroBlank [registerMarkSymbol] [] 0 [] []).tape.right =
      (registerWord [0, 0]).reverse ++ [PipelineTape.leftMarker, WorkSymbol.zeroBlank,
        registerMarkSymbol] := rfl

example (newerCount : Nat) :
    (machine newerCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct newerCount

example (newerCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine newerCount) :=
  noRuleAtAccept newerCount

example (newerCount : Nat) : (machine newerCount).acceptState ≠ (machine newerCount).rejectState :=
  machine_acceptState_ne_rejectState newerCount

example (head : WorkSymbol) (sourceTail older : List WorkSymbol) (sourceValue : Nat)
    (newer : List Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hOlder : CookLevin.BuilderBalancedCursor.RegisterSymbols older) :
    workRunExact? (machine newer.length) (workSteps older sourceValue newer)
        (initialConfiguration head sourceTail older sourceValue newer tail) =
      some (finalConfiguration head sourceTail older sourceValue newer tail) :=
  workRunExact head sourceTail older sourceValue newer tail hHead hOlder

example (head : WorkSymbol) (sourceTail older : List WorkSymbol) (sourceValue : Nat)
    (newer : List Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hOlder : CookLevin.BuilderBalancedCursor.RegisterSymbols older) :
    run (compileWorkMachine (machine newer.length)) (6 * workSteps older sourceValue newer)
        (encodeWorkConfiguration (initialConfiguration head sourceTail older sourceValue newer tail)) =
      encodeWorkConfiguration (finalConfiguration head sourceTail older sourceValue newer tail) :=
  run_compile_exact head sourceTail older sourceValue newer tail hHead hOlder

example (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol) :
    (finalConfiguration head sourceTail older sourceValue newer tail).state =
      (machine newer.length).acceptState :=
  finalConfiguration_state head sourceTail older sourceValue newer tail

example (older : List WorkSymbol) (sourceValue : Nat) (newer : List Nat) (bound : Nat)
    (hSpan : (encodedWord older sourceValue newer).length ≤ bound) :
    workSteps older sourceValue newer ≤
      bound + 4 + (4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5) :=
  workSteps_le older sourceValue newer bound hSpan

end PNP.Concrete.CookLevinBuilderRegisterAccessRegression
