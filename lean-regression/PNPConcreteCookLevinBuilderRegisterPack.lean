/-
Copyright (c) 2026 PNP Labs.
Fixed packs must copy the intended original registers, preserve their frame,
append consecutive fields and charge every final identity-chain handoff.
-/
import PNP.Concrete.CookLevinBuilderRegisterPack

namespace PNP.Concrete.CookLevin.BuilderRegisterPack.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def two (first second : Nat) : Fin 2 → Nat :=
  fun index => if index.val = 0 then first else second

private def swapped : List (Field 2) :=
  [.argument ⟨1, by decide⟩, .argument ⟨0, by decide⟩]
private def repeated : List (Field 2) :=
  [.argument ⟨1, by decide⟩, .constant 0, .argument ⟨1, by decide⟩]
private def mixed : List (Field 2) :=
  [.constant 0, .argument ⟨1, by decide⟩]

example : values swapped (two 2 5) = [5, 2] := rfl
example : values swapped (two 5 2) = [2, 5] := rfl
example : values swapped (two 2 5) ≠ values swapped (two 5 2) := by decide
example : values repeated (two 2 5) = [5, 0, 5] := rfl
example : values mixed (two 2 5) = [0, 5] := rfl
example : values ([] : List (Field 2)) (two 2 5) = [] := rfl
example : values ([.constant 0, .constant 2] : List (Field 0)) Fin.elim0 = [0, 2] := rfl
example : workSteps ([] : List (Field 0)) Fin.elim0 [] = 0 := rfl
example : workSteps ([.constant 0] : List (Field 0)) Fin.elim0 [] = 3 := rfl
example : workSteps ([.constant 0, .constant 2] : List (Field 0)) Fin.elim0 [] = 10 := rfl
example : (BuilderRegisterPack.machine ([] : List (Field 0)) 4).rules = [] := rfl
example : (BuilderRegisterPack.machine ([] : List (Field 0)) 4).acceptState = 0 := rfl
example : (BuilderRegisterPack.machine ([] : List (Field 0)) 4).rejectState = 1 := rfl
example : spanPolynomial ([] : List (Field 0)) (.constant 7) = .constant 7 := rfl
example : (spanPolynomial ([.constant 0, .constant 2] : List (Field 0)) (.constant 7)).eval 0 = 11 := rfl
example : (rawTimePolynomial ([.constant 0, .constant 2] : List (Field 0)) (.constant 7)).eval 0 = 60 := rfl
example : (spanPolynomial swapped (.constant 7)).eval 0 = 31 := rfl

example : workRunExact? (BuilderRegisterPack.machine ([] : List (Field 0)) 0) 0
    (initialConfiguration [] 0 [] Fin.elim0 [] [] []) =
      some (finalConfiguration [] 0 [] Fin.elim0 [] [] []) := rfl
example : workRunExact? (BuilderRegisterPack.machine ([.constant 0] : List (Field 0)) 0) 3
    (initialConfiguration [.constant 0] 0 [] Fin.elim0 [] [] []) =
      some (finalConfiguration [.constant 0] 0 [] Fin.elim0 [] [] []) := rfl
set_option maxRecDepth 4096 in
example : workRunExact? (BuilderRegisterPack.machine ([.constant 0, .constant 1] : List (Field 0)) 0) 8
    (initialConfiguration [.constant 0, .constant 1] 0 [] Fin.elim0 [] [] []) =
      some (finalConfiguration [.constant 0, .constant 1] 0 [] Fin.elim0 [] [] []) := rfl
set_option maxRecDepth 8192 in
example : workRunExact? (BuilderRegisterPack.machine mixed 0) (workSteps mixed (two 0 1) [])
    (initialConfiguration mixed 0 [] (two 0 1) [] [] []) =
      some (finalConfiguration mixed 0 [] (two 0 1) [] [] []) := rfl
set_option maxRecDepth 8192 in
example : workRunExact? (BuilderRegisterPack.machine swapped 0) (workSteps swapped (two 0 1) [])
    (initialConfiguration swapped 0 [] (two 0 1) [] [] []) =
      some (finalConfiguration swapped 0 [] (two 0 1) [] [] []) := rfl

example (older after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration swapped after.length older (two 2 5) after inside outside).tape =
      endTape (older ++ [2, 5] ++ after ++ [5, 2]) inside (outside.drop 9) := rfl
example (older after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration repeated after.length older (two 2 5) after inside outside).tape =
      endTape (older ++ [2, 5] ++ after ++ [5, 0, 5]) inside (outside.drop 13) := rfl

example {arity : Nat} (field : Field arity) (environment : Fin arity → Nat) :
    BuilderRegisterExpression.values field.expression environment = [field.eval environment] :=
  field.expression_values environment
example {arity : Nat} (fields : List (Field arity)) (environment : Fin arity → Nat) :
    (values fields environment).length = fields.length := values_length fields environment
example {arity count : Nat} (fields : Fin count → Field arity) (environment : Fin arity → Nat) :
    values (List.ofFn fields) environment = List.ofFn (fun i => (fields i).eval environment) :=
  values_ofFn fields environment
example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    workRunExact? (BuilderRegisterPack.machine fields afterCount) (workSteps fields environment after)
      (initialConfiguration fields afterCount older environment after inside outside) =
      some (finalConfiguration fields afterCount older environment after inside outside) :=
  workRunExact fields afterCount older environment after inside outside hAfter
example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    run (compileWorkMachine (BuilderRegisterPack.machine fields afterCount)) (6 * workSteps fields environment after)
      (encodeWorkConfiguration (initialConfiguration fields afterCount older environment after inside outside)) =
      encodeWorkConfiguration (finalConfiguration fields afterCount older environment after inside outside) :=
  run_compile_exact fields afterCount older environment after inside outside hAfter
example {arity : Nat} (fields : List (Field arity)) (bound : NatPolynomial) (inputLength : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values fields environment)).length ≤
        (spanPolynomial fields bound).eval inputLength ∧
      6 * workSteps fields environment after ≤ (rawTimePolynomial fields bound).eval inputLength :=
  source_polynomial_bounds fields bound inputLength older environment after hSpan
example (older after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine repeated after.length) (workSteps repeated (two 2 5) after)
      (initialConfiguration repeated after.length older (two 2 5) after inside outside) =
      some (finalConfiguration repeated after.length older (two 2 5) after inside outside) :=
  workRunExact repeated after.length older (two 2 5) after inside outside rfl

example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    (BuilderRegisterPack.machine fields afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct fields afterCount
example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (BuilderRegisterPack.machine fields afterCount) := noRuleAtAccept fields afterCount
example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (BuilderRegisterPack.machine fields afterCount)
      (BuilderRegisterPack.machine fields afterCount).rejectState := noRuleAtReject fields afterCount
example {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    (BuilderRegisterPack.machine fields afterCount).acceptState ≠
      (BuilderRegisterPack.machine fields afterCount).rejectState := acceptState_ne_rejectState fields afterCount

end PNP.Concrete.CookLevin.BuilderRegisterPack.Regression
