/-
Copyright (c) 2026 PNP Labs.
Fixed register-expression programs must read their environment, preserve it,
write the ordered postorder result, and charge all runtime scratch and work.
-/
import PNP.Concrete.CookLevinBuilderRegisterExpression

namespace PNP.Concrete.CookLevin.BuilderRegisterExpression.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def two (first second : Nat) : Fin 2 → Nat :=
  fun index => if index.val = 0 then first else second

private def addArguments : Expr 2 :=
  .binary .add (.argument ⟨0, by decide⟩) (.argument ⟨1, by decide⟩)

private def weightedArguments : Expr 2 :=
  .binary .add (.binary .mul (.argument ⟨0, by decide⟩) (.constant 3))
    (.argument ⟨1, by decide⟩)

example : eval addArguments (two 2 3) = 5 := rfl
example : values addArguments (two 2 3) = [2, 3, 5] := rfl
example : prefixValues addArguments (two 2 3) = [2, 3] := rfl
example : nodeCount addArguments = 3 := rfl
example : eval weightedArguments (two 2 4) = 10 := rfl
example : eval weightedArguments (two 4 2) = 14 := rfl
example : values weightedArguments (two 2 4) = [2, 3, 6, 4, 10] := rfl
example : nodeCount weightedArguments = 5 := rfl
example : eval weightedArguments (two 2 4) ≠ eval weightedArguments (two 4 2) := by decide
example : eval (.binary .mul (.argument ⟨0, by decide⟩) (.argument ⟨1, by decide⟩))
    (two 0 7) = 0 := rfl

example {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    values expression environment = prefixValues expression environment ++ [eval expression environment] :=
  values_root expression environment
example {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    (values expression environment).length = nodeCount expression := values_length expression environment
example {arity : Nat} (expression : Expr arity) : 0 < nodeCount expression := nodeCount_positive expression
example {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    (prefixValues expression environment).length = nodeCount expression - 1 :=
  prefixValues_length expression environment

example {arity : Nat} (expression : Expr arity) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    workRunExact? (BuilderRegisterExpression.machine expression afterCount)
      (workSteps expression environment after)
      (initialConfiguration expression afterCount older environment after inside outside) =
      some (finalConfiguration expression afterCount older environment after inside outside) :=
  workRunExact expression afterCount older environment after inside outside hAfter
example {arity : Nat} (expression : Expr arity) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    run (compileWorkMachine (BuilderRegisterExpression.machine expression afterCount))
      (6 * workSteps expression environment after)
      (encodeWorkConfiguration (initialConfiguration expression afterCount older environment after inside outside)) =
      encodeWorkConfiguration (finalConfiguration expression afterCount older environment after inside outside) :=
  run_compile_exact expression afterCount older environment after inside outside hAfter

example (older after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterExpression.machine weightedArguments after.length)
      (workSteps weightedArguments (two 2 4) after)
      (initialConfiguration weightedArguments after.length older (two 2 4) after inside outside) =
      some (finalConfiguration weightedArguments after.length older (two 2 4) after inside outside) :=
  workRunExact weightedArguments after.length older (two 2 4) after inside outside rfl

example : workRunExact? (BuilderRegisterExpression.machine (.constant 0 : Expr 0) 0) 2
    (initialConfiguration (.constant 0) 0 [] Fin.elim0 [] [] []) =
      some (finalConfiguration (.constant 0) 0 [] Fin.elim0 [] [] []) := by rfl
example : workRunExact? (BuilderRegisterExpression.machine (.argument ⟨0, by decide⟩ : Expr 2) 0)
    (workSteps (.argument ⟨0, by decide⟩) (two 0 1) [])
    (initialConfiguration (.argument ⟨0, by decide⟩) 0 [] (two 0 1) [] [] []) =
      some (finalConfiguration (.argument ⟨0, by decide⟩) 0 [] (two 0 1) [] [] []) := by rfl
example : workRunExact? (BuilderRegisterExpression.machine (.argument ⟨1, by decide⟩ : Expr 2) 0)
    (workSteps (.argument ⟨1, by decide⟩) (two 0 1) [])
    (initialConfiguration (.argument ⟨1, by decide⟩) 0 [] (two 0 1) [] [] []) =
      some (finalConfiguration (.argument ⟨1, by decide⟩) 0 [] (two 0 1) [] [] []) := by rfl

set_option maxRecDepth 4096 in
example : workRunExact? (BuilderRegisterExpression.machine addArguments 0)
    (workSteps addArguments (two 0 1) [])
    (initialConfiguration addArguments 0 [] (two 0 1) [] [] []) =
      some (finalConfiguration addArguments 0 [] (two 0 1) [] [] []) := by rfl

example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration addArguments 1 older (two 2 3) [4] inside outside).tape =
      endTape (older ++ [2, 3, 4, 2, 3, 5]) inside (outside.drop 13) := by
  change endTape ((older ++ [2, 3]) ++ [4] ++ [2, 3, 5]) inside (outside.drop 13) = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]

example {arity : Nat} (expression : Expr arity) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values expression environment)).length ≤
        spanBound expression bound ∧ workSteps expression environment after ≤ timeBound expression bound :=
  space_time_bounds expression older environment after bound hSpan
example {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial expression bound).eval input = spanBound expression (bound.eval input) :=
  spanPolynomial_eval expression bound input
example {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) (input : Nat) :
    (timePolynomial expression bound).eval input = timeBound expression (bound.eval input) :=
  timePolynomial_eval expression bound input
example {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) (inputLength : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values expression environment)).length ≤
        (spanPolynomial expression bound).eval inputLength ∧
      6 * workSteps expression environment after ≤ (rawTimePolynomial expression bound).eval inputLength :=
  source_polynomial_bounds expression bound inputLength older environment after hSpan

example {arity : Nat} (expression : Expr arity) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expression afterCount older environment after inside outside).tape =
      endTape (older ++ List.ofFn environment ++ after ++ values expression environment)
        inside (outside.drop (registerWord (values expression environment)).length) :=
  final_tape expression afterCount older environment after inside outside
example {arity : Nat} (expression : Expr arity) (afterCount : Nat) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expression afterCount older environment after inside outside).tape =
      endTape ((older ++ List.ofFn environment ++ after ++ prefixValues expression environment) ++
        [eval expression environment]) inside (outside.drop (registerWord (values expression environment)).length) :=
  final_root_register expression afterCount older environment after inside outside

example {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    (BuilderRegisterExpression.machine expression afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct expression afterCount
example {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (BuilderRegisterExpression.machine expression afterCount) :=
  noRuleAtAccept expression afterCount
example {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (BuilderRegisterExpression.machine expression afterCount)
      (BuilderRegisterExpression.machine expression afterCount).rejectState := noRuleAtReject expression afterCount
example {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    (BuilderRegisterExpression.machine expression afterCount).acceptState ≠
      (BuilderRegisterExpression.machine expression afterCount).rejectState := acceptState_ne_rejectState expression afterCount

example : workRunExact? (BuilderRegisterExpression.machine addArguments 0) 2
    (workStartConfiguration (BuilderRegisterExpression.machine addArguments 0)
      { left := [], head := .blank, right := [] }) = none := by rfl

end PNP.Concrete.CookLevin.BuilderRegisterExpression.Regression
