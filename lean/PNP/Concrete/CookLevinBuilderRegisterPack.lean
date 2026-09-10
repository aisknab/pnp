/-
Copyright (c) 2026 PNP Labs.

Pack fixed constant/register references into consecutive argument registers.
Each field uses the existing one-register expression compiler; no runtime
value chooses control or becomes a supplied answer. The original frame and
arbitrary inside/exterior data are preserved, with exact exterior allocation.
-/

import PNP.Concrete.CookLevinBuilderRegisterExpression

namespace PNP.Concrete.CookLevin.BuilderRegisterPack

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

inductive Field (arity : Nat) where
  | constant (value : Nat)
  | argument (index : Fin arity)
  deriving Repr

namespace Field

def expression {arity : Nat} : Field arity → BuilderRegisterExpression.Expr arity
  | .constant value => .constant value
  | .argument index => .argument index

def eval {arity : Nat} (field : Field arity) (environment : Fin arity → Nat) : Nat :=
  BuilderRegisterExpression.eval field.expression environment

theorem expression_values {arity : Nat} (field : Field arity) (environment : Fin arity → Nat) :
    BuilderRegisterExpression.values field.expression environment = [field.eval environment] := by
  cases field <;> rfl

end Field

def doneMachine : WorkMachine :=
  { rules := [], startState := 0, acceptState := 0, rejectState := 1 }

def machine {arity : Nat} : List (Field arity) → Nat → WorkMachine
  | [], _ => doneMachine
  | field :: rest, afterCount =>
      WorkMachineChain.machine (BuilderRegisterExpression.machine field.expression afterCount)
        (machine rest (afterCount + 1))

def values {arity : Nat} (fields : List (Field arity)) (environment : Fin arity → Nat) : List Nat :=
  fields.map (fun field => field.eval environment)

theorem values_length {arity : Nat} (fields : List (Field arity)) (environment : Fin arity → Nat) :
    (values fields environment).length = fields.length := by
  simp only [values, List.length_map]

theorem values_ofFn {arity count : Nat} (fields : Fin count → Field arity) (environment : Fin arity → Nat) :
    values (List.ofFn fields) environment = List.ofFn (fun index => (fields index).eval environment) := by
  simp only [values, List.map_ofFn, Function.comp_def]

def workSteps {arity : Nat} : List (Field arity) → (Fin arity → Nat) → List Nat → Nat
  | [], _, _ => 0
  | field :: rest, environment, after =>
      BuilderRegisterExpression.workSteps field.expression environment after + 1 +
        workSteps rest environment (after ++ [field.eval environment])

def initialConfiguration {arity : Nat} (fields : List (Field arity)) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine fields afterCount)
    (endTape (older ++ List.ofFn environment ++ after) inside outsideTail)

def finalConfiguration {arity : Nat} (fields : List (Field arity)) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  { state := (machine fields afterCount).acceptState
    tape := endTape (older ++ List.ofFn environment ++ after ++ values fields environment)
      inside (outsideTail.drop (registerWord (values fields environment)).length) }

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem workRunExact {arity : Nat} (fields : List (Field arity)) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine fields afterCount) (workSteps fields environment after)
      (initialConfiguration fields afterCount older environment after inside outsideTail) =
      some (finalConfiguration fields afterCount older environment after inside outsideTail) := by
  induction fields generalizing afterCount after outsideTail with
  | nil =>
      simp only [machine, workSteps, values, List.map_nil, List.append_nil, registerWord,
        List.length_nil, List.drop_zero, initialConfiguration, finalConfiguration,
        doneMachine, workStartConfiguration, workRunExact?]
  | cons field rest ih =>
      have hFirst := BuilderRegisterExpression.workRunExact field.expression afterCount
        older environment after inside outsideTail hAfter
      simp only [BuilderRegisterExpression.initialConfiguration,
        BuilderRegisterExpression.finalConfiguration, field.expression_values] at hFirst
      have hCount : (after ++ [field.eval environment]).length = afterCount + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil, hAfter]
      have hNext := ih (afterCount + 1) (after ++ [field.eval environment])
        (outsideTail.drop (registerWord [field.eval environment]).length) hCount
      simp only [initialConfiguration, finalConfiguration, List.append_assoc] at hNext
      simp only [List.append_assoc] at hFirst
      have hDrop :
          (outsideTail.drop (registerWord [field.eval environment]).length).drop
              (registerWord (values rest environment)).length =
            outsideTail.drop (registerWord (values (field :: rest) environment)).length := by
        rw [List.drop_drop]
        change outsideTail.drop _ =
          outsideTail.drop (registerWord ([field.eval environment] ++ values rest environment)).length
        rw [registerWord_append, List.length_append]
      rw [hDrop] at hNext
      have h := chain_run (BuilderRegisterExpression.machine field.expression afterCount)
        (machine rest (afterCount + 1))
        (BuilderRegisterExpression.workSteps field.expression environment after)
        (workSteps rest environment (after ++ [field.eval environment])) _ _ _ hFirst hNext
      simpa only [machine, workSteps, initialConfiguration, finalConfiguration, values,
        List.map_cons, List.cons_append, List.nil_append, List.append_assoc,
        List.drop_drop, registerWord_append, List.length_append] using h

theorem run_compile_exact {arity : Nat} (fields : List (Field arity)) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine fields afterCount)) (6 * workSteps fields environment after)
      (encodeWorkConfiguration (initialConfiguration fields afterCount older environment after inside outsideTail)) =
      encodeWorkConfiguration (finalConfiguration fields afterCount older environment after inside outsideTail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact fields afterCount older environment after inside outsideTail hAfter)

def spanPolynomial {arity : Nat} : List (Field arity) → NatPolynomial → NatPolynomial
  | [], bound => bound
  | field :: rest, bound =>
      spanPolynomial rest (BuilderRegisterExpression.spanPolynomial field.expression bound)

def rawTimePolynomial {arity : Nat} : List (Field arity) → NatPolynomial → NatPolynomial
  | [], _ => .constant 0
  | field :: rest, bound =>
      .add (.add (BuilderRegisterExpression.rawTimePolynomial field.expression bound) (.constant 6))
        (rawTimePolynomial rest (BuilderRegisterExpression.spanPolynomial field.expression bound))

theorem source_polynomial_bounds {arity : Nat} (fields : List (Field arity)) (bound : NatPolynomial)
    (inputLength : Nat) (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values fields environment)).length ≤
        (spanPolynomial fields bound).eval inputLength ∧
      6 * workSteps fields environment after ≤ (rawTimePolynomial fields bound).eval inputLength := by
  induction fields generalizing bound after with
  | nil =>
      simpa only [values, List.map_nil, List.append_nil, spanPolynomial, rawTimePolynomial,
        workSteps, Nat.mul_zero, NatPolynomial.eval_constant] using And.intro hSpan (Nat.le_refl 0)
  | cons field rest ih =>
      have hFirst := BuilderRegisterExpression.source_polynomial_bounds field.expression
        bound inputLength older environment after hSpan
      rw [field.expression_values] at hFirst
      have hNextSpan :
          (registerWord (older ++ List.ofFn environment ++ (after ++ [field.eval environment]))).length ≤
            (BuilderRegisterExpression.spanPolynomial field.expression bound).eval inputLength := by
        simpa only [List.append_assoc] using hFirst.1
      have hNext := ih (BuilderRegisterExpression.spanPolynomial field.expression bound)
        (after ++ [field.eval environment]) hNextSpan
      constructor
      · simpa only [spanPolynomial, values, List.map_cons, List.append_assoc,
          List.cons_append, List.nil_append] using hNext.1
      · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem good {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    Good (machine fields afterCount) := by
  induction fields generalizing afterCount with
  | nil =>
      change Good doneMachine
      refine ⟨List.Pairwise.nil, ?_, ?_, by decide⟩
      · intro rule hMem; cases hMem
      · intro rule hMem; cases hMem
  | cons field rest ih =>
      have hNext := ih (afterCount + 1)
      exact ⟨WorkMachineChain.rules_pairwise_query_distinct _ _
          (BuilderRegisterExpression.rules_pairwise_query_distinct field.expression afterCount)
          hNext.1 (BuilderRegisterExpression.noRuleAtAccept field.expression afterCount),
        WorkMachineChain.noRuleAtAccept _ _ hNext.2.1,
        WorkMachineChain.noRuleAtAccept (BuilderRegisterExpression.machine field.expression afterCount)
          { machine rest (afterCount + 1) with acceptState := (machine rest (afterCount + 1)).rejectState } hNext.2.2.1,
        WorkMachineChain.machine_acceptState_ne_rejectState _ _ hNext.2.2.2⟩

theorem rules_pairwise_query_distinct {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    (machine fields afterCount).rules.Pairwise WorkMachineChain.QueryDistinct := (good fields afterCount).1

theorem noRuleAtAccept {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine fields afterCount) := (good fields afterCount).2.1

theorem noRuleAtReject {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine fields afterCount) (machine fields afterCount).rejectState :=
  (good fields afterCount).2.2.1

theorem acceptState_ne_rejectState {arity : Nat} (fields : List (Field arity)) (afterCount : Nat) :
    (machine fields afterCount).acceptState ≠ (machine fields afterCount).rejectState := (good fields afterCount).2.2.2

end PNP.Concrete.CookLevin.BuilderRegisterPack
