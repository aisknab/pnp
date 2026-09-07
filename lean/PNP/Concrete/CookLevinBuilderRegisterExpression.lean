/-
Copyright (c) 2026 PNP Labs.

A fixed expression compiler reads a materialized finite register environment.
Constants, static argument addresses and binary operators determine the machine;
no environment value or evaluated result is used to generate control.
Postorder scratch, exact copies, arithmetic and every chain join are charged.

This is runtime coordinate arithmetic, not a canonical constraint constructor.
The caller must physically derive its environment from source/regional data.
-/

import PNP.Concrete.CookLevinBuilderRegionComparisonOperands
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.CookLevin.BuilderRegisterExpression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

inductive Expr (arity : Nat) where
  | constant (value : Nat)
  | argument (index : Fin arity)
  | binary (operator : RegisterBinary.Operator) (left right : Expr arity)
  deriving Repr

def eval {arity : Nat} : Expr arity → (Fin arity → Nat) → Nat
  | .constant value, _ => value
  | .argument index, environment => environment index
  | .binary operator left right, environment => RegisterBinary.value operator
      (eval left environment) (eval right environment)

def nodeCount {arity : Nat} : Expr arity → Nat
  | .constant _ => 1
  | .argument _ => 1
  | .binary _ left right => nodeCount left + nodeCount right + 1

def values {arity : Nat} : Expr arity → (Fin arity → Nat) → List Nat
  | .constant value, _ => [value]
  | .argument index, environment => [environment index]
  | .binary operator left right, environment =>
      values left environment ++ values right environment ++
        [RegisterBinary.value operator (eval left environment) (eval right environment)]

def prefixValues {arity : Nat} : Expr arity → (Fin arity → Nat) → List Nat
  | .constant _, _ => []
  | .argument _, _ => []
  | .binary _ left right, environment => values left environment ++ values right environment

theorem values_root {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    values expression environment = prefixValues expression environment ++ [eval expression environment] := by
  cases expression <;> rfl

theorem values_length {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    (values expression environment).length = nodeCount expression := by
  induction expression <;> simp only [values, nodeCount, List.length_append,
    List.length_cons, List.length_nil, *]

theorem nodeCount_positive {arity : Nat} (expression : Expr arity) : 0 < nodeCount expression := by
  cases expression <;> simp only [nodeCount] <;> omega

theorem prefixValues_length {arity : Nat} (expression : Expr arity) (environment : Fin arity → Nat) :
    (prefixValues expression environment).length = nodeCount expression - 1 := by
  have h := values_length expression environment
  rw [values_root] at h
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

def machine {arity : Nat} : Expr arity → Nat → WorkMachine
  | .constant value, _ => RegisterConstant.machine value
  | .argument index, afterCount => RegisterCopy.machine (arity - (index.val + 1) + afterCount)
  | .binary operator left right, afterCount =>
      WorkMachineChain.machine (machine left afterCount)
        (WorkMachineChain.machine (machine right (afterCount + nodeCount left))
          (RegisterBinary.machine operator (nodeCount right - 1)))

def workSteps {arity : Nat} : Expr arity → (Fin arity → Nat) → List Nat → Nat
  | .constant value, _, _ => RegisterConstant.steps value
  | .argument index, environment, after =>
      RegisterCopy.steps ((List.ofFn environment).drop (index.val + 1) ++ after) (environment index)
  | .binary operator left right, environment, after =>
      workSteps left environment after + 1 +
        (workSteps right environment (after ++ values left environment) + 1 +
          RegisterBinary.steps operator (prefixValues right environment)
            (eval left environment) (eval right environment))

def initialConfiguration {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine expression afterCount)
    (endTape (older ++ List.ofFn environment ++ after) inside outsideTail)

def finalConfiguration {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  { state := (machine expression afterCount).acceptState
    tape := endTape (older ++ List.ofFn environment ++ after ++ values expression environment)
      inside (outsideTail.drop (registerWord (values expression environment)).length) }

private theorem list_split (items : List Nat) (index : Nat) (hIndex : index < items.length) :
    items = items.take index ++ [items[index]] ++ items.drop (index + 1) := by
  induction items generalizing index with
  | nil => simp only [List.length_nil] at hIndex; exact False.elim (by omega)
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hRest : index < rest.length := by
            simp only [List.length_cons] at hIndex
            omega
          simpa only [List.take_succ_cons, List.getElem_cons_succ,
            List.drop_succ_cons, List.cons_append] using congrArg (fun tail => first :: tail) (ih index hRest)

private theorem environment_split {arity : Nat} (environment : Fin arity → Nat) (index : Fin arity) :
    List.ofFn environment =
      (List.ofFn environment).take index.val ++ [environment index] ++
        (List.ofFn environment).drop (index.val + 1) := by
  have hIndex : index.val < (List.ofFn environment).length := by
    simpa only [List.length_ofFn] using index.isLt
  have hValue : (List.ofFn environment)[index.val]'hIndex = environment index :=
    List.getElem_ofFn hIndex
  have hSplit := list_split (List.ofFn environment) index.val hIndex
  rw [hValue] at hSplit
  exact hSplit

private theorem constant_run (value : Nat) (existing : List Nat) (inside outsideTail : List WorkSymbol) :
    workRunExact? (RegisterConstant.machine value) (RegisterConstant.steps value)
      (workStartConfiguration (RegisterConstant.machine value) (endTape existing inside outsideTail)) =
      some
        { state := (RegisterConstant.machine value).acceptState
          tape := endTape (existing ++ [value]) inside (outsideTail.drop (value + 1)) } := by
  rw [RegisterConstant.machine_acceptState]
  exact RegisterConstant.workRunExact value existing inside outsideTail

private theorem binary_run (operator : RegisterBinary.Operator) (older between : List Nat) (left right : Nat)
    (inside outsideTail : List WorkSymbol) :
    workRunExact? (RegisterBinary.machine operator between.length) (RegisterBinary.steps operator between left right)
      (workStartConfiguration (RegisterBinary.machine operator between.length)
        (endTape (older ++ [left] ++ between ++ [right]) inside outsideTail)) =
      some
        { state := (RegisterBinary.machine operator between.length).acceptState
          tape := endTape (older ++ [left] ++ between ++ [right, RegisterBinary.value operator left right])
            inside (outsideTail.drop (RegisterBinary.value operator left right + 1)) } := by
  rw [RegisterBinary.machine_acceptState]
  exact RegisterBinary.workRunExact operator older between left right inside outsideTail

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

/-- The environment's values are read from its actual registers. Only the
structural after-count is an entry-layout premise. -/
theorem workRunExact {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine expression afterCount) (workSteps expression environment after)
      (initialConfiguration expression afterCount older environment after inside outsideTail) =
      some (finalConfiguration expression afterCount older environment after inside outsideTail) := by
  induction expression generalizing afterCount after outsideTail with
  | constant value =>
      simpa only [machine, workSteps, initialConfiguration, finalConfiguration,
        values, registerWord_length, List.length_cons, List.length_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_comm] using
          constant_run value (older ++ List.ofFn environment ++ after) inside outsideTail
  | argument index =>
      have hLength : ((List.ofFn environment).drop (index.val + 1) ++ after).length =
          arity - (index.val + 1) + afterCount := by
        simp only [List.length_append, List.length_drop, List.length_ofFn, hAfter]
      have hCopy := BuilderRegionComparisonOperands.copy_workRunExact
        (arity - (index.val + 1) + afterCount)
        (older ++ (List.ofFn environment).take index.val)
        ((List.ofFn environment).drop (index.val + 1) ++ after)
        (environment index) inside outsideTail hLength
      have hFrame :
          (older ++ (List.ofFn environment).take index.val) ++ [environment index] ++
            ((List.ofFn environment).drop (index.val + 1) ++ after) =
          older ++ List.ofFn environment ++ after := by
        have h := congrArg (fun data => older ++ data ++ after) (environment_split environment index)
        simpa only [List.append_assoc] using h.symm
      rw [hFrame] at hCopy
      simpa only [machine, workSteps, initialConfiguration, finalConfiguration, values,
        registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, Nat.zero_add, Nat.add_comm, List.append_assoc] using hCopy
  | binary operator left right ihLeft ihRight =>
      have hLeft := ihLeft afterCount after outsideTail hAfter
      have hNextCount : (after ++ values left environment).length = afterCount + nodeCount left := by
        rw [List.length_append, values_length, hAfter]
      have hRight := ihRight (afterCount + nodeCount left) (after ++ values left environment)
        (outsideTail.drop (registerWord (values left environment)).length) hNextCount
      have hBinary := binary_run operator
        (older ++ List.ofFn environment ++ after ++ prefixValues left environment)
        (prefixValues right environment) (eval left environment) (eval right environment) inside
        ((outsideTail.drop (registerWord (values left environment)).length).drop
          (registerWord (values right environment)).length)
      rw [prefixValues_length] at hBinary
      have hInput :
          (older ++ List.ofFn environment ++ after ++ prefixValues left environment) ++
            [eval left environment] ++ prefixValues right environment ++ [eval right environment] =
          older ++ List.ofFn environment ++ after ++ values left environment ++ values right environment := by
        rw [values_root left, values_root right]
        simp only [List.append_assoc]
      have hOutput :
          (older ++ List.ofFn environment ++ after ++ prefixValues left environment) ++
            [eval left environment] ++ prefixValues right environment ++
              [eval right environment, RegisterBinary.value operator (eval left environment) (eval right environment)] =
          older ++ List.ofFn environment ++ after ++ values (.binary operator left right) environment := by
        simp only [values, values_root left, values_root right, List.append_assoc,
          List.cons_append, List.nil_append]
      rw [hInput, hOutput] at hBinary
      have hRightRun := chain_run (machine right (afterCount + nodeCount left))
        (RegisterBinary.machine operator (nodeCount right - 1))
        (workSteps right environment (after ++ values left environment))
        (RegisterBinary.steps operator (prefixValues right environment) (eval left environment) (eval right environment))
        _ _ _ (by simpa only [initialConfiguration, finalConfiguration, List.append_assoc] using hRight) hBinary
      have hAll := chain_run (machine left afterCount)
        (WorkMachineChain.machine (machine right (afterCount + nodeCount left))
          (RegisterBinary.machine operator (nodeCount right - 1)))
        (workSteps left environment after)
        (workSteps right environment (after ++ values left environment) + 1 +
          RegisterBinary.steps operator (prefixValues right environment) (eval left environment) (eval right environment))
        _ _ _ (by simpa only [initialConfiguration, finalConfiguration, List.append_assoc] using hLeft) hRightRun
      simpa only [machine, workSteps, initialConfiguration, finalConfiguration, values,
        registerWord_append, List.length_append, registerWord_length, List.length_cons,
        List.length_nil, List.sum_cons, List.sum_nil, List.drop_drop, List.append_assoc,
        Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

theorem run_compile_exact {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine expression afterCount)) (6 * workSteps expression environment after)
      (encodeWorkConfiguration (initialConfiguration expression afterCount older environment after inside outsideTail)) =
      encodeWorkConfiguration (finalConfiguration expression afterCount older environment after inside outsideTail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact expression afterCount older environment after inside outsideTail hAfter)

private theorem span_append_single (existing : List Nat) (value : Nat) :
    (registerWord (existing ++ [value])).length =
      (registerWord existing).length + value + 1 := by
  rw [registerWord_append, List.length_append]
  simp only [registerWord_length, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

private theorem argument_bounds {arity : Nat} (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (index : Fin arity) (bound : Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound) :
    environment index ≤ bound ∧
      ((List.ofFn environment).drop (index.val + 1) ++ after).length +
        ((List.ofFn environment).drop (index.val + 1) ++ after).sum ≤ bound := by
  have hFrame :
      (older ++ (List.ofFn environment).take index.val) ++ [environment index] ++
        ((List.ofFn environment).drop (index.val + 1) ++ after) =
      older ++ List.ofFn environment ++ after := by
    have h := congrArg (fun data => older ++ data ++ after) (environment_split environment index)
    simpa only [List.append_assoc] using h.symm
  rw [← hFrame, registerWord_length] at hSpan
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hSpan ⊢
  constructor <;> omega

private theorem operand_bounds (older between : List Nat) (left right bound : Nat)
    (hSpan : (registerWord (older ++ [left] ++ between ++ [right])).length ≤ bound) :
    (registerWord ([left] ++ between ++ [right])).length ≤ bound ∧
      left ≤ bound ∧ right ≤ bound := by
  simp only [registerWord_length, List.length_append, List.length_cons,
    List.length_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero] at hSpan ⊢
  constructor
  · omega
  · constructor <;> omega

def spanBound {arity : Nat} : Expr arity → Nat → Nat
  | .constant value, bound => bound + value + 1
  | .argument _, bound => 2 * bound + 1
  | .binary operator left right, bound =>
      let afterLeft := spanBound left bound
      let afterRight := spanBound right afterLeft
      afterRight + RegisterBinary.resultBound operator afterRight + 1

def timeBound {arity : Nat} : Expr arity → Nat → Nat
  | .constant value, _ => RegisterConstant.steps value
  | .argument _, bound => 4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5
  | .binary operator left right, bound =>
      let afterLeft := spanBound left bound
      let afterRight := spanBound right afterLeft
      timeBound left bound + 1 +
        (timeBound right afterLeft + 1 + RegisterBinary.workBound operator afterRight)

/-- Bounds the entire surviving register frame, every intermediate and every
charged transition; the input environment need only be physically bounded. -/
theorem space_time_bounds {arity : Nat} (expression : Expr arity) (older : List Nat)
    (environment : Fin arity → Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values expression environment)).length ≤
        spanBound expression bound ∧
      workSteps expression environment after ≤ timeBound expression bound := by
  induction expression generalizing after bound with
  | constant value =>
      constructor
      · simp only [values, spanBound]
        rw [span_append_single]
        omega
      · exact Nat.le_refl _
  | argument index =>
      have hBounds := argument_bounds older environment after index bound hSpan
      constructor
      · simp only [values, spanBound]
        rw [span_append_single]
        omega
      · exact RegisterCopy.steps_le _ _ bound hBounds.1 hBounds.2
  | binary operator left right ihLeft ihRight =>
      have hLeft := ihLeft after bound hSpan
      have hRight := ihRight (after ++ values left environment) (spanBound left bound) (by
        simpa only [List.append_assoc] using hLeft.1)
      let afterRight := spanBound right (spanBound left bound)
      have hOperands := operand_bounds
        (older ++ List.ofFn environment ++ after ++ prefixValues left environment)
        (prefixValues right environment) (eval left environment) (eval right environment)
        afterRight (by
          simpa only [afterRight, values_root left, values_root right, List.append_assoc] using hRight.1)
      have hResult := RegisterBinary.value_le operator (eval left environment) (eval right environment)
        afterRight hOperands.2.1 hOperands.2.2
      have hTime := RegisterBinary.steps_le operator (prefixValues right environment)
        (eval left environment) (eval right environment) afterRight hOperands.1
      constructor
      · have hOutput :
            (registerWord (older ++ List.ofFn environment ++ after ++
              values (.binary operator left right) environment)).length =
            (registerWord (older ++ List.ofFn environment ++
              (after ++ values left environment) ++ values right environment)).length +
                RegisterBinary.value operator (eval left environment) (eval right environment) + 1 := by
          simpa only [values, List.append_assoc] using span_append_single
            (older ++ List.ofFn environment ++ (after ++ values left environment) ++ values right environment)
            (RegisterBinary.value operator (eval left environment) (eval right environment))
        rw [hOutput]
        change _ ≤ afterRight + RegisterBinary.resultBound operator afterRight + 1
        exact Nat.add_le_add_right (Nat.add_le_add hRight.1 hResult) 1
      · change workSteps left environment after + 1 +
            (workSteps right environment (after ++ values left environment) + 1 +
              RegisterBinary.steps operator (prefixValues right environment)
                (eval left environment) (eval right environment)) ≤
          timeBound left bound + 1 +
            (timeBound right (spanBound left bound) + 1 + RegisterBinary.workBound operator afterRight)
        omega

private def binaryResultPolynomial (operator : RegisterBinary.Operator) (bound : NatPolynomial) :
    NatPolynomial :=
  match operator with
  | .add => .mul (.constant 2) bound
  | .mul => .mul bound bound

private theorem binaryResultPolynomial_eval (operator : RegisterBinary.Operator)
    (bound : NatPolynomial) (input : Nat) :
    (binaryResultPolynomial operator bound).eval input = RegisterBinary.resultBound operator (bound.eval input) := by
  cases operator <;> rfl

private def binaryWorkPolynomial (operator : RegisterBinary.Operator) (bound : NatPolynomial) :
    NatPolynomial :=
  let twice := NatPolynomial.mul (.constant 2) bound
  let square := NatPolynomial.mul bound bound
  match operator with
  | .add => .add (.constant 2) (.mul (.constant 2)
      (.add (.add (.mul (.mul (.constant 4) bound) bound) (.mul (.constant 9) bound)) (.constant 3)))
  | .mul => .add (.constant 2)
      (.add (.add (.add (.add
        (.mul bound (.add (.add (.add twice square) (.mul (.constant 7) bound)) (.constant 7)))
        (.mul (.mul (.add (.add square twice) (.constant 1)) bound) bound))
        twice) (.mul twice bound)) (.add twice (.constant 3)))

private theorem binaryWorkPolynomial_eval (operator : RegisterBinary.Operator)
    (bound : NatPolynomial) (input : Nat) :
    (binaryWorkPolynomial operator bound).eval input = RegisterBinary.workBound operator (bound.eval input) := by
  cases operator with
  | add => rfl
  | mul =>
      simp only [binaryWorkPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
        NatPolynomial.eval_constant, RegisterBinary.workBound, Nat.add_assoc]

def spanPolynomial {arity : Nat} : Expr arity → NatPolynomial → NatPolynomial
  | .constant value, bound => .add (.add bound (.constant value)) (.constant 1)
  | .argument _, bound => .add (.mul (.constant 2) bound) (.constant 1)
  | .binary operator left right, bound =>
      let afterRight := spanPolynomial right (spanPolynomial left bound)
      .add (.add afterRight (binaryResultPolynomial operator afterRight)) (.constant 1)

theorem spanPolynomial_eval {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial expression bound).eval input = spanBound expression (bound.eval input) := by
  induction expression generalizing bound with
  | constant value => rfl
  | argument index => rfl
  | binary operator left right ihLeft ihRight =>
      simp only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
        binaryResultPolynomial_eval, ihLeft, ihRight, spanBound]

def timePolynomial {arity : Nat} : Expr arity → NatPolynomial → NatPolynomial
  | .constant value, _ => .constant (RegisterConstant.steps value)
  | .argument _, bound =>
      let next := NatPolynomial.add bound (.constant 1)
      .add (.add (.mul (.mul (.constant 4) next) next) (.mul (.constant 9) next)) (.constant 5)
  | .binary operator left right, bound =>
      let afterLeft := spanPolynomial left bound
      let afterRight := spanPolynomial right afterLeft
      .add (.add (timePolynomial left bound) (.constant 1))
        (.add (.add (timePolynomial right afterLeft) (.constant 1))
          (binaryWorkPolynomial operator afterRight))

theorem timePolynomial_eval {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) (input : Nat) :
    (timePolynomial expression bound).eval input = timeBound expression (bound.eval input) := by
  induction expression generalizing bound with
  | constant value => rfl
  | argument index => rfl
  | binary operator left right ihLeft ihRight =>
      simp only [timePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
        binaryWorkPolynomial_eval, spanPolynomial_eval, ihLeft, ihRight, timeBound]

def rawTimePolynomial {arity : Nat} (expression : Expr arity) (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (timePolynomial expression bound)

theorem source_polynomial_bounds {arity : Nat} (expression : Expr arity) (bound : NatPolynomial)
    (inputLength : Nat) (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (hSpan : (registerWord (older ++ List.ofFn environment ++ after)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ List.ofFn environment ++ after ++ values expression environment)).length ≤
        (spanPolynomial expression bound).eval inputLength ∧
      6 * workSteps expression environment after ≤ (rawTimePolynomial expression bound).eval inputLength := by
  have h := space_time_bounds expression older environment after (bound.eval inputLength) hSpan
  constructor
  · rw [spanPolynomial_eval]
    exact h.1
  · simp only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant, timePolynomial_eval]
    exact Nat.mul_le_mul_left 6 h.2

theorem final_tape {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) :
    (finalConfiguration expression afterCount older environment after inside outsideTail).tape =
      endTape (older ++ List.ofFn environment ++ after ++ values expression environment)
        inside (outsideTail.drop (registerWord (values expression environment)).length) := rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem constant_good (value : Nat) : Good (RegisterConstant.machine value) := by
  refine ⟨RegisterConstant.rules_pairwise_query_distinct value, ?_, ?_,
    RegisterConstant.machine_acceptState_ne_rejectState value⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterConstant.rule_source_lt_acceptState value rule hRule)
  · intro rule hRule
    have h := RegisterConstant.rule_source_lt_acceptState value rule hRule
    rw [RegisterConstant.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterConstant.machine value).rejectState
    rw [RegisterConstant.machine_rejectState]
    omega

private theorem copy_good (newerCount : Nat) : Good (RegisterCopy.machine newerCount) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct newerCount, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState newerCount⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState newerCount rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState newerCount rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterCopy.machine newerCount).rejectState
    rw [RegisterCopy.machine_rejectState]
    omega

private theorem binary_good (operator : RegisterBinary.Operator) (betweenCount : Nat) :
    Good (RegisterBinary.machine operator betweenCount) := by
  refine ⟨RegisterBinary.rules_pairwise_query_distinct operator betweenCount, ?_, ?_,
    RegisterBinary.machine_acceptState_ne_rejectState operator betweenCount⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterBinary.rule_source_lt_acceptState operator betweenCount rule hRule)
  · intro rule hRule
    have h := RegisterBinary.rule_source_lt_acceptState operator betweenCount rule hRule
    rw [RegisterBinary.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterBinary.machine operator betweenCount).rejectState
    rw [RegisterBinary.machine_rejectState]
    omega

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem good {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    Good (machine expression afterCount) := by
  induction expression generalizing afterCount with
  | constant value => exact constant_good value
  | argument index => exact copy_good _
  | binary operator left right ihLeft ihRight =>
      exact chain_good _ _ (ihLeft afterCount)
        (chain_good _ _ (ihRight (afterCount + nodeCount left)) (binary_good _ _))

theorem rules_pairwise_query_distinct {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    (machine expression afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  (good expression afterCount).1

theorem noRuleAtAccept {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine expression afterCount) := (good expression afterCount).2.1

theorem noRuleAtReject {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine expression afterCount) (machine expression afterCount).rejectState :=
  (good expression afterCount).2.2.1

theorem acceptState_ne_rejectState {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    (machine expression afterCount).acceptState ≠ (machine expression afterCount).rejectState :=
  (good expression afterCount).2.2.2

theorem final_root_register {arity : Nat} (expression : Expr arity) (afterCount : Nat)
    (older : List Nat) (environment : Fin arity → Nat) (after : List Nat)
    (inside outsideTail : List WorkSymbol) :
    (finalConfiguration expression afterCount older environment after inside outsideTail).tape =
      endTape ((older ++ List.ofFn environment ++ after ++ prefixValues expression environment) ++
        [eval expression environment]) inside (outsideTail.drop (registerWord (values expression environment)).length) := by
  simp only [finalConfiguration, values_root, List.append_assoc]

end PNP.Concrete.CookLevin.BuilderRegisterExpression
