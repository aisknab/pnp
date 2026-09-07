/-
Copyright (c) 2026 PNP Labs.

Structural addresses into already materialized polynomial postorder registers.
The address and copy list determine finite control; input values do not.
This reads existing cells rather than reevaluating a polynomial or accepting
a supplied value. The sequence compiler preserves the complete original frame.
-/

import PNP.Concrete.CookLevinBuilderRegionRadixDecoder

namespace PNP.Concrete.CookLevin.BuilderPolynomialRegisterCopies

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

inductive Address : NatPolynomial → Type where
  | root (polynomial : NatPolynomial) : Address polynomial
  | addLeft {left right : NatPolynomial} : Address left → Address (.add left right)
  | addRight {left right : NatPolynomial} : Address right → Address (.add left right)
  | mulLeft {left right : NatPolynomial} : Address left → Address (.mul left right)
  | mulRight {left right : NatPolynomial} : Address right → Address (.mul left right)

namespace Address

def selected : {polynomial : NatPolynomial} → Address polynomial → NatPolynomial
  | _, .root polynomial => polynomial
  | _, .addLeft address => selected address
  | _, .addRight address => selected address
  | _, .mulLeft address => selected address
  | _, .mulRight address => selected address

def older : {polynomial : NatPolynomial} → Address polynomial → Nat → List Nat
  | _, .root polynomial, input => BuilderOperandRegisters.rootPrefix polynomial input
  | _, .addLeft address, input => older address input
  | .add left _, .addRight address, input => registerValues left input ++ older address input
  | _, .mulLeft address, input => older address input
  | .mul left _, .mulRight address, input => registerValues left input ++ older address input

def newer : {polynomial : NatPolynomial} → Address polynomial → Nat → List Nat
  | _, .root _, _ => []
  | .add left right, .addLeft address, input =>
      newer address input ++ registerValues right input ++ [left.eval input + right.eval input]
  | .add left right, .addRight address, input =>
      newer address input ++ [left.eval input + right.eval input]
  | .mul left right, .mulLeft address, input =>
      newer address input ++ registerValues right input ++ [left.eval input * right.eval input]
  | .mul left right, .mulRight address, input =>
      newer address input ++ [left.eval input * right.eval input]

def newerCount : {polynomial : NatPolynomial} → Address polynomial → Nat
  | _, .root _ => 0
  | .add _ right, .addLeft address => newerCount address + nodeCount right + 1
  | _, .addRight address => newerCount address + 1
  | .mul _ right, .mulLeft address => newerCount address + nodeCount right + 1
  | _, .mulRight address => newerCount address + 1

theorem layout {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) :
    registerValues polynomial input =
      address.older input ++ [address.selected.eval input] ++ address.newer input := by
  induction address with
  | root polynomial => simpa only [older, selected, newer, List.append_nil] using
      BuilderOperandRegisters.registerValues_rootPrefix polynomial input
  | addLeft address ih =>
    simp only [registerValues, older, selected, newer]
    rw [ih]
    simp only [List.append_assoc]
  | addRight address ih =>
    simp only [registerValues, older, selected, newer]
    rw [ih]
    simp only [List.append_assoc]
  | mulLeft address ih =>
    simp only [registerValues, older, selected, newer]
    rw [ih]
    simp only [List.append_assoc]
  | mulRight address ih =>
    simp only [registerValues, older, selected, newer]
    rw [ih]
    simp only [List.append_assoc]

theorem newer_length {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) :
    (address.newer input).length = address.newerCount := by
  induction address <;>
    simp only [newer, newerCount, List.length_append, List.length_cons, List.length_nil,
      registerValues_length, *]

end Address

def inputValues (polynomial : NatPolynomial) (input : Nat) (before after : List Nat) : List Nat :=
  before ++ registerValues polynomial input ++ after

theorem inputValues_selection {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) :
    inputValues polynomial input before after =
      (before ++ address.older input) ++ [address.selected.eval input] ++ (address.newer input ++ after) := by
  unfold inputValues
  rw [address.layout]
  simp only [List.append_assoc]

def copyMachine {polynomial : NatPolynomial} (address : Address polynomial) (afterCount : Nat) : WorkMachine :=
  RegisterCopy.machine (address.newerCount + afterCount)

def copySteps {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) (after : List Nat) : Nat :=
  RegisterCopy.steps (address.newer input ++ after) (address.selected.eval input)

theorem copy_workRunExact {polynomial : NatPolynomial} (address : Address polynomial)
    (afterCount input : Nat) (before after : List Nat) (workspace : List WorkSymbol)
    (hCount : after.length = afterCount) :
    workRunExact? (copyMachine address afterCount) (copySteps address input after)
      (workStartConfiguration (copyMachine address afterCount)
        (endTape (inputValues polynomial input before after) workspace [])) =
      some {
        state := (copyMachine address afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ [address.selected.eval input]) workspace []
      } := by
  have hLength : (address.newer input ++ after).length = address.newerCount + afterCount := by
    rw [List.length_append, address.newer_length, hCount]
  have h := BuilderRegionComparisonOperands.copy_workRunExact (address.newerCount + afterCount)
    (before ++ address.older input) (address.newer input ++ after) (address.selected.eval input)
    workspace [] hLength
  simpa only [copyMachine, copySteps, inputValues_selection address, List.drop_nil, List.append_assoc] using h

theorem selection_bounds {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    address.selected.eval input ≤ bound ∧
      (address.newer input ++ after).length + (address.newer input ++ after).sum ≤ bound := by
  rw [inputValues_selection address, registerWord_length] at hSpan
  simp only [List.length_append, List.length_cons, List.length_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero] at hSpan ⊢
  constructor <;> omega

def copyBound (bound : Nat) : Nat := 4 * (bound + 1) ^ 2 + 9 * (bound + 1) + 5

theorem copySteps_le {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    copySteps address input after ≤ copyBound bound := by
  have h := selection_bounds address input before after bound hSpan
  simpa only [copySteps, copyBound, Nat.pow_two, Nat.mul_assoc] using RegisterCopy.steps_le _ _ _ h.1 h.2

theorem copied_span_le {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    (registerWord (inputValues polynomial input before (after ++ [address.selected.eval input]))).length ≤ 2 * bound + 1 := by
  have hValue := (selection_bounds address input before after bound hSpan).1
  have hAppend :
      inputValues polynomial input before (after ++ [address.selected.eval input]) =
        inputValues polynomial input before after ++ [address.selected.eval input] := by
    simp only [inputValues, List.append_assoc]
  rw [hAppend, registerWord_append, List.length_append]
  have hSingle : (registerWord [address.selected.eval input]).length = 1 + address.selected.eval input := by
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [hSingle]
  omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem copy_good {polynomial : NatPolynomial} (address : Address polynomial) (afterCount : Nat) :
    Good (copyMachine address afterCount) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct _, ?_, ?_, RegisterCopy.machine_acceptState_ne_rejectState _⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState _ rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState _ rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterCopy.machine (address.newerCount + afterCount)).rejectState
    rw [RegisterCopy.machine_rejectState]
    omega

/-- A fixed list of structural source addresses, not an input-generated program. -/
def machine {polynomial : NatPolynomial} : List (Address polynomial) → Nat → WorkMachine
  | [], _ => BuilderRegionRadixDecoder.doneMachine
  | address :: rest, afterCount => WorkMachineChain.machine (copyMachine address afterCount)
      (machine rest (afterCount + 1))

def values {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (input : Nat) : List Nat :=
  addresses.map (fun address => address.selected.eval input)

def workSteps {polynomial : NatPolynomial} : List (Address polynomial) → Nat → List Nat → Nat
  | [], _, _ => 0
  | address :: rest, input, after => copySteps address input after + 1 +
      workSteps rest input (after ++ [address.selected.eval input])

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

theorem workRunExact {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (afterCount input : Nat) (before after : List Nat) (workspace : List WorkSymbol)
    (hCount : after.length = afterCount) :
    workRunExact? (machine addresses afterCount) (workSteps addresses input after)
      (workStartConfiguration (machine addresses afterCount)
        (endTape (inputValues polynomial input before after) workspace [])) =
      some {
        state := (machine addresses afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ values addresses input) workspace []
      } := by
  induction addresses generalizing afterCount after with
  | nil =>
    simp only [machine, workSteps, values, List.map_nil, List.append_nil,
      BuilderRegionRadixDecoder.doneMachine, workStartConfiguration, workRunExact?]
  | cons address rest ih =>
    have hFirst := copy_workRunExact address afterCount input before after workspace hCount
    have hNextCount : (after ++ [address.selected.eval input]).length = afterCount + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil, hCount]
    have hNext := ih (afterCount + 1) (after ++ [address.selected.eval input]) hNextCount
    have hMiddle :
        inputValues polynomial input before (after ++ [address.selected.eval input]) =
          inputValues polynomial input before after ++ [address.selected.eval input] := by
      simp only [inputValues, List.append_assoc]
    rw [hMiddle] at hNext
    have h := chain_run (copyMachine address afterCount) (machine rest (afterCount + 1))
      (copySteps address input after) (workSteps rest input (after ++ [address.selected.eval input]))
      _ _ _ hFirst hNext
    simpa only [machine, workSteps, values, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append] using h

theorem run_compile_exact {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (afterCount input : Nat) (before after : List Nat) (workspace : List WorkSymbol)
    (hCount : after.length = afterCount) :
    run (compileWorkMachine (machine addresses afterCount)) (6 * workSteps addresses input after)
      (encodeWorkConfiguration (workStartConfiguration (machine addresses afterCount)
        (endTape (inputValues polynomial input before after) workspace []))) =
      encodeWorkConfiguration {
        state := (machine addresses afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ values addresses input) workspace []
      } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact addresses afterCount input before after workspace hCount)

private theorem good {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (afterCount : Nat) :
    Good (machine addresses afterCount) := by
  induction addresses generalizing afterCount with
  | nil =>
    change Good BuilderRegionRadixDecoder.doneMachine
    refine ⟨List.Pairwise.nil, ?_, ?_, by decide⟩
    · intro rule hMem; cases hMem
    · intro rule hMem; cases hMem
  | cons address rest ih =>
    have hFirst := copy_good address afterCount
    have hNext := ih (afterCount + 1)
    exact ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hNext.1 hFirst.2.1,
      WorkMachineChain.noRuleAtAccept _ _ hNext.2.1,
      WorkMachineChain.noRuleAtAccept (copyMachine address afterCount)
        { machine rest (afterCount + 1) with acceptState := (machine rest (afterCount + 1)).rejectState } hNext.2.2.1,
      WorkMachineChain.machine_acceptState_ne_rejectState _ _ hNext.2.2.2⟩

theorem rules_pairwise_query_distinct {polynomial : NatPolynomial}
    (addresses : List (Address polynomial)) (afterCount : Nat) :
    (machine addresses afterCount).rules.Pairwise WorkMachineChain.QueryDistinct := (good addresses afterCount).1

theorem noRuleAtAccept {polynomial : NatPolynomial}
    (addresses : List (Address polynomial)) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine addresses afterCount) := (good addresses afterCount).2.1

theorem noRuleAtReject {polynomial : NatPolynomial}
    (addresses : List (Address polynomial)) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine addresses afterCount) (machine addresses afterCount).rejectState :=
  (good addresses afterCount).2.2.1

theorem acceptState_ne_rejectState {polynomial : NatPolynomial}
    (addresses : List (Address polynomial)) (afterCount : Nat) :
    (machine addresses afterCount).acceptState ≠ (machine addresses afterCount).rejectState :=
  (good addresses afterCount).2.2.2

def workBound : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, bound => copyBound bound + 1 + workBound count (2 * bound + 1)

def spanBound : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => spanBound count (2 * bound + 1)

theorem spanBound_ge (count bound : Nat) : bound ≤ spanBound count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    have h := ih (2 * bound + 1)
    change bound ≤ spanBound count (2 * bound + 1)
    omega

theorem workSteps_le {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    workSteps addresses input after ≤ workBound addresses.length bound := by
  induction addresses generalizing after bound with
  | nil => exact Nat.le_refl _
  | cons address rest ih =>
    have hFirst := copySteps_le address input before after bound hSpan
    have hSpanNext := copied_span_le address input before after bound hSpan
    have hNext := ih (after ++ [address.selected.eval input]) (2 * bound + 1) hSpanNext
    simp only [workSteps, workBound, List.length_cons]
    omega

theorem final_span_le {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    (registerWord (inputValues polynomial input before after ++ values addresses input)).length ≤
      spanBound addresses.length bound := by
  induction addresses generalizing after bound with
  | nil => simpa only [values, List.map_nil, List.append_nil, List.length_nil, spanBound] using hSpan
  | cons address rest ih =>
    have hSpanNext := copied_span_le address input before after bound hSpan
    have hNext := ih (after ++ [address.selected.eval input]) (2 * bound + 1) hSpanNext
    simpa only [values, List.map_cons, List.length_cons, spanBound, inputValues, List.append_assoc,
      List.cons_append, List.nil_append] using hNext

private def nextBound (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 2) bound) (.constant 1)

def spanPolynomial : Nat → NatPolynomial → NatPolynomial
  | 0, bound => bound
  | count + 1, bound => spanPolynomial count (nextBound bound)

theorem spanPolynomial_eval (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial count bound).eval input = spanBound count (bound.eval input) := by
  induction count generalizing bound with
  | zero => rfl
  | succ count ih =>
    simp only [spanPolynomial, ih, spanBound, nextBound, NatPolynomial.eval_add,
      NatPolynomial.eval_mul, NatPolynomial.eval_constant]

def copyPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let next := NatPolynomial.add bound (.constant 1)
  .add (.mul (.constant 4) (.mul next next)) (.add (.mul (.constant 9) next) (.constant 5))

theorem copyPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (copyPolynomial bound).eval input = copyBound (bound.eval input) := by
  simp only [copyPolynomial, copyBound, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, Nat.pow_two, Nat.add_assoc]

def rawTimePolynomial : Nat → NatPolynomial → NatPolynomial
  | 0, _ => .constant 0
  | count + 1, bound =>
      .add (.mul (.constant 6) (copyPolynomial bound))
        (.add (.constant 6) (rawTimePolynomial count (nextBound bound)))

theorem rawTimePolynomial_eval (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial count bound).eval input = 6 * workBound count (bound.eval input) := by
  induction count generalizing bound with
  | zero => rfl
  | succ count ih =>
    simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
      NatPolynomial.eval_constant, copyPolynomial_eval, ih, nextBound, workBound,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc]

theorem rawTimePolynomial_le {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : NatPolynomial)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound.eval input) :
    6 * workSteps addresses input after ≤ (rawTimePolynomial addresses.length bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le addresses input before after (bound.eval input) hSpan)

end PNP.Concrete.CookLevin.BuilderPolynomialRegisterCopies
