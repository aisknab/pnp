/-
Copyright (c) 2026 PNP Labs.

Count actual clause-separator token pairs in formula bytes. The finite
machine derives its count from the data, handles odd or malformed inputs,
and has a linear bound independent of any supplied clause count.
-/

import PNP.Concrete.NormalizerExplorationRuntime

namespace PNP.Concrete.NormalizerBlocks.ClauseCount
open BitRegister Occurrence

def pop : Block 9 := .action (.pop 0)
def popped (r : Registers) : Registers := {r with input := r.input.tail}
theorem pop_exec (r : Registers) : Exec pop r.store 1 (popped r).store := .action _ _

def add : Block 9 := .seq (.action (.push 1 true)) pop
def added (r : Registers) : Registers := {r with input := r.input.tail, target := true :: r.target}
theorem add_exec (r : Registers) : Exec add r.store 2 (added r).store := by
  have start : Exec (.action (.push (1 : Fin 9) true)) r.store 1
      ({r with target := true :: r.target}).store := .action _ _
  exact Exec.seq start (pop_exec {r with target := true :: r.target})

def second : Block 9 := .branch 0 pop pop add
def secondResult (r : Registers) : Registers := if ForwardEdge.present r.input then added r else popped r
def secondFuel (r : Registers) : Nat := 1 + if ForwardEdge.present r.input then 2 else 1
theorem second_exec (r : Registers) : Exec second r.store (secondFuel r) (secondResult r).store := by
  have checked := EdgeKinds.branch_head (0 : Fin 9) r.store pop add 1 2
    (popped r).store (added r).store (pop_exec r) (add_exec r)
  change Exec second r.store (secondFuel r)
    (if ForwardEdge.present r.input then (added r).store else (popped r).store) at checked
  cases found : ForwardEdge.present r.input <;>
    simpa only [secondResult, found, Bool.false_eq_true, ite_false, ite_true] using checked

def body : Block 9 := .branch 0 pop (.seq pop second) (.seq pop pop)
def bodyResult (r : Registers) : Registers :=
  match r.input with
  | [] => popped r
  | false :: _ => secondResult (popped r)
  | true :: _ => popped (popped r)
def bodyFuel (r : Registers) : Nat :=
  match r.input with
  | [] => 2
  | false :: _ => 2 + secondFuel (popped r)
  | true :: _ => 3
theorem body_exec (r : Registers) : Exec body r.store (bodyFuel r) (bodyResult r).store := by
  cases input : r.input with
  | nil =>
      simp only [bodyResult, bodyFuel, input]
      exact Exec.empty (source := (0 : Fin 9)) (before := r.store) input (pop_exec r)
  | cons first rest =>
      cases first with
      | false =>
          simp only [bodyResult, bodyFuel, input]
          have checked := Exec.zero (source := (0 : Fin 9)) (before := r.store)
            (empty := pop) (one := .seq pop pop) input (Exec.seq (pop_exec r) (second_exec (popped r)))
          have joined : 1 + (1 + secondFuel (popped r)) = 2 + secondFuel (popped r) := by omega
          rw [joined] at checked
          exact checked
      | true =>
          simp only [bodyResult, bodyFuel, input]
          exact Exec.one (source := (0 : Fin 9)) (before := r.store)
            input (Exec.seq (pop_exec r) (pop_exec (popped r)))

def count : BitString → Nat
  | false :: true :: rest => count rest + 1
  | _ :: _ :: rest => count rest
  | _ => 0

def bodyCount (r : Registers) : Nat :=
  if ForwardEdge.present r.input then 0 else if ForwardEdge.present r.input.tail then 1 else 0

theorem body_fields (r : Registers) :
    bodyResult r = {r with input := r.input.tail.tail, target := List.replicate (bodyCount r) true ++ r.target} := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases input with
      | nil => rfl
      | cons first rest =>
          cases first <;> cases rest with
          | nil => rfl
          | cons second tail => cases second <;> rfl

theorem bodyFuel_bound (r : Registers) : bodyFuel r ≤ 5 := by
  cases input : r.input with
  | nil => simp only [bodyFuel, input]; omega
  | cons first rest =>
      cases first with
      | true => simp only [bodyFuel, input]; omega
      | false =>
          simp only [bodyFuel, input, secondFuel]
          cases ForwardEdge.present (popped r).input <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

def loop : Block 9 := .loop 0 body
def run : BitString → Registers → Result
  | [], r => ⟨1, {r with input := []}⟩
  | [first], r =>
      let next := bodyResult {r with input := [first]}
      ⟨1 + (bodyFuel {r with input := [first]} + 1), {next with input := []}⟩
  | first :: second :: rest, r =>
      let next := bodyResult {r with input := first :: second :: rest}
      let tail := run rest next
      ⟨1 + (bodyFuel {r with input := first :: second :: rest} + tail.fuel), tail.state⟩

private theorem input_reset (r : Registers) (word : BitString) (read : r.input = word) :
    {r with input := word} = r := by
  cases r
  cases read
  rfl

theorem run_exec (word : BitString) (r : Registers) :
    Exec loop ({r with input := word}).store (run word r).fuel (run word r).state.store := by
  cases word with
  | nil => exact Exec.loopStop rfl
  | cons first rest =>
      cases rest with
      | nil =>
          have nextInput : (bodyResult {r with input := [first]}).input = [] := by rw [body_fields]; rfl
          have finalStore : {bodyResult {r with input := [first]} with input := []} =
              bodyResult {r with input := [first]} := input_reset _ _ nextInput
          simp only [run, finalStore]
          exact Exec.loopStep (source := (0 : Fin 9)) (body := body) (before := ({r with input := [first]}).store)
            rfl (body_exec _) (Exec.loopStop (source := (0 : Fin 9)) (body := body)
              (store := (bodyResult {r with input := [first]}).store) nextInput)
      | cons second tail =>
          have nextInput : (bodyResult {r with input := first :: second :: tail}).input = tail := by
            rw [body_fields]
            rfl
          have start : {bodyResult {r with input := first :: second :: tail} with input := tail} =
              bodyResult {r with input := first :: second :: tail} := input_reset _ _ nextInput
          have restChecked := run_exec tail (bodyResult {r with input := first :: second :: tail})
          rw [start] at restChecked
          exact Exec.loopStep (source := (0 : Fin 9)) (body := body)
            (before := ({r with input := first :: second :: tail}).store) rfl (body_exec _) restChecked
termination_by structural word

private theorem replicate_push (count : Nat) (word : BitString) :
    List.replicate count true ++ (true :: word) = true :: (List.replicate count true ++ word) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons true) ih

theorem run_result (word : BitString) (r : Registers) :
    (run word r).state = {r with input := [], target := List.replicate (count word) true ++ r.target} := by
  cases word with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => cases first <;> rw [run, body_fields] <;> rfl
      | cons second tail =>
          change (run tail (bodyResult {r with input := first :: second :: tail})).state = _
          rw [run_result tail, body_fields]
          cases first <;> cases second
          · rfl
          · change {r with input := [], target := List.replicate (count tail) true ++ (true :: r.target)} =
              {r with input := [], target := true :: (List.replicate (count tail) true ++ r.target)}
            exact congrArg (fun target => ({r with input := [], target := target} : Registers))
              (replicate_push (count tail) r.target)
          · rfl
          · rfl
termination_by structural word

theorem run_fuel_bound (word : BitString) (r : Registers) :
    (run word r).fuel ≤ 6 * word.length + 1 := by
  cases word with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      cases rest with
      | nil =>
          have step := bodyFuel_bound {r with input := [first]}
          change 1 + (bodyFuel {r with input := [first]} + 1) ≤ 6 * (0 + 1) + 1
          omega
      | cons second tail =>
          have step := bodyFuel_bound {r with input := first :: second :: tail}
          have next := run_fuel_bound tail (bodyResult {r with input := first :: second :: tail})
          simp only [run, List.length_cons]
          omega
termination_by structural word

theorem count_bound (word : BitString) : count word ≤ word.length := by
  cases word with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      cases rest with
      | nil => cases first <;> simp only [count, List.length_cons, List.length_nil] <;> omega
      | cons second tail =>
          have next := count_bound tail
          cases first <;> cases second <;> simp only [count, List.length_cons] <;> omega
termination_by structural word

end PNP.Concrete.NormalizerBlocks.ClauseCount
