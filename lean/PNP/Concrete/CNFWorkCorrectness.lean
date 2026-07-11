/-
Copyright (c) 2026 PNP Labs.

Universal operational correctness of the literal CNF work machine.  This
module keeps the proof at the finite rule-list interpreter boundary: phase
invariants describe concrete work tapes, exact traces are composed, and only
then is the generic six-raw-steps compiler theorem applied.
-/

import PNP.Concrete.CNFWorkTransitions
import PNP.Concrete.CNFVerifier

namespace PNP.Concrete

/-! ### Constructive tape and exact-run infrastructure -/

namespace WorkTape

/-- A tape with its nearest-left cells given first, matching `WorkTape.left`. -/
def focus (leftSide : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol) : WorkTape :=
  { left := leftSide, head := head, right := suffix }

theorem focus_moveRight (leftSide : List WorkSymbol) (head next : WorkSymbol)
    (suffix : List WorkSymbol) :
    (focus leftSide head (next :: suffix)).moveRight =
      focus (head :: leftSide) next suffix := rfl

theorem focus_moveRight_blank (leftSide : List WorkSymbol)
    (head : WorkSymbol) :
    (focus leftSide head []).moveRight =
      focus (head :: leftSide) WorkSymbol.blank [] := rfl

theorem focus_write (leftSide : List WorkSymbol) (head write : WorkSymbol)
    (suffix : List WorkSymbol) :
    (focus leftSide head suffix).write write = focus leftSide write suffix := rfl

end WorkTape

theorem workRunExact?_compose (machine : WorkMachine)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, hStart]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine start with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

theorem workRunExact?_one_of_step (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

theorem workStep?_eq_none_of_halted (machine : WorkMachine)
    (config : WorkConfiguration) (hHalted : machine.isHalted config = true) :
    workStep? machine config = none := by
  unfold workStep?
  exact if_pos hHalted

theorem workRun_eq_self_of_step?_none (machine : WorkMachine)
    (fuel : Nat) (config : WorkConfiguration)
    (hStep : workStep? machine config = none) :
    workRun machine fuel config = config := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change (match workStep? machine config with
        | none => config
        | some next => workRun machine fuel next) = config
      rw [hStep]

theorem workRun_eq_self_of_halted (machine : WorkMachine)
    (fuel : Nat) (config : WorkConfiguration)
    (hHalted : machine.isHalted config = true) :
    workRun machine fuel config = config :=
  workRun_eq_self_of_step?_none machine fuel config
    (workStep?_eq_none_of_halted machine config hHalted)

theorem workRun_add (machine : WorkMachine) (first second : Nat)
    (config : WorkConfiguration) :
    workRun machine (first + second) config =
      workRun machine second (workRun machine first config) := by
  induction first generalizing config with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      change
        (match workStep? machine config with
         | none => config
         | some next => workRun machine (first + second) next) =
        workRun machine second
          (match workStep? machine config with
           | none => config
           | some next => workRun machine first next)
      cases hStep : workStep? machine config with
      | none =>
          exact (workRun_eq_self_of_step?_none machine second config hStep).symm
      | some next => exact ih next

theorem workRun_of_exact (machine : WorkMachine) (steps : Nat)
    (start final : WorkConfiguration)
    (hExact : workRunExact? machine steps start = some final) :
    workRun machine steps start = final := by
  induction steps generalizing start with
  | zero =>
      change some start = some final at hExact
      exact Option.some.inj hExact
  | succ steps ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine steps next) =
              some final at hExact
          rw [hStep] at hExact
          contradiction
      | some next =>
          have hTail : workRunExact? machine steps next = some final := by
            change
              (match workStep? machine start with
               | none => none
               | some next => workRunExact? machine steps next) =
                some final at hExact
            rw [hStep] at hExact
            exact hExact
          change (match workStep? machine start with
            | none => start
            | some next => workRun machine steps next) = final
          rw [hStep]
          exact ih next hTail

private theorem exists_add_of_le_constructive {smaller larger : Nat}
    (h : smaller ≤ larger) : ∃ extra, larger = smaller + extra := by
  induction larger generalizing smaller with
  | zero =>
      cases smaller with
      | zero => exact ⟨0, rfl⟩
      | succ smaller => cases h
  | succ larger ih =>
      cases smaller with
      | zero => exact ⟨larger + 1, (Nat.zero_add (larger + 1)).symm⟩
      | succ smaller =>
          have hTail : smaller ≤ larger := Nat.le_of_succ_le_succ h
          rcases ih hTail with ⟨extra, hExtra⟩
          refine ⟨extra, ?_⟩
          rw [Nat.succ_add]
          exact congrArg Nat.succ hExtra

theorem workRun_pad_exact_halted (machine : WorkMachine)
    (steps fuel : Nat) (start final : WorkConfiguration)
    (hExact : workRunExact? machine steps start = some final)
    (hHalted : machine.isHalted final = true)
    (hBound : steps ≤ fuel) :
    workRun machine fuel start = final := by
  rcases exists_add_of_le_constructive hBound with ⟨extra, hFuel⟩
  rw [hFuel, workRun_add]
  rw [workRun_of_exact machine steps start final hExact]
  exact workRun_eq_self_of_halted machine extra final hHalted

end PNP.Concrete
