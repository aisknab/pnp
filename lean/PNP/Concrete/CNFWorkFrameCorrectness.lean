/-
Copyright (c) 2026 PNP Labs.

Constructive exact-run infrastructure for the two self-delimiting frame
validation phases of the direct CNF work machine.  The tape predicates below
make the nearest-cell-first convention on the left half of a work tape
explicit; this keeps later phase proofs independent of implementation-level
list reassociation.
-/

import PNP.Concrete.CNFWorkTransitions

namespace PNP.Concrete

/-! ### Exact-run composition -/

/-- Exact work executions compose without forgetting early-stop information. -/
theorem workRunExact?_add_of_exact (machine : WorkMachine)
    (first second : Nat) (initial middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first initial = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final := by
  induction first generalizing initial with
  | zero =>
      have hInitial : initial = middle := Option.some.inj hFirst
      cases hInitial
      simpa using hSecond
  | succ first ih =>
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

/-- A selected nonhalting transition is a one-step exact execution. -/
theorem workRunExact?_one_of_find (machine : WorkMachine)
    (config : WorkConfiguration) (rule : WorkRule)
    (hHalted : machine.isHalted config = false)
    (hFind : findWorkRule machine.rules config.state config.tape.head =
      some rule) :
    workRunExact? machine 1 config = some (applyWorkRule rule config) := by
  change
    (match workStep? machine config with
     | none => none
     | some next => some next) = some (applyWorkRule rule config)
  rw [workStep?_eq_apply_of_find machine config rule hHalted hFind]

/-! ### Directional scan invariants -/

/-- A tape focused just before a rightward scan.  `word` is the finite word
to cross, and `delimiter` is guaranteed to provide the next focused cell. -/
def WorkTape.beforeRightScan (left word : List WorkSymbol)
    (delimiter : WorkSymbol) (suffix : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := delimiter, right := suffix }
  | symbol :: rest =>
      { left := left, head := symbol, right := rest ++ delimiter :: suffix }

/-- A tape focused just before a leftward scan.  `word` is written in scan
order (nearest cell first), exactly as `WorkTape.left` stores it. -/
def WorkTape.beforeLeftScan (leftSuffix word : List WorkSymbol)
    (delimiter : WorkSymbol) (right : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := leftSuffix, head := delimiter, right := right }
  | symbol :: rest =>
      { left := rest ++ delimiter :: leftSuffix, head := symbol, right := right }

/-- Push a word across a focused head in scan order.  This accumulator form
is definitionally aligned with repeated head movement and avoids importing
any extensional list-reversal theorem into the proof closure. -/
def pushScannedWorkSymbols : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], farSide => farSide
  | symbol :: rest, farSide =>
      pushScannedWorkSymbols rest (symbol :: farSide)

/-- Repeated keep-and-move-right rules cross exactly the stated finite word.
The theorem is constructive and records the exact transition count. -/
theorem workRunExact?_scanRight_keep (machine : WorkMachine) (state : Nat)
    (left word : List WorkSymbol) (delimiter : WorkSymbol)
    (suffix : List WorkSymbol)
    (hHalted : ∀ tape : WorkTape,
      machine.isHalted ({ state := state, tape := tape } : WorkConfiguration) =
        false)
    (hFind : ∀ symbol, List.Mem symbol word →
      findWorkRule machine.rules state symbol =
        some (cnfKeepRule state symbol state .right)) :
    workRunExact? machine word.length
        { state := state
          tape := WorkTape.beforeRightScan left word delimiter suffix } =
      some
        { state := state
          tape := WorkTape.beforeRightScan (pushScannedWorkSymbols word left) []
            delimiter suffix } := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      have hSelected := hFind symbol (List.Mem.head rest)
      have hStep :
          workStep? machine
              { state := state
                tape := WorkTape.beforeRightScan left (symbol :: rest)
                  delimiter suffix } =
            some
              (applyWorkRule (cnfKeepRule state symbol state .right)
                { state := state
                  tape := WorkTape.beforeRightScan left (symbol :: rest)
                    delimiter suffix }) :=
        workStep?_eq_apply_of_find machine _ _ (hHalted _) hSelected
      have hTail := ih (symbol :: left)
        (fun found foundMem =>
          hFind found (List.Mem.tail symbol foundMem))
      change
        (match workStep? machine
            { state := state
              tape := WorkTape.beforeRightScan left (symbol :: rest)
                delimiter suffix } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep]
      have hNext :
          applyWorkRule (cnfKeepRule state symbol state .right)
              { state := state
                tape := WorkTape.beforeRightScan left (symbol :: rest)
                  delimiter suffix } =
            { state := state
              tape := WorkTape.beforeRightScan (symbol :: left) rest
                delimiter suffix } := by
        cases rest <;> rfl
      rw [hNext]
      exact hTail

/-- Repeated keep-and-move-left rules cross exactly the stated finite word.
The left word is nearest-first, and therefore appears reversed on the right
after the scan. -/
theorem workRunExact?_scanLeft_keep (machine : WorkMachine) (state : Nat)
    (leftSuffix word : List WorkSymbol) (delimiter : WorkSymbol)
    (right : List WorkSymbol)
    (hHalted : ∀ tape : WorkTape,
      machine.isHalted ({ state := state, tape := tape } : WorkConfiguration) =
        false)
    (hFind : ∀ symbol, List.Mem symbol word →
      findWorkRule machine.rules state symbol =
        some (cnfKeepRule state symbol state .left)) :
    workRunExact? machine word.length
        { state := state
          tape := WorkTape.beforeLeftScan leftSuffix word delimiter right } =
      some
        { state := state
          tape := WorkTape.beforeLeftScan leftSuffix [] delimiter
            (pushScannedWorkSymbols word right) } := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
      have hSelected := hFind symbol (List.Mem.head rest)
      have hStep :
          workStep? machine
              { state := state
                tape := WorkTape.beforeLeftScan leftSuffix (symbol :: rest)
                  delimiter right } =
            some
              (applyWorkRule (cnfKeepRule state symbol state .left)
                { state := state
                  tape := WorkTape.beforeLeftScan leftSuffix (symbol :: rest)
                    delimiter right }) :=
        workStep?_eq_apply_of_find machine _ _ (hHalted _) hSelected
      have hTail := ih (symbol :: right)
        (fun found foundMem =>
          hFind found (List.Mem.tail symbol foundMem))
      change
        (match workStep? machine
            { state := state
              tape := WorkTape.beforeLeftScan leftSuffix (symbol :: rest)
                delimiter right } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep]
      have hNext :
          applyWorkRule (cnfKeepRule state symbol state .left)
              { state := state
                tape := WorkTape.beforeLeftScan leftSuffix (symbol :: rest)
                  delimiter right } =
            { state := state
              tape := WorkTape.beforeLeftScan leftSuffix rest delimiter
                (symbol :: right) } := by
        cases rest <;> rfl
      rw [hNext]
      exact hTail

end PNP.Concrete
