/-
Copyright (c) 2026 PNP Labs.

Exact exterior framing for a finite work machine that preserves its left
boundary. The finite trace is reused without equating nonblank exterior data
with implicit blank cells or assuming an unverified execution footprint.
-/

import PNP.Concrete.WorkMachine

namespace PNP.Concrete.WorkMachineLeftBoundary

def Protected (boundary : WorkSymbol) (tape : WorkTape) : Prop :=
  (∃ leftPrefix, tape.left = leftPrefix ++ [boundary]) ∨
    (tape.left = [] ∧ tape.head = boundary)

def RuleSafe (boundary : WorkSymbol) (rule : WorkRule) : Prop :=
  rule.readSymbol = boundary → rule.writeSymbol = boundary ∧ rule.move ≠ .left

def Safe (boundary : WorkSymbol) (machine : WorkMachine) : Prop :=
  ∀ rule ∈ machine.rules, RuleSafe boundary rule

def appendTape (tape : WorkTape) (outside : List WorkSymbol) : WorkTape :=
  { tape with left := tape.left ++ outside }

def appendConfiguration (config : WorkConfiguration) (outside : List WorkSymbol) :
    WorkConfiguration :=
  { config with tape := appendTape config.tape outside }

private theorem find_mem {rules : List WorkRule} {state : Nat} {symbol : WorkSymbol}
    {selected : WorkRule} (hFind : findWorkRule rules state symbol = some selected) :
    selected ∈ rules := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hMatches : first.sourceState = state ∧ first.readSymbol = symbol
      · have hHead := findWorkRule_cons_of_matches first rest state symbol hMatches
        have hEqual : first = selected := Option.some.inj (hHead.symm.trans hFind)
        subst selected
        exact List.Mem.head rest
      · have hTail := findWorkRule_cons_of_not_matches first rest state symbol hMatches
        exact List.Mem.tail first (ih (hTail.symm.trans hFind))

private theorem head_of_left_nil (boundary : WorkSymbol) (tape : WorkTape)
    (hProtected : Protected boundary tape) (hLeft : tape.left = []) :
    tape.head = boundary := by
  rcases hProtected with ⟨leftPrefix, hPrefix⟩ | hHead
  · have hImpossible : ([] : List WorkSymbol) = leftPrefix ++ [boundary] :=
      hLeft.symm.trans hPrefix
    cases leftPrefix with
    | nil => cases hImpossible
    | cons _ _ => cases hImpossible
  · exact hHead.2

private theorem appendTape_write (tape : WorkTape) (symbol : WorkSymbol)
    (outside : List WorkSymbol) :
    appendTape (tape.write symbol) outside = (appendTape tape outside).write symbol := rfl

private theorem appendTape_moveRight (tape : WorkTape) (outside : List WorkSymbol) :
    appendTape tape.moveRight outside = (appendTape tape outside).moveRight := by
  rcases tape with ⟨left, head, right⟩
  cases right <;> rfl

private theorem appendTape_moveLeft (tape : WorkTape) (outside : List WorkSymbol)
    (hLeft : tape.left ≠ []) :
    appendTape tape.moveLeft outside = (appendTape tape outside).moveLeft := by
  cases hTape : tape.left with
  | nil => contradiction
  | cons symbol rest =>
      simp only [appendTape, WorkTape.moveLeft, hTape, List.cons_append]

private theorem protected_apply (boundary : WorkSymbol) (config : WorkConfiguration)
    (rule : WorkRule) (hProtected : Protected boundary config.tape)
    (hBoundary : config.tape.head = boundary →
      rule.writeSymbol = boundary ∧ rule.move ≠ .left) :
    Protected boundary (applyWorkRule rule config).tape := by
  rcases hProtected with ⟨leftPrefix, hPrefix⟩ | hAtBoundary
  · cases hMove : rule.move with
    | stay =>
        exact Or.inl ⟨leftPrefix, by
          simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove, hPrefix]⟩
    | right =>
        exact Or.inl ⟨rule.writeSymbol :: leftPrefix, by
          cases hRight : config.tape.right <;>
            simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveRight, hPrefix, hRight, List.cons_append]⟩
    | left =>
        cases leftPrefix with
        | nil =>
            exact Or.inr (by
              simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveLeft, hPrefix, List.nil_append]
              exact ⟨True.intro, True.intro⟩)
        | cons symbol rest =>
            exact Or.inl ⟨rest, by
              simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveLeft, hPrefix, List.cons_append]⟩
  · have hSafe := hBoundary hAtBoundary.2
    cases hMove : rule.move with
    | left => exact False.elim (hSafe.2 hMove)
    | stay =>
        exact Or.inr (by
          simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
            hAtBoundary.1, hSafe.1]
          exact ⟨True.intro, True.intro⟩)
    | right =>
        exact Or.inl ⟨[], by
          cases hRight : config.tape.right <;>
            simp only [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveRight, hAtBoundary.1, hSafe.1, hRight, List.nil_append]⟩

theorem step_transport (boundary : WorkSymbol) (machine : WorkMachine)
    (hSafe : Safe boundary machine) (config next : WorkConfiguration)
    (outside : List WorkSymbol) (hProtected : Protected boundary config.tape)
    (hStep : workStep? machine config = some next) :
    Protected boundary next.tape ∧
      workStep? machine (appendConfiguration config outside) =
        some (appendConfiguration next outside) := by
  rcases workStep?_some_exists machine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hRule := find_mem hFind
  have hMatches := findWorkRule_some_matches hFind
  have hBoundary : config.tape.head = boundary →
      rule.writeSymbol = boundary ∧ rule.move ≠ .left := by
    intro hHead
    exact hSafe rule hRule (hMatches.2.trans hHead)
  have hNextProtected : Protected boundary next.tape := by
    rw [hNext]
    exact protected_apply boundary config rule hProtected hBoundary
  have hLeftNonempty : rule.move = .left → config.tape.left ≠ [] := by
    intro hMove hLeft
    exact (hBoundary (head_of_left_nil boundary config.tape hProtected hLeft)).2 hMove
  have hTapeCommute :
      appendTape ((config.tape.write rule.writeSymbol).move rule.move) outside =
        ((appendTape config.tape outside).write rule.writeSymbol).move rule.move := by
    cases hMove : rule.move with
    | stay => rfl
    | right =>
        simpa only [WorkTape.move, hMove, appendTape_write] using
          appendTape_moveRight (config.tape.write rule.writeSymbol) outside
    | left =>
        have hNonempty : (config.tape.write rule.writeSymbol).left ≠ [] :=
          hLeftNonempty hMove
        simpa only [WorkTape.move, hMove, appendTape_write] using
          appendTape_moveLeft (config.tape.write rule.writeSymbol) outside hNonempty
  have hHaltedOutside : machine.isHalted (appendConfiguration config outside) = false :=
    hHalted
  have hFindOutside :
      findWorkRule machine.rules (appendConfiguration config outside).state
        (appendConfiguration config outside).tape.head = some rule := hFind
  have hOutsideStep := workStep?_eq_apply_of_find machine
    (appendConfiguration config outside) rule hHaltedOutside hFindOutside
  refine ⟨hNextProtected, ?_⟩
  rw [hOutsideStep]
  apply congrArg Option.some
  rw [hNext]
  cases config
  simp only [appendConfiguration, applyWorkRule]
  exact congrArg (fun tape => WorkConfiguration.mk rule.targetState tape) hTapeCommute.symm

/-- The exact same transition count and terminal state, with the complete exterior retained. -/
theorem workRunExact_transport (boundary : WorkSymbol) (machine : WorkMachine)
    (hSafe : Safe boundary machine) (steps : Nat) (initial final : WorkConfiguration)
    (outside : List WorkSymbol) (hProtected : Protected boundary initial.tape)
    (hRun : workRunExact? machine steps initial = some final) :
    workRunExact? machine steps (appendConfiguration initial outside) =
      some (appendConfiguration final outside) := by
  induction steps generalizing initial with
  | zero =>
      have hEqual : initial = final := Option.some.inj hRun
      subst initial
      rfl
  | succ steps ih =>
      cases hStep : workStep? machine initial with
      | none =>
          simp only [workRunExact?, hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine steps next = some final := by
            simpa only [workRunExact?, hStep] using hRun
          have hTransport := step_transport boundary machine hSafe initial next outside hProtected hStep
          simp only [workRunExact?, hTransport.2]
          exact ih next hTransport.1 hTail

end PNP.Concrete.WorkMachineLeftBoundary
