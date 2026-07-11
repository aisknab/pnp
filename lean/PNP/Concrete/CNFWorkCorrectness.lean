/-
Copyright (c) 2026 PNP Labs.

Universal operational correctness of the literal CNF work machine.  This
module keeps the proof at the finite rule-list interpreter boundary: phase
invariants describe concrete work tapes, exact traces are composed, and only
then is the generic six-raw-steps compiler theorem applied.
-/

import PNP.Concrete.CNFWorkFrameCorrectness
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

/-- Focus the first symbol of a finite right word, or the implicit blank when
the word is empty. -/
def atWord (leftSide : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => focus leftSide WorkSymbol.blank []
  | head :: suffix => focus leftSide head suffix

/-- Focus the first symbol encountered while scanning left.  The tail is
stored directly as the nearest-first left stack. -/
def atLeftWord (rightSide : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => focus [] WorkSymbol.blank rightSide
  | head :: leftTail => focus leftTail head rightSide

end WorkTape

/-- Configuration focused at the first symbol of a finite right word. -/
def workConfigAtWord (state : Nat) (leftSide word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := WorkTape.atWord leftSide word }

/-- Configuration focused at the first symbol of a nearest-first left word. -/
def workConfigAtLeftWord (state : Nat) (leftWord rightSide : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := WorkTape.atLeftWord rightSide leftWord }

/-- Push an ordinary left-to-right scanned word onto a nearest-first left
stack. -/
def pushWorkLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], leftSide => leftSide
  | symbol :: rest, leftSide => pushWorkLeft rest (symbol :: leftSide)

theorem pushWorkLeft_cons (symbol : WorkSymbol) (rest leftSide : List WorkSymbol) :
    pushWorkLeft (symbol :: rest) leftSide =
      pushWorkLeft rest (symbol :: leftSide) := rfl

/-- Generic exact right scan.  The premise is a literal interpreter step for
every allowed focused symbol; the theorem performs no semantic shortcut. -/
theorem workRunExact?_scanRight (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine (workConfigAtWord state leftSide (head :: suffix)) =
        some (workConfigAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtWord state leftSide (word ++ suffix)) =
      some (workConfigAtWord state (pushWorkLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (workConfigAtWord state leftSide (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

/-- Generic exact left scan, dual to `workRunExact?_scanRight`. -/
theorem workRunExact?_scanLeft (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (workConfigAtLeftWord state (head :: leftTail) rightSide) =
        some (workConfigAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord state leftSuffix
        (pushWorkLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (workConfigAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

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

/-! ### Symbol classes used by the phase invariants -/

inductive FormulaScanSymbol : WorkSymbol → Prop where
  | markTrue : FormulaScanSymbol cnfMarkTrue
  | f : FormulaScanSymbol cnfF
  | t : FormulaScanSymbol cnfT
  | sep : FormulaScanSymbol cnfSep
  | finish : FormulaScanSymbol cnfFinish

inductive AssignmentMarkSymbol : WorkSymbol → Prop where
  | markFalse : AssignmentMarkSymbol cnfMarkFalse
  | markTrue : AssignmentMarkSymbol cnfMarkTrue

inductive FormulaOrCounterSymbol : WorkSymbol → Prop where
  | markFalse : FormulaOrCounterSymbol cnfMarkFalse
  | markTrue : FormulaOrCounterSymbol cnfMarkTrue
  | f : FormulaOrCounterSymbol cnfF
  | t : FormulaOrCounterSymbol cnfT
  | sep : FormulaOrCounterSymbol cnfSep
  | finish : FormulaOrCounterSymbol cnfFinish

theorem cnfTokenWorkSymbol_formulaScan (token : CNFToken) :
    FormulaScanSymbol token.workSymbol := by
  cases token with
  | f => exact .f
  | t => exact .t
  | sep => exact .sep
  | finish => exact .finish

theorem cnfTokenWorkSymbols_formulaScan (tokens : List CNFToken)
    (symbol : WorkSymbol) (found : List.Mem symbol (cnfTokenWorkSymbols tokens)) :
    FormulaScanSymbol symbol := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases found with
      | head => exact cnfTokenWorkSymbol_formulaScan token
      | tail _ tailFound => exact ih tailFound

/-- Marked assignment values preserve enough information for exact restore. -/
def markedAssignmentWorkSymbols : BitString → List WorkSymbol
  | [] => []
  | false :: rest => cnfMarkFalse :: markedAssignmentWorkSymbols rest
  | true :: rest => cnfMarkTrue :: markedAssignmentWorkSymbols rest

def assignmentWorkSymbols : BitString → List WorkSymbol
  | [] => []
  | false :: rest => cnfF :: assignmentWorkSymbols rest
  | true :: rest => cnfT :: assignmentWorkSymbols rest

theorem assignmentValueTokens_workSymbols (assignment : BitString) :
    cnfTokenWorkSymbols (assignmentValueTokens assignment) =
      assignmentWorkSymbols assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact congrArg (List.cons _) ih

theorem markedAssignmentWorkSymbols_allowed (assignment : BitString)
    (symbol : WorkSymbol)
    (found : List.Mem symbol (markedAssignmentWorkSymbols assignment)) :
    AssignmentMarkSymbol symbol := by
  induction assignment with
  | nil => contradiction
  | cons value rest ih =>
      cases value with
      | false =>
          cases found with
          | head => exact .markFalse
          | tail _ tailFound => exact ih tailFound
      | true =>
          cases found with
          | head => exact .markTrue
          | tail _ tailFound => exact ih tailFound

theorem assignmentWorkSymbols_length (assignment : BitString) :
    (assignmentWorkSymbols assignment).length = assignment.length := by
  induction assignment with
  | nil => rfl
  | cons value rest ih => cases value <;> exact congrArg Nat.succ ih

theorem markedAssignmentWorkSymbols_length (assignment : BitString) :
    (markedAssignmentWorkSymbols assignment).length = assignment.length := by
  induction assignment with
  | nil => rfl
  | cons value rest ih => cases value <;> exact congrArg Nat.succ ih

/-! ### Strict codec canonicality used by the all-pairs split -/

theorem encodeTokenPairs_of_decode (bits : BitString) (tokens : List CNFToken)
    (decoded : decodeTokenPairs bits = some tokens) :
    encodeTokenPairs tokens = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => contradiction
          | cons second rest =>
              change (match decodeTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) = some []
                  at decoded
              cases hRest : decodeTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have impossible : CNFToken.ofBits first second :: suffix = [] :=
                    Option.some.inj decoded
                  cases impossible
  | cons token tokens ih =>
      cases bits with
      | nil =>
          change some [] = some (token :: tokens) at decoded
          have impossible : [] = token :: tokens := Option.some.inj decoded
          cases impossible
      | cons first tail =>
          cases tail with
          | nil => contradiction
          | cons second rest =>
              change (match decodeTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) =
                  some (token :: tokens) at decoded
              cases hRest : decodeTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have hCons : CNFToken.ofBits first second :: suffix =
                      token :: tokens := Option.some.inj decoded
                  have hToken : CNFToken.ofBits first second = token :=
                    List.cons.inj hCons |>.1
                  have hSuffix : suffix = tokens := List.cons.inj hCons |>.2
                  cases hSuffix
                  have hTail := ih rest hRest
                  cases first <;> cases second <;> cases hToken <;>
                    exact congrArg (List.cons _ ∘ List.cons _) hTail

theorem encodeFormulaTokenPairs_of_decode (bits : BitString)
    (tokens : List CNFToken)
    (decoded : decodeFormulaTokenPairs bits = some tokens) :
    encodeTokenPairs tokens ++ [false] = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil => contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false => rfl
              | true => contradiction
          | cons second rest =>
              change (match decodeFormulaTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) = some []
                  at decoded
              cases hRest : decodeFormulaTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have impossible : CNFToken.ofBits first second :: suffix = [] :=
                    Option.some.inj decoded
                  cases impossible
  | cons token tokens ih =>
      cases bits with
      | nil => contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false =>
                  change some [] = some (token :: tokens) at decoded
                  have impossible : [] = token :: tokens :=
                    Option.some.inj decoded
                  cases impossible
              | true => contradiction
          | cons second rest =>
              change (match decodeFormulaTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) =
                  some (token :: tokens) at decoded
              cases hRest : decodeFormulaTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have hCons : CNFToken.ofBits first second :: suffix =
                      token :: tokens := Option.some.inj decoded
                  have hToken : CNFToken.ofBits first second = token :=
                    List.cons.inj hCons |>.1
                  have hSuffix : suffix = tokens := List.cons.inj hCons |>.2
                  cases hSuffix
                  have hTail := ih rest hRest
                  cases first <;> cases second <;> cases hToken <;>
                    exact congrArg (List.cons _ ∘ List.cons _) hTail

theorem encodeAssignmentCertificate_of_decode (certificate : BitString)
    (assignment : BitString)
    (decoded : decodeAssignmentCertificate certificate = some assignment) :
    encodeAssignmentCertificate assignment = certificate := by
  unfold decodeAssignmentCertificate at decoded
  cases hTokens : decodeTokenPairs certificate with
  | none => rw [hTokens] at decoded; contradiction
  | some tokens =>
      rw [hTokens] at decoded
      unfold encodeAssignmentCertificate
      rw [encodeAssignmentTokens_of_decode tokens assignment decoded]
      exact encodeTokenPairs_of_decode certificate tokens hTokens

/-! ### Width-phase literal interpreter steps -/

theorem widthToBoundary_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthToBoundary
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthDoneToBoundary_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneToBoundary
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthPastCounter_step (leftSide : List WorkSymbol)
    (suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthPastCertificateCounter leftSide
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthPastCertificateCounter
        (cnfMarkFalse :: leftSide) suffix) := by
  rfl

theorem widthFindAssignment_mark_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindAssignment leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindAssignment
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthDoneCheckAssignment_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDoneCheckAssignment leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthBackAssignment_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackAssignment
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackAssignment
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

theorem widthBackCounter_step (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
          (cnfMarkFalse :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
        leftTail (cnfMarkFalse :: rightSide)) := by
  rfl

theorem widthBackFormula_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : FormulaOrCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackFormula
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackFormula
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

theorem widthRestoreBackFormula_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : FormulaOrCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

end PNP.Concrete
