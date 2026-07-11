/-
Copyright (c) 2026 PNP Labs.

A finite nine-symbol work machine and a literal compiler to the concrete
three-symbol single-tape machine.  A work symbol is exactly a pair of raw
tape symbols.  The compiler implements one work transition by six raw
transitions; neither the source machine nor the compiled machine contains a
Lean function as executable program data.
-/

import PNP.Concrete.Machine

namespace PNP.Concrete

instance : ReflBEq TapeSymbol where
  rfl := by
    intro symbol
    cases symbol <;> rfl

instance : LawfulBEq TapeSymbol where
  eq_of_beq := by
    intro left right h
    cases left <;> cases right <;> first | rfl | contradiction

/-- The nine-symbol alphabet used by the readable work-machine layer. -/
structure WorkSymbol where
  first : TapeSymbol
  second : TapeSymbol
deriving BEq, DecidableEq, Repr

instance : ReflBEq WorkSymbol where
  rfl := by
    rintro ⟨first, second⟩
    cases first <;> cases second <;> rfl

instance : LawfulBEq WorkSymbol where
  eq_of_beq := by
    rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩ h
    cases leftFirst <;> cases leftSecond <;>
      cases rightFirst <;> cases rightSecond <;>
      first | rfl | contradiction

namespace WorkSymbol

def blank : WorkSymbol := ⟨.blank, .blank⟩
def blankZero : WorkSymbol := ⟨.blank, .zero⟩
def blankOne : WorkSymbol := ⟨.blank, .one⟩
def zeroBlank : WorkSymbol := ⟨.zero, .blank⟩
def zeroZero : WorkSymbol := ⟨.zero, .zero⟩
def zeroOne : WorkSymbol := ⟨.zero, .one⟩
def oneBlank : WorkSymbol := ⟨.one, .blank⟩
def oneZero : WorkSymbol := ⟨.one, .zero⟩
def oneOne : WorkSymbol := ⟨.one, .one⟩

end WorkSymbol

/-- One transition in a finite work-machine program. -/
structure WorkRule where
  sourceState : Nat
  readSymbol : WorkSymbol
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove
deriving BEq, DecidableEq, Repr

/-- A work tape focused at one two-cell work symbol. -/
structure WorkTape where
  left : List WorkSymbol
  head : WorkSymbol
  right : List WorkSymbol
deriving BEq, DecidableEq, Repr

namespace WorkTape

def blank : WorkTape :=
  { left := [], head := WorkSymbol.blank, right := [] }

def write (tape : WorkTape) (symbol : WorkSymbol) : WorkTape :=
  { tape with head := symbol }

def moveLeft (tape : WorkTape) : WorkTape :=
  match tape.left with
  | [] =>
      { left := []
        head := WorkSymbol.blank
        right := tape.head :: tape.right }
  | symbol :: rest =>
      { left := rest
        head := symbol
        right := tape.head :: tape.right }

def moveRight (tape : WorkTape) : WorkTape :=
  match tape.right with
  | [] =>
      { left := tape.head :: tape.left
        head := WorkSymbol.blank
        right := [] }
  | symbol :: rest =>
      { left := tape.head :: tape.left
        head := symbol
        right := rest }

def move (tape : WorkTape) : HeadMove → WorkTape
  | .left => tape.moveLeft
  | .stay => tape
  | .right => tape.moveRight

end WorkTape

structure WorkConfiguration where
  state : Nat
  tape : WorkTape
deriving BEq, DecidableEq, Repr

/-- Finite syntax for a deterministic work machine. -/
structure WorkMachine where
  rules : List WorkRule
  startState : Nat
  acceptState : Nat
  rejectState : Nat
deriving BEq, DecidableEq, Repr

/-- First matching work rule, paired with its zero-based list index. -/
private inductive WorkRuleMatch (rule : WorkRule) (state : Nat)
    (symbol : WorkSymbol) where
  | no
  | yes (source_eq : rule.sourceState = state)
      (symbol_eq : rule.readSymbol = symbol)

private def inspectWorkRule (rule : WorkRule) (state : Nat)
    (symbol : WorkSymbol) : WorkRuleMatch rule state symbol :=
  if hSource : rule.sourceState = state then
    if hSymbol : rule.readSymbol = symbol then
      .yes hSource hSymbol
    else
      .no
  else
    .no

def findIndexedWorkRuleFrom :
    List WorkRule → Nat → WorkSymbol → Nat → Option (Nat × WorkRule)
  | [], _, _, _ => none
  | rule :: rest, state, symbol, index =>
      match inspectWorkRule rule state symbol with
      | .yes _ _ => some (index, rule)
      | .no => findIndexedWorkRuleFrom rest state symbol (index + 1)

def findIndexedWorkRule (rules : List WorkRule) (state : Nat)
    (symbol : WorkSymbol) : Option (Nat × WorkRule) :=
  findIndexedWorkRuleFrom rules state symbol 0

def findWorkRule : List WorkRule → Nat → WorkSymbol → Option WorkRule
  | [], _, _ => none
  | rule :: rest, state, symbol =>
      match inspectWorkRule rule state symbol with
      | .yes _ _ => some rule
      | .no => findWorkRule rest state symbol

theorem findIndexedWorkRuleFrom_some_matches
    {rules : List WorkRule} {state : Nat} {symbol : WorkSymbol}
    {index foundIndex : Nat} {rule : WorkRule}
    (h : findIndexedWorkRuleFrom rules state symbol index =
      some (foundIndex, rule)) :
    rule.sourceState = state ∧ rule.readSymbol = symbol := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      unfold findIndexedWorkRuleFrom at h
      cases hMatch : inspectWorkRule first state symbol with
      | no =>
          rw [hMatch] at h
          exact ih h
      | yes hFirstSource hFirstSymbol =>
          rw [hMatch] at h
          have hPair : (index, first) = (foundIndex, rule) :=
            Option.some.inj h
          have hRule : first = rule := congrArg Prod.snd hPair
          exact
            ⟨(congrArg WorkRule.sourceState hRule).symm.trans hFirstSource,
             (congrArg WorkRule.readSymbol hRule).symm.trans hFirstSymbol⟩

theorem findWorkRule_cons_of_matches (rule : WorkRule)
    (rest : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (h : rule.sourceState = state ∧ rule.readSymbol = symbol) :
    findWorkRule (rule :: rest) state symbol = some rule := by
  change (match inspectWorkRule rule state symbol with
    | .yes _ _ => some rule
    | .no => findWorkRule rest state symbol) = some rule
  have hInspect : inspectWorkRule rule state symbol = .yes h.1 h.2 := by
    unfold inspectWorkRule
    rw [dif_pos h.1, dif_pos h.2]
  rw [hInspect]

theorem findWorkRule_cons_of_not_matches (rule : WorkRule)
    (rest : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (h : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findWorkRule (rule :: rest) state symbol =
      findWorkRule rest state symbol := by
  change (match inspectWorkRule rule state symbol with
    | .yes _ _ => some rule
    | .no => findWorkRule rest state symbol) = findWorkRule rest state symbol
  by_cases hSource : rule.sourceState = state
  · have hSymbol : rule.readSymbol ≠ symbol := by
      intro hRead
      exact h ⟨hSource, hRead⟩
    have hInspect : inspectWorkRule rule state symbol = .no := by
      unfold inspectWorkRule
      rw [dif_pos hSource, dif_neg hSymbol]
    rw [hInspect]
  · have hInspect : inspectWorkRule rule state symbol = .no := by
      unfold inspectWorkRule
      rw [dif_neg hSource]
    rw [hInspect]

theorem findWorkRule_append_of_some (left right : List WorkRule)
    (state : Nat) (symbol : WorkSymbol) (selected : WorkRule)
    (h : findWorkRule left state symbol = some selected) :
    findWorkRule (left ++ right) state symbol = some selected := by
  induction left with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hFirst
        have hSelected : first = selected := Option.some.inj (hCons.symm.trans h)
        have hAppend := findWorkRule_cons_of_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (congrArg Option.some hSelected)
      · have hCons := findWorkRule_cons_of_not_matches first rest state symbol hFirst
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans h
        have hAppend := findWorkRule_cons_of_not_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (ih hTail)

theorem findWorkRule_append_of_none (left right : List WorkRule)
    (state : Nat) (symbol : WorkSymbol)
    (h : findWorkRule left state symbol = none) :
    findWorkRule (left ++ right) state symbol = findWorkRule right state symbol := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      by_cases hFirst : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hFirst
        have impossible : (some first : Option WorkRule) = none := hCons.symm.trans h
        contradiction
      · have hCons := findWorkRule_cons_of_not_matches first rest state symbol hFirst
        have hTail : findWorkRule rest state symbol = none := hCons.symm.trans h
        have hAppend := findWorkRule_cons_of_not_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (ih hTail)

def WorkMachine.isHalted (machine : WorkMachine)
    (config : WorkConfiguration) : Bool :=
  config.state == machine.acceptState || config.state == machine.rejectState

def workStartConfiguration (machine : WorkMachine) (tape : WorkTape) :
    WorkConfiguration :=
  { state := machine.startState, tape := tape }

def applyWorkRule (rule : WorkRule) (config : WorkConfiguration) :
    WorkConfiguration :=
  { state := rule.targetState
    tape := (config.tape.write rule.writeSymbol).move rule.move }

def workStep? (machine : WorkMachine) (config : WorkConfiguration) :
    Option WorkConfiguration :=
  if machine.isHalted config then
    none
  else
    match findWorkRule machine.rules config.state config.tape.head with
    | none => none
    | some rule => some (applyWorkRule rule config)

theorem workStep?_eq_apply_of_find (machine : WorkMachine)
    (config : WorkConfiguration) (rule : WorkRule)
    (hHalted : machine.isHalted config = false)
    (hFind : findWorkRule machine.rules config.state config.tape.head = some rule) :
    workStep? machine config = some (applyWorkRule rule config) := by
  have hNotHalted : ¬(machine.isHalted config = true) := by
    intro hTrue
    have impossible : false = true := hHalted.symm.trans hTrue
    contradiction
  have hOuter : workStep? machine config =
      match findWorkRule machine.rules config.state config.tape.head with
      | none => none
      | some selected => some (applyWorkRule selected config) := by
    unfold workStep?
    exact if_neg hNotHalted
  have hInner :
      (match findWorkRule machine.rules config.state config.tape.head with
       | none => none
       | some selected => some (applyWorkRule selected config)) =
      some (applyWorkRule rule config) := by
    exact congrArg
      (fun found => match found with
        | none => none
        | some selected => some (applyWorkRule selected config)) hFind
  exact hOuter.trans hInner

def workRun (machine : WorkMachine) : Nat → WorkConfiguration → WorkConfiguration
  | 0, config => config
  | fuel + 1, config =>
      match workStep? machine config with
      | none => config
      | some next => workRun machine fuel next

/-- Execute exactly `steps` transitions, failing when execution stops early. -/
def workRunExact? (machine : WorkMachine) :
    Nat → WorkConfiguration → Option WorkConfiguration
  | 0, config => some config
  | steps + 1, config =>
      match workStep? machine config with
      | none => none
      | some next => workRunExact? machine steps next

inductive WorkVerdict where
  | accept
  | reject
  | timeout
deriving BEq, DecidableEq, Repr

def workBoundedDecide (machine : WorkMachine) (fuel : Nat)
    (initialTape : WorkTape) : WorkVerdict :=
  let final := workRun machine fuel (workStartConfiguration machine initialTape)
  if final.state == machine.acceptState then
    .accept
  else if final.state == machine.rejectState then
    .reject
  else
    .timeout

/-! ### Literal two-cell encoding -/

/-- Raw cells strictly to the left of a work focus, nearest first. -/
def encodeWorkLeft : List WorkSymbol → List TapeSymbol
  | [] => []
  | symbol :: rest => symbol.second :: symbol.first :: encodeWorkLeft rest

/-- Raw cells strictly to the right of a work focus, ordinary left-to-right. -/
def encodeWorkRight : List WorkSymbol → List TapeSymbol
  | [] => []
  | symbol :: rest => symbol.first :: symbol.second :: encodeWorkRight rest

/-- Encode a focused work tape with the raw head on the first component. -/
def encodeWorkTape (tape : WorkTape) : Tape :=
  { left := encodeWorkLeft tape.left
    head := tape.head.first
    right := tape.head.second :: encodeWorkRight tape.right }

theorem decide_true_iff_constructive (proposition : Prop)
    (decision : Decidable proposition) :
    @decide proposition decision = true ↔ proposition := by
  cases decision with
  | isFalse hFalse =>
      exact
        ⟨fun impossible => False.elim (by contradiction),
         fun hTrue => False.elim (hFalse hTrue)⟩
  | isTrue hTrue => exact ⟨fun _ => hTrue, fun _ => rfl⟩

theorem nat_beq_true_iff (left right : Nat) :
    (left == right) = true ↔ left = right := by
  change decide (left = right) = true ↔ left = right
  exact decide_true_iff_constructive (left = right)
    (inferInstanceAs (Decidable (left = right)))

theorem tapeSymbol_beq_true_iff (left right : TapeSymbol) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => False.elim (by contradiction),
        fun h => False.elim (by contradiction)⟩

theorem rawRule_match_iff (rule : Rule) (state : Nat)
    (symbol : TapeSymbol) :
    ((rule.sourceState == state) && (rule.readSymbol == symbol)) = true ↔
      rule.sourceState = state ∧ rule.readSymbol = symbol := by
  constructor
  · intro h
    have hSource : (rule.sourceState == state) = true := by
      cases hValue : (rule.sourceState == state) with
      | false => rw [hValue] at h; contradiction
      | true => rfl
    have hSymbol : (rule.readSymbol == symbol) = true := by
      rw [hSource] at h
      exact h
    exact ⟨nat_beq_true_iff _ _ |>.mp hSource,
      tapeSymbol_beq_true_iff _ _ |>.mp hSymbol⟩
  · intro h
    rcases h with ⟨hSource, hSymbol⟩
    cases hSource
    cases hSymbol
    have hSourceRefl := nat_beq_true_iff rule.sourceState rule.sourceState |>.mpr rfl
    have hSymbolRefl := tapeSymbol_beq_true_iff rule.readSymbol rule.readSymbol |>.mpr rfl
    rw [hSourceRefl, hSymbolRefl]
    rfl

theorem findRule_cons_of_matches (rule : Rule) (rest : List Rule)
    (state : Nat) (symbol : TapeSymbol)
    (h : rule.sourceState = state ∧ rule.readSymbol = symbol) :
    findRule (rule :: rest) state symbol = some rule := by
  change (if ((rule.sourceState == state) && (rule.readSymbol == symbol)) = true
    then some rule else findRule rest state symbol) = some rule
  exact if_pos (rawRule_match_iff rule state symbol |>.mpr h)

theorem findRule_cons_of_not_matches (rule : Rule) (rest : List Rule)
    (state : Nat) (symbol : TapeSymbol)
    (h : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (rule :: rest) state symbol = findRule rest state symbol := by
  change (if ((rule.sourceState == state) && (rule.readSymbol == symbol)) = true
    then some rule else findRule rest state symbol) = findRule rest state symbol
  exact if_neg (fun hBool => h (rawRule_match_iff rule state symbol |>.mp hBool))

theorem findRule_append_of_some (left right : List Rule) (state : Nat)
    (symbol : TapeSymbol) (selected : Rule)
    (h : findRule left state symbol = some selected) :
    findRule (left ++ right) state symbol = some selected := by
  induction left with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst :
          first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findRule_cons_of_matches first rest state symbol hFirst
        have hSelected : first = selected :=
          Option.some.inj (hCons.symm.trans h)
        have hAppend := findRule_cons_of_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (congrArg Option.some hSelected)
      · have hCons := findRule_cons_of_not_matches first rest state symbol hFirst
        have hTail : findRule rest state symbol = some selected :=
          hCons.symm.trans h
        have hAppend := findRule_cons_of_not_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (ih hTail)

theorem findRule_append_of_none (left right : List Rule) (state : Nat)
    (symbol : TapeSymbol)
    (h : findRule left state symbol = none) :
    findRule (left ++ right) state symbol = findRule right state symbol := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      by_cases hFirst :
          first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findRule_cons_of_matches first rest state symbol hFirst
        have impossible : (some first : Option Rule) = none := hCons.symm.trans h
        contradiction
      · have hCons := findRule_cons_of_not_matches first rest state symbol hFirst
        have hTail : findRule rest state symbol = none := hCons.symm.trans h
        have hAppend := findRule_cons_of_not_matches first (rest ++ right)
          state symbol hFirst
        exact hAppend.trans (ih hTail)

/-! ### Compiler state and finite rule syntax -/

private def tripleKey : Nat → TapeSymbol → Nat
  | 0, .blank => 0
  | 0, .zero => 1
  | 0, .one => 2
  | state + 1, symbol =>
      Nat.succ (Nat.succ (Nat.succ (tripleKey state symbol)))

private theorem tripleKey_zero_ne_succ3 (symbol : TapeSymbol) (n : Nat) :
    tripleKey 0 symbol ≠ Nat.succ (Nat.succ (Nat.succ n)) := by
  intro h
  cases symbol with
  | blank => contradiction
  | zero =>
      have hInner := Nat.succ.inj h
      contradiction
  | one =>
      have hInner := Nat.succ.inj (Nat.succ.inj h)
      contradiction

private theorem tripleKey_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : TapeSymbol}
    (h : tripleKey leftState leftSymbol = tripleKey rightState rightSymbol) :
    leftState = rightState ∧ leftSymbol = rightSymbol := by
  induction leftState generalizing rightState with
  | zero =>
      cases rightState with
      | zero =>
          cases leftSymbol <;> cases rightSymbol <;>
            first | exact ⟨rfl, rfl⟩ | contradiction
      | succ rightState =>
          exact False.elim
            (tripleKey_zero_ne_succ3 leftSymbol
              (tripleKey rightState rightSymbol) h)
  | succ leftState ih =>
      cases rightState with
      | zero =>
          exact False.elim
            (tripleKey_zero_ne_succ3 rightSymbol
              (tripleKey leftState leftSymbol) h.symm)
      | succ rightState =>
          have hInner := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))
          have hParts := ih hInner
          exact ⟨congrArg Nat.succ hParts.1, hParts.2⟩

private inductive CompilerTag where
  | boundary
  | dispatch
  | selected
  | written
  | moved
  | finished
deriving DecidableEq

private def taggedState : Nat → CompilerTag → Nat
  | 0, .boundary => 0
  | 0, .dispatch => 1
  | 0, .selected => 2
  | 0, .written => 3
  | 0, .moved => 4
  | 0, .finished => 5
  | payload + 1, tag =>
      Nat.succ (Nat.succ (Nat.succ (Nat.succ
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (taggedState payload tag))))))))

private theorem taggedState_zero_ne_succ8 (tag : CompilerTag) (n : Nat) :
    taggedState 0 tag ≠
      Nat.succ (Nat.succ (Nat.succ (Nat.succ
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))))) := by
  intro h
  cases tag with
  | boundary => contradiction
  | dispatch =>
      have hInner := Nat.succ.inj h
      contradiction
  | selected =>
      have hInner := Nat.succ.inj (Nat.succ.inj h)
      contradiction
  | written =>
      have hInner := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))
      contradiction
  | moved =>
      have hInner := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj h)))
      contradiction
  | finished =>
      have hInner := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj (Nat.succ.inj h))))
      contradiction

private theorem taggedState_injective {leftPayload rightPayload : Nat}
    {leftTag rightTag : CompilerTag}
    (h : taggedState leftPayload leftTag = taggedState rightPayload rightTag) :
    leftPayload = rightPayload ∧ leftTag = rightTag := by
  induction leftPayload generalizing rightPayload with
  | zero =>
      cases rightPayload with
      | zero =>
          cases leftTag <;> cases rightTag <;>
            first | exact ⟨rfl, rfl⟩ | contradiction
      | succ rightPayload =>
          exact False.elim
            (taggedState_zero_ne_succ8 leftTag
              (taggedState rightPayload rightTag) h)
  | succ leftPayload ih =>
      cases rightPayload with
      | zero =>
          exact False.elim
            (taggedState_zero_ne_succ8 rightTag
              (taggedState leftPayload leftTag) h.symm)
      | succ rightPayload =>
          have hInner := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
            (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
              (Nat.succ.inj (Nat.succ.inj h)))))))
          have hParts := ih hInner
          exact ⟨congrArg Nat.succ hParts.1, hParts.2⟩

private def boundaryState (state : Nat) : Nat :=
  taggedState state .boundary

private def dispatchState (state : Nat) (first : TapeSymbol) : Nat :=
  taggedState (tripleKey state first) .dispatch

private def selectedPayload (state : Nat) (symbol : WorkSymbol) : Nat :=
  tripleKey (tripleKey state symbol.first) symbol.second

private def selectedState (state : Nat) (symbol : WorkSymbol) : Nat → Nat
  | 2 => taggedState (selectedPayload state symbol) .selected
  | 3 => taggedState (selectedPayload state symbol) .written
  | 4 => taggedState (selectedPayload state symbol) .moved
  | 5 => taggedState (selectedPayload state symbol) .finished
  | _ => taggedState (selectedPayload state symbol) .selected

private theorem taggedState_ne_of_tag_ne {leftPayload rightPayload : Nat}
    {leftTag rightTag : CompilerTag} (hTag : leftTag ≠ rightTag) :
    taggedState leftPayload leftTag ≠ taggedState rightPayload rightTag := by
  intro h
  exact hTag (taggedState_injective h).2

private theorem boundaryState_injective {left right : Nat}
    (h : boundaryState left = boundaryState right) : left = right :=
  (taggedState_injective h).1

private theorem dispatchState_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : TapeSymbol}
    (h : dispatchState leftState leftSymbol =
      dispatchState rightState rightSymbol) :
    leftState = rightState ∧ leftSymbol = rightSymbol :=
  tripleKey_injective (taggedState_injective h).1

private theorem selectedPayload_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : WorkSymbol}
    (h : selectedPayload leftState leftSymbol =
      selectedPayload rightState rightSymbol) :
    leftState = rightState ∧ leftSymbol = rightSymbol := by
  have hOuter := tripleKey_injective h
  have hInner := tripleKey_injective hOuter.1
  cases leftSymbol with
  | mk leftFirst leftSecond =>
      cases rightSymbol with
      | mk rightFirst rightSecond =>
          have hFirst : leftFirst = rightFirst := hInner.2
          have hSecond : leftSecond = rightSecond := hOuter.2
          cases hFirst
          cases hSecond
          exact ⟨hInner.1, rfl⟩

private theorem selectedState_two_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : WorkSymbol}
    (h : selectedState leftState leftSymbol 2 =
      selectedState rightState rightSymbol 2) :
    leftState = rightState ∧ leftSymbol = rightSymbol :=
  selectedPayload_injective (taggedState_injective h).1

private theorem selectedState_three_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : WorkSymbol}
    (h : selectedState leftState leftSymbol 3 =
      selectedState rightState rightSymbol 3) :
    leftState = rightState ∧ leftSymbol = rightSymbol :=
  selectedPayload_injective (taggedState_injective h).1

private theorem selectedState_four_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : WorkSymbol}
    (h : selectedState leftState leftSymbol 4 =
      selectedState rightState rightSymbol 4) :
    leftState = rightState ∧ leftSymbol = rightSymbol :=
  selectedPayload_injective (taggedState_injective h).1

private theorem selectedState_five_injective {leftState rightState : Nat}
    {leftSymbol rightSymbol : WorkSymbol}
    (h : selectedState leftState leftSymbol 5 =
      selectedState rightState rightSymbol 5) :
    leftState = rightState ∧ leftSymbol = rightSymbol :=
  selectedPayload_injective (taggedState_injective h).1

private theorem boundary_ne_dispatch (state otherState : Nat)
    (symbol : TapeSymbol) :
    boundaryState state ≠ dispatchState otherState symbol :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem boundary_ne_selected_two (state otherState : Nat)
    (symbol : WorkSymbol) :
    boundaryState state ≠ selectedState otherState symbol 2 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem boundary_ne_selected_three (state otherState : Nat)
    (symbol : WorkSymbol) :
    boundaryState state ≠ selectedState otherState symbol 3 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem boundary_ne_selected_four (state otherState : Nat)
    (symbol : WorkSymbol) :
    boundaryState state ≠ selectedState otherState symbol 4 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem boundary_ne_selected_five (state otherState : Nat)
    (symbol : WorkSymbol) :
    boundaryState state ≠ selectedState otherState symbol 5 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem dispatch_ne_selected_two (state : Nat) (raw : TapeSymbol)
    (otherState : Nat) (symbol : WorkSymbol) :
    dispatchState state raw ≠ selectedState otherState symbol 2 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem dispatch_ne_selected_three (state : Nat) (raw : TapeSymbol)
    (otherState : Nat) (symbol : WorkSymbol) :
    dispatchState state raw ≠ selectedState otherState symbol 3 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem dispatch_ne_selected_four (state : Nat) (raw : TapeSymbol)
    (otherState : Nat) (symbol : WorkSymbol) :
    dispatchState state raw ≠ selectedState otherState symbol 4 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem dispatch_ne_selected_five (state : Nat) (raw : TapeSymbol)
    (otherState : Nat) (symbol : WorkSymbol) :
    dispatchState state raw ≠ selectedState otherState symbol 5 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_two_ne_three (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 2 ≠ selectedState otherState otherSymbol 3 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_two_ne_four (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 2 ≠ selectedState otherState otherSymbol 4 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_two_ne_five (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 2 ≠ selectedState otherState otherSymbol 5 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_three_ne_four (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 3 ≠ selectedState otherState otherSymbol 4 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_three_ne_five (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 3 ≠ selectedState otherState otherSymbol 5 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private theorem selected_four_ne_five (state : Nat) (symbol : WorkSymbol)
    (otherState : Nat) (otherSymbol : WorkSymbol) :
    selectedState state symbol 4 ≠ selectedState otherState otherSymbol 5 :=
  taggedState_ne_of_tag_ne (by intro impossible; contradiction)

private def rawSymbols : List TapeSymbol := [.blank, .zero, .one]

private def preserveRule (source target : Nat) (movement : HeadMove)
    (symbol : TapeSymbol) : Rule :=
  { sourceState := source
    readSymbol := symbol
    targetState := target
    writeSymbol := symbol
    move := movement }

private def compiledDispatchRule (rule : WorkRule) : Rule :=
  { sourceState := boundaryState rule.sourceState
    readSymbol := rule.readSymbol.first
    targetState := dispatchState rule.sourceState rule.readSymbol.first
    writeSymbol := rule.readSymbol.first
    move := .right }

private def compiledSelectRule (rule : WorkRule) : Rule :=
  { sourceState := dispatchState rule.sourceState rule.readSymbol.first
    readSymbol := rule.readSymbol.second
    targetState := selectedState rule.sourceState rule.readSymbol 2
    writeSymbol := rule.writeSymbol.second
    move := .left }

private def compiledWriteRule (rule : WorkRule) : Rule :=
  { sourceState := selectedState rule.sourceState rule.readSymbol 2
    readSymbol := rule.readSymbol.first
    targetState := selectedState rule.sourceState rule.readSymbol 3
    writeSymbol := rule.writeSymbol.first
    move := .stay }

private def compiledMoveRule (rule : WorkRule) : Rule :=
  { sourceState := selectedState rule.sourceState rule.readSymbol 3
    readSymbol := rule.writeSymbol.first
    targetState := selectedState rule.sourceState rule.readSymbol 4
    writeSymbol := rule.writeSymbol.first
    move := rule.move }

private def preserveRules (source target : Nat) (movement : HeadMove) :
    List Rule :=
  rawSymbols.map (preserveRule source target movement)

private theorem findRule_preserveRules (source target : Nat)
    (movement : HeadMove) (symbol : TapeSymbol) :
    findRule (preserveRules source target movement) source symbol =
      some (preserveRule source target movement symbol) := by
  cases symbol with
  | blank =>
      change findRule
        ([preserveRule source target movement .blank,
          preserveRule source target movement .zero,
          preserveRule source target movement .one]) source .blank =
        some (preserveRule source target movement .blank)
      exact findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
  | zero =>
      change findRule
        ([preserveRule source target movement .blank,
          preserveRule source target movement .zero,
          preserveRule source target movement .one]) source .zero =
        some (preserveRule source target movement .zero)
      have hSkip := findRule_cons_of_not_matches
        (preserveRule source target movement .blank)
        [preserveRule source target movement .zero,
         preserveRule source target movement .one] source .zero
        (by
          intro h
          have hRead := h.2
          change TapeSymbol.blank = TapeSymbol.zero at hRead
          contradiction)
      exact hSkip.trans (findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩)
  | one =>
      change findRule
        ([preserveRule source target movement .blank,
          preserveRule source target movement .zero,
          preserveRule source target movement .one]) source .one =
        some (preserveRule source target movement .one)
      have hSkipBlank := findRule_cons_of_not_matches
        (preserveRule source target movement .blank)
        [preserveRule source target movement .zero,
         preserveRule source target movement .one] source .one
        (by
          intro h
          have hRead := h.2
          change TapeSymbol.blank = TapeSymbol.one at hRead
          contradiction)
      have hSkipZero := findRule_cons_of_not_matches
        (preserveRule source target movement .zero)
        [preserveRule source target movement .one] source .one
        (by
          intro h
          have hRead := h.2
          change TapeSymbol.zero = TapeSymbol.one at hRead
          contradiction)
      exact hSkipBlank.trans
        (hSkipZero.trans (findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩))

private theorem findRule_preserveRules_none_of_source_ne
    (source target queryState : Nat) (movement : HeadMove)
    (symbol : TapeSymbol) (hSource : source ≠ queryState) :
    findRule (preserveRules source target movement) queryState symbol = none := by
  change findRule
    ([preserveRule source target movement .blank,
      preserveRule source target movement .zero,
      preserveRule source target movement .one]) queryState symbol = none
  have hBlank := findRule_cons_of_not_matches
    (preserveRule source target movement .blank)
    [preserveRule source target movement .zero,
     preserveRule source target movement .one] queryState symbol
    (by intro h; exact hSource h.1)
  have hZero := findRule_cons_of_not_matches
    (preserveRule source target movement .zero)
    [preserveRule source target movement .one] queryState symbol
    (by intro h; exact hSource h.1)
  have hOne := findRule_cons_of_not_matches
    (preserveRule source target movement .one) [] queryState symbol
    (by intro h; exact hSource h.1)
  exact hBlank.trans (hZero.trans (hOne.trans rfl))

private def compiledTail (rule : WorkRule) : List Rule :=
  preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move ++
    preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay

private def compileWorkRule (_index : Nat) (rule : WorkRule) : List Rule :=
  [ compiledDispatchRule rule
  , compiledSelectRule rule
  , compiledWriteRule rule
  , compiledMoveRule rule
  ] ++ compiledTail rule

private theorem findRule_compileWorkRule_boundary (index : Nat)
    (rule : WorkRule) :
    findRule (compileWorkRule index rule)
      (boundaryState rule.sourceState) rule.readSymbol.first =
      some (compiledDispatchRule rule) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (boundaryState rule.sourceState) rule.readSymbol.first =
      some (compiledDispatchRule rule)
  exact findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩

private theorem findRule_compileWorkRule_dispatch (index : Nat)
    (rule : WorkRule) :
    findRule (compileWorkRule index rule)
      (dispatchState rule.sourceState rule.readSymbol.first)
      rule.readSymbol.second = some (compiledSelectRule rule) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (dispatchState rule.sourceState rule.readSymbol.first)
      rule.readSymbol.second = some (compiledSelectRule rule)
  have hSkip := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (dispatchState rule.sourceState rule.readSymbol.first) rule.readSymbol.second
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        dispatchState rule.sourceState rule.readSymbol.first at hSource
      exact boundary_ne_dispatch _ _ _ hSource)
  exact hSkip.trans (findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩)

private theorem findRule_compileWorkRule_selected (index : Nat)
    (rule : WorkRule) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 2)
      rule.readSymbol.first = some (compiledWriteRule rule) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 2)
      rule.readSymbol.first = some (compiledWriteRule rule)
  have hSkipDispatch := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 2) rule.readSymbol.first
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        selectedState rule.sourceState rule.readSymbol 2 at hSource
      exact boundary_ne_selected_two _ _ _ hSource)
  have hSkipSelect := findRule_cons_of_not_matches
    (compiledSelectRule rule)
    (compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 2) rule.readSymbol.first
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        selectedState rule.sourceState rule.readSymbol 2 at hSource
      exact dispatch_ne_selected_two _ _ _ _ hSource)
  exact hSkipDispatch.trans
    (hSkipSelect.trans (findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩))

private theorem findRule_compileWorkRule_written (index : Nat)
    (rule : WorkRule) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 3)
      rule.writeSymbol.first = some (compiledMoveRule rule) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 3)
      rule.writeSymbol.first = some (compiledMoveRule rule)
  have hSkipDispatch := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 3) rule.writeSymbol.first
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        selectedState rule.sourceState rule.readSymbol 3 at hSource
      exact boundary_ne_selected_three _ _ _ hSource)
  have hSkipSelect := findRule_cons_of_not_matches
    (compiledSelectRule rule)
    (compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 3) rule.writeSymbol.first
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        selectedState rule.sourceState rule.readSymbol 3 at hSource
      exact dispatch_ne_selected_three _ _ _ _ hSource)
  have hSkipWrite := findRule_cons_of_not_matches
    (compiledWriteRule rule) (compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 3) rule.writeSymbol.first
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 2 =
        selectedState rule.sourceState rule.readSymbol 3 at hSource
      exact selected_two_ne_three _ _ _ _ hSource)
  exact hSkipDispatch.trans (hSkipSelect.trans
    (hSkipWrite.trans (findRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩)))

private theorem findRule_compileWorkRule_moved (index : Nat)
    (rule : WorkRule) (symbol : TapeSymbol) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 4) symbol =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 4)
        (selectedState rule.sourceState rule.readSymbol 5) rule.move symbol) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 4) symbol = _
  have hSkipDispatch := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 4) symbol
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        selectedState rule.sourceState rule.readSymbol 4 at hSource
      exact boundary_ne_selected_four _ _ _ hSource)
  have hSkipSelect := findRule_cons_of_not_matches
    (compiledSelectRule rule)
    (compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 4) symbol
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        selectedState rule.sourceState rule.readSymbol 4 at hSource
      exact dispatch_ne_selected_four _ _ _ _ hSource)
  have hSkipWrite := findRule_cons_of_not_matches
    (compiledWriteRule rule) (compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 4) symbol
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 2 =
        selectedState rule.sourceState rule.readSymbol 4 at hSource
      exact selected_two_ne_four _ _ _ _ hSource)
  have hSkipMove := findRule_cons_of_not_matches
    (compiledMoveRule rule) (compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 4) symbol
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 3 =
        selectedState rule.sourceState rule.readSymbol 4 at hSource
      exact selected_three_ne_four _ _ _ _ hSource)
  have hPreserve := findRule_append_of_some
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    _ _ _ (findRule_preserveRules _ _ _ symbol)
  exact hSkipDispatch.trans (hSkipSelect.trans
    (hSkipWrite.trans (hSkipMove.trans hPreserve)))

private theorem findRule_compileWorkRule_finished (index : Nat)
    (rule : WorkRule) (symbol : TapeSymbol) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 5) symbol =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 5)
        (boundaryState rule.targetState) .stay symbol) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule ::
      compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 5) symbol = _
  have hSkipDispatch := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 5) symbol
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        selectedState rule.sourceState rule.readSymbol 5 at hSource
      exact boundary_ne_selected_five _ _ _ hSource)
  have hSkipSelect := findRule_cons_of_not_matches
    (compiledSelectRule rule)
    (compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 5) symbol
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        selectedState rule.sourceState rule.readSymbol 5 at hSource
      exact dispatch_ne_selected_five _ _ _ _ hSource)
  have hSkipWrite := findRule_cons_of_not_matches
    (compiledWriteRule rule) (compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 5) symbol
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 2 =
        selectedState rule.sourceState rule.readSymbol 5 at hSource
      exact selected_two_ne_five _ _ _ _ hSource)
  have hSkipMove := findRule_cons_of_not_matches
    (compiledMoveRule rule) (compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 5) symbol
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 3 =
        selectedState rule.sourceState rule.readSymbol 5 at hSource
      exact selected_three_ne_five _ _ _ _ hSource)
  have hFirstNone := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (selectedState rule.sourceState rule.readSymbol 5) rule.move symbol
    (selected_four_ne_five _ _ _ _)
  have hPreserve := findRule_append_of_none
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    _ _ hFirstNone
  have hFinal := findRule_preserveRules
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) .stay symbol
  exact hSkipDispatch.trans (hSkipSelect.trans
    (hSkipWrite.trans (hSkipMove.trans (hPreserve.trans hFinal))))

private theorem workSymbol_eq_of_fields {left right : WorkSymbol}
    (hFirst : left.first = right.first)
    (hSecond : left.second = right.second) : left = right := by
  cases left with
  | mk leftFirst leftSecond =>
      cases right with
      | mk rightFirst rightSecond =>
          cases hFirst
          cases hSecond
          rfl

private theorem findRule_compileWorkRule_boundary_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (hLhs : ¬(rule.sourceState = state ∧
      rule.readSymbol.first = symbol.first)) :
    findRule (compileWorkRule index rule)
      (boundaryState state) symbol.first = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (boundaryState state) symbol.first = none
  have hDispatch := findRule_cons_of_not_matches
    (compiledDispatchRule rule)
    (compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule) _ _
    (by
      intro h
      have hSource : rule.sourceState = state :=
        boundaryState_injective h.1
      exact hLhs ⟨hSource, h.2⟩)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := boundaryState state) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        boundaryState state at hSource
      exact boundary_ne_dispatch _ _ _ hSource.symm)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := boundaryState state) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 2 =
        boundaryState state at hSource
      exact boundary_ne_selected_two _ _ _ hSource.symm)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := boundaryState state) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 3 =
        boundaryState state at hSource
      exact boundary_ne_selected_three _ _ _ hSource.symm)
  have hPreserveFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState state) rule.move symbol.first
    (by intro h; exact boundary_ne_selected_four _ _ _ h.symm)
  have hPreserveFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (boundaryState state)
    .stay symbol.first
    (by intro h; exact boundary_ne_selected_five _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := boundaryState state) (symbol := symbol.first) hPreserveFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hPreserveFive))))

private theorem findRule_compileWorkRule_dispatch_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (hLhs : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (compileWorkRule index rule)
      (dispatchState state symbol.first) symbol.second = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (dispatchState state symbol.first) symbol.second = none
  have hDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState =
        dispatchState state symbol.first at hSource
      exact boundary_ne_dispatch _ _ _ hSource)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    (by
      intro h
      have hParts := dispatchState_injective h.1
      have hSymbol := workSymbol_eq_of_fields hParts.2 h.2
      exact hLhs ⟨hParts.1, hSymbol⟩)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 2 =
        dispatchState state symbol.first at hSource
      exact dispatch_ne_selected_two _ _ _ _ hSource.symm)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 3 =
        dispatchState state symbol.first at hSource
      exact dispatch_ne_selected_three _ _ _ _ hSource.symm)
  have hPreserveFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (dispatchState state symbol.first) rule.move symbol.second
    (by intro h; exact dispatch_ne_selected_four _ _ _ _ h.symm)
  have hPreserveFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (dispatchState state symbol.first)
    .stay symbol.second
    (by intro h; exact dispatch_ne_selected_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    hPreserveFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hPreserveFive))))

private theorem findRule_compileWorkRule_selected_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (hLhs : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (compileWorkRule index rule)
      (selectedState state symbol 2) symbol.first = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState state symbol 2) symbol.first = none
  have hDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 2) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change boundaryState rule.sourceState = selectedState state symbol 2 at hSource
      exact boundary_ne_selected_two _ _ _ hSource)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 2) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change dispatchState rule.sourceState rule.readSymbol.first =
        selectedState state symbol 2 at hSource
      exact dispatch_ne_selected_two _ _ _ _ hSource)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 2) (symbol := symbol.first)
    (by
      intro h
      have hParts := selectedState_two_injective h.1
      exact hLhs hParts)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := selectedState state symbol 2) (symbol := symbol.first)
    (by
      intro h
      have hSource := h.1
      change selectedState rule.sourceState rule.readSymbol 3 =
        selectedState state symbol 2 at hSource
      exact selected_two_ne_three _ _ _ _ hSource.symm)
  have hFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (selectedState state symbol 2) rule.move symbol.first
    (by intro h; exact selected_two_ne_four _ _ _ _ h.symm)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 2)
    .stay symbol.first
    (by intro h; exact selected_two_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := selectedState state symbol 2) (symbol := symbol.first) hFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hFive))))

private theorem findRule_compileWorkRule_written_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (query : TapeSymbol)
    (hLhs : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (compileWorkRule index rule)
      (selectedState state symbol 3) query = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState state symbol 3) query = none
  have hDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 3) (symbol := query)
    (by intro h; exact boundary_ne_selected_three _ _ _ h.1)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 3) (symbol := query)
    (by intro h; exact dispatch_ne_selected_three _ _ _ _ h.1)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 3) (symbol := query)
    (by intro h; exact selected_two_ne_three _ _ _ _ h.1)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := selectedState state symbol 3) (symbol := query)
    (by
      intro h
      have hParts := selectedState_three_injective h.1
      exact hLhs hParts)
  have hFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (selectedState state symbol 3) rule.move query
    (by intro h; exact selected_three_ne_four _ _ _ _ h.symm)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 3)
    .stay query
    (by intro h; exact selected_three_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := selectedState state symbol 3) (symbol := query) hFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hFive))))

private theorem findRule_compileWorkRule_moved_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (query : TapeSymbol)
    (hLhs : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (compileWorkRule index rule)
      (selectedState state symbol 4) query = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState state symbol 4) query = none
  have hDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 4) (symbol := query)
    (by intro h; exact boundary_ne_selected_four _ _ _ h.1)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 4) (symbol := query)
    (by intro h; exact dispatch_ne_selected_four _ _ _ _ h.1)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 4) (symbol := query)
    (by intro h; exact selected_two_ne_four _ _ _ _ h.1)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := selectedState state symbol 4) (symbol := query)
    (by intro h; exact selected_three_ne_four _ _ _ _ h.1)
  have hFourSource : selectedState rule.sourceState rule.readSymbol 4 ≠
      selectedState state symbol 4 := by
    intro h
    exact hLhs (selectedState_four_injective h)
  have hFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (selectedState state symbol 4) rule.move query hFourSource
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 4)
    .stay query
    (by intro h; exact selected_four_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := selectedState state symbol 4) (symbol := query) hFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hFive))))

private theorem findRule_compileWorkRule_finished_none (index : Nat)
    (rule : WorkRule) (state : Nat) (symbol : WorkSymbol)
    (query : TapeSymbol)
    (hLhs : ¬(rule.sourceState = state ∧ rule.readSymbol = symbol)) :
    findRule (compileWorkRule index rule)
      (selectedState state symbol 5) query = none := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState state symbol 5) query = none
  have hDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 5) (symbol := query)
    (by intro h; exact boundary_ne_selected_five _ _ _ h.1)
  have hSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 5) (symbol := query)
    (by intro h; exact dispatch_ne_selected_five _ _ _ _ h.1)
  have hWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := selectedState state symbol 5) (symbol := query)
    (by intro h; exact selected_two_ne_five _ _ _ _ h.1)
  have hMove := findRule_cons_of_not_matches
    (rule := compiledMoveRule rule) (rest := compiledTail rule)
    (state := selectedState state symbol 5) (symbol := query)
    (by intro h; exact selected_three_ne_five _ _ _ _ h.1)
  have hFour := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState rule.sourceState rule.readSymbol 5)
    (selectedState state symbol 5) rule.move query
    (by intro h; exact selected_four_ne_five _ _ _ _ h)
  have hFiveSource : selectedState rule.sourceState rule.readSymbol 5 ≠
      selectedState state symbol 5 := by
    intro h
    exact hLhs (selectedState_five_injective h)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 5)
    .stay query hFiveSource
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move)
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay)
    (state := selectedState state symbol 5) (symbol := query) hFour
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hTail.trans hFive))))

private def compileWorkRulesFrom : Nat → List WorkRule → List Rule
  | _, [] => []
  | index, rule :: rest =>
      compileWorkRule index rule ++ compileWorkRulesFrom (index + 1) rest

/-- Compile a finite work-machine rule list to a finite raw rule list. -/
def compileWorkMachine (machine : WorkMachine) : Machine :=
  { rules := compileWorkRulesFrom 0 machine.rules
    startState := boundaryState machine.startState
    acceptState := boundaryState machine.acceptState
    rejectState := boundaryState machine.rejectState }

/-- Encode a macro-boundary work configuration as a raw configuration. -/
def encodeWorkConfiguration (config : WorkConfiguration) : Configuration :=
  { state := boundaryState config.state
    tape := encodeWorkTape config.tape }

end PNP.Concrete
