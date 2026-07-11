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

theorem findWorkRule_some_matches {rules : List WorkRule} {state : Nat}
    {symbol : WorkSymbol} {selected : WorkRule}
    (h : findWorkRule rules state symbol = some selected) :
    selected.sourceState = state ∧ selected.readSymbol = symbol := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hFirst
        have hRule : first = selected := Option.some.inj (hCons.symm.trans h)
        exact
          ⟨(congrArg WorkRule.sourceState hRule).symm.trans hFirst.1,
           (congrArg WorkRule.readSymbol hRule).symm.trans hFirst.2⟩
      · have hCons := findWorkRule_cons_of_not_matches first rest state symbol hFirst
        exact ih (hCons.symm.trans h)

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

private def dispatchRuleFor (state : Nat) (first : TapeSymbol) : Rule :=
  { sourceState := boundaryState state
    readSymbol := first
    targetState := dispatchState state first
    writeSymbol := first
    move := .right }

private def compiledDispatchRule (rule : WorkRule) : Rule :=
  dispatchRuleFor rule.sourceState rule.readSymbol.first

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
    move := rule.move }

private def compilerSecondMove : HeadMove → HeadMove
  | .left => .left
  | .stay => .right
  | .right => .right

private def compilerThirdMove : HeadMove → HeadMove
  | .left => .right
  | .stay => .left
  | .right => .right

private def compilerFinalMove : HeadMove → HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .left

private def compiledMoveRule (rule : WorkRule) : Rule :=
  { sourceState := selectedState rule.sourceState rule.readSymbol 3
    readSymbol := rule.writeSymbol.first
    targetState := selectedState rule.sourceState rule.readSymbol 4
    writeSymbol := rule.writeSymbol.first
    move := compilerSecondMove rule.move }

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

private def compiledLateTail (rule : WorkRule) : List Rule :=
  preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move) ++
    preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move)

private def compiledTail (rule : WorkRule) : List Rule :=
  compiledLateTail rule ++
    preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move)

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

private theorem findRule_compileWorkRule_written_any (index : Nat)
    (rule : WorkRule) (query : TapeSymbol) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 3) query =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 3)
        (selectedState rule.sourceState rule.readSymbol 4)
        (compilerSecondMove rule.move) query) := by
  change findRule
    (compiledDispatchRule rule :: compiledSelectRule rule ::
      compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (selectedState rule.sourceState rule.readSymbol 3) query = _
  have hSkipDispatch := findRule_cons_of_not_matches
    (rule := compiledDispatchRule rule)
    (rest := compiledSelectRule rule :: compiledWriteRule rule ::
      compiledMoveRule rule :: compiledTail rule)
    (state := selectedState rule.sourceState rule.readSymbol 3) (symbol := query)
    (by intro h; exact boundary_ne_selected_three _ _ _ h.1)
  have hSkipSelect := findRule_cons_of_not_matches
    (rule := compiledSelectRule rule)
    (rest := compiledWriteRule rule :: compiledMoveRule rule :: compiledTail rule)
    (state := selectedState rule.sourceState rule.readSymbol 3) (symbol := query)
    (by intro h; exact dispatch_ne_selected_three _ _ _ _ h.1)
  have hSkipWrite := findRule_cons_of_not_matches
    (rule := compiledWriteRule rule)
    (rest := compiledMoveRule rule :: compiledTail rule)
    (state := selectedState rule.sourceState rule.readSymbol 3) (symbol := query)
    (by intro h; exact selected_two_ne_three _ _ _ _ h.1)
  by_cases hQuery : rule.writeSymbol.first = query
  · have hMove := findRule_cons_of_matches
      (compiledMoveRule rule) (compiledTail rule)
      (selectedState rule.sourceState rule.readSymbol 3) query ⟨rfl, hQuery⟩
    have hRaw : compiledMoveRule rule = preserveRule
        (selectedState rule.sourceState rule.readSymbol 3)
        (selectedState rule.sourceState rule.readSymbol 4)
        (compilerSecondMove rule.move) query := by
      unfold compiledMoveRule preserveRule
      rw [← hQuery]
    exact hSkipDispatch.trans (hSkipSelect.trans
      (hSkipWrite.trans (hMove.trans (congrArg Option.some hRaw))))
  · have hMove := findRule_cons_of_not_matches
      (compiledMoveRule rule) (compiledTail rule)
      (selectedState rule.sourceState rule.readSymbol 3) query
      (by intro h; exact hQuery h.2)
    have hFour := findRule_preserveRules_none_of_source_ne
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (selectedState rule.sourceState rule.readSymbol 3)
      (compilerThirdMove rule.move) query
      (by intro h; exact selected_three_ne_four _ _ _ _ h.symm)
    have hFive := findRule_preserveRules_none_of_source_ne
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState)
      (selectedState rule.sourceState rule.readSymbol 3)
      (compilerFinalMove rule.move) query
      (by intro h; exact selected_three_ne_five _ _ _ _ h.symm)
    have hLate := findRule_append_of_none _ _ _ _ hFour |>.trans hFive
    have hAppend := findRule_append_of_none
      (compiledLateTail rule)
      (preserveRules
        (selectedState rule.sourceState rule.readSymbol 3)
        (selectedState rule.sourceState rule.readSymbol 4)
        (compilerSecondMove rule.move))
      _ _ hLate
    have hPreserve := findRule_preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move) query
    exact hSkipDispatch.trans (hSkipSelect.trans
      (hSkipWrite.trans (hMove.trans (hAppend.trans hPreserve))))

private theorem findRule_compileWorkRule_moved (index : Nat)
    (rule : WorkRule) (symbol : TapeSymbol) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 4) symbol =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 4)
        (selectedState rule.sourceState rule.readSymbol 5)
        (compilerThirdMove rule.move) symbol) := by
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
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    _ _ _ (findRule_preserveRules _ _ _ symbol)
  have hAll := findRule_append_of_some
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ _ hPreserve
  exact hSkipDispatch.trans (hSkipSelect.trans
    (hSkipWrite.trans (hSkipMove.trans hAll)))

private theorem findRule_compileWorkRule_finished (index : Nat)
    (rule : WorkRule) (symbol : TapeSymbol) :
    findRule (compileWorkRule index rule)
      (selectedState rule.sourceState rule.readSymbol 5) symbol =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 5)
        (boundaryState rule.targetState) (compilerFinalMove rule.move) symbol) := by
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
    (selectedState rule.sourceState rule.readSymbol 5)
    (compilerThirdMove rule.move) symbol
    (selected_four_ne_five _ _ _ _)
  have hPreserve := findRule_append_of_none
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    _ _ hFirstNone
  have hFinal := findRule_preserveRules
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (compilerFinalMove rule.move) symbol
  have hLate := hPreserve.trans hFinal
  have hAll := findRule_append_of_some
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ _ hLate
  exact hSkipDispatch.trans (hSkipSelect.trans
    (hSkipWrite.trans (hSkipMove.trans hAll)))

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
    (boundaryState state) (compilerThirdMove rule.move) symbol.first
    (by intro h; exact boundary_ne_selected_four _ _ _ h.symm)
  have hPreserveFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (boundaryState state)
    (compilerFinalMove rule.move) symbol.first
    (by intro h; exact boundary_ne_selected_five _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := boundaryState state) (symbol := symbol.first) hPreserveFour
  have hLate := hTail.trans hPreserveFive
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (boundaryState state) (compilerSecondMove rule.move) symbol.first
    (by intro h; exact boundary_ne_selected_three _ _ _ h.symm)
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

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
    (dispatchState state symbol.first) (compilerThirdMove rule.move) symbol.second
    (by intro h; exact dispatch_ne_selected_four _ _ _ _ h.symm)
  have hPreserveFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (dispatchState state symbol.first)
    (compilerFinalMove rule.move) symbol.second
    (by intro h; exact dispatch_ne_selected_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := dispatchState state symbol.first) (symbol := symbol.second)
    hPreserveFour
  have hLate := hTail.trans hPreserveFive
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (dispatchState state symbol.first) (compilerSecondMove rule.move) symbol.second
    (by intro h; exact dispatch_ne_selected_three _ _ _ _ h.symm)
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

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
    (selectedState state symbol 2) (compilerThirdMove rule.move) symbol.first
    (by intro h; exact selected_two_ne_four _ _ _ _ h.symm)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 2)
    (compilerFinalMove rule.move) symbol.first
    (by intro h; exact selected_two_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := selectedState state symbol 2) (symbol := symbol.first) hFour
  have hLate := hTail.trans hFive
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState state symbol 2) (compilerSecondMove rule.move) symbol.first
    (by intro h; exact selected_two_ne_three _ _ _ _ h.symm)
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

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
    (selectedState state symbol 3) (compilerThirdMove rule.move) query
    (by intro h; exact selected_three_ne_four _ _ _ _ h.symm)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 3)
    (compilerFinalMove rule.move) query
    (by intro h; exact selected_three_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := selectedState state symbol 3) (symbol := query) hFour
  have hLate := hTail.trans hFive
  have hThreeSource : selectedState rule.sourceState rule.readSymbol 3 ≠
      selectedState state symbol 3 := by
    intro h
    exact hLhs (selectedState_three_injective h)
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState state symbol 3) (compilerSecondMove rule.move) query
    hThreeSource
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

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
    (selectedState state symbol 4) (compilerThirdMove rule.move) query hFourSource
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 4)
    (compilerFinalMove rule.move) query
    (by intro h; exact selected_four_ne_five _ _ _ _ h.symm)
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := selectedState state symbol 4) (symbol := query) hFour
  have hLate := hTail.trans hFive
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState state symbol 4) (compilerSecondMove rule.move) query
    (selected_three_ne_four _ _ _ _)
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

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
    (selectedState state symbol 5) (compilerThirdMove rule.move) query
    (by intro h; exact selected_four_ne_five _ _ _ _ h)
  have hFiveSource : selectedState rule.sourceState rule.readSymbol 5 ≠
      selectedState state symbol 5 := by
    intro h
    exact hLhs (selectedState_five_injective h)
  have hFive := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 5)
    (boundaryState rule.targetState) (selectedState state symbol 5)
    (compilerFinalMove rule.move) query hFiveSource
  have hTail := findRule_append_of_none
    (left := preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move))
    (right := preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move))
    (state := selectedState state symbol 5) (symbol := query) hFour
  have hLate := hTail.trans hFive
  have hThree := findRule_preserveRules_none_of_source_ne
    (selectedState rule.sourceState rule.readSymbol 3)
    (selectedState rule.sourceState rule.readSymbol 4)
    (selectedState state symbol 5) (compilerSecondMove rule.move) query
    (selected_three_ne_five _ _ _ _)
  have hAll := findRule_append_of_none
    (compiledLateTail rule)
    (preserveRules
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move))
    _ _ hLate
  exact hDispatch.trans (hSelect.trans (hWrite.trans
    (hMove.trans (hAll.trans hThree))))

private def compileWorkRulesFrom : Nat → List WorkRule → List Rule
  | _, [] => []
  | index, rule :: rest =>
      compileWorkRule index rule ++ compileWorkRulesFrom (index + 1) rest

theorem findRule_compileWorkRulesFrom_boundary_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (boundaryState state) symbol.first =
      some (dispatchRuleFor state symbol.first) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (boundaryState state) symbol.first = _
      by_cases hPartial : first.sourceState = state ∧
          first.readSymbol.first = symbol.first
      · have hBlock := findRule_compileWorkRule_boundary index first
        rw [hPartial.1, hPartial.2] at hBlock
        have hRaw : compiledDispatchRule first =
            dispatchRuleFor state symbol.first := by
          unfold compiledDispatchRule
          rw [hPartial.1, hPartial.2]
        have hBlockCanonical := hBlock.trans (congrArg Option.some hRaw)
        exact findRule_append_of_some _ _ _ _ _ hBlockCanonical
      · have hBlock := findRule_compileWorkRule_boundary_none
          index first state symbol hPartial
        have hHeadFull : ¬(first.sourceState = state ∧
            first.readSymbol = symbol) := by
          intro h
          exact hPartial ⟨h.1, congrArg WorkSymbol.first h.2⟩
        have hCons := findWorkRule_cons_of_not_matches
          first rest state symbol hHeadFull
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (boundaryState state) symbol.first hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_dispatch_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (dispatchState state symbol.first) symbol.second =
      some (compiledSelectRule selected) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (dispatchState state symbol.first) symbol.second = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_dispatch index selected)
      · have hBlock := findRule_compileWorkRule_dispatch_none
          index first state symbol hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (dispatchState state symbol.first) symbol.second hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_selected_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (selectedState state symbol 2) symbol.first =
      some (compiledWriteRule selected) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (selectedState state symbol 2) symbol.first = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_selected index selected)
      · have hBlock := findRule_compileWorkRule_selected_none
          index first state symbol hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (selectedState state symbol 2) symbol.first hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_written_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (selectedState state symbol 3) selected.writeSymbol.first =
      some (compiledMoveRule selected) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (selectedState state symbol 3) selected.writeSymbol.first = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_written index selected)
      · have hBlock := findRule_compileWorkRule_written_none
          index first state symbol selected.writeSymbol.first hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (selectedState state symbol 3) selected.writeSymbol.first hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_written_any_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat) (query : TapeSymbol)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (selectedState state symbol 3) query =
      some (preserveRule (selectedState state symbol 3)
        (selectedState state symbol 4)
        (compilerSecondMove selected.move) query) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (selectedState state symbol 3) query = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_written_any index selected query)
      · have hBlock := findRule_compileWorkRule_written_none
          index first state symbol query hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (selectedState state symbol 3) query hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_moved_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat) (query : TapeSymbol)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (selectedState state symbol 4) query =
      some (preserveRule (selectedState state symbol 4)
        (selectedState state symbol 5)
        (compilerThirdMove selected.move) query) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (selectedState state symbol 4) query = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_moved index selected query)
      · have hBlock := findRule_compileWorkRule_moved_none
          index first state symbol query hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (selectedState state symbol 4) query hBlock
        exact hAppend.trans (ih (index + 1) hTail)

theorem findRule_compileWorkRulesFrom_finished_of_findWorkRule
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (selected : WorkRule) (index : Nat) (query : TapeSymbol)
    (hFind : findWorkRule rules state symbol = some selected) :
    findRule (compileWorkRulesFrom index rules)
      (selectedState state symbol 5) query =
      some (preserveRule (selectedState state symbol 5)
        (boundaryState selected.targetState)
        (compilerFinalMove selected.move) query) := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      change findRule
        (compileWorkRule index first ++
          compileWorkRulesFrom (index + 1) rest)
        (selectedState state symbol 5) query = _
      by_cases hHead : first.sourceState = state ∧ first.readSymbol = symbol
      · have hCons := findWorkRule_cons_of_matches first rest state symbol hHead
        have hRule : first = selected := Option.some.inj (hCons.symm.trans hFind)
        cases hRule
        cases hHead.1
        cases hHead.2
        exact findRule_append_of_some _ _ _ _ _
          (findRule_compileWorkRule_finished index selected query)
      · have hBlock := findRule_compileWorkRule_finished_none
          index first state symbol query hHead
        have hCons := findWorkRule_cons_of_not_matches first rest state symbol hHead
        have hTail : findWorkRule rest state symbol = some selected :=
          hCons.symm.trans hFind
        have hAppend := findRule_append_of_none
          (compileWorkRule index first)
          (compileWorkRulesFrom (index + 1) rest)
          (selectedState state symbol 5) query hBlock
        exact hAppend.trans (ih (index + 1) hTail)

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

theorem nat_beq_map_of_injective (function : Nat → Nat)
    (hInjective : Function.Injective function) (left right : Nat) :
    (function left == function right) = (left == right) := by
  cases hMapped : (function left == function right) with
  | false =>
      cases hPlain : (left == right) with
      | false => rfl
      | true =>
          have hEq := (nat_beq_true_iff left right).mp hPlain
          have hMappedTrue :=
            (nat_beq_true_iff (function left) (function right)).mpr
              (congrArg function hEq)
          rw [hMapped] at hMappedTrue
          contradiction
  | true =>
      cases hPlain : (left == right) with
      | true => rfl
      | false =>
          have hMappedEq :=
            (nat_beq_true_iff (function left) (function right)).mp hMapped
          have hEq := hInjective hMappedEq
          have hPlainTrue := (nat_beq_true_iff left right).mpr hEq
          rw [hPlain] at hPlainTrue
          contradiction

theorem compileWorkMachine_isHalted_encode (machine : WorkMachine)
    (config : WorkConfiguration) :
    (compileWorkMachine machine).isHalted (encodeWorkConfiguration config) =
      machine.isHalted config := by
  unfold Machine.isHalted WorkMachine.isHalted compileWorkMachine
    encodeWorkConfiguration
  rw [nat_beq_map_of_injective boundaryState
    (fun {_ _} h => boundaryState_injective h)]
  rw [nat_beq_map_of_injective boundaryState
    (fun {_ _} h => boundaryState_injective h)]

theorem step?_eq_apply_of_find (machine : Machine) (config : Configuration)
    (rule : Rule) (hHalted : machine.isHalted config = false)
    (hFind : findRule machine.rules config.state config.tape.head = some rule) :
    step? machine config = some (applyRule rule config) := by
  have hNotHalted : ¬(machine.isHalted config = true) := by
    intro hTrue
    have impossible : false = true := hHalted.symm.trans hTrue
    contradiction
  have hOuter : step? machine config =
      match findRule machine.rules config.state config.tape.head with
      | none => none
      | some selected => some (applyRule selected config) := by
    unfold step?
    exact if_neg hNotHalted
  have hInner :
      (match findRule machine.rules config.state config.tape.head with
       | none => none
       | some selected => some (applyRule selected config)) =
      some (applyRule rule config) := by
    exact congrArg
      (fun found => match found with
        | none => none
        | some selected => some (applyRule selected config)) hFind
  exact hOuter.trans hInner

private theorem compileWorkMachine_not_halted_of_state_ne
    (machine : WorkMachine) (config : Configuration)
    (hAccept : config.state ≠ boundaryState machine.acceptState)
    (hReject : config.state ≠ boundaryState machine.rejectState) :
    (compileWorkMachine machine).isHalted config = false := by
  unfold Machine.isHalted compileWorkMachine
  cases hAcceptBool : (config.state == boundaryState machine.acceptState) with
  | true =>
      have hEq := (nat_beq_true_iff _ _).mp hAcceptBool
      exact False.elim (hAccept hEq)
  | false =>
      cases hRejectBool : (config.state == boundaryState machine.rejectState) with
      | true =>
          have hEq := (nat_beq_true_iff _ _).mp hRejectBool
          exact False.elim (hReject hEq)
      | false => rfl

private def compilePhaseOne (config : WorkConfiguration) : Configuration :=
  applyRule (dispatchRuleFor config.state config.tape.head.first)
    (encodeWorkConfiguration config)

private def compilePhaseTwo (rule : WorkRule)
    (config : WorkConfiguration) : Configuration :=
  applyRule (compiledSelectRule rule) (compilePhaseOne config)

private def compilePhaseThree (rule : WorkRule)
    (config : WorkConfiguration) : Configuration :=
  applyRule (compiledWriteRule rule) (compilePhaseTwo rule config)

private def compilePhaseFour (rule : WorkRule)
    (config : WorkConfiguration) : Configuration :=
  let phaseThree := compilePhaseThree rule config
  applyRule
    (preserveRule (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move) phaseThree.tape.head)
    phaseThree

private def compilePhaseFive (rule : WorkRule)
    (config : WorkConfiguration) : Configuration :=
  let phaseFour := compilePhaseFour rule config
  applyRule
    (preserveRule (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move) phaseFour.tape.head)
    phaseFour

private def compilePhaseSix (rule : WorkRule)
    (config : WorkConfiguration) : Configuration :=
  let phaseFive := compilePhaseFive rule config
  applyRule
    (preserveRule (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move)
      phaseFive.tape.head)
    phaseFive

set_option linter.unusedSimpArgs false in
theorem compilePhaseSix_eq_encode_apply (rule : WorkRule)
    (config : WorkConfiguration) :
    compilePhaseSix rule config =
      encodeWorkConfiguration (applyWorkRule rule config) := by
  unfold compilePhaseSix compilePhaseFive compilePhaseFour compilePhaseThree
    compilePhaseTwo compilePhaseOne
  cases config with
  | mk state tape =>
      cases tape with
      | mk left head right =>
          cases rule with
          | mk source read target write movement =>
              cases movement with
              | left =>
                  cases left with
                  | nil =>
                      unfold compiledWriteRule compiledSelectRule dispatchRuleFor
                        preserveRule compilerSecondMove compilerThirdMove
                        compilerFinalMove encodeWorkConfiguration encodeWorkTape
                        applyWorkRule WorkTape.write WorkTape.move applyRule
                        Tape.write Tape.move
                      rfl
                  | cons leftHead leftTail =>
                      unfold compiledWriteRule compiledSelectRule dispatchRuleFor
                        preserveRule compilerSecondMove compilerThirdMove
                        compilerFinalMove encodeWorkConfiguration encodeWorkTape
                        applyWorkRule WorkTape.write WorkTape.move applyRule
                        Tape.write Tape.move
                      rfl
              | stay =>
                  unfold compiledWriteRule compiledSelectRule dispatchRuleFor
                    preserveRule compilerSecondMove compilerThirdMove
                    compilerFinalMove encodeWorkConfiguration encodeWorkTape
                    applyWorkRule WorkTape.write WorkTape.move applyRule
                    Tape.write Tape.move
                  rfl
              | right =>
                  cases right with
                  | nil =>
                      unfold compiledWriteRule compiledSelectRule dispatchRuleFor
                        preserveRule compilerSecondMove compilerThirdMove
                        compilerFinalMove encodeWorkConfiguration encodeWorkTape
                        applyWorkRule WorkTape.write WorkTape.move applyRule
                        Tape.write Tape.move
                      rfl
                  | cons rightHead rightTail =>
                      unfold compiledWriteRule compiledSelectRule dispatchRuleFor
                        preserveRule compilerSecondMove compilerThirdMove
                        compilerFinalMove encodeWorkConfiguration encodeWorkTape
                        applyWorkRule WorkTape.write WorkTape.move applyRule
                        Tape.write Tape.move
                      rfl

/-- One selected work transition is implemented by exactly six raw
transitions, from one macro boundary to the next. -/
theorem run_compileWorkMachine_six_of_selected (machine : WorkMachine)
    (config : WorkConfiguration) (rule : WorkRule)
    (hHalted : machine.isHalted config = false)
    (hFind : findWorkRule machine.rules config.state config.tape.head = some rule) :
    run (compileWorkMachine machine) 6 (encodeWorkConfiguration config) =
      encodeWorkConfiguration (applyWorkRule rule config) := by
  have hMatches := findWorkRule_some_matches hFind
  have hLookupOne :=
    findRule_compileWorkRulesFrom_boundary_of_findWorkRule
      machine.rules config.state config.tape.head rule 0 hFind
  have hLookupTwo :=
    findRule_compileWorkRulesFrom_dispatch_of_findWorkRule
      machine.rules config.state config.tape.head rule 0 hFind
  have hLookupThree :=
    findRule_compileWorkRulesFrom_selected_of_findWorkRule
      machine.rules config.state config.tape.head rule 0 hFind
  have hLookupFour :=
    findRule_compileWorkRulesFrom_written_any_of_findWorkRule
      machine.rules config.state config.tape.head rule 0
      (compilePhaseThree rule config).tape.head hFind
  have hLookupFive :=
    findRule_compileWorkRulesFrom_moved_of_findWorkRule
      machine.rules config.state config.tape.head rule 0
      (compilePhaseFour rule config).tape.head hFind
  have hLookupSix :=
    findRule_compileWorkRulesFrom_finished_of_findWorkRule
      machine.rules config.state config.tape.head rule 0
      (compilePhaseFive rule config).tape.head hFind
  have hRawHalted : (compileWorkMachine machine).isHalted
      (encodeWorkConfiguration config) = false :=
    (compileWorkMachine_isHalted_encode machine config).trans hHalted
  have hHaltedOne : (compileWorkMachine machine).isHalted
      (compilePhaseOne config) = false := by
    apply compileWorkMachine_not_halted_of_state_ne
    · intro h
      exact boundary_ne_dispatch _ _ _ h.symm
    · intro h
      exact boundary_ne_dispatch _ _ _ h.symm
  have hHaltedTwo : (compileWorkMachine machine).isHalted
      (compilePhaseTwo rule config) = false := by
    apply compileWorkMachine_not_halted_of_state_ne
    · intro h
      change selectedState rule.sourceState rule.readSymbol 2 =
        boundaryState machine.acceptState at h
      exact boundary_ne_selected_two _ _ _ h.symm
    · intro h
      change selectedState rule.sourceState rule.readSymbol 2 =
        boundaryState machine.rejectState at h
      exact boundary_ne_selected_two _ _ _ h.symm
  have hHaltedThree : (compileWorkMachine machine).isHalted
      (compilePhaseThree rule config) = false := by
    apply compileWorkMachine_not_halted_of_state_ne
    · intro h
      change selectedState rule.sourceState rule.readSymbol 3 =
        boundaryState machine.acceptState at h
      exact boundary_ne_selected_three _ _ _ h.symm
    · intro h
      change selectedState rule.sourceState rule.readSymbol 3 =
        boundaryState machine.rejectState at h
      exact boundary_ne_selected_three _ _ _ h.symm
  have hHaltedFour : (compileWorkMachine machine).isHalted
      (compilePhaseFour rule config) = false := by
    apply compileWorkMachine_not_halted_of_state_ne
    · intro h
      change selectedState rule.sourceState rule.readSymbol 4 =
        boundaryState machine.acceptState at h
      exact boundary_ne_selected_four _ _ _ h.symm
    · intro h
      change selectedState rule.sourceState rule.readSymbol 4 =
        boundaryState machine.rejectState at h
      exact boundary_ne_selected_four _ _ _ h.symm
  have hHaltedFive : (compileWorkMachine machine).isHalted
      (compilePhaseFive rule config) = false := by
    apply compileWorkMachine_not_halted_of_state_ne
    · intro h
      change selectedState rule.sourceState rule.readSymbol 5 =
        boundaryState machine.acceptState at h
      exact boundary_ne_selected_five _ _ _ h.symm
    · intro h
      change selectedState rule.sourceState rule.readSymbol 5 =
        boundaryState machine.rejectState at h
      exact boundary_ne_selected_five _ _ _ h.symm
  have hLookupOne' : findRule (compileWorkMachine machine).rules
      (encodeWorkConfiguration config).state
      (encodeWorkConfiguration config).tape.head =
      some (dispatchRuleFor config.state config.tape.head.first) := hLookupOne
  have hLookupTwo' : findRule (compileWorkMachine machine).rules
      (compilePhaseOne config).state (compilePhaseOne config).tape.head =
      some (compiledSelectRule rule) := by
    exact hLookupTwo
  have hStateTwo : selectedState config.state config.tape.head 2 =
      selectedState rule.sourceState rule.readSymbol 2 := by
    rw [hMatches.1, hMatches.2]
  have hStateThree : selectedState config.state config.tape.head 3 =
      selectedState rule.sourceState rule.readSymbol 3 := by
    rw [hMatches.1, hMatches.2]
  have hStateFour : selectedState config.state config.tape.head 4 =
      selectedState rule.sourceState rule.readSymbol 4 := by
    rw [hMatches.1, hMatches.2]
  have hStateFive : selectedState config.state config.tape.head 5 =
      selectedState rule.sourceState rule.readSymbol 5 := by
    rw [hMatches.1, hMatches.2]
  have hLookupThree' : findRule (compileWorkMachine machine).rules
      (compilePhaseTwo rule config).state (compilePhaseTwo rule config).tape.head =
      some (compiledWriteRule rule) := by
    rw [hStateTwo] at hLookupThree
    exact hLookupThree
  have hLookupFour' : findRule (compileWorkMachine machine).rules
      (compilePhaseThree rule config).state
      (compilePhaseThree rule config).tape.head =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 3)
        (selectedState rule.sourceState rule.readSymbol 4)
        (compilerSecondMove rule.move)
        (compilePhaseThree rule config).tape.head) := by
    rw [hStateThree, hStateFour] at hLookupFour
    exact hLookupFour
  have hLookupFive' : findRule (compileWorkMachine machine).rules
      (compilePhaseFour rule config).state
      (compilePhaseFour rule config).tape.head =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 4)
        (selectedState rule.sourceState rule.readSymbol 5)
        (compilerThirdMove rule.move)
        (compilePhaseFour rule config).tape.head) := by
    rw [hStateFour, hStateFive] at hLookupFive
    exact hLookupFive
  have hLookupSix' : findRule (compileWorkMachine machine).rules
      (compilePhaseFive rule config).state
      (compilePhaseFive rule config).tape.head =
      some (preserveRule
        (selectedState rule.sourceState rule.readSymbol 5)
        (boundaryState rule.targetState) (compilerFinalMove rule.move)
        (compilePhaseFive rule config).tape.head) := by
    rw [hStateFive] at hLookupSix
    exact hLookupSix
  have hStepOne := step?_eq_apply_of_find
    (compileWorkMachine machine) (encodeWorkConfiguration config)
    (dispatchRuleFor config.state config.tape.head.first) hRawHalted hLookupOne'
  have hStepTwo := step?_eq_apply_of_find
    (compileWorkMachine machine) (compilePhaseOne config)
    (compiledSelectRule rule) hHaltedOne hLookupTwo'
  have hStepThree := step?_eq_apply_of_find
    (compileWorkMachine machine) (compilePhaseTwo rule config)
    (compiledWriteRule rule) hHaltedTwo hLookupThree'
  have hStepFour := step?_eq_apply_of_find
    (compileWorkMachine machine) (compilePhaseThree rule config)
    (preserveRule
      (selectedState rule.sourceState rule.readSymbol 3)
      (selectedState rule.sourceState rule.readSymbol 4)
      (compilerSecondMove rule.move)
      (compilePhaseThree rule config).tape.head)
    hHaltedThree hLookupFour'
  have hStepFive := step?_eq_apply_of_find
    (compileWorkMachine machine) (compilePhaseFour rule config)
    (preserveRule
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5)
      (compilerThirdMove rule.move)
      (compilePhaseFour rule config).tape.head)
    hHaltedFour hLookupFive'
  have hStepSix := step?_eq_apply_of_find
    (compileWorkMachine machine) (compilePhaseFive rule config)
    (preserveRule
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) (compilerFinalMove rule.move)
      (compilePhaseFive rule config).tape.head)
    hHaltedFive hLookupSix'
  rw [run_succ, hStepOne]
  change run (compileWorkMachine machine) 5 (compilePhaseOne config) = _
  rw [run_succ, hStepTwo]
  change run (compileWorkMachine machine) 4 (compilePhaseTwo rule config) = _
  rw [run_succ, hStepThree]
  change run (compileWorkMachine machine) 3 (compilePhaseThree rule config) = _
  rw [run_succ, hStepFour]
  change run (compileWorkMachine machine) 2 (compilePhaseFour rule config) = _
  rw [run_succ, hStepFive]
  change run (compileWorkMachine machine) 1 (compilePhaseFive rule config) = _
  rw [run_succ, hStepSix]
  change compilePhaseSix rule config = _
  exact compilePhaseSix_eq_encode_apply rule config

/-- A successful work step exposes the selected rule and its two lookup
conditions. -/
theorem workStep?_some_exists (machine : WorkMachine)
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    ∃ rule, machine.isHalted config = false ∧
      findWorkRule machine.rules config.state config.tape.head = some rule ∧
      next = applyWorkRule rule config := by
  cases hHalted : machine.isHalted config with
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction
  | false =>
      cases hFind : findWorkRule machine.rules config.state config.tape.head with
      | none =>
          unfold workStep? at hStep
          rw [hHalted, hFind] at hStep
          contradiction
      | some rule =>
          refine ⟨rule, rfl, rfl, ?_⟩
          have hApply := workStep?_eq_apply_of_find
            machine config rule hHalted hFind
          exact (Option.some.inj (hApply.symm.trans hStep)).symm

/-- Every successful work transition is simulated by exactly six raw
transitions. -/
theorem run_compileWorkMachine_six_of_workStep (machine : WorkMachine)
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    run (compileWorkMachine machine) 6 (encodeWorkConfiguration config) =
      encodeWorkConfiguration next := by
  rcases workStep?_some_exists machine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  rw [hNext]
  exact run_compileWorkMachine_six_of_selected
    machine config rule hHalted hFind

/-- A raw configuration with no successor is stable under every fuel budget. -/
theorem run_eq_self_of_step?_eq_none (machine : Machine)
    (config : Configuration) (fuel : Nat)
    (hStep : step? machine config = none) :
    run machine fuel config = config := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        (match step? machine config with
         | none => config
         | some next => run machine fuel next) = config
      rw [hStep]

/-- Splitting a raw fuel budget runs the first part before the second. -/
theorem run_add (machine : Machine) (first second : Nat)
    (config : Configuration) :
    run machine (first + second) config =
      run machine second (run machine first config) := by
  induction first generalizing config with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      change
        (match step? machine config with
         | none => config
         | some next => run machine (first + second) next) =
        run machine second
          (match step? machine config with
           | none => config
           | some next => run machine first next)
      cases hStep : step? machine config with
      | none =>
          exact (run_eq_self_of_step?_eq_none machine config second hStep).symm
      | some next => exact ih next

/-- A selected work transition may be followed by any additional raw fuel. -/
theorem run_compileWorkMachine_add_six_of_selected (machine : WorkMachine)
    (config : WorkConfiguration) (rule : WorkRule) (fuel : Nat)
    (hHalted : machine.isHalted config = false)
    (hFind : findWorkRule machine.rules config.state config.tape.head = some rule) :
    run (compileWorkMachine machine) (fuel + 6)
        (encodeWorkConfiguration config) =
      run (compileWorkMachine machine) fuel
        (encodeWorkConfiguration (applyWorkRule rule config)) := by
  rw [Nat.add_comm fuel 6]
  rw [run_add]
  rw [run_compileWorkMachine_six_of_selected machine config rule hHalted hFind]

/-- A successful work transition may be followed by any additional raw fuel. -/
theorem run_compileWorkMachine_add_six_of_workStep (machine : WorkMachine)
    (config next : WorkConfiguration) (fuel : Nat)
    (hStep : workStep? machine config = some next) :
    run (compileWorkMachine machine) (fuel + 6)
        (encodeWorkConfiguration config) =
      run (compileWorkMachine machine) fuel (encodeWorkConfiguration next) := by
  rw [Nat.add_comm fuel 6]
  rw [run_add]
  rw [run_compileWorkMachine_six_of_workStep machine config next hStep]

private theorem six_mul_succ_add (steps fuel : Nat) :
    6 * (steps + 1) + fuel = (6 * steps + fuel) + 6 := by
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.add_assoc]
  rw [Nat.add_comm 6 fuel]
  rw [← Nat.add_assoc]

/-- An exact work execution is simulated at six raw transitions per work
transition, with an arbitrary raw suffix budget. -/
theorem run_compileWorkMachine_add_mul_of_workRunExact
    (machine : WorkMachine) (steps fuel : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    run (compileWorkMachine machine) (6 * steps + fuel)
        (encodeWorkConfiguration config) =
      run (compileWorkMachine machine) fuel
        (encodeWorkConfiguration final) := by
  induction steps generalizing config with
  | zero =>
      change some config = some final at hRun
      have hConfig : config = final := Option.some.inj hRun
      cases hConfig
      rw [Nat.zero_add]
  | succ steps ih =>
      cases hStep : workStep? machine config with
      | none =>
          change
            (match workStep? machine config with
             | none => none
             | some next => workRunExact? machine steps next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine steps next = some final := by
            change
              (match workStep? machine config with
               | none => none
               | some next => workRunExact? machine steps next) = some final at hRun
            rw [hStep] at hRun
            exact hRun
          rw [six_mul_succ_add]
          exact (run_compileWorkMachine_add_six_of_workStep
            machine config next (6 * steps + fuel) hStep).trans
              (ih next hTail)

/-- An exact `steps`-transition work execution is simulated by exactly
`6 * steps` raw transitions. -/
theorem run_compileWorkMachine_mul_of_workRunExact
    (machine : WorkMachine) (steps : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    run (compileWorkMachine machine) (6 * steps)
        (encodeWorkConfiguration config) =
      encodeWorkConfiguration final := by
  exact run_compileWorkMachine_add_mul_of_workRunExact
    machine steps 0 config final hRun

/-- A halting raw configuration has no successor. -/
theorem step?_eq_none_of_isHalted (machine : Machine)
    (config : Configuration) (hHalted : machine.isHalted config = true) :
    step? machine config = none := by
  unfold step?
  exact if_pos hHalted

/-- A halting work configuration has no successor. -/
theorem workStep?_eq_none_of_isHalted (machine : WorkMachine)
    (config : WorkConfiguration)
    (hHalted : machine.isHalted config = true) :
    workStep? machine config = none := by
  unfold workStep?
  exact if_pos hHalted

/-- A halting raw configuration is stable under every fuel budget. -/
theorem run_eq_self_of_isHalted (machine : Machine)
    (config : Configuration) (fuel : Nat)
    (hHalted : machine.isHalted config = true) :
    run machine fuel config = config :=
  run_eq_self_of_step?_eq_none machine config fuel
    (step?_eq_none_of_isHalted machine config hHalted)

/-- An encoded halting work configuration is stable under any further raw
fuel. -/
theorem run_compileWorkMachine_encode_eq_of_halted (machine : WorkMachine)
    (config : WorkConfiguration) (fuel : Nat)
    (hHalted : machine.isHalted config = true) :
    run (compileWorkMachine machine) fuel (encodeWorkConfiguration config) =
      encodeWorkConfiguration config := by
  apply run_eq_self_of_isHalted
  exact (compileWorkMachine_isHalted_encode machine config).trans hHalted

private theorem exists_eq_add_of_le_constructive {small large : Nat}
    (hLe : small ≤ large) : ∃ rest, large = small + rest := by
  induction hLe with
  | refl => exact ⟨0, rfl⟩
  | @step next hLe ih =>
      rcases ih with ⟨rest, hRest⟩
      refine ⟨rest + 1, ?_⟩
      rw [hRest]
      rfl

/-- Once an exact work trace reaches a halting configuration, every raw fuel
budget at least six times the trace length reaches the corresponding encoded
configuration and remains there. -/
theorem run_compileWorkMachine_of_workRunExact_halted_le
    (machine : WorkMachine) (steps rawFuel : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final)
    (hHalted : machine.isHalted final = true)
    (hLe : 6 * steps ≤ rawFuel) :
    run (compileWorkMachine machine) rawFuel
        (encodeWorkConfiguration config) =
      encodeWorkConfiguration final := by
  rcases exists_eq_add_of_le_constructive hLe with ⟨remaining, hFuel⟩
  rw [hFuel]
  exact (run_compileWorkMachine_add_mul_of_workRunExact
    machine steps remaining config final hRun).trans
      (run_compileWorkMachine_encode_eq_of_halted
        machine final remaining hHalted)

/-- A sufficiently padded exact work trace ending in acceptance leaves the
compiled raw machine in its designated accept state. -/
theorem run_compileWorkMachine_halted_le_acceptState
    (machine : WorkMachine) (steps rawFuel : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final)
    (hHalted : machine.isHalted final = true)
    (hAccept : final.state = machine.acceptState)
    (hLe : 6 * steps ≤ rawFuel) :
    (run (compileWorkMachine machine) rawFuel
      (encodeWorkConfiguration config)).state =
        (compileWorkMachine machine).acceptState := by
  rw [run_compileWorkMachine_of_workRunExact_halted_le
    machine steps rawFuel config final hRun hHalted hLe]
  unfold encodeWorkConfiguration compileWorkMachine
  exact congrArg boundaryState hAccept

/-- A sufficiently padded exact work trace ending in rejection leaves the
compiled raw machine in its designated reject state. -/
theorem run_compileWorkMachine_halted_le_rejectState
    (machine : WorkMachine) (steps rawFuel : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final)
    (hHalted : machine.isHalted final = true)
    (hReject : final.state = machine.rejectState)
    (hLe : 6 * steps ≤ rawFuel) :
    (run (compileWorkMachine machine) rawFuel
      (encodeWorkConfiguration config)).state =
        (compileWorkMachine machine).rejectState := by
  rw [run_compileWorkMachine_of_workRunExact_halted_le
    machine steps rawFuel config final hRun hHalted hLe]
  unfold encodeWorkConfiguration compileWorkMachine
  exact congrArg boundaryState hReject

/-- At an exact simulated budget, raw acceptance is exactly acceptance of the
work trace's final configuration. -/
theorem run_compileWorkMachine_mul_accept_iff
    (machine : WorkMachine) (steps : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    (run (compileWorkMachine machine) (6 * steps)
      (encodeWorkConfiguration config)).state =
        (compileWorkMachine machine).acceptState ↔
      final.state = machine.acceptState := by
  have hSimulation := run_compileWorkMachine_mul_of_workRunExact
    machine steps config final hRun
  constructor
  · intro hAccept
    rw [hSimulation] at hAccept
    unfold encodeWorkConfiguration compileWorkMachine at hAccept
    exact boundaryState_injective hAccept
  · intro hAccept
    rw [hSimulation]
    unfold encodeWorkConfiguration compileWorkMachine
    exact congrArg boundaryState hAccept

/-- An encoded boundary configuration is in the compiled accept state exactly
when its work configuration is accepting. -/
theorem encodeWorkConfiguration_accept_iff (machine : WorkMachine)
    (config : WorkConfiguration) :
    (encodeWorkConfiguration config).state =
        (compileWorkMachine machine).acceptState ↔
      config.state = machine.acceptState := by
  constructor
  · intro hAccept
    unfold encodeWorkConfiguration compileWorkMachine at hAccept
    exact boundaryState_injective hAccept
  · intro hAccept
    unfold encodeWorkConfiguration compileWorkMachine
    exact congrArg boundaryState hAccept

/-- At an exact simulated budget, raw rejection is exactly rejection of the
work trace's final configuration. -/
theorem run_compileWorkMachine_mul_reject_iff
    (machine : WorkMachine) (steps : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    (run (compileWorkMachine machine) (6 * steps)
      (encodeWorkConfiguration config)).state =
        (compileWorkMachine machine).rejectState ↔
      final.state = machine.rejectState := by
  have hSimulation := run_compileWorkMachine_mul_of_workRunExact
    machine steps config final hRun
  constructor
  · intro hReject
    rw [hSimulation] at hReject
    unfold encodeWorkConfiguration compileWorkMachine at hReject
    exact boundaryState_injective hReject
  · intro hReject
    rw [hSimulation]
    unfold encodeWorkConfiguration compileWorkMachine
    exact congrArg boundaryState hReject

/-- An encoded boundary configuration is in the compiled reject state exactly
when its work configuration is rejecting. -/
theorem encodeWorkConfiguration_reject_iff (machine : WorkMachine)
    (config : WorkConfiguration) :
    (encodeWorkConfiguration config).state =
        (compileWorkMachine machine).rejectState ↔
      config.state = machine.rejectState := by
  constructor
  · intro hReject
    unfold encodeWorkConfiguration compileWorkMachine at hReject
    exact boundaryState_injective hReject
  · intro hReject
    unfold encodeWorkConfiguration compileWorkMachine
    exact congrArg boundaryState hReject

/-- At an exact simulated budget, the compiled and work machines agree on
whether their final configurations are halting. -/
theorem run_compileWorkMachine_mul_isHalted
    (machine : WorkMachine) (steps : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    (compileWorkMachine machine).isHalted
        (run (compileWorkMachine machine) (6 * steps)
          (encodeWorkConfiguration config)) =
      machine.isHalted final := by
  rw [run_compileWorkMachine_mul_of_workRunExact
    machine steps config final hRun]
  exact compileWorkMachine_isHalted_encode machine final

/-- A work configuration with no successor is stable under every fuel
budget. -/
theorem workRun_eq_self_of_workStep?_eq_none (machine : WorkMachine)
    (config : WorkConfiguration) (fuel : Nat)
    (hStep : workStep? machine config = none) :
    workRun machine fuel config = config := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        (match workStep? machine config with
         | none => config
         | some next => workRun machine fuel next) = config
      rw [hStep]

/-- A halting work configuration is stable under every work fuel budget. -/
theorem workRun_eq_self_of_isHalted (machine : WorkMachine)
    (config : WorkConfiguration) (fuel : Nat)
    (hHalted : machine.isHalted config = true) :
    workRun machine fuel config = config :=
  workRun_eq_self_of_workStep?_eq_none machine config fuel
    (workStep?_eq_none_of_isHalted machine config hHalted)

/-- Splitting a work fuel budget runs the first part before the second. -/
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
          exact (workRun_eq_self_of_workStep?_eq_none
            machine config second hStep).symm
      | some next => exact ih next

/-- Forgetting the early-stop witness from an exact work run yields the same
ordinary bounded run at that exact transition count. -/
theorem workRun_eq_of_workRunExact (machine : WorkMachine) (steps : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final) :
    workRun machine steps config = final := by
  induction steps generalizing config with
  | zero =>
      change some config = some final at hRun
      exact Option.some.inj hRun
  | succ steps ih =>
      cases hStep : workStep? machine config with
      | none =>
          change
            (match workStep? machine config with
             | none => none
             | some next => workRunExact? machine steps next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine steps next = some final := by
            change
              (match workStep? machine config with
               | none => none
               | some next => workRunExact? machine steps next) = some final at hRun
            rw [hStep] at hRun
            exact hRun
          change
            (match workStep? machine config with
             | none => config
             | some next => workRun machine steps next) = final
          rw [hStep]
          exact ih next hTail

/-- Once an exact work trace reaches a halting configuration, every larger
work fuel budget has the same final configuration. -/
theorem workRun_of_workRunExact_halted_le
    (machine : WorkMachine) (steps fuel : Nat)
    (config final : WorkConfiguration)
    (hRun : workRunExact? machine steps config = some final)
    (hHalted : machine.isHalted final = true)
    (hLe : steps ≤ fuel) :
    workRun machine fuel config = final := by
  rcases exists_eq_add_of_le_constructive hLe with ⟨remaining, hFuel⟩
  rw [hFuel, workRun_add]
  rw [workRun_eq_of_workRunExact machine steps config final hRun]
  exact workRun_eq_self_of_isHalted machine final remaining hHalted

/-- Work bounded acceptance is exactly acceptance of its final bounded-run
configuration. -/
theorem workBoundedDecide_accept_iff_final (machine : WorkMachine)
    (fuel : Nat) (initialTape : WorkTape) :
    workBoundedDecide machine fuel initialTape = .accept ↔
      (workRun machine fuel
        (workStartConfiguration machine initialTape)).state =
          machine.acceptState := by
  let final := workRun machine fuel
    (workStartConfiguration machine initialTape)
  change
    (if final.state == machine.acceptState then
       WorkVerdict.accept
     else if final.state == machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.accept ↔
      final.state = machine.acceptState
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      constructor
      · intro _
        exact (nat_beq_true_iff final.state machine.acceptState).mp hAccept
      · intro _
        rw [if_pos rfl]
  | false =>
      constructor
      · intro hVerdict
        rw [if_neg Bool.false_ne_true] at hVerdict
        by_cases hReject : (final.state == machine.rejectState) = true
        · rw [if_pos hReject] at hVerdict
          contradiction
        · rw [if_neg hReject] at hVerdict
          contradiction
      · intro hState
        have hTrue :=
          (nat_beq_true_iff final.state machine.acceptState).mpr hState
        rw [hAccept] at hTrue
        contradiction

/-- Work bounded rejection means that acceptance failed and the final state is
the designated reject state.  The first conjunct records the interpreter's
accept-before-reject priority when the two designated states coincide. -/
theorem workBoundedDecide_reject_iff_final (machine : WorkMachine)
    (fuel : Nat) (initialTape : WorkTape) :
    workBoundedDecide machine fuel initialTape = .reject ↔
      (workRun machine fuel
        (workStartConfiguration machine initialTape)).state ≠
          machine.acceptState ∧
      (workRun machine fuel
        (workStartConfiguration machine initialTape)).state =
          machine.rejectState := by
  let final := workRun machine fuel
    (workStartConfiguration machine initialTape)
  change
    (if final.state == machine.acceptState then
       WorkVerdict.accept
     else if final.state == machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.reject ↔
      final.state ≠ machine.acceptState ∧
        final.state = machine.rejectState
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      constructor
      · intro hVerdict
        rw [if_pos rfl] at hVerdict
        contradiction
      · intro hFinal
        have hEq :=
          (nat_beq_true_iff final.state machine.acceptState).mp hAccept
        exact False.elim (hFinal.1 hEq)
  | false =>
      have hNotAccept : final.state ≠ machine.acceptState := by
        intro hEq
        have hTrue :=
          (nat_beq_true_iff final.state machine.acceptState).mpr hEq
        rw [hAccept] at hTrue
        contradiction
      cases hReject : (final.state == machine.rejectState) with
      | true =>
          constructor
          · intro _
            exact ⟨hNotAccept,
              (nat_beq_true_iff final.state machine.rejectState).mp hReject⟩
          · intro _
            rw [if_neg Bool.false_ne_true, if_pos rfl]
      | false =>
          constructor
          · intro hVerdict
            rw [if_neg Bool.false_ne_true,
              if_neg Bool.false_ne_true] at hVerdict
            contradiction
          · intro hFinal
            have hTrue :=
              (nat_beq_true_iff final.state machine.rejectState).mpr hFinal.2
            rw [hReject] at hTrue
            contradiction

/-- A work bounded decision is non-timeout exactly when its final state is
halting. -/
theorem workBoundedDecide_ne_timeout_iff_final_isHalted
    (machine : WorkMachine) (fuel : Nat) (initialTape : WorkTape) :
    workBoundedDecide machine fuel initialTape ≠ .timeout ↔
      machine.isHalted
        (workRun machine fuel
          (workStartConfiguration machine initialTape)) = true := by
  let final := workRun machine fuel
    (workStartConfiguration machine initialTape)
  change
    (if final.state == machine.acceptState then
       WorkVerdict.accept
     else if final.state == machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) ≠ WorkVerdict.timeout ↔
      ((final.state == machine.acceptState) ||
        (final.state == machine.rejectState)) = true
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      rw [if_pos rfl]
      constructor
      · intro _
        rfl
      · intro _ hImpossible
        contradiction
  | false =>
      cases hReject : (final.state == machine.rejectState) with
      | true =>
          rw [if_neg Bool.false_ne_true, if_pos rfl]
          constructor
          · intro _
            rfl
          · intro _ hImpossible
            contradiction
      | false =>
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
          constructor
          · intro hImpossible
            exact False.elim (hImpossible rfl)
          · intro hImpossible
            contradiction

/-- Raw bounded acceptance is exactly acceptance of its final bounded-run
configuration. -/
theorem boundedDecide_accept_iff_final (machine : Machine)
    (fuel : Nat) (input : BitString) :
    boundedDecide machine fuel input = .accept ↔
      (run machine fuel (startConfig machine input)).state =
        machine.acceptState := by
  let final := run machine fuel (startConfig machine input)
  change
    (if final.state == machine.acceptState then
       Verdict.accept
     else if final.state == machine.rejectState then
       Verdict.reject
     else Verdict.timeout) = Verdict.accept ↔
      final.state = machine.acceptState
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      constructor
      · intro _
        exact (nat_beq_true_iff final.state machine.acceptState).mp hAccept
      · intro _
        rw [if_pos rfl]
  | false =>
      constructor
      · intro hVerdict
        rw [if_neg Bool.false_ne_true] at hVerdict
        by_cases hReject : (final.state == machine.rejectState) = true
        · rw [if_pos hReject] at hVerdict
          contradiction
        · rw [if_neg hReject] at hVerdict
          contradiction
      · intro hState
        have hTrue :=
          (nat_beq_true_iff final.state machine.acceptState).mpr hState
        rw [hAccept] at hTrue
        contradiction

/-- Raw bounded rejection means that acceptance failed and the final state is
the designated reject state. -/
theorem boundedDecide_reject_iff_final (machine : Machine)
    (fuel : Nat) (input : BitString) :
    boundedDecide machine fuel input = .reject ↔
      (run machine fuel (startConfig machine input)).state ≠
          machine.acceptState ∧
      (run machine fuel (startConfig machine input)).state =
          machine.rejectState := by
  let final := run machine fuel (startConfig machine input)
  change
    (if final.state == machine.acceptState then
       Verdict.accept
     else if final.state == machine.rejectState then
       Verdict.reject
     else Verdict.timeout) = Verdict.reject ↔
      final.state ≠ machine.acceptState ∧
        final.state = machine.rejectState
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      constructor
      · intro hVerdict
        rw [if_pos rfl] at hVerdict
        contradiction
      · intro hFinal
        have hEq :=
          (nat_beq_true_iff final.state machine.acceptState).mp hAccept
        exact False.elim (hFinal.1 hEq)
  | false =>
      have hNotAccept : final.state ≠ machine.acceptState := by
        intro hEq
        have hTrue :=
          (nat_beq_true_iff final.state machine.acceptState).mpr hEq
        rw [hAccept] at hTrue
        contradiction
      cases hReject : (final.state == machine.rejectState) with
      | true =>
          constructor
          · intro _
            exact ⟨hNotAccept,
              (nat_beq_true_iff final.state machine.rejectState).mp hReject⟩
          · intro _
            rw [if_neg Bool.false_ne_true, if_pos rfl]
      | false =>
          constructor
          · intro hVerdict
            rw [if_neg Bool.false_ne_true,
              if_neg Bool.false_ne_true] at hVerdict
            contradiction
          · intro hFinal
            have hTrue :=
              (nat_beq_true_iff final.state machine.rejectState).mpr hFinal.2
            rw [hReject] at hTrue
            contradiction

/-- A raw bounded decision is non-timeout exactly when its final state is
halting. -/
theorem boundedDecide_ne_timeout_iff_final_isHalted
    (machine : Machine) (fuel : Nat) (input : BitString) :
    boundedDecide machine fuel input ≠ .timeout ↔
      machine.isHalted (run machine fuel (startConfig machine input)) = true := by
  let final := run machine fuel (startConfig machine input)
  change
    (if final.state == machine.acceptState then
       Verdict.accept
     else if final.state == machine.rejectState then
       Verdict.reject
     else Verdict.timeout) ≠ Verdict.timeout ↔
      ((final.state == machine.acceptState) ||
        (final.state == machine.rejectState)) = true
  cases hAccept : (final.state == machine.acceptState) with
  | true =>
      rw [if_pos rfl]
      constructor
      · intro _
        rfl
      · intro _ hImpossible
        contradiction
  | false =>
      cases hReject : (final.state == machine.rejectState) with
      | true =>
          rw [if_neg Bool.false_ne_true, if_pos rfl]
          constructor
          · intro _
            rfl
          · intro _ hImpossible
            contradiction
      | false =>
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
          constructor
          · intro hImpossible
            exact False.elim (hImpossible rfl)
          · intro hImpossible
            contradiction

/-- Under an exact halting trace and sufficient work/raw budgets, work
acceptance is equivalent to the compiled raw run ending in its accept state. -/
theorem workBoundedDecide_accept_iff_compiled_run
    (machine : WorkMachine) (steps workFuel rawFuel : Nat)
    (initialTape : WorkTape) (final : WorkConfiguration)
    (hRun : workRunExact? machine steps
      (workStartConfiguration machine initialTape) = some final)
    (hHalted : machine.isHalted final = true)
    (hWorkLe : steps ≤ workFuel)
    (hRawLe : 6 * steps ≤ rawFuel) :
    workBoundedDecide machine workFuel initialTape = .accept ↔
      (run (compileWorkMachine machine) rawFuel
        (encodeWorkConfiguration
          (workStartConfiguration machine initialTape))).state =
        (compileWorkMachine machine).acceptState := by
  have hWorkFinal := workRun_of_workRunExact_halted_le
    machine steps workFuel
    (workStartConfiguration machine initialTape) final
    hRun hHalted hWorkLe
  have hRawFinal := run_compileWorkMachine_of_workRunExact_halted_le
    machine steps rawFuel
    (workStartConfiguration machine initialTape) final
    hRun hHalted hRawLe
  constructor
  · intro hVerdict
    have hAccept :=
      (workBoundedDecide_accept_iff_final
        machine workFuel initialTape).mp hVerdict
    rw [hWorkFinal] at hAccept
    rw [hRawFinal]
    unfold encodeWorkConfiguration compileWorkMachine
    exact congrArg boundaryState hAccept
  · intro hRawAccept
    rw [hRawFinal] at hRawAccept
    have hAccept : final.state = machine.acceptState := by
      unfold encodeWorkConfiguration compileWorkMachine at hRawAccept
      exact boundaryState_injective hRawAccept
    apply (workBoundedDecide_accept_iff_final
      machine workFuel initialTape).mpr
    rw [hWorkFinal]
    exact hAccept

end PNP.Concrete
