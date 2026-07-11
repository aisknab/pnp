/-
Copyright (c) 2026 PNP Labs.

A finite raw-machine-to-work-machine simulator over boundary-marked pipeline
tapes.  Public control-state tags are collision-free; designated halts use
fresh accept/reject sentinels; terminal-source entry rules are omitted; and
entry selection preserves the raw interpreter's first-match rule order.

The local result simulates one successful raw `step?` by exactly three work
transitions from any `PipelineTape.Represents` frame, including arbitrary
exterior garbage.  The finite-run result iterates this over every exact chain
of `n` successful raw transitions, using exactly `3 * n` work transitions and
a compiled raw fuel budget of `18 * n` to reach the encoded endpoint.

This module does not construct a frame from raw input, prove arbitrary
at-most-run or bounded-verdict preservation, decode or hand off output,
provide a pipeline refinement or end-to-end input-size polynomial bound,
establish a complexity-class equality, or prove `P = NP`.
-/

import PNP.Concrete.PipelineTapeGeometry

namespace PNP.Concrete

namespace PipelineMachineSimulation

open PipelineTape

def allWorkSymbols : List WorkSymbol :=
  [WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
   WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

def allDataSymbols : List TapeSymbol := [.blank, .zero, .one]

def findIndexedRawRuleFrom :
    List Rule → Nat → TapeSymbol → Nat → Option (Nat × Rule)
  | [], _, _, _ => none
  | rule :: rest, state, symbol, index =>
      if rule.sourceState == state && rule.readSymbol == symbol then
        some (index, rule)
      else
        findIndexedRawRuleFrom rest state symbol (index + 1)

def findIndexedRawRule (rules : List Rule) (state : Nat)
    (symbol : TapeSymbol) : Option (Nat × Rule) :=
  findIndexedRawRuleFrom rules state symbol 0

theorem findIndexedRawRuleFrom_map_snd (rules : List Rule)
    (state : Nat) (symbol : TapeSymbol) (index : Nat) :
    Option.map Prod.snd (findIndexedRawRuleFrom rules state symbol index) =
      findRule rules state symbol := by
  induction rules generalizing index with
  | nil => rfl
  | cons rule rest ih =>
      unfold findIndexedRawRuleFrom findRule
      cases hMatch : ((rule.sourceState == state) &&
          (rule.readSymbol == symbol)) with
      | false =>
          rw [if_neg (by intro impossible; contradiction),
            if_neg (by intro impossible; contradiction)]
          exact ih (index + 1)
      | true =>
          rw [if_pos rfl, if_pos rfl]
          rfl

theorem findIndexedRawRule_of_findRule_some {rules : List Rule}
    {state : Nat} {symbol : TapeSymbol} {rule : Rule}
    (h : findRule rules state symbol = some rule) :
    ∃ index, findIndexedRawRule rules state symbol = some (index, rule) := by
  have hMap := findIndexedRawRuleFrom_map_snd rules state symbol 0
  rw [h] at hMap
  cases hFound : findIndexedRawRule rules state symbol with
  | none =>
      unfold findIndexedRawRule at hFound
      rw [hFound] at hMap
      contradiction
  | some pair =>
      rcases pair with ⟨index, selected⟩
      unfold findIndexedRawRule at hFound
      rw [hFound] at hMap
      have hSelected : selected = rule := Option.some.inj hMap
      cases hSelected
      exact ⟨index, rfl⟩

theorem findIndexedRawRuleFrom_index_ge
    {rules : List Rule} {state : Nat} {symbol : TapeSymbol}
    {start index : Nat} {rule : Rule}
    (h : findIndexedRawRuleFrom rules state symbol start =
      some (index, rule)) : start ≤ index := by
  induction rules generalizing start with
  | nil => contradiction
  | cons first rest ih =>
      unfold findIndexedRawRuleFrom at h
      split at h
      · have hPair : (start, first) = (index, rule) := Option.some.inj h
        exact Nat.le_of_eq (congrArg Prod.fst hPair)
      · have hTail := ih h
        exact Nat.le_trans (Nat.le_succ start) hTail

def interiorRule (source target : Nat) (symbol : TapeSymbol) : WorkRule :=
  { sourceState := source
    readSymbol := dataSymbol symbol
    targetState := target
    writeSymbol := dataSymbol symbol
    move := .stay }

/-- Public namespaces used by the exact-three-step raw-machine lift. -/
inductive Phase where
  | main
  | stayOne
  | stayTwo
  | inspectLeft
  | finishLeft
  | extendLeft
  | inspectRight
  | finishRight
  | extendRight
  | accept
  | reject
deriving DecidableEq, Repr

def tagStep (value : Nat) : Nat :=
  Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ value))))))))))

def taggedState : Nat → Phase → Nat
  | 0, .main => 0
  | 0, .stayOne => 1
  | 0, .stayTwo => 2
  | 0, .inspectLeft => 3
  | 0, .finishLeft => 4
  | 0, .extendLeft => 5
  | 0, .inspectRight => 6
  | 0, .finishRight => 7
  | 0, .extendRight => 8
  | 0, .accept => 9
  | 0, .reject => 10
  | payload + 1, phase => tagStep (taggedState payload phase)

theorem tagStep_injective {left right : Nat}
    (h : tagStep left = tagStep right) : left = right := by
  exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
    (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))))))))))

theorem taggedState_zero_ne_succ (leftPhase rightPhase : Phase)
    (payload : Nat) :
    taggedState 0 leftPhase ≠ taggedState (payload + 1) rightPhase := by
  intro h
  cases leftPhase with
  | main => contradiction
  | stayOne =>
      have h1 := Nat.succ.inj h
      contradiction
  | stayTwo =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      contradiction
  | inspectLeft =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      contradiction
  | finishLeft =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      contradiction
  | extendLeft =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      contradiction
  | inspectRight =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      have h6 := Nat.succ.inj h5
      contradiction
  | finishRight =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      have h6 := Nat.succ.inj h5
      have h7 := Nat.succ.inj h6
      contradiction
  | extendRight =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      have h6 := Nat.succ.inj h5
      have h7 := Nat.succ.inj h6
      have h8 := Nat.succ.inj h7
      contradiction
  | accept =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      have h6 := Nat.succ.inj h5
      have h7 := Nat.succ.inj h6
      have h8 := Nat.succ.inj h7
      have h9 := Nat.succ.inj h8
      contradiction
  | reject =>
      have h1 := Nat.succ.inj h
      have h2 := Nat.succ.inj h1
      have h3 := Nat.succ.inj h2
      have h4 := Nat.succ.inj h3
      have h5 := Nat.succ.inj h4
      have h6 := Nat.succ.inj h5
      have h7 := Nat.succ.inj h6
      have h8 := Nat.succ.inj h7
      have h9 := Nat.succ.inj h8
      have h10 := Nat.succ.inj h9
      contradiction

theorem taggedState_injective {leftPayload rightPayload : Nat}
    {leftPhase rightPhase : Phase}
    (h : taggedState leftPayload leftPhase = taggedState rightPayload rightPhase) :
    leftPayload = rightPayload ∧ leftPhase = rightPhase := by
  induction leftPayload generalizing rightPayload with
  | zero =>
      cases rightPayload with
      | zero =>
          cases leftPhase <;> cases rightPhase <;>
            first | exact ⟨rfl, rfl⟩ | contradiction
      | succ rightPayload =>
          exact False.elim (taggedState_zero_ne_succ
            leftPhase rightPhase rightPayload h)
  | succ leftPayload ih =>
      cases rightPayload with
      | zero =>
          exact False.elim (taggedState_zero_ne_succ
            rightPhase leftPhase leftPayload h.symm)
      | succ rightPayload =>
          have hInner := tagStep_injective h
          have hParts := ih hInner
          exact ⟨congrArg Nat.succ hParts.1, hParts.2⟩

theorem taggedState_ne_of_phase_ne {leftPayload rightPayload : Nat}
    {leftPhase rightPhase : Phase} (hPhase : leftPhase ≠ rightPhase) :
    taggedState leftPayload leftPhase ≠ taggedState rightPayload rightPhase := by
  intro h
  exact hPhase (taggedState_injective h).2

theorem taggedState_ne_of_payload_ne {leftPayload rightPayload : Nat}
    {leftPhase rightPhase : Phase} (hPayload : leftPayload ≠ rightPayload) :
    taggedState leftPayload leftPhase ≠ taggedState rightPayload rightPhase := by
  intro h
  exact hPayload (taggedState_injective h).1

def mainState (state : Nat) : Nat := taggedState state .main
def stayOneState (index : Nat) : Nat := taggedState index .stayOne
def stayTwoState (index : Nat) : Nat := taggedState index .stayTwo
def inspectLeftState (index : Nat) : Nat := taggedState index .inspectLeft
def finishLeftState (index : Nat) : Nat := taggedState index .finishLeft
def extendLeftState (index : Nat) : Nat := taggedState index .extendLeft
def inspectRightState (index : Nat) : Nat := taggedState index .inspectRight
def finishRightState (index : Nat) : Nat := taggedState index .finishRight
def extendRightState (index : Nat) : Nat := taggedState index .extendRight
def acceptSentinel : Nat := taggedState 0 .accept
def rejectSentinel : Nat := taggedState 0 .reject

@[simp] theorem mainState_eq (state : Nat) :
    mainState state = taggedState state .main := rfl
@[simp] theorem stayOneState_eq (index : Nat) :
    stayOneState index = taggedState index .stayOne := rfl
@[simp] theorem stayTwoState_eq (index : Nat) :
    stayTwoState index = taggedState index .stayTwo := rfl
@[simp] theorem inspectLeftState_eq (index : Nat) :
    inspectLeftState index = taggedState index .inspectLeft := rfl
@[simp] theorem finishLeftState_eq (index : Nat) :
    finishLeftState index = taggedState index .finishLeft := rfl
@[simp] theorem extendLeftState_eq (index : Nat) :
    extendLeftState index = taggedState index .extendLeft := rfl
@[simp] theorem inspectRightState_eq (index : Nat) :
    inspectRightState index = taggedState index .inspectRight := rfl
@[simp] theorem finishRightState_eq (index : Nat) :
    finishRightState index = taggedState index .finishRight := rfl
@[simp] theorem extendRightState_eq (index : Nat) :
    extendRightState index = taggedState index .extendRight := rfl

theorem mainState_injective {left right : Nat}
    (h : mainState left = mainState right) : left = right :=
  (taggedState_injective h).1

/-- Map terminal raw states to fresh sentinels and all other states to `main`. -/
def controlState (machine : Machine) (state : Nat) : Nat :=
  if state = machine.acceptState then acceptSentinel
  else if state = machine.rejectState then rejectSentinel
  else mainState state

theorem controlState_of_nonterminal (machine : Machine) (state : Nat)
    (hAccept : state ≠ machine.acceptState)
    (hReject : state ≠ machine.rejectState) :
    controlState machine state = mainState state := by
  unfold controlState
  rw [if_neg hAccept, if_neg hReject]

def entryRule (index : Nat) (rule : Rule) : WorkRule :=
  { sourceState := mainState rule.sourceState
    readSymbol := dataSymbol rule.readSymbol
    targetState := match rule.move with
      | .stay => stayOneState index
      | .left => inspectLeftState index
      | .right => inspectRightState index
    writeSymbol := dataSymbol rule.writeSymbol
    move := rule.move }

/-- Terminal-source entries are omitted; the interpreter would never use them. -/
def entryRulesFrom (machine : Machine) : List Rule → Nat → List WorkRule
  | [], _ => []
  | rule :: rest, index =>
      if rule.sourceState = machine.acceptState ∨
          rule.sourceState = machine.rejectState then
        entryRulesFrom machine rest (index + 1)
      else
        entryRule index rule :: entryRulesFrom machine rest (index + 1)

def stayOneRule (index : Nat) (rule : Rule) : WorkRule :=
  interiorRule (stayOneState index) (stayTwoState index) rule.writeSymbol

def stayTwoRule (machine : Machine) (index : Nat) (rule : Rule) : WorkRule :=
  interiorRule (stayTwoState index) (controlState machine rule.targetState)
    rule.writeSymbol

def leftBoundaryRule (index : Nat) : WorkRule :=
  { sourceState := inspectLeftState index
    readSymbol := leftMarker
    targetState := extendLeftState index
    writeSymbol := dataSymbol .blank
    move := .left }

def rightBoundaryRule (index : Nat) : WorkRule :=
  { sourceState := inspectRightState index
    readSymbol := rightMarker
    targetState := extendRightState index
    writeSymbol := dataSymbol .blank
    move := .right }

def leftExtensionRule (machine : Machine) (index : Nat) (rule : Rule)
    (symbol : WorkSymbol) : WorkRule :=
  { sourceState := extendLeftState index
    readSymbol := symbol
    targetState := controlState machine rule.targetState
    writeSymbol := leftMarker
    move := .right }

def rightExtensionRule (machine : Machine) (index : Nat) (rule : Rule)
    (symbol : WorkSymbol) : WorkRule :=
  { sourceState := extendRightState index
    readSymbol := symbol
    targetState := controlState machine rule.targetState
    writeSymbol := rightMarker
    move := .left }

def dataRules (source target : Nat) : List WorkRule :=
  allDataSymbols.map (interiorRule source target)

def continuationRulesFor (machine : Machine) (index : Nat)
    (rule : Rule) : List WorkRule :=
  match rule.move with
  | .stay => [stayOneRule index rule, stayTwoRule machine index rule]
  | .left =>
      dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState) ++
      [leftBoundaryRule index] ++
      allWorkSymbols.map (leftExtensionRule machine index rule)
  | .right =>
      dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState) ++
      [rightBoundaryRule index] ++
      allWorkSymbols.map (rightExtensionRule machine index rule)

def continuationRulesFrom (machine : Machine) : List Rule → Nat → List WorkRule
  | [], _ => []
  | rule :: rest, index =>
      continuationRulesFor machine index rule ++
        continuationRulesFrom machine rest (index + 1)

def liftMachine (machine : Machine) : WorkMachine :=
  { rules := entryRulesFrom machine machine.rules 0 ++
      continuationRulesFrom machine machine.rules 0
    startState := controlState machine machine.startState
    acceptState := acceptSentinel
    rejectState := rejectSentinel }

def liftConfiguration (machine : Machine) (raw : Configuration)
    (workTape : WorkTape) : WorkConfiguration :=
  { state := controlState machine raw.state, tape := workTape }

def RepresentsConfiguration (machine : Machine) (raw : Configuration)
    (work : WorkConfiguration) : Prop :=
  work.state = controlState machine raw.state ∧ Represents raw.tape work.tape

theorem machine_not_halted_parts {machine : Machine} {config : Configuration}
    (h : machine.isHalted config = false) :
    config.state ≠ machine.acceptState ∧ config.state ≠ machine.rejectState := by
  constructor
  · intro hEq
    unfold Machine.isHalted at h
    rw [hEq, nat_beq_true_iff _ _ |>.mpr rfl] at h
    contradiction
  · intro hEq
    unfold Machine.isHalted at h
    rw [hEq, nat_beq_true_iff _ _ |>.mpr rfl] at h
    cases hAccept : (machine.rejectState == machine.acceptState) with
    | false => rw [hAccept] at h; contradiction
    | true => rw [hAccept] at h; contradiction

theorem liftMachine_main_not_halted (machine : Machine) (state : Nat)
    (tape : WorkTape) :
    (liftMachine machine).isHalted
      { state := mainState state, tape := tape } = false := by
  unfold WorkMachine.isHalted liftMachine
  cases hAccept : (mainState state == acceptSentinel) with
  | true =>
      have hEq := nat_beq_true_iff _ _ |>.mp hAccept
      exact False.elim
        (taggedState_ne_of_phase_ne
          (leftPhase := .main) (rightPhase := .accept)
          (by intro h; contradiction) hEq)
  | false =>
      cases hReject : (mainState state == rejectSentinel) with
      | true =>
          have hEq := nat_beq_true_iff _ _ |>.mp hReject
          exact False.elim
            (taggedState_ne_of_phase_ne
              (leftPhase := .main) (rightPhase := .reject)
              (by intro h; contradiction) hEq)
      | false => rfl

theorem liftMachine_stage_not_halted (machine : Machine) (payload : Nat)
    (phase : Phase) (tape : WorkTape)
    (hAccept : phase ≠ .accept) (hReject : phase ≠ .reject) :
    (liftMachine machine).isHalted
      { state := taggedState payload phase, tape := tape } = false := by
  unfold WorkMachine.isHalted liftMachine
  cases hAcceptBool : (taggedState payload phase == acceptSentinel) with
  | true =>
      have hEq := nat_beq_true_iff _ _ |>.mp hAcceptBool
      exact False.elim (hAccept (taggedState_injective hEq).2)
  | false =>
      cases hRejectBool : (taggedState payload phase == rejectSentinel) with
      | true =>
          have hEq := nat_beq_true_iff _ _ |>.mp hRejectBool
          exact False.elim (hReject (taggedState_injective hEq).2)
      | false => rfl

theorem findEntryRulesFrom_of_findIndexedRawRuleFrom
    {machine : Machine} {rules : List Rule} {state : Nat}
    {symbol : TapeSymbol} {start index : Nat} {rule : Rule}
    (hState : state ≠ machine.acceptState ∧ state ≠ machine.rejectState)
    (hSelected : findIndexedRawRuleFrom rules state symbol start =
      some (index, rule)) :
    findWorkRule (entryRulesFrom machine rules start)
      (mainState state) (dataSymbol symbol) = some (entryRule index rule) := by
  induction rules generalizing start with
  | nil => contradiction
  | cons first rest ih =>
      unfold entryRulesFrom
      split
      next hTerminal =>
        unfold findIndexedRawRuleFrom at hSelected
        split at hSelected
        next hMatch =>
          have hRaw := rawRule_match_iff first state symbol |>.mp hMatch
          rcases hTerminal with hAccept | hReject
          · exact False.elim (hState.1 (hRaw.1.symm.trans hAccept))
          · exact False.elim (hState.2 (hRaw.1.symm.trans hReject))
        next => exact ih hSelected
      next hNonterminal =>
        unfold findIndexedRawRuleFrom at hSelected
        split at hSelected
        next hMatch =>
          have hPair : (start, first) = (index, rule) :=
            Option.some.inj hSelected
          have hIndex : start = index := congrArg Prod.fst hPair
          have hRule : first = rule := congrArg Prod.snd hPair
          have hRaw := rawRule_match_iff first state symbol |>.mp hMatch
          cases hIndex
          cases hRule
          exact findWorkRule_cons_of_matches _ _ _ _
            ⟨congrArg mainState hRaw.1, congrArg dataSymbol hRaw.2⟩
        next hNoMatch =>
          rw [findWorkRule_cons_of_not_matches]
          · exact ih hSelected
          · intro hEntry
            have hRaw : first.sourceState = state ∧
                first.readSymbol = symbol :=
              ⟨mainState_injective hEntry.1,
               dataSymbol_injective hEntry.2⟩
            exact hNoMatch (rawRule_match_iff first state symbol |>.mpr hRaw)

theorem find_dataRules (source target : Nat) (symbol : TapeSymbol) :
    findWorkRule (dataRules source target) source (dataSymbol symbol) =
      some (interiorRule source target symbol) := by
  change findWorkRule
    (interiorRule source target .blank ::
     interiorRule source target .zero ::
     interiorRule source target .one :: []) source (dataSymbol symbol) = _
  cases symbol with
  | blank =>
      exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
  | zero =>
      rw [findWorkRule_cons_of_not_matches]
      · exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      · intro h
        have impossible := dataSymbol_injective h.2
        contradiction
  | one =>
      rw [findWorkRule_cons_of_not_matches]
      · rw [findWorkRule_cons_of_not_matches]
        · exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
        · intro h
          have impossible := dataSymbol_injective h.2
          contradiction
      · intro h
        have impossible := dataSymbol_injective h.2
        contradiction

theorem find_dataRules_none_of_source_ne (source target state : Nat)
    (symbol : WorkSymbol) (hSource : source ≠ state) :
    findWorkRule (dataRules source target) state symbol = none := by
  change findWorkRule
    (interiorRule source target .blank ::
     interiorRule source target .zero ::
     interiorRule source target .one :: []) state symbol = none
  rw [findWorkRule_cons_of_not_matches]
  · rw [findWorkRule_cons_of_not_matches]
    · rw [findWorkRule_cons_of_not_matches]
      · rfl
      · exact fun h => hSource h.1
    · exact fun h => hSource h.1
  · exact fun h => hSource h.1

theorem findWorkRule_append_none_exact (left right : List WorkRule)
    (state : Nat) (symbol : WorkSymbol)
    (hLeft : findWorkRule left state symbol = none)
    (hRight : findWorkRule right state symbol = none) :
    findWorkRule (left ++ right) state symbol = none :=
  (findWorkRule_append_of_none left right state symbol hLeft).trans hRight

theorem findWorkRule_map_none_of_source_ne {alpha : Type}
    (items : List alpha) (make : alpha → WorkRule)
    (state : Nat) (symbol : WorkSymbol)
    (hSource : ∀ item, (make item).sourceState ≠ state) :
    findWorkRule (items.map make) state symbol = none := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      exact (findWorkRule_cons_of_not_matches _ _ _ _
        (fun h => hSource first h.1)).trans ih

theorem find_continuationRulesFor_none_of_index_ne
    (machine : Machine) (rawRule : Rule) (blockIndex selectedIndex : Nat)
    (phase : Phase) (symbol : WorkSymbol)
    (hIndex : blockIndex ≠ selectedIndex) :
    findWorkRule (continuationRulesFor machine blockIndex rawRule)
      (taggedState selectedIndex phase) symbol = none := by
  have hNe (sourcePhase : Phase) :
      taggedState blockIndex sourcePhase ≠ taggedState selectedIndex phase :=
    taggedState_ne_of_payload_ne hIndex
  rcases rawRule with ⟨source, read, target, write, move⟩
  cases move with
  | stay =>
      change findWorkRule
        [stayOneRule blockIndex
          { sourceState := source, readSymbol := read, targetState := target,
            writeSymbol := write, move := .stay },
         stayTwoRule machine blockIndex
          { sourceState := source, readSymbol := read, targetState := target,
            writeSymbol := write, move := .stay }]
        (taggedState selectedIndex phase) symbol = none
      exact (findWorkRule_cons_of_not_matches _ _ _ _
        (fun h => hNe .stayOne h.1)).trans
        ((findWorkRule_cons_of_not_matches _ _ _ _
          (fun h => hNe .stayTwo h.1)).trans rfl)
  | left =>
      let rule : Rule :=
        { sourceState := source, readSymbol := read, targetState := target,
          writeSymbol := write, move := .left }
      change findWorkRule
        (((dataRules (inspectLeftState blockIndex) (finishLeftState blockIndex) ++
          dataRules (finishLeftState blockIndex) (controlState machine target)) ++
          [leftBoundaryRule blockIndex]) ++
          allWorkSymbols.map (leftExtensionRule machine blockIndex rule))
        (taggedState selectedIndex phase) symbol = none
      have hInspect := find_dataRules_none_of_source_ne
        (inspectLeftState blockIndex) (finishLeftState blockIndex)
        (taggedState selectedIndex phase) symbol (hNe .inspectLeft)
      have hFinish := find_dataRules_none_of_source_ne
        (finishLeftState blockIndex) (controlState machine target)
        (taggedState selectedIndex phase) symbol (hNe .finishLeft)
      have hBoundary : findWorkRule [leftBoundaryRule blockIndex]
          (taggedState selectedIndex phase) symbol = none :=
        (findWorkRule_cons_of_not_matches _ _ _ _
          (fun h => hNe .inspectLeft h.1)).trans rfl
      have hExtension := findWorkRule_map_none_of_source_ne allWorkSymbols
        (leftExtensionRule machine blockIndex rule)
        (taggedState selectedIndex phase) symbol
        (fun _ => hNe .extendLeft)
      exact findWorkRule_append_none_exact _ _ _ _
        (findWorkRule_append_none_exact _ _ _ _
          (findWorkRule_append_none_exact _ _ _ _ hInspect hFinish)
          hBoundary) hExtension
  | right =>
      let rule : Rule :=
        { sourceState := source, readSymbol := read, targetState := target,
          writeSymbol := write, move := .right }
      change findWorkRule
        (((dataRules (inspectRightState blockIndex) (finishRightState blockIndex) ++
          dataRules (finishRightState blockIndex) (controlState machine target)) ++
          [rightBoundaryRule blockIndex]) ++
          allWorkSymbols.map (rightExtensionRule machine blockIndex rule))
        (taggedState selectedIndex phase) symbol = none
      have hInspect := find_dataRules_none_of_source_ne
        (inspectRightState blockIndex) (finishRightState blockIndex)
        (taggedState selectedIndex phase) symbol (hNe .inspectRight)
      have hFinish := find_dataRules_none_of_source_ne
        (finishRightState blockIndex) (controlState machine target)
        (taggedState selectedIndex phase) symbol (hNe .finishRight)
      have hBoundary : findWorkRule [rightBoundaryRule blockIndex]
          (taggedState selectedIndex phase) symbol = none :=
        (findWorkRule_cons_of_not_matches _ _ _ _
          (fun h => hNe .inspectRight h.1)).trans rfl
      have hExtension := findWorkRule_map_none_of_source_ne allWorkSymbols
        (rightExtensionRule machine blockIndex rule)
        (taggedState selectedIndex phase) symbol
        (fun _ => hNe .extendRight)
      exact findWorkRule_append_none_exact _ _ _ _
        (findWorkRule_append_none_exact _ _ _ _
          (findWorkRule_append_none_exact _ _ _ _ hInspect hFinish)
          hBoundary) hExtension

theorem findContinuationRulesFrom_of_findIndexedRawRuleFrom
    {machine : Machine} {rules : List Rule} {state : Nat}
    {rawSymbol : TapeSymbol} {start selectedIndex : Nat} {rawRule : Rule}
    (phase : Phase) (workSymbol : WorkSymbol) (selected : WorkRule)
    (hSelected : findIndexedRawRuleFrom rules state rawSymbol start =
      some (selectedIndex, rawRule))
    (hBlock : findWorkRule (continuationRulesFor machine selectedIndex rawRule)
      (taggedState selectedIndex phase) workSymbol = some selected) :
    findWorkRule (continuationRulesFrom machine rules start)
      (taggedState selectedIndex phase) workSymbol = some selected := by
  induction rules generalizing start with
  | nil => contradiction
  | cons first rest ih =>
      unfold findIndexedRawRuleFrom at hSelected
      split at hSelected
      next =>
        have hPair : (start, first) = (selectedIndex, rawRule) :=
          Option.some.inj hSelected
        have hIndex : start = selectedIndex := congrArg Prod.fst hPair
        have hRule : first = rawRule := congrArg Prod.snd hPair
        cases hIndex
        cases hRule
        unfold continuationRulesFrom
        exact findWorkRule_append_of_some _ _ _ _ _ hBlock
      next =>
        have hGe : start + 1 ≤ selectedIndex :=
          findIndexedRawRuleFrom_index_ge hSelected
        have hLt : start < selectedIndex := Nat.lt_of_succ_le hGe
        have hNe : start ≠ selectedIndex := Nat.ne_of_lt hLt
        unfold continuationRulesFrom
        rw [findWorkRule_append_of_none _ _ _ _
          (find_continuationRulesFor_none_of_index_ne machine first start
            selectedIndex phase workSymbol hNe)]
        exact ih hSelected

theorem findEntryRulesFrom_none_of_nonmain_phase (machine : Machine)
    (rules : List Rule) (start payload : Nat) (phase : Phase)
    (symbol : WorkSymbol) (hPhase : Phase.main ≠ phase) :
    findWorkRule (entryRulesFrom machine rules start)
      (taggedState payload phase) symbol = none := by
  induction rules generalizing start with
  | nil => rfl
  | cons first rest ih =>
      unfold entryRulesFrom
      split
      · exact ih (start + 1)
      · rw [findWorkRule_cons_of_not_matches]
        · exact ih (start + 1)
        · intro hMatch
          exact taggedState_ne_of_phase_ne hPhase hMatch.1

theorem findLiftedContinuation_of_findIndexedRawRule
    {machine : Machine} {state : Nat} {rawSymbol : TapeSymbol}
    {selectedIndex : Nat} {rawRule : Rule}
    (phase : Phase) (workSymbol : WorkSymbol) (selected : WorkRule)
    (hPhase : Phase.main ≠ phase)
    (hSelected : findIndexedRawRule machine.rules state rawSymbol =
      some (selectedIndex, rawRule))
    (hBlock : findWorkRule (continuationRulesFor machine selectedIndex rawRule)
      (taggedState selectedIndex phase) workSymbol = some selected) :
    findWorkRule (liftMachine machine).rules
      (taggedState selectedIndex phase) workSymbol = some selected := by
  unfold liftMachine
  rw [findWorkRule_append_of_none _ _ _ _
    (findEntryRulesFrom_none_of_nonmain_phase machine machine.rules 0
      selectedIndex phase workSymbol hPhase)]
  exact findContinuationRulesFrom_of_findIndexedRawRuleFrom
    phase workSymbol selected hSelected hBlock

theorem find_dataRules_none_of_symbol (source target : Nat)
    (symbol : WorkSymbol)
    (hSymbol : ∀ raw, dataSymbol raw ≠ symbol) :
    findWorkRule (dataRules source target) source symbol = none := by
  change findWorkRule
    (interiorRule source target .blank ::
     interiorRule source target .zero ::
     interiorRule source target .one :: []) source symbol = none
  rw [findWorkRule_cons_of_not_matches]
  · rw [findWorkRule_cons_of_not_matches]
    · rw [findWorkRule_cons_of_not_matches]
      · rfl
      · exact fun h => hSymbol .one h.2
    · exact fun h => hSymbol .zero h.2
  · exact fun h => hSymbol .blank h.2

theorem allWorkSymbols_mem (symbol : WorkSymbol) : symbol ∈ allWorkSymbols := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

theorem find_leftExtension_map_of_mem (symbols : List WorkSymbol)
    (machine : Machine) (index : Nat) (rule : Rule) (symbol : WorkSymbol)
    (hMem : symbol ∈ symbols) :
    findWorkRule (symbols.map (leftExtensionRule machine index rule))
      (extendLeftState index) symbol =
      some (leftExtensionRule machine index rule symbol) := by
  induction symbols with
  | nil => contradiction
  | cons first rest ih =>
      cases hMem with
      | head =>
        exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      | tail =>
          by_cases hFirst : first = symbol
          · cases hFirst
            exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
          · change findWorkRule
              (leftExtensionRule machine index rule first ::
                rest.map (leftExtensionRule machine index rule))
              (extendLeftState index) symbol = _
            rw [findWorkRule_cons_of_not_matches]
            · apply ih
              assumption
            · exact fun h => hFirst h.2

theorem find_rightExtension_map_of_mem (symbols : List WorkSymbol)
    (machine : Machine) (index : Nat) (rule : Rule) (symbol : WorkSymbol)
    (hMem : symbol ∈ symbols) :
    findWorkRule (symbols.map (rightExtensionRule machine index rule))
      (extendRightState index) symbol =
      some (rightExtensionRule machine index rule symbol) := by
  induction symbols with
  | nil => contradiction
  | cons first rest ih =>
      cases hMem with
      | head =>
        exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      | tail =>
          by_cases hFirst : first = symbol
          · cases hFirst
            exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
          · change findWorkRule
              (rightExtensionRule machine index rule first ::
                rest.map (rightExtensionRule machine index rule))
              (extendRightState index) symbol = _
            rw [findWorkRule_cons_of_not_matches]
            · apply ih
              assumption
            · exact fun h => hFirst h.2

theorem find_continuation_stayOne (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .stay) :
    findWorkRule (continuationRulesFor machine index rule)
      (stayOneState index) (dataSymbol rule.writeSymbol) =
      some (stayOneRule index rule) := by
  unfold continuationRulesFor
  rw [hMove]
  exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩

theorem find_continuation_stayTwo (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .stay) :
    findWorkRule (continuationRulesFor machine index rule)
      (stayTwoState index) (dataSymbol rule.writeSymbol) =
      some (stayTwoRule machine index rule) := by
  unfold continuationRulesFor
  rw [hMove]
  rw [findWorkRule_cons_of_not_matches]
  · exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
  · intro h
    exact taggedState_ne_of_phase_ne
      (leftPhase := .stayOne) (rightPhase := .stayTwo)
      (by intro impossible; contradiction) h.1

theorem find_continuation_left_inspect (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .left) (symbol : TapeSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (inspectLeftState index) (dataSymbol symbol) =
      some (interiorRule (inspectLeftState index) (finishLeftState index) symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState)) ++
      [leftBoundaryRule index]) ++
      allWorkSymbols.map (leftExtensionRule machine index rule))
    (inspectLeftState index) (dataSymbol symbol) = _
  have hInspect := find_dataRules
    (inspectLeftState index) (finishLeftState index) symbol
  have hFinish := findWorkRule_append_of_some
    (dataRules (inspectLeftState index) (finishLeftState index))
    (dataRules (finishLeftState index) (controlState machine rule.targetState))
    (inspectLeftState index) (dataSymbol symbol) _ hInspect
  have hBoundary := findWorkRule_append_of_some
    (dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState))
    [leftBoundaryRule index] (inspectLeftState index) (dataSymbol symbol) _ hFinish
  exact findWorkRule_append_of_some _
    (allWorkSymbols.map (leftExtensionRule machine index rule))
    (inspectLeftState index) (dataSymbol symbol) _ hBoundary

theorem find_continuation_left_finish (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .left) (symbol : TapeSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (finishLeftState index) (dataSymbol symbol) =
      some (interiorRule (finishLeftState index)
        (controlState machine rule.targetState) symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState)) ++
      [leftBoundaryRule index]) ++
      allWorkSymbols.map (leftExtensionRule machine index rule))
    (finishLeftState index) (dataSymbol symbol) = _
  have hNone := find_dataRules_none_of_source_ne
    (inspectLeftState index) (finishLeftState index) (finishLeftState index)
    (dataSymbol symbol)
    (taggedState_ne_of_phase_ne
      (leftPhase := .inspectLeft) (rightPhase := .finishLeft)
      (by intro impossible; contradiction))
  have hSelected := find_dataRules (finishLeftState index)
    (controlState machine rule.targetState) symbol
  have hFinish := (findWorkRule_append_of_none _ _ _ _ hNone).trans hSelected
  have hBoundary := findWorkRule_append_of_some
    (dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState))
    [leftBoundaryRule index] (finishLeftState index) (dataSymbol symbol) _ hFinish
  exact findWorkRule_append_of_some _
    (allWorkSymbols.map (leftExtensionRule machine index rule))
    (finishLeftState index) (dataSymbol symbol) _ hBoundary

theorem find_continuation_left_boundary (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .left) :
    findWorkRule (continuationRulesFor machine index rule)
      (inspectLeftState index) leftMarker = some (leftBoundaryRule index) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState)) ++
      [leftBoundaryRule index]) ++
      allWorkSymbols.map (leftExtensionRule machine index rule))
    (inspectLeftState index) leftMarker = _
  have hInspectNone := find_dataRules_none_of_symbol
    (inspectLeftState index) (finishLeftState index) leftMarker
    dataSymbol_ne_leftMarker
  have hFinishNone := find_dataRules_none_of_source_ne
    (finishLeftState index) (controlState machine rule.targetState)
    (inspectLeftState index) leftMarker
    (taggedState_ne_of_phase_ne
      (leftPhase := .finishLeft) (rightPhase := .inspectLeft)
      (by intro impossible; contradiction))
  have hPrefix := findWorkRule_append_none_exact _ _ _ _
    hInspectNone hFinishNone
  have hSelected : findWorkRule [leftBoundaryRule index]
      (inspectLeftState index) leftMarker = some (leftBoundaryRule index) :=
    findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
  have hBoundary := (findWorkRule_append_of_none _ _ _ _ hPrefix).trans hSelected
  exact findWorkRule_append_of_some _ _ _ _ _ hBoundary

theorem find_continuation_left_extension (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .left) (symbol : WorkSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (extendLeftState index) symbol =
      some (leftExtensionRule machine index rule symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectLeftState index) (finishLeftState index) ++
      dataRules (finishLeftState index) (controlState machine rule.targetState)) ++
      [leftBoundaryRule index]) ++
      allWorkSymbols.map (leftExtensionRule machine index rule))
    (extendLeftState index) symbol = _
  have hInspectNone := find_dataRules_none_of_source_ne
    (inspectLeftState index) (finishLeftState index) (extendLeftState index)
    symbol (taggedState_ne_of_phase_ne
      (leftPhase := .inspectLeft) (rightPhase := .extendLeft)
      (by intro impossible; contradiction))
  have hFinishNone := find_dataRules_none_of_source_ne
    (finishLeftState index) (controlState machine rule.targetState)
    (extendLeftState index) symbol (taggedState_ne_of_phase_ne
      (leftPhase := .finishLeft) (rightPhase := .extendLeft)
      (by intro impossible; contradiction))
  have hPrefix := findWorkRule_append_none_exact _ _ _ _
    hInspectNone hFinishNone
  have hBoundary : findWorkRule [leftBoundaryRule index]
      (extendLeftState index) symbol = none :=
    (findWorkRule_cons_of_not_matches _ _ _ _ (by
      intro h
      exact taggedState_ne_of_phase_ne
        (leftPhase := .inspectLeft) (rightPhase := .extendLeft)
        (by intro impossible; contradiction) h.1)).trans rfl
  have hBeforeExtension := findWorkRule_append_none_exact _ _ _ _
    hPrefix hBoundary
  have hSelected := find_leftExtension_map_of_mem allWorkSymbols
    machine index rule symbol
    (allWorkSymbols_mem symbol)
  exact (findWorkRule_append_of_none _ _ _ _ hBeforeExtension).trans hSelected

theorem find_continuation_right_inspect (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .right) (symbol : TapeSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (inspectRightState index) (dataSymbol symbol) =
      some (interiorRule (inspectRightState index) (finishRightState index) symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState)) ++
      [rightBoundaryRule index]) ++
      allWorkSymbols.map (rightExtensionRule machine index rule))
    (inspectRightState index) (dataSymbol symbol) = _
  have hInspect := find_dataRules
    (inspectRightState index) (finishRightState index) symbol
  have hFinish := findWorkRule_append_of_some
    (dataRules (inspectRightState index) (finishRightState index))
    (dataRules (finishRightState index) (controlState machine rule.targetState))
    (inspectRightState index) (dataSymbol symbol) _ hInspect
  have hBoundary := findWorkRule_append_of_some
    (dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState))
    [rightBoundaryRule index] (inspectRightState index) (dataSymbol symbol) _ hFinish
  exact findWorkRule_append_of_some _
    (allWorkSymbols.map (rightExtensionRule machine index rule))
    (inspectRightState index) (dataSymbol symbol) _ hBoundary

theorem find_continuation_right_finish (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .right) (symbol : TapeSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (finishRightState index) (dataSymbol symbol) =
      some (interiorRule (finishRightState index)
        (controlState machine rule.targetState) symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState)) ++
      [rightBoundaryRule index]) ++
      allWorkSymbols.map (rightExtensionRule machine index rule))
    (finishRightState index) (dataSymbol symbol) = _
  have hNone := find_dataRules_none_of_source_ne
    (inspectRightState index) (finishRightState index) (finishRightState index)
    (dataSymbol symbol)
    (taggedState_ne_of_phase_ne
      (leftPhase := .inspectRight) (rightPhase := .finishRight)
      (by intro impossible; contradiction))
  have hSelected := find_dataRules (finishRightState index)
    (controlState machine rule.targetState) symbol
  have hFinish := (findWorkRule_append_of_none _ _ _ _ hNone).trans hSelected
  have hBoundary := findWorkRule_append_of_some
    (dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState))
    [rightBoundaryRule index] (finishRightState index) (dataSymbol symbol) _ hFinish
  exact findWorkRule_append_of_some _
    (allWorkSymbols.map (rightExtensionRule machine index rule))
    (finishRightState index) (dataSymbol symbol) _ hBoundary

theorem find_continuation_right_boundary (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .right) :
    findWorkRule (continuationRulesFor machine index rule)
      (inspectRightState index) rightMarker = some (rightBoundaryRule index) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState)) ++
      [rightBoundaryRule index]) ++
      allWorkSymbols.map (rightExtensionRule machine index rule))
    (inspectRightState index) rightMarker = _
  have hInspectNone := find_dataRules_none_of_symbol
    (inspectRightState index) (finishRightState index) rightMarker
    dataSymbol_ne_rightMarker
  have hFinishNone := find_dataRules_none_of_source_ne
    (finishRightState index) (controlState machine rule.targetState)
    (inspectRightState index) rightMarker
    (taggedState_ne_of_phase_ne
      (leftPhase := .finishRight) (rightPhase := .inspectRight)
      (by intro impossible; contradiction))
  have hPrefix := findWorkRule_append_none_exact _ _ _ _
    hInspectNone hFinishNone
  have hSelected : findWorkRule [rightBoundaryRule index]
      (inspectRightState index) rightMarker = some (rightBoundaryRule index) :=
    findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
  have hBoundary := (findWorkRule_append_of_none _ _ _ _ hPrefix).trans hSelected
  exact findWorkRule_append_of_some _ _ _ _ _ hBoundary

theorem find_continuation_right_extension (machine : Machine) (index : Nat)
    (rule : Rule) (hMove : rule.move = .right) (symbol : WorkSymbol) :
    findWorkRule (continuationRulesFor machine index rule)
      (extendRightState index) symbol =
      some (rightExtensionRule machine index rule symbol) := by
  unfold continuationRulesFor
  rw [hMove]
  change findWorkRule
    (((dataRules (inspectRightState index) (finishRightState index) ++
      dataRules (finishRightState index) (controlState machine rule.targetState)) ++
      [rightBoundaryRule index]) ++
      allWorkSymbols.map (rightExtensionRule machine index rule))
    (extendRightState index) symbol = _
  have hInspectNone := find_dataRules_none_of_source_ne
    (inspectRightState index) (finishRightState index) (extendRightState index)
    symbol (taggedState_ne_of_phase_ne
      (leftPhase := .inspectRight) (rightPhase := .extendRight)
      (by intro impossible; contradiction))
  have hFinishNone := find_dataRules_none_of_source_ne
    (finishRightState index) (controlState machine rule.targetState)
    (extendRightState index) symbol (taggedState_ne_of_phase_ne
      (leftPhase := .finishRight) (rightPhase := .extendRight)
      (by intro impossible; contradiction))
  have hPrefix := findWorkRule_append_none_exact _ _ _ _
    hInspectNone hFinishNone
  have hBoundary : findWorkRule [rightBoundaryRule index]
      (extendRightState index) symbol = none :=
    (findWorkRule_cons_of_not_matches _ _ _ _ (by
      intro h
      exact taggedState_ne_of_phase_ne
        (leftPhase := .inspectRight) (rightPhase := .extendRight)
        (by intro impossible; contradiction) h.1)).trans rfl
  have hBeforeExtension := findWorkRule_append_none_exact _ _ _ _
    hPrefix hBoundary
  have hSelected := find_rightExtension_map_of_mem allWorkSymbols
    machine index rule symbol
    (allWorkSymbols_mem symbol)
  exact (findWorkRule_append_of_none _ _ _ _ hBeforeExtension).trans hSelected

theorem find_liftMachine_entry {machine : Machine} {state : Nat}
    {symbol : TapeSymbol} {index : Nat} {rule : Rule}
    (hState : state ≠ machine.acceptState ∧ state ≠ machine.rejectState)
    (hSelected : findIndexedRawRule machine.rules state symbol =
      some (index, rule)) :
    findWorkRule (liftMachine machine).rules
      (mainState state) (dataSymbol symbol) = some (entryRule index rule) := by
  unfold liftMachine
  apply findWorkRule_append_of_some
  exact findEntryRulesFrom_of_findIndexedRawRuleFrom hState hSelected

theorem workRunExact_three_of_steps (machine : WorkMachine)
    (c0 c1 c2 c3 : WorkConfiguration)
    (h0 : workStep? machine c0 = some c1)
    (h1 : workStep? machine c1 = some c2)
    (h2 : workStep? machine c2 = some c3) :
    workRunExact? machine 3 c0 = some c3 := by
  change
    (match workStep? machine c0 with
     | none => none
     | some next =>
       match workStep? machine next with
       | none => none
       | some next =>
         match workStep? machine next with
         | none => none
         | some next => some next) = some c3
  rw [h0]
  change
    (match workStep? machine c1 with
     | none => none
     | some next =>
       match workStep? machine next with
       | none => none
       | some next => some next) = some c3
  rw [h1]
  change
    (match workStep? machine c2 with
     | none => none
     | some next => some next) = some c3
  rw [h2]

theorem workRunExact_three_of_selected (machine : Machine)
    (config : Configuration) (workTape : WorkTape)
    (index : Nat) (rule : Rule)
    (hHalted : machine.isHalted config = false)
    (hSelected : findIndexedRawRule machine.rules config.state
      config.tape.head = some (index, rule))
    (hRepresents : Represents config.tape workTape) :
    ∃ final,
      workRunExact? (liftMachine machine) 3
        (liftConfiguration machine config workTape) = some final ∧
      RepresentsConfiguration machine (applyRule rule config) final := by
  have hState := machine_not_halted_parts hHalted
  have hControl := controlState_of_nonterminal machine config.state
    hState.1 hState.2
  rcases hRepresents with ⟨outsideLeft, outsideRight, hWork⟩
  subst workTape
  let c0 := liftConfiguration machine config
    (frameWithGarbage config.tape outsideLeft outsideRight)
  let r0 := entryRule index rule
  let c1 := applyWorkRule r0 c0
  have hFind0 : findWorkRule (liftMachine machine).rules
      c0.state c0.tape.head = some r0 := by
    dsimp [c0, r0, liftConfiguration, frameWithGarbage]
    rw [hControl]
    exact find_liftMachine_entry hState hSelected
  have hHalt0 : (liftMachine machine).isHalted c0 = false := by
    dsimp [c0, liftConfiguration]
    rw [hControl]
    exact liftMachine_main_not_halted machine config.state
      (frameWithGarbage config.tape outsideLeft outsideRight)
  have hStep0 : workStep? (liftMachine machine) c0 = some c1 :=
    workStep?_eq_apply_of_find _ _ _ hHalt0 hFind0
  have hFrame : Represents config.tape
      (frameWithGarbage config.tape outsideLeft outsideRight) :=
    frameWithGarbage_represents _ _ _
  cases hMove : rule.move with
  | stay =>
      let r1 := stayOneRule index rule
      let c2 := applyWorkRule r1 c1
      have hBlock1 := find_continuation_stayOne machine index rule hMove
      have hFind1 : findWorkRule (liftMachine machine).rules
          c1.state c1.tape.head = some r1 := by
        have hGlobal := findLiftedContinuation_of_findIndexedRawRule
          .stayOne (dataSymbol rule.writeSymbol) r1
          (by intro impossible; contradiction) hSelected
          (by exact hBlock1)
        dsimp [c1, c0, r0, r1, entryRule, liftConfiguration,
          applyWorkRule, WorkTape.write, WorkTape.move, frameWithGarbage]
        rw [hMove]
        exact hGlobal
      have hHalt1 : (liftMachine machine).isHalted c1 = false := by
        dsimp [c1, r0, entryRule, applyWorkRule]
        rw [hMove]
        exact liftMachine_stage_not_halted machine index .stayOne _
          (by intro impossible; contradiction)
          (by intro impossible; contradiction)
      have hStep1 : workStep? (liftMachine machine) c1 = some c2 :=
        workStep?_eq_apply_of_find _ _ _ hHalt1 hFind1
      let r2 := stayTwoRule machine index rule
      let c3 := applyWorkRule r2 c2
      have hBlock2 := find_continuation_stayTwo machine index rule hMove
      have hFind2 : findWorkRule (liftMachine machine).rules
          c2.state c2.tape.head = some r2 := by
        have hGlobal := findLiftedContinuation_of_findIndexedRawRule
          .stayTwo (dataSymbol rule.writeSymbol) r2
          (by intro impossible; contradiction) hSelected
          (by exact hBlock2)
        dsimp [c2, c1, c0, r1, r0, r2, stayOneRule, interiorRule,
          entryRule, liftConfiguration, applyWorkRule,
          WorkTape.write, WorkTape.move, frameWithGarbage]
        exact hGlobal
      have hHalt2 : (liftMachine machine).isHalted c2 = false := by
        change (liftMachine machine).isHalted
          { state := taggedState index .stayTwo, tape := c2.tape } = false
        exact liftMachine_stage_not_halted machine index .stayTwo c2.tape
          (by intro impossible; contradiction)
          (by intro impossible; contradiction)
      have hStep2 : workStep? (liftMachine machine) c2 = some c3 :=
        workStep?_eq_apply_of_find _ _ _ hHalt2 hFind2
      refine ⟨c3, workRunExact_three_of_steps _ c0 c1 c2 c3
        hStep0 hStep1 hStep2, ?_⟩
      constructor
      · rfl
      · have hWritten := represents_write hFrame rule.writeSymbol
        dsimp [applyRule, Tape.move, c3, c2, c1, c0, r2, r1, r0,
          stayTwoRule, stayOneRule, interiorRule, entryRule,
          liftConfiguration, applyWorkRule, WorkTape.write, WorkTape.move,
          frameWithGarbage]
        rw [hMove]
        exact hWritten
  | left =>
      cases hLeft : config.tape.left with
      | nil =>
          let r1 := leftBoundaryRule index
          let c2 := applyWorkRule r1 c1
          have hBlock1 := find_continuation_left_boundary machine index rule hMove
          have hFind1 : findWorkRule (liftMachine machine).rules
              c1.state c1.tape.head = some r1 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .inspectLeft leftMarker r1
              (by intro impossible; contradiction) hSelected
              (by exact hBlock1)
            dsimp [c1, c0, r0, r1, entryRule, liftConfiguration,
              applyWorkRule, WorkTape.write, WorkTape.move, WorkTape.moveLeft,
              frameWithGarbage]
            rw [hMove, hLeft]
            exact hGlobal
          have hHalt1 : (liftMachine machine).isHalted c1 = false := by
            dsimp [c1, r0, entryRule, applyWorkRule]
            rw [hMove]
            exact liftMachine_stage_not_halted machine index .inspectLeft _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep1 : workStep? (liftMachine machine) c1 = some c2 :=
            workStep?_eq_apply_of_find _ _ _ hHalt1 hFind1
          let r2 := leftExtensionRule machine index rule c2.tape.head
          let c3 := applyWorkRule r2 c2
          have hBlock2 := find_continuation_left_extension machine index rule
            hMove c2.tape.head
          have hFind2 : findWorkRule (liftMachine machine).rules
              c2.state c2.tape.head = some r2 := by
            exact findLiftedContinuation_of_findIndexedRawRule
              .extendLeft c2.tape.head r2
              (by intro impossible; contradiction) hSelected
              (by exact hBlock2)
          have hHalt2 : (liftMachine machine).isHalted c2 = false := by
            dsimp [c2, r1, leftBoundaryRule, applyWorkRule]
            exact liftMachine_stage_not_halted machine index .extendLeft _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep2 : workStep? (liftMachine machine) c2 = some c3 :=
            workStep?_eq_apply_of_find _ _ _ hHalt2 hFind2
          refine ⟨c3, workRunExact_three_of_steps _ c0 c1 c2 c3
            hStep0 hStep1 hStep2, ?_⟩
          constructor
          · rfl
          · have hExpanded := represents_expandLeft_of_nil
              (represents_write hFrame rule.writeSymbol) hLeft
            have hRawTape : (applyRule rule config).tape =
                (config.tape.write rule.writeSymbol).moveLeft := by
              unfold applyRule
              rw [hMove]
              rfl
            have hWorkTape : c3.tape = expandLeftBoundary
                ((frameWithGarbage config.tape outsideLeft outsideRight).write
                  (dataSymbol rule.writeSymbol)) := by
              dsimp [c3, c2, c1, c0, r2, r1, r0,
                leftExtensionRule, leftBoundaryRule, entryRule,
                liftConfiguration, applyWorkRule, WorkTape.write,
                WorkTape.move, expandLeftBoundary]
              rw [hMove]
            rw [hRawTape, hWorkTape]
            exact hExpanded
      | cons leftHead leftTail =>
          let r1 := interiorRule (inspectLeftState index)
            (finishLeftState index) leftHead
          let c2 := applyWorkRule r1 c1
          have hBlock1 := find_continuation_left_inspect machine index rule
            hMove leftHead
          have hFind1 : findWorkRule (liftMachine machine).rules
              c1.state c1.tape.head = some r1 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .inspectLeft (dataSymbol leftHead) r1
              (by intro impossible; contradiction) hSelected
              (by exact hBlock1)
            dsimp [c1, c0, r0, r1, entryRule, liftConfiguration,
              applyWorkRule, WorkTape.write, WorkTape.move,
              WorkTape.moveLeft, frameWithGarbage]
            rw [hMove, hLeft]
            exact hGlobal
          have hHalt1 : (liftMachine machine).isHalted c1 = false := by
            dsimp [c1, r0, entryRule, applyWorkRule]
            rw [hMove]
            exact liftMachine_stage_not_halted machine index .inspectLeft _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep1 : workStep? (liftMachine machine) c1 = some c2 :=
            workStep?_eq_apply_of_find _ _ _ hHalt1 hFind1
          let r2 := interiorRule (finishLeftState index)
            (controlState machine rule.targetState) leftHead
          let c3 := applyWorkRule r2 c2
          have hBlock2 := find_continuation_left_finish machine index rule
            hMove leftHead
          have hFind2 : findWorkRule (liftMachine machine).rules
              c2.state c2.tape.head = some r2 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .finishLeft (dataSymbol leftHead) r2
              (by intro impossible; contradiction) hSelected
              (by exact hBlock2)
            dsimp [c2, c1, c0, r1, r0, r2, interiorRule, entryRule,
              liftConfiguration, applyWorkRule, WorkTape.write,
              WorkTape.move, WorkTape.moveLeft, frameWithGarbage]
            exact hGlobal
          have hHalt2 : (liftMachine machine).isHalted c2 = false := by
            dsimp [c2, r1, interiorRule, applyWorkRule]
            exact liftMachine_stage_not_halted machine index .finishLeft _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep2 : workStep? (liftMachine machine) c2 = some c3 :=
            workStep?_eq_apply_of_find _ _ _ hHalt2 hFind2
          refine ⟨c3, workRunExact_three_of_steps _ c0 c1 c2 c3
            hStep0 hStep1 hStep2, ?_⟩
          constructor
          · rfl
          · have hMoved := represents_moveLeft_of_cons
              (represents_write hFrame rule.writeSymbol) hLeft
            have hRawTape : (applyRule rule config).tape =
                (config.tape.write rule.writeSymbol).moveLeft := by
              unfold applyRule
              rw [hMove]
              rfl
            have hWorkTape : c3.tape =
                ((frameWithGarbage config.tape outsideLeft outsideRight).write
                  (dataSymbol rule.writeSymbol)).moveLeft := by
              dsimp [c3, c2, c1, c0, r2, r1, r0, interiorRule,
                entryRule, liftConfiguration, applyWorkRule, WorkTape.write,
                WorkTape.move]
              rw [hMove]
              unfold frameWithGarbage
              rw [hLeft]
              rfl
            rw [hRawTape, hWorkTape]
            exact hMoved
  | right =>
      cases hRight : config.tape.right with
      | nil =>
          let r1 := rightBoundaryRule index
          let c2 := applyWorkRule r1 c1
          have hBlock1 := find_continuation_right_boundary machine index rule hMove
          have hFind1 : findWorkRule (liftMachine machine).rules
              c1.state c1.tape.head = some r1 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .inspectRight rightMarker r1
              (by intro impossible; contradiction) hSelected
              (by exact hBlock1)
            dsimp [c1, c0, r0, r1, entryRule, liftConfiguration,
              applyWorkRule, WorkTape.write, WorkTape.move,
              WorkTape.moveRight, frameWithGarbage]
            rw [hMove, hRight]
            exact hGlobal
          have hHalt1 : (liftMachine machine).isHalted c1 = false := by
            dsimp [c1, r0, entryRule, applyWorkRule]
            rw [hMove]
            exact liftMachine_stage_not_halted machine index .inspectRight _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep1 : workStep? (liftMachine machine) c1 = some c2 :=
            workStep?_eq_apply_of_find _ _ _ hHalt1 hFind1
          let r2 := rightExtensionRule machine index rule c2.tape.head
          let c3 := applyWorkRule r2 c2
          have hBlock2 := find_continuation_right_extension machine index rule
            hMove c2.tape.head
          have hFind2 : findWorkRule (liftMachine machine).rules
              c2.state c2.tape.head = some r2 := by
            exact findLiftedContinuation_of_findIndexedRawRule
              .extendRight c2.tape.head r2
              (by intro impossible; contradiction) hSelected
              (by exact hBlock2)
          have hHalt2 : (liftMachine machine).isHalted c2 = false := by
            dsimp [c2, r1, rightBoundaryRule, applyWorkRule]
            exact liftMachine_stage_not_halted machine index .extendRight _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep2 : workStep? (liftMachine machine) c2 = some c3 :=
            workStep?_eq_apply_of_find _ _ _ hHalt2 hFind2
          refine ⟨c3, workRunExact_three_of_steps _ c0 c1 c2 c3
            hStep0 hStep1 hStep2, ?_⟩
          constructor
          · rfl
          · have hExpanded := represents_expandRight_of_nil
              (represents_write hFrame rule.writeSymbol) hRight
            have hRawTape : (applyRule rule config).tape =
                (config.tape.write rule.writeSymbol).moveRight := by
              unfold applyRule
              rw [hMove]
              rfl
            have hWorkTape : c3.tape = expandRightBoundary
                ((frameWithGarbage config.tape outsideLeft outsideRight).write
                  (dataSymbol rule.writeSymbol)) := by
              dsimp [c3, c2, c1, c0, r2, r1, r0,
                rightExtensionRule, rightBoundaryRule, entryRule,
                liftConfiguration, applyWorkRule, WorkTape.write,
                WorkTape.move, expandRightBoundary]
              rw [hMove]
            rw [hRawTape, hWorkTape]
            exact hExpanded
      | cons rightHead rightTail =>
          let r1 := interiorRule (inspectRightState index)
            (finishRightState index) rightHead
          let c2 := applyWorkRule r1 c1
          have hBlock1 := find_continuation_right_inspect machine index rule
            hMove rightHead
          have hFind1 : findWorkRule (liftMachine machine).rules
              c1.state c1.tape.head = some r1 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .inspectRight (dataSymbol rightHead) r1
              (by intro impossible; contradiction) hSelected
              (by exact hBlock1)
            dsimp [c1, c0, r0, r1, entryRule, liftConfiguration,
              applyWorkRule, WorkTape.write, WorkTape.move,
              WorkTape.moveRight, frameWithGarbage]
            rw [hMove, hRight]
            exact hGlobal
          have hHalt1 : (liftMachine machine).isHalted c1 = false := by
            dsimp [c1, r0, entryRule, applyWorkRule]
            rw [hMove]
            exact liftMachine_stage_not_halted machine index .inspectRight _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep1 : workStep? (liftMachine machine) c1 = some c2 :=
            workStep?_eq_apply_of_find _ _ _ hHalt1 hFind1
          let r2 := interiorRule (finishRightState index)
            (controlState machine rule.targetState) rightHead
          let c3 := applyWorkRule r2 c2
          have hBlock2 := find_continuation_right_finish machine index rule
            hMove rightHead
          have hFind2 : findWorkRule (liftMachine machine).rules
              c2.state c2.tape.head = some r2 := by
            have hGlobal := findLiftedContinuation_of_findIndexedRawRule
              .finishRight (dataSymbol rightHead) r2
              (by intro impossible; contradiction) hSelected
              (by exact hBlock2)
            dsimp [c2, c1, c0, r1, r0, r2, interiorRule, entryRule,
              liftConfiguration, applyWorkRule, WorkTape.write,
              WorkTape.move, WorkTape.moveRight, frameWithGarbage]
            exact hGlobal
          have hHalt2 : (liftMachine machine).isHalted c2 = false := by
            dsimp [c2, r1, interiorRule, applyWorkRule]
            exact liftMachine_stage_not_halted machine index .finishRight _
              (by intro impossible; contradiction)
              (by intro impossible; contradiction)
          have hStep2 : workStep? (liftMachine machine) c2 = some c3 :=
            workStep?_eq_apply_of_find _ _ _ hHalt2 hFind2
          refine ⟨c3, workRunExact_three_of_steps _ c0 c1 c2 c3
            hStep0 hStep1 hStep2, ?_⟩
          constructor
          · rfl
          · have hMoved := represents_moveRight_of_cons
              (represents_write hFrame rule.writeSymbol) hRight
            have hRawTape : (applyRule rule config).tape =
                (config.tape.write rule.writeSymbol).moveRight := by
              unfold applyRule
              rw [hMove]
              rfl
            have hWorkTape : c3.tape =
                ((frameWithGarbage config.tape outsideLeft outsideRight).write
                  (dataSymbol rule.writeSymbol)).moveRight := by
              dsimp [c3, c2, c1, c0, r2, r1, r0, interiorRule,
                entryRule, liftConfiguration, applyWorkRule, WorkTape.write,
                WorkTape.move]
              rw [hMove]
              unfold frameWithGarbage
              rw [hRight]
              rfl
            rw [hRawTape, hWorkTape]
            exact hMoved

/-- A successful raw step exposes the selected first matching rule. -/
theorem step?_some_exists (machine : Machine) (config next : Configuration)
    (hStep : step? machine config = some next) :
    ∃ rule, machine.isHalted config = false ∧
      findRule machine.rules config.state config.tape.head = some rule ∧
      next = applyRule rule config := by
  cases hHalted : machine.isHalted config with
  | true =>
      unfold step? at hStep
      rw [hHalted] at hStep
      contradiction
  | false =>
      cases hFind : findRule machine.rules config.state config.tape.head with
      | none =>
          unfold step? at hStep
          rw [hHalted, hFind] at hStep
          contradiction
      | some rule =>
          refine ⟨rule, rfl, rfl, ?_⟩
          have hApply := step?_eq_apply_of_find machine config rule hHalted hFind
          exact (Option.some.inj (hApply.symm.trans hStep)).symm

/-- Every successful raw transition is simulated by exactly three work steps
from any representing boundary frame. -/
theorem workRunExact_three_of_step (machine : Machine)
    (config next : Configuration) (workTape : WorkTape)
    (hStep : step? machine config = some next)
    (hRepresents : Represents config.tape workTape) :
    ∃ final,
      workRunExact? (liftMachine machine) 3
        (liftConfiguration machine config workTape) = some final ∧
      RepresentsConfiguration machine next final := by
  rcases step?_some_exists machine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  rcases findIndexedRawRule_of_findRule_some hFind with ⟨index, hIndexed⟩
  rcases workRunExact_three_of_selected machine config workTape index rule
    hHalted hIndexed hRepresents with ⟨final, hRun, hRep⟩
  subst next
  exact ⟨final, hRun, hRep⟩

/-- The existing literal work-to-raw compiler reaches the encoded endpoint
with a concrete raw fuel budget of eighteen. -/
theorem run_compileWorkMachine_eighteen_of_step (machine : Machine)
    (config next : Configuration) (workTape : WorkTape)
    (hStep : step? machine config = some next)
    (hRepresents : Represents config.tape workTape) :
    ∃ final,
      run (compileWorkMachine (liftMachine machine)) 18
          (encodeWorkConfiguration
            (liftConfiguration machine config workTape)) =
        encodeWorkConfiguration final ∧
      RepresentsConfiguration machine next final := by
  rcases workRunExact_three_of_step machine config next workTape
    hStep hRepresents with ⟨final, hRun, hRep⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (liftMachine machine) 3
    (liftConfiguration machine config workTape) final hRun
  change run (compileWorkMachine (liftMachine machine)) 18
      (encodeWorkConfiguration
        (liftConfiguration machine config workTape)) =
      encodeWorkConfiguration final at hCompiled
  exact ⟨final, hCompiled, hRep⟩

/-! ### Exact finite-run lifting

The following layer iterates the local theorem above over an arbitrary finite
chain of successful raw transitions.  Its cost parameter is the number of
source transitions in that supplied chain, not the source input length.  It
does not cover a `run` that stops early, create an initial frame, decode or
hand off output, or establish an end-to-end polynomial-time refinement.
-/

/-- Execute exactly `steps` raw transitions, failing when execution stops
early.  This is the raw-machine analogue of `workRunExact?`. -/
def rawRunExact? (machine : Machine) :
    Nat → Configuration → Option Configuration
  | 0, config => some config
  | steps + 1, config =>
      match step? machine config with
      | none => none
      | some next => rawRunExact? machine steps next

theorem rawRunExact?_one_of_step (machine : Machine)
    (config next : Configuration)
    (hStep : step? machine config = some next) :
    rawRunExact? machine 1 config = some next := by
  change
    (match step? machine config with
     | none => none
     | some result => some result) = some next
  rw [hStep]

/-- Exact raw executions compose without adding any stuttering transitions. -/
theorem rawRunExact?_compose (machine : Machine)
    (first second : Nat) (start middle final : Configuration)
    (hFirst : rawRunExact? machine first start = some middle)
    (hSecond : rawRunExact? machine second middle = some final) :
    rawRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, hStart]
      exact hSecond
  | succ first ih =>
      cases hStep : step? machine start with
      | none =>
          change
            (match step? machine start with
             | none => none
             | some next => rawRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : rawRunExact? machine first next = some middle := by
            change
              (match step? machine start with
               | none => none
               | some next => rawRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match step? machine start with
             | none => none
             | some next =>
                 rawRunExact? machine (first + second) next) = some final
          rw [hStep]
          exact ih next hTail

/-- An exact raw execution agrees with the ordinary at-most interpreter at
the same transition budget. -/
theorem run_eq_of_rawRunExact (machine : Machine) (steps : Nat)
    (start final : Configuration)
    (hExact : rawRunExact? machine steps start = some final) :
    run machine steps start = final := by
  induction steps generalizing start with
  | zero =>
      change some start = some final at hExact
      exact Option.some.inj hExact
  | succ steps ih =>
      cases hStep : step? machine start with
      | none =>
          change
            (match step? machine start with
             | none => none
             | some next => rawRunExact? machine steps next) =
              some final at hExact
          rw [hStep] at hExact
          contradiction
      | some next =>
          have hTail : rawRunExact? machine steps next = some final := by
            change
              (match step? machine start with
               | none => none
               | some next => rawRunExact? machine steps next) =
                some final at hExact
            rw [hStep] at hExact
            exact hExact
          change
            (match step? machine start with
             | none => start
             | some next => run machine steps next) = final
          rw [hStep]
          exact ih next hTail

/-- Exact work executions compose without adding any stuttering transitions. -/
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
             | some next =>
                 workRunExact? machine (first + second) next) = some final
          rw [hStep]
          exact ih next hTail

/-- Every exact `steps`-transition raw execution is simulated from any
representing boundary frame in exactly `3 * steps` work transitions. -/
theorem workRunExact_three_mul_of_rawRunExact (machine : Machine)
    (steps : Nat) (config final : Configuration) (workTape : WorkTape)
    (hRaw : rawRunExact? machine steps config = some final)
    (hRepresents : Represents config.tape workTape) :
    ∃ workFinal,
      workRunExact? (liftMachine machine) (3 * steps)
          (liftConfiguration machine config workTape) = some workFinal ∧
      RepresentsConfiguration machine final workFinal := by
  induction steps generalizing config workTape with
  | zero =>
      change some config = some final at hRaw
      have hFinal : config = final := Option.some.inj hRaw
      subst final
      refine ⟨liftConfiguration machine config workTape, rfl, ?_⟩
      exact ⟨rfl, hRepresents⟩
  | succ steps ih =>
      cases hStep : step? machine config with
      | none =>
          change
            (match step? machine config with
             | none => none
             | some next => rawRunExact? machine steps next) =
              some final at hRaw
          rw [hStep] at hRaw
          contradiction
      | some next =>
          have hTail : rawRunExact? machine steps next = some final := by
            change
              (match step? machine config with
               | none => none
               | some next => rawRunExact? machine steps next) =
                some final at hRaw
            rw [hStep] at hRaw
            exact hRaw
          rcases workRunExact_three_of_step machine config next workTape
            hStep hRepresents with ⟨middle, hThree, hMiddleRep⟩
          rcases ih next middle.tape hTail hMiddleRep.2 with
            ⟨workFinal, hRest, hFinalRep⟩
          have hMiddle :
              liftConfiguration machine next middle.tape = middle := by
            cases middle with
            | mk state tape =>
                have hState : state = controlState machine next.state :=
                  hMiddleRep.1
                change
                  (⟨controlState machine next.state, tape⟩ :
                    WorkConfiguration) = ⟨state, tape⟩
                rw [hState]
          rw [hMiddle] at hRest
          have hComposed := workRunExact?_compose
            (liftMachine machine) 3 (3 * steps)
            (liftConfiguration machine config workTape) middle workFinal
            hThree hRest
          refine ⟨workFinal, ?_, hFinalRep⟩
          have hCost : 3 * (steps + 1) = 3 + 3 * steps := by
            rw [Nat.mul_succ]
            exact Nat.add_comm _ _
          rw [hCost]
          exact hComposed

/-- Literal compilation reaches the encoded work endpoint with raw fuel
`18 * steps` for every exact `steps`-transition source execution. -/
theorem run_compileWorkMachine_eighteen_mul_of_rawRunExact
    (machine : Machine) (steps : Nat)
    (config final : Configuration) (workTape : WorkTape)
    (hRaw : rawRunExact? machine steps config = some final)
    (hRepresents : Represents config.tape workTape) :
    ∃ workFinal,
      run (compileWorkMachine (liftMachine machine)) (18 * steps)
          (encodeWorkConfiguration
            (liftConfiguration machine config workTape)) =
        encodeWorkConfiguration workFinal ∧
      RepresentsConfiguration machine final workFinal := by
  rcases workRunExact_three_mul_of_rawRunExact machine steps config final
    workTape hRaw hRepresents with ⟨workFinal, hWork, hFinalRep⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (liftMachine machine) (3 * steps)
    (liftConfiguration machine config workTape) workFinal hWork
  have hFuelAll : ∀ count : Nat, 18 * count = 6 * (3 * count) := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
        calc
          18 * (count + 1) = 18 * count + 18 := Nat.mul_succ 18 count
          _ = 6 * (3 * count) + 18 :=
            congrArg (fun value => value + 18) ih
          _ = 6 * (3 * count) + 6 * 3 := rfl
          _ = 6 * (3 * count + 3) :=
            (Nat.mul_add 6 (3 * count) 3).symm
          _ = 6 * (3 * (count + 1)) :=
            congrArg (fun value => 6 * value) (Nat.mul_succ 3 count).symm
  have hFuel := hFuelAll steps
  have hRunCost := congrArg
    (fun fuel =>
      run (compileWorkMachine (liftMachine machine)) fuel
        (encodeWorkConfiguration
          (liftConfiguration machine config workTape))) hFuel
  exact ⟨workFinal, hRunCost.trans hCompiled, hFinalRep⟩

end PipelineMachineSimulation

end PNP.Concrete
