/-
Copyright (c) 2026 PNP Labs.

A single literal machine reads an arbitrary source bit at an index stored in
the nearest unary register. Temporary source/counter marks are restored, and
the result code (0 absent, 1 false, 2 true) is appended as a new register.
The scan does not cross the source terminator into tally or prior output.

This primitive is not a canonical constraint constructor or complete builder.
The caller must still derive its requested index from the physical source and
regional coordinates and prove the full writer/loop execution.
-/

import PNP.Concrete.CookLevinBuilderDividerOperands
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.CookLevin.BuilderIndexedInputRead

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)

def bitSymbol (bit : Bool) : WorkSymbol := if bit then .oneBlank else .zeroBlank
def markedBit (bit : Bool) : WorkSymbol := if bit then .oneZero else .zeroZero
def resultCode : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

private def restoreSource (read : WorkSymbol) : WorkSymbol :=
  if read = .zeroZero then .zeroBlank else if read = .oneZero then .oneBlank else read

private def restoreRegister (read : WorkSymbol) : WorkSymbol :=
  if read = registerMarkSymbol then unitSymbol else read

private def isRegister (read : WorkSymbol) : Bool :=
  read == unitSymbol || read == separatorSymbol

private def markedSource (read : WorkSymbol) : Bool :=
  read == .zeroZero || read == .oneZero

private def sourceRewindSpec (code : Nat) : StateSpec := fun read =>
  if markedSource read then writeAction (9 + code) (restoreSource read) .left
  else if read = leftMarker then keepAction (12 + code) .left read
  else deadAction 20 read

private def registerRewindSpec (code : Nat) : StateSpec := fun read =>
  if isRegister read || read == registerMarkSymbol then
    writeAction (12 + code) (restoreRegister read) .left
  else if read = scratchEndSymbol then writeAction (15 + code) separatorSymbol .left
  else deadAction 20 read

private def seekOlderSpec (next : Nat) : StateSpec := fun read =>
  if isRegister read then keepAction (next - 1) .right read
  else if read = leftMarker then keepAction next .right read
  else deadAction 20 read

private def stateSpec : Nat → StateSpec
  | 0 => fun read =>
      if read = scratchEndSymbol then keepAction 1 .right read else deadAction 20 read
  | 1 => fun read =>
      if read = registerMarkSymbol then keepAction 1 .right read
      else if read = unitSymbol then writeAction 2 registerMarkSymbol .right
      else if read = separatorSymbol then keepAction 7 .right read
      else deadAction 20 read
  | 2 => fun read =>
      if read = unitSymbol then keepAction 2 .right read
      else if read = separatorSymbol then keepAction 3 .right read
      else deadAction 20 read
  | 3 => seekOlderSpec 4
  | 4 => fun read =>
      if markedSource read then keepAction 4 .right read
      else if read = .zeroBlank then writeAction 5 .zeroZero .left
      else if read = .oneBlank then writeAction 5 .oneZero .left
      else if read == .blank || read == rightMarker then keepAction 9 .left read
      else deadAction 20 read
  | 5 => fun read =>
      if markedSource read then keepAction 5 .left read
      else if read = leftMarker then keepAction 6 .left read
      else deadAction 20 read
  | 6 => fun read =>
      if isRegister read || read == registerMarkSymbol then keepAction 6 .left read
      else if read = scratchEndSymbol then keepAction 0 .stay read
      else deadAction 20 read
  | 7 => seekOlderSpec 8
  | 8 => fun read =>
      if markedSource read then keepAction 8 .right read
      else if read = .zeroBlank then keepAction 10 .left read
      else if read = .oneBlank then keepAction 11 .left read
      else if read == .blank || read == rightMarker then keepAction 9 .left read
      else deadAction 20 read
  | 9 => sourceRewindSpec 0
  | 10 => sourceRewindSpec 1
  | 11 => sourceRewindSpec 2
  | 12 => registerRewindSpec 0
  | 13 => registerRewindSpec 1
  | 14 => registerRewindSpec 2
  | 15 => fun _ => writeAction 18 scratchEndSymbol .stay
  | 16 => fun _ => writeAction 15 unitSymbol .left
  | 17 => fun _ => writeAction 16 unitSymbol .left
  | _ => fun read => deadAction 20 read

private def stateSpecs : List StateSpec := List.ofFn fun state : Fin 18 => stateSpec state.val

/-- The rule table is fixed; neither the index nor source bits select a program. -/
def machine : WorkMachine :=
  { rules := rulesFrom 0 stateSpecs, startState := 0, acceptState := 18, rejectState := 19 }

private theorem lookup_at (specs : List StateSpec) (base index : Nat)
    (hIndex : index < specs.length) (symbol : WorkSymbol) :
    findWorkRule (rulesFrom base specs) (base + index) symbol =
      some (ruleOf (base + index) specs[index] symbol) := by
  induction specs generalizing base index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons spec rest ih =>
      cases index with
      | zero => simpa using findWorkRule_rulesFrom_head base spec rest symbol
      | succ index =>
          have hRest : index < rest.length := by
            simp only [List.length_cons] at hIndex
            omega
          rw [rulesFrom, findWorkRule_append_of_none]
          · simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using ih (base + 1) index hRest
          · exact findWorkRule_rulesAt_none_of_state_ne base (base + (index + 1))
              spec symbol (by omega)

private theorem lookup (state : Nat) (hState : state < 18) (symbol : WorkSymbol) :
    findWorkRule machine.rules state symbol = some (ruleOf state (stateSpec state) symbol) := by
  have hIndex : state < stateSpecs.length := by
    simpa only [stateSpecs, List.length_ofFn] using hState
  simpa only [machine, stateSpecs, Nat.zero_add, List.getElem_ofFn] using
    lookup_at stateSpecs 0 state hIndex symbol

private theorem step_at (state : Nat) (tape : WorkTape) (hState : state < 18) :
    workStep? machine { state := state, tape := tape } =
      some (applyWorkRule (ruleOf state (stateSpec state) tape.head)
        { state := state, tape := tape }) := by
  apply workStep?_eq_apply_of_find
  · simp only [WorkMachine.isHalted, machine, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor <;> omega
  · exact lookup state hState tape.head

theorem rules_length : machine.rules.length = 162 := by
  simp only [machine, rulesFrom_length, stateSpecs, List.length_ofFn]

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  rulesFrom_pairwise_query_distinct 0 stateSpecs

private theorem source_lt (specs : List StateSpec) (base : Nat) (rule : WorkRule)
    (hMem : rule ∈ rulesFrom base specs) : rule.sourceState < base + specs.length := by
  induction specs generalizing base with
  | nil => cases hMem
  | cons spec rest ih =>
      rw [rulesFrom, List.mem_append] at hMem
      rcases hMem with hHead | hTail
      · rcases List.mem_map.mp hHead with ⟨symbol, _, hRule⟩
        rw [← hRule]
        simp only [ruleOf, List.length_cons]
        omega
      · have h := ih (base + 1) hTail
        simp only [List.length_cons]
        omega

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hMem
  have h := source_lt stateSpecs 0 rule hMem
  simp only [stateSpecs, List.length_ofFn, Nat.zero_add] at h
  exact Nat.ne_of_lt h

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  intro rule hMem
  have h := source_lt stateSpecs 0 rule hMem
  simp only [stateSpecs, List.length_ofFn, Nat.zero_add] at h
  change rule.sourceState ≠ 19
  omega

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private def rightFocus (left : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => { left := left, head := .blank, right := [] }
  | head :: right => { left := left, head := head, right := right }

private def leftFocus (right : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => { left := [], head := .blank, right := right }
  | head :: left => { left := left, head := head, right := right }

private abbrev Run (steps : Nat) (first last : WorkConfiguration) :=
  workRunExact? machine steps first = some last

private theorem run_compose {first middle last : WorkConfiguration} {left right : Nat}
    (hLeft : Run left first middle) (hRight : Run right middle last) :
    Run (left + right) first last :=
  PipelineMachineSimulation.workRunExact?_compose machine left right first middle last hLeft hRight

private theorem run_steps {first last : WorkConfiguration} {left right : Nat}
    (hRun : Run left first last) (hSteps : left = right) : Run right first last := hSteps ▸ hRun

private theorem step_right (state next : Nat) (left right : List WorkSymbol)
    (read write : WorkSymbol) (hState : state < 18)
    (hSpec : stateSpec state read = writeAction next write .right) :
    Run 1 { state := state, tape := { left := left, head := read, right := right } }
      { state := next, tape := rightFocus (write :: left) right } := by
  have h := step_at state { left := left, head := read, right := right } hState
  simp only [ruleOf, hSpec, writeAction, applyWorkRule, WorkTape.write, WorkTape.move,
    WorkTape.moveRight] at h
  cases right <;> simp only [Run, workRunExact?, h, rightFocus]

private theorem step_left (state next : Nat) (left right : List WorkSymbol)
    (read write : WorkSymbol) (hState : state < 18)
    (hSpec : stateSpec state read = writeAction next write .left) :
    Run 1 { state := state, tape := { left := left, head := read, right := right } }
      { state := next, tape := leftFocus (write :: right) left } := by
  have h := step_at state { left := left, head := read, right := right } hState
  cases left <;> simpa only [Run, workRunExact?, h, ruleOf, hSpec, writeAction,
    applyWorkRule, WorkTape.write, WorkTape.move, WorkTape.moveLeft, leftFocus]

private theorem scan_right (state : Nat) (mapping : WorkSymbol → WorkSymbol)
    (word left right : List WorkSymbol) (stop : WorkSymbol) (hState : state < 18)
    (hSpec : ∀ read ∈ word, stateSpec state read = writeAction state (mapping read) .right) :
    Run word.length
      { state := state, tape := rightFocus left (word ++ stop :: right) }
      { state := state, tape := { left := (word.map mapping).reverse ++ left, head := stop, right := right } } := by
  induction word generalizing left with
  | nil => rfl
  | cons read rest ih =>
      have hStep := step_right state state left (rest ++ stop :: right) read (mapping read)
        hState (hSpec read List.mem_cons_self)
      have hRest := ih (mapping read :: left)
        (fun symbol hMem => hSpec symbol (List.mem_cons_of_mem read hMem))
      have hRun := run_compose hStep hRest
      simpa only [List.length_cons, Nat.one_add, rightFocus, List.cons_append, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append,
        Nat.succ_eq_add_one] using hRun

private theorem scan_left (state : Nat) (mapping : WorkSymbol → WorkSymbol)
    (word left right : List WorkSymbol) (stop : WorkSymbol) (hState : state < 18)
    (hSpec : ∀ read ∈ word, stateSpec state read = writeAction state (mapping read) .left) :
    Run word.length
      { state := state, tape := leftFocus right (word ++ stop :: left) }
      { state := state, tape := { left := left, head := stop, right := (word.map mapping).reverse ++ right } } := by
  induction word generalizing right with
  | nil => rfl
  | cons read rest ih =>
      have hStep := step_left state state (rest ++ stop :: left) right read (mapping read)
        hState (hSpec read List.mem_cons_self)
      have hRest := ih (mapping read :: right)
        (fun symbol hMem => hSpec symbol (List.mem_cons_of_mem read hMem))
      have hRun := run_compose hStep hRest
      simpa only [List.length_cons, Nat.one_add, leftFocus, List.cons_append, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append,
        Nat.succ_eq_add_one] using hRun

private theorem restoreSource_marked (bit : Bool) : restoreSource (markedBit bit) = bitSymbol bit := by
  cases bit <;> rfl

private theorem restoreRegister_regular (word : List WorkSymbol)
    (hWord : BuilderBalancedCursor.RegisterSymbols word) :
    word.map restoreRegister = word := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      have hRest := ih (fun item hItem => hWord item (List.mem_cons_of_mem symbol hItem))
      have hSymbol := hWord symbol List.mem_cons_self
      rcases hSymbol with rfl | rfl
      · change unitSymbol :: rest.map restoreRegister = unitSymbol :: rest
        rw [hRest]
      · change separatorSymbol :: rest.map restoreRegister = separatorSymbol :: rest
        rw [hRest]

private theorem restoreRegister_unit : restoreRegister unitSymbol = unitSymbol := rfl
private theorem restoreRegister_separator : restoreRegister separatorSymbol = separatorSymbol := rfl
private theorem restoreRegister_mark : restoreRegister registerMarkSymbol = unitSymbol := rfl

private theorem replicate_sum (left right : Nat) (symbol : WorkSymbol) :
    List.replicate (left + right) symbol =
      List.replicate left symbol ++ List.replicate right symbol := by
  induction left with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ left ih =>
      simp only [Nat.succ_add, List.replicate_succ, ih, List.cons_append]

private def sourceConfiguration (state : Nat) (processed : BitString)
    (older counterLeft : List WorkSymbol) (head : WorkSymbol) (right : List WorkSymbol) : WorkConfiguration :=
  { state := state
    tape := { left := (processed.map markedBit).reverse ++ leftMarker :: (older ++ separatorSymbol :: counterLeft), head := head, right := right } }

/-- Starting at the index delimiter, walk only the older registers and marked input processed. -/
private theorem seek_source (reading : Bool) (processed : BitString)
    (older counterLeft : List WorkSymbol) (head : WorkSymbol) (right : List WorkSymbol)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    Run (older.length + processed.length + 2)
      { state := if reading then 1 else 2
        tape := { left := counterLeft, head := separatorSymbol, right := older.reverse ++ leftMarker :: (processed.map markedBit ++ head :: right) } }
      (sourceConfiguration (if reading then 8 else 4) processed older counterLeft head right) := by
  let seek := if reading then 7 else 3
  let readState := if reading then 8 else 4
  have hStart := step_right (if reading then 1 else 2) seek counterLeft
    (older.reverse ++ leftMarker :: (processed.map markedBit ++ head :: right))
    separatorSymbol separatorSymbol (by cases reading <;> simp only [seek, readState, Bool.false_eq_true, if_false, if_true] <;> omega)
    (by cases reading <;> rfl)
  have hOlderRun := scan_right seek id older.reverse (separatorSymbol :: counterLeft)
    (processed.map markedBit ++ head :: right) leftMarker (by cases reading <;> simp only [seek, readState, Bool.false_eq_true, if_false, if_true] <;> omega) (by
      intro symbol hMem
      have hSymbol := hOlder symbol (List.mem_reverse.mp hMem)
      rcases hSymbol with rfl | rfl <;> cases reading <;> rfl)
  have hBoundary := step_right seek readState (older ++ separatorSymbol :: counterLeft)
    (processed.map markedBit ++ head :: right) leftMarker leftMarker
    (by cases reading <;> simp only [seek, readState, Bool.false_eq_true, if_false, if_true] <;> omega) (by cases reading <;> rfl)
  have hPrefix := scan_right readState id (processed.map markedBit)
    (leftMarker :: (older ++ separatorSymbol :: counterLeft)) right head
    (by cases reading <;> simp only [seek, readState, Bool.false_eq_true, if_false, if_true] <;> omega) (by
      intro symbol hMem
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hMem
      cases reading <;> cases bit <;> rfl)
  have hRun := run_compose (run_compose (run_compose hStart (by
    simpa only [List.map_id, List.reverse_reverse] using hOlderRun)) hBoundary) hPrefix
  apply run_steps (by
    simpa only [sourceConfiguration, List.map_id] using hRun)
  simp only [List.length_reverse, List.length_map]
  omega

private theorem sourceRewind_spec (code : Nat) (hCode : code ≤ 2) :
    stateSpec (9 + code) = sourceRewindSpec code := by
  cases code with
  | zero => rfl
  | succ code =>
      cases code with
      | zero => rfl
      | succ code =>
          cases code with
          | zero => rfl
          | succ code => exact False.elim (by omega)

private theorem registerRewind_spec (code : Nat) (hCode : code ≤ 2) :
    stateSpec (12 + code) = registerRewindSpec code := by
  cases code with
  | zero => rfl
  | succ code =>
      cases code with
      | zero => rfl
      | succ code =>
          cases code with
          | zero => rfl
          | succ code => exact False.elim (by omega)

private theorem emit_spec (code : Nat) (hCode : code < 2) :
    stateSpec (16 + code) = fun _ => writeAction (15 + code) unitSymbol .left := by
  cases code with
  | zero => rfl
  | succ code =>
      cases code with
      | zero => rfl
      | succ code => exact False.elim (by omega)

private theorem emit_run (code : Nat) (hCode : code ≤ 2)
    (right tail : List WorkSymbol) :
    Run (code + 1)
      { state := 15 + code, tape := leftFocus right tail }
      { state := 18, tape := { left := tail.drop (code + 1), head := scratchEndSymbol, right := List.replicate code unitSymbol ++ right } } := by
  induction code generalizing right tail with
  | zero =>
      have hRun : Run 1 { state := 15, tape := leftFocus right tail }
          { state := 18, tape := (leftFocus right tail).write scratchEndSymbol } := by
        have h := step_at 15 (leftFocus right tail) (by decide)
        simp only [Run, workRunExact?]
        rw [h]
        rfl
      cases tail <;> simpa only [Nat.add_zero, leftFocus, WorkTape.write,
        List.drop_succ_cons, List.drop_zero, List.drop_nil, List.replicate_zero,
        List.nil_append] using hRun
  | succ code ih =>
      have hSmall : code < 2 := by omega
      have hStep : Run 1 { state := 15 + (code + 1), tape := leftFocus right tail }
          { state := 15 + code, tape := leftFocus (unitSymbol :: right) (tail.drop 1) } := by
        rw [show 15 + (code + 1) = 16 + code by omega]
        cases tail with
        | nil =>
            simpa only [leftFocus, List.drop_nil, Nat.add_assoc] using
              step_left (16 + code) (15 + code) [] right .blank unitSymbol (by omega)
                (congrFun (emit_spec code hSmall) .blank)
        | cons symbol rest =>
            simpa only [leftFocus, List.drop_succ_cons, List.drop_zero, Nat.add_assoc] using
              step_left (16 + code) (15 + code) rest right symbol unitSymbol (by omega)
                (congrFun (emit_spec code hSmall) symbol)
      have hRun := run_compose hStep (ih (by omega) (unitSymbol :: right) (tail.drop 1))
      apply run_steps (by
        simpa only [List.drop_drop, List.replicate_succ', List.append_assoc,
          List.singleton_append, Nat.add_assoc, Nat.add_comm] using hRun)
      omega

private theorem append_result (code : Nat) (hCode : code ≤ 2)
    (right tail : List WorkSymbol) :
    Run (code + 2)
      { state := 12 + code, tape := { left := tail, head := scratchEndSymbol, right := right } }
      { state := 18, tape := { left := tail.drop (code + 1), head := scratchEndSymbol, right := List.replicate code unitSymbol ++ separatorSymbol :: right } } := by
  have hStep := step_left (12 + code) (15 + code) tail right scratchEndSymbol separatorSymbol
    (by omega) (by
      rw [registerRewind_spec code hCode]
      rfl)
  have hRun := run_compose hStep (emit_run code hCode (separatorSymbol :: right) tail)
  exact run_steps hRun (by omega)

private def restoredConfiguration (code marks remaining : Nat) (processed : BitString)
    (older : List WorkSymbol) (head : WorkSymbol) (right tail : List WorkSymbol) : WorkConfiguration :=
  { state := 18
    tape := { left := tail.drop (code + 1), head := scratchEndSymbol, right := List.replicate code unitSymbol ++ separatorSymbol :: (List.replicate (marks + remaining) unitSymbol ++ separatorSymbol :: (older.reverse ++ leftMarker :: (processed.map bitSymbol ++ head :: right))) } }

private theorem restore_read (code marks remaining : Nat) (hCode : code ≤ 2)
    (processed : BitString) (older : List WorkSymbol) (head : WorkSymbol)
    (right tail : List WorkSymbol) (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    Run (older.length + processed.length + remaining + marks + code + 4)
      { state := 9 + code
        tape := leftFocus (head :: right)
          ((processed.map markedBit).reverse ++ leftMarker ::
            (older ++ separatorSymbol :: (List.replicate remaining unitSymbol ++
              List.replicate marks registerMarkSymbol ++ scratchEndSymbol :: tail))) }
      (restoredConfiguration code marks remaining processed older head right tail) := by
  let counter := List.replicate remaining unitSymbol ++
    List.replicate marks registerMarkSymbol ++ scratchEndSymbol :: tail
  let sourceRight := processed.map bitSymbol ++ head :: right
  let registers := older ++ separatorSymbol :: (List.replicate remaining unitSymbol ++
    List.replicate marks registerMarkSymbol)
  have hSource := scan_left (9 + code) restoreSource (processed.map markedBit).reverse
    (older ++ separatorSymbol :: counter) (head :: right) leftMarker (by omega) (by
      intro symbol hMem
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hMem)
      rw [sourceRewind_spec code hCode]
      cases bit <;> rfl)
  have hSourceMap : (((processed.map markedBit).reverse).map restoreSource).reverse =
      processed.map bitSymbol := by
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def,
      restoreSource_marked]
  have hBoundary := step_left (9 + code) (12 + code) (older ++ separatorSymbol :: counter)
    sourceRight leftMarker leftMarker (by omega) (by
      rw [sourceRewind_spec code hCode]
      rfl)
  have hRegisters := scan_left (12 + code) restoreRegister registers tail
    (leftMarker :: sourceRight) scratchEndSymbol (by omega) (by
      intro symbol hMem
      rw [registerRewind_spec code hCode]
      change symbol ∈ older ++ separatorSymbol ::
        (List.replicate remaining unitSymbol ++ List.replicate marks registerMarkSymbol) at hMem
      simp only [List.mem_append, List.mem_cons] at hMem
      rcases hMem with hOld | rfl | hUnit | hMark
      · rcases hOlder symbol hOld with rfl | rfl <;> rfl
      · rfl
      · rw [List.eq_of_mem_replicate hUnit]
        rfl
      · rw [List.eq_of_mem_replicate hMark]
        rfl)
  have hRegisterMap : (registers.map restoreRegister).reverse =
      List.replicate (marks + remaining) unitSymbol ++ separatorSymbol :: older.reverse := by
    simp only [registers, List.map_append, List.map_cons, restoreRegister_regular older hOlder,
      List.map_replicate, restoreRegister_unit, restoreRegister_separator, restoreRegister_mark, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, replicate_sum, List.append_assoc, List.singleton_append]
  simp only [registers] at hRegisterMap
  have hFinish := append_result code hCode
    (List.replicate (marks + remaining) unitSymbol ++ separatorSymbol ::
      (older.reverse ++ leftMarker :: sourceRight)) tail
  have hFirst := run_compose (by
    simpa only [hSourceMap, sourceRight] using hSource) hBoundary
  have hSecond := run_compose hFirst (by
    simpa only [registers, counter, List.append_assoc, List.cons_append,
      List.singleton_append] using hRegisters)
  have hAll := run_compose (by
    simpa only [hRegisterMap, List.append_assoc, List.cons_append] using hSecond) hFinish
  apply run_steps (by
    simpa only [restoredConfiguration, counter, sourceRight, List.append_assoc,
      List.cons_append] using hAll)
  simp only [registers, List.length_append, List.length_cons, List.length_replicate,
    List.length_reverse, List.length_map]
  omega

private def loopTape (processed input : BitString) (remaining : Nat)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol) : WorkTape :=
  { left := tail, head := scratchEndSymbol, right := List.replicate processed.length registerMarkSymbol ++ List.replicate remaining unitSymbol ++ separatorSymbol :: (older.reverse ++ leftMarker :: (processed.map markedBit ++ input.map bitSymbol ++ terminator :: right)) }

private def finalTape (code index : Nat) (input : BitString)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol) : WorkTape :=
  { left := tail.drop (code + 1), head := scratchEndSymbol, right := List.replicate code unitSymbol ++ separatorSymbol :: (List.replicate index unitSymbol ++ separatorSymbol :: (older.reverse ++ leftMarker :: (input.map bitSymbol ++ terminator :: right))) }

/-- Exact cost; recursion specifies a trace length, not runtime program generation. -/
def loopSteps (olderLength seen : Nat) : Nat → BitString → Nat
  | 0, input => 2 * olderLength + 4 * seen + resultCode input[0]? + 8
  | remaining + 1, [] => 2 * olderLength + 4 * seen + 2 * remaining + 10
  | remaining + 1, _ :: rest =>
      2 * olderLength + 4 * seen + 2 * remaining + 9 +
        loopSteps olderLength (seen + 1) remaining rest

private theorem start_index (processed input : BitString) (remaining : Nat)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol) :
    Run (processed.length + 1)
      { state := 0, tape := loopTape processed input remaining older terminator right tail }
      { state := 1
        tape := rightFocus (List.replicate processed.length registerMarkSymbol ++ scratchEndSymbol :: tail)
          (List.replicate remaining unitSymbol ++ separatorSymbol ::
            (older.reverse ++ leftMarker ::
              (processed.map markedBit ++ input.map bitSymbol ++ terminator :: right))) } := by
  let suffix := List.replicate remaining unitSymbol ++ separatorSymbol ::
    (older.reverse ++ leftMarker ::
      (processed.map markedBit ++ input.map bitSymbol ++ terminator :: right))
  have hStep := step_right 0 1 tail
    (List.replicate processed.length registerMarkSymbol ++ suffix) scratchEndSymbol scratchEndSymbol
    (by decide) (by rfl)
  have hScan : Run processed.length
      { state := 1, tape := rightFocus (scratchEndSymbol :: tail)
          (List.replicate processed.length registerMarkSymbol ++ suffix) }
      { state := 1, tape := rightFocus
          (List.replicate processed.length registerMarkSymbol ++ scratchEndSymbol :: tail) suffix } := by
    have hNonempty : suffix ≠ [] := by
      have hLength : 0 < suffix.length := by
        simp only [suffix, List.length_append, List.length_cons, List.length_replicate]
        omega
      intro hEmpty
      simp only [hEmpty, List.length_nil] at hLength
      omega
    cases hSuffix : suffix with
    | nil => exact False.elim (hNonempty hSuffix)
    | cons first rest =>
        simpa only [List.length_replicate, List.map_id, List.reverse_replicate, rightFocus] using
          scan_right 1 id (List.replicate processed.length registerMarkSymbol) (scratchEndSymbol :: tail)
            rest first (by decide) (by
              intro symbol hMem
              rw [List.eq_of_mem_replicate hMem]
              rfl)
  exact run_steps (by simpa only [loopTape, suffix, List.append_assoc] using run_compose hStep hScan) (by omega)

private def firstSymbol (input : BitString) (terminator : WorkSymbol) : WorkSymbol :=
  match input with
  | [] => terminator
  | bit :: _ => bitSymbol bit

private def afterFirst (input : BitString) (terminator : WorkSymbol)
    (right : List WorkSymbol) : List WorkSymbol :=
  match input with
  | [] => right
  | _ :: rest => rest.map bitSymbol ++ terminator :: right

private theorem first_layout (input : BitString) (terminator : WorkSymbol)
    (right : List WorkSymbol) :
    input.map bitSymbol ++ terminator :: right =
      firstSymbol input terminator :: afterFirst input terminator right := by
  cases input <;> rfl

theorem resultCode_le (value : Option Bool) : resultCode value ≤ 2 := by
  cases value with
  | none => change 0 ≤ 2; omega
  | some bit => cases bit <;> simp only [resultCode] <;> omega

private theorem observe_first (input : BitString) (terminator : WorkSymbol)
    (hTerminator : terminator = .blank ∨ terminator = rightMarker) :
    stateSpec 8 (firstSymbol input terminator) =
      keepAction (9 + resultCode input[0]?) .left (firstSymbol input terminator) := by
  cases input with
  | nil => rcases hTerminator with rfl | rfl <;> rfl
  | cons bit rest => cases bit <;> rfl

private theorem finish_observed (state code marks remaining : Nat)
    (processed : BitString) (older : List WorkSymbol) (head : WorkSymbol)
    (right tail : List WorkSymbol) (hOlder : BuilderBalancedCursor.RegisterSymbols older)
    (hState : state < 18) (hCode : code ≤ 2)
    (hObserve : stateSpec state head = keepAction (9 + code) .left head) :
    Run (older.length + processed.length + remaining + marks + code + 5)
      (sourceConfiguration state processed older
        (List.replicate remaining unitSymbol ++ List.replicate marks registerMarkSymbol ++
          scratchEndSymbol :: tail) head right)
      (restoredConfiguration code marks remaining processed older head right tail) := by
  have hStep := step_left state (9 + code)
    ((processed.map markedBit).reverse ++ leftMarker ::
      (older ++ separatorSymbol :: (List.replicate remaining unitSymbol ++
        List.replicate marks registerMarkSymbol ++ scratchEndSymbol :: tail)))
    right head head hState hObserve
  have hRestore := restore_read code marks remaining hCode processed older head right tail hOlder
  exact run_steps (by simpa only [sourceConfiguration] using run_compose hStep hRestore) (by omega)

private theorem advance_seek (processed input : BitString) (remaining : Nat)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    Run (older.length + 2 * processed.length + remaining + 4)
      { state := 0, tape := loopTape processed input (remaining + 1) older terminator right tail }
      (sourceConfiguration 4 processed older
        (List.replicate remaining unitSymbol ++
          List.replicate (processed.length + 1) registerMarkSymbol ++ scratchEndSymbol :: tail)
        (firstSymbol input terminator) (afterFirst input terminator right)) := by
  let suffix := older.reverse ++ leftMarker ::
    (processed.map markedBit ++ input.map bitSymbol ++ terminator :: right)
  have hStart := start_index processed input (remaining + 1) older terminator right tail
  have hMark := step_right 1 2
    (List.replicate processed.length registerMarkSymbol ++ scratchEndSymbol :: tail)
    (List.replicate remaining unitSymbol ++ separatorSymbol :: suffix)
    unitSymbol registerMarkSymbol (by decide) (by rfl)
  have hRemaining := scan_right 2 id (List.replicate remaining unitSymbol)
    (List.replicate (processed.length + 1) registerMarkSymbol ++ scratchEndSymbol :: tail)
    suffix separatorSymbol (by decide) (by
      intro symbol hMem
      rw [List.eq_of_mem_replicate hMem]
      rfl)
  have hSeek := seek_source false processed older
    (List.replicate remaining unitSymbol ++
      List.replicate (processed.length + 1) registerMarkSymbol ++ scratchEndSymbol :: tail)
    (firstSymbol input terminator) (afterFirst input terminator right) hOlder
  simp only [Bool.false_eq_true, if_false] at hSeek
  have hFirst := run_compose (by
    simpa only [suffix, List.replicate_succ, List.cons_append, rightFocus] using hStart) hMark
  have hSecond := run_compose (by
    simpa only [List.replicate_succ, List.cons_append] using hFirst) hRemaining
  have hAll := run_compose (by
    simpa only [List.map_id, List.reverse_replicate, suffix, List.append_assoc, first_layout input terminator right] using hSecond) hSeek
  exact run_steps hAll (by simp only [List.length_replicate]; omega)

private theorem skip_bit (processed : BitString) (bit : Bool) (input : BitString) (remaining : Nat)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    Run (older.length + 2 * processed.length + remaining + 5)
      (sourceConfiguration 4 processed older
        (List.replicate remaining unitSymbol ++
          List.replicate (processed.length + 1) registerMarkSymbol ++ scratchEndSymbol :: tail)
        (bitSymbol bit) (input.map bitSymbol ++ terminator :: right))
      { state := 0, tape := loopTape (processed ++ [bit]) input remaining older terminator right tail } := by
  let counter := List.replicate remaining unitSymbol ++
    List.replicate (processed.length + 1) registerMarkSymbol ++ scratchEndSymbol :: tail
  let sourceRight := markedBit bit :: (input.map bitSymbol ++ terminator :: right)
  let registers := older ++ separatorSymbol :: (List.replicate remaining unitSymbol ++
    List.replicate (processed.length + 1) registerMarkSymbol)
  have hMark := step_left 4 5
    ((processed.map markedBit).reverse ++ leftMarker :: (older ++ separatorSymbol :: counter))
    (input.map bitSymbol ++ terminator :: right) (bitSymbol bit) (markedBit bit)
    (by decide) (by cases bit <;> rfl)
  have hSource := scan_left 5 id (processed.map markedBit).reverse
    (older ++ separatorSymbol :: counter) sourceRight leftMarker (by decide) (by
      intro symbol hMem
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hMem)
      cases value <;> rfl)
  have hBoundary := step_left 5 6 (older ++ separatorSymbol :: counter)
    (processed.map markedBit ++ sourceRight) leftMarker leftMarker (by decide) (by rfl)
  have hRegisters := scan_left 6 id registers tail
    (leftMarker :: (processed.map markedBit ++ sourceRight)) scratchEndSymbol (by decide) (by
      intro symbol hMem
      change symbol ∈ older ++ separatorSymbol :: (List.replicate remaining unitSymbol ++
        List.replicate (processed.length + 1) registerMarkSymbol) at hMem
      simp only [List.mem_append, List.mem_cons] at hMem
      rcases hMem with hOld | rfl | hUnit | hMark
      · rcases hOlder symbol hOld with rfl | rfl <;> rfl
      · rfl
      · rw [List.eq_of_mem_replicate hUnit]
        rfl
      · rw [List.eq_of_mem_replicate hMark]
        rfl)
  have hStop : Run 1
      { state := 6, tape := { left := tail, head := scratchEndSymbol, right := registers.reverse ++ leftMarker :: (processed.map markedBit ++ sourceRight) } }
      { state := 0, tape := { left := tail, head := scratchEndSymbol, right := registers.reverse ++ leftMarker :: (processed.map markedBit ++ sourceRight) } } := by
    rfl
  have hFirst := run_compose (by simpa only [sourceConfiguration, counter] using hMark) hSource
  have hSecond := run_compose (by
    simpa only [List.map_id, List.reverse_reverse] using hFirst) hBoundary
  have hThird := run_compose hSecond (by
    simpa only [registers, counter, List.append_assoc, List.cons_append] using hRegisters)
  have hAll := run_compose (by simpa only [List.map_id] using hThird) hStop
  apply run_steps (by
    simpa only [loopTape, registers, counter, sourceRight, sourceConfiguration, List.nil_append,
      Nat.zero_add, List.map_append, List.map_cons,
      List.map_nil, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
      List.cons_append, List.singleton_append] using hAll)
  simp only [registers, List.length_append, List.length_cons, List.length_replicate,
    List.length_reverse, List.length_map]
  omega

private theorem loop_run (remaining : Nat) (processed input : BitString)
    (older : List WorkSymbol) (terminator : WorkSymbol) (right tail : List WorkSymbol)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older)
    (hTerminator : terminator = .blank ∨ terminator = rightMarker) :
    Run (loopSteps older.length processed.length remaining input)
      { state := 0, tape := loopTape processed input remaining older terminator right tail }
      { state := 18, tape := finalTape (resultCode input[remaining]?)
          (processed.length + remaining) (processed ++ input) older terminator right tail } := by
  induction remaining generalizing processed input with
  | zero =>
      have hStart := start_index processed input 0 older terminator right tail
      have hSeek := seek_source true processed older
        (List.replicate processed.length registerMarkSymbol ++ scratchEndSymbol :: tail)
        (firstSymbol input terminator) (afterFirst input terminator right) hOlder
      have hFinish := finish_observed 8 (resultCode input[0]?) processed.length 0 processed older
        (firstSymbol input terminator) (afterFirst input terminator right) tail hOlder (by decide)
        (resultCode_le _) (observe_first input terminator hTerminator)
      simp only [if_true] at hSeek
      have hFirst := run_compose (by
        simpa only [List.replicate_zero, List.nil_append, rightFocus, List.append_assoc, first_layout input terminator right] using hStart) hSeek
      have hAll := run_compose hFirst (by
        simpa only [List.replicate_zero, List.nil_append] using hFinish)
      apply run_steps (by
        simpa only [restoredConfiguration, finalTape, List.map_append, List.append_assoc,
          first_layout input terminator right] using hAll)
      simp only [loopSteps]
      omega
  | succ remaining ih =>
      have hSeek := advance_seek processed input remaining older terminator right tail hOlder
      cases input with
      | nil =>
          have hFinish := finish_observed 4 0 (processed.length + 1) remaining processed older
            terminator right tail hOlder (by decide) (by decide) (by
              rcases hTerminator with rfl | rfl <;> rfl)
          have hAll := run_compose (by
            simpa only [firstSymbol, afterFirst] using hSeek) hFinish
          apply run_steps (by
            simpa only [restoredConfiguration, finalTape, List.append_nil,
              List.getElem?_nil, resultCode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll)
          simp only [loopSteps]
          omega
      | cons bit rest =>
          have hSkip := skip_bit processed bit rest remaining older terminator right tail hOlder
          have hFirst := run_compose (by
            simpa only [firstSymbol, afterFirst] using hSeek) hSkip
          have hAll := run_compose hFirst (ih (processed ++ [bit]) rest)
          apply run_steps (by
            simpa only [List.getElem?_cons_succ, List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Nat.zero_add, List.append_assoc, List.singleton_append,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll)
          simp only [loopSteps, List.length_append, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add]
          omega

private def sourceTerminator : BitString → WorkSymbol
  | [] => .blank
  | _ :: _ => rightMarker

private def sourceRemainder (input : BitString) (output : List CNFToken) : List WorkSymbol :=
  let rest := List.replicate input.length BuilderInputLength.tallySymbol ++
    BuilderTokenAppender.outputRegion output
  match input with
  | [] => rightMarker :: rest
  | _ :: _ => rest

private theorem bitSymbol_eq_data (bit : Bool) :
    bitSymbol bit = dataSymbol (TapeSymbol.ofBool bit) := by
  cases bit <;> rfl

private theorem inside_layout (input : BitString) (output : List CNFToken) :
    inside input output =
      leftMarker :: (input.map bitSymbol ++ sourceTerminator input :: sourceRemainder input output) := by
  cases input with
  | nil => rfl
  | cons bit rest =>
      have hSymbols : bitSymbol = fun value => dataSymbol (TapeSymbol.ofBool value) := by
        funext value
        exact bitSymbol_eq_data value
      simp only [inside, BuilderTokenAppender.workspaceTape, frameWithGarbage, Tape.ofInput,
        List.map_nil, List.nil_append, List.map_cons, List.map_map, Function.comp_def,
        sourceTerminator, sourceRemainder, hSymbols, List.cons_append]

def initialConfiguration (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [index]) (inside input output) tail)

def finalConfiguration (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := endTape (older ++ [index, resultCode input[index]?]) (inside input output)
      (tail.drop (resultCode input[index]? + 1)) }

def workSteps (older : List Nat) (index : Nat) (input : BitString) : Nat :=
  loopSteps (registerWord older).length 0 index input

/-- No index bound, supplied source answer or selected branch is required. -/
theorem workRunExact (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older index input)
      (initialConfiguration older index input output tail) =
      some (finalConfiguration older index input output tail) := by
  have hTerm : sourceTerminator input = .blank ∨ sourceTerminator input = rightMarker := by
    cases input with
    | nil => exact Or.inl rfl
    | cons bit rest => exact Or.inr rfl
  have hRun := loop_run index [] input (registerWord older) (sourceTerminator input)
    (sourceRemainder input output) tail (BuilderRegisterAccess.registerWord_symbols older) hTerm
  simpa only [Run, initialConfiguration, finalConfiguration, workSteps, workStartConfiguration,
    machine, loopTape, finalTape, endTape, registerWord_append, registerWord,
    inside_layout, List.map_nil, List.nil_append, List.length_nil, List.replicate_zero,
    Nat.zero_add, List.append_nil, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.append_assoc, List.cons_append] using hRun

theorem run_compile_exact (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps older index input)
      (encodeWorkConfiguration (initialConfiguration older index input output tail)) =
      encodeWorkConfiguration (finalConfiguration older index input output tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact older index input output tail)

theorem final_tape (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    (finalConfiguration older index input output tail).tape =
      endTape (older ++ [index, resultCode input[index]?]) (inside input output)
        (tail.drop (resultCode input[index]? + 1)) := rfl

theorem final_accept (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    (finalConfiguration older index input output tail).state = machine.acceptState := rfl

theorem loopSteps_le (olderLength seen remaining : Nat) (input : BitString) :
    loopSteps olderLength seen remaining input ≤
      (remaining + 1) * (2 * olderLength + 6 * (seen + remaining) + 12) := by
  induction remaining generalizing seen input with
  | zero =>
      have hCode := resultCode_le input[0]?
      simp only [loopSteps, Nat.zero_add, Nat.add_zero, Nat.one_mul]
      omega
  | succ remaining ih =>
      let bound := 2 * olderLength + 6 * (seen + (remaining + 1)) + 12
      cases input with
      | nil =>
          have hPositive : 1 ≤ remaining + 1 + 1 := by omega
          have hMul := Nat.mul_le_mul_right bound hPositive
          simp only [Nat.one_mul] at hMul
          have hStep : loopSteps olderLength seen (remaining + 1) [] ≤ bound := by
            simp only [loopSteps, bound]
            omega
          exact Nat.le_trans hStep hMul
      | cons bit rest =>
          have hRest : loopSteps olderLength (seen + 1) remaining rest ≤ (remaining + 1) * bound := by
            simpa only [bound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih (seen + 1) rest
          have hStep : 2 * olderLength + 4 * seen + 2 * remaining + 9 ≤ bound := by
            dsimp only [bound]
            omega
          change (2 * olderLength + 4 * seen + 2 * remaining + 9) +
            loopSteps olderLength (seen + 1) remaining rest ≤ (remaining + 1 + 1) * bound
          calc
            _ ≤ bound + (remaining + 1) * bound := Nat.add_le_add hStep hRest
            _ = (remaining + 1 + 1) * bound :=
              (Nat.add_comm bound ((remaining + 1) * bound)).trans
                (Nat.succ_mul (remaining + 1) bound).symm

theorem workSteps_le (older : List Nat) (index : Nat) (input : BitString) :
    workSteps older index input ≤
      (index + 1) * (2 * (registerWord older).length + 6 * index + 12) := by
  simpa only [workSteps, Nat.zero_add] using loopSteps_le (registerWord older).length 0 index input

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6)
    (.mul (.add bound (.constant 1)) (.add (.mul (.constant 8) bound) (.constant 12)))

theorem rawTimePolynomial_eval (bound : NatPolynomial) (inputLength : Nat) :
    (rawTimePolynomial bound).eval inputLength =
      6 * ((bound.eval inputLength + 1) * (8 * bound.eval inputLength + 12)) := rfl

/-- Bounds on already materialized register space and index suffice; output size is irrelevant. -/
theorem rawTimeBound_le (bound : NatPolynomial) (older : List Nat) (index : Nat) (input : BitString)
    (hOlder : (registerWord older).length ≤ bound.eval input.length)
    (hIndex : index ≤ bound.eval input.length) :
    6 * workSteps older index input ≤ (rawTimePolynomial bound).eval input.length := by
  rw [rawTimePolynomial_eval]
  apply Nat.mul_le_mul_left 6
  apply Nat.le_trans (workSteps_le older index input)
  apply Nat.mul_le_mul
  · omega
  · omega

theorem register_span_added (older : List Nat) (index : Nat) (input : BitString) :
    (registerWord (older ++ [index, resultCode input[index]?])).length =
      (registerWord (older ++ [index])).length + resultCode input[index]? + 1 := by
  simp only [registerWord_append, List.length_append, registerWord_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

theorem register_span_increase_le (older : List Nat) (index : Nat) (input : BitString) :
    (registerWord (older ++ [index, resultCode input[index]?])).length ≤
      (registerWord (older ++ [index])).length + 3 := by
  rw [register_span_added]
  have hCode := resultCode_le input[index]?
  omega

theorem invalid_entry (tape : WorkTape) (hHead : tape.head ≠ scratchEndSymbol) :
    workRunExact? machine 1 (workStartConfiguration machine tape) =
      some { state := 20, tape := tape } := by
  have h := step_at 0 tape (by decide)
  change workRunExact? machine 1 { state := 0, tape := tape } =
    some { state := 20, tape := tape }
  simp only [workRunExact?, h, ruleOf, stateSpec, if_neg hHead, deadAction,
    keepAction, applyWorkRule, WorkTape.write, WorkTape.move]

end PNP.Concrete.CookLevin.BuilderIndexedInputRead
