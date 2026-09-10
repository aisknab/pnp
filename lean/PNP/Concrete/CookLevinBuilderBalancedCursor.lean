/-
Copyright (c) 2026 PNP Labs.

Physical balanced cursor over adjacent unary index and remaining registers.
The fixed table scans, transfers one unit across their separator, and returns
to the input head. It preserves tape span, the preceding width/register prefix,
the source input, the output region, and arbitrary data beyond the active end.
This is coordinate control, not clause selection, emission, or a complete builder.
-/

import PNP.Concrete.CookLevinBuilderInitialization

namespace PNP.Concrete.CookLevin.BuilderBalancedCursor

open PipelineTape

abbrev unitSymbol := BuilderUnaryPolynomial.unitSymbol
abbrev separatorSymbol := BuilderUnaryPolynomial.separatorSymbol
abbrev endSymbol := BuilderUnaryPolynomial.scratchEndSymbol

private def keep (source target : Nat) (symbol : WorkSymbol)
    (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := symbol, targetState := target,
    writeSymbol := symbol, move := move }

private def write (source target : Nat) (read written : WorkSymbol)
    (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := written, move := move }

def rules : List WorkRule :=
  [keep 0 1 .blank .left, keep 0 1 .zeroBlank .left,
   keep 0 1 .oneBlank .left, keep 1 2 leftMarker .left,
   keep 2 2 unitSymbol .left, keep 2 2 separatorSymbol .left,
   keep 2 3 endSymbol .right,
   keep 3 4 unitSymbol .right, keep 3 7 separatorSymbol .right,
   keep 4 4 unitSymbol .right, write 4 5 separatorSymbol unitSymbol .left,
   write 5 6 unitSymbol separatorSymbol .right,
   keep 6 6 unitSymbol .right, keep 6 6 separatorSymbol .right,
   keep 6 8 leftMarker .right,
   keep 7 7 unitSymbol .right, keep 7 7 separatorSymbol .right,
   keep 7 9 leftMarker .right]

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 8, rejectState := 9 }

theorem rules_length : rules.length = 18 := rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hRule
  change rule.sourceState ≠ 8
  change rule ∈ rules at hRule
  decide +revert

theorem noRuleAtReject :
    ∀ rule ∈ rules, rule.sourceState ≠ machine.rejectState := by
  decide

def RegisterSymbols (word : List WorkSymbol) : Prop :=
  ∀ symbol ∈ word, symbol = unitSymbol ∨ symbol = separatorSymbol

def word (wordPrefix : List WorkSymbol) (index remaining : Nat) : List WorkSymbol :=
  wordPrefix ++ separatorSymbol ::
    (List.replicate index unitSymbol ++ separatorSymbol ::
      List.replicate remaining unitSymbol)

def outside (wordPrefix : List WorkSymbol) (index remaining : Nat)
    (tail : List WorkSymbol) : List WorkSymbol :=
  word wordPrefix index remaining ++ endSymbol :: tail

def sourceTape (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index remaining : Nat) (tail : List WorkSymbol) : WorkTape :=
  { left := leftMarker :: outside wordPrefix index remaining tail,
    head := head, right := sourceTail }

def initialConfiguration (head : WorkSymbol)
    (sourceTail wordPrefix : List WorkSymbol) (index remaining : Nat)
    (tail : List WorkSymbol) : WorkConfiguration :=
  { state := 0, tape := sourceTape head sourceTail wordPrefix index remaining tail }

def advancedConfiguration (head : WorkSymbol)
    (sourceTail wordPrefix : List WorkSymbol) (index remaining : Nat)
    (tail : List WorkSymbol) : WorkConfiguration :=
  { state := 8, tape := sourceTape head sourceTail wordPrefix (index + 1) remaining tail }

def exhaustedConfiguration (head : WorkSymbol)
    (sourceTail wordPrefix : List WorkSymbol) (index : Nat)
    (tail : List WorkSymbol) : WorkConfiguration :=
  { state := 9, tape := sourceTape head sourceTail wordPrefix index 0 tail }

def steps (prefixLength index remaining : Nat) : Nat :=
  2 * (prefixLength + index + remaining) + if remaining = 0 then 8 else 10

theorem word_length (wordPrefix : List WorkSymbol) (index remaining : Nat) :
    (word wordPrefix index remaining).length = wordPrefix.length + index + remaining + 2 := by
  simp only [word, List.length_append, List.length_cons, List.length_replicate]
  omega

theorem word_symbols (wordPrefix : List WorkSymbol) (index remaining : Nat)
    (hPrefix : RegisterSymbols wordPrefix) : RegisterSymbols (word wordPrefix index remaining) := by
  intro symbol hMem
  simp only [word, List.mem_append, List.mem_cons] at hMem
  rcases hMem with hPrefixMem | hSeparator | hIndex | hSeparator | hRemaining
  · exact hPrefix symbol hPrefixMem
  · exact Or.inr hSeparator
  · exact Or.inl (List.eq_of_mem_replicate hIndex)
  · exact Or.inr hSeparator
  · exact Or.inl (List.eq_of_mem_replicate hRemaining)

theorem balanced_span (wordPrefix : List WorkSymbol) (index remaining : Nat) :
    (word wordPrefix index (remaining + 1)).length =
      (word wordPrefix (index + 1) remaining).length ∧
    index + (remaining + 1) = (index + 1) + remaining := by
  constructor
  · rw [word_length, word_length]
    omega
  · omega

private def leftFocus (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => { left := [], head := .blank, right := right }
  | symbol :: rest => { left := rest, head := symbol, right := right }

private def rightFocus (left right : List WorkSymbol) : WorkTape :=
  match right with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

private theorem one (initial final : WorkConfiguration)
    (hStep : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change (match workStep? machine initial with
    | none => none | some result => some result) = some final
  rw [hStep]

private theorem compose (first second : Nat) (initial middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first initial = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose machine first second
    initial middle final hFirst hSecond

private theorem seek_step (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : symbol = unitSymbol ∨ symbol = separatorSymbol) :
    workStep? machine { state := 2, tape := { left := left, head := symbol, right := right } } =
      some { state := 2, tape := leftFocus left (symbol :: right) } := by
  rcases hSymbol with hSymbol | hSymbol <;> subst symbol <;> rfl

private theorem scan_left (scanned tail right : List WorkSymbol)
    (hSymbols : RegisterSymbols scanned) :
    workRunExact? machine scanned.length
        { state := 2, tape := leftFocus (scanned ++ endSymbol :: tail) right } =
      some {
        state := 2
        tape := {
          left := tail
          head := endSymbol
          right := scanned.reverse ++ right
        }
      } := by
  induction scanned generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hSymbol := hSymbols symbol (by exact List.mem_cons_self)
    have hRest : RegisterSymbols rest := by
      intro item hItem
      exact hSymbols item (List.mem_cons_of_mem symbol hItem)
    have hStep := seek_step symbol (rest ++ endSymbol :: tail) right hSymbol
    simp only [List.length_cons, List.cons_append, leftFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      using ih (symbol :: right) hRest

private theorem scan_right (state : Nat) (scanned left : List WorkSymbol)
    (last : WorkSymbol) (tail : List WorkSymbol)
    (hStep : ∀ symbol ∈ scanned, ∀ left right,
      workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
        some { state := state, tape := rightFocus (symbol :: left) right }) :
    workRunExact? machine scanned.length
        { state := state, tape := rightFocus left (scanned ++ last :: tail) } =
      some {
        state := state
        tape := {
          left := scanned.reverse ++ left
          head := last
          right := tail
        }
      } := by
  induction scanned generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
    have hFirst := hStep symbol List.mem_cons_self left (rest ++ last :: tail)
    have hRest : ∀ symbol ∈ rest, ∀ left right,
        workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
          some { state := state, tape := rightFocus (symbol :: left) right } := by
      intro item hItem
      exact hStep item (List.mem_cons_of_mem symbol hItem)
    simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
    rw [hFirst]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      using ih (symbol :: left) hRest

private theorem return_step (state : Nat) (hState : state = 6 ∨ state = 7)
    (symbol : WorkSymbol) (hSymbol : symbol = unitSymbol ∨ symbol = separatorSymbol)
    (left right : List WorkSymbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := rightFocus (symbol :: left) right } := by
  rcases hState with hState | hState <;> subst state <;>
    rcases hSymbol with hSymbol | hSymbol <;> subst symbol <;> rfl

private theorem return_word_symbols (wordPrefix : List WorkSymbol) (index : Nat)
    (hPrefix : RegisterSymbols wordPrefix) :
    RegisterSymbols (List.replicate index unitSymbol ++ separatorSymbol :: wordPrefix.reverse) := by
  intro symbol hMem
  simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hMem
  rcases hMem with hUnit | hSeparator | hPrefixMem
  · exact Or.inl (List.eq_of_mem_replicate hUnit)
  · exact Or.inr hSeparator
  · exact hPrefix symbol hPrefixMem

private theorem to_probe (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index remaining : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    workRunExact? machine (2 + (word wordPrefix index remaining).length + 1)
        (initialConfiguration head sourceTail wordPrefix index remaining tail) =
      some {
        state := 3
        tape := rightFocus (endSymbol :: tail)
          (List.replicate remaining unitSymbol ++ separatorSymbol ::
            (List.replicate index unitSymbol ++ separatorSymbol :: wordPrefix.reverse) ++
            leftMarker :: head :: sourceTail) } := by
  let scanned := word wordPrefix index remaining
  let inside := leftMarker :: head :: sourceTail
  let c1 : WorkConfiguration :=
    { state := 2, tape := leftFocus (scanned ++ endSymbol :: tail) inside }
  let c2 : WorkConfiguration :=
    { state := 2
      tape := {
        left := tail
        head := endSymbol
        right := scanned.reverse ++ inside
      } }
  let c3 : WorkConfiguration :=
    { state := 3, tape := rightFocus (endSymbol :: tail) (scanned.reverse ++ inside) }
  have hStart : workRunExact? machine 2
      (initialConfiguration head sourceTail wordPrefix index remaining tail) = some c1 := by
    rcases hHead with hHead | hHead | hHead <;> subst head <;> rfl
  have hScan : workRunExact? machine scanned.length c1 = some c2 :=
    scan_left scanned tail inside (word_symbols wordPrefix index remaining hPrefix)
  have hEnd : workRunExact? machine 1 c2 = some c3 := one c2 c3 (by rfl)
  have hAll := compose _ _ _ _ _ (compose _ _ _ _ _ hStart hScan) hEnd
  simpa only [c3, scanned, inside, word, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append] using hAll

private theorem replicate_tail (count : Nat) (symbol : WorkSymbol) (tail : List WorkSymbol) :
    List.replicate count symbol ++ symbol :: tail = List.replicate (count + 1) symbol ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons symbol) ih

theorem advance_workRunExact (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index remaining : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    workRunExact? machine (steps wordPrefix.length index (remaining + 1))
        (initialConfiguration head sourceTail wordPrefix index (remaining + 1) tail) =
      some (advancedConfiguration head sourceTail wordPrefix index remaining tail) := by
  let ret := List.replicate index unitSymbol ++ separatorSymbol :: wordPrefix.reverse
  let inside := leftMarker :: head :: sourceTail
  let c0 : WorkConfiguration :=
    { state := 3
      tape := rightFocus (endSymbol :: tail)
        (List.replicate (remaining + 1) unitSymbol ++ separatorSymbol :: ret ++ inside) }
  let c1 : WorkConfiguration :=
    { state := 4
      tape := rightFocus (unitSymbol :: endSymbol :: tail)
        (List.replicate remaining unitSymbol ++ separatorSymbol :: ret ++ inside) }
  let c2 : WorkConfiguration :=
    { state := 4
      tape := {
        left := List.replicate (remaining + 1) unitSymbol ++ endSymbol :: tail
        head := separatorSymbol
        right := ret ++ inside } }
  let c3 : WorkConfiguration :=
    { state := 6
      tape := rightFocus (separatorSymbol ::
          (List.replicate remaining unitSymbol ++ endSymbol :: tail))
        (List.replicate (index + 1) unitSymbol ++ separatorSymbol :: wordPrefix.reverse ++ inside) }
  let returnWord := List.replicate (index + 1) unitSymbol ++ separatorSymbol :: wordPrefix.reverse
  let c4 : WorkConfiguration :=
    { state := 6
      tape := {
        left := outside wordPrefix (index + 1) remaining tail
        head := leftMarker
        right := head :: sourceTail } }
  have hStart := to_probe head sourceTail wordPrefix index (remaining + 1) tail hHead hPrefix
  have hProbe : workRunExact? machine 1 c0 = some c1 := one c0 c1 (by rfl)
  have hRewind : workRunExact? machine remaining c1 = some c2 := by
    have h := scan_right 4 (List.replicate remaining unitSymbol)
      (unitSymbol :: endSymbol :: tail) separatorSymbol (ret ++ inside) (by
        intro symbol hSymbol left right
        have hEq := List.eq_of_mem_replicate hSymbol
        subst symbol
        rfl)
    simpa only [c1, c2, List.length_replicate, List.reverse_replicate, replicate_tail,
      List.append_assoc, List.cons_append] using h
  have hSwap : workRunExact? machine 2 c2 = some c3 := by rfl
  have hReturn : workRunExact? machine returnWord.length c3 = some c4 := by
    have h := scan_right 6 returnWord
      (separatorSymbol :: (List.replicate remaining unitSymbol ++ endSymbol :: tail))
      leftMarker (head :: sourceTail) (by
        intro symbol hSymbol left right
        exact return_step 6 (Or.inl rfl) symbol
          (return_word_symbols wordPrefix (index + 1) hPrefix symbol hSymbol) left right)
    simpa only [c3, c4, returnWord, inside, outside, word, List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.reverse_reverse,
      List.append_assoc, List.cons_append, List.nil_append] using h
  have hExit : workRunExact? machine 1 c4 =
      some (advancedConfiguration head sourceTail wordPrefix index remaining tail) :=
    one _ _ (by rfl)
  have hAll := compose _ _ _ _ _
    (compose _ _ _ _ _ (compose _ _ _ _ _
      (compose _ _ _ _ _ hStart hProbe) hRewind) hSwap)
    (compose _ _ _ _ _ hReturn hExit)
  have hSteps :
      (((2 + (word wordPrefix index (remaining + 1)).length + 1 + 1) + remaining) + 2) +
        (returnWord.length + 1) = steps wordPrefix.length index (remaining + 1) := by
    simp only [returnWord, List.length_append, List.length_cons, List.length_replicate,
      List.length_reverse, word_length, steps, Nat.succ_ne_zero, if_false]
    omega
  rw [hSteps] at hAll
  exact hAll

theorem exhausted_workRunExact (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    workRunExact? machine (steps wordPrefix.length index 0)
        (initialConfiguration head sourceTail wordPrefix index 0 tail) =
      some (exhaustedConfiguration head sourceTail wordPrefix index tail) := by
  let returnWord := List.replicate index unitSymbol ++ separatorSymbol :: wordPrefix.reverse
  let inside := leftMarker :: head :: sourceTail
  let c0 : WorkConfiguration :=
    { state := 3
      tape := {
        left := endSymbol :: tail
        head := separatorSymbol
        right := returnWord ++ inside } }
  let c1 : WorkConfiguration :=
    { state := 7, tape := rightFocus (separatorSymbol :: endSymbol :: tail) (returnWord ++ inside) }
  let c2 : WorkConfiguration :=
    { state := 7
      tape := {
        left := outside wordPrefix index 0 tail
        head := leftMarker
        right := head :: sourceTail } }
  have hStart := to_probe head sourceTail wordPrefix index 0 tail hHead hPrefix
  have hProbe : workRunExact? machine 1 c0 = some c1 := one _ _ (by rfl)
  have hReturn : workRunExact? machine returnWord.length c1 = some c2 := by
    have h := scan_right 7 returnWord (separatorSymbol :: endSymbol :: tail)
      leftMarker (head :: sourceTail) (by
        intro symbol hSymbol left right
        exact return_step 7 (Or.inr rfl) symbol
          (return_word_symbols wordPrefix index hPrefix symbol hSymbol) left right)
    simpa only [c1, c2, returnWord, inside, outside, word, List.replicate_zero,
      List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_reverse,
      List.append_assoc, List.cons_append, List.nil_append] using h
  have hExit : workRunExact? machine 1 c2 =
      some (exhaustedConfiguration head sourceTail wordPrefix index tail) :=
    one _ _ (by rfl)
  have hAll := compose _ _ _ _ _ (compose _ _ _ _ _ hStart hProbe)
    (compose _ _ _ _ _ hReturn hExit)
  have hSteps : (2 + (word wordPrefix index 0).length + 1 + 1) +
      (returnWord.length + 1) = steps wordPrefix.length index 0 := by
    simp only [returnWord, List.length_append, List.length_cons, List.length_replicate,
      List.length_reverse, word_length, steps, if_true]
    omega
  rw [hSteps] at hAll
  exact hAll

theorem compiled_advance (head : WorkSymbol) (sourceTail wordPrefix : List WorkSymbol)
    (index remaining : Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hPrefix : RegisterSymbols wordPrefix) :
    run (compileWorkMachine machine) (6 * steps wordPrefix.length index (remaining + 1))
        (encodeWorkConfiguration (initialConfiguration head sourceTail wordPrefix index (remaining + 1) tail)) =
      encodeWorkConfiguration (advancedConfiguration head sourceTail wordPrefix index remaining tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (advance_workRunExact head sourceTail wordPrefix index remaining tail hHead hPrefix)

theorem compiled_steps_le (prefixLength index remaining : Nat) :
    6 * steps prefixLength index remaining ≤ 12 * (prefixLength + index + remaining + 2) + 36 := by
  unfold steps
  split <;> omega

end PNP.Concrete.CookLevin.BuilderBalancedCursor
