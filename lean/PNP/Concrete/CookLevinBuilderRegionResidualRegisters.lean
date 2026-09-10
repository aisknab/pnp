/-
Copyright (c) 2026 PNP Labs.

Restore the three physical fields of a comparator result to ordinary registers.
A one-cell left shift inserts their missing separator. The normalizing scan
counts marked-cell parity in fixed control, distinguishing greater from equal
without a supplied verdict. The protected workspace is never traversed.

The non-less residual still requires the proved copy/increment continuation;
this module is not the complete dispatcher or formula-builder reduction.
-/

import PNP.Concrete.CookLevinBuilderRegionComparisonOperands

namespace PNP.Concrete.CookLevin.BuilderRegionResidualRegisters

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial

abbrev boundaryMark : WorkSymbol := BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark
abbrev coordinateMark : WorkSymbol := BuilderArbitrarySlotHeaderRouter.RawRouter.coordinateMark

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := write, move := move }

private inductive Carry where
  | unit | separator | boundary

private def Carry.state : Carry → Nat
  | .unit => 3
  | .separator => 4
  | .boundary => 5

private def Carry.symbol : Carry → WorkSymbol
  | .unit => unitSymbol
  | .separator => separatorSymbol
  | .boundary => boundaryMark

private def carryRules (carry : Carry) : List WorkRule :=
  [rule carry.state Carry.unit.state unitSymbol carry.symbol .left,
   rule carry.state Carry.separator.state separatorSymbol carry.symbol .left,
   rule carry.state Carry.boundary.state boundaryMark carry.symbol .left,
   rule carry.state 6 scratchEndSymbol carry.symbol .left]

private def boundaryState (odd : Bool) : Nat := if odd then 9 else 8
private def restState (odd : Bool) : Nat := if odd then 11 else 10
private def markedState (odd : Bool) : Nat := if odd then 13 else 12
private def rewindState (odd : Bool) : Nat := if odd then 15 else 14
def terminalState (odd : Bool) : Nat := if odd then 17 else 16

private def parityRules (odd : Bool) : List WorkRule :=
  [rule (boundaryState odd) (boundaryState odd) unitSymbol unitSymbol .right,
   rule (boundaryState odd) (boundaryState (!odd)) boundaryMark unitSymbol .right,
   rule (boundaryState odd) (restState odd) separatorSymbol separatorSymbol .right,
   rule (restState odd) (restState odd) unitSymbol unitSymbol .right,
   rule (restState odd) (markedState odd) separatorSymbol separatorSymbol .right,
   rule (markedState odd) (markedState (!odd)) coordinateMark unitSymbol .right,
   rule (markedState odd) (rewindState odd) leftMarker separatorSymbol .left,
   rule (rewindState odd) (rewindState odd) unitSymbol unitSymbol .left,
   rule (rewindState odd) (rewindState odd) separatorSymbol separatorSymbol .left,
   rule (rewindState odd) (terminalState odd) scratchEndSymbol scratchEndSymbol .stay]

def rules : List WorkRule :=
  [rule 0 0 unitSymbol unitSymbol .left,
   rule 0 1 scratchEndSymbol scratchEndSymbol .right,
   rule 1 1 unitSymbol unitSymbol .right,
   rule 1 1 boundaryMark boundaryMark .right,
   rule 1 2 separatorSymbol separatorSymbol .right,
   rule 2 2 unitSymbol unitSymbol .right,
   rule 2 4 coordinateMark coordinateMark .left,
   rule 2 4 leftMarker leftMarker .left] ++
  carryRules .unit ++ carryRules .separator ++ carryRules .boundary ++
  [rule 6 7 .blank scratchEndSymbol .stay,
   rule 7 8 scratchEndSymbol scratchEndSymbol .right] ++
  parityRules false ++ parityRules true

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 16, rejectState := 17 }

theorem rules_length : rules.length = 42 := rfl

theorem rules_pairwise_query_distinct : rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro selected hMem
  change selected.sourceState ≠ 16
  change selected ∈ rules at hMem
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

/-- Descriptive fields of the existing tape, not supplied mathematical authority. -/
structure RestoreView where
  boundaryRest : Nat
  boundaryMarked : Nat
  coordinateRest : Nat
  coordinateMarked : Nat
  deriving DecidableEq, Repr

def toggled (odd : Bool) : Nat → Bool
  | 0 => odd
  | count + 1 => !(toggled odd count)

private theorem toggled_not (odd : Bool) (count : Nat) :
    toggled (!odd) count = !(toggled odd count) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [toggled, ih]

private theorem toggled_add (odd : Bool) (first second : Nat) :
    toggled odd (first + second) = toggled (toggled odd first) second := by
  induction second with
  | zero => simp only [Nat.add_zero, toggled]
  | succ second ih =>
    change Bool.not (toggled odd (first + second)) = Bool.not (toggled (toggled odd first) second)
    exact congrArg Bool.not ih

private theorem toggled_double (odd : Bool) (count : Nat) :
    toggled odd (count + count) = odd := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have h : (count + 1) + (count + 1) = (count + count) + 1 + 1 := by omega
    rw [h]
    simp only [toggled, ih, Bool.not_not]

def restoredValues (view : RestoreView) : List Nat :=
  [view.coordinateMarked, view.coordinateRest, view.boundaryRest + view.boundaryMarked]

def markedParity (view : RestoreView) : Bool :=
  toggled false (view.boundaryMarked + view.coordinateMarked)

def inputTape (view : RestoreView) (workspace tail : List WorkSymbol) : WorkTape :=
  BuilderDividerLayout.leftFocus
    (List.replicate view.boundaryRest unitSymbol ++ scratchEndSymbol :: tail)
    (List.replicate view.boundaryMarked boundaryMark ++ separatorSymbol ::
      (List.replicate view.coordinateRest unitSymbol ++
        List.replicate view.coordinateMarked coordinateMark ++ leftMarker :: workspace))

def initialConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (inputTape view workspace tail)

def finalConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  { state := terminalState (markedParity view),
    tape := BuilderDividerOperands.endTape (restoredValues view) workspace (tail.drop 1) }

def workSteps (view : RestoreView) : Nat :=
  5 * view.boundaryRest + 4 * view.boundaryMarked + 4 * view.coordinateRest +
    2 * view.coordinateMarked + 13

private def rightFocus (left word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

private def KeepRight (state : Nat) (symbol : WorkSymbol) : Prop :=
  (state = 1 ∧ (symbol = unitSymbol ∨ symbol = boundaryMark)) ∨
  (state = 2 ∧ symbol = unitSymbol) ∨
  (∃ odd, state = boundaryState odd ∧ symbol = unitSymbol) ∨
  (∃ odd, state = restState odd ∧ symbol = unitSymbol)

private theorem right_keep_step (state : Nat) (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : KeepRight state symbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := rightFocus (symbol :: left) right } := by
  rcases hSymbol with ⟨rfl, hSymbol⟩ | ⟨rfl, rfl⟩ | ⟨odd, rfl, rfl⟩ | ⟨odd, rfl, rfl⟩
  · rcases hSymbol with rfl | rfl <;> rfl
  · rfl
  · cases odd <;> rfl
  · cases odd <;> rfl

private theorem scan_right_keep (state : Nat) (word left right : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ word, KeepRight state symbol) :
    workRunExact? machine word.length
      { state := state, tape := rightFocus left (word ++ right) } =
      some { state := state, tape := rightFocus (word.reverse ++ left) right } := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
    have hRest : ∀ item ∈ rest, KeepRight state item := by
      intro item hMem
      exact hSymbols item (List.mem_cons_of_mem symbol hMem)
    simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
    rw [right_keep_step state symbol left _ (hSymbols symbol List.mem_cons_self)]
    simpa only [rightFocus, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      using ih (symbol :: left) hRest

private def KeepLeft (state : Nat) (symbol : WorkSymbol) : Prop :=
  (state = 0 ∧ symbol = unitSymbol) ∨
  (∃ odd, state = rewindState odd ∧ (symbol = unitSymbol ∨ symbol = separatorSymbol))

private theorem left_keep_step (state : Nat) (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : KeepLeft state symbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := BuilderDividerLayout.leftFocus left (symbol :: right) } := by
  rcases hSymbol with ⟨rfl, rfl⟩ | ⟨odd, rfl, hSymbol⟩
  · rfl
  · cases odd <;> rcases hSymbol with rfl | rfl <;> rfl

private theorem scan_left_keep (state : Nat) (word tail right : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ word, KeepLeft state symbol) :
    workRunExact? machine word.length
      { state := state, tape := BuilderDividerLayout.leftFocus (word ++ scratchEndSymbol :: tail) right } =
      some { state := state, tape := { left := tail, head := scratchEndSymbol, right := word.reverse ++ right } } := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hRest : ∀ item ∈ rest, KeepLeft state item := by
      intro item hMem
      exact hSymbols item (List.mem_cons_of_mem symbol hMem)
    simp only [List.length_cons, List.cons_append, BuilderDividerLayout.leftFocus, workRunExact?]
    rw [left_keep_step state symbol _ _ (hSymbols symbol List.mem_cons_self)]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      using ih (symbol :: right) hRest

private theorem carry_step (carry next : Carry) (left right : List WorkSymbol) :
    workStep? machine
      { state := carry.state, tape := { left := left, head := next.symbol, right := right } } =
      some { state := next.state,
             tape := BuilderDividerLayout.leftFocus left (carry.symbol :: right) } := by
  cases carry <;> cases next <;> rfl

private theorem carry_end (carry : Carry) (tail right : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine 2
      { state := carry.state, tape := { left := tail, head := scratchEndSymbol, right := right } } =
      some { state := 7,
             tape := { left := tail.drop 1, head := scratchEndSymbol, right := carry.symbol :: right } } := by
  cases tail with
  | nil => cases carry <;> rfl
  | cons symbol rest =>
    change symbol = .blank at hBlank
    subst symbol
    cases carry <;> rfl

private theorem shift_left (word : List Carry) (carry : Carry) (tail right : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine (word.length + 2)
      { state := carry.state,
        tape := BuilderDividerLayout.leftFocus (word.map Carry.symbol ++ scratchEndSymbol :: tail) right } =
      some { state := 7,
             tape := { left := tail.drop 1, head := scratchEndSymbol,
                       right := (word.map Carry.symbol).reverse ++ carry.symbol :: right } } := by
  induction word generalizing carry right with
  | nil => exact carry_end carry tail right hBlank
  | cons next rest ih =>
    simp only [List.length_cons, List.map_cons,
      List.cons_append, BuilderDividerLayout.leftFocus, workRunExact?]
    rw [carry_step]
    simpa only [workRunExact?, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append] using ih next (carry.symbol :: right)

private inductive MarkedPhase where
  | boundary | coordinate

private def MarkedPhase.state : MarkedPhase → Bool → Nat
  | .boundary => boundaryState
  | .coordinate => markedState

private def MarkedPhase.symbol : MarkedPhase → WorkSymbol
  | .boundary => boundaryMark
  | .coordinate => coordinateMark

private theorem marked_step (phase : MarkedPhase) (odd : Bool) (left right : List WorkSymbol) :
    workStep? machine
      { state := phase.state odd, tape := { left := left, head := phase.symbol, right := right } } =
      some { state := phase.state (!odd), tape := rightFocus (unitSymbol :: left) right } := by
  cases phase <;> cases odd <;> rfl

private theorem scan_marked (phase : MarkedPhase) (odd : Bool) (count : Nat)
    (left right : List WorkSymbol) :
    workRunExact? machine count
      { state := phase.state odd,
        tape := rightFocus left (List.replicate count phase.symbol ++ right) } =
      some { state := phase.state (toggled odd count),
             tape := rightFocus (List.replicate count unitSymbol ++ left) right } := by
  induction count generalizing odd left with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, rightFocus, workRunExact?]
    rw [marked_step]
    have hUnits : List.replicate count unitSymbol ++ unitSymbol :: left =
        unitSymbol :: (List.replicate count unitSymbol ++ left) := by
      calc
        _ = (List.replicate count unitSymbol ++ [unitSymbol]) ++ left := by
          rw [List.append_assoc]
          rfl
        _ = List.replicate (count + 1) unitSymbol ++ left := by
          rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ, List.cons_append]
    have h := ih (!odd) (unitSymbol :: left)
    rw [hUnits] at h
    simpa only [toggled, toggled_not, rightFocus] using h

private theorem start_shift (count : Nat) (left workspace : List WorkSymbol) :
    workRunExact? machine 1
      { state := 2, tape := rightFocus left (List.replicate count coordinateMark ++ leftMarker :: workspace) } =
      some {
        state := Carry.separator.state
        tape := BuilderDividerLayout.leftFocus left
          (List.replicate count coordinateMark ++ leftMarker :: workspace)
      } := by
  cases count <;> rfl

private theorem end_right_step (left right : List WorkSymbol) :
    workRunExact? machine 1
      { state := 7, tape := { left := left, head := scratchEndSymbol, right := right } } =
      some { state := boundaryState false, tape := rightFocus (scratchEndSymbol :: left) right } := rfl

private theorem boundary_separator_step (odd : Bool) (left right : List WorkSymbol) :
    workRunExact? machine 1
      { state := boundaryState odd, tape := { left := left, head := separatorSymbol, right := right } } =
      some { state := restState odd, tape := rightFocus (separatorSymbol :: left) right } := by
  cases odd <;> rfl

private theorem rest_separator_step (odd : Bool) (left right : List WorkSymbol) :
    workRunExact? machine 1
      { state := restState odd, tape := { left := left, head := separatorSymbol, right := right } } =
      some { state := markedState odd, tape := rightFocus (separatorSymbol :: left) right } := by
  cases odd <;> rfl

private theorem marked_end_step (odd : Bool) (left workspace : List WorkSymbol) :
    workRunExact? machine 1
      { state := markedState odd, tape := { left := left, head := leftMarker, right := workspace } } =
      some { state := rewindState odd, tape := BuilderDividerLayout.leftFocus left (separatorSymbol :: workspace) } := by
  cases odd <;> rfl

private theorem halt_step (odd : Bool) (left right : List WorkSymbol) :
    workRunExact? machine 1
      { state := rewindState odd, tape := { left := left, head := scratchEndSymbol, right := right } } =
      some { state := terminalState odd,
             tape := { left := left, head := scratchEndSymbol, right := right } } := by
  cases odd <;> rfl

private theorem startState_eq : machine.startState = 0 := rfl

private def boundaryWord (view : RestoreView) : List WorkSymbol :=
  List.replicate view.boundaryRest unitSymbol ++ List.replicate view.boundaryMarked boundaryMark

private def coordinateWord (view : RestoreView) (workspace : List WorkSymbol) : List WorkSymbol :=
  List.replicate view.coordinateRest unitSymbol ++
    (List.replicate view.coordinateMarked coordinateMark ++ leftMarker :: workspace)

private def shiftedTape (view : RestoreView) (workspace tail : List WorkSymbol) : WorkTape :=
  { left := tail.drop 1, head := scratchEndSymbol,
    right := boundaryWord view ++ separatorSymbol ::
      (List.replicate view.coordinateRest unitSymbol ++ separatorSymbol ::
        (List.replicate view.coordinateMarked coordinateMark ++ leftMarker :: workspace)) }

private def prefixSteps (view : RestoreView) : Nat :=
  3 * view.boundaryRest + 2 * view.boundaryMarked + 2 * view.coordinateRest + 6

private theorem prefix_workRunExact (view : RestoreView) (workspace tail : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine (prefixSteps view) (initialConfiguration view workspace tail) =
      some { state := 7, tape := shiftedTape view workspace tail } := by
  let a := view.boundaryRest
  let b := view.boundaryMarked
  let c := view.coordinateRest
  let d := view.coordinateMarked
  let bw := boundaryWord view
  let qw := coordinateWord view workspace
  let remaining := List.replicate d coordinateMark ++ leftMarker :: workspace
  let scanPrefix : List Carry :=
    List.replicate c .unit ++ [.separator] ++
      List.replicate b .boundary ++ List.replicate a .unit
  have hPrefix : scanPrefix.map Carry.symbol =
      (List.replicate c unitSymbol).reverse ++ separatorSymbol :: bw.reverse := by
    simp only [scanPrefix, bw, boundaryWord, a, b, c, List.map_append,
      List.map_replicate, List.map_cons, Carry.symbol,
      List.reverse_append, List.reverse_replicate, List.cons_append,
      List.nil_append, List.append_assoc]
  have hPrefixSteps : scanPrefix.length + 2 = a + b + c + 3 := by
    simp only [scanPrefix, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have h0 := scan_left_keep 0 (List.replicate a unitSymbol) tail
    (List.replicate b boundaryMark ++ separatorSymbol :: qw) (by
      intro symbol hMem
      exact Or.inl ⟨rfl, List.eq_of_mem_replicate hMem⟩)
  simp only [List.length_replicate, List.reverse_replicate] at h0
  have h0' : workRunExact? machine a (initialConfiguration view workspace tail) =
      some { state := 0, tape := { left := tail, head := scratchEndSymbol,
                                   right := bw ++ separatorSymbol :: qw } } := by
    simpa only [initialConfiguration, workStartConfiguration, startState_eq,
      inputTape, bw, boundaryWord, qw, coordinateWord, a, b,
      List.append_assoc] using h0
  have h1 : workRunExact? machine 1
      { state := 0, tape := { left := tail, head := scratchEndSymbol,
                              right := bw ++ separatorSymbol :: qw } } =
      some {
        state := 1
        tape := rightFocus (scratchEndSymbol :: tail) (bw ++ separatorSymbol :: qw)
      } := rfl
  have h2 := scan_right_keep 1 bw (scratchEndSymbol :: tail)
    (separatorSymbol :: qw) (by
      intro symbol hMem
      rcases List.mem_append.mp hMem with hMem | hMem
      · exact Or.inl ⟨rfl, Or.inl (List.eq_of_mem_replicate hMem)⟩
      · exact Or.inl ⟨rfl, Or.inr (List.eq_of_mem_replicate hMem)⟩)
  have hBwLength : bw.length = a + b := by
    simp only [bw, boundaryWord, a, b, List.length_append, List.length_replicate]
  rw [hBwLength] at h2
  have h3 : workRunExact? machine 1
      {
        state := 1
        tape := { left := bw.reverse ++ scratchEndSymbol :: tail,
                  head := separatorSymbol, right := qw }
      } =
      some {
        state := 2
        tape := rightFocus (separatorSymbol :: (bw.reverse ++ scratchEndSymbol :: tail)) qw
      } := rfl
  have h4 := scan_right_keep 2 (List.replicate c unitSymbol)
    (separatorSymbol :: (bw.reverse ++ scratchEndSymbol :: tail)) remaining (by
      intro symbol hMem
      exact Or.inr (Or.inl ⟨rfl, List.eq_of_mem_replicate hMem⟩))
  simp only [List.length_replicate] at h4
  have h5 := start_shift d
    ((List.replicate c unitSymbol).reverse ++
      separatorSymbol :: (bw.reverse ++ scratchEndSymbol :: tail)) workspace
  have h6 := shift_left scanPrefix .separator tail remaining hBlank
  rw [hPrefixSteps, hPrefix] at h6
  have h6' : workRunExact? machine (a + b + c + 3)
      { state := Carry.separator.state,
        tape := BuilderDividerLayout.leftFocus
          ((List.replicate c unitSymbol).reverse ++
            separatorSymbol :: (bw.reverse ++ scratchEndSymbol :: tail)) remaining } =
      some { state := 7, tape := shiftedTape view workspace tail } := by
    simpa only [shiftedTape, remaining, bw, c, d, Carry.symbol,
      List.reverse_append, List.reverse_cons, List.reverse_reverse,
      List.reverse_nil, List.cons_append, List.nil_append, List.append_assoc] using h6
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine a 1 _ _ _ h0' h1
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    (a + 1) (a + b) _ _ _ h01 h2
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (a + 1 + (a + b)) 1 _ _ _ h02 h3
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (a + 1 + (a + b) + 1) c _ _ _ h03 h4
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (a + 1 + (a + b) + 1 + c) 1 _ _ _ h04 h5
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (a + 1 + (a + b) + 1 + c + 1) (a + b + c + 3) _ _ _ h05 h6'
  have hSteps : a + 1 + (a + b) + 1 + c + 1 + (a + b + c + 3) =
      prefixSteps view := by
    unfold prefixSteps
    dsimp [a, b, c]
    omega
  rw [hSteps] at h06
  exact h06

private theorem replicate_append (first second : Nat) (symbol : WorkSymbol) :
    List.replicate first symbol ++ List.replicate second symbol =
      List.replicate (first + second) symbol := by
  induction first with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ first ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

private def suffixSteps (view : RestoreView) : Nat :=
  2 * view.boundaryRest + 2 * view.boundaryMarked + 2 * view.coordinateRest +
    2 * view.coordinateMarked + 7

private theorem suffix_workRunExact (view : RestoreView) (workspace tail : List WorkSymbol) :
    workRunExact? machine (suffixSteps view)
      { state := 7, tape := shiftedTape view workspace tail } =
      some (finalConfiguration view workspace tail) := by
  let a := view.boundaryRest
  let b := view.boundaryMarked
  let c := view.coordinateRest
  let d := view.coordinateMarked
  let outer := tail.drop 1
  let oddB := toggled false b
  let oddFinal := toggled oddB d
  let coordinate := List.replicate c unitSymbol ++ separatorSymbol ::
    (List.replicate d coordinateMark ++ leftMarker :: workspace)
  let marked := List.replicate d coordinateMark ++ leftMarker :: workspace
  let scanPrefix := List.replicate d unitSymbol ++ separatorSymbol ::
    (List.replicate c unitSymbol ++ separatorSymbol :: List.replicate (a + b) unitSymbol)
  have h0 := end_right_step outer (boundaryWord view ++ separatorSymbol :: coordinate)
  have h1 := scan_right_keep (boundaryState false) (List.replicate a unitSymbol)
    (scratchEndSymbol :: outer) (List.replicate b boundaryMark ++ separatorSymbol :: coordinate) (by
      intro symbol hMem
      exact Or.inr (Or.inr (Or.inl ⟨false, rfl, List.eq_of_mem_replicate hMem⟩)))
  simp only [List.length_replicate, List.reverse_replicate] at h1
  have h2 := scan_marked .boundary false b
    (List.replicate a unitSymbol ++ scratchEndSymbol :: outer) (separatorSymbol :: coordinate)
  have hJoin : List.replicate b unitSymbol ++
      (List.replicate a unitSymbol ++ scratchEndSymbol :: outer) =
      List.replicate (a + b) unitSymbol ++ scratchEndSymbol :: outer := by
    rw [← List.append_assoc, replicate_append, Nat.add_comm b a]
  simp only [MarkedPhase.state, MarkedPhase.symbol] at h2
  rw [hJoin] at h2
  have h3 := boundary_separator_step oddB
    (List.replicate (a + b) unitSymbol ++ scratchEndSymbol :: outer) coordinate
  have h4 := scan_right_keep (restState oddB) (List.replicate c unitSymbol)
    (separatorSymbol :: (List.replicate (a + b) unitSymbol ++ scratchEndSymbol :: outer))
    (separatorSymbol :: marked) (by
      intro symbol hMem
      exact Or.inr (Or.inr (Or.inr ⟨oddB, rfl, List.eq_of_mem_replicate hMem⟩)))
  simp only [List.length_replicate, List.reverse_replicate] at h4
  have h5 := rest_separator_step oddB
    (List.replicate c unitSymbol ++ separatorSymbol ::
      (List.replicate (a + b) unitSymbol ++ scratchEndSymbol :: outer)) marked
  have h6 := scan_marked .coordinate oddB d
    (separatorSymbol :: (List.replicate c unitSymbol ++ separatorSymbol ::
      (List.replicate (a + b) unitSymbol ++ scratchEndSymbol :: outer))) (leftMarker :: workspace)
  simp only [MarkedPhase.state, MarkedPhase.symbol] at h6
  have h7 := marked_end_step oddFinal (scanPrefix ++ scratchEndSymbol :: outer) workspace
  have h8 := scan_left_keep (rewindState oddFinal) scanPrefix outer (separatorSymbol :: workspace) (by
    intro symbol hMem
    have hSafe : symbol = unitSymbol ∨ symbol = separatorSymbol := by
      simp only [scanPrefix, List.mem_append, List.mem_cons] at hMem
      rcases hMem with hMem | rfl | hMem | rfl | hMem
      · exact Or.inl (List.eq_of_mem_replicate hMem)
      · exact Or.inr rfl
      · exact Or.inl (List.eq_of_mem_replicate hMem)
      · exact Or.inr rfl
      · exact Or.inl (List.eq_of_mem_replicate hMem)
    exact Or.inr ⟨oddFinal, rfl, hSafe⟩)
  have hLength : scanPrefix.length = a + b + c + d + 2 := by
    simp only [scanPrefix, List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [hLength] at h8
  have h9 := halt_step oddFinal outer (scanPrefix.reverse ++ separatorSymbol :: workspace)
  simp only [boundaryWord, coordinate, marked, scanPrefix, outer, a, b, c, d,
    List.append_assoc, List.cons_append] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine 1 a _ _ _ h0 h1
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine (1 + a) b _ _ _ h01 h2
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine (1 + a + b) 1 _ _ _ h02 h3
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine (1 + a + b + 1) c _ _ _ h03 h4
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine (1 + a + b + 1 + c) 1 _ _ _ h04 h5
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine (1 + a + b + 1 + c + 1) d _ _ _ h05 h6
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + a + b + 1 + c + 1 + d) 1 _ _ _ h06 h7
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + a + b + 1 + c + 1 + d + 1) (a + b + c + d + 2) _ _ _ h07 h8
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + a + b + 1 + c + 1 + d + 1 + (a + b + c + d + 2)) 1 _ _ _ h08 h9
  have hSteps : 1 + a + b + 1 + c + 1 + d + 1 + (a + b + c + d + 2) + 1 =
      suffixSteps view := by
    unfold suffixSteps
    dsimp [a, b, c, d]
    omega
  have hOdd : oddFinal = markedParity view := by
    exact (toggled_add false b d).symm
  rw [hSteps, hOdd] at h09
  simpa only [shiftedTape, finalConfiguration, BuilderDividerOperands.endTape,
    restoredValues, boundaryWord, coordinate, marked, scanPrefix, outer, a, b, c, d,
    registerWord, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.reverse_replicate, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc] using h09

/-- The marker parity is computed by actual transitions; the workspace is untouched. -/
theorem workRunExact (view : RestoreView) (workspace tail : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) := by
  have h := PipelineMachineSimulation.workRunExact?_compose machine
    (prefixSteps view) (suffixSteps view) _ _ _
    (prefix_workRunExact view workspace tail hBlank) (suffix_workRunExact view workspace tail)
  have hSteps : prefixSteps view + suffixSteps view = workSteps view := by
    unfold prefixSteps suffixSteps workSteps
    omega
  rw [hSteps] at h
  exact h

theorem run_compile_exact (view : RestoreView) (workspace tail : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    run (compileWorkMachine machine) (6 * workSteps view)
      (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact view workspace tail hBlank)

theorem workSteps_le (view : RestoreView) (bound : Nat)
    (hA : view.boundaryRest ≤ bound) (hB : view.boundaryMarked ≤ bound)
    (hC : view.coordinateRest ≤ bound) (hD : view.coordinateMarked ≤ bound) :
    workSteps view ≤ 15 * bound + 13 := by
  unfold workSteps
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 90) bound) (.constant 78)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 90 * bound.eval input + 78 := rfl

theorem rawTimePolynomial_le (view : RestoreView) (bound : NatPolynomial) (input : Nat)
    (hA : view.boundaryRest ≤ bound.eval input) (hB : view.boundaryMarked ≤ bound.eval input)
    (hC : view.coordinateRest ≤ bound.eval input) (hD : view.coordinateMarked ≤ bound.eval input) :
    6 * workSteps view ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  have h := workSteps_le view (bound.eval input) hA hB hC hD
  omega

open BuilderArbitrarySlotHeaderRouter

def ofComparison : RawRouter.ComparisonResult → RestoreView
  | .less processed remaining => ⟨remaining + 1, processed, 0, processed⟩
  | .equal processed => ⟨0, processed, 0, processed⟩
  | .greater processed remaining => ⟨0, processed, remaining, processed + 1⟩

def isGreater : RawRouter.ComparisonResult → Bool
  | .less _ _ => false
  | .equal _ => false
  | .greater _ _ => true

theorem ofComparison_markedParity (result : RawRouter.ComparisonResult) :
    markedParity (ofComparison result) = isGreater result := by
  cases result with
  | less processed remaining =>
    exact toggled_double false processed
  | equal processed =>
    exact toggled_double false processed
  | greater processed remaining =>
    simp only [markedParity, ofComparison, isGreater, Nat.add_succ, toggled,
      toggled_double, Bool.not_false]

theorem ofComparison_restoredValues (result : RawRouter.ComparisonResult) :
    restoredValues (ofComparison result) =
      match result with
      | .less processed remaining => [processed, 0, (remaining + 1) + processed]
      | .equal processed => [processed, 0, processed]
      | .greater processed remaining => [processed + 1, remaining, processed] := by
  cases result <;> simp only [restoredValues, ofComparison, Nat.zero_add]


/-- The descriptive view is the actual mirrored comparator tape for every result. -/
theorem inputTape_ofComparison (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    inputTape (ofComparison result) workspace [] =
      BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
        (BuilderPostDividerRawRouteClassifier.appendExteriorTape
          (RawRouter.resultConfiguration result).tape workspace) := by
  cases result <;>
    simp only [inputTape, ofComparison, BuilderDividerLayout.leftFocus,
      BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape,
      BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
      BuilderPostDividerRawRouteClassifier.appendExteriorTape, RawRouter.resultConfiguration,
      List.replicate_zero, List.replicate_succ, List.nil_append,
      List.cons_append, List.append_assoc] <;> rfl

theorem comparison_workRunExact (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps (ofComparison result))
      (workStartConfiguration machine
        (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
          (BuilderPostDividerRawRouteClassifier.appendExteriorTape
            (RawRouter.resultConfiguration result).tape workspace))) =
      some (finalConfiguration (ofComparison result) workspace []) := by
  rw [← inputTape_ofComparison]
  exact workRunExact (ofComparison result) workspace [] rfl

theorem comparison_final_state (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    (finalConfiguration (ofComparison result) workspace []).state = terminalState (isGreater result) := by
  change terminalState (markedParity (ofComparison result)) = _
  rw [ofComparison_markedParity]

end PNP.Concrete.CookLevin.BuilderRegionResidualRegisters
