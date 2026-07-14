/-
Copyright (c) 2026 PNP Labs.

Finite whole-tableau constraint families for the concrete Cook--Levin route.

This layer allocates every time, tape, head, state, certificate-bit, and
certificate-length variable through the collision-free layout.  It emits the
one-hot row constraints and the complete deterministic transition constraints
for the compiled verifier machine, the exact input/certificate row, and the
designated accepting endpoint before exposing the concrete CNF formula.

No SAT solver, minimization procedure, semantic oracle, or caller-supplied
proof certificate occurs in the construction.
-/

import PNP.Concrete.CookLevinLocalCNF

namespace PNP.Concrete

namespace CookLevin

/-! ### Constructive finite enumerations -/

/-- Enumerate every member of one finite initial segment exactly once. -/
def finiteIndices : (width : Nat) → List (Fin width)
  | 0 => []
  | width + 1 =>
      ⟨0, Nat.zero_lt_succ width⟩ ::
        (finiteIndices width).map Fin.succ

theorem finiteIndices_length (width : Nat) :
    (finiteIndices width).length = width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      change Nat.succ ((finiteIndices width).map Fin.succ).length =
        Nat.succ width
      have mapLength : ((finiteIndices width).map Fin.succ).length =
          (finiteIndices width).length := by
        induction finiteIndices width with
        | nil => rfl
        | cons first rest restIH =>
            exact congrArg Nat.succ restIH
      rw [mapLength, ih]

theorem mem_map_of_mem (mapping : α → β) {item : α} {items : List α}
    (hItem : item ∈ items) : mapping item ∈ items.map mapping := by
  induction items with
  | nil => cases hItem
  | cons first rest ih =>
      cases hItem with
      | head => exact List.Mem.head _
      | tail _ hTail => exact List.Mem.tail _ (ih hTail)

theorem finiteIndices_mem {width : Nat} (index : Fin width) :
    index ∈ finiteIndices width := by
  induction width with
  | zero => exact Fin.elim0 index
  | succ width ih =>
      rcases index with ⟨value, hValue⟩
      cases value with
      | zero => exact List.Mem.head _
      | succ previous =>
          exact List.Mem.tail _
            (mem_map_of_mem Fin.succ
              (ih ⟨previous, Nat.lt_of_succ_lt_succ hValue⟩))

def tapeSymbols : List TapeSymbol :=
  [.blank, .zero, .one]

theorem tapeSymbols_mem (symbol : TapeSymbol) : symbol ∈ tapeSymbols := by
  cases symbol
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-! ### Layout-bound literals -/

namespace VerifierTableauProblem

abbrev FormulaWidth {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.layout.variableCount

def symbolLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : BoundedLiteral problem.FormulaWidth :=
  { positive := true
    index := ⟨problem.layout.symbolVariable time position symbol,
      problem.layout.symbolVariable_lt_variableCount time position symbol⟩ }

def headLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    BoundedLiteral problem.FormulaWidth :=
  { positive := true
    index := ⟨problem.layout.headVariable time position,
      problem.layout.headVariable_lt_variableCount time position⟩ }

def stateLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (state : Fin problem.dimensions.stateBound) :
    BoundedLiteral problem.FormulaWidth :=
  { positive := true
    index := ⟨problem.layout.stateVariable time state,
      problem.layout.stateVariable_lt_variableCount time state⟩ }

def certificateBitLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin problem.layout.certificateBitWidth) :
    BoundedLiteral problem.FormulaWidth :=
  { positive := true
    index := ⟨problem.layout.certificateBitVariable index,
      problem.layout.certificateBitVariable_lt_variableCount index⟩ }

def certificateLengthLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin problem.layout.certificateLengthWidth) :
    BoundedLiteral problem.FormulaWidth :=
  { positive := true
    index := ⟨problem.layout.certificateLengthVariable length,
      problem.layout.certificateLengthVariable_lt_variableCount length⟩ }

def symbolVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    List (Fin problem.FormulaWidth) :=
  tapeSymbols.map fun symbol => (problem.symbolLiteral time position symbol).index

def headVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices
    (problem.dimensions.tapeWidth problem.tableauInputMode)).map fun position =>
      (problem.headLiteral time position).index

def stateVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices problem.dimensions.stateBound).map fun state =>
    (problem.stateLiteral time state).index

/-! ### One-hot shape of every represented row -/

def symbolShapeAt {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalConstraint problem.FormulaWidth :=
  .exactlyOne (problem.symbolVariables time position)

def symbolShapeRow {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices
    (problem.dimensions.tapeWidth problem.tableauInputMode)).map fun position =>
      problem.symbolShapeAt time position

def headShapeAt {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalConstraint problem.FormulaWidth :=
  .exactlyOne (problem.headVariables time)

def stateShapeAt {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalConstraint problem.FormulaWidth :=
  .exactlyOne (problem.stateVariables time)

def rowShapeProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    LocalProgram problem.FormulaWidth :=
  problem.symbolShapeRow time ++
    [problem.headShapeAt time, problem.stateShapeAt time]

def shapeProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices problem.dimensions.timeCount).flatMap fun time =>
    problem.rowShapeProgram time

/-! ### Literal first-match local transition action -/

theorem findRule_some_mem (rules : List Rule) (state : Nat)
    (symbol : TapeSymbol) (selected : Rule)
    (hSelected : findRule rules state symbol = some selected) :
    selected ∈ rules := by
  induction rules with
  | nil => cases hSelected
  | cons first rest ih =>
      unfold findRule at hSelected
      cases hMatch : (first.sourceState == state && first.readSymbol == symbol) with
      | false =>
          rw [hMatch] at hSelected
          exact List.Mem.tail first (ih hSelected)
      | true =>
          rw [hMatch] at hSelected
          have hEqual : first = selected := Option.some.inj hSelected
          rw [← hEqual]
          exact List.Mem.head rest

structure LocalAction {language : Language}
    (problem : VerifierTableauProblem language) where
  targetState : Fin problem.dimensions.stateBound
  writeSymbol : TapeSymbol
  move : HeadMove
deriving DecidableEq, Repr

def localAction {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound)
    (symbol : TapeSymbol) : LocalAction problem :=
  if state.val == problem.rawMachine.acceptState ||
      state.val == problem.rawMachine.rejectState then
    { targetState := state, writeSymbol := symbol, move := .stay }
  else
    match hSelected : findRule problem.rawMachine.rules state.val symbol with
    | none =>
        { targetState := state, writeSymbol := symbol, move := .stay }
    | some selected =>
        { targetState :=
            ⟨selected.targetState, by
              change selected.targetState <
                machineStateBound problem.rawMachine
              exact rule_target_lt_machineStateBound problem.rawMachine
                selected
                (findRule_some_mem problem.rawMachine.rules state.val symbol
                  selected hSelected)⟩
          writeSymbol := selected.writeSymbol
          move := selected.move }

def movePosition {width : Nat} (position : Fin width) :
    HeadMove → Fin width
  | .stay => position
  | .left =>
      ⟨position.val - 1,
        Nat.lt_of_le_of_lt (Nat.sub_le position.val 1) position.isLt⟩
  | .right =>
      if hNext : position.val + 1 < width then
        ⟨position.val + 1, hNext⟩
      else
        position

def initialTime {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin problem.dimensions.timeCount :=
  ⟨0, problem.dimensions.timeCount_positive⟩

def finalTime {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin problem.dimensions.timeCount :=
  ⟨problem.uniformFuel, by
    change problem.uniformFuel < problem.uniformFuel + 1
    exact Nat.lt_succ_self problem.uniformFuel⟩

def currentTime {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) :
    Fin problem.dimensions.timeCount :=
  ⟨step.val, by
    change step.val < problem.uniformFuel + 1
    exact Nat.lt_trans step.isLt (Nat.lt_succ_self problem.uniformFuel)⟩

def nextTime {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) :
    Fin problem.dimensions.timeCount :=
  ⟨step.val + 1, by
    change step.val + 1 < problem.uniformFuel + 1
    exact Nat.succ_lt_succ step.isLt⟩

def controlPremises {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : BoundedClause problem.FormulaWidth :=
  [problem.stateLiteral (problem.currentTime step) state,
   problem.headLiteral (problem.currentTime step) position,
   problem.symbolLiteral (problem.currentTime step) position symbol]

def controlConstraints {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : LocalProgram problem.FormulaWidth :=
  let action := problem.localAction state symbol
  let premises := problem.controlPremises step state position symbol
  [.implication premises
      (problem.stateLiteral (problem.nextTime step) action.targetState),
   .implication premises
      (problem.headLiteral (problem.nextTime step)
        (movePosition position action.move)),
   .implication premises
      (problem.symbolLiteral (problem.nextTime step) position
        action.writeSymbol)]

def controlConstraintsAtPosition {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices problem.dimensions.stateBound).flatMap fun state =>
    tapeSymbols.flatMap fun symbol =>
      problem.controlConstraints step state position symbol

def controlTransitionProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices problem.uniformFuel).flatMap fun step =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
        fun position => problem.controlConstraintsAtPosition step position

def preservationConstraints {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition
      otherPosition : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram problem.FormulaWidth :=
  if headPosition = otherPosition then
    []
  else
    tapeSymbols.map fun symbol =>
      .implication
        [problem.headLiteral (problem.currentTime step) headPosition,
         problem.symbolLiteral (problem.currentTime step) otherPosition symbol]
        (problem.symbolLiteral (problem.nextTime step) otherPosition symbol)

def preservationAtHead {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices
    (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
      fun otherPosition =>
        problem.preservationConstraints step headPosition otherPosition

def preservationProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices problem.uniformFuel).flatMap fun step =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
        fun headPosition => problem.preservationAtHead step headPosition

def transitionProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  problem.controlTransitionProgram ++ problem.preservationProgram

/-! ### Exact source-input and variable-certificate row -/

inductive InitialCell (certificateWidth : Nat) where
  | blank
  | fixed (value : Bool)
  | certificate (index : Fin certificateWidth)
deriving DecidableEq, Repr

def fixedFrameCells (bits : BitString) :
    List (InitialCell certificateWidth) :=
  List.replicate bits.length
      (InitialCell.fixed true : InitialCell certificateWidth) ++
    (InitialCell.fixed false : InitialCell certificateWidth) ::
      bits.map InitialCell.fixed

def certificateFrameCells (certificateWidth : Nat)
    (length : Fin (certificateWidth + 1)) :
    List (InitialCell certificateWidth) :=
  List.replicate length.val
      (InitialCell.fixed true : InitialCell certificateWidth) ++
    (InitialCell.fixed false : InitialCell certificateWidth) ::
      ((finiteIndices certificateWidth).take length.val).map
        InitialCell.certificate

def pairedInitialCells (input : BitString) (certificateWidth : Nat)
    (length : Fin (certificateWidth + 1)) :
    List (InitialCell certificateWidth) :=
  fixedFrameCells input ++ certificateFrameCells certificateWidth length

def inputOnlyInitialCells (input : BitString) :
    List (InitialCell 0) :=
  input.map InitialCell.fixed

def initialCellAtOffset :
    List (InitialCell certificateWidth) → Nat → InitialCell certificateWidth
  | [], _ => .blank
  | first :: _, 0 => first
  | _ :: rest, offset + 1 => initialCellAtOffset rest offset

def initialCellAt (cells : List (InitialCell certificateWidth))
    (center position : Nat) : InitialCell certificateWidth :=
  if center ≤ position then
    initialCellAtOffset cells (position - center)
  else
    .blank

def symbolOfFixedBit : Bool → TapeSymbol
  | false => .zero
  | true => .one

theorem certificateBitWidth_eq_of_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.layout.certificateBitWidth = problem.certificateLimit := by
  unfold VerifierTableauProblem.layout
    VariableLayout.certificateBitWidth
  rw [hMode]
  exact problem.dimensions_certificateBound

theorem certificateLengthWidth_eq_of_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.layout.certificateLengthWidth = problem.certificateLimit + 1 := by
  unfold VerifierTableauProblem.layout
    VariableLayout.certificateLengthWidth
  rw [hMode]
  exact congrArg (fun value => value + 1)
    problem.dimensions_certificateBound

def pairedCertificateBitIndex {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (index : Fin problem.certificateLimit) :
    Fin problem.layout.certificateBitWidth :=
  Fin.cast (problem.certificateBitWidth_eq_of_paired hMode).symm index

def pairedCertificateLengthIndex {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    Fin problem.layout.certificateLengthWidth :=
  Fin.cast (problem.certificateLengthWidth_eq_of_paired hMode).symm length

def pairedLengthLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    BoundedLiteral problem.FormulaWidth :=
  problem.certificateLengthLiteral
    (problem.pairedCertificateLengthIndex hMode length)

def pairedBitLiteral {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (index : Fin problem.certificateLimit) :
    BoundedLiteral problem.FormulaWidth :=
  problem.certificateBitLiteral
    (problem.pairedCertificateBitIndex hMode index)

def pairedLengthVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices (problem.certificateLimit + 1)).map fun length =>
    (problem.pairedLengthLiteral hMode length).index

theorem dimensions_encodedInputLength {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.dimensions.encodedInputLength problem.tableauInputMode =
      problem.encodedInputLimit := by
  unfold VerifierTableauProblem.dimensions dimensionsAt
    Dimensions.encodedInputLength encodedInputLimit
  cases problem.tableauInputMode <;> rfl

def initialHeadPosition {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin (problem.dimensions.tapeWidth problem.tableauInputMode) :=
  ⟨problem.uniformFuel, by
    unfold Dimensions.tapeWidth
    rw [problem.dimensions_encodedInputLength,
      problem.dimensions_timeBound]
    rw [Nat.two_mul]
    have doubled : problem.uniformFuel ≤
        problem.uniformFuel + problem.uniformFuel :=
      Nat.le_add_right problem.uniformFuel problem.uniformFuel
    have withInput : problem.uniformFuel ≤
        problem.encodedInputLimit +
          (problem.uniformFuel + problem.uniformFuel) :=
      Nat.le_trans doubled
        (Nat.le_add_left
          (problem.uniformFuel + problem.uniformFuel)
          problem.encodedInputLimit)
    exact Nat.lt_succ_of_le withInput⟩

def startState {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin problem.dimensions.stateBound :=
  ⟨problem.rawMachine.startState, by
    change problem.rawMachine.startState <
      machineStateBound problem.rawMachine
    exact machine_startState_lt_bound problem.rawMachine⟩

def fixedInitialCellConstraint {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : LocalConstraint problem.FormulaWidth :=
  .require (problem.symbolLiteral problem.initialTime position symbol)

def inputOnlyCellProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram problem.FormulaWidth :=
  let cell := initialCellAt (inputOnlyInitialCells problem.input)
    problem.uniformFuel position.val
  match cell with
  | .blank => [problem.fixedInitialCellConstraint position .blank]
  | .fixed value =>
      [problem.fixedInitialCellConstraint position (symbolOfFixedBit value)]
  | .certificate index => Fin.elim0 index

def inputOnlyInitialSymbolsProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices
    (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
      problem.inputOnlyCellProgram

def pairedCellProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram problem.FormulaWidth :=
  let selectedLength := problem.pairedLengthLiteral hMode length
  let cell := initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val
  match cell with
  | .blank =>
      [.implication [selectedLength]
        (problem.symbolLiteral problem.initialTime position .blank)]
  | .fixed value =>
      [.implication [selectedLength]
        (problem.symbolLiteral problem.initialTime position
          (symbolOfFixedBit value))]
  | .certificate index =>
      let bit := problem.pairedBitLiteral hMode index
      [.implication [selectedLength, bit]
        (problem.symbolLiteral problem.initialTime position .one),
       .implication [selectedLength, bit.negate]
        (problem.symbolLiteral problem.initialTime position .zero)]

def pairedCellsForLengthProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    LocalProgram problem.FormulaWidth :=
  (finiteIndices
    (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
      (problem.pairedCellProgram hMode length)

def pairedInitialSymbolsProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    LocalProgram problem.FormulaWidth :=
  .exactlyOne (problem.pairedLengthVariables hMode) ::
    (finiteIndices (problem.certificateLimit + 1)).flatMap fun length =>
      problem.pairedCellsForLengthProgram hMode length

theorem tableauInputMode_of_inputOnly {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .inputOnly) :
    problem.tableauInputMode = .inputOnly := by
  unfold tableauInputMode inputModeOfVerifier
  rw [hMode]

theorem tableauInputMode_of_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .paired) :
    problem.tableauInputMode = .paired := by
  unfold tableauInputMode inputModeOfVerifier
  rw [hMode]

def initialSymbolsProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  match hMode : problem.verifier.program.inputMode with
  | .inputOnly => problem.inputOnlyInitialSymbolsProgram
  | .paired =>
      problem.pairedInitialSymbolsProgram
        (problem.tableauInputMode_of_paired hMode)

def initialProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  [.require (problem.stateLiteral problem.initialTime problem.startState),
   .require
    (problem.headLiteral problem.initialTime problem.initialHeadPosition)] ++
    problem.initialSymbolsProgram

/-! ### Endpoint constraint and complete whole-tableau formula -/

def acceptingState {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin problem.dimensions.stateBound :=
  ⟨problem.rawMachine.acceptState, by
    change problem.rawMachine.acceptState <
      machineStateBound problem.rawMachine
    exact machine_acceptState_lt_bound problem.rawMachine⟩

def acceptanceProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  [.require (problem.stateLiteral problem.finalTime problem.acceptingState)]

/-- A reusable structural subprogram containing every row shape, every control
update, every untouched-cell update, and the final accepting state.  The
exported whole-tableau program below additionally fixes the exact initial row. -/
def structuralProgram {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  problem.shapeProgram ++ problem.transitionProgram ++
    problem.acceptanceProgram

def structuralFormula {language : Language}
    (problem : VerifierTableauProblem language) : CNFFormula :=
  LocalProgram.toFormula problem.structuralProgram

theorem structuralFormula_wellScoped {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaWellScoped problem.structuralFormula :=
  localProgram_formula_wellScoped problem.structuralProgram

theorem structuralFormula_satisfied_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString) :
    problem.structuralFormula.Satisfied assignment ↔
      assignment.length = problem.FormulaWidth ∧
        LocalProgram.Holds problem.structuralProgram assignment :=
  LocalProgram.toFormula_satisfied_iff problem.structuralProgram assignment

theorem structuralFormula_clauseCount {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.structuralFormula.clauses.length =
      LocalProgram.clauseCount problem.structuralProgram :=
  LocalProgram.emitted_clause_count problem.structuralProgram

/-- The complete answer-independent constraint program: exact row shape,
exact initial instance/certificate encoding, all deterministic transitions,
and a designated accepting final state. -/
def program {language : Language}
    (problem : VerifierTableauProblem language) :
    LocalProgram problem.FormulaWidth :=
  problem.shapeProgram ++ problem.initialProgram ++
    problem.transitionProgram ++ problem.acceptanceProgram

def formula {language : Language}
    (problem : VerifierTableauProblem language) : CNFFormula :=
  LocalProgram.toFormula problem.program

def encodedFormula {language : Language}
    (problem : VerifierTableauProblem language) : BitString :=
  encodeCNF problem.formula

theorem formula_wellScoped {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaWellScoped problem.formula :=
  localProgram_formula_wellScoped problem.program

theorem formula_satisfied_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString) :
    problem.formula.Satisfied assignment ↔
      assignment.length = problem.FormulaWidth ∧
        LocalProgram.Holds problem.program assignment :=
  LocalProgram.toFormula_satisfied_iff problem.program assignment

theorem formula_satisfiable_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formula.Satisfiable ↔
      ∃ assignment,
        assignment.length = problem.FormulaWidth ∧
          LocalProgram.Holds problem.program assignment :=
  LocalProgram.toFormula_satisfiable_iff problem.program

theorem formula_clauseCount {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formula.clauses.length =
      LocalProgram.clauseCount problem.program :=
  LocalProgram.emitted_clause_count problem.program

theorem decode_encodedFormula {language : Language}
    (problem : VerifierTableauProblem language) :
    decodeEncodedCNF problem.encodedFormula = some problem.formula :=
  decodeEncodedCNF_canonical problem.formula

theorem encodedFormula_mem_CNFSAT_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    CNFSAT problem.encodedFormula ↔ problem.formula.Satisfiable := by
  constructor
  · intro member
    rcases member with ⟨decoded, hDecoded, hSatisfiable⟩
    rw [problem.decode_encodedFormula] at hDecoded
    have equal : decoded = problem.formula := Option.some.inj hDecoded.symm
    rw [equal] at hSatisfiable
    exact hSatisfiable
  · intro hSatisfiable
    exact ⟨problem.formula, problem.decode_encodedFormula, hSatisfiable⟩

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
