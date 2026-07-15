/-
Copyright (c) 2026 PNP Labs.

Rectangular, answer-independent scheduling for the concrete Cook--Levin
formula.  The schedules below contain explicit empty slots.  Removing those
slots in order reproduces the already-proved local program, emitted clauses,
canonical tokens, and raw formula bits.

This file is a specification layer.  It does not interpret a schedule slot
as a constant-time operation, implement a raw finite machine, prove a
construction-runtime polynomial, or package a polynomial reduction.
-/

import PNP.Concrete.CookLevinFormulaSize

namespace PNP.Concrete

namespace CookLevin

/-! ### Generic finite padded schedules -/

namespace FormulaSchedule

/-- Emit the populated entries of a finite option schedule in their original
order. -/
def emit (schedule : List (Option α)) : List α :=
  schedule.filterMap id

/-- Append empty slots until `items` occupies the advertised bound.  When the
bound is smaller, no items are discarded; the length theorem below therefore
requires the explicit bound proof used by every concrete caller. -/
def pad (bound : Nat) (items : List α) : List (Option α) :=
  items.map some ++ List.replicate (bound - items.length) none

@[simp] theorem emit_nil : emit ([] : List (Option α)) = [] := rfl

@[simp] theorem emit_some (item : α) (rest : List (Option α)) :
    emit (some item :: rest) = item :: emit rest := rfl

@[simp] theorem emit_none (rest : List (Option α)) :
    emit (none :: rest) = emit rest := rfl

@[simp] theorem emit_append (left right : List (Option α)) :
    emit (left ++ right) = emit left ++ emit right := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      cases first <;> simp [ih]

@[simp] theorem emit_map_some (items : List α) :
    emit (items.map some) = items := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [ih]

@[simp] theorem emit_map_some_apply (items : List β) (value : β → α) :
    emit (items.map (fun item => some (value item))) = items.map value := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [ih]

@[simp] theorem emit_replicate_none (count : Nat) :
    emit (List.replicate count (none : Option α)) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

@[simp] theorem emit_pad (bound : Nat) (items : List α) :
    emit (pad bound items) = items := by
  unfold pad
  rw [emit_append, emit_map_some, emit_replicate_none, List.append_nil]

theorem pad_length {bound : Nat} {items : List α}
    (hBound : items.length ≤ bound) :
    (pad bound items).length = bound := by
  unfold pad
  rw [List.length_append, List.length_map, List.length_replicate]
  omega

@[simp] theorem emit_flatMap (items : List β)
    (schedule : β → List (Option α)) :
    emit (items.flatMap schedule) =
      items.flatMap (fun item => emit (schedule item)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      change emit (schedule first ++ rest.flatMap schedule) = _
      rw [emit_append, ih]
      rfl

theorem flatMap_option_entries (schedule : List (Option β))
    (items : β → List α) :
    schedule.flatMap (fun entry =>
      match entry with
      | none => []
      | some item => items item) =
      (emit schedule).flatMap items := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [ih]

theorem flatMap_map_apply (items : List α) (value : α → β)
    (schedule : β → List γ) :
    (items.map value).flatMap schedule =
      items.flatMap (fun item => schedule (value item)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih]

/-- A fixed-width expansion of optional entries emits exactly the expansion
of the populated source entries. -/
theorem emit_flatMap_padOptions (schedule : List (Option β)) (bound : Nat)
    (items : β → List α) :
    emit (schedule.flatMap fun entry =>
      match entry with
      | none => List.replicate bound none
      | some item => pad bound (items item)) =
      (emit schedule).flatMap items := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | none =>
          change emit (List.replicate bound none ++
              rest.flatMap fun entry =>
                match entry with
                | none => List.replicate bound none
                | some item => pad bound (items item)) = _
          rw [emit_append, emit_replicate_none, List.nil_append, ih]
          rfl
      | some item =>
          change emit (pad bound (items item) ++
              rest.flatMap fun entry =>
                match entry with
                | none => List.replicate bound none
                | some next => pad bound (items next)) = _
          rw [emit_append, emit_pad, ih]
          rfl

theorem length_flatMap_constant (items : List β)
    (schedule : β → List α) (width : Nat)
    (hWidth : ∀ item, item ∈ items → (schedule item).length = width) :
    (items.flatMap schedule).length = items.length * width :=
  flatMap_length_eq_mul items schedule width hWidth

theorem mem_emit_of_mem_some {item : α} {schedule : List (Option α)}
    (hMem : some item ∈ schedule) : item ∈ emit schedule := by
  induction schedule with
  | nil => cases hMem
  | cons first rest ih =>
      cases first with
      | none =>
          apply ih
          exact (List.mem_cons.mp hMem).resolve_left (by intro impossible; cases impossible)
      | some value =>
          rcases List.mem_cons.mp hMem with hHead | hTail
          · have hValue : value = item := Option.some.inj hHead.symm
            subst value
            exact List.Mem.head _
          · exact List.Mem.tail _ (ih hTail)

end FormulaSchedule

/-! ### Coordinate lookup for the initial row -/

namespace VerifierTableauProblem

/-- Direct list-coordinate form of the recursive initial-cell lookup. -/
def initialCellAtCoordinate (cells : List (InitialCell certificateWidth))
    (center position : Nat) : InitialCell certificateWidth :=
  if center ≤ position then
    (cells.drop (position - center)).head?.getD .blank
  else
    .blank

theorem initialCellAtOffset_eq_getD
    (cells : List (InitialCell certificateWidth)) (offset : Nat) :
    initialCellAtOffset cells offset =
      (cells.drop offset).head?.getD .blank := by
  induction cells generalizing offset with
  | nil => simp [initialCellAtOffset]
  | cons first rest ih =>
      cases offset with
      | zero => rfl
      | succ offset =>
          change initialCellAtOffset rest offset =
            (rest.drop offset).head?.getD .blank
          exact ih offset

theorem initialCellAtCoordinate_eq_initialCellAt
    (cells : List (InitialCell certificateWidth)) (center position : Nat) :
    initialCellAtCoordinate cells center position =
      initialCellAt cells center position := by
  unfold initialCellAtCoordinate initialCellAt
  split
  · rw [initialCellAtOffset_eq_getD]
  · rfl

/-! ### Constraint-slot rectangle -/

/-- The exact external variable bound used by every later rectangle. -/
def formulaVariableSlotBound {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (formulaVariableCountPolynomial problem.verifier).eval
    (BitString.size problem.input)

/-- The exact number of constraint opportunities in the rectangular
schedule. -/
def formulaConstraintSlotCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (formulaConstraintCountPolynomial problem.verifier).eval
    (BitString.size problem.input)

def scheduledShapeConstraints {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  (finiteIndices problem.dimensions.timeCount).flatMap fun time =>
    ((finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).map fun position =>
        some (problem.symbolShapeAt time position)) ++
      [some (problem.headShapeAt time), some (problem.stateShapeAt time)]

def scheduledInputOnlyCells {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  let cells :=
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).map fun position =>
        problem.fixedInitialCellConstraint position
          (initialCellSymbol (fun index : Fin 0 => Fin.elim0 index)
            (initialCellAtCoordinate
              (inputOnlyInitialCells problem.input)
              problem.uniformFuel position.val))
  FormulaSchedule.pad
    (2 * ((problem.certificateLimit + 1) *
      problem.dimensions.tapeWidth problem.tableauInputMode))
    cells

def scheduledPairedCellConstraints {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  let selectedLength := problem.pairedLengthLiteral hMode length
  let cell := initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val
  let constraints : LocalProgram problem.FormulaWidth :=
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
  FormulaSchedule.pad 2 constraints

def scheduledPairedCells {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  (finiteIndices (problem.certificateLimit + 1)).flatMap fun length =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap fun position =>
        problem.scheduledPairedCellConstraints hMode length position

def scheduledInitialConstraints {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  [some (.require
      (problem.stateLiteral problem.initialTime problem.startState)),
   some (.require
      (problem.headLiteral problem.initialTime problem.initialHeadPosition))] ++
  FormulaSchedule.pad
    (1 + 2 * ((problem.certificateLimit + 1) *
      problem.dimensions.tapeWidth problem.tableauInputMode))
    problem.initialSymbolsProgram

def scheduledControlConstraints {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  (finiteIndices problem.uniformFuel).flatMap fun step =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap fun position =>
        (finiteIndices problem.dimensions.stateBound).flatMap fun state =>
          tapeSymbols.flatMap fun symbol =>
            (problem.controlConstraints step state position symbol).map some

def scheduledPreservationConstraints {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  (finiteIndices problem.uniformFuel).flatMap fun step =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
        fun headPosition =>
          (finiteIndices
            (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
              fun otherPosition =>
                FormulaSchedule.pad 3
                  (problem.preservationConstraints step headPosition
                    otherPosition)

/-- Complete padded constraint schedule, in the exact canonical program
order. -/
def formulaConstraintSchedule {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (LocalConstraint problem.FormulaWidth)) :=
  problem.scheduledShapeConstraints ++
    problem.scheduledInitialConstraints ++
    problem.scheduledControlConstraints ++
    problem.scheduledPreservationConstraints ++
    [some (.require
      (problem.stateLiteral problem.finalTime problem.acceptingState))]

/-- Total lookup of one already-bounded constraint slot. -/
def formulaConstraintSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (slot : Fin problem.formulaConstraintSchedule.length) :
    Option (LocalConstraint problem.FormulaWidth) :=
  problem.formulaConstraintSchedule.get slot

theorem scheduledShapeConstraints_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.scheduledShapeConstraints.length =
      problem.dimensions.timeCount *
        (problem.dimensions.tapeWidth problem.tableauInputMode + 2) := by
  unfold scheduledShapeConstraints
  rw [flatMap_length_eq_mul
    (finiteIndices problem.dimensions.timeCount)
    (fun time =>
      (finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).map
          (fun position => some (problem.symbolShapeAt time position)) ++
        [some (problem.headShapeAt time), some (problem.stateShapeAt time)])
    (problem.dimensions.tapeWidth problem.tableauInputMode + 2)]
  · rw [finiteIndices_length]
  · intro time hTime
    simp [finiteIndices_length]

theorem scheduledShapeConstraints_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.scheduledShapeConstraints =
      problem.shapeProgram := by
  unfold scheduledShapeConstraints shapeProgram
  rw [FormulaSchedule.emit_flatMap]
  generalize finiteIndices problem.dimensions.timeCount = times
  induction times with
  | nil => rfl
  | cons time rest ih =>
      simp only [List.flatMap_cons]
      rw [ih]
      congr 1
      simp [rowShapeProgram, symbolShapeRow]

theorem scheduledInputOnlyCells_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.scheduledInputOnlyCells.length =
      2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold scheduledInputOnlyCells
  apply FormulaSchedule.pad_length
  simp only [List.length_map, finiteIndices_length]
  have hPositive : 0 < 2 * (problem.certificateLimit + 1) := by omega
  calc
    problem.dimensions.tapeWidth problem.tableauInputMode ≤
        (2 * (problem.certificateLimit + 1)) *
          problem.dimensions.tapeWidth problem.tableauInputMode :=
      Nat.le_mul_of_pos_left _ hPositive
    _ = 2 * ((problem.certificateLimit + 1) *
          problem.dimensions.tapeWidth problem.tableauInputMode) := by
      ac_rfl

theorem scheduledInputOnlyCells_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.scheduledInputOnlyCells =
      problem.inputOnlyInitialSymbolsProgram := by
  unfold scheduledInputOnlyCells inputOnlyInitialSymbolsProgram
  rw [FormulaSchedule.emit_pad]
  generalize finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode) = positions
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      change problem.fixedInitialCellConstraint position
          (initialCellSymbol (fun index : Fin 0 => Fin.elim0 index)
            (initialCellAtCoordinate (inputOnlyInitialCells problem.input)
              problem.uniformFuel position.val)) ::
          List.map _ rest =
        problem.inputOnlyCellProgram position ++
          rest.flatMap problem.inputOnlyCellProgram
      rw [problem.inputOnlyCellProgram_eq]
      unfold inputOnlyInitialSymbol
      rw [initialCellAtCoordinate_eq_initialCellAt]
      exact congrArg (List.cons _) ih

theorem scheduledPairedCellConstraints_length {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.scheduledPairedCellConstraints hMode length position).length = 2 := by
  unfold scheduledPairedCellConstraints
  apply FormulaSchedule.pad_length
  generalize initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  cases cell <;> simp

theorem scheduledPairedCellConstraints_emit_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    FormulaSchedule.emit
        (problem.scheduledPairedCellConstraints hMode length position) =
      problem.pairedCellProgram hMode length position := by
  unfold scheduledPairedCellConstraints pairedCellProgram
  rw [FormulaSchedule.emit_pad]
  have hCoordinate := initialCellAtCoordinate_eq_initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val
  generalize hDirect : initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  have hRecursive : initialCellAt
      (pairedInitialCells problem.input problem.certificateLimit length)
      problem.uniformFuel position.val = cell := by
    rw [← hCoordinate]
    exact hDirect
  rw [hRecursive]
  cases cell <;> rfl

theorem scheduledPairedCells_length {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.scheduledPairedCells hMode).length =
      (problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode * 2 := by
  unfold scheduledPairedCells
  rw [flatMap_length_eq_mul
    (finiteIndices (problem.certificateLimit + 1)) _
    (problem.dimensions.tapeWidth problem.tableauInputMode * 2)]
  · simp [finiteIndices_length, Nat.mul_assoc]
  · intro length hLength
    rw [flatMap_length_eq_mul
      (finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)) _ 2]
    · rw [finiteIndices_length]
    · intro position hPosition
      exact problem.scheduledPairedCellConstraints_length hMode length position

theorem scheduledPairedCells_emit_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    FormulaSchedule.emit (problem.scheduledPairedCells hMode) =
      (finiteIndices (problem.certificateLimit + 1)).flatMap fun length =>
        problem.pairedCellsForLengthProgram hMode length := by
  unfold scheduledPairedCells pairedCellsForLengthProgram
  simp [problem.scheduledPairedCellConstraints_emit_eq hMode]

theorem scheduledInitialConstraints_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.scheduledInitialConstraints.length =
      3 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold scheduledInitialConstraints
  rw [List.length_append]
  change 2 + (FormulaSchedule.pad _ problem.initialSymbolsProgram).length = _
  rw [FormulaSchedule.pad_length problem.initialSymbolsProgram_length_le]
  omega

theorem scheduledInitialConstraints_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.scheduledInitialConstraints =
      problem.initialProgram := by
  unfold scheduledInitialConstraints initialProgram
  rw [FormulaSchedule.emit_append]
  rw [FormulaSchedule.emit_pad]
  rfl

theorem scheduledControlConstraints_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.scheduledControlConstraints.length =
      9 * (problem.uniformFuel *
        problem.dimensions.tapeWidth problem.tableauInputMode *
        problem.dimensions.stateBound) := by
  have hProgram := problem.controlTransitionProgram_length
  unfold scheduledControlConstraints controlTransitionProgram
    controlConstraintsAtPosition at *
  simp only [List.length_flatMap, List.length_map]
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hProgram

theorem scheduledControlConstraints_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.scheduledControlConstraints =
      problem.controlTransitionProgram := by
  unfold scheduledControlConstraints controlTransitionProgram
    controlConstraintsAtPosition
  simp

theorem scheduledPreservationConstraints_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.scheduledPreservationConstraints.length =
      3 * (problem.uniformFuel *
        problem.dimensions.tapeWidth problem.tableauInputMode *
        problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold scheduledPreservationConstraints
  rw [flatMap_length_eq_mul (finiteIndices problem.uniformFuel) _
    (problem.dimensions.tapeWidth problem.tableauInputMode *
      (problem.dimensions.tapeWidth problem.tableauInputMode * 3))]
  · rw [finiteIndices_length]
    ac_rfl
  · intro step hStep
    rw [flatMap_length_eq_mul
      (finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)) _
      (problem.dimensions.tapeWidth problem.tableauInputMode * 3)]
    · rw [finiteIndices_length]
    · intro headPosition hHead
      rw [flatMap_length_eq_mul
        (finiteIndices
          (problem.dimensions.tapeWidth problem.tableauInputMode)) _ 3]
      · rw [finiteIndices_length]
      · intro otherPosition hOther
        apply FormulaSchedule.pad_length
        exact problem.preservationConstraints_length_le step headPosition
          otherPosition

theorem scheduledPreservationConstraints_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.scheduledPreservationConstraints =
      problem.preservationProgram := by
  unfold scheduledPreservationConstraints preservationProgram
    preservationAtHead
  simp

/-- Removing empty constraint slots yields exactly the existing canonical
whole-tableau local program. -/
theorem formulaConstraintSchedule_emit_eq_program {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.formulaConstraintSchedule =
      problem.program := by
  unfold formulaConstraintSchedule program transitionProgram acceptanceProgram
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_append, FormulaSchedule.emit_append]
  rw [problem.scheduledShapeConstraints_emit_eq,
    problem.scheduledInitialConstraints_emit_eq,
    problem.scheduledControlConstraints_emit_eq,
    problem.scheduledPreservationConstraints_emit_eq]
  simp [FormulaSchedule.emit, List.append_assoc]

theorem formulaConstraintSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaConstraintSchedule.length =
      problem.formulaConstraintSlotCount := by
  unfold formulaConstraintSchedule formulaConstraintSlotCount
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [problem.scheduledShapeConstraints_length,
    problem.scheduledInitialConstraints_length,
    problem.scheduledControlConstraints_length,
    problem.scheduledPreservationConstraints_length,
    problem.formulaConstraintCountPolynomial_eval]
  omega

/-! ### Clause, token, and raw-bit rectangles -/

def formulaClauseSlotsPerConstraint {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  1 + problem.formulaVariableSlotBound * problem.formulaVariableSlotBound

def formulaClauseSlotCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaConstraintSlotCount *
    problem.formulaClauseSlotsPerConstraint

def scheduledConstraintClauses {language : Language}
    (problem : VerifierTableauProblem language) :
    Option (LocalConstraint problem.FormulaWidth) →
      List (Option (BoundedClause problem.FormulaWidth))
  | none => List.replicate problem.formulaClauseSlotsPerConstraint none
  | some constraint =>
      FormulaSchedule.pad problem.formulaClauseSlotsPerConstraint
        (LocalConstraint.emit constraint)

/-- Every constraint opportunity receives the same clause rectangle. -/
def formulaClauseSchedule {language : Language}
    (problem : VerifierTableauProblem language) :
    List (Option (BoundedClause problem.FormulaWidth)) :=
  problem.formulaConstraintSchedule.flatMap
    problem.scheduledConstraintClauses

def formulaClauseSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (slot : Fin problem.formulaClauseSchedule.length) :
    Option (BoundedClause problem.FormulaWidth) :=
  problem.formulaClauseSchedule.get slot

def formulaTokensPerClause {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  2 + (problem.formulaVariableSlotBound + 4) *
    (problem.formulaVariableSlotBound + 1)

def scheduledClauseTokens {language : Language}
    (problem : VerifierTableauProblem language) :
    Option (BoundedClause problem.FormulaWidth) → List (Option CNFToken)
  | none => List.replicate problem.formulaTokensPerClause none
  | some clause =>
      FormulaSchedule.pad problem.formulaTokensPerClause
        (encodeClauseTokens (BoundedClause.emit clause))

/-- Padded header, padded clause rectangles, and the final formula token. -/
def formulaTokenSchedule {language : Language}
    (problem : VerifierTableauProblem language) : List (Option CNFToken) :=
  FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
      (encodeUnaryTokens problem.FormulaWidth) ++
    problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens ++
    [some .finish]

def formulaTokenSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (slot : Fin problem.formulaTokenSchedule.length) : Option CNFToken :=
  problem.formulaTokenSchedule.get slot

def scheduledTokenBits : Option CNFToken → List (Option Bool)
  | none => [none, none]
  | some token => token.bits.map some

/-- Every token opportunity receives two raw-bit slots; one final populated
slot supplies the canonical odd-length zero pad. -/
def formulaBitSchedule {language : Language}
    (problem : VerifierTableauProblem language) : List (Option Bool) :=
  problem.formulaTokenSchedule.flatMap scheduledTokenBits ++ [some false]

def formulaBitSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (slot : Fin problem.formulaBitSchedule.length) : Option Bool :=
  problem.formulaBitSchedule.get slot

/-! ### Correctness of the clause rectangle -/

theorem constraint_sizeBounded_formulaVariableSlotBound
    {language : Language} (problem : VerifierTableauProblem language)
    (constraint : LocalConstraint problem.FormulaWidth)
    (hConstraint : some constraint ∈ problem.formulaConstraintSchedule) :
    LocalConstraint.SizeBounded problem.formulaVariableSlotBound
      constraint := by
  have hEmitted : constraint ∈
      FormulaSchedule.emit problem.formulaConstraintSchedule :=
    FormulaSchedule.mem_emit_of_mem_some hConstraint
  rw [problem.formulaConstraintSchedule_emit_eq_program] at hEmitted
  have hBounded := problem.program_sizeBounded constraint hEmitted
  have hWidth : problem.FormulaWidth ≤ problem.formulaVariableSlotBound := by
    unfold formulaVariableSlotBound
    exact problem.formulaWidth_le_formulaVariableCountPolynomial
  cases constraint with
  | require literal => trivial
  | implication premises conclusion =>
      change premises.length ≤ problem.formulaVariableSlotBound + 3
      exact Nat.le_trans hBounded (Nat.add_le_add_right hWidth 3)
  | exactlyOne variables =>
      exact Nat.le_trans hBounded hWidth

theorem scheduledConstraintClauses_length {language : Language}
    (problem : VerifierTableauProblem language)
    (entry : Option (LocalConstraint problem.FormulaWidth))
    (hEntry : entry ∈ problem.formulaConstraintSchedule) :
    (problem.scheduledConstraintClauses entry).length =
      problem.formulaClauseSlotsPerConstraint := by
  cases entry with
  | none =>
      simp [scheduledConstraintClauses]
  | some constraint =>
      unfold scheduledConstraintClauses
      apply FormulaSchedule.pad_length
      rw [LocalConstraint.emit_length]
      apply LocalConstraint.clauseCount_le
      exact problem.constraint_sizeBounded_formulaVariableSlotBound
        constraint hEntry

@[simp] theorem scheduledConstraintClauses_emit {language : Language}
    (problem : VerifierTableauProblem language)
    (entry : Option (LocalConstraint problem.FormulaWidth)) :
    FormulaSchedule.emit (problem.scheduledConstraintClauses entry) =
      match entry with
      | none => []
      | some constraint => LocalConstraint.emit constraint := by
  cases entry <;> simp [scheduledConstraintClauses]

theorem scheduledConstraintClauses_flatMap_emit {language : Language}
    (problem : VerifierTableauProblem language)
    (schedule : List (Option (LocalConstraint problem.FormulaWidth))) :
    schedule.flatMap (fun entry =>
        FormulaSchedule.emit (problem.scheduledConstraintClauses entry)) =
      (FormulaSchedule.emit schedule).flatMap LocalConstraint.emit := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | none =>
          simp only [List.flatMap_cons, FormulaSchedule.emit_none]
          rw [ih]
          simp [scheduledConstraintClauses]
      | some constraint =>
          simp only [List.flatMap_cons, FormulaSchedule.emit_some]
          rw [ih]
          simp [scheduledConstraintClauses]

theorem formulaClauseSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaClauseSchedule.length = problem.formulaClauseSlotCount := by
  unfold formulaClauseSchedule formulaClauseSlotCount
  rw [flatMap_length_eq_mul problem.formulaConstraintSchedule
    problem.scheduledConstraintClauses
    problem.formulaClauseSlotsPerConstraint]
  · rw [problem.formulaConstraintSchedule_length]
  · intro entry hEntry
    exact problem.scheduledConstraintClauses_length entry hEntry

theorem localProgram_emit_eq_flatMap {width : Nat}
    (program : LocalProgram width) :
    LocalProgram.emit program = program.flatMap LocalConstraint.emit := by
  induction program with
  | nil => rfl
  | cons constraint rest ih =>
      change LocalConstraint.emit constraint ++ LocalProgram.emit rest = _
      rw [ih]
      rfl

/-- Removing empty clause slots yields exactly the bounded clauses emitted by
the scheduled canonical local program. -/
theorem formulaClauseSchedule_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.formulaClauseSchedule =
      LocalProgram.emit problem.program := by
  unfold formulaClauseSchedule
  rw [FormulaSchedule.emit_flatMap]
  rw [problem.scheduledConstraintClauses_flatMap_emit]
  rw [← localProgram_emit_eq_flatMap]
  rw [problem.formulaConstraintSchedule_emit_eq_program]

/-- Materializing the populated bounded clauses reproduces the exact clause
list already stored in the canonical formula. -/
theorem formulaClauseSchedule_emit_eq_formulaClauses
    {language : Language} (problem : VerifierTableauProblem language) :
    BoundedClauses.emit
        (FormulaSchedule.emit problem.formulaClauseSchedule) =
      problem.formula.clauses := by
  rw [problem.formulaClauseSchedule_emit_eq]
  rfl

/-! ### Correctness of the canonical token rectangle -/

theorem scheduledClauseTokens_length {language : Language}
    (problem : VerifierTableauProblem language)
    (entry : Option (BoundedClause problem.FormulaWidth))
    (hEntry : entry ∈ problem.formulaClauseSchedule) :
    (problem.scheduledClauseTokens entry).length =
      problem.formulaTokensPerClause := by
  cases entry with
  | none => simp [scheduledClauseTokens]
  | some clause =>
      unfold scheduledClauseTokens
      apply FormulaSchedule.pad_length
      rw [encodeClauseTokens_length]
      apply clauseTokenCost_le (BoundedClause.emit clause)
      · intro literal hLiteral
        exact BoundedClause.emitted_variable_lt clause literal hLiteral
      · unfold formulaVariableSlotBound
        exact problem.formulaWidth_le_formulaVariableCountPolynomial
      · have hBoundedClause : clause ∈
            FormulaSchedule.emit problem.formulaClauseSchedule :=
          FormulaSchedule.mem_emit_of_mem_some hEntry
        have hFormulaClause : BoundedClause.emit clause ∈
            problem.formula.clauses := by
          rw [← problem.formulaClauseSchedule_emit_eq_formulaClauses]
          exact List.mem_map_of_mem hBoundedClause
        have hLength := problem.formula_clause_length_le
          (BoundedClause.emit clause) hFormulaClause
        simpa [formulaVariableSlotBound] using hLength

@[simp] theorem scheduledClauseTokens_emit {language : Language}
    (problem : VerifierTableauProblem language)
    (entry : Option (BoundedClause problem.FormulaWidth)) :
    FormulaSchedule.emit (problem.scheduledClauseTokens entry) =
      match entry with
      | none => []
      | some clause => encodeClauseTokens (BoundedClause.emit clause) := by
  cases entry <;> simp [scheduledClauseTokens]

theorem scheduledClauseTokens_flatMap_emit {language : Language}
    (problem : VerifierTableauProblem language)
    (schedule : List (Option (BoundedClause problem.FormulaWidth))) :
    schedule.flatMap (fun entry =>
        FormulaSchedule.emit (problem.scheduledClauseTokens entry)) =
      (FormulaSchedule.emit schedule).flatMap
        (fun clause => encodeClauseTokens (BoundedClause.emit clause)) := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | none =>
          simp only [List.flatMap_cons, FormulaSchedule.emit_none]
          rw [ih]
          simp [scheduledClauseTokens]
      | some clause =>
          simp only [List.flatMap_cons, FormulaSchedule.emit_some]
          rw [ih]
          simp [scheduledClauseTokens]

theorem formulaClauseTokensSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (problem.formulaClauseSchedule.flatMap
      problem.scheduledClauseTokens).length =
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause := by
  rw [flatMap_length_eq_mul problem.formulaClauseSchedule
    problem.scheduledClauseTokens problem.formulaTokensPerClause]
  · rw [problem.formulaClauseSchedule_length]
  · intro entry hEntry
    exact problem.scheduledClauseTokens_length entry hEntry

theorem encodeClauseListTokens_eq_flatMap
    (clauses : List (List CNFLiteral)) :
    encodeClauseListTokens clauses = clauses.flatMap encodeClauseTokens := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      change encodeClauseTokens clause ++ encodeClauseListTokens rest = _
      rw [ih]
      rfl

theorem formulaClauseTokensSchedule_emit_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit
        (problem.formulaClauseSchedule.flatMap
          problem.scheduledClauseTokens) =
      encodeClauseListTokens problem.formula.clauses := by
  rw [FormulaSchedule.emit_flatMap]
  rw [problem.scheduledClauseTokens_flatMap_emit]
  rw [encodeClauseListTokens_eq_flatMap]
  rw [← problem.formulaClauseSchedule_emit_eq_formulaClauses]
  unfold BoundedClauses.emit
  rw [FormulaSchedule.flatMap_map_apply]

theorem formulaTokenSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSchedule.length =
      (problem.formulaVariableSlotBound + 1) +
        problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1 := by
  unfold formulaTokenSchedule
  simp only [List.length_append, List.length_cons, List.length_nil]
  have hHeader : (encodeUnaryTokens problem.FormulaWidth).length ≤
      problem.formulaVariableSlotBound + 1 := by
    rw [encodeUnaryTokens_length]
    unfold formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  rw [FormulaSchedule.pad_length hHeader,
    problem.formulaClauseTokensSchedule_length]

/-- Removing empty token slots yields the canonical token encoding of the
already-proved formula. -/
theorem formulaTokenSchedule_emit_eq_encodeCNFTokens
    {language : Language} (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.formulaTokenSchedule =
      encodeCNFTokens problem.formula := by
  unfold formulaTokenSchedule encodeCNFTokens
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad,
    problem.formulaClauseTokensSchedule_emit_eq]
  rfl

/-! ### Correctness and exact length of the raw-bit rectangle -/

theorem scheduledTokenBits_length (entry : Option CNFToken) :
    (scheduledTokenBits entry).length = 2 := by
  cases entry with
  | none => rfl
  | some token => cases token <;> rfl

theorem formulaBitSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaBitSchedule.length =
      (encodedFormulaSizePolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  unfold formulaBitSchedule
  rw [List.length_append]
  rw [flatMap_length_eq_mul problem.formulaTokenSchedule
    scheduledTokenBits 2]
  · rw [problem.formulaTokenSchedule_length]
    unfold formulaVariableSlotBound formulaClauseSlotCount
      formulaClauseSlotsPerConstraint formulaConstraintSlotCount
      formulaTokensPerClause
    rw [problem.encodedFormulaSizePolynomial_eval,
      problem.formulaClauseCountPolynomial_eval]
    simp only [formulaVariableSlotBound, List.length_cons, List.length_nil]
    omega
  · intro entry hEntry
    exact scheduledTokenBits_length entry

theorem scheduledTokenBits_emit_eq_encodeTokenPairs
    (schedule : List (Option CNFToken)) :
    FormulaSchedule.emit (schedule.flatMap scheduledTokenBits) =
      encodeTokenPairs (FormulaSchedule.emit schedule) := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | none => simp [scheduledTokenBits, ih]
      | some token =>
          cases token <;>
            simp [scheduledTokenBits, ih, CNFToken.bits, encodeTokenPairs]

/-- Removing empty raw-bit slots gives exactly the canonical odd-length CNF
encoding, including its final zero pad. -/
theorem formulaBitSchedule_emit_eq_encodedFormula
    {language : Language} (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit problem.formulaBitSchedule =
      problem.encodedFormula := by
  unfold formulaBitSchedule encodedFormula encodeCNF
  rw [FormulaSchedule.emit_append,
    scheduledTokenBits_emit_eq_encodeTokenPairs,
    problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  rfl

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
