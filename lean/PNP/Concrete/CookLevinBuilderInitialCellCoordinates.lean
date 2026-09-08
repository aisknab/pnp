/-
Copyright (c) 2026 PNP Labs.

Arithmetic requests for every canonical initial-row cell. The request
contains a source index, not a supplied source bit. Its resolution is an
execution specification, not a finite-machine implementation. Exact paired
cell widths preserve the existing compressed one/two-constraint schedule.
Physical selection, reader binding and complete payload construction remain
separate obligations of the all-input builder.
-/

import PNP.Concrete.CookLevinFormulaCursor

namespace PNP.Concrete.CookLevin.BuilderInitialCellCoordinates

open VerifierTableauProblem

inductive Request (certificateWidth : Nat) where
  | blank
  | fixed (value : Bool)
  | sourceBit (index : Nat)
  | certificate (index : Fin certificateWidth)
  deriving DecidableEq, Repr

/-- Resolve only for the semantic endpoint; runtime must read the actual source. -/
def resolve (input : BitString) : Request certificateWidth → InitialCell certificateWidth
  | .blank => .blank
  | .fixed value => .fixed value
  | .sourceBit index => ((input[index]?).map InitialCell.fixed).getD .blank
  | .certificate index => .certificate index

def fixedRequest (inputLength offset : Nat) : Request certificateWidth :=
  if offset < inputLength then .fixed true
  else if offset = inputLength then .fixed false
  else .sourceBit (offset - (inputLength + 1))

def certificateRequest (length : Fin (certificateWidth + 1)) (offset : Nat) : Request certificateWidth :=
  if offset < length.val then .fixed true
  else if offset = length.val then .fixed false
  else if hIndex : offset - (length.val + 1) < length.val then
    .certificate ⟨offset - (length.val + 1), by have h := length.isLt; omega⟩
  else .blank

def pairedOffsetRequest (inputLength : Nat) (length : Fin (certificateWidth + 1)) (offset : Nat) :
    Request certificateWidth :=
  if offset < 2 * inputLength + 1 then fixedRequest inputLength offset
  else certificateRequest length (offset - (2 * inputLength + 1))

def pairedRequest (inputLength : Nat) (length : Fin (certificateWidth + 1)) (center position : Nat) :
    Request certificateWidth :=
  if center ≤ position then pairedOffsetRequest inputLength length (position - center) else .blank

def inputOnlyRequest (center position : Nat) : Request 0 :=
  if center ≤ position then .sourceBit (position - center) else .blank

private theorem head_drop_eq_getElem? (values : List α) (index : Nat) :
    (values.drop index).head? = values[index]? := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons value rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem fixedFrameCells_length (input : BitString) :
    (fixedFrameCells input : List (InitialCell certificateWidth)).length = 2 * input.length + 1 := by
  simp only [fixedFrameCells, List.length_append, List.length_replicate, List.length_cons, List.length_map]
  omega

theorem certificateFrameCells_length (length : Fin (certificateWidth + 1)) :
    (certificateFrameCells certificateWidth length).length = 2 * length.val + 1 := by
  have hLength : length.val ≤ certificateWidth := by have h := length.isLt; omega
  simp only [certificateFrameCells, List.length_append, List.length_replicate, List.length_cons,
    List.length_map, List.length_take, finiteIndices_length, Nat.min_eq_left hLength]
  omega

theorem pairedInitialCells_length (input : BitString) (length : Fin (certificateWidth + 1)) :
    (pairedInitialCells input certificateWidth length).length = 2 * input.length + 2 * length.val + 2 := by
  simp only [pairedInitialCells, List.length_append, fixedFrameCells_length, certificateFrameCells_length]
  omega

theorem fixedRequest_resolve (input : BitString) (offset : Nat) :
    resolve input (fixedRequest input.length offset : Request certificateWidth) =
      ((fixedFrameCells input : List (InitialCell certificateWidth))[offset]?).getD .blank := by
  unfold fixedRequest fixedFrameCells
  rw [List.getElem?_append, List.length_replicate]
  by_cases hPrefix : offset < input.length
  · simp only [List.getElem?_replicate, if_pos hPrefix, Option.getD_some, resolve]
  · by_cases hDelimiter : offset = input.length
    · subst offset
      simp only [Nat.lt_irrefl, if_false, ite_true, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some, resolve]
    · have hOffset : offset - input.length = (offset - (input.length + 1)) + 1 := by omega
      simp only [if_neg hPrefix, if_neg hDelimiter, hOffset, List.getElem?_cons_succ,
        List.getElem?_map, resolve]

theorem certificateRequest_resolve (input : BitString) (length : Fin (certificateWidth + 1)) (offset : Nat) :
    resolve input (certificateRequest length offset) =
      ((certificateFrameCells certificateWidth length)[offset]?).getD .blank := by
  unfold certificateRequest certificateFrameCells
  rw [List.getElem?_append, List.length_replicate]
  by_cases hPrefix : offset < length.val
  · simp only [List.getElem?_replicate, if_pos hPrefix, Option.getD_some, resolve]
  · by_cases hDelimiter : offset = length.val
    · subst offset
      simp only [Nat.lt_irrefl, if_false, ite_true, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some, resolve]
    · have hOffset : offset - length.val = (offset - (length.val + 1)) + 1 := by omega
      simp only [if_neg hPrefix, if_neg hDelimiter, hOffset, List.getElem?_cons_succ, List.getElem?_map]
      by_cases hIndex : offset - (length.val + 1) < length.val
      · have hWidth : offset - (length.val + 1) < certificateWidth := by have h := length.isLt; omega
        simp only [dif_pos hIndex, resolve, List.getElem?_take_of_lt hIndex,
          DirectSlot.finiteIndices_eq_ofFn, List.getElem?_ofFn, dif_pos hWidth,
          Option.map_some, Option.getD_some]
      · have hOutside : ((finiteIndices certificateWidth).take length.val).length ≤ offset - (length.val + 1) := by
          simp only [List.length_take, finiteIndices_length]
          omega
        simp only [dif_neg hIndex, resolve, List.getElem?_eq_none hOutside, Option.map_none, Option.getD_none]

theorem pairedOffsetRequest_resolve (input : BitString) (length : Fin (certificateWidth + 1)) (offset : Nat) :
    resolve input (pairedOffsetRequest input.length length offset) =
      ((pairedInitialCells input certificateWidth length)[offset]?).getD .blank := by
  unfold pairedOffsetRequest pairedInitialCells
  rw [List.getElem?_append, fixedFrameCells_length]
  by_cases hFirst : offset < 2 * input.length + 1
  · simp only [if_pos hFirst]
    exact fixedRequest_resolve input offset
  · simp only [if_neg hFirst]
    exact certificateRequest_resolve input length _

theorem pairedRequest_resolve (input : BitString) (length : Fin (certificateWidth + 1)) (center position : Nat) :
    resolve input (pairedRequest input.length length center position) =
      initialCellAtCoordinate (pairedInitialCells input certificateWidth length) center position := by
  by_cases hPosition : center ≤ position
  · simp only [pairedRequest, initialCellAtCoordinate, if_pos hPosition, head_drop_eq_getElem?]
    exact pairedOffsetRequest_resolve input length _
  · simp only [pairedRequest, initialCellAtCoordinate, if_neg hPosition, resolve]

theorem inputOnlyRequest_resolve (input : BitString) (center position : Nat) :
    resolve input (inputOnlyRequest center position) =
      initialCellAtCoordinate (inputOnlyInitialCells input) center position := by
  by_cases hPosition : center ≤ position
  · simp only [inputOnlyRequest, initialCellAtCoordinate, if_pos hPosition, head_drop_eq_getElem?,
      inputOnlyInitialCells, List.getElem?_map, resolve]
  · simp only [inputOnlyRequest, initialCellAtCoordinate, if_neg hPosition, resolve]

def requestWidth : Request certificateWidth → Nat
  | .certificate _ => 2
  | _ => 1
def cellWidth : InitialCell certificateWidth → Nat
  | .certificate _ => 2
  | _ => 1

theorem resolve_width (input : BitString) (request : Request certificateWidth) :
    cellWidth (resolve input request) = requestWidth request := by
  cases request with
  | blank => rfl
  | fixed value => rfl
  | certificate index => rfl
  | sourceBit index =>
      cases hBit : input[index]? with
      | none => simp only [resolve, hBit, Option.map_none, Option.getD_none, cellWidth, requestWidth]
      | some value => simp only [resolve, hBit, Option.map_some, Option.getD_some, cellWidth, requestWidth]

theorem fixedRequest_width (inputLength offset : Nat) :
    requestWidth (fixedRequest inputLength offset : Request certificateWidth) = 1 := by
  unfold fixedRequest
  split
  · rfl
  · split <;> rfl

/-- The doubled part of a compressed cell block. -/
def intervalWidth (start length position : Nat) : Nat :=
  if start ≤ position ∧ position < start + length then 2 else 1

def certificateStart (inputLength length center : Nat) : Nat :=
  center + 2 * inputLength + length + 2

theorem certificateRequest_width (length : Fin (certificateWidth + 1)) (offset : Nat) :
    requestWidth (certificateRequest length offset) = intervalWidth (length.val + 1) length.val offset := by
  by_cases hPrefix : offset < length.val
  · have hOutside : ¬ (length.val + 1 ≤ offset ∧ offset < length.val + 1 + length.val) := by
      intro h
      omega
    simp only [certificateRequest, if_pos hPrefix, requestWidth, intervalWidth, if_neg hOutside]
  · by_cases hDelimiter : offset = length.val
    · have hOutside : ¬ (length.val + 1 ≤ offset ∧ offset < length.val + 1 + length.val) := by
        intro h
        omega
      simp only [certificateRequest, if_neg hPrefix, if_pos hDelimiter, requestWidth, intervalWidth, if_neg hOutside]
    · by_cases hIndex : offset - (length.val + 1) < length.val
      · have hInside : length.val + 1 ≤ offset ∧ offset < length.val + 1 + length.val := by
          constructor <;> omega
        simp only [certificateRequest, if_neg hPrefix, if_neg hDelimiter, dif_pos hIndex,
          requestWidth, intervalWidth, if_pos hInside]
      · have hOutside : ¬ (length.val + 1 ≤ offset ∧ offset < length.val + 1 + length.val) := by
          intro h
          omega
        simp only [certificateRequest, if_neg hPrefix, if_neg hDelimiter, dif_neg hIndex,
          requestWidth, intervalWidth, if_neg hOutside]

theorem pairedRequest_width (inputLength : Nat) (length : Fin (certificateWidth + 1)) (center position : Nat) :
    requestWidth (pairedRequest inputLength length center position) =
      intervalWidth (certificateStart inputLength length.val center) length.val position := by
  by_cases hPosition : center ≤ position
  · simp only [pairedRequest, if_pos hPosition, pairedOffsetRequest]
    by_cases hFirst : position - center < 2 * inputLength + 1
    · have hOutside : ¬ (certificateStart inputLength length.val center ≤ position ∧
          position < certificateStart inputLength length.val center + length.val) := by
        simp only [certificateStart]
        intro h
        omega
      simp only [if_pos hFirst, fixedRequest_width, intervalWidth, if_neg hOutside]
    · simp only [if_neg hFirst, certificateRequest_width, intervalWidth]
      have hZone :
          (length.val + 1 ≤ position - center - (2 * inputLength + 1) ∧
            position - center - (2 * inputLength + 1) < length.val + 1 + length.val) ↔
          (certificateStart inputLength length.val center ≤ position ∧
            position < certificateStart inputLength length.val center + length.val) := by
        simp only [certificateStart]
        constructor <;> intro h <;> constructor <;> omega
      simp only [hZone]
  · have hOutside : ¬ (certificateStart inputLength length.val center ≤ position ∧
        position < certificateStart inputLength length.val center + length.val) := by
      simp only [certificateStart]
      intro h
      omega
    simp only [pairedRequest, if_neg hPosition, requestWidth, intervalWidth, if_neg hOutside]

theorem requestWidth_bounds (request : Request certificateWidth) : 1 ≤ requestWidth request ∧ requestWidth request ≤ 2 := by
  cases request <;> simp only [requestWidth] <;> constructor <;> decide

theorem pairedCellConstraintWidthDirect_eq_interval {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.pairedCellConstraintWidthDirect length position =
      intervalWidth (certificateStart problem.input.length length.val problem.uniformFuel) length.val position.val := by
  have hResolved :
      cellWidth (initialCellAtCoordinate (pairedInitialCells problem.input problem.certificateLimit length)
        problem.uniformFuel position.val) =
      intervalWidth (certificateStart problem.input.length length.val problem.uniformFuel) length.val position.val := by
    rw [← pairedRequest_resolve, resolve_width, pairedRequest_width]
  unfold pairedCellConstraintWidthDirect
  cases hCell : initialCellAtCoordinate (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val <;> simpa only [hCell, cellWidth] using hResolved


private theorem interval_zero_length (start position : Nat) : intervalWidth start 0 position = 1 := by
  have hEmpty : ¬ (start ≤ position ∧ position < start + 0) := by intro h; omega
  exact if_neg hEmpty

private theorem interval_start_succ_zero (start length : Nat) : intervalWidth (start + 1) length 0 = 1 := by
  have hEmpty : ¬ (start + 1 ≤ 0 ∧ 0 < start + 1 + length) := by intro h; omega
  exact if_neg hEmpty

private theorem interval_start_succ_succ (start length position : Nat) :
    intervalWidth (start + 1) length (position + 1) = intervalWidth start length position := by
  unfold intervalWidth
  have hZone : (start + 1 ≤ position + 1 ∧ position + 1 < start + 1 + length) ↔
      (start ≤ position ∧ position < start + length) := by
    constructor <;> intro h <;> constructor <;> omega
  simp only [hZone]

private theorem interval_length_succ_zero (length : Nat) : intervalWidth 0 (length + 1) 0 = 2 := by
  have hInside : 0 ≤ 0 ∧ 0 < 0 + (length + 1) := by constructor <;> omega
  exact if_pos hInside

private theorem interval_length_succ_succ (length position : Nat) :
    intervalWidth 0 (length + 1) (position + 1) = intervalWidth 0 length position := by
  unfold intervalWidth
  have hZone : (0 ≤ position + 1 ∧ position + 1 < 0 + (length + 1)) ↔
      (0 ≤ position ∧ position < 0 + length) := by
    constructor <;> intro h <;> constructor <;> omega
  simp only [hZone]

/-- Exact clipped count, including empty windows and intervals outside the tape. -/
theorem interval_totalWidth (count start length : Nat) :
    DirectSlot.totalWidth count (fun position => intervalWidth start length position.val) =
      count + min length (count - start) := by
  induction count generalizing start length with
  | zero =>
      simp only [DirectSlot.totalWidth, Nat.zero_sub, Nat.min_zero, Nat.zero_add]
  | succ count ih =>
      cases start with
      | zero =>
          cases length with
          | zero =>
              have hTail :
                  (fun position : Fin count => intervalWidth 0 0 position.succ.val) =
                    (fun position : Fin count => intervalWidth 0 0 position.val) := by
                funext position
                rw [interval_zero_length, interval_zero_length]
              rw [DirectSlot.totalWidth, interval_zero_length, hTail, ih]
              omega
          | succ length =>
              have hTail :
                  (fun position : Fin count => intervalWidth 0 (length + 1) position.succ.val) =
                    (fun position : Fin count => intervalWidth 0 length position.val) := by
                funext position
                exact interval_length_succ_succ length position.val
              rw [DirectSlot.totalWidth, interval_length_succ_zero, hTail, ih]
              omega
      | succ start =>
          have hTail :
              (fun position : Fin count => intervalWidth (start + 1) length position.succ.val) =
                (fun position : Fin count => intervalWidth start length position.val) := by
            funext position
            exact interval_start_succ_succ start length position.val
          rw [DirectSlot.totalWidth, interval_start_succ_zero, hTail, ih]
          omega

theorem paired_row_width_clipped {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) :
    problem.pairedCellsForLengthWidthDirect length =
      problem.dimensions.tapeWidth problem.tableauInputMode +
        min length.val (problem.dimensions.tapeWidth problem.tableauInputMode -
          certificateStart problem.input.length length.val problem.uniformFuel) := by
  unfold pairedCellsForLengthWidthDirect
  have hWidths :
      (fun position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode) =>
        problem.pairedCellConstraintWidthDirect length position) =
      (fun position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode) =>
        intervalWidth (certificateStart problem.input.length length.val problem.uniformFuel) length.val position.val) := by
    funext position
    exact pairedCellConstraintWidthDirect_eq_interval problem length position
  rw [hWidths, interval_totalWidth]

theorem certificate_interval_within_tape {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1)) :
    certificateStart problem.input.length length.val problem.uniformFuel + length.val ≤
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  have hLength : length.val ≤ problem.certificateLimit := by have h := length.isLt; omega
  simp only [certificateStart, Dimensions.tapeWidth, hMode, Dimensions.encodedInputLength,
    dimensions_inputLength, dimensions_certificateBound, dimensions_timeBound, BitString.size]
  omega

/-- One canonical paired row has one constraint per tape cell plus one per certificate bit. -/
theorem paired_row_width {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1)) :
    problem.pairedCellsForLengthWidthDirect length =
      problem.dimensions.tapeWidth problem.tableauInputMode + length.val := by
  have hInside := certificate_interval_within_tape problem hMode length
  rw [paired_row_width_clipped]
  have hRoom : length.val ≤ problem.dimensions.tapeWidth problem.tableauInputMode -
      certificateStart problem.input.length length.val problem.uniformFuel := by omega
  rw [Nat.min_eq_left hRoom]

theorem paired_row_width_le {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) :
    problem.pairedCellsForLengthWidthDirect length ≤
      2 * problem.dimensions.tapeWidth problem.tableauInputMode := by
  rw [paired_row_width_clipped]
  omega

theorem fixedRequest_source_index_lt (inputLength offset index : Nat)
    (hOffset : offset < 2 * inputLength + 1)
    (hRequest : (fixedRequest inputLength offset : Request certificateWidth) = .sourceBit index) :
    index < inputLength := by
  unfold fixedRequest at hRequest
  split at hRequest
  · cases hRequest
  · split at hRequest
    · cases hRequest
    · have hIndex := Request.sourceBit.inj hRequest
      omega

theorem certificateRequest_ne_sourceBit (length : Fin (certificateWidth + 1)) (offset index : Nat) :
    certificateRequest length offset ≠ .sourceBit index := by
  unfold certificateRequest
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h

theorem pairedRequest_source_index_lt (inputLength : Nat) (length : Fin (certificateWidth + 1))
    (center position index : Nat)
    (hRequest : pairedRequest inputLength length center position = .sourceBit index) :
    index < inputLength := by
  unfold pairedRequest at hRequest
  split at hRequest
  · unfold pairedOffsetRequest at hRequest
    split at hRequest
    · rename_i hFirst
      exact fixedRequest_source_index_lt inputLength _ index hFirst hRequest
    · exact False.elim (certificateRequest_ne_sourceBit length _ index hRequest)
  · cases hRequest

end PNP.Concrete.CookLevin.BuilderInitialCellCoordinates
