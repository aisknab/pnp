import PNP.Concrete.CookLevinBuilderInitialCellCoordinates

open PNP.Concrete PNP.Concrete.CookLevin
open VerifierTableauProblem
open BuilderInitialCellCoordinates

example : (List.range 16).map (pairedRequest 2 (⟨2, by decide⟩ : Fin 4) 3) =
    [.blank, .blank, .blank, .fixed true, .fixed true, .fixed false,
     .sourceBit 0, .sourceBit 1, .fixed true, .fixed true, .fixed false,
     .certificate ⟨0, by decide⟩, .certificate ⟨1, by decide⟩, .blank, .blank, .blank] := by decide
example : (List.range 4).map (pairedRequest 0 (⟨0, by decide⟩ : Fin 1) 0) =
    [.fixed false, .fixed false, .blank, .blank] := by decide
example : resolve [true, false] (inputOnlyRequest 2 1) = .blank := rfl
example : resolve [true, false] (inputOnlyRequest 2 2) = .fixed true := rfl
example : resolve [true, false] (inputOnlyRequest 2 3) = .fixed false := rfl
example : resolve [true, false] (inputOnlyRequest 2 4) = .blank := rfl
example : resolve ([] : BitString) (inputOnlyRequest 0 0) = .blank := rfl
example : (fixedRequest 2 2 : Request 0) = .fixed false := rfl
example : (fixedRequest 2 3 : Request 0) = .sourceBit 0 := rfl
example : (fixedRequest 2 4 : Request 0) = .sourceBit 1 := rfl
example : resolve [true, false] (fixedRequest 2 5 : Request 0) = .blank := rfl
example : certificateRequest (⟨2, by decide⟩ : Fin 4) 2 = .fixed false := rfl
example : certificateRequest (⟨2, by decide⟩ : Fin 4) 3 = .certificate ⟨0, by decide⟩ := rfl
example : certificateRequest (⟨2, by decide⟩ : Fin 4) 4 = .certificate ⟨1, by decide⟩ := rfl
example : certificateRequest (⟨2, by decide⟩ : Fin 4) 5 = .blank := rfl
example : (List.range 6).map (intervalWidth 2 2) = [1, 1, 2, 2, 1, 1] := by decide
example : DirectSlot.totalWidth 6 (fun i => intervalWidth 2 2 i.val) = 8 := by decide
example : DirectSlot.totalWidth 6 (fun i => intervalWidth 2 10 i.val) = 10 := by decide
example : DirectSlot.totalWidth 6 (fun i => intervalWidth 20 5 i.val) = 6 := by decide
example : DirectSlot.totalWidth 0 (fun i => intervalWidth 0 5 i.val) = 0 := rfl

section Universal
variable {certificateWidth : Nat} (input : BitString) (length : Fin (certificateWidth + 1))
variable (center position offset index : Nat)

example : (fixedFrameCells input : List (InitialCell certificateWidth)).length = 2 * input.length + 1 :=
  fixedFrameCells_length input
example : (certificateFrameCells certificateWidth length).length = 2 * length.val + 1 :=
  certificateFrameCells_length length
example : (pairedInitialCells input certificateWidth length).length = 2 * input.length + 2 * length.val + 2 :=
  pairedInitialCells_length input length
example : resolve input (fixedRequest input.length offset : Request certificateWidth) =
    ((fixedFrameCells input : List (InitialCell certificateWidth))[offset]?).getD .blank :=
  fixedRequest_resolve input offset
example : resolve input (certificateRequest length offset) =
    ((certificateFrameCells certificateWidth length)[offset]?).getD .blank :=
  certificateRequest_resolve input length offset
example : resolve input (pairedOffsetRequest input.length length offset) =
    ((pairedInitialCells input certificateWidth length)[offset]?).getD .blank :=
  pairedOffsetRequest_resolve input length offset
example : resolve input (pairedRequest input.length length center position) =
    initialCellAtCoordinate (pairedInitialCells input certificateWidth length) center position :=
  pairedRequest_resolve input length center position
example : resolve input (inputOnlyRequest center position) =
    initialCellAtCoordinate (inputOnlyInitialCells input) center position :=
  inputOnlyRequest_resolve input center position
example (request : Request certificateWidth) : cellWidth (resolve input request) = requestWidth request :=
  resolve_width input request
example : requestWidth (fixedRequest input.length offset : Request certificateWidth) = 1 :=
  fixedRequest_width input.length offset
example : requestWidth (certificateRequest length offset) = intervalWidth (length.val + 1) length.val offset :=
  certificateRequest_width length offset
example : requestWidth (pairedRequest input.length length center position) =
    intervalWidth (certificateStart input.length length.val center) length.val position :=
  pairedRequest_width input.length length center position
example (request : Request certificateWidth) : 1 ≤ requestWidth request ∧ requestWidth request ≤ 2 :=
  requestWidth_bounds request
example (count start width : Nat) :
    DirectSlot.totalWidth count (fun p => intervalWidth start width p.val) = count + min width (count - start) :=
  interval_totalWidth count start width
example (hOffset : offset < 2 * input.length + 1)
    (hRequest : (fixedRequest input.length offset : Request certificateWidth) = .sourceBit index) :
    index < input.length := fixedRequest_source_index_lt input.length offset index hOffset hRequest
example : certificateRequest length offset ≠ .sourceBit index := certificateRequest_ne_sourceBit length offset index
example (hRequest : pairedRequest input.length length center position = .sourceBit index) :
    index < input.length := pairedRequest_source_index_lt input.length length center position index hRequest
end Universal

section Source
variable {language : Language} (problem : VerifierTableauProblem language)
variable (length : Fin (problem.certificateLimit + 1))

example (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.pairedCellConstraintWidthDirect length position =
      intervalWidth (certificateStart problem.input.length length.val problem.uniformFuel) length.val position.val :=
  pairedCellConstraintWidthDirect_eq_interval problem length position
example : problem.pairedCellsForLengthWidthDirect length =
    problem.dimensions.tapeWidth problem.tableauInputMode +
      min length.val (problem.dimensions.tapeWidth problem.tableauInputMode -
        certificateStart problem.input.length length.val problem.uniformFuel) :=
  paired_row_width_clipped problem length
example (hMode : problem.tableauInputMode = .paired) :
    certificateStart problem.input.length length.val problem.uniformFuel + length.val ≤
      problem.dimensions.tapeWidth problem.tableauInputMode :=
  certificate_interval_within_tape problem hMode length
example (hMode : problem.tableauInputMode = .paired) :
    problem.pairedCellsForLengthWidthDirect length =
      problem.dimensions.tapeWidth problem.tableauInputMode + length.val :=
  paired_row_width problem hMode length
example : problem.pairedCellsForLengthWidthDirect length ≤
    2 * problem.dimensions.tapeWidth problem.tableauInputMode :=
  paired_row_width_le problem length
end Source
