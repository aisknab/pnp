import PNP.Concrete.CookLevinBuilderControlCoordinates

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderControlCoordinates

example (code : Fin 3) : VariableLayout.tapeSymbolCode (symbol code) = code.val := symbol_code code
example : symbol ⟨0, by decide⟩ = .blank := rfl
example : symbol ⟨1, by decide⟩ = .zero := rfl
example : symbol ⟨2, by decide⟩ = .one := rfl

section Universal
variable {language : Language} (problem : VerifierTableauProblem language)

example : 0 < StateCount problem := stateCount_positive problem
example : BuilderConstraintRegionRegisters.regionLength problem .control =
    problem.uniformFuel * (Width problem * (StateCount problem * 9)) := regionLength_eq problem
example : BuilderRegionRadixSource.radices problem .control =
    [3, 3, problem.dimensions.stateBound, problem.dimensions.tapeWidth problem.tableauInputMode] :=
  radices_eq problem

example (coordinates : Coordinates problem) : coordinates.index < slotCount problem := coordinates.index_lt
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).index = coordinate := decode_index problem coordinate h
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).step.val = coordinate / 3 / 3 / StateCount problem / Width problem := rfl
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).position.val = coordinate / 3 / 3 / StateCount problem % Width problem := rfl
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).state.val = coordinate / 3 / 3 % StateCount problem := rfl
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).readCode.val = coordinate / 3 % 3 := rfl
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    (decode problem coordinate h).conclusion.val = coordinate % 3 := rfl

example (coordinates : Coordinates problem) :
    action coordinates = problem.localAction coordinates.state (symbol coordinates.readCode) := rfl
example (coordinates : Coordinates problem) :
    problem.controlConstraintSlotDirect coordinates.index = some (some (constraint coordinates)) := slot_at coordinates
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    problem.controlConstraintSlotDirect coordinate = slot (decode problem coordinate h) :=
  decode_slot problem coordinate h
example (coordinate : Nat) (h : coordinate < slotCount problem) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderLocalConstraintPayload.values (slot (decode problem coordinate h))) =
        some (problem.controlConstraintSlotDirect coordinate) := payload_decode problem coordinate h
example (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (slot coordinates) =
      [(readRequest coordinates).index, 1, (headRequest coordinates).index, 1,
        (stateRequest coordinates).index, 1, (conclusionRequest coordinates).index, 1, 3, 3] :=
  candidate_payload coordinates
example (coordinates : Coordinates problem) :
    (BuilderLocalConstraintPayload.values (slot coordinates)).length = 10 := by
  rw [candidate_payload]; rfl
example (coordinates : Coordinates problem) :
    (stateRequest coordinates).index < problem.FormulaWidth ∧
      (headRequest coordinates).index < problem.FormulaWidth ∧
      (readRequest coordinates).index < problem.FormulaWidth ∧
      (conclusionRequest coordinates).index < problem.FormulaWidth := candidate_indices_lt coordinates

variable (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)

example : BuilderConstraintRegionSource.localCoordinate problem index .control < slotCount problem :=
  source_coordinate_lt problem index hRegion
example : BuilderConstraintRegionSource.regionSlot problem .control
    (BuilderConstraintRegionSource.localCoordinate problem index .control) =
      slot (ofSource problem index hRegion) := source_slot problem index hRegion
example : BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .control)
    (BuilderConstraintRegionSource.localCoordinate problem index .control) =
      [(ofSource problem index hRegion).conclusion.val, (ofSource problem index hRegion).readCode.val,
        (ofSource problem index hRegion).state.val, (ofSource problem index hRegion).position.val] :=
  (source_radix_coordinates problem index hRegion).1
example : BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .control)
    (BuilderConstraintRegionSource.localCoordinate problem index .control) =
      (ofSource problem index hRegion).step.val := (source_radix_coordinates problem index hRegion).2

variable (step : Fin problem.uniformFuel) (position : Fin (Width problem))
  (state : Fin (StateCount problem)) (readCode : Fin 3)

example : conclusionRequest (Coordinates.mk step position state readCode ⟨0, by decide⟩) =
    .state (problem.nextTime step) (problem.localAction state (symbol readCode)).targetState := rfl
example : conclusionRequest (Coordinates.mk step position state readCode ⟨1, by decide⟩) =
    .head (problem.nextTime step)
      (VerifierTableauProblem.movePosition position (problem.localAction state (symbol readCode)).move) := rfl
example : conclusionRequest (Coordinates.mk step position state readCode ⟨2, by decide⟩) =
    .symbol (problem.nextTime step) position (problem.localAction state (symbol readCode)).writeSymbol := rfl
end Universal

example {width : Nat} (position : Fin width) :
    (VerifierTableauProblem.movePosition position .left).val = position.val - 1 := rfl
example {width : Nat} (h : 0 < width) :
    (VerifierTableauProblem.movePosition ⟨0, h⟩ .left).val = 0 := rfl
example {width : Nat} (position : Fin width) :
    VerifierTableauProblem.movePosition position .stay = position := rfl
example {width : Nat} (position : Fin width) (h : position.val + 1 < width) :
    (VerifierTableauProblem.movePosition position .right).val = position.val + 1 := by
  simp only [VerifierTableauProblem.movePosition, dif_pos h]
example {width : Nat} (position : Fin width) (h : ¬ position.val + 1 < width) :
    VerifierTableauProblem.movePosition position .right = position := by
  simp only [VerifierTableauProblem.movePosition, dif_neg h]
