/-
Copyright (c) 2026 PNP Labs.
All-coordinate canonical preservation contracts. Finite symbol checks are codec
regressions only; they do not replace the arbitrary-coordinate theorems.
-/
import PNP.Concrete.CookLevinBuilderPreservationCoordinates

namespace PNP.Concrete.CookLevin.BuilderPreservationCoordinates.Regression

example : symbol ⟨0, by decide⟩ = .blank := rfl
example : symbol ⟨1, by decide⟩ = .zero := rfl
example : symbol ⟨2, by decide⟩ = .one := rfl
example (code : Fin 3) : VariableLayout.tapeSymbolCode (symbol code) = code.val := symbol_code code
example (code : Fin 3) : tapeSymbols[code.val]? = some (symbol code) := symbol_lookup code

variable {language : Language} (problem : VerifierTableauProblem language)

example : BuilderConstraintRegionRegisters.regionLength problem .preservation = slotCount problem :=
  regionLength_eq problem
example : BuilderRegionRadixSource.radices problem .preservation = [3, Width problem, Width problem] :=
  radices_eq problem
example (coordinates : Coordinates problem) : coordinates.index < slotCount problem := coordinates.index_lt
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).index = coordinate := decode_index problem coordinate hCoordinate
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).step.val = coordinate / 3 / Width problem / Width problem := rfl
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).head.val = coordinate / 3 / Width problem % Width problem := rfl
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).other.val = coordinate / 3 % Width problem := rfl
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).code.val = coordinate % 3 := rfl
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    problem.preservationConstraintSlotDirect coordinate = slot (decode problem coordinate hCoordinate) :=
  decode_slot problem coordinate hCoordinate
example (coordinates : Coordinates problem) :
    problem.preservationConstraintSlotDirect coordinates.index = slot coordinates := slot_at coordinates
example (coordinates : Coordinates problem) (hEqual : coordinates.head = coordinates.other) :
    slot coordinates = some none := slot_diagonal coordinates hEqual
example (coordinates : Coordinates problem) (hDifferent : coordinates.head ≠ coordinates.other) :
    slot coordinates = some (some (constraint coordinates)) := slot_off_diagonal coordinates hDifferent
example (coordinates : Coordinates problem) :
    constraint coordinates = .implication
      [problem.headLiteral (problem.currentTime coordinates.step) coordinates.head,
        problem.symbolLiteral (problem.currentTime coordinates.step) coordinates.other (symbol coordinates.code)]
      (problem.symbolLiteral (problem.nextTime coordinates.step) coordinates.other (symbol coordinates.code)) := rfl
example (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (some (some (constraint coordinates))) =
      [(oldSymbolRequest coordinates).index, 1, (headRequest coordinates).index, 1,
        (newSymbolRequest coordinates).index, 1, 2, 3] := candidate_payload coordinates
example (coordinates : Coordinates problem) :
    (headRequest coordinates).index < problem.FormulaWidth ∧
      (oldSymbolRequest coordinates).index < problem.FormulaWidth ∧
        (newSymbolRequest coordinates).index < problem.FormulaWidth := candidate_indices_lt coordinates
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderLocalConstraintPayload.values (slot (decode problem coordinate hCoordinate))) =
        some (problem.preservationConstraintSlotDirect coordinate) := payload_decode problem coordinate hCoordinate
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem)
    (hDiagonal : (decode problem coordinate hCoordinate).head = (decode problem coordinate hCoordinate).other) :
    BuilderLocalConstraintPayload.values (slot (decode problem coordinate hCoordinate)) = [1] := by
  rw [slot_diagonal _ hDiagonal]
  rfl
example (coordinate : Nat) (hCoordinate : coordinate < slotCount problem)
    (hDifferent : (decode problem coordinate hCoordinate).head ≠ (decode problem coordinate hCoordinate).other) :
    BuilderLocalConstraintPayload.values (slot (decode problem coordinate hCoordinate)) =
      [(oldSymbolRequest (decode problem coordinate hCoordinate)).index, 1,
        (headRequest (decode problem coordinate hCoordinate)).index, 1,
        (newSymbolRequest (decode problem coordinate hCoordinate)).index, 1, 2, 3] := by
  rw [slot_off_diagonal _ hDifferent, candidate_payload]
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderConstraintRegionSource.localCoordinate problem index .preservation < slotCount problem :=
  source_coordinate_lt problem index hRegion
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderConstraintRegionSource.regionSlot problem .preservation
      (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
        slot (ofSource problem index hRegion) := source_slot problem index hRegion
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .preservation)
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
      [(ofSource problem index hRegion).code.val, (ofSource problem index hRegion).other.val,
        (ofSource problem index hRegion).head.val] :=
  (source_radix_coordinates problem index hRegion).1
example (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .preservation)
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
      (ofSource problem index hRegion).step.val :=
  (source_radix_coordinates problem index hRegion).2

end PNP.Concrete.CookLevin.BuilderPreservationCoordinates.Regression
