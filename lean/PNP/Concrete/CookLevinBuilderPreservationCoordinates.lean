/-
Copyright (c) 2026 PNP Labs.

Canonical preservation coordinates from the existing source-derived radix frame.
Every valid coordinate is covered, including all three padded diagonal slots.
Typed literals and the lossless payload specification agree with the unchanged
canonical formula. The specifications here do not supply runtime answers:
physical payload construction and diagonal dispatch remain separate obligations.
-/

import PNP.Concrete.CookLevinBuilderLiteralArgumentSource
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderPreservationCoordinates

abbrev Width {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.dimensions.tapeWidth problem.tableauInputMode

def slotCount {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.uniformFuel * (Width problem * (Width problem * 3))

theorem regionLength_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionRegisters.regionLength problem .preservation = slotCount problem := by
  have hFuel : (formulaFuelPolynomial problem.verifier).eval problem.input.length = problem.uniformFuel :=
    problem.formulaFuelPolynomial_eval
  have hWidth : (formulaTapeWidthPolynomial problem.verifier).eval problem.input.length = Width problem :=
    problem.formulaTapeWidthPolynomial_eval
  simp only [BuilderConstraintRegionRegisters.regionLength,
    BuilderConstraintRegionRegisters.lengthPolynomial,
    BuilderConstraintRegionRegisters.termPolynomial, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, hFuel, hWidth, slotCount]
  ac_rfl

theorem radices_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRegionRadixSource.radices problem .preservation = [3, Width problem, Width problem] := by
  simp only [BuilderRegionRadixSource.radices, BuilderRegionRadixSource.radixFields,
    List.map_cons, List.map_nil, BuilderRegionRadixSource.fieldValue_three,
    BuilderRegionRadixSource.fieldValue_tapeWidth, Width]

/-- The ordering is the canonical `tapeSymbols` ordering, not a new codec. -/
def symbol (code : Fin 3) : TapeSymbol :=
  match code.val with
  | 0 => .blank
  | 1 => .zero
  | _ => .one

theorem symbol_code (code : Fin 3) :
    VariableLayout.tapeSymbolCode (symbol code) = code.val := by
  decide +revert

theorem symbol_lookup (code : Fin 3) : tapeSymbols[code.val]? = some (symbol code) := by
  decide +revert

structure Coordinates {language : Language} (problem : VerifierTableauProblem language) where
  step : Fin problem.uniformFuel
  head : Fin (Width problem)
  other : Fin (Width problem)
  code : Fin 3

def Coordinates.index {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat :=
  coordinates.code.val + 3 * (coordinates.other.val +
    Width problem * (coordinates.head.val + Width problem * coordinates.step.val))

private theorem rectangle_index_lt (count width : Nat) (outer : Fin count) (inner : Fin width) :
    outer.val * width + inner.val < count * width := by
  have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt outer.isLt)
  rw [Nat.succ_mul] at h
  have hInner := inner.isLt
  omega

private theorem rectangle_at (count width : Nat)
    (block : Fin count → Nat → Option α) (outer : Fin count) (inner : Nat) (hInner : inner < width) :
    DirectSlot.rectangle count width block (outer.val * width + inner) = block outer inner := by
  induction count with
  | zero => exact Fin.elim0 outer
  | succ count ih =>
      rcases outer with ⟨outer, hOuter⟩
      cases outer with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, DirectSlot.rectangle, DirectSlot.flatFinite,
            if_pos hInner]
      | succ outer =>
          have hNot : ¬ (outer + 1) * width + inner < width := by
            rw [Nat.succ_mul]
            omega
          rw [DirectSlot.rectangle, DirectSlot.flatFinite, if_neg hNot]
          have hSub : (outer + 1) * width + inner - width = outer * width + inner := by
            rw [Nat.succ_mul]
            omega
          change DirectSlot.rectangle count width (fun i => block i.succ)
            ((outer + 1) * width + inner - width) = _
          rw [hSub]
          exact ih (fun i => block i.succ) ⟨outer, by omega⟩

private theorem index_rectangle {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    coordinates.index = coordinates.step.val * (Width problem * (Width problem * 3)) +
      (coordinates.head.val * (Width problem * 3) +
        (coordinates.other.val * 3 + coordinates.code.val)) := by
  simp only [Coordinates.index, Nat.mul_add]
  ac_rfl

theorem Coordinates.index_lt {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : coordinates.index < slotCount problem := by
  have hOther := rectangle_index_lt (Width problem) 3 coordinates.other coordinates.code
  have hHead := rectangle_index_lt (Width problem) (Width problem * 3) coordinates.head
    ⟨coordinates.other.val * 3 + coordinates.code.val, hOther⟩
  have hTime := rectangle_index_lt problem.uniformFuel (Width problem * (Width problem * 3))
    coordinates.step ⟨coordinates.head.val * (Width problem * 3) +
      (coordinates.other.val * 3 + coordinates.code.val), hHead⟩
  rw [index_rectangle]
  exact hTime

private theorem step_lt {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    coordinate / 3 / Width problem / Width problem < problem.uniformFuel := by
  have hWidth := problem.dimensions.tapeWidth_positive problem.tableauInputMode
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide : 0 < 3) (Nat.mul_pos hWidth hWidth))).2
  simpa only [slotCount, Width, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hCoordinate

/-- All values are quotient/remainder projections of the one local coordinate. -/
def decode {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) : Coordinates problem :=
  { step := ⟨coordinate / 3 / Width problem / Width problem, step_lt problem coordinate hCoordinate⟩
    head := ⟨coordinate / 3 / Width problem % Width problem,
      Nat.mod_lt _ (problem.dimensions.tapeWidth_positive problem.tableauInputMode)⟩
    other := ⟨coordinate / 3 % Width problem,
      Nat.mod_lt _ (problem.dimensions.tapeWidth_positive problem.tableauInputMode)⟩
    code := ⟨coordinate % 3, Nat.mod_lt _ (by decide)⟩ }

theorem decode_index {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).index = coordinate := by
  have h := BuilderRegionRadixDecoder.reconstruct_eq [3, Width problem, Width problem] coordinate
  simpa only [decode, Coordinates.index, BuilderRegionRadixDecoder.reconstruct,
    BuilderRegionRadixDecoder.digits, BuilderRegionRadixDecoder.finalQuotient] using h

def headRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .head (problem.currentTime coordinates.step) coordinates.head

def oldSymbolRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .symbol (problem.currentTime coordinates.step) coordinates.other (symbol coordinates.code)

def newSymbolRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .symbol (problem.nextTime coordinates.step) coordinates.other (symbol coordinates.code)

def constraint {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : LocalConstraint problem.FormulaWidth :=
  .implication
    [problem.headLiteral (problem.currentTime coordinates.step) coordinates.head,
      problem.symbolLiteral (problem.currentTime coordinates.step) coordinates.other (symbol coordinates.code)]
    (problem.symbolLiteral (problem.nextTime coordinates.step) coordinates.other (symbol coordinates.code))

def slot {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLocalConstraintPayload.Slot problem.FormulaWidth :=
  if coordinates.head = coordinates.other then some none else some (some (constraint coordinates))

/-- Literal order and signs are exactly those of the canonical implication. -/
theorem candidate_payload {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (some (some (constraint coordinates))) =
      [(oldSymbolRequest coordinates).index, 1, (headRequest coordinates).index, 1,
        (newSymbolRequest coordinates).index, 1, 2, 3] := by
  rfl

theorem candidate_indices_lt {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    (headRequest coordinates).index < problem.FormulaWidth ∧
      (oldSymbolRequest coordinates).index < problem.FormulaWidth ∧
        (newSymbolRequest coordinates).index < problem.FormulaWidth :=
  ⟨(headRequest coordinates).index_lt, (oldSymbolRequest coordinates).index_lt,
    (newSymbolRequest coordinates).index_lt⟩

theorem slot_at {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    problem.preservationConstraintSlotDirect coordinates.index = slot coordinates := by
  have hOther := rectangle_index_lt (Width problem) 3 coordinates.other coordinates.code
  have hHead := rectangle_index_lt (Width problem) (Width problem * 3) coordinates.head
    ⟨coordinates.other.val * 3 + coordinates.code.val, hOther⟩
  rw [index_rectangle]
  unfold VerifierTableauProblem.preservationConstraintSlotDirect
  rw [rectangle_at _ _ _ coordinates.step _ hHead]
  unfold VerifierTableauProblem.preservationHeadBlockSlotDirect
  rw [rectangle_at _ _ _ coordinates.head _ hOther]
  unfold VerifierTableauProblem.preservationOtherBlockSlotDirect
  rw [rectangle_at _ _ _ coordinates.other _ coordinates.code.isLt]
  simp only [VerifierTableauProblem.preservationLocalSlotDirect, DirectSlot.pad,
    if_pos coordinates.code.isLt, VerifierTableauProblem.preservationConstraints, slot]
  split
  · rfl
  · rw [List.getElem?_map, symbol_lookup]
    rfl

theorem decode_slot {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    problem.preservationConstraintSlotDirect coordinate = slot (decode problem coordinate hCoordinate) := by
  calc
    problem.preservationConstraintSlotDirect coordinate =
        problem.preservationConstraintSlotDirect (decode problem coordinate hCoordinate).index :=
      congrArg problem.preservationConstraintSlotDirect (decode_index problem coordinate hCoordinate).symm
    _ = slot (decode problem coordinate hCoordinate) := slot_at (decode problem coordinate hCoordinate)

theorem slot_diagonal {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) (hEqual : coordinates.head = coordinates.other) :
    slot coordinates = some none := by
  exact if_pos hEqual

theorem slot_off_diagonal {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) (hDifferent : coordinates.head ≠ coordinates.other) :
    slot coordinates = some (some (constraint coordinates)) := by
  exact if_neg hDifferent

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderLocalConstraintPayload.values (slot (decode problem coordinate hCoordinate))) =
        some (problem.preservationConstraintSlotDirect coordinate) := by
  rw [BuilderLocalConstraintPayload.decode_values, decode_slot]

theorem source_coordinate_lt {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderConstraintRegionSource.localCoordinate problem index .preservation < slotCount problem := by
  rw [← regionLength_eq]
  exact BuilderConstraintRegionSource.localCoordinate_valid problem index .preservation hRegion

def ofSource {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    Coordinates problem :=
  decode problem (BuilderConstraintRegionSource.localCoordinate problem index .preservation)
    (source_coordinate_lt problem index hRegion)

theorem source_slot {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderConstraintRegionSource.regionSlot problem .preservation
      (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
        slot (ofSource problem index hRegion) :=
  decode_slot problem _ (source_coordinate_lt problem index hRegion)

/-- This interpretation is proved for the actual written radix data. -/
theorem source_radix_coordinates {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .preservation)
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
      [(ofSource problem index hRegion).code.val, (ofSource problem index hRegion).other.val,
        (ofSource problem index hRegion).head.val] ∧
    BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .preservation)
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation) =
      (ofSource problem index hRegion).step.val := by
  rw [radices_eq]
  exact ⟨rfl, rfl⟩

end PNP.Concrete.CookLevin.BuilderPreservationCoordinates
