/-
Copyright (c) 2026 PNP Labs.

Complete initial-family payload specification in the unchanged logical register
order. Source-bit requests read the actual input, certificate branches retain
their two distinct signs and conclusions, and absent/padded coordinates differ.
This is a semantic contract for the physical writer, not that writer or a
complete polynomial formula-builder theorem.
-/

import PNP.Concrete.CookLevinBuilderInitialCellSelection
import PNP.Concrete.CookLevinBuilderIndexedInputRead
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload
import PNP.Concrete.CookLevinBuilderShapeCoordinates

namespace PNP.Concrete.CookLevin.BuilderInitialConstraintPayload

open VerifierTableauProblem
open BuilderInitialCellCoordinates (Request resolve pairedRequest)

def sourceSymbol : Option Bool → TapeSymbol
  | none => .blank
  | some value => symbolOfFixedBit value

theorem sourceSymbol_code (value : Option Bool) :
    VariableLayout.tapeSymbolCode (sourceSymbol value) =
      BuilderIndexedInputRead.resultCode value := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

def requiredValues (index : Nat) : List Nat := [index, 1, 2]
def guardedValues (lengthIndex symbolIndex : Nat) : List Nat :=
  [lengthIndex, 1, symbolIndex, 1, 1, 3]
def bitGuardedValues (lengthIndex bitIndex symbolIndex : Nat) (positive : Bool) : List Nat :=
  [bitIndex, BuilderLocalConstraintPayload.signValue positive, lengthIndex, 1, symbolIndex, 1, 2, 3]

theorem requiredValues_length (index : Nat) : (requiredValues index).length = 3 := rfl
theorem guardedValues_length (lengthIndex symbolIndex : Nat) :
    (guardedValues lengthIndex symbolIndex).length = 6 := rfl
theorem bitGuardedValues_length (lengthIndex bitIndex symbolIndex : Nat) (positive : Bool) :
    (bitGuardedValues lengthIndex bitIndex symbolIndex positive).length = 8 := rfl

private def encode {width : Nat} (constraint : LocalConstraint width) : List Nat :=
  BuilderLocalConstraintPayload.values (some (some constraint))

theorem requiredValues_canonical {width : Nat} (index : Fin width) :
    requiredValues index.val = BuilderLocalConstraintPayload.values
      (some (some (.require ⟨true, index⟩))) := rfl

theorem guardedValues_canonical {width : Nat} (lengthIndex symbolIndex : Fin width) :
    guardedValues lengthIndex.val symbolIndex.val = BuilderLocalConstraintPayload.values
      (some (some (.implication [⟨true, lengthIndex⟩] ⟨true, symbolIndex⟩))) := rfl

theorem bitGuardedValues_canonical {width : Nat}
    (lengthIndex bitIndex symbolIndex : Fin width) (positive : Bool) :
    bitGuardedValues lengthIndex.val bitIndex.val symbolIndex.val positive =
      BuilderLocalConstraintPayload.values
        (some (some (.implication [⟨true, lengthIndex⟩, ⟨positive, bitIndex⟩]
          ⟨true, symbolIndex⟩))) := by
  cases positive <;> rfl

private def singletonValues (payload : List Nat) : Nat → Option (List Nat)
  | 0 => some payload
  | _ + 1 => none

/-- No supplied bit: a source request uses the actual indexed input read. -/
def requestValues {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    Request problem.certificateLimit → Nat → Option (List Nat)
  | .blank, offset => singletonValues
      (guardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.symbolLiteral problem.initialTime position .blank).index.val) offset
  | .fixed value, offset => singletonValues
      (guardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.symbolLiteral problem.initialTime position (symbolOfFixedBit value)).index.val) offset
  | .sourceBit index, offset => singletonValues
      (guardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.symbolLiteral problem.initialTime position (sourceSymbol problem.input[index]?)).index.val) offset
  | .certificate index, 0 => some
      (bitGuardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.pairedBitLiteral hMode index).index.val
        (problem.symbolLiteral problem.initialTime position .one).index.val true)
  | .certificate index, 1 => some
      (bitGuardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.pairedBitLiteral hMode index).index.val
        (problem.symbolLiteral problem.initialTime position .zero).index.val false)
  | .certificate _, _ + 2 => none

private def cellSlot {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    InitialCell problem.certificateLimit → Nat → Option (LocalConstraint problem.FormulaWidth)
  | .blank => DirectSlot.singleton (.implication [problem.pairedLengthLiteral hMode length]
      (problem.symbolLiteral problem.initialTime position .blank))
  | .fixed value => DirectSlot.singleton (.implication [problem.pairedLengthLiteral hMode length]
      (problem.symbolLiteral problem.initialTime position (symbolOfFixedBit value)))
  | .certificate index => DirectSlot.append 1
      (DirectSlot.singleton (.implication
        [problem.pairedLengthLiteral hMode length, problem.pairedBitLiteral hMode index]
        (problem.symbolLiteral problem.initialTime position .one)))
      (DirectSlot.singleton (.implication
        [problem.pairedLengthLiteral hMode length, (problem.pairedBitLiteral hMode index).negate]
        (problem.symbolLiteral problem.initialTime position .zero)))

theorem requestValues_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    requestValues problem hMode length position request offset =
      (cellSlot problem hMode length position (resolve problem.input request) offset).map encode := by
  cases request with
  | blank => cases offset <;> rfl
  | fixed value => cases offset <;> rfl
  | sourceBit index =>
      simp only [requestValues, resolve]
      cases hBit : problem.input[index]? with
      | none => cases offset <;> rfl
      | some value => cases offset <;> rfl
  | certificate index =>
      cases offset with
      | zero => rfl
      | succ offset => cases offset <;> rfl

def pairedCellValues {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (offset : Nat) :
    Option (List Nat) :=
  requestValues problem hMode length position
    (pairedRequest problem.input.length length problem.uniformFuel position.val) offset

theorem pairedCellValues_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (offset : Nat) :
    pairedCellValues problem hMode length position offset =
      (problem.pairedCellConstraintSlotDirect hMode length position offset).map encode := by
  rw [pairedCellValues, requestValues_canonical, BuilderInitialCellCoordinates.pairedRequest_resolve]
  cases hCell : initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length) problem.uniformFuel position.val <;>
    simp only [cellSlot, pairedCellConstraintSlotDirect, hCell]

def lengthValues {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) : List Nat :=
  ((problem.pairedLengthVariables hMode).map Fin.val).reverse ++
    [problem.certificateLimit + 1, 4]

theorem lengthValues_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    lengthValues problem hMode = encode (.exactlyOne (problem.pairedLengthVariables hMode)) := by
  rw [encode, BuilderShapeCoordinates.exactlyOne_values]
  simp only [lengthValues, pairedLengthVariables, List.length_map, finiteIndices_length]

/-- Both the chosen row and the within-row cell come from the canonical coordinate. -/
def pairedSymbolsValues {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) : Nat → Option (List Nat)
  | 0 => some (lengthValues problem hMode)
  | coordinate + 1 =>
      (BuilderInitialCellSelection.selectedInitialCell problem hMode coordinate).bind
        (fun found => pairedCellValues problem hMode found.1 found.2.1 found.2.2)

theorem pairedSymbolsValues_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    pairedSymbolsValues problem hMode coordinate =
      (problem.pairedSymbolsSlotDirect hMode coordinate).map encode := by
  cases coordinate with
  | zero =>
      simpa only [pairedSymbolsValues, pairedSymbolsSlotDirect, DirectSlot.append,
        DirectSlot.singleton, if_pos (by decide : 0 < 1), Option.map_some] using
        congrArg some (lengthValues_canonical problem hMode)
  | succ coordinate =>
      simp only [pairedSymbolsValues, pairedSymbolsSlotDirect, DirectSlot.append,
        if_neg (by omega : ¬ coordinate + 1 < 1), Nat.add_sub_cancel]
      rw [BuilderInitialCellSelection.selectedInitialCell_canonical]
      cases hCell : BuilderInitialCellSelection.selectedInitialCell problem hMode coordinate with
      | none => rfl
      | some cell =>
          simpa only [Option.bind_some, Option.map_some] using
            pairedCellValues_canonical problem hMode cell.1 cell.2.1 cell.2.2

def inputOnlySymbol (input : BitString) (center position : Nat) : TapeSymbol :=
  if center ≤ position then sourceSymbol input[position - center]? else .blank

theorem inputOnlySymbol_canonical {language : Language} (problem : VerifierTableauProblem language)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    inputOnlySymbol problem.input problem.uniformFuel position.val =
      problem.inputOnlyInitialSymbolDirect position := by
  unfold inputOnlyInitialSymbolDirect
  rw [← BuilderInitialCellCoordinates.inputOnlyRequest_resolve]
  unfold inputOnlySymbol BuilderInitialCellCoordinates.inputOnlyRequest
  by_cases hPosition : problem.uniformFuel ≤ position.val
  · simp only [if_pos hPosition, resolve]
    cases problem.input[position.val - problem.uniformFuel]? <;> rfl
  · simp only [if_neg hPosition, resolve, initialCellSymbol]

def inputOnlySymbolsValues {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) : Option (List Nat) :=
  if hPosition : coordinate < problem.dimensions.tapeWidth problem.tableauInputMode then
    some (requiredValues (problem.symbolLiteral problem.initialTime ⟨coordinate, hPosition⟩
      (inputOnlySymbol problem.input problem.uniformFuel coordinate)).index.val)
  else none

theorem inputOnlySymbolsValues_canonical {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    inputOnlySymbolsValues problem coordinate = (problem.inputOnlySymbolsSlotDirect coordinate).map encode := by
  unfold inputOnlySymbolsValues inputOnlySymbolsSlotDirect DirectSlot.finiteMap
  by_cases hPosition : coordinate < problem.dimensions.tapeWidth problem.tableauInputMode
  · simp only [dif_pos hPosition, Option.map_some]
    rw [inputOnlySymbol_canonical problem ⟨coordinate, hPosition⟩]
    rfl
  · simp only [dif_neg hPosition, Option.map_none]

def symbolCapacity {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  1 + 2 * ((problem.certificateLimit + 1) * problem.dimensions.tapeWidth problem.tableauInputMode)

/-- Complete initial-region register payload, including both prefixes and padding. -/
def values {language : Language} (problem : VerifierTableauProblem language) : Nat → List Nat
  | 0 => requiredValues (problem.stateLiteral problem.initialTime problem.startState).index.val
  | 1 => requiredValues (problem.headLiteral problem.initialTime problem.initialHeadPosition).index.val
  | coordinate + 2 =>
      if coordinate < symbolCapacity problem then
        if hMode : problem.tableauInputMode = .paired then
          (pairedSymbolsValues problem hMode coordinate).getD [1]
        else (inputOnlySymbolsValues problem coordinate).getD [1]
      else [0]

private theorem padding_values {width : Nat} (slot : Option (LocalConstraint width)) :
    (slot.map encode).getD [1] = BuilderLocalConstraintPayload.values (some slot) := by
  cases slot <;> rfl

theorem values_canonical {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    values problem coordinate = BuilderLocalConstraintPayload.values
      (problem.initialConstraintSlotDirect coordinate) := by
  cases coordinate with
  | zero => rfl
  | succ coordinate =>
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          have hPrefix : ¬ coordinate + 1 + 1 < 2 := by omega
          have hOffset : coordinate + 1 + 1 - 2 = coordinate := by omega
          simp only [values, initialConstraintSlotDirect, DirectSlot.append, if_neg hPrefix, hOffset,
            DirectSlot.pad]
          by_cases hCapacity : coordinate < symbolCapacity problem
          · simp only [symbolCapacity] at hCapacity
            simp only [symbolCapacity, if_pos hCapacity, initialSymbolsSlotDirect]
            by_cases hMode : problem.tableauInputMode = .paired
            · simp only [dif_pos hMode, pairedSymbolsValues_canonical, padding_values]
            · simp only [dif_neg hMode, inputOnlySymbolsValues_canonical, padding_values]
          · simp only [symbolCapacity] at hCapacity
            simp only [symbolCapacity, if_neg hCapacity, BuilderLocalConstraintPayload.values,
              BuilderLocalConstraintPayload.front, List.reverse_cons, List.reverse_nil, List.nil_append]

theorem values_schedule {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    values problem coordinate = BuilderLocalConstraintPayload.values
      (problem.scheduledInitialConstraints[coordinate]?) := by
  rw [values_canonical, problem.initialConstraintSlotDirect_eq]

theorem decode_values {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (values problem coordinate) =
      some (problem.initialConstraintSlotDirect coordinate) := by
  rw [values_canonical]
  exact BuilderLocalConstraintPayload.decode_values _

theorem state_values {language : Language} (problem : VerifierTableauProblem language) :
    values problem 0 = requiredValues (problem.stateLiteral problem.initialTime problem.startState).index.val := rfl

theorem head_values {language : Language} (problem : VerifierTableauProblem language) :
    values problem 1 = requiredValues
      (problem.headLiteral problem.initialTime problem.initialHeadPosition).index.val := rfl

theorem paired_length_values {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) : values problem 2 = lengthValues problem hMode := by
  have hCapacity : 0 < symbolCapacity problem := by unfold symbolCapacity; omega
  simp only [values, if_pos hCapacity, dif_pos hMode, pairedSymbolsValues, Option.getD_some]

theorem outside_values {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hOutside : symbolCapacity problem ≤ coordinate) : values problem (coordinate + 2) = [0] := by
  simp only [values, if_neg (by omega : ¬ coordinate < symbolCapacity problem)]

theorem inputOnly_padding_values {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode ≠ .paired) (coordinate : Nat)
    (hCapacity : coordinate < symbolCapacity problem)
    (hOutside : problem.dimensions.tapeWidth problem.tableauInputMode ≤ coordinate) :
    values problem (coordinate + 2) = [1] := by
  simp only [values, if_pos hCapacity, dif_neg hMode, inputOnlySymbolsValues,
    dif_neg (by omega : ¬ coordinate < problem.dimensions.tapeWidth problem.tableauInputMode), Option.getD_none]

theorem paired_padding_values {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat)
    (hCapacity : coordinate + 1 < symbolCapacity problem)
    (hOutside : problem.pairedCellsWidthDirect ≤ coordinate) :
    values problem (coordinate + 3) = [1] := by
  have hNone := (BuilderInitialCellSelection.selectedInitialCell_none_iff problem hMode coordinate).mpr hOutside
  simp only [values, if_pos hCapacity, dif_pos hMode, pairedSymbolsValues, hNone,
    Option.bind_none, Option.getD_none]

end PNP.Concrete.CookLevin.BuilderInitialConstraintPayload
