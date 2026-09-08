/-
Copyright (c) 2026 PNP Labs.
Complete initial-family specification: independent payload order/sign checks
and universal canonical schedule/decoder contracts. No physical writer claim.
-/
import PNP.Concrete.CookLevinBuilderInitialConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderInitialConstraintPayload.Regression
open BuilderInitialConstraintPayload

example : sourceSymbol none = .blank := rfl
example : sourceSymbol (some false) = .zero := rfl
example : sourceSymbol (some true) = .one := rfl
example : sourceSymbol (some false) ≠ .one := by decide
example : sourceSymbol (some true) ≠ .zero := by decide
example (value : Option Bool) : VariableLayout.tapeSymbolCode (sourceSymbol value) =
    BuilderIndexedInputRead.resultCode value := sourceSymbol_code value
example : requiredValues 7 = [7, 1, 2] := rfl
example : guardedValues 7 9 = [7, 1, 9, 1, 1, 3] := rfl
example : bitGuardedValues 7 8 9 true = [8, 1, 7, 1, 9, 1, 2, 3] := rfl
example : bitGuardedValues 7 8 10 false = [8, 0, 7, 1, 10, 1, 2, 3] := rfl
example : bitGuardedValues 7 8 9 true ≠ [7, 1, 8, 1, 9, 1, 2, 3] := by decide
example : bitGuardedValues 7 8 10 false ≠ [8, 1, 7, 1, 10, 1, 2, 3] := by decide
example : guardedValues 7 9 ≠ [7, 1, 9, 1, 2, 3] := by decide
example : requiredValues 7 ≠ [7, 0, 2] := by decide
example (i : Nat) : (requiredValues i).length = 3 := requiredValues_length i
example (i j : Nat) : (guardedValues i j).length = 6 := guardedValues_length i j
example (i j k : Nat) (sign : Bool) : (bitGuardedValues i j k sign).length = 8 :=
  bitGuardedValues_length i j k sign
example : inputOnlySymbol [false, true] 3 2 = .blank := by decide
example : inputOnlySymbol [false, true] 3 3 = .zero := by decide
example : inputOnlySymbol [false, true] 3 4 = .one := by decide
example : inputOnlySymbol [false, true] 3 5 = .blank := by decide
example : inputOnlySymbol [] 0 0 = .blank := rfl
example (width : Nat) : BuilderLocalConstraintPayload.decode width [0] = some none := rfl
example (width : Nat) : BuilderLocalConstraintPayload.decode width [1] = some (some none) := rfl
example : ([0] : List Nat) ≠ [1] := by decide

section Complete
variable {language : Language} (problem : VerifierTableauProblem language)
example (coordinate : Nat) : values problem coordinate = BuilderLocalConstraintPayload.values
    (problem.initialConstraintSlotDirect coordinate) := values_canonical problem coordinate
example (coordinate : Nat) : values problem coordinate = BuilderLocalConstraintPayload.values
    (problem.scheduledInitialConstraints[coordinate]?) := values_schedule problem coordinate
example (coordinate : Nat) : BuilderLocalConstraintPayload.decode problem.FormulaWidth (values problem coordinate) =
    some (problem.initialConstraintSlotDirect coordinate) := decode_values problem coordinate
example : values problem 0 =
    requiredValues (problem.stateLiteral problem.initialTime problem.startState).index.val := state_values problem
example : values problem 1 =
    requiredValues (problem.headLiteral problem.initialTime problem.initialHeadPosition).index.val := head_values problem
example (hMode : problem.tableauInputMode = .paired) : values problem 2 = lengthValues problem hMode :=
  paired_length_values problem hMode
example (coordinate : Nat) (hOutside : symbolCapacity problem ≤ coordinate) :
    values problem (coordinate + 2) = [0] := outside_values problem coordinate hOutside
example (hMode : problem.tableauInputMode ≠ .paired) (coordinate : Nat)
    (hCapacity : coordinate < symbolCapacity problem)
    (hOutside : problem.dimensions.tapeWidth problem.tableauInputMode ≤ coordinate) :
    values problem (coordinate + 2) = [1] := inputOnly_padding_values problem hMode coordinate hCapacity hOutside
example (hMode : problem.tableauInputMode = .paired) (coordinate : Nat)
    (hCapacity : coordinate + 1 < symbolCapacity problem)
    (hOutside : problem.pairedCellsWidthDirect ≤ coordinate) :
    values problem (coordinate + 3) = [1] := paired_padding_values problem hMode coordinate hCapacity hOutside
example (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    inputOnlySymbol problem.input problem.uniformFuel position.val =
      problem.inputOnlyInitialSymbolDirect position := inputOnlySymbol_canonical problem position
example (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (index : Fin problem.certificateLimit) :
    requestValues problem hMode length position (.certificate index) 0 = some
      (bitGuardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.pairedBitLiteral hMode index).index.val
        (problem.symbolLiteral problem.initialTime position .one).index.val true) := rfl
example (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (index : Fin problem.certificateLimit) :
    requestValues problem hMode length position (.certificate index) 1 = some
      (bitGuardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.pairedBitLiteral hMode index).index.val
        (problem.symbolLiteral problem.initialTime position .zero).index.val false) := rfl
example (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (index : Fin problem.certificateLimit) (offset : Nat) :
    requestValues problem hMode length position (.certificate index) (offset + 2) = none := rfl
example (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (index : Nat) :
    requestValues problem hMode length position (.sourceBit index) 0 = some
      (guardedValues (problem.pairedLengthLiteral hMode length).index.val
        (problem.symbolLiteral problem.initialTime position (sourceSymbol problem.input[index]?)).index.val) := rfl
end Complete
end PNP.Concrete.CookLevin.BuilderInitialConstraintPayload.Regression
