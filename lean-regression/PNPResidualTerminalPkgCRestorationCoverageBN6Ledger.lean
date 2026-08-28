import PNP.ResidualTerminalPkgCRestorationCoverageBN6Ledger

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace ResidualTerminalPkgCRestorationCoverageBN6LedgerRegression

abbrev LedgerAtom := Fin 4
abbrev LedgerCoordinate := TerminalBN5ShadowCoordinate LedgerAtom Nat Nat Nat
  Nat Nat Nat Nat

def ledgerCarrier : List LedgerAtom := [0, 1, 2, 3]

def ledgerSystem02 : TerminalV54ConsumerSystem LedgerAtom where
  carrier := ledgerCarrier
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included, ledgerCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def ledgerSystem13 : TerminalV54ConsumerSystem LedgerAtom where
  carrier := ledgerCarrier
  carrierNodup := by decide
  consumers := [[1], [3]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included, ledgerCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def ledgerSeparatingSystem : TerminalV54ConsumerSystem LedgerAtom where
  carrier := ledgerCarrier
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included, ledgerCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def ledgerSystem02Singletonized :
    ledgerSystem02.DisjointPairsSingletonized :=
  terminalBN6_disjointPairsSingletonized_of_all_singletons
    ledgerSystem02 (by simp [ledgerSystem02])

def ledgerSystem13Singletonized :
    ledgerSystem13.DisjointPairsSingletonized :=
  terminalBN6_disjointPairsSingletonized_of_all_singletons
    ledgerSystem13 (by simp [ledgerSystem13])

def ledgerPayload (mass : Nat) (positive : 0 < mass) :
    TerminalBN6PayloadAtom Nat :=
  { mass := mass
    massPositive := positive
    payload := mass + 100 }

def ledgerSource02 : TerminalPkgCBN6SourceCell LedgerAtom Nat ledgerCarrier where
  consumerSystem := ledgerSystem02
  carrierBinding := rfl
  activeCut := [0]
  active := (ledgerSystem02.cutActivationBool_eq_true_iff [0]).1 (by decide)
  payloadAtom := ledgerPayload 3 (by decide)

def ledgerSource13 : TerminalPkgCBN6SourceCell LedgerAtom Nat ledgerCarrier where
  consumerSystem := ledgerSystem13
  carrierBinding := rfl
  activeCut := [1]
  active := (ledgerSystem13.cutActivationBool_eq_true_iff [1]).1 (by decide)
  payloadAtom := ledgerPayload 5 (by decide)

def ledgerSeparatingSource :
    TerminalPkgCBN6SourceCell LedgerAtom Nat ledgerCarrier where
  consumerSystem := ledgerSeparatingSystem
  carrierBinding := rfl
  activeCut := [0, 1]
  active :=
    (ledgerSeparatingSystem.cutActivationBool_eq_true_iff [0, 1]).1
      (by decide)
  payloadAtom := ledgerPayload 7 (by decide)

def ledgerKey : TerminalBN4ActivationKey LedgerAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def ledgerCoordinate (atom : LedgerAtom) : LedgerCoordinate :=
  { key := ledgerKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def ledgerCoveredRestoration :
    TerminalPkgCRestorationUniverse LedgerAtom LedgerCoordinate where
  coordinateOf := ledgerCoordinate
  fullRestorationCoordinates := fun left right =>
    (left ++ right).map ledgerCoordinate

def ledgerDeficientRestoration :
    TerminalPkgCRestorationUniverse LedgerAtom LedgerCoordinate where
  coordinateOf := ledgerCoordinate
  fullRestorationCoordinates := fun _left _right => []

def ledgerCoveragePair : TerminalPkgCSeparatingPair ledgerSeparatingSystem :=
  terminalPkgCSeparatingPairOfFound ledgerSeparatingSystem [0, 1] [2]
    (by decide)

def ledgerRemainder : List (TerminalBN4ActivationCell LedgerAtom Nat Nat) :=
  [{ key := { atom := 0, semanticSignature := 31, transportType := 37 }
     sign := .positive
     mass := 5 },
   { key := { atom := 0, semanticSignature := 31, transportType := 37 }
     sign := .negative
     mass := 1 }]

def ledgerReorderedAmbient :
    List (TerminalBN4ActivationCell LedgerAtom Nat Nat) :=
  ledgerRemainder ++
    (ledgerCoveragePair.restorationCoverageCancellationCells
      ledgerCoveredRestoration).reverse

def ledgerDeficientAmbient :
    List (TerminalBN4ActivationCell LedgerAtom Nat Nat) :=
  (ledgerCoveragePair.restorationCoverageCancellationCells
    ledgerCoveredRestoration).tail

abbrev LedgerCell := TerminalPkgCRestorationCoverageBN6SourceCell LedgerAtom
  Nat LedgerAtom Nat Nat Nat Nat Nat Nat Nat ledgerCarrier

def ledgerCell02 : LedgerCell where
  source := ledgerSource02
  restoration := ledgerDeficientRestoration
  ambient := []

def ledgerCell13 : LedgerCell where
  source := ledgerSource13
  restoration := ledgerDeficientRestoration
  ambient := []

def ledgerHallCell : LedgerCell where
  source := ledgerSeparatingSource
  restoration := ledgerDeficientRestoration
  ambient := []

def ledgerReducedCell : LedgerCell where
  source := ledgerSeparatingSource
  restoration := ledgerCoveredRestoration
  ambient := ledgerReorderedAmbient

def ledgerMismatchCell : LedgerCell where
  source := ledgerSeparatingSource
  restoration := ledgerCoveredRestoration
  ambient := ledgerDeficientAmbient

def ledgerSingletonCells : List LedgerCell := [ledgerCell02, ledgerCell13]

def ledgerSingletonized : forall cell, cell ∈ ledgerSingletonCells ->
    cell.source.consumerSystem.DisjointPairsSingletonized := by
  intro cell member
  have cases : cell = ledgerCell02 ∨ cell = ledgerCell13 := by
    simpa [ledgerSingletonCells] using member
  rcases cases with rfl | rfl
  · exact ledgerSystem02Singletonized
  · exact ledgerSystem13Singletonized

def ledgerPositiveCells :=
  terminalPkgCRestorationCoverageBN6PositiveCells ledgerSingletonCells
    ledgerSingletonized

example : ledgerPositiveCells.length = 2 := by decide

example : ledgerPositiveCells.map (fun cell => cell.footprint) =
    [[0, 2], [1, 3]] := by decide

example : ledgerPositiveCells.map (fun cell => cell.payloadAtom.mass) =
    [3, 5] := by decide

example : terminalPkgCRestorationCoverageBN6SourceActivationWeight
    ledgerSingletonCells [0, 1] = 8 := by decide

example (cut : List LedgerAtom) :
    terminalBN6PositiveCellsActivationWeight ledgerCarrier
        ledgerPositiveCells cut =
      terminalPkgCRestorationCoverageBN6SourceActivationWeight
        ledgerSingletonCells cut :=
  terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
    ledgerSingletonCells ledgerSingletonized cut

def ledgerHallFirst : List LedgerCell :=
  [ledgerCell02, ledgerHallCell, ledgerReducedCell]

def ledgerReductionFirst : List LedgerCell :=
  [ledgerCell02, ledgerReducedCell, ledgerHallCell]

def ledgerMismatchFirst : List LedgerCell :=
  [ledgerCell02, ledgerMismatchCell, ledgerReducedCell]

private def ledgerOutcomeTag {cells : List LedgerCell} :
    TerminalPkgCRestorationCoverageBN6LedgerOutcome ledgerCarrier cells -> Nat
  | .cellized _ => 0
  | .hallRoute _ _ _ _ => 1
  | .reduced _ _ _ _ _ _ _ => 2
  | .ambientMismatch _ _ _ _ _ _ _ => 3

example : ledgerOutcomeTag
    (classifyTerminalPkgCRestorationCoverageBN6Ledger ledgerCarrier
      ledgerSingletonCells) = 0 := by decide

example : ledgerOutcomeTag
    (classifyTerminalPkgCRestorationCoverageBN6Ledger ledgerCarrier
      ledgerHallFirst) = 1 := by decide

example : ledgerOutcomeTag
    (classifyTerminalPkgCRestorationCoverageBN6Ledger ledgerCarrier
      ledgerReductionFirst) = 2 := by decide

example : ledgerOutcomeTag
    (classifyTerminalPkgCRestorationCoverageBN6Ledger ledgerCarrier
      ledgerMismatchFirst) = 3 := by decide

example :=
  terminalPkgC_restorationCoverage_bn6_cellization_checked_complete
    ledgerCarrier ledgerSingletonCells

example :=
  terminalPkgC_restorationCoverage_bn6_cellization_checked_complete
    ledgerCarrier ledgerHallFirst

#print axioms terminalPkgCRestorationCoverageBN6SourceCells_singletonized
#print axioms terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
#print axioms classifyTerminalPkgCRestorationCoverageBN6Ledger
#print axioms terminalPkgC_restorationCoverage_bn6_cellization_checked_complete

end ResidualTerminalPkgCRestorationCoverageBN6LedgerRegression
end DirectWire
end PNP
