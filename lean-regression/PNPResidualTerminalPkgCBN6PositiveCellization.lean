import PNP.ResidualTerminalPkgCBN6PositiveCellization

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCBN6CellizationRegressionAtom := Fin 4

def pkgCBN6CellizationCarrier : List PkgCBN6CellizationRegressionAtom :=
  [0, 1, 2, 3]

def pkgCBN6CellizationSystem02 :
    TerminalV54ConsumerSystem PkgCBN6CellizationRegressionAtom where
  carrier := pkgCBN6CellizationCarrier
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included,
    pkgCBN6CellizationCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCBN6CellizationSystem13 :
    TerminalV54ConsumerSystem PkgCBN6CellizationRegressionAtom where
  carrier := pkgCBN6CellizationCarrier
  carrierNodup := by decide
  consumers := [[1], [3]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included,
    pkgCBN6CellizationCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCBN6CellizationSeparatingSystem :
    TerminalV54ConsumerSystem PkgCBN6CellizationRegressionAtom where
  carrier := pkgCBN6CellizationCarrier
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included,
    pkgCBN6CellizationCarrier]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCBN6CellizationSystem02Singletonized :
    pkgCBN6CellizationSystem02.DisjointPairsSingletonized :=
  terminalBN6_disjointPairsSingletonized_of_all_singletons
    pkgCBN6CellizationSystem02 (by simp [pkgCBN6CellizationSystem02])

def pkgCBN6CellizationSystem13Singletonized :
    pkgCBN6CellizationSystem13.DisjointPairsSingletonized :=
  terminalBN6_disjointPairsSingletonized_of_all_singletons
    pkgCBN6CellizationSystem13 (by simp [pkgCBN6CellizationSystem13])

def pkgCBN6CellizationPayload (mass : Nat) (positive : 0 < mass) :
    TerminalBN6PayloadAtom Nat :=
  { mass := mass
    massPositive := positive
    payload := mass + 100 }

def pkgCBN6CellizationSource02 : TerminalPkgCBN6SourceCell
    PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier where
  consumerSystem := pkgCBN6CellizationSystem02
  carrierBinding := rfl
  activeCut := [0]
  active := (pkgCBN6CellizationSystem02.cutActivationBool_eq_true_iff
    [0]).1 (by decide)
  payloadAtom := pkgCBN6CellizationPayload 3 (by decide)

def pkgCBN6CellizationSource13 : TerminalPkgCBN6SourceCell
    PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier where
  consumerSystem := pkgCBN6CellizationSystem13
  carrierBinding := rfl
  activeCut := [1]
  active := (pkgCBN6CellizationSystem13.cutActivationBool_eq_true_iff
    [1]).1 (by decide)
  payloadAtom := pkgCBN6CellizationPayload 5 (by decide)

def pkgCBN6CellizationSources : List (TerminalPkgCBN6SourceCell
    PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier) :=
  [pkgCBN6CellizationSource02, pkgCBN6CellizationSource13]

def pkgCBN6CellizationSourcesSingletonized : ∀ cell,
    cell ∈ pkgCBN6CellizationSources →
      cell.consumerSystem.DisjointPairsSingletonized := by
  intro cell member
  have cases : cell = pkgCBN6CellizationSource02 ∨
      cell = pkgCBN6CellizationSource13 := by
    simpa [pkgCBN6CellizationSources] using member
  rcases cases with rfl | rfl
  ·
    exact pkgCBN6CellizationSystem02Singletonized
  ·
    exact pkgCBN6CellizationSystem13Singletonized

def pkgCBN6CellizationPositiveCells :=
  terminalPkgCBN6PositiveCells pkgCBN6CellizationSources
    pkgCBN6CellizationSourcesSingletonized

example : pkgCBN6CellizationPositiveCells.length = 2 := by decide

example : pkgCBN6CellizationPositiveCells.map
    (fun cell => cell.footprint) = [[0, 2], [1, 3]] := by decide

example : pkgCBN6CellizationPositiveCells.map
    (fun cell => cell.payloadAtom.mass) = [3, 5] := by decide

example : terminalPkgCBN6SourceActivationWeight
    pkgCBN6CellizationSources [0] = 3 := by decide

example : terminalPkgCBN6SourceActivationWeight
    pkgCBN6CellizationSources [0, 1] = 8 := by decide

example : terminalPkgCBN6SourceActivationWeight
    pkgCBN6CellizationSources [0, 2] = 0 := by decide

example : terminalBN6PositiveCellsActivationWeight
    pkgCBN6CellizationCarrier pkgCBN6CellizationPositiveCells [0, 1] = 8 :=
  by decide

example (cut : List PkgCBN6CellizationRegressionAtom) :
    terminalBN6PositiveCellsActivationWeight pkgCBN6CellizationCarrier
        pkgCBN6CellizationPositiveCells cut =
      terminalPkgCBN6SourceActivationWeight pkgCBN6CellizationSources cut :=
  terminalPkgCBN6PositiveCells_activationWeight
    pkgCBN6CellizationSources pkgCBN6CellizationSourcesSingletonized cut

structure PkgCBN6CellizationFullCandidate where
  atom : PkgCBN6CellizationRegressionAtom
  payload : Nat
deriving DecidableEq

def pkgCBN6CellizationKey : TerminalBN4ActivationKey
    PkgCBN6CellizationRegressionAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def pkgCBN6CellizationCoordinate
    (atom : PkgCBN6CellizationRegressionAtom) :
    TerminalBN5ShadowCoordinate PkgCBN6CellizationRegressionAtom Nat Nat Nat
      Nat Nat Nat Nat :=
  { key := pkgCBN6CellizationKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def pkgCBN6CellizationRestorer : TerminalPkgCTypedRestorer
    PkgCBN6CellizationRegressionAtom PkgCBN6CellizationFullCandidate
      (TerminalBN5ShadowCoordinate PkgCBN6CellizationRegressionAtom Nat Nat Nat
        Nat Nat Nat Nat) where
  quotientCoordinate := pkgCBN6CellizationCoordinate
  restore := fun atom => { atom := atom, payload := atom.val + 50 }
  fullCoordinate := fun candidate =>
    pkgCBN6CellizationCoordinate candidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

def pkgCBN6CellizationSeparatingSource : TerminalPkgCBN6SourceCell
    PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier where
  consumerSystem := pkgCBN6CellizationSeparatingSystem
  carrierBinding := rfl
  activeCut := [0, 1]
  active :=
    (pkgCBN6CellizationSeparatingSystem.cutActivationBool_eq_true_iff
      [0, 1]).1 (by decide)
  payloadAtom := pkgCBN6CellizationPayload 7 (by decide)

def pkgCBN6CellizationSeparatingSources : List (TerminalPkgCBN6SourceCell
    PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier) :=
  [pkgCBN6CellizationSeparatingSource]

def pkgCBN6CellizationOutcomeTag
    {cells : List (TerminalPkgCBN6SourceCell
      PkgCBN6CellizationRegressionAtom Nat pkgCBN6CellizationCarrier)} :
    TerminalPkgCBN6CellizationOutcome pkgCBN6CellizationCarrier cells
      pkgCBN6CellizationRestorer → Nat
  | .cellized _ => 0
  | .pkgCCancellation _ _ _ _ => 1

example : pkgCBN6CellizationOutcomeTag
    (classifyTerminalPkgCBN6Cellization pkgCBN6CellizationCarrier
      pkgCBN6CellizationRestorer pkgCBN6CellizationSources) = 0 := by decide

example : pkgCBN6CellizationOutcomeTag
    (classifyTerminalPkgCBN6Cellization pkgCBN6CellizationCarrier
      pkgCBN6CellizationRestorer pkgCBN6CellizationSeparatingSources) = 1 :=
  by decide

example :
    (∃ singletonized : ∀ cell, cell ∈ pkgCBN6CellizationSources →
        cell.consumerSystem.DisjointPairsSingletonized,
      (terminalPkgCBN6PositiveCells pkgCBN6CellizationSources
        singletonized).length = pkgCBN6CellizationSources.length ∧
      (terminalPkgCBN6PositiveCells pkgCBN6CellizationSources
        singletonized).map TerminalBN6PositiveCell.payloadAtom =
          pkgCBN6CellizationSources.map
            TerminalPkgCBN6SourceCell.payloadAtom ∧
      ∀ cut,
        terminalBN6PositiveCellsActivationWeight pkgCBN6CellizationCarrier
            (terminalPkgCBN6PositiveCells pkgCBN6CellizationSources
              singletonized) cut =
          terminalPkgCBN6SourceActivationWeight
            pkgCBN6CellizationSources cut) ∨
      ∃ cell, cell ∈ pkgCBN6CellizationSources ∧
        ∃ pair : TerminalPkgCSeparatingPair cell.consumerSystem,
          Nonempty (TerminalPkgCSameKeyCancellationRealization pair
            pkgCBN6CellizationRestorer) :=
  terminalPkgC_bn6_positive_cellization_checked_complete
    pkgCBN6CellizationCarrier pkgCBN6CellizationSources
    pkgCBN6CellizationRestorer

end DirectWire
end PNP
