import PNP.ResidualTerminalPkgCSameKeyCancellation

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCSameKeyRegressionAtom := Fin 4

def pkgCSameKeyRegressionSingletonSystem :
    TerminalV54ConsumerSystem PkgCSameKeyRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCSameKeyRegressionSeparatingSystem :
    TerminalV54ConsumerSystem PkgCSameKeyRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCSameKeyRegressionPair :
    TerminalPkgCSeparatingPair pkgCSameKeyRegressionSeparatingSystem :=
  terminalPkgCSeparatingPairOfFound pkgCSameKeyRegressionSeparatingSystem
    [0, 1] [2] (by decide)

structure PkgCSameKeyRegressionFullCandidate where
  atom : PkgCSameKeyRegressionAtom
  payload : Nat
deriving DecidableEq

def pkgCSameKeyRegressionKey :
    TerminalBN4ActivationKey PkgCSameKeyRegressionAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def pkgCSameKeyRegressionCoordinate (atom : PkgCSameKeyRegressionAtom) :
    TerminalBN5ShadowCoordinate PkgCSameKeyRegressionAtom Nat Nat Nat Nat Nat
      Nat Nat :=
  { key := pkgCSameKeyRegressionKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def pkgCSameKeyRegressionRestorer : TerminalPkgCTypedRestorer
    PkgCSameKeyRegressionAtom PkgCSameKeyRegressionFullCandidate
      (TerminalBN5ShadowCoordinate PkgCSameKeyRegressionAtom Nat Nat Nat Nat
        Nat Nat Nat) where
  quotientCoordinate := pkgCSameKeyRegressionCoordinate
  restore := fun atom => { atom := atom, payload := atom.val + 50 }
  fullCoordinate := fun candidate =>
    pkgCSameKeyRegressionCoordinate candidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

example : (pkgCSameKeyRegressionPair.restorationCancellationCells
    pkgCSameKeyRegressionRestorer).length = 6 := by decide

example : terminalBN4PositiveMass
    (pkgCSameKeyRegressionPair.restorationCancellationCells
      pkgCSameKeyRegressionRestorer) pkgCSameKeyRegressionKey = 3 := by decide

example : terminalBN4NegativeMass
    (pkgCSameKeyRegressionPair.restorationCancellationCells
      pkgCSameKeyRegressionRestorer) pkgCSameKeyRegressionKey = 3 := by decide

example : TerminalBN4KeyCancellation.residualCells
    (terminalBN4CancelAtKey
      (pkgCSameKeyRegressionPair.restorationCancellationCells
        pkgCSameKeyRegressionRestorer)
      pkgCSameKeyRegressionKey) pkgCSameKeyRegressionKey = [] := by decide

example : terminalBN4InputSignedMass
    (pkgCSameKeyRegressionPair.restorationCancellationCells
      pkgCSameKeyRegressionRestorer) pkgCSameKeyRegressionKey = 0 := by decide

def pkgCSameKeyRegressionOutcomeTag
    {system : TerminalV54ConsumerSystem PkgCSameKeyRegressionAtom} :
    TerminalPkgCSameKeyCancellationOutcome system
      pkgCSameKeyRegressionRestorer -> Nat
  | .singletonized _ => 0
  | .cancelled _ _ => 1

example : pkgCSameKeyRegressionOutcomeTag
    (classifyTerminalPkgCSameKeyCancellation
      pkgCSameKeyRegressionSingletonSystem pkgCSameKeyRegressionRestorer) = 0 :=
  by decide

example : pkgCSameKeyRegressionOutcomeTag
    (classifyTerminalPkgCSameKeyCancellation
      pkgCSameKeyRegressionSeparatingSystem pkgCSameKeyRegressionRestorer) = 1 :=
  by decide

example :
    pkgCSameKeyRegressionSeparatingSystem.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair
          pkgCSameKeyRegressionSeparatingSystem,
        Nonempty (TerminalPkgCSameKeyCancellationRealization pair
          pkgCSameKeyRegressionRestorer) :=
  terminalPkgC_typedRestoration_sameKeyCancellation
    pkgCSameKeyRegressionSeparatingSystem pkgCSameKeyRegressionRestorer

example
    (silent : TerminalPkgCSameKeyCancellationSilent
      pkgCSameKeyRegressionSeparatingSystem pkgCSameKeyRegressionRestorer) :
    pkgCSameKeyRegressionSeparatingSystem.DisjointPairsSingletonized :=
  terminalPkgC_sameKeyCancellation_silence_singletonizes
    pkgCSameKeyRegressionSeparatingSystem pkgCSameKeyRegressionRestorer silent

#print axioms terminalPkgCRestorationCancellationCellsForAtom_key_eq
#print axioms terminalPkgCRestorationCancellationCellsForAtoms_balanced
#print axioms TerminalPkgCSeparatingPair.restorationCancellation_balanced
#print axioms TerminalPkgCSeparatingPair.restorationCancellation_residualCells_empty
#print axioms TerminalPkgCSeparatingPair.restorationCancellation_signedMass_zero
#print axioms terminalPkgC_typedRestoration_sameKeyCancellation
#print axioms terminalPkgC_sameKeyCancellation_silence_singletonizes

end DirectWire
end PNP
