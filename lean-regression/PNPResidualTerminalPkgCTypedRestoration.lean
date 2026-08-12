import PNP.ResidualTerminalPkgCTypedRestoration

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCTypedRegressionAtom := Fin 4

def pkgCTypedRegressionSingletonSystem :
    TerminalV54ConsumerSystem PkgCTypedRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCTypedRegressionSeparatingSystem :
    TerminalV54ConsumerSystem PkgCTypedRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCTypedRegressionPair :
    TerminalPkgCSeparatingPair pkgCTypedRegressionSeparatingSystem :=
  terminalPkgCSeparatingPairOfFound pkgCTypedRegressionSeparatingSystem
    [0, 1] [2] (by decide)

structure PkgCTypedRegressionFullCandidate where
  atom : PkgCTypedRegressionAtom
  payload : Nat
deriving DecidableEq

def pkgCTypedRegressionRestorer : TerminalPkgCTypedRestorer
    PkgCTypedRegressionAtom PkgCTypedRegressionFullCandidate
      PkgCTypedRegressionAtom where
  quotientCoordinate := id
  restore := fun atom => { atom := atom, payload := atom.val + 10 }
  fullCoordinate := PkgCTypedRegressionFullCandidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

example : pkgCTypedRegressionPair.fullRestorationCandidates
    pkgCTypedRegressionRestorer =
      [{ atom := 0, payload := 10 },
       { atom := 1, payload := 11 },
       { atom := 2, payload := 12 }] := by
  decide

example : (pkgCTypedRegressionPair.fullRestorationCandidates
    pkgCTypedRegressionRestorer).map
      pkgCTypedRegressionRestorer.fullCoordinate = [0, 1, 2] := by
  decide

example : TerminalPkgCExactCoordinateCoverage
    pkgCTypedRegressionRestorer.coordinateUniverse
      pkgCTypedRegressionPair :=
  pkgCTypedRegressionPair.typedRestoration_exactCoverage
    pkgCTypedRegressionRestorer

example (deficit : TerminalBN5HallDeficit
    (pkgCTypedRegressionPair.quotientUnits
      pkgCTypedRegressionRestorer.coordinateUniverse)
    (pkgCTypedRegressionRestorer.coordinateUniverse.fullRestorations
      pkgCTypedRegressionPair)) : False :=
  terminalBN5CompleteMultiplicityMatching_not_hallDeficit
    (pkgCTypedRegressionPair.typedRestoration_exactCoverage
      pkgCTypedRegressionRestorer)
    deficit

def pkgCTypedRegressionOutcomeTag
    {system : TerminalV54ConsumerSystem PkgCTypedRegressionAtom} :
    TerminalPkgCTypedRestorationOutcome system
      pkgCTypedRegressionRestorer -> Nat
  | .singletonized _ => 0
  | .realized _ _ => 1

example : pkgCTypedRegressionOutcomeTag
    (classifyTerminalPkgCTypedRestoration
      pkgCTypedRegressionSingletonSystem pkgCTypedRegressionRestorer) = 0 :=
  by decide

example : pkgCTypedRegressionOutcomeTag
    (classifyTerminalPkgCTypedRestoration
      pkgCTypedRegressionSeparatingSystem pkgCTypedRegressionRestorer) = 1 :=
  by decide

example :
    pkgCTypedRegressionSeparatingSystem.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair
          pkgCTypedRegressionSeparatingSystem,
        Nonempty (TerminalPkgCTypedRestorationRealization pair
          pkgCTypedRegressionRestorer) :=
  terminalPkgC_typedRestoration_realization
    pkgCTypedRegressionSeparatingSystem pkgCTypedRegressionRestorer

#print axioms TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates
#print axioms TerminalPkgCSeparatingPair.typedRestoration_exactCoverage
#print axioms terminalBN5CompleteMultiplicityMatching_not_hallDeficit
#print axioms terminalPkgC_typedRestoration_realization

end DirectWire
end PNP
