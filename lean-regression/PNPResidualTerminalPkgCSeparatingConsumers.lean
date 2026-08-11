import PNP.ResidualTerminalPkgCSeparatingConsumers

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCRegressionAtom := Fin 4

def pkgCRegressionSingletonSystem :
    TerminalV54ConsumerSystem PkgCRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

example : firstTerminalPkgCSeparatingPair? pkgCRegressionSingletonSystem = none :=
  by decide

theorem pkgCRegressionSingletonized :
    pkgCRegressionSingletonSystem.DisjointPairsSingletonized :=
  (firstTerminalPkgCSeparatingPair?_eq_none_iff
    pkgCRegressionSingletonSystem).1 (by decide)

def pkgCRegressionSeparatingSystem :
    TerminalV54ConsumerSystem PkgCRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

/-- The nested scan deterministically selects the first ordered disjoint pair
    that is not singleton-singleton. -/
example : firstTerminalPkgCSeparatingPair? pkgCRegressionSeparatingSystem =
    some ([0, 1], [2]) := by decide

def pkgCRegressionPair :
    TerminalPkgCSeparatingPair pkgCRegressionSeparatingSystem :=
  terminalPkgCSeparatingPairOfFound pkgCRegressionSeparatingSystem
    [0, 1] [2] (by decide)

def pkgCRegressionMatchedRestoration :
    TerminalPkgCRestorationUniverse PkgCRegressionAtom PkgCRegressionAtom where
  coordinateOf := id
  fullRestorationCoordinates := fun _ _ => [0, 1, 2]

def pkgCRegressionHallRestoration :
    TerminalPkgCRestorationUniverse PkgCRegressionAtom PkgCRegressionAtom where
  coordinateOf := id
  fullRestorationCoordinates := fun _ _ => [0, 1]

example : (pkgCRegressionPair.quotientUnits
    pkgCRegressionMatchedRestoration).map
      TerminalBN5FullUnit.coordinate = [0, 1, 2] := by decide

example : pkgCRegressionPair.quotientUnits
    pkgCRegressionMatchedRestoration ≠ [] :=
  pkgCRegressionPair.quotientUnits_nonempty
    pkgCRegressionMatchedRestoration

def pkgCRegressionOutcomeTag
    {system : TerminalV54ConsumerSystem PkgCRegressionAtom}
    {restoration : TerminalPkgCRestorationUniverse
      PkgCRegressionAtom PkgCRegressionAtom} :
    TerminalPkgCSeparatingConsumersOutcome system restoration -> Nat
  | .singletonized _ => 0
  | .restored _ _ => 1
  | .localized _ _ => 2

/-- Equal exact-coordinate multiplicities take the complete restoration
    branch. -/
example : pkgCRegressionOutcomeTag
    (classifyTerminalPkgCSeparatingConsumers
      pkgCRegressionSeparatingSystem pkgCRegressionMatchedRestoration) = 1 :=
  by decide

/-- Omitting coordinate `2` forces the proof-bearing strict Hall branch. -/
example : pkgCRegressionOutcomeTag
    (classifyTerminalPkgCSeparatingConsumers
      pkgCRegressionSeparatingSystem pkgCRegressionHallRestoration) = 2 :=
  by decide

/-- A singletonized system takes the other total branch without consulting a
    restoration list. -/
example : pkgCRegressionOutcomeTag
    (classifyTerminalPkgCSeparatingConsumers
      pkgCRegressionSingletonSystem pkgCRegressionMatchedRestoration) = 0 :=
  by decide

example :
    pkgCRegressionSeparatingSystem.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair pkgCRegressionSeparatingSystem,
        TerminalPkgCExactCoordinateCoverage
            pkgCRegressionMatchedRestoration pair ∨
          ∃ deficit : TerminalBN5HallDeficit
              (pair.quotientUnits pkgCRegressionMatchedRestoration)
              (pkgCRegressionMatchedRestoration.fullRestorations pair),
            deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
              deficit.neighborShadows.length < deficit.fullSubset.length :=
  terminalPkgC_separatingConsumers_restorationDichotomy
    pkgCRegressionSeparatingSystem pkgCRegressionMatchedRestoration

#print axioms firstTerminalPkgCSeparatingPair?_eq_none_iff
#print axioms TerminalPkgCSeparatingPair.quotientUnits_nonempty
#print axioms terminalPkgC_restorationEdge_preservesCoordinate
#print axioms terminalPkgC_separatingConsumers_restorationDichotomy

end DirectWire
end PNP
