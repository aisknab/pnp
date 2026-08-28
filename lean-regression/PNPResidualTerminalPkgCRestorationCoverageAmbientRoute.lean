import PNP.ResidualTerminalPkgCRestorationCoverageAmbientRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace ResidualTerminalPkgCRestorationCoverageAmbientRouteRegression

abbrev CoverageAtom := Fin 4
abbrev CoverageCoordinate := TerminalBN5ShadowCoordinate CoverageAtom Nat Nat
  Nat Nat Nat Nat Nat

def coverageSystem : TerminalV54ConsumerSystem CoverageAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def singletonizedSystem : TerminalV54ConsumerSystem CoverageAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [1]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def coveragePair : TerminalPkgCSeparatingPair coverageSystem :=
  terminalPkgCSeparatingPairOfFound coverageSystem [0, 1] [2] (by decide)

def coverageKey : TerminalBN4ActivationKey CoverageAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def coverageCoordinate (atom : CoverageAtom) : CoverageCoordinate :=
  { key := coverageKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

/-- The covered universe contains exactly one coordinate occurrence for every
    canonical quotient-unit occurrence. -/
def coveredRestoration :
    TerminalPkgCRestorationUniverse CoverageAtom CoverageCoordinate where
  coordinateOf := coverageCoordinate
  fullRestorationCoordinates := fun left right =>
    (left ++ right).map coverageCoordinate

/-- The empty full-restoration universe forces an exact Hall deficit for the
    first canonical quotient coordinate. -/
def deficientRestoration :
    TerminalPkgCRestorationUniverse CoverageAtom CoverageCoordinate where
  coordinateOf := coverageCoordinate
  fullRestorationCoordinates := fun _left _right => []

def coverageRemainder :
    List (TerminalBN4ActivationCell CoverageAtom Nat Nat) :=
  [{ key := { atom := 0, semanticSignature := 31, transportType := 37 }
     sign := .positive
     mass := 5 },
   { key := { atom := 0, semanticSignature := 31, transportType := 37 }
     sign := .negative
     mass := 1 }]

def coverageReorderedAmbient :
    List (TerminalBN4ActivationCell CoverageAtom Nat Nat) :=
  coverageRemainder ++
    (coveragePair.restorationCoverageCancellationCells
      coveredRestoration).reverse

def coverageDeficientAmbient :
    List (TerminalBN4ActivationCell CoverageAtom Nat Nat) :=
  (coveragePair.restorationCoverageCancellationCells
    coveredRestoration).tail

private def routeOutcomeTag
    {system : TerminalV54ConsumerSystem CoverageAtom}
    {restoration : TerminalPkgCRestorationUniverse CoverageAtom
      CoverageCoordinate}
    {ambient : List (TerminalBN4ActivationCell CoverageAtom Nat Nat)} :
    TerminalPkgCRestorationCoverageAmbientBN4RouteOutcome system restoration
      ambient -> Nat
  | .singletonized _ => 0
  | .hallRoute _ _ => 1
  | .reduced _ _ _ _ _ => 2
  | .ambientMismatch _ _ _ _ _ => 3

example :
    (coveragePair.restorationCoverageCancellationCells
      coveredRestoration).length =
      2 * (coveragePair.left.length + coveragePair.right.length) :=
  coveragePair.restorationCoverageCancellationCells_length coveredRestoration

/-- All quotient coordinates share one nested key in this fixture, so the
    generated subledger deliberately contains duplicate cells. -/
example : ¬ (coveragePair.restorationCoverageCancellationCells
    coveredRestoration).Nodup := by
  decide

example : routeOutcomeTag
    (classifyTerminalPkgCRestorationCoverageAmbientBN4Route
      singletonizedSystem coveredRestoration []) = 0 := by
  decide

example : routeOutcomeTag
    (classifyTerminalPkgCRestorationCoverageAmbientBN4Route
      coverageSystem deficientRestoration []) = 1 := by
  decide

/-- A permuted ambient ledger with duplicate generated cells returns the
    computed remainder and exact residual reduction. -/
example : routeOutcomeTag
    (classifyTerminalPkgCRestorationCoverageAmbientBN4Route
      coverageSystem coveredRestoration coverageReorderedAmbient) = 2 := by
  decide

/-- Removing one generated occurrence is detected as an exact multiplicity
    failure. -/
example : routeOutcomeTag
    (classifyTerminalPkgCRestorationCoverageAmbientBN4Route
      coverageSystem coveredRestoration coverageDeficientAmbient) = 3 := by
  decide

example : exists pair : TerminalPkgCSeparatingPair coverageSystem,
    Nonempty (TerminalPkgCRestorationCoverageCancellationRealization pair
      coveredRestoration) ∧
    exists remainder,
      exists embedding :
        TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          coveredRestoration coverageReorderedAmbient remainder,
        Nonempty
          (TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
            embedding) := by
  generalize classified :
      classifyTerminalPkgCRestorationCoverageAmbientBN4Route coverageSystem
        coveredRestoration coverageReorderedAmbient = outcome
  have reduced : routeOutcomeTag outcome = 2 := by
    rw [← classified]
    decide
  cases outcome with
  | singletonized proof =>
      change 0 = 2 at reduced
      omega
  | hallRoute pair deficit =>
      change 1 = 2 at reduced
      omega
  | reduced pair realization remainder embedding reduction =>
      exact ⟨pair, ⟨realization⟩, remainder, embedding, ⟨reduction⟩⟩
  | ambientMismatch pair realization cell generatedMember noExactEmbedding =>
      change 3 = 2 at reduced
      omega

example : exists pair : TerminalPkgCSeparatingPair coverageSystem,
    exists cell,
      cell ∈ pair.restorationCoverageCancellationCells coveredRestoration ∧
      forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          coveredRestoration coverageDeficientAmbient remainder := by
  generalize classified :
      classifyTerminalPkgCRestorationCoverageAmbientBN4Route coverageSystem
        coveredRestoration coverageDeficientAmbient = outcome
  have missing : routeOutcomeTag outcome = 3 := by
    rw [← classified]
    decide
  cases outcome with
  | singletonized proof =>
      change 0 = 3 at missing
      omega
  | hallRoute pair deficit =>
      change 1 = 3 at missing
      omega
  | reduced pair realization remainder embedding reduction =>
      change 2 = 3 at missing
      omega
  | ambientMismatch pair realization cell generatedMember noExactEmbedding =>
      exact ⟨pair, cell, generatedMember, noExactEmbedding⟩

example : coverageSystem.DisjointPairsSingletonized ∨
    exists pair : TerminalPkgCSeparatingPair coverageSystem,
      (exists deficit : TerminalBN5HallDeficit
          (pair.quotientUnits coveredRestoration)
          (coveredRestoration.fullRestorations pair),
        deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
          deficit.neighborShadows.length < deficit.fullSubset.length) ∨
      Nonempty
          (TerminalPkgCRestorationCoverageCancellationRealization pair
            coveredRestoration) ∧
        ((exists remainder,
            exists embedding :
              TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                coveredRestoration coverageReorderedAmbient remainder,
              Nonempty
                (TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
                  embedding)) ∨
          exists cell,
            cell ∈ pair.restorationCoverageCancellationCells
              coveredRestoration ∧
            forall remainder,
              ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                coveredRestoration coverageReorderedAmbient remainder) :=
  terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete
    coverageSystem coveredRestoration coverageReorderedAmbient

#print axioms terminalPkgCRestorationCoverageCancellationCellsForUnits_balanced
#print axioms TerminalPkgCSeparatingPair.restorationCoverageCancellationRealization
#print axioms classifyTerminalPkgCRestorationCoverageAmbientBN4Route
#print axioms terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete

end ResidualTerminalPkgCRestorationCoverageAmbientRouteRegression
end DirectWire
end PNP
