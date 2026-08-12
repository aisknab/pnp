/-
Copyright (c) 2026 PNP Labs.

Typed finite realization of the PkgC restoration branch.  The preceding
PkgC classifier retains only exact restoration coordinates.  This module
accepts a typed restoration operation, materializes one full candidate for
every quotient atom in the canonical separating pair, and proves that the
resulting coordinate universe has complete multiplicity coverage.

The restoration operation and its coordinate-preservation proof remain
explicit inputs.  No semantic construction of that operation from a terminal
candidate is claimed.  The module does not connect complete restoration to a
BN4 or BN5 contradiction, embed local routes into the global outcome system,
prove route silence, polynomial runtime, ZeroSlack or PCCMin, put SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPkgCSeparatingConsumers

namespace PNP
namespace DirectWire

/-! ## Typed restoration data -/

/-- A typed full-restoration operation.  Each quotient atom is sent to an
    actual value of `FullCandidate`, and the complete restoration coordinate
    is preserved literally. -/
structure TerminalPkgCTypedRestorer
    (Atom FullCandidate Coordinate : Type) where
  quotientCoordinate : Atom -> Coordinate
  restore : Atom -> FullCandidate
  fullCoordinate : FullCandidate -> Coordinate
  restore_preserves_coordinate : forall atom,
    fullCoordinate (restore atom) = quotientCoordinate atom

/-- The canonical full candidates realized for one separating pair. -/
def TerminalPkgCSeparatingPair.fullRestorationCandidates
    {Atom FullCandidate Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    List FullCandidate :=
  (pair.left ++ pair.right).map restorer.restore

theorem TerminalPkgCSeparatingPair.fullRestorationCandidates_length
    {Atom FullCandidate Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    (pair.fullRestorationCandidates restorer).length =
      pair.left.length + pair.right.length := by
  simp [TerminalPkgCSeparatingPair.fullRestorationCandidates]

/-- The realized full candidates preserve the quotient coordinate at every
    canonical list position. -/
theorem TerminalPkgCSeparatingPair.fullRestorationCandidates_coordinates
    {Atom FullCandidate Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    (pair.fullRestorationCandidates restorer).map restorer.fullCoordinate =
      (pair.left ++ pair.right).map restorer.quotientCoordinate := by
  simp only [TerminalPkgCSeparatingPair.fullRestorationCandidates,
    List.map_map]
  apply List.map_congr_left
  intro atom _member
  exact restorer.restore_preserves_coordinate atom

/-- Forget only the typed full-candidate payloads to obtain the coordinate
    universe consumed by the existing PkgC classifier. -/
def TerminalPkgCTypedRestorer.coordinateUniverse
    {Atom FullCandidate Coordinate : Type}
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    TerminalPkgCRestorationUniverse Atom Coordinate :=
  { coordinateOf := restorer.quotientCoordinate
    fullRestorationCoordinates := fun left right =>
      ((left ++ right).map restorer.restore).map restorer.fullCoordinate }

theorem TerminalPkgCTypedRestorer.coordinateUniverse_coordinates
    {Atom FullCandidate Coordinate : Type}
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate)
    (left right : List Atom) :
    restorer.coordinateUniverse.fullRestorationCoordinates left right =
      (left ++ right).map restorer.quotientCoordinate := by
  simp only [TerminalPkgCTypedRestorer.coordinateUniverse, List.map_map]
  apply List.map_congr_left
  intro atom _member
  exact restorer.restore_preserves_coordinate atom

/-! ## Exact multiplicity realization -/

/-- Coordinate multiplicity in an unindexed finite list. -/
def terminalPkgCCoordinateMultiplicity
    {Coordinate : Type} [DecidableEq Coordinate]
    (coordinates : List Coordinate) (coordinate : Coordinate) : Nat :=
  (coordinates.filter fun found => decide (found = coordinate)).length

theorem terminalBN5FullMultiplicity_indexed_eq
    {Coordinate : Type} [DecidableEq Coordinate]
    (start : Nat) (coordinates : List Coordinate) (coordinate : Coordinate) :
    terminalBN5FullMultiplicity
        (terminalBN5IndexFullUnitsFrom start coordinates) coordinate =
      terminalPkgCCoordinateMultiplicity coordinates coordinate := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons head tail ih =>
      by_cases equal : head = coordinate
      · have tailEquality := ih (start + 1)
        unfold terminalBN5FullMultiplicity
          terminalPkgCCoordinateMultiplicity at tailEquality
        simp [terminalBN5FullMultiplicity,
          terminalBN5IndexFullUnitsFrom,
          terminalPkgCCoordinateMultiplicity, equal, tailEquality]
      · have tailEquality := ih (start + 1)
        unfold terminalBN5FullMultiplicity
          terminalPkgCCoordinateMultiplicity at tailEquality
        simp [terminalBN5FullMultiplicity,
          terminalBN5IndexFullUnitsFrom,
          terminalPkgCCoordinateMultiplicity, equal, tailEquality]

theorem terminalBN5ShadowMultiplicity_indexed_eq
    {Coordinate : Type} [DecidableEq Coordinate]
    (start : Nat) (coordinates : List Coordinate) (coordinate : Coordinate) :
    terminalBN5ShadowMultiplicity
        (terminalBN5IndexQuotientShadowsFrom start coordinates) coordinate =
      terminalPkgCCoordinateMultiplicity coordinates coordinate := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons head tail ih =>
      by_cases equal : head = coordinate
      · have tailEquality := ih (start + 1)
        unfold terminalBN5ShadowMultiplicity
          terminalPkgCCoordinateMultiplicity at tailEquality
        simp [terminalBN5ShadowMultiplicity,
          terminalBN5IndexQuotientShadowsFrom,
          terminalPkgCCoordinateMultiplicity, equal, tailEquality]
      · have tailEquality := ih (start + 1)
        unfold terminalBN5ShadowMultiplicity
          terminalPkgCCoordinateMultiplicity at tailEquality
        simp [terminalBN5ShadowMultiplicity,
          terminalBN5IndexQuotientShadowsFrom,
          terminalPkgCCoordinateMultiplicity, equal, tailEquality]

/-- A typed restorer supplies exact multiplicity coverage for every
    separating pair, not merely an untyped list of restoration coordinates. -/
theorem TerminalPkgCSeparatingPair.typedRestoration_exactCoverage
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Coordinate]
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    TerminalPkgCExactCoordinateCoverage restorer.coordinateUniverse pair := by
  intro unit _member
  simp only [TerminalPkgCSeparatingPair.quotientUnits,
    TerminalPkgCRestorationUniverse.fullRestorations,
    terminalBN5QuotientShadows]
  rw [restorer.coordinateUniverse_coordinates]
  rw [terminalBN5FullMultiplicity_indexed_eq,
    terminalBN5ShadowMultiplicity_indexed_eq]
  simp [TerminalPkgCTypedRestorer.coordinateUniverse]

/-- Complete multiplicity coverage and a strict Hall deficit for the same
    finite equality-fibre graph are contradictory. -/
theorem terminalBN5CompleteMultiplicityMatching_not_hallDeficit
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (coverage : TerminalBN5CompleteMultiplicityMatching fullUnits shadows)
    (deficit : TerminalBN5HallDeficit fullUnits shadows) : False := by
  have covered := coverage deficit.fullUnit deficit.fullMember
  rw [deficit.fullCoordinate] at covered
  exact (Nat.not_lt_of_ge covered) deficit.strictDeficit

/-! ## Proof-bearing typed realization and total finite outcome -/

/-- Materialized typed full candidates and their exact-coordinate coverage
    for one separating pair. -/
structure TerminalPkgCTypedRestorationRealization
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Coordinate]
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) where
  fullCandidates : List FullCandidate
  canonical : fullCandidates = pair.fullRestorationCandidates restorer
  candidateCount : fullCandidates.length =
    pair.left.length + pair.right.length
  coordinates : fullCandidates.map restorer.fullCoordinate =
    (pair.left ++ pair.right).map restorer.quotientCoordinate
  exactCoverage :
    TerminalPkgCExactCoordinateCoverage restorer.coordinateUniverse pair

/-- Construct the typed realization directly from the supplied restorer. -/
def TerminalPkgCSeparatingPair.typedRestorationRealization
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Coordinate]
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    TerminalPkgCTypedRestorationRealization pair restorer :=
  { fullCandidates := pair.fullRestorationCandidates restorer
    canonical := rfl
    candidateCount := pair.fullRestorationCandidates_length restorer
    coordinates := pair.fullRestorationCandidates_coordinates restorer
    exactCoverage := pair.typedRestoration_exactCoverage restorer }

/-- With a typed restorer, the canonical first-pair scan has only two
    outcomes: V54 singletonization or a materialized full restoration. -/
inductive TerminalPkgCTypedRestorationOutcome
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) where
  | singletonized (proof : system.DisjointPairsSingletonized)
  | realized
      (pair : TerminalPkgCSeparatingPair system)
      (realization : TerminalPkgCTypedRestorationRealization pair restorer)

/-- Execute the same canonical separating-pair scan and materialize typed
    restorations whenever a pair is found. -/
def classifyTerminalPkgCTypedRestoration
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    TerminalPkgCTypedRestorationOutcome system restorer :=
  match found : firstTerminalPkgCSeparatingPair? system with
  | none => .singletonized
      ((firstTerminalPkgCSeparatingPair?_eq_none_iff system).1 found)
  | some rawPair =>
      let pair := terminalPkgCSeparatingPairOfFound system
        rawPair.1 rawPair.2 found
      .realized pair (pair.typedRestorationRealization restorer)

/-- The finite typed-restoration theorem.  The first separating pair is
    either absent, proving V54 singletonization, or has canonical typed full
    candidates with exact multiplicity coverage. -/
theorem terminalPkgC_typedRestoration_realization
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    system.DisjointPairsSingletonized ∨
      exists pair : TerminalPkgCSeparatingPair system,
        Nonempty (TerminalPkgCTypedRestorationRealization pair restorer) := by
  cases classifyTerminalPkgCTypedRestoration system restorer with
  | singletonized proof => exact Or.inl proof
  | realized pair realization => exact Or.inr ⟨pair, ⟨realization⟩⟩

/-- No third unclassified typed-restoration outcome exists. -/
theorem classifyTerminalPkgCTypedRestoration_exhaustive
    {Atom FullCandidate Coordinate : Type}
    [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate Coordinate) :
    Nonempty (TerminalPkgCTypedRestorationOutcome system restorer) :=
  ⟨classifyTerminalPkgCTypedRestoration system restorer⟩

end DirectWire
end PNP
