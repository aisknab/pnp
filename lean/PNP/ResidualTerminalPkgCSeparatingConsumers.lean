/-
Copyright (c) 2026 PNP Labs.

Constructive finite reconstruction of the pinned manuscript's PkgC
separating-consumer restoration dichotomy.  An arbitrary finite minimal-
consumer system is scanned in canonical list order for the first disjoint pair
that is not singleton-singleton.  If no such pair exists, the exact
singletonization premise consumed by V54 is proved.

For a found pair, every participating quotient atom is canonically indexed
and mapped to one exact restoration coordinate.  An explicit finite full-
restoration universe is then classified by the existing BN5 equality-fibre
matcher.  The result is either complete exact-coordinate multiplicity coverage
or a proof-bearing strict Hall deficit with a deterministic local Q route.  No
edge can change a BN5 coordinate, so the nested BN4 activation key and every
frontier, charge-owner, obligation, origin/kernel, and mode-projection field
are preserved when that exact coordinate type is used.

The full-restoration coordinate universe remains explicit input.  Complete
coverage is not connected back to a BN4/BN5 contradiction, Hall routes are not
embedded into the complete global outcome system, and route silence is not
proved.  This module does not derive consumers or restorations from a terminal
candidate, establish full PkgC, BN6, selector or realizer completeness, prove
polynomial generation or runtime, ZeroSlack or PCCMin, put SAT in P, remove a
project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalConsumerAntichainNormalForm

namespace PNP
namespace DirectWire

/-! ## Canonical separating-pair scan -/

/-- Executable recognition of a singleton finite consumer. -/
def terminalPkgCConsumerIsSingleton {Atom : Type} : List Atom -> Bool
  | [_] => true
  | _ => false

theorem terminalPkgCConsumerIsSingleton_eq_true_iff
    {Atom : Type} (consumer : List Atom) :
    terminalPkgCConsumerIsSingleton consumer = true ↔
      ∃ atom, consumer = [atom] := by
  cases consumer with
  | nil => simp [terminalPkgCConsumerIsSingleton]
  | cons head tail =>
      cases tail with
      | nil => simp [terminalPkgCConsumerIsSingleton]
      | cons second rest => simp [terminalPkgCConsumerIsSingleton]

/-- Executable extensional disjointness for two finite consumers. -/
def terminalPkgCDisjointBool
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) : Bool :=
  left.all fun atom => decide (atom ∉ right)

theorem terminalPkgCDisjointBool_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) :
    terminalPkgCDisjointBool left right = true ↔
      TerminalV54Disjoint left right := by
  simp [terminalPkgCDisjointBool, TerminalV54Disjoint]

/-- Every ordered pair of listed minimal consumers, in canonical nested list
    order. -/
def terminalPkgCConsumerPairs
    {Atom : Type} (system : TerminalV54ConsumerSystem Atom) :
    List (List Atom × List Atom) :=
  system.consumers.flatMap fun left =>
    system.consumers.map fun right => (left, right)

theorem mem_terminalPkgCConsumerPairs_iff
    {Atom : Type} (system : TerminalV54ConsumerSystem Atom)
    (left right : List Atom) :
    (left, right) ∈ terminalPkgCConsumerPairs system ↔
      left ∈ system.consumers ∧ right ∈ system.consumers := by
  simp [terminalPkgCConsumerPairs]

/-- A pair needs PkgC restoration exactly when it is disjoint and at least one
    side is not a singleton. -/
def terminalPkgCPairNeedsRestoration
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) : Bool :=
  terminalPkgCDisjointBool left right &&
    !(terminalPkgCConsumerIsSingleton left &&
      terminalPkgCConsumerIsSingleton right)

theorem terminalPkgCPairNeedsRestoration_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) :
    terminalPkgCPairNeedsRestoration left right = true ↔
      TerminalV54Disjoint left right ∧
        ¬ ∃ leftAtom rightAtom,
          left = [leftAtom] ∧ right = [rightAtom] := by
  constructor
  · intro needsRestoration
    cases disjointCheck : terminalPkgCDisjointBool left right with
    | false =>
        simp [terminalPkgCPairNeedsRestoration, disjointCheck] at needsRestoration
    | true =>
        have disjoint :=
          (terminalPkgCDisjointBool_eq_true_iff left right).1 disjointCheck
        cases leftCheck : terminalPkgCConsumerIsSingleton left with
        | false =>
            refine ⟨disjoint, ?_⟩
            rintro ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩
            have leftSingleton :
                terminalPkgCConsumerIsSingleton left = true :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff left).2
                ⟨leftAtom, leftEqual⟩
            exact Bool.noConfusion (leftCheck.symm.trans leftSingleton)
        | true =>
            cases rightCheck : terminalPkgCConsumerIsSingleton right with
            | false =>
                refine ⟨disjoint, ?_⟩
                rintro ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩
                have rightSingleton :
                    terminalPkgCConsumerIsSingleton right = true :=
                  (terminalPkgCConsumerIsSingleton_eq_true_iff right).2
                    ⟨rightAtom, rightEqual⟩
                exact Bool.noConfusion
                  (rightCheck.symm.trans rightSingleton)
            | true =>
                simp [terminalPkgCPairNeedsRestoration, disjointCheck,
                  leftCheck, rightCheck] at needsRestoration
  · rintro ⟨disjoint, nonsingleton⟩
    have disjointCheck : terminalPkgCDisjointBool left right = true :=
      (terminalPkgCDisjointBool_eq_true_iff left right).2 disjoint
    cases leftCheck : terminalPkgCConsumerIsSingleton left with
    | false =>
        simp [terminalPkgCPairNeedsRestoration, disjointCheck, leftCheck]
    | true =>
        cases rightCheck : terminalPkgCConsumerIsSingleton right with
        | false =>
            simp [terminalPkgCPairNeedsRestoration, disjointCheck,
              leftCheck, rightCheck]
        | true =>
            obtain ⟨leftAtom, leftEqual⟩ :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff left).1 leftCheck
            obtain ⟨rightAtom, rightEqual⟩ :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff right).1 rightCheck
            exact False.elim
              (nonsingleton ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩)

/-- The first nonsingleton disjoint pair in canonical consumer-pair order. -/
def firstTerminalPkgCSeparatingPair?
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV54ConsumerSystem Atom) :
    Option (List Atom × List Atom) :=
  (terminalPkgCConsumerPairs system).find? fun pair =>
    terminalPkgCPairNeedsRestoration pair.1 pair.2

/-- A proof-bearing PkgC separating pair.  Membership, disjointness, and the
    nonsingleton condition come from the executable scan. -/
structure TerminalPkgCSeparatingPair
    {Atom : Type} (system : TerminalV54ConsumerSystem Atom) where
  left : List Atom
  right : List Atom
  leftMember : left ∈ system.consumers
  rightMember : right ∈ system.consumers
  disjoint : TerminalV54Disjoint left right
  nonsingleton : ¬ ∃ leftAtom rightAtom,
    left = [leftAtom] ∧ right = [rightAtom]

/-- Turn a successful canonical scan into its proof-bearing separating pair. -/
def terminalPkgCSeparatingPairOfFound
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV54ConsumerSystem Atom)
    (left right : List Atom)
    (found : firstTerminalPkgCSeparatingPair? system = some (left, right)) :
    TerminalPkgCSeparatingPair system := by
  unfold firstTerminalPkgCSeparatingPair? at found
  have pairMember :
      (left, right) ∈ terminalPkgCConsumerPairs system :=
    List.mem_of_find?_eq_some found
  have needsRestoration :
      terminalPkgCPairNeedsRestoration left right = true :=
    by simpa using List.find?_some found
  have members :=
    (mem_terminalPkgCConsumerPairs_iff system left right).1 pairMember
  have conditions :=
    (terminalPkgCPairNeedsRestoration_eq_true_iff left right).1
      needsRestoration
  exact
    { left := left
      right := right
      leftMember := members.1
      rightMember := members.2
      disjoint := conditions.1
      nonsingleton := conditions.2 }

theorem firstTerminalPkgCSeparatingPair?_sound
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV54ConsumerSystem Atom)
    (left right : List Atom)
    (found : firstTerminalPkgCSeparatingPair? system = some (left, right)) :
    Nonempty (TerminalPkgCSeparatingPair system) :=
  ⟨terminalPkgCSeparatingPairOfFound system left right found⟩

/-- Absence of a restoration pair is exactly the PkgC singletonization premise
    consumed by V54. -/
theorem firstTerminalPkgCSeparatingPair?_eq_none_iff
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV54ConsumerSystem Atom) :
    firstTerminalPkgCSeparatingPair? system = none ↔
      system.DisjointPairsSingletonized := by
  constructor
  · intro noneFound left leftMember right rightMember disjoint
    have impossibleFound :
        (¬ ∃ leftAtom rightAtom,
          left = [leftAtom] ∧ right = [rightAtom]) ->
        ∃ leftAtom rightAtom,
          left = [leftAtom] ∧ right = [rightAtom] := by
      intro nonsingleton
      have pairMember :
          (left, right) ∈ terminalPkgCConsumerPairs system :=
        (mem_terminalPkgCConsumerPairs_iff system left right).2
          ⟨leftMember, rightMember⟩
      have needsRestoration :
          terminalPkgCPairNeedsRestoration left right = true :=
        (terminalPkgCPairNeedsRestoration_eq_true_iff left right).2
          ⟨disjoint, nonsingleton⟩
      have isSome : (firstTerminalPkgCSeparatingPair? system).isSome = true := by
        unfold firstTerminalPkgCSeparatingPair?
        exact (List.find?_isSome).2
          ⟨(left, right), pairMember, needsRestoration⟩
      rw [noneFound] at isSome
      exact False.elim (Bool.noConfusion isSome)
    cases leftCheck : terminalPkgCConsumerIsSingleton left with
    | false =>
        apply impossibleFound
        rintro ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩
        have singletonCheck : terminalPkgCConsumerIsSingleton left = true :=
          (terminalPkgCConsumerIsSingleton_eq_true_iff left).2
            ⟨leftAtom, leftEqual⟩
        exact Bool.noConfusion (leftCheck.symm.trans singletonCheck)
    | true =>
        cases rightCheck : terminalPkgCConsumerIsSingleton right with
        | false =>
            apply impossibleFound
            rintro ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩
            have singletonCheck :
                terminalPkgCConsumerIsSingleton right = true :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff right).2
                ⟨rightAtom, rightEqual⟩
            exact Bool.noConfusion (rightCheck.symm.trans singletonCheck)
        | true =>
            obtain ⟨leftAtom, leftEqual⟩ :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff left).1 leftCheck
            obtain ⟨rightAtom, rightEqual⟩ :=
              (terminalPkgCConsumerIsSingleton_eq_true_iff right).1 rightCheck
            exact ⟨leftAtom, rightAtom, leftEqual, rightEqual⟩
  · intro singletonized
    cases found : firstTerminalPkgCSeparatingPair? system with
    | none => rfl
    | some pair =>
        rcases pair with ⟨left, right⟩
        let separating :=
          terminalPkgCSeparatingPairOfFound system left right found
        exact False.elim (separating.nonsingleton
          (singletonized separating.left separating.leftMember
            separating.right separating.rightMember separating.disjoint))

/-! ## Exact-coordinate restoration universe -/

/-- Explicit finite full-restoration data for every consumer pair.  Quotient
    units are not caller supplied: they are generated from the pair's atoms and
    `coordinateOf`. -/
structure TerminalPkgCRestorationUniverse
    (Atom Coordinate : Type) where
  coordinateOf : Atom -> Coordinate
  fullRestorationCoordinates : List Atom -> List Atom -> List Coordinate

/-- Canonical quotient units participating in one separating pair. -/
def TerminalPkgCSeparatingPair.quotientUnits
    {Atom Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    List (TerminalBN5FullUnit Coordinate) :=
  terminalBN5IndexFullUnitsFrom 0
    ((pair.left ++ pair.right).map restoration.coordinateOf)

theorem TerminalPkgCSeparatingPair.quotientUnits_length
    {Atom Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    (pair.quotientUnits restoration).length =
      pair.left.length + pair.right.length := by
  unfold TerminalPkgCSeparatingPair.quotientUnits
  rw [terminalBN5IndexFullUnitsFrom_length]
  simp

/-- A separating pair always contributes at least one canonical quotient unit;
    complete coverage is therefore not a vacuous empty-domain result. -/
theorem TerminalPkgCSeparatingPair.quotientUnits_nonempty
    {Atom Coordinate : Type}
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    pair.quotientUnits restoration ≠ [] := by
  intro empty
  have leftNonempty := system.consumerNonempty pair.left pair.leftMember
  cases leftShape : pair.left with
  | nil => exact False.elim (leftNonempty leftShape)
  | cons head tail =>
      unfold TerminalPkgCSeparatingPair.quotientUnits at empty
      simp [leftShape, terminalBN5IndexFullUnitsFrom] at empty

/-- Canonically indexed full-restoration candidates for one pair. -/
def TerminalPkgCRestorationUniverse.fullRestorations
    {Atom Coordinate : Type}
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate)
    {system : TerminalV54ConsumerSystem Atom}
    (pair : TerminalPkgCSeparatingPair system) :
    List (TerminalBN5QuotientShadow Coordinate) :=
  terminalBN5QuotientShadows
    (restoration.fullRestorationCoordinates pair.left pair.right)

/-- Exact-coordinate multiplicity coverage is the finite PkgC matching
    boundary. -/
def TerminalPkgCExactCoordinateCoverage
    {Atom Coordinate : Type} [DecidableEq Coordinate]
    {system : TerminalV54ConsumerSystem Atom}
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate)
    (pair : TerminalPkgCSeparatingPair system) : Prop :=
  TerminalBN5CompleteMultiplicityMatching
    (pair.quotientUnits restoration) (restoration.fullRestorations pair)

/-- Every restoration edge preserves the whole exact coordinate literally. -/
theorem terminalPkgC_restorationEdge_preservesCoordinate
    {Coordinate : Type}
    (unit : TerminalBN5FullUnit Coordinate)
    (restoration : TerminalBN5QuotientShadow Coordinate)
    (edge : TerminalBN5ShadowEdge unit restoration) :
    unit.coordinate = restoration.coordinate :=
  edge

/-! ## Total restoration dichotomy -/

/-- The local PkgC route justified by a strict full-restoration Hall deficit. -/
inductive TerminalPkgCNamedLocalRoute where
  | qRestorationHall
deriving DecidableEq, Repr

def TerminalBN5HallDeficit.pkgCNamedLocalRoute
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {restorations : List (TerminalBN5QuotientShadow Coordinate)}
    (_ : TerminalBN5HallDeficit fullUnits restorations) :
    TerminalPkgCNamedLocalRoute :=
  .qRestorationHall

theorem TerminalBN5HallDeficit.pkgCRestorationNotSilent
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {restorations : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits restorations) :
    deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
      deficit.neighborShadows.length < deficit.fullSubset.length :=
  ⟨rfl, deficit.neighbor_card_lt_full_card⟩

/-- Total finite PkgC outcome: V54's premise already holds, or the first
    nonsingleton disjoint pair is completely restored or Hall-localized. -/
inductive TerminalPkgCSeparatingConsumersOutcome
    {Atom Coordinate : Type} [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) where
  | singletonized (proof : system.DisjointPairsSingletonized)
  | restored
      (pair : TerminalPkgCSeparatingPair system)
      (coverage : TerminalPkgCExactCoordinateCoverage restoration pair)
  | localized
      (pair : TerminalPkgCSeparatingPair system)
      (deficit : TerminalBN5HallDeficit
        (pair.quotientUnits restoration) (restoration.fullRestorations pair))

/-- Execute the first separating-pair scan and then the exact-coordinate BN5
    matcher on that pair's restoration universe. -/
def classifyTerminalPkgCSeparatingConsumers
    {Atom Coordinate : Type} [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    TerminalPkgCSeparatingConsumersOutcome system restoration :=
  match found : firstTerminalPkgCSeparatingPair? system with
  | none => .singletonized
      ((firstTerminalPkgCSeparatingPair?_eq_none_iff system).1 found)
  | some rawPair =>
      let pair : TerminalPkgCSeparatingPair system :=
        terminalPkgCSeparatingPairOfFound system rawPair.1 rawPair.2
          found
      match classifyTerminalBN5ShadowMatching
          (pair.quotientUnits restoration)
          (restoration.fullRestorations pair) with
      | .matched coverage => .restored pair coverage
      | .hallDeficit deficit => .localized pair deficit

/-- Manuscript PkgC separating-consumer restoration dichotomy over an
    arbitrary finite consumer system and explicit exact-coordinate restoration
    universe. -/
theorem terminalPkgC_separatingConsumers_restorationDichotomy
    {Atom Coordinate : Type} [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    system.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair system,
        TerminalPkgCExactCoordinateCoverage restoration pair ∨
          ∃ deficit : TerminalBN5HallDeficit
              (pair.quotientUnits restoration)
              (restoration.fullRestorations pair),
            deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
              deficit.neighborShadows.length < deficit.fullSubset.length := by
  cases classifyTerminalPkgCSeparatingConsumers system restoration with
  | singletonized proof => exact Or.inl proof
  | restored pair coverage => exact Or.inr ⟨pair, Or.inl coverage⟩
  | localized pair deficit =>
      exact Or.inr ⟨pair, Or.inr ⟨deficit,
        deficit.pkgCRestorationNotSilent⟩⟩

/-- No fourth unclassified PkgC result exists. -/
theorem classifyTerminalPkgCSeparatingConsumers_exhaustive
    {Atom Coordinate : Type} [DecidableEq Atom] [DecidableEq Coordinate]
    (system : TerminalV54ConsumerSystem Atom)
    (restoration : TerminalPkgCRestorationUniverse Atom Coordinate) :
    Nonempty (TerminalPkgCSeparatingConsumersOutcome system restoration) :=
  ⟨classifyTerminalPkgCSeparatingConsumers system restoration⟩

end DirectWire
end PNP
