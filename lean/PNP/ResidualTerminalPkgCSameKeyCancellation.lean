/-
Copyright (c) 2026 PNP Labs.

Finite reconstruction of the next edge in the pinned manuscript's PkgC
separating-consumer argument.  The preceding typed-restoration theorem
materializes one full candidate for every quotient atom and proves exact BN5
coordinate preservation.  Here those paired values are converted into an
opposite-sign BN4 ledger: each quotient atom contributes one positive cell and
its restored full candidate contributes one negative cell.  Because equality
of the complete BN5 coordinate includes equality of its nested BN4 key, every
BN4 key balances exactly and its canonical residual list is empty.

The carrier, consumer antichain, typed restorer, and complete coordinate maps
remain arbitrary finite inputs.  In particular, this module still does not
construct the semantic full-restoration operation from a terminal candidate.
It does not embed Hall or cancellation outcomes into the complete global route
system, derive global route silence, construct the complete manuscript PkgC or
BN6 pipeline, prove polynomial runtime, ZeroSlack or PCCMin, put SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPkgCTypedRestoration

namespace PNP
namespace DirectWire

/-! ## Canonical opposite-sign restoration cells -/

/-- One quotient atom and its typed full restoration become opposite-sign BN4
    unit cells.  The quotient coordinate supplies the positive key; the full
    candidate's complete coordinate supplies the negative key. -/
def terminalPkgCRestorationCancellationCellsForAtom
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atom : ConsumerAtom) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  [{ key := (restorer.quotientCoordinate atom).key
     sign := .positive
     mass := 1 },
   { key := (restorer.fullCoordinate (restorer.restore atom)).key
     sign := .negative
     mass := 1 }]

/-- Exact BN5 coordinate preservation forces the two generated unit cells to
    have the same nested BN4 activation key. -/
theorem terminalPkgCRestorationCancellationCellsForAtom_key_eq
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atom : ConsumerAtom) :
    (restorer.fullCoordinate (restorer.restore atom)).key =
      (restorer.quotientCoordinate atom).key :=
  congrArg TerminalBN5ShadowCoordinate.key
    (restorer.restore_preserves_coordinate atom)

/-- A single quotient/restoration pair contributes equal positive and negative
    mass at every BN4 key. -/
theorem terminalPkgCRestorationCancellationCellsForAtom_balanced
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atom : ConsumerAtom)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass
        (terminalPkgCRestorationCancellationCellsForAtom restorer atom) key =
      terminalBN4NegativeMass
        (terminalPkgCRestorationCancellationCellsForAtom restorer atom) key := by
  have keyEqual :=
    terminalPkgCRestorationCancellationCellsForAtom_key_eq restorer atom
  simp [terminalPkgCRestorationCancellationCellsForAtom,
    terminalBN4PositiveMass, terminalBN4NegativeMass, keyEqual]

/-- Concatenate the paired unit cells for an arbitrary finite atom list. -/
def terminalPkgCRestorationCancellationCellsForAtoms
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atoms : List ConsumerAtom) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  atoms.flatMap
    (terminalPkgCRestorationCancellationCellsForAtom restorer)

theorem terminalPkgCRestorationCancellationCellsForAtoms_length
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atoms : List ConsumerAtom) :
    (terminalPkgCRestorationCancellationCellsForAtoms restorer atoms).length =
      2 * atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      change
        (terminalPkgCRestorationCancellationCellsForAtom restorer atom ++
          terminalPkgCRestorationCancellationCellsForAtoms restorer tail).length =
            2 * (atom :: tail).length
      rw [List.length_append, ih]
      simp [terminalPkgCRestorationCancellationCellsForAtom]
      omega

theorem terminalBN4PositiveMass_append
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    terminalBN4PositiveMass (left ++ right) key =
      terminalBN4PositiveMass left key +
        terminalBN4PositiveMass right key := by
  simp [terminalBN4PositiveMass]

theorem terminalBN4NegativeMass_append
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    terminalBN4NegativeMass (left ++ right) key =
      terminalBN4NegativeMass left key +
        terminalBN4NegativeMass right key := by
  simp [terminalBN4NegativeMass]

/-- Positionwise exact restoration yields multiplicity balance at every BN4
    key for an arbitrary finite atom list. -/
theorem terminalPkgCRestorationCancellationCellsForAtoms_balanced
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (atoms : List ConsumerAtom)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass
        (terminalPkgCRestorationCancellationCellsForAtoms restorer atoms) key =
      terminalBN4NegativeMass
        (terminalPkgCRestorationCancellationCellsForAtoms restorer atoms) key := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      rw [show terminalPkgCRestorationCancellationCellsForAtoms restorer
          (atom :: tail) =
            terminalPkgCRestorationCancellationCellsForAtom restorer atom ++
              terminalPkgCRestorationCancellationCellsForAtoms restorer tail
        from rfl]
      rw [terminalBN4PositiveMass_append, terminalBN4NegativeMass_append,
        terminalPkgCRestorationCancellationCellsForAtom_balanced, ih]

/-! ## Separating-pair cancellation -/

/-- The canonical BN4 ledger generated from the atoms of one separating pair. -/
def TerminalPkgCSeparatingPair.restorationCancellationCells
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  terminalPkgCRestorationCancellationCellsForAtoms restorer
    (pair.left ++ pair.right)

theorem TerminalPkgCSeparatingPair.restorationCancellationCells_length
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    (pair.restorationCancellationCells restorer).length =
      2 * (pair.left.length + pair.right.length) := by
  rw [TerminalPkgCSeparatingPair.restorationCancellationCells,
    terminalPkgCRestorationCancellationCellsForAtoms_length]
  simp

theorem TerminalPkgCSeparatingPair.restorationCancellation_balanced
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass (pair.restorationCancellationCells restorer) key =
      terminalBN4NegativeMass
        (pair.restorationCancellationCells restorer) key :=
  terminalPkgCRestorationCancellationCellsForAtoms_balanced restorer
    (pair.left ++ pair.right) key

/-- A balanced generated ledger has no canonical BN4 residual at any key. -/
theorem TerminalPkgCSeparatingPair.restorationCancellation_residualCells_empty
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    TerminalBN4KeyCancellation.residualCells
      (terminalBN4CancelAtKey (pair.restorationCancellationCells restorer) key)
        key = [] := by
  have balanced := pair.restorationCancellation_balanced restorer key
  simp [terminalBN4CancelAtKey, classifyTerminalBN4KeyCancellation, balanced,
    TerminalBN4KeyCancellation.residualCells]

/-- The generated signed integer ledger is exactly zero at every BN4 key. -/
theorem TerminalPkgCSeparatingPair.restorationCancellation_signedMass_zero
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4InputSignedMass
      (pair.restorationCancellationCells restorer) key = 0 := by
  unfold terminalBN4InputSignedMass
  rw [pair.restorationCancellation_balanced restorer key]
  omega

/-! ## Proof-bearing realization and no-cancellation consequence -/

/-- The preceding typed candidate realization together with the mechanically
    generated exact BN4 cancellation ledger for the same pair. -/
structure TerminalPkgCSameKeyCancellationRealization
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) where
  typedRealization : TerminalPkgCTypedRestorationRealization pair restorer
  cells : List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
    TransportType)
  canonical : cells = pair.restorationCancellationCells restorer
  cellCount : cells.length =
    2 * (pair.left.length + pair.right.length)
  balanced : ∀ key,
    terminalBN4PositiveMass cells key = terminalBN4NegativeMass cells key
  residualCellsEmpty : ∀ key,
    TerminalBN4KeyCancellation.residualCells
      (terminalBN4CancelAtKey cells key) key = []
  signedMassZero : ∀ key, terminalBN4InputSignedMass cells key = 0

/-- Construct the cancellation proof directly from the typed restorer; no
    cancellation result or mass equality is supplied by the caller. -/
def TerminalPkgCSeparatingPair.sameKeyCancellationRealization
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    TerminalPkgCSameKeyCancellationRealization pair restorer :=
  { typedRealization := pair.typedRestorationRealization restorer
    cells := pair.restorationCancellationCells restorer
    canonical := rfl
    cellCount := pair.restorationCancellationCells_length restorer
    balanced := pair.restorationCancellation_balanced restorer
    residualCellsEmpty :=
      pair.restorationCancellation_residualCells_empty restorer
    signedMassZero := pair.restorationCancellation_signedMass_zero restorer }

/-- Total PkgC outcome at this edge: either V54 singletonization already
    holds, or the first nonsingleton disjoint pair has typed exact-coordinate
    candidates whose opposite-sign BN4 ledger cancels at every key. -/
inductive TerminalPkgCSameKeyCancellationOutcome
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) where
  | singletonized (proof : system.DisjointPairsSingletonized)
  | cancelled
      (pair : TerminalPkgCSeparatingPair system)
      (realization : TerminalPkgCSameKeyCancellationRealization pair restorer)

/-- Execute the canonical separating-pair scan and construct the exact
    cancellation ledger when restoration is needed. -/
def classifyTerminalPkgCSameKeyCancellation
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    TerminalPkgCSameKeyCancellationOutcome system restorer :=
  match found : firstTerminalPkgCSeparatingPair? system with
  | none => .singletonized
      ((firstTerminalPkgCSeparatingPair?_eq_none_iff system).1 found)
  | some rawPair =>
      let pair := terminalPkgCSeparatingPairOfFound system
        rawPair.1 rawPair.2 found
      .cancelled pair (pair.sameKeyCancellationRealization restorer)

/-- The finite typed-restoration-to-cancellation theorem. -/
theorem terminalPkgC_typedRestoration_sameKeyCancellation
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    system.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair system,
        Nonempty (TerminalPkgCSameKeyCancellationRealization pair restorer) := by
  cases classifyTerminalPkgCSameKeyCancellation system restorer with
  | singletonized proof => exact Or.inl proof
  | cancelled pair realization => exact Or.inr ⟨pair, ⟨realization⟩⟩

/-- Exact local no-cancellation is the manuscript's no-outcome premise at this
    edge.  It is stated negatively, rather than as a caller-labelled truth
    field: every proof-bearing generated cancellation is excluded. -/
def TerminalPkgCSameKeyCancellationSilent
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) : Prop :=
  ∀ pair : TerminalPkgCSeparatingPair system,
    ¬ Nonempty (TerminalPkgCSameKeyCancellationRealization pair restorer)

/-- If the mechanically generated same-key cancellation outcome is silent,
    no nonsingleton disjoint consumer pair can remain; hence the exact V54
    singletonization premise follows. -/
theorem terminalPkgC_sameKeyCancellation_silence_singletonizes
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (silent : TerminalPkgCSameKeyCancellationSilent system restorer) :
    system.DisjointPairsSingletonized := by
  cases terminalPkgC_typedRestoration_sameKeyCancellation system restorer with
  | inl singletonized => exact singletonized
  | inr found =>
      obtain ⟨pair, realization⟩ := found
      exact False.elim (silent pair realization)

/-- No third unclassified result exists at the typed same-key cancellation
    boundary. -/
theorem classifyTerminalPkgCSameKeyCancellation_exhaustive
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    Nonempty (TerminalPkgCSameKeyCancellationOutcome system restorer) :=
  ⟨classifyTerminalPkgCSameKeyCancellation system restorer⟩

end DirectWire
end PNP
