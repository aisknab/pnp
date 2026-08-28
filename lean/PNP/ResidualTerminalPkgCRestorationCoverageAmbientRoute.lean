/-
Copyright (c) 2026 PNP Labs.

Finite PkgC restoration-coverage classification at the ambient BN4 boundary.

The earlier finite restoration-universe classifier either proves that every
disjoint consumer pair is singletonized, returns complete exact-coordinate
coverage for the first nonsingleton pair, or retains an exact Hall deficit.
The typed-cancellation path instead accepts an always-total restorer and
therefore cannot expose that Hall branch. This module connects the general
finite classifier to BN4 without accepting a typed restorer: complete coverage
constructs one opposite-sign unit pair at the nested BN4 key of every canonical
quotient unit, while Hall failure remains the exact local Q route.

The constructed balanced subledger is then removed from an arbitrary-order
ambient BN4 ledger. The total result returns either the computed remainder and
exact residual reduction, or a generated cell together with proof that no exact
multiset embedding exists.

The consumer system, restoration-coordinate universe, and ambient ledger remain
explicit inputs. Coordinate coverage does not materialize semantic full
candidates or derive the restoration universe from terminal data. A Hall
deficit or ambient mismatch is not yet a globally ranked route, and an exact
reduction does not prove that the computed remainder is empty. This module does
not establish complete PkgC/BN3-BN6 integration, unconditional ZeroSlack,
polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute

namespace PNP
namespace DirectWire

/-! ## Coverage-derived opposite-sign BN4 cells -/

/-- One canonical quotient unit contributes an opposite-sign BN4 unit pair at
    the nested key of its complete restoration coordinate. -/
def terminalPkgCRestorationCoverageCancellationCellsForUnit
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    (unit : TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  [{ key := unit.coordinate.key
     sign := .positive
     mass := 1 },
   { key := unit.coordinate.key
     sign := .negative
     mass := 1 }]

/-- Concatenate the canonical opposite-sign pair for every quotient unit. -/
def terminalPkgCRestorationCoverageCancellationCellsForUnits
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    (units : List (TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  units.flatMap terminalPkgCRestorationCoverageCancellationCellsForUnit

theorem terminalPkgCRestorationCoverageCancellationCellsForUnits_length
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    (units : List (TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))) :
    (terminalPkgCRestorationCoverageCancellationCellsForUnits units).length =
      2 * units.length := by
  induction units with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (terminalPkgCRestorationCoverageCancellationCellsForUnit head ++
          terminalPkgCRestorationCoverageCancellationCellsForUnits tail
        ).length = 2 * (head :: tail).length
      rw [List.length_append, inductionHypothesis]
      simp [terminalPkgCRestorationCoverageCancellationCellsForUnit]
      omega

theorem terminalPkgCRestorationCoverageCancellationCellsForUnit_balanced
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (unit : TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass
        (terminalPkgCRestorationCoverageCancellationCellsForUnit unit) key =
      terminalBN4NegativeMass
        (terminalPkgCRestorationCoverageCancellationCellsForUnit unit) key := by
  simp [terminalPkgCRestorationCoverageCancellationCellsForUnit,
    terminalBN4PositiveMass, terminalBN4NegativeMass]

/-- The complete coordinate-coverage cancellation ledger balances at every
    nested BN4 key. -/
theorem terminalPkgCRestorationCoverageCancellationCellsForUnits_balanced
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (units : List (TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass
        (terminalPkgCRestorationCoverageCancellationCellsForUnits units) key =
      terminalBN4NegativeMass
        (terminalPkgCRestorationCoverageCancellationCellsForUnits units) key := by
  induction units with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [show
        terminalPkgCRestorationCoverageCancellationCellsForUnits
            (head :: tail) =
          terminalPkgCRestorationCoverageCancellationCellsForUnit head ++
            terminalPkgCRestorationCoverageCancellationCellsForUnits tail
        from rfl]
      rw [terminalBN4PositiveMass_append, terminalBN4NegativeMass_append,
        terminalPkgCRestorationCoverageCancellationCellsForUnit_balanced,
        inductionHypothesis]

/-- A separating pair's canonical quotient units determine the exact BN4
    cancellation subledger used after complete restoration coverage. -/
def TerminalPkgCSeparatingPair.restorationCoverageCancellationCells
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :=
  terminalPkgCRestorationCoverageCancellationCellsForUnits
    (pair.quotientUnits restoration)

theorem TerminalPkgCSeparatingPair.restorationCoverageCancellationCells_length
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    (pair.restorationCoverageCancellationCells restoration).length =
      2 * (pair.left.length + pair.right.length) := by
  rw [TerminalPkgCSeparatingPair.restorationCoverageCancellationCells,
    terminalPkgCRestorationCoverageCancellationCellsForUnits_length,
    pair.quotientUnits_length]

theorem TerminalPkgCSeparatingPair.restorationCoverageCancellation_balanced
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass
        (pair.restorationCoverageCancellationCells restoration) key =
      terminalBN4NegativeMass
        (pair.restorationCoverageCancellationCells restoration) key :=
  terminalPkgCRestorationCoverageCancellationCellsForUnits_balanced
    (pair.quotientUnits restoration) key

theorem TerminalPkgCSeparatingPair.restorationCoverageCancellation_residualCells_empty
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    (terminalBN4CancelAtKey
      (pair.restorationCoverageCancellationCells restoration) key
      ).residualCells key = [] := by
  have balanced :=
    pair.restorationCoverageCancellation_balanced restoration key
  simp [terminalBN4CancelAtKey, classifyTerminalBN4KeyCancellation, balanced,
    TerminalBN4KeyCancellation.residualCells]

theorem TerminalPkgCSeparatingPair.restorationCoverageCancellation_signedMass_zero
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4InputSignedMass
      (pair.restorationCoverageCancellationCells restoration) key = 0 := by
  unfold terminalBN4InputSignedMass
  rw [pair.restorationCoverageCancellation_balanced restoration key]
  omega

/-! ## Proof-bearing complete-coverage realization -/

/-- Complete finite coordinate coverage together with the mechanically
    constructed BN4 cancellation ledger. -/
structure TerminalPkgCRestorationCoverageCancellationRealization
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) where
  coverage : TerminalPkgCExactCoordinateCoverage restoration pair
  cells : List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
    TransportType)
  canonical : cells = pair.restorationCoverageCancellationCells restoration
  cellCount : cells.length = 2 * (pair.left.length + pair.right.length)
  balanced : forall key,
    terminalBN4PositiveMass cells key = terminalBN4NegativeMass cells key
  residualCellsEmpty : forall key,
    (terminalBN4CancelAtKey cells key).residualCells key = []
  signedMassZero : forall key, terminalBN4InputSignedMass cells key = 0

/-- Build the cancellation realization from exact coordinate coverage; no
    typed restorer or caller-provided cancellation result is accepted. -/
def TerminalPkgCSeparatingPair.restorationCoverageCancellationRealization
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (coverage : TerminalPkgCExactCoordinateCoverage restoration pair) :
    TerminalPkgCRestorationCoverageCancellationRealization pair
      restoration :=
  { coverage := coverage
    cells := pair.restorationCoverageCancellationCells restoration
    canonical := rfl
    cellCount := pair.restorationCoverageCancellationCells_length restoration
    balanced := pair.restorationCoverageCancellation_balanced restoration
    residualCellsEmpty :=
      pair.restorationCoverageCancellation_residualCells_empty restoration
    signedMassZero :=
      pair.restorationCoverageCancellation_signedMass_zero restoration }

/-! ## Exact ambient extraction and residual reduction -/

/-- Exact multiset embedding of the coverage-derived cancellation subledger in
    an arbitrary-order ambient BN4 ledger. -/
structure TerminalPkgCRestorationCoverageAmbientBN4Embedding
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) : Prop where
  exactDecomposition : ambient.Perm
    (pair.restorationCoverageCancellationCells restoration ++ remainder)

theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.positiveMass_decomposition
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass ambient key =
      terminalBN4PositiveMass
          (pair.restorationCoverageCancellationCells restoration) key +
        terminalBN4PositiveMass remainder key := by
  rw [terminalBN4PositiveMass_perm embedding.exactDecomposition key,
    terminalBN4PositiveMass_append]

theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.negativeMass_decomposition
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4NegativeMass ambient key =
      terminalBN4NegativeMass
          (pair.restorationCoverageCancellationCells restoration) key +
        terminalBN4NegativeMass remainder key := by
  rw [terminalBN4NegativeMass_perm embedding.exactDecomposition key,
    terminalBN4NegativeMass_append]

/-- Removing the balanced coverage-derived subledger preserves the executable
    residual cell at every complete BN4 key. -/
theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.residualCells_eq_remainder
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    (terminalBN4CancelAtKey ambient key).residualCells key =
      (terminalBN4CancelAtKey remainder key).residualCells key := by
  unfold terminalBN4CancelAtKey
  rw [embedding.positiveMass_decomposition key,
    embedding.negativeMass_decomposition key,
    pair.restorationCoverageCancellation_balanced restoration key]
  exact terminalBN4ResidualCells_add_common
    (terminalBN4NegativeMass
      (pair.restorationCoverageCancellationCells restoration) key)
    (terminalBN4PositiveMass remainder key)
    (terminalBN4NegativeMass remainder key) key

theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.residualLedgerOver_eq_remainder
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder)
    (keys : List (TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType)) :
    terminalBN4ResidualLedgerOver keys ambient =
      terminalBN4ResidualLedgerOver keys remainder := by
  induction keys with
  | nil => rfl
  | cons key tail inductionHypothesis =>
      simp only [terminalBN4ResidualLedgerOver, List.flatMap_cons]
      rw [embedding.residualCells_eq_remainder key]
      exact congrArg
        (fun suffix =>
          (terminalBN4CancelAtKey remainder key).residualCells key ++ suffix)
        inductionHypothesis

theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.canonicalResidualLedger_eq_remainder
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder) :
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
        remainder :=
  embedding.residualLedgerOver_eq_remainder
    (terminalBN4CanonicalKeys ambient)

/-- Proof-bearing complete residual reduction for one extracted
    coverage-derived cancellation subledger. -/
structure TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder) : Prop where
  exactResidualReduction :
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
        remainder

def TerminalPkgCRestorationCoverageAmbientBN4Embedding.residualReduction
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      restoration ambient remainder) :
    TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding :=
  { exactResidualReduction :=
      embedding.canonicalResidualLedger_eq_remainder }

/-! ## Total restoration/Hall/ambient classifier -/

inductive TerminalPkgCRestorationCoverageAmbientBN4ExtractionOutcome
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    (_realization : TerminalPkgCRestorationCoverageCancellationRealization pair
      restoration)
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) where
  | reduced
      (remainder : List (TerminalBN4ActivationCell ActivationAtom
        SemanticSignature TransportType))
      (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
        restoration ambient remainder)
      (reduction :
        TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding)
  | missing
      (cell : TerminalBN4ActivationCell ActivationAtom SemanticSignature
        TransportType)
      (generatedMember : cell ∈
        pair.restorationCoverageCancellationCells restoration)
      (noExactEmbedding : forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair restoration
          ambient remainder)

def classifyTerminalPkgCRestorationCoverageAmbientBN4Extraction
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    (realization : TerminalPkgCRestorationCoverageCancellationRealization pair
      restoration)
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    TerminalPkgCRestorationCoverageAmbientBN4ExtractionOutcome realization
      ambient :=
  match classifyTerminalExactSubledgerExtraction
      (pair.restorationCoverageCancellationCells restoration) ambient with
  | .extracted remainder exactDecomposition =>
      let embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          restoration ambient remainder :=
        { exactDecomposition := exactDecomposition }
      .reduced remainder embedding embedding.residualReduction
  | .missing cell generatedMember noExactDecomposition =>
      .missing cell generatedMember fun remainder embedding =>
        noExactDecomposition remainder embedding.exactDecomposition

/-- Complete finite PkgC result at this edge: singletonization, an exact Hall
    route, a computed ambient reduction, or proved ambient incompatibility. -/
inductive TerminalPkgCRestorationCoverageAmbientBN4RouteOutcome
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) where
  | singletonized (proof : system.DisjointPairsSingletonized)
  | hallRoute
      (pair : TerminalPkgCSeparatingPair system)
      (deficit : TerminalBN5HallDeficit
        (pair.quotientUnits restoration)
        (restoration.fullRestorations pair))
  | reduced
      (pair : TerminalPkgCSeparatingPair system)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair restoration)
      (remainder : List (TerminalBN4ActivationCell ActivationAtom
        SemanticSignature TransportType))
      (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
        restoration ambient remainder)
      (reduction :
        TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding)
  | ambientMismatch
      (pair : TerminalPkgCSeparatingPair system)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair restoration)
      (cell : TerminalBN4ActivationCell ActivationAtom SemanticSignature
        TransportType)
      (generatedMember : cell ∈
        pair.restorationCoverageCancellationCells restoration)
      (noExactEmbedding : forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair restoration
          ambient remainder)

def classifyTerminalPkgCRestorationCoverageAmbientBN4Route
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    TerminalPkgCRestorationCoverageAmbientBN4RouteOutcome system restoration
      ambient :=
  match classifyTerminalPkgCSeparatingConsumers system restoration with
  | .singletonized proof => .singletonized proof
  | .localized pair deficit => .hallRoute pair deficit
  | .restored pair coverage =>
      let realization :=
        pair.restorationCoverageCancellationRealization restoration coverage
      match classifyTerminalPkgCRestorationCoverageAmbientBN4Extraction
          realization ambient with
      | .reduced remainder embedding reduction =>
          .reduced pair realization remainder embedding reduction
      | .missing cell generatedMember noExactEmbedding =>
          .ambientMismatch pair realization cell generatedMember
            noExactEmbedding

/-- Public M204 endpoint. The finite restoration graph keeps Hall failure as
    exact route evidence and otherwise computes the coordinate-level BN4
    cancellation subledger's complete ambient consequence. -/
theorem terminalPkgC_restorationCoverage_ambientBN4_route_checked_complete
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    system.DisjointPairsSingletonized ∨
      ∃ pair : TerminalPkgCSeparatingPair system,
        (∃ deficit : TerminalBN5HallDeficit
            (pair.quotientUnits restoration)
            (restoration.fullRestorations pair),
          deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
            deficit.neighborShadows.length < deficit.fullSubset.length) ∨
        Nonempty
            (TerminalPkgCRestorationCoverageCancellationRealization pair
              restoration) ∧
          ((∃ remainder,
              ∃ embedding :
                  TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                    restoration ambient remainder,
                Nonempty
                  (TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
                    embedding)) ∨
            ∃ cell,
              cell ∈ pair.restorationCoverageCancellationCells restoration ∧
              ∀ remainder,
                ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                  restoration ambient remainder) := by
  exact match classifyTerminalPkgCRestorationCoverageAmbientBN4Route system
      restoration ambient with
    | .singletonized proof => Or.inl proof
    | .hallRoute pair deficit =>
        Or.inr ⟨pair, Or.inl ⟨deficit, rfl,
          deficit.neighbor_card_lt_full_card⟩⟩
    | .reduced pair realization remainder embedding reduction =>
        Or.inr ⟨pair, Or.inr ⟨⟨realization⟩,
          Or.inl ⟨remainder, embedding, ⟨reduction⟩⟩⟩⟩
    | .ambientMismatch pair realization cell generatedMember
        noExactEmbedding =>
        Or.inr ⟨pair, Or.inr ⟨⟨realization⟩,
          Or.inr ⟨cell, generatedMember, noExactEmbedding⟩⟩⟩

end DirectWire
end PNP
