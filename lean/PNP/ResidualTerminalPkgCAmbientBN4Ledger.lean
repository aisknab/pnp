/-
Copyright (c) 2026 PNP Labs.

Finite proof-bearing bridge from PkgC's generated same-key cancellation cells
to an explicit ambient BN4 ledger.  The previous milestone constructed a
balanced opposite-sign ledger for every separating pair, but did not identify
those generated cells with cells already present in an ambient BN4
cancellation problem.  Here that identification is expressed by exact list
permutation: the ambient ledger is the generated ledger plus an explicit
remainder, up to order.  A canonical executable path accepts the literal
generated-then-remainder serialization; other orders require an explicit
kernel-checked permutation certificate.  This preserves multiplicity, rejects
missing, duplicated, and foreign cells, and proves that removing the generated
balanced subledger leaves every ambient signed mass and canonical residual
contribution equal to the remainder's.

The bridge can additionally retain a successful candidate-derived BN4 kernel,
so every embedded generated cell is proved to use the kernel's canonical BN3
request-atom space.  The ambient ledger, typed restorer, exact decomposition,
and successful BN4 kernel remain explicit proof-bearing inputs.  This module
does not derive any of them from a terminal candidate, construct a semantic
restorer, embed local outcomes into the complete global route system, prove
PkgC route silence, polynomial runtime, ZeroSlack or PCCMin, put SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPkgCSameKeyCancellation

namespace PNP
namespace DirectWire

/-! ## Permutation-invariant BN4 mass -/

/-- Reordering a finite cell ledger does not change positive mass at any
    complete BN4 key. -/
theorem terminalBN4PositiveMass_perm
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)}
    (permutation : left.Perm right)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    terminalBN4PositiveMass left key =
      terminalBN4PositiveMass right key := by
  unfold terminalBN4PositiveMass
  induction permutation with
  | nil => rfl
  | cons cell permutation inductionHypothesis =>
      simp [inductionHypothesis]
  | swap first second tail =>
      simp [Nat.add_left_comm]
  | trans first second firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Reordering a finite cell ledger does not change negative mass at any
    complete BN4 key. -/
theorem terminalBN4NegativeMass_perm
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)}
    (permutation : left.Perm right)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    terminalBN4NegativeMass left key =
      terminalBN4NegativeMass right key := by
  unfold terminalBN4NegativeMass
  induction permutation with
  | nil => rfl
  | cons cell permutation inductionHypothesis =>
      simp [inductionHypothesis]
  | swap first second tail =>
      simp [Nat.add_left_comm]
  | trans first second firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-! ## Exact ambient-ledger embedding -/

/-- Exact multiset binding of the generated PkgC cancellation cells into an
    ambient BN4 ledger.  `Perm` is deliberately stronger than membership: it
    preserves every duplicate and requires the proposed remainder to account
    for every ambient cell exactly once. -/
structure TerminalPkgCAmbientBN4LedgerEmbedding
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
    (ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) : Prop where
  exactDecomposition : ambient.Perm
    (pair.restorationCancellationCells restorer ++ remainder)

/-- Every generated cell occurs in the ambient ledger. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.generatedCell_mem_ambient
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (cell : TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType)
    (member : cell ∈ pair.restorationCancellationCells restorer) :
    cell ∈ ambient := by
  apply embedding.exactDecomposition.mem_iff.mpr
  exact List.mem_append_left remainder member

/-- Exact decomposition preserves each cell's multiplicity, including
    duplicate generated cells. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.cellMultiplicity
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (cell : TerminalBN4ActivationCell ActivationAtom SemanticSignature
      TransportType) :
    ambient.count cell =
      (pair.restorationCancellationCells restorer).count cell +
        remainder.count cell := by
  rw [embedding.exactDecomposition.count_eq cell, List.count_append]

/-- The ambient length is the exact generated cell count plus the remainder
    length. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.length_eq
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder) :
    ambient.length =
      2 * (pair.left.length + pair.right.length) + remainder.length := by
  rw [embedding.exactDecomposition.length_eq, List.length_append,
    pair.restorationCancellationCells_length]

/-- Positive ambient mass decomposes exactly into generated and remainder
    mass at every complete key. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.positiveMass_decomposition
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4PositiveMass ambient key =
      terminalBN4PositiveMass
          (pair.restorationCancellationCells restorer) key +
        terminalBN4PositiveMass remainder key := by
  rw [terminalBN4PositiveMass_perm embedding.exactDecomposition key,
    terminalBN4PositiveMass_append]

/-- Negative ambient mass decomposes exactly into generated and remainder
    mass at every complete key. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.negativeMass_decomposition
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4NegativeMass ambient key =
      terminalBN4NegativeMass
          (pair.restorationCancellationCells restorer) key +
        terminalBN4NegativeMass remainder key := by
  rw [terminalBN4NegativeMass_perm embedding.exactDecomposition key,
    terminalBN4NegativeMass_append]

/-- Because the generated subledger is balanced at every key, exact ambient
    removal preserves the complete signed integer mass of the remainder. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.signedMass_eq_remainder
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    terminalBN4InputSignedMass ambient key =
      terminalBN4InputSignedMass remainder key := by
  unfold terminalBN4InputSignedMass
  rw [embedding.positiveMass_decomposition key,
    embedding.negativeMass_decomposition key,
    pair.restorationCancellation_balanced restorer key]
  have positiveCast :
      Int.ofNat (terminalBN4NegativeMass
          (pair.restorationCancellationCells restorer) key +
        terminalBN4PositiveMass remainder key) =
        Int.ofNat (terminalBN4NegativeMass
          (pair.restorationCancellationCells restorer) key) +
          Int.ofNat (terminalBN4PositiveMass remainder key) :=
    Int.natCast_add _ _
  have negativeCast :
      Int.ofNat (terminalBN4NegativeMass
          (pair.restorationCancellationCells restorer) key +
        terminalBN4NegativeMass remainder key) =
        Int.ofNat (terminalBN4NegativeMass
          (pair.restorationCancellationCells restorer) key) +
          Int.ofNat (terminalBN4NegativeMass remainder key) :=
    Int.natCast_add _ _
  rw [positiveCast, negativeCast]
  omega

/-- The ambient executable BN4 cancellation has exactly the remainder's
    signed contribution after removing the embedded balanced subledger. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.residualSignedContribution_eq_remainder
    {ConsumerAtom FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)}
    {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)}
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
      ambient remainder)
    (key : TerminalBN4ActivationKey ActivationAtom SemanticSignature
      TransportType) :
    ((((terminalBN4CancelAtKey ambient key).residualCells key).map
      TerminalBN4ActivationCell.signedContribution).sum) =
        terminalBN4InputSignedMass remainder key := by
  rw [terminalBN4CancelAtKey_signedContribution_exact,
    embedding.signedMass_eq_remainder]

/-! ## Fail-closed executable binding -/

/-- Canonical binding either succeeds with an exact embedding or rejects the
    proposed generated-then-remainder serialization.  A differently ordered
    ambient ledger remains admissible through an explicit `Perm` certificate. -/
inductive TerminalPkgCAmbientBN4LedgerBindingOutcome
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
    (ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) where
  | embedded
      (proof : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
        ambient remainder)
  | mismatch
      (failure : ambient ≠
        pair.restorationCancellationCells restorer ++ remainder)

/-- Decide the canonical exact serialization; no success bit or binding proof
    is accepted from the caller. -/
def classifyTerminalPkgCAmbientBN4LedgerBinding
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
    (ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    TerminalPkgCAmbientBN4LedgerBindingOutcome pair restorer ambient
      remainder :=
  if exact : ambient =
      pair.restorationCancellationCells restorer ++ remainder then
    .embedded ⟨List.Perm.of_eq exact⟩
  else
    .mismatch exact

/-- No third result exists for an explicit proposed ambient decomposition. -/
theorem classifyTerminalPkgCAmbientBN4LedgerBinding_exhaustive
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
    (ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    Nonempty (TerminalPkgCAmbientBN4LedgerBindingOutcome pair restorer
      ambient remainder) :=
  ⟨classifyTerminalPkgCAmbientBN4LedgerBinding pair restorer ambient
    remainder⟩

/-! ## Candidate-derived BN4 bridge -/

/-- A PkgC cancellation embedded in an ambient ledger that is itself accepted
    by the candidate-derived finite BN4 kernel. -/
structure TerminalPkgCComputedAmbientBN4Cancellation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {saturation : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate saturation}
    {ConsumerAtom FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (result : TerminalComputedBCELAnchorNucleus problem)
    (ambient : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType))
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)) : Type where
  bn4Kernel : TerminalComputedBN4ActivationCancellation result ambient
  remainder : List (TerminalBN4ActivationCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    SemanticSignature TransportType)
  embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient
    remainder

/-- Every generated PkgC cancellation cell in the computed bridge uses an
    atom from the successful candidate-derived BN3 request space. -/
theorem TerminalPkgCComputedAmbientBN4Cancellation.generatedCell_usesCanonicalAtom
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {saturation : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate saturation}
    {ConsumerAtom FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {result : TerminalComputedBCELAnchorNucleus problem}
    {ambient : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)}
    (bridge : TerminalPkgCComputedAmbientBN4Cancellation result ambient pair
      restorer)
    (cell : TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)
    (member : cell ∈ pair.restorationCancellationCells restorer) :
    cell.key.atom ∈ result.requestAtoms := by
  apply (terminalBN4CellsUseCanonicalAtoms_iff result ambient).1
    bridge.bn4Kernel.cellsUseCanonicalAtoms cell
  exact bridge.embedding.generatedCell_mem_ambient cell member

/-- Assemble the computed ambient bridge from the successful BN4 kernel and
    an exact multiset embedding. -/
def TerminalComputedBN4ActivationCancellation.pkgCAmbientCancellation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {saturation : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate saturation}
    {ConsumerAtom FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {result : TerminalComputedBCELAnchorNucleus problem}
    {ambient : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (kernel : TerminalComputedBN4ActivationCancellation result ambient)
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (remainder : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType))
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient
      remainder) :
    TerminalPkgCComputedAmbientBN4Cancellation result ambient pair restorer :=
  { bn4Kernel := kernel
    remainder := remainder
    embedding := embedding }

/-- If every separating pair has an exact binding into the same successful
    ambient BN4 ledger, then absence of every proof-bearing computed ambient
    cancellation forces V54 singletonization. -/
theorem terminalPkgC_computedAmbientBN4_silence_singletonizes
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {saturation : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate saturation}
    {ConsumerAtom FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ConsumerAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {result : TerminalComputedBCELAnchorNucleus problem}
    {ambient : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)}
    (kernel : TerminalComputedBN4ActivationCancellation result ambient)
    (system : TerminalV54ConsumerSystem ConsumerAtom)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection))
    (complete : ∀ pair : TerminalPkgCSeparatingPair system,
      ∃ remainder, TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
        ambient remainder)
    (silent : ∀ pair : TerminalPkgCSeparatingPair system,
      ¬ Nonempty (TerminalPkgCComputedAmbientBN4Cancellation result ambient
        pair restorer)) :
    system.DisjointPairsSingletonized := by
  apply terminalPkgC_sameKeyCancellation_silence_singletonizes system restorer
  intro pair _localRealization
  obtain ⟨remainder, embedding⟩ := complete pair
  exact silent pair ⟨kernel.pkgCAmbientCancellation pair restorer remainder
    embedding⟩

end DirectWire
end PNP
