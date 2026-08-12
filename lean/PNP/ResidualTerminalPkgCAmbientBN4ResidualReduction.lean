/-
Copyright (c) 2026 PNP Labs.

Exact residual reduction after embedding PkgC's generated balanced
cancellation cells in an ambient BN4 ledger.  The preceding milestone proved
that ambient positive and negative mass decompose into the generated subledger
and an explicit remainder at every complete key.  Here Lean proves the
stronger executable statement: adding the same generated mass to both signs
does not change the BN4 cancellation result, so cancelling the complete
ambient ledger over its canonical key universe yields exactly the same
residual cells as cancelling the remainder over that same universe.

The ambient ledger, typed restorer, exact embedding, and remainder remain
explicit finite proof-bearing inputs.  In particular, this module does not
derive the remainder from a terminal candidate, prove that it is empty or
route-producing, establish restoration semantic adequacy or complete global
route silence, construct BN6 or Packet completeness, prove polynomial runtime,
ZeroSlack or PCCMin, put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPkgCAmbientBN4Ledger

namespace PNP
namespace DirectWire

/-! ## Cancellation is invariant under a balanced common summand -/

/-- Adding the same natural mass to the positive and negative sides preserves
    the executable residual cell at one complete key. -/
theorem terminalBN4ResidualCells_add_common
    {Atom SemanticSignature TransportType : Type}
    (shared positive negative : Nat)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    (classifyTerminalBN4KeyCancellation
        (shared + positive) (shared + negative)).residualCells key =
      (classifyTerminalBN4KeyCancellation positive negative).residualCells
        key := by
  by_cases equal : positive = negative
  · simp [classifyTerminalBN4KeyCancellation, equal,
      TerminalBN4KeyCancellation.residualCells]
  · by_cases positiveWins : negative < positive
    · have sharedPositiveWins :
          shared + negative < shared + positive := by omega
      have subtraction :
          shared + positive - (shared + negative) = positive - negative := by
        omega
      simp [classifyTerminalBN4KeyCancellation, equal,
        positiveWins, sharedPositiveWins,
        TerminalBN4KeyCancellation.residualCells, subtraction]
    · have sharedPositiveNotWins :
          ¬ shared + negative < shared + positive := by omega
      have subtraction :
          shared + negative - (shared + positive) = negative - positive := by
        omega
      simp [classifyTerminalBN4KeyCancellation, equal,
        positiveWins, sharedPositiveNotWins,
        TerminalBN4KeyCancellation.residualCells, subtraction]

/-- Exact ambient embedding and generated balance preserve the complete
    executable cancellation result at every BN4 key, not only its signed sum. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.residualCells_eq_remainder
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
    (terminalBN4CancelAtKey ambient key).residualCells key =
      (terminalBN4CancelAtKey remainder key).residualCells key := by
  unfold terminalBN4CancelAtKey
  rw [embedding.positiveMass_decomposition key,
    embedding.negativeMass_decomposition key,
    pair.restorationCancellation_balanced restorer key]
  exact terminalBN4ResidualCells_add_common
    (terminalBN4NegativeMass
      (pair.restorationCancellationCells restorer) key)
    (terminalBN4PositiveMass remainder key)
    (terminalBN4NegativeMass remainder key) key

/-! ## Complete residual ledger on an explicit key universe -/

/-- Concatenate the canonical residual cell at each supplied key.  The key
    order is explicit so both sides of a reduction are compared in one common
    ambient coordinate system. -/
def terminalBN4ResidualLedgerOver
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (keys : List (TerminalBN4ActivationKey Atom SemanticSignature
      TransportType))
    (cells : List (TerminalBN4ActivationCell Atom SemanticSignature
      TransportType)) :
    List (TerminalBN4ActivationCell Atom SemanticSignature TransportType) :=
  keys.flatMap fun key => (terminalBN4CancelAtKey cells key).residualCells key

/-- Per-key residual preservation lifts to any shared finite key universe. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.residualLedgerOver_eq_remainder
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

/-- Every key occurring in the remainder occurs in the ambient ledger, hence
    the ambient canonical key list is complete for both ledgers. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.remainderKey_mem_ambientCanonicalKeys
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
    (member : cell ∈ remainder) :
    cell.key ∈ terminalBN4CanonicalKeys ambient := by
  apply (mem_terminalBN4CanonicalKeys_iff ambient cell.key).2
  refine ⟨cell, ?_, rfl⟩
  apply embedding.exactDecomposition.mem_iff.mpr
  exact List.mem_append_right _ member

/-- The complete ambient canonical residual ledger is exactly the remainder's
    residual ledger evaluated on that same complete key universe. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_eq_remainder
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
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
        remainder :=
  embedding.residualLedgerOver_eq_remainder
    (terminalBN4CanonicalKeys ambient)

/-- If the exact ambient decomposition has no remainder, then no residual cell
    survives at any canonical ambient key. -/
theorem TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty
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
    (remainderEmpty : remainder = []) :
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      [] := by
  rw [embedding.canonicalResidualLedger_eq_remainder, remainderEmpty]
  simp [terminalBN4ResidualLedgerOver, terminalBN4CancelAtKey,
    terminalBN4PositiveMass, terminalBN4NegativeMass,
    classifyTerminalBN4KeyCancellation,
    TerminalBN4KeyCancellation.residualCells]

/-! ## Fail-closed executable reduction -/

/-- An explicit canonical serialization either produces both its exact
    embedding and the residual reduction mechanically implied by that
    embedding, or returns the exact serialization mismatch. -/
inductive TerminalPkgCAmbientBN4ResidualReductionOutcome
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
  | reduced
      (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
        ambient remainder)
      (exactResidualReduction :
        terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
            ambient =
          terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
            remainder)
  | mismatch
      (failure : ambient ≠
        pair.restorationCancellationCells restorer ++ remainder)

/-- Decide the canonical generated-then-remainder serialization and construct
    its complete residual reduction without accepting a success bit, embedding,
    or residual equality from the caller. -/
def classifyTerminalPkgCAmbientBN4ResidualReduction
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
    TerminalPkgCAmbientBN4ResidualReductionOutcome pair restorer ambient
      remainder :=
  match classifyTerminalPkgCAmbientBN4LedgerBinding pair restorer ambient
      remainder with
  | .embedded embedding =>
      .reduced embedding embedding.canonicalResidualLedger_eq_remainder
  | .mismatch failure => .mismatch failure

/-- The fail-closed residual-reduction classifier has no third result. -/
theorem classifyTerminalPkgCAmbientBN4ResidualReduction_exhaustive
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
    Nonempty (TerminalPkgCAmbientBN4ResidualReductionOutcome pair restorer
      ambient remainder) :=
  ⟨classifyTerminalPkgCAmbientBN4ResidualReduction pair restorer ambient
    remainder⟩

/-! ## Candidate-derived proof-bearing reduction -/

/-- A computed ambient PkgC bridge together with the exact complete residual
    reduction mechanically implied by its embedding. -/
structure TerminalPkgCComputedAmbientBN4ResidualReduction
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
      restorer) : Prop where
  exactResidualReduction :
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
        bridge.remainder

/-- Construct the reduction from the existing computed ambient bridge; no
    residual equality or success flag is accepted from the caller. -/
def TerminalPkgCComputedAmbientBN4Cancellation.residualReduction
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
      restorer) :
    TerminalPkgCComputedAmbientBN4ResidualReduction bridge :=
  { exactResidualReduction :=
      bridge.embedding.canonicalResidualLedger_eq_remainder }

/-- When a computed bridge's exact remainder is empty, its complete ambient
    BN4 residual ledger is empty. -/
theorem TerminalPkgCComputedAmbientBN4Cancellation.residualLedger_empty_of_remainder_empty
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
    (remainderEmpty : bridge.remainder = []) :
    terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient) ambient =
      [] :=
  bridge.embedding.canonicalResidualLedger_empty_of_remainder_empty
    remainderEmpty

end DirectWire
end PNP
