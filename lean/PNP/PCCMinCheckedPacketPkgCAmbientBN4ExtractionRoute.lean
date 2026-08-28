/-
Copyright (c) 2026 PNP Labs.

Computed ambient-BN4 extraction for the source-derived PkgC/BN6 route.

M202 retains an exact PkgC same-key cancellation, conditional ZeroSlack, or a
source-ledger BCEL activation mismatch.  The existing ambient-BN4 bridge can
reduce the complete residual ledger after a PkgC cancellation, but accepts an
explicit remainder and permutation embedding.  This module removes that seam:
it recursively erases the generated cancellation cells from an arbitrary-order
ambient ledger and either constructs the exact remainder and residual reduction
or proves that no exact multiset embedding exists.

The ambient ledger, source systems, typed restorer, payloads, downstream tables,
and checked finite BCEL-ready branch remain supplied.  A successful extraction
is exact structural evidence, not a verified gain or global rank descent; a
failed extraction is a precise compatibility failure, not a completed global
route.  This module does not establish complete PkgC/BN3--BN6 integration,
unconditional ZeroSlack, polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.PCCMinCheckedPacketPkgCBN6BCELSourceRoute
import PNP.ResidualTerminalPkgCAmbientBN4ResidualReduction

namespace PNP
namespace DirectWire

/-! ## Constructive exact finite-subledger extraction -/

/-- Internal proof-bearing result for remove-first multiset extraction.  The
    failure branch retains both a required occurrence and the stronger proof
    that no exact remainder decomposition exists. -/
private inductive ExactSubledgerExtractionOutcome {Alpha : Type}
    (required ambient : List Alpha) : Type where
  | extracted
      (remainder : List Alpha)
      (exactDecomposition : ambient.Perm (required ++ remainder))
  | missing
      (cell : Alpha)
      (requiredMember : cell ∈ required)
      (noExactDecomposition :
        ∀ remainder, ¬ ambient.Perm (required ++ remainder))

/-- Construct the remove-first permutation directly.  The standard convenience
    theorem carries `Classical.choice`; this proof uses only the explicit
    `DecidableEq` recursion needed by the executable extractor. -/
private theorem permConsEraseConstructive
    {Alpha : Type} [DecidableEq Alpha]
    {cell : Alpha} {ambient : List Alpha}
    (member : cell ∈ ambient) :
    ambient.Perm (cell :: ambient.erase cell) := by
  induction ambient with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      by_cases equal : head = cell
      · subst head
        simp only [List.erase_cons_head]
        exact List.Perm.refl _
      · have tailMember : cell ∈ tail := by
          simpa [Ne.symm equal] using member
        have tailPermutation := inductionHypothesis tailMember
        rw [List.erase_cons_tail (by simp [equal])]
        exact (tailPermutation.cons head).trans
          (List.Perm.swap cell head _)

/-- Constructively remove every required occurrence from the ambient list.
    `erase` makes the result order independent and preserves multiplicity. -/
private def classifyExactSubledgerExtraction
    {Alpha : Type} [DecidableEq Alpha] :
    (required ambient : List Alpha) ->
      ExactSubledgerExtractionOutcome required ambient
  | [], ambient =>
      .extracted ambient (by simp)
  | head :: tail, ambient =>
      if found : head ∈ ambient then
        match classifyExactSubledgerExtraction tail (ambient.erase head) with
        | .extracted remainder exactDecomposition =>
            .extracted remainder <|
              (permConsEraseConstructive found).trans
                (exactDecomposition.cons head)
        | .missing cell requiredMember noExactDecomposition =>
            .missing cell (by simp [requiredMember]) (by
              intro remainder exactDecomposition
              apply noExactDecomposition remainder
              apply List.Perm.cons_inv
              exact (permConsEraseConstructive found).symm.trans
                exactDecomposition)
      else
        .missing head (by simp) (by
          intro remainder exactDecomposition
          apply found
          apply exactDecomposition.mem_iff.mpr
          simp)

/-! ## Exact ambient PkgC extraction -/

/-- Total order-independent multiset extraction of one generated PkgC
    cancellation ledger from an ambient BN4 ledger. -/
inductive TerminalPkgCAmbientBN4ExtractionOutcome
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
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) where
  | extracted
      (remainder : List (TerminalBN4ActivationCell ActivationAtom
        SemanticSignature TransportType))
      (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
        ambient remainder)
      (exactResidualReduction :
        terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
            ambient =
          terminalBN4ResidualLedgerOver (terminalBN4CanonicalKeys ambient)
            remainder)
  | missing
      (cell : TerminalBN4ActivationCell ActivationAtom SemanticSignature
        TransportType)
      (generatedMember : cell ∈
        pair.restorationCancellationCells restorer)
      (noExactEmbedding : ∀ remainder,
        ¬ TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient
          remainder)

/-- Compute the ambient remainder and its complete residual reduction without
    accepting a proposed remainder, serialization, or permutation. -/
def classifyTerminalPkgCAmbientBN4Extraction
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
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    TerminalPkgCAmbientBN4ExtractionOutcome pair restorer ambient :=
  match classifyExactSubledgerExtraction
      (pair.restorationCancellationCells restorer) ambient with
  | .extracted remainder exactDecomposition =>
      let embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer
          ambient remainder :=
        { exactDecomposition := exactDecomposition }
      .extracted remainder embedding
        embedding.canonicalResidualLedger_eq_remainder
  | .missing cell generatedMember noExactDecomposition =>
      .missing cell generatedMember fun remainder embedding =>
        noExactDecomposition remainder embedding.exactDecomposition

/-- The constructive arbitrary-order ambient extractor has no third result. -/
theorem classifyTerminalPkgCAmbientBN4Extraction_exhaustive
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
    (ambient : List (TerminalBN4ActivationCell ActivationAtom
      SemanticSignature TransportType)) :
    Nonempty (TerminalPkgCAmbientBN4ExtractionOutcome pair restorer
      ambient) :=
  ⟨classifyTerminalPkgCAmbientBN4Extraction pair restorer ambient⟩

/-! ## Candidate-bound ambient BN4 extraction -/

/-- Total result of extracting one PkgC cancellation subledger from an
    arbitrary-order ambient ledger tied to the same computed BCEL nucleus. -/
inductive TerminalPkgCComputedAmbientBN4ExtractionOutcome
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
        OriginKernel ModeProjection)) where
  | reduced
      (bridge : TerminalPkgCComputedAmbientBN4Cancellation result ambient pair
        restorer)
      (reduction : TerminalPkgCComputedAmbientBN4ResidualReduction bridge)
  | missing
      (cell : TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType)
      (generatedMember : cell ∈
        pair.restorationCancellationCells restorer)
      (noExactEmbedding : ∀ remainder,
        ¬ TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient
          remainder)

/-- Compute the exact ambient remainder and residual reduction, or prove that
    no exact remainder embedding exists.  The candidate-derived BN4 kernel is
    assembled internally from the checked canonical-atom condition. -/
def classifyTerminalPkgCComputedAmbientBN4Extraction
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
    (canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result ambient)
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)) :
    TerminalPkgCComputedAmbientBN4ExtractionOutcome result ambient pair
      restorer :=
  match classifyTerminalPkgCAmbientBN4Extraction pair restorer ambient with
  | .extracted remainder embedding _exactResidualReduction =>
      let kernel := result.computedBN4ActivationCancellation ambient
        canonicalAtoms
      let bridge := kernel.pkgCAmbientCancellation pair restorer remainder
        embedding
      .reduced bridge bridge.residualReduction
  | .missing cell generatedMember noExactEmbedding =>
      .missing cell generatedMember noExactEmbedding

/-- The computed arbitrary-order ambient extraction has no third result. -/
theorem classifyTerminalPkgCComputedAmbientBN4Extraction_exhaustive
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
    (canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result ambient)
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection)) :
    Nonempty (TerminalPkgCComputedAmbientBN4ExtractionOutcome result ambient
      pair restorer) :=
  ⟨classifyTerminalPkgCComputedAmbientBN4Extraction result ambient
    canonicalAtoms pair restorer⟩

/-! ## Composition with the source-derived PkgC/BN6/BCEL route -/

/-- M202 source data plus one ambient BN4 ledger checked against the same
    computed BCEL-ready nucleus.  The source restorer is specialized to that
    nucleus's primitive-record activation space. -/
structure PCCMinCheckedPacketPkgCAmbientBN4SourceData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat)
    (FullCandidate SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type)
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection] where
  source : PCCMinCheckedPacketPkgCBN6BCELSourceHBData candidate model
    rankCount FullCandidate
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection
  ambientCells : List (TerminalBN4ActivationCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    SemanticSignature TransportType)
  ambientCanonicalAtoms : TerminalBN4CellsUseCanonicalAtoms
    source.terminalReady.result ambientCells

/-- Four-way source result: conditional ZeroSlack, computed ambient reduction,
    exact ambient incompatibility, or M202's source activation mismatch. -/
inductive PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCAmbientBN4SourceData candidate model
      rankCount FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | ambientReduction
      (cell : TerminalPkgCBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        data.source.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.source.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.consumerSystem)
      (realization : TerminalPkgCSameKeyCancellationRealization pair
        data.source.restorer)
      (bridge : TerminalPkgCComputedAmbientBN4Cancellation
        data.source.terminalReady.result data.ambientCells pair
        data.source.restorer)
      (reduction : TerminalPkgCComputedAmbientBN4ResidualReduction bridge)
  | ambientMismatch
      (cell : TerminalPkgCBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        data.source.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.source.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.consumerSystem)
      (realization : TerminalPkgCSameKeyCancellationRealization pair
        data.source.restorer)
      (missingCell : TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType)
      (generatedMember : missingCell ∈
        pair.restorationCancellationCells data.source.restorer)
      (noExactEmbedding : ∀ remainder,
        ¬ TerminalPkgCAmbientBN4LedgerEmbedding pair data.source.restorer
          data.ambientCells remainder)
  | activationRoute
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist
        data.source.terminalReady.result.nucleus.anchors)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.source.terminalReady.result.nucleus.anchors)
      (length_le_two : cut.length <= 2)
      (sourceMismatch :
        terminalPkgCBN6SourceActivationWeight data.source.sourceCells cut ≠
          data.source.problem.anchorProblem.toProblem.familyDefect
            data.source.terminalReady.result.nucleus.anchors)

/-- Run M202 and compute the ambient BN4 consequence of its exact PkgC
    cancellation branch without accepting a remainder or embedding. -/
def PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCAmbientBN4SourceData candidate model
      rankCount FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection) :
    PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteOrZeroSlack data :=
  match data.source.sourceRouteOrZeroSlack with
  | .zeroSlack result => .zeroSlack result
  | .pkgCCancellation cell member pair realization =>
      match classifyTerminalPkgCComputedAmbientBN4Extraction
          data.source.terminalReady.result data.ambientCells
          data.ambientCanonicalAtoms pair data.source.restorer with
      | .reduced bridge reduction =>
          .ambientReduction cell member pair realization bridge reduction
      | .missing missingCell generatedMember noExactEmbedding =>
          .ambientMismatch cell member pair realization missingCell
            generatedMember noExactEmbedding
  | .activationRoute cut included nonempty proper length_le_two
      sourceMismatch =>
      .activationRoute cut included nonempty proper length_le_two
        sourceMismatch

/-- Public M203 endpoint: M202's arbitrary-finite source result now computes
    the exact candidate-bound ambient BN4 remainder and residual reduction, or
    proves that no such multiset embedding exists. -/
theorem pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCAmbientBN4SourceData candidate model
      rankCount FullCandidate SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection) :
    residualSlack candidate.toImplementation = 0 ∨
      (exists cell, cell ∈ data.source.sourceCells ∧
        exists pair : TerminalPkgCSeparatingPair cell.consumerSystem,
          Nonempty (TerminalPkgCSameKeyCancellationRealization pair
            data.source.restorer) ∧
          ((exists bridge : TerminalPkgCComputedAmbientBN4Cancellation
                data.source.terminalReady.result data.ambientCells pair
                data.source.restorer,
              Nonempty
                (TerminalPkgCComputedAmbientBN4ResidualReduction bridge)) ∨
            exists missingCell,
              missingCell ∈
                pair.restorationCancellationCells data.source.restorer ∧
              ∀ remainder,
                ¬ TerminalPkgCAmbientBN4LedgerEmbedding pair
                  data.source.restorer data.ambientCells remainder)) ∨
      exists cut,
        cut.Sublist data.source.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.source.terminalReady.result.nucleus.anchors ∧
        cut.length <= 2 ∧
        terminalPkgCBN6SourceActivationWeight data.source.sourceCells cut ≠
          data.source.problem.anchorProblem.toProblem.familyDefect
            data.source.terminalReady.result.nucleus.anchors := by
  exact match data.extractionRouteOrZeroSlack with
    | .zeroSlack result => Or.inl result.sound
    | .ambientReduction cell member pair realization bridge reduction =>
        Or.inr (Or.inl ⟨cell, member, pair, ⟨realization⟩,
          Or.inl ⟨bridge, ⟨reduction⟩⟩⟩)
    | .ambientMismatch cell member pair realization missingCell
        generatedMember noExactEmbedding =>
        Or.inr (Or.inl ⟨cell, member, pair, ⟨realization⟩,
          Or.inr ⟨missingCell, generatedMember, noExactEmbedding⟩⟩)
    | .activationRoute cut included nonempty proper length_le_two
        sourceMismatch =>
        Or.inr (Or.inr ⟨cut, included, nonempty, proper, length_le_two,
          sourceMismatch⟩)

end DirectWire
end PNP
