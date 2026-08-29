/-
Copyright (c) 2026 PNP Labs.

Exact charge-coordinate descent for the candidate-bound PkgC restoration
coverage route.

M206 retains a coverage-derived balanced BN4 subledger together with an exact
multiset embedding into the ambient ledger and a mechanically computed
remainder.  The branch already preserves the complete canonical residual
ledger, but it was not connected to the manuscript's ten-coordinate residual
rank.

Every coverage-derived cancellation cell has unit mass, and every separating
consumer pair has two nonempty sides.  The extracted subledger therefore has
strictly positive unsigned charge.  Exact multiset decomposition proves that
the remainder has strictly smaller unsigned charge than the ambient ledger.
With all other residual-rank coordinates held fixed, this is a kernel-checked
strict decrease of the `chargeSize` coordinate for every surrounding rank
context.

The terminal problem, source cells, restoration universes, ambient ledgers,
semantic payloads, ranks outside this computed charge transition, claims,
dependency table, checked HB closure, route-clear result, and selector silence
remain supplied.  Hall, ambient-incompatibility, and activation-mismatch
branches remain exact diagnostics rather than verified global descents.  This
module does not complete global route coverage, PkgC/BN3--BN6 integration,
unconditional ZeroSlack, polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute

namespace PNP
namespace DirectWire

/-! ## Permutation-invariant unsigned BN4 charge -/

/-- Total unsigned charge represented by a finite BN4 cell ledger. -/
def terminalBN4UnsignedChargeSize
    {Atom SemanticSignature TransportType : Type}
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)) : Nat :=
  (cells.map fun cell => cell.mass).sum

/-- Unsigned charge is additive across concatenated ledgers. -/
theorem terminalBN4UnsignedChargeSize_append
    {Atom SemanticSignature TransportType : Type}
    (left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)) :
    terminalBN4UnsignedChargeSize (left ++ right) =
      terminalBN4UnsignedChargeSize left +
        terminalBN4UnsignedChargeSize right := by
  simp [terminalBN4UnsignedChargeSize]

/-- Reordering a finite cell ledger preserves its unsigned charge. -/
theorem terminalBN4UnsignedChargeSize_perm
    {Atom SemanticSignature TransportType : Type}
    {left right : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)}
    (permutation : left.Perm right) :
    terminalBN4UnsignedChargeSize left =
      terminalBN4UnsignedChargeSize right := by
  unfold terminalBN4UnsignedChargeSize
  induction permutation with
  | nil => rfl
  | cons cell permutation inductionHypothesis =>
      simp [inductionHypothesis]
  | swap first second tail =>
      simp [Nat.add_left_comm]
  | trans first second firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-! ## Positive charge of the canonical restoration subledger -/

/-- Each canonical quotient unit contributes exactly two units of unsigned
    BN4 charge. -/
theorem terminalPkgCRestorationCoverageCancellationCellsForUnits_unsignedChargeSize
    {ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection : Type}
    (units : List (TerminalBN5FullUnit
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection))) :
    terminalBN4UnsignedChargeSize
        (terminalPkgCRestorationCoverageCancellationCellsForUnits units) =
      2 * units.length := by
  induction units with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change terminalBN4UnsignedChargeSize
          (terminalPkgCRestorationCoverageCancellationCellsForUnit head ++
            terminalPkgCRestorationCoverageCancellationCellsForUnits tail) =
        2 * (head :: tail).length
      rw [terminalBN4UnsignedChargeSize_append, inductionHypothesis]
      simp [terminalPkgCRestorationCoverageCancellationCellsForUnit,
        terminalBN4UnsignedChargeSize]
      omega

/-- A separating pair's coverage-derived cancellation ledger has twice the
    combined consumer cardinality as unsigned charge. -/
theorem TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    terminalBN4UnsignedChargeSize
        (pair.restorationCoverageCancellationCells restoration) =
      2 * (pair.left.length + pair.right.length) := by
  rw [TerminalPkgCSeparatingPair.restorationCoverageCancellationCells,
    terminalPkgCRestorationCoverageCancellationCellsForUnits_unsignedChargeSize,
    pair.quotientUnits_length]

/-- Both consumers are nonempty, so every separating pair removes strictly
    positive unsigned charge. -/
theorem TerminalPkgCSeparatingPair.restorationCoverageCancellation_unsignedChargeSize_pos
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    (pair : TerminalPkgCSeparatingPair system)
    (restoration : TerminalPkgCRestorationUniverse ConsumerAtom
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    0 < terminalBN4UnsignedChargeSize
      (pair.restorationCoverageCancellationCells restoration) := by
  rw [pair.restorationCoverageCancellation_unsignedChargeSize restoration]
  have leftNonempty : pair.left ≠ [] :=
    system.consumerNonempty pair.left pair.leftMember
  have rightNonempty : pair.right ≠ [] :=
    system.consumerNonempty pair.right pair.rightMember
  have leftPositive : 0 < pair.left.length := by
    cases leftEquation : pair.left with
    | nil => exact False.elim (leftNonempty leftEquation)
    | cons head tail => simp
  have rightPositive : 0 < pair.right.length :=
    by
      cases rightEquation : pair.right with
      | nil => exact False.elim (rightNonempty rightEquation)
      | cons head tail => simp
  omega

/-! ## Exact ambient charge descent -/

/-- Exact decomposition of unsigned charge across the coverage-derived
    subledger and the computed remainder. -/
theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.unsignedChargeSize_decomposition
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
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
    terminalBN4UnsignedChargeSize ambient =
      terminalBN4UnsignedChargeSize
          (pair.restorationCoverageCancellationCells restoration) +
        terminalBN4UnsignedChargeSize remainder := by
  calc
    terminalBN4UnsignedChargeSize ambient =
        terminalBN4UnsignedChargeSize
          (pair.restorationCoverageCancellationCells restoration ++
            remainder) :=
      terminalBN4UnsignedChargeSize_perm embedding.exactDecomposition
    _ = terminalBN4UnsignedChargeSize
          (pair.restorationCoverageCancellationCells restoration) +
        terminalBN4UnsignedChargeSize remainder :=
      terminalBN4UnsignedChargeSize_append _ _

/-- Removing the nonempty balanced restoration subledger strictly lowers
    unsigned BN4 charge. -/
theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.remainder_unsignedChargeSize_lt
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
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
    terminalBN4UnsignedChargeSize remainder <
      terminalBN4UnsignedChargeSize ambient := by
  have decomposition := embedding.unsignedChargeSize_decomposition
  have removedPositive :=
    pair.restorationCoverageCancellation_unsignedChargeSize_pos restoration
  omega

/-- The nine residual-rank coordinates unchanged by the BN4 charge reduction. -/
structure TerminalPkgCBN4ChargeRankContext where
  witnessType : Nat
  spanType : Nat
  mode : Nat
  frontierDefect : Nat
  projectionDefect : Nat
  saturationDefect : Nat
  anchorCount : Nat
  profileSize : Nat
  canonicalCode : Nat

/-- Install a computed unsigned charge size into the exact ten-coordinate
    manuscript residual rank. -/
def TerminalPkgCBN4ChargeRankContext.rank
    (context : TerminalPkgCBN4ChargeRankContext)
    (chargeSize : Nat) : TerminalResidualRank :=
  TerminalResidualRank.mk context.witnessType context.spanType context.mode
    context.frontierDefect context.projectionDefect context.saturationDefect
    context.anchorCount chargeSize context.profileSize context.canonicalCode

/-- The coverage-derived ambient reduction decreases the exact residual rank
    for every fixed surrounding rank context. -/
theorem TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeRank_lt
    {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
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
    (context : TerminalPkgCBN4ChargeRankContext) :
    (context.rank (terminalBN4UnsignedChargeSize remainder)).LexLT
      (context.rank (terminalBN4UnsignedChargeSize ambient)) := by
  exact terminalResidualRank_chargeSize_lt context.witnessType context.spanType
    context.mode context.frontierDefect context.projectionDefect
    context.saturationDefect context.anchorCount
    (terminalBN4UnsignedChargeSize remainder)
    (terminalBN4UnsignedChargeSize ambient) context.profileSize
    context.canonicalCode context.profileSize context.canonicalCode
    embedding.remainder_unsignedChargeSize_lt

/-- Proof-bearing M207 route constructed solely from the exact M206 ambient
    embedding.  It retains residual-ledger preservation and exposes both the
    scalar charge decrease and its exact ten-coordinate rank interpretation. -/
structure TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent
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
  chargeSizeStrict :
    terminalBN4UnsignedChargeSize remainder <
      terminalBN4UnsignedChargeSize ambient
  rankStrict : forall context : TerminalPkgCBN4ChargeRankContext,
    (context.rank (terminalBN4UnsignedChargeSize remainder)).LexLT
      (context.rank (terminalBN4UnsignedChargeSize ambient))

/-- Construct the complete charge-descent route; no rank or inequality proof
    is accepted from the caller. -/
def TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeDescent
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
    TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent embedding :=
  { exactResidualReduction :=
      embedding.canonicalResidualLedger_eq_remainder
    chargeSizeStrict := embedding.remainder_unsignedChargeSize_lt
    rankStrict := embedding.chargeRank_lt }

/-! ## Candidate-bound M206 composition -/

/-- M207 preserves every M206 branch but upgrades the successful ambient
    reduction to a mechanically constructed exact charge-coordinate descent. -/
inductive PCCMinCheckedPacketPkgCRestorationCoverageChargeRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | hallRoute
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (deficit : TerminalBN5HallDeficit
        (pair.quotientUnits cell.restoration)
        (cell.restoration.fullRestorations pair))
  | ambientChargeDescent
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (canonicalAtoms :
        TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
          cell.ambient)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (remainder : List (TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType))
      (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
        cell.restoration cell.ambient remainder)
      (descent :
        TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent embedding)
  | ambientMismatch
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (canonicalAtoms :
        TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
          cell.ambient)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (missingCell : TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType)
      (generatedMember : missingCell ∈
        pair.restorationCoverageCancellationCells cell.restoration)
      (noExactEmbedding : forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          cell.restoration cell.ambient remainder)
  | activationRoute
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist data.terminalReady.result.nucleus.anchors)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.terminalReady.result.nucleus.anchors)
      (length_le_two : cut.length <= 2)
      (sourceMismatch :
        terminalPkgCRestorationCoverageBN6SourceActivationWeight
            data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors)

/-- Run the exact M206 classifier and mechanically enrich only its ambient
    reduction branch with the computed charge-coordinate descent. -/
def PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) :
    PCCMinCheckedPacketPkgCRestorationCoverageChargeRouteOrZeroSlack data := by
  match data.routeOrZeroSlack with
  | .zeroSlack result => exact .zeroSlack result
  | .hallRoute cell member pair deficit =>
      exact .hallRoute cell member pair deficit
  | .ambientReduction cell member pair canonicalAtoms realization remainder
      embedding _reduction =>
      exact .ambientChargeDescent cell member pair canonicalAtoms realization
        remainder embedding embedding.chargeDescent
  | .ambientMismatch cell member pair canonicalAtoms realization missingCell
      generatedMember noExactEmbedding =>
      exact .ambientMismatch cell member pair canonicalAtoms realization
        missingCell generatedMember noExactEmbedding
  | .activationRoute cut included nonempty proper length_le_two
      sourceMismatch =>
      exact .activationRoute cut included nonempty proper length_le_two
        sourceMismatch

/-- Public M207 endpoint.  M206's exact ambient-reduction branch now carries
    residual-ledger preservation, strict unsigned-charge decrease, and exact
    `chargeSize`-coordinate rank descent for every fixed surrounding context. -/
theorem pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) :
    residualSlack candidate.toImplementation = 0 ∨
      (exists cell, cell ∈ data.sourceCells ∧
        exists pair : TerminalPkgCSeparatingPair
            cell.source.consumerSystem,
          (exists deficit : TerminalBN5HallDeficit
              (pair.quotientUnits cell.restoration)
              (cell.restoration.fullRestorations pair),
            deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
              deficit.neighborShadows.length < deficit.fullSubset.length) ∨
          TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
              cell.ambient ∧
            Nonempty
              (TerminalPkgCRestorationCoverageCancellationRealization pair
                cell.restoration) ∧
            ((exists remainder,
                exists embedding :
                    TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                      cell.restoration cell.ambient remainder,
                  Nonempty
                    (TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent
                      embedding)) ∨
              exists missingCell,
                missingCell ∈
                  pair.restorationCoverageCancellationCells
                    cell.restoration ∧
                forall remainder,
                  ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                    cell.restoration cell.ambient remainder)) ∨
      exists cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        cut.length <= 2 ∧
        terminalPkgCRestorationCoverageBN6SourceActivationWeight
            data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  exact match data.chargeRouteOrZeroSlack with
    | .zeroSlack result => Or.inl result.sound
    | .hallRoute cell member pair deficit =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inl ⟨deficit, rfl,
          deficit.neighbor_card_lt_full_card⟩⟩)
    | .ambientChargeDescent cell member pair canonicalAtoms realization
        remainder embedding descent =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inr ⟨canonicalAtoms,
          ⟨realization⟩, Or.inl ⟨remainder, embedding, ⟨descent⟩⟩⟩⟩)
    | .ambientMismatch cell member pair canonicalAtoms realization missingCell
        generatedMember noExactEmbedding =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inr ⟨canonicalAtoms,
          ⟨realization⟩, Or.inr ⟨missingCell, generatedMember,
            noExactEmbedding⟩⟩⟩)
    | .activationRoute cut included nonempty proper length_le_two
        sourceMismatch =>
        Or.inr (Or.inr ⟨cut, included, nonempty, proper, length_le_two,
          sourceMismatch⟩)

end DirectWire
end PNP
