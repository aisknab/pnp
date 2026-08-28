import PNP.PCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteRegression

/-! ## Concrete arbitrary-order multiset extraction -/

abbrev ExtractionAtom := Fin 4

def extractionSystem : TerminalV54ConsumerSystem ExtractionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def extractionPair : TerminalPkgCSeparatingPair extractionSystem :=
  terminalPkgCSeparatingPairOfFound extractionSystem [0, 1] [2] (by decide)

structure ExtractionFullCandidate where
  atom : ExtractionAtom
  payload : Nat
deriving DecidableEq

def extractionKey : TerminalBN4ActivationKey ExtractionAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def extractionCoordinate (atom : ExtractionAtom) :
    TerminalBN5ShadowCoordinate ExtractionAtom Nat Nat Nat Nat Nat Nat Nat :=
  { key := extractionKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def extractionRestorer : TerminalPkgCTypedRestorer ExtractionAtom
    ExtractionFullCandidate
      (TerminalBN5ShadowCoordinate ExtractionAtom Nat Nat Nat Nat Nat Nat Nat)
    where
  quotientCoordinate := extractionCoordinate
  restore := fun atom => { atom := atom, payload := atom.val + 50 }
  fullCoordinate := fun candidate => extractionCoordinate candidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

def extractionRemainder :
    List (TerminalBN4ActivationCell ExtractionAtom Nat Nat) :=
  [{ key := extractionKey
     sign := .positive
     mass := 5 },
   { key := extractionKey
     sign := .negative
     mass := 1 }]

def extractionReorderedAmbient :
    List (TerminalBN4ActivationCell ExtractionAtom Nat Nat) :=
  extractionRemainder ++
    extractionPair.restorationCancellationCells extractionRestorer

def extractionDeficientAmbient :
    List (TerminalBN4ActivationCell ExtractionAtom Nat Nat) :=
  (extractionPair.restorationCancellationCells extractionRestorer).tail

def extractionOutcomeTag
    (ambient : List (TerminalBN4ActivationCell ExtractionAtom Nat Nat)) :
    TerminalPkgCAmbientBN4ExtractionOutcome extractionPair
      extractionRestorer ambient → Nat
  | .extracted _ _ _ => 0
  | .missing _ _ _ => 1

/-- The generated ledger deliberately contains duplicate cells, so extraction
    must preserve multiplicity rather than reduce to set membership. -/
example : ¬ (extractionPair.restorationCancellationCells
    extractionRestorer).Nodup := by
  decide

/-- A noncanonical ambient order with duplicate generated cells is accepted. -/
example : extractionOutcomeTag extractionReorderedAmbient
    (classifyTerminalPkgCAmbientBN4Extraction extractionPair
      extractionRestorer extractionReorderedAmbient) = 0 := by
  decide

/-- Success exposes the computed remainder, exact permutation, and complete
    residual-ledger reduction. -/
example : exists remainder,
    TerminalPkgCAmbientBN4LedgerEmbedding extractionPair extractionRestorer
      extractionReorderedAmbient remainder ∧
    terminalBN4ResidualLedgerOver
        (terminalBN4CanonicalKeys extractionReorderedAmbient)
        extractionReorderedAmbient =
      terminalBN4ResidualLedgerOver
        (terminalBN4CanonicalKeys extractionReorderedAmbient) remainder := by
  generalize classified : classifyTerminalPkgCAmbientBN4Extraction
    extractionPair extractionRestorer extractionReorderedAmbient = outcome
  have accepted : extractionOutcomeTag extractionReorderedAmbient outcome = 0 :=
    by
      rw [← classified]
      decide
  cases outcome with
  | extracted remainder embedding exactResidualReduction =>
      exact ⟨remainder, embedding, exactResidualReduction⟩
  | missing cell generatedMember noExactEmbedding =>
      change 1 = 0 at accepted
      omega

/-- Removing one required occurrence is detected as a multiplicity failure. -/
example : extractionOutcomeTag extractionDeficientAmbient
    (classifyTerminalPkgCAmbientBN4Extraction extractionPair
      extractionRestorer extractionDeficientAmbient) = 1 := by
  decide

/-- Failure retains a required generated cell and proves that no exact
    remainder embedding exists. -/
example : exists cell,
    cell ∈ extractionPair.restorationCancellationCells extractionRestorer ∧
    ∀ remainder,
      ¬ TerminalPkgCAmbientBN4LedgerEmbedding extractionPair
        extractionRestorer extractionDeficientAmbient remainder := by
  generalize classified : classifyTerminalPkgCAmbientBN4Extraction
    extractionPair extractionRestorer extractionDeficientAmbient = outcome
  have failed : extractionOutcomeTag extractionDeficientAmbient outcome = 1 :=
    by
      rw [← classified]
      decide
  cases outcome with
  | extracted remainder embedding exactResidualReduction =>
      change 0 = 1 at failed
      omega
  | missing cell generatedMember noExactEmbedding =>
      exact ⟨cell, generatedMember, noExactEmbedding⟩

/-! ## All four source-composition branches remain proof bearing -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {FullCandidate SemanticSignature TransportType Frontier ChargeOwner
  Obligation OriginKernel ModeProjection : Type}
variable [DecidableEq SemanticSignature] [DecidableEq TransportType]
variable [DecidableEq Frontier] [DecidableEq ChargeOwner]
variable [DecidableEq Obligation] [DecidableEq OriginKernel]
variable [DecidableEq ModeProjection]

variable (data : PCCMinCheckedPacketPkgCAmbientBN4SourceData candidate model
  rankCount FullCandidate SemanticSignature TransportType Frontier ChargeOwner
  Obligation OriginKernel ModeProjection)

private def sourceOutcomeTag :
    PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteOrZeroSlack data → Nat
  | .zeroSlack _ => 0
  | .ambientReduction _ _ _ _ _ _ => 1
  | .ambientMismatch _ _ _ _ _ _ _ => 2
  | .activationRoute _ _ _ _ _ _ => 3

example
    (result : ZeroSlackResult candidate.toImplementation)
    (classified : data.source.sourceRouteOrZeroSlack = .zeroSlack result) :
    sourceOutcomeTag data data.extractionRouteOrZeroSlack = 0 := by
  simp [PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack,
    classified, sourceOutcomeTag]

example
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
    (sourceClassified : data.source.sourceRouteOrZeroSlack =
      .pkgCCancellation cell member pair realization)
    (ambientClassified :
      classifyTerminalPkgCComputedAmbientBN4Extraction
          data.source.terminalReady.result data.ambientCells
          data.ambientCanonicalAtoms pair data.source.restorer =
        .reduced bridge reduction) :
    sourceOutcomeTag data data.extractionRouteOrZeroSlack = 1 := by
  simp [PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack,
    sourceClassified, ambientClassified, sourceOutcomeTag]

example
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
    (sourceClassified : data.source.sourceRouteOrZeroSlack =
      .pkgCCancellation cell member pair realization)
    (ambientClassified :
      classifyTerminalPkgCComputedAmbientBN4Extraction
          data.source.terminalReady.result data.ambientCells
          data.ambientCanonicalAtoms pair data.source.restorer =
        .missing missingCell generatedMember noExactEmbedding) :
    sourceOutcomeTag data data.extractionRouteOrZeroSlack = 2 := by
  simp [PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack,
    sourceClassified, ambientClassified, sourceOutcomeTag]

example
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : cut.Sublist data.source.terminalReady.result.nucleus.anchors)
    (nonempty : cut ≠ [])
    (proper : cut ≠ data.source.terminalReady.result.nucleus.anchors)
    (length_le_two : cut.length ≤ 2)
    (sourceMismatch :
      terminalPkgCBN6SourceActivationWeight data.source.sourceCells cut ≠
        data.source.problem.anchorProblem.toProblem.familyDefect
          data.source.terminalReady.result.nucleus.anchors)
    (classified : data.source.sourceRouteOrZeroSlack =
      .activationRoute cut included nonempty proper length_le_two
        sourceMismatch) :
    sourceOutcomeTag data data.extractionRouteOrZeroSlack = 3 := by
  simp [PCCMinCheckedPacketPkgCAmbientBN4SourceData.extractionRouteOrZeroSlack,
    classified, sourceOutcomeTag]

example : residualSlack candidate.toImplementation = 0 ∨
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
        cut.length ≤ 2 ∧
        terminalPkgCBN6SourceActivationWeight data.source.sourceCells cut ≠
          data.source.problem.anchorProblem.toProblem.familyDefect
            data.source.terminalReady.result.nucleus.anchors :=
  pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete
    data

#print axioms classifyTerminalPkgCAmbientBN4Extraction_exhaustive
#print axioms classifyTerminalPkgCComputedAmbientBN4Extraction_exhaustive
#print axioms pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete

end PCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteRegression
end DirectWire
end PNP
