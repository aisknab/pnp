import PNP.ResidualTerminalPkgCAmbientBN4ResidualReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCResidualRegressionAtom := Fin 4

def pkgCResidualRegressionSystem :
    TerminalV54ConsumerSystem PkgCResidualRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCResidualRegressionPair :
    TerminalPkgCSeparatingPair pkgCResidualRegressionSystem :=
  terminalPkgCSeparatingPairOfFound pkgCResidualRegressionSystem
    [0, 1] [2] (by decide)

structure PkgCResidualRegressionFullCandidate where
  atom : PkgCResidualRegressionAtom
  payload : Nat
deriving DecidableEq

def pkgCResidualRegressionKey :
    TerminalBN4ActivationKey PkgCResidualRegressionAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def pkgCResidualRegressionOtherKey :
    TerminalBN4ActivationKey PkgCResidualRegressionAtom Nat Nat :=
  { atom := 0
    semanticSignature := 29
    transportType := 31 }

def pkgCResidualRegressionCoordinate (atom : PkgCResidualRegressionAtom) :
    TerminalBN5ShadowCoordinate PkgCResidualRegressionAtom Nat Nat Nat Nat Nat
      Nat Nat :=
  { key := pkgCResidualRegressionKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def pkgCResidualRegressionRestorer : TerminalPkgCTypedRestorer
    PkgCResidualRegressionAtom PkgCResidualRegressionFullCandidate
      (TerminalBN5ShadowCoordinate PkgCResidualRegressionAtom Nat Nat Nat Nat
        Nat Nat Nat) where
  quotientCoordinate := pkgCResidualRegressionCoordinate
  restore := fun atom => { atom := atom, payload := atom.val + 50 }
  fullCoordinate := fun candidate =>
    pkgCResidualRegressionCoordinate candidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

def pkgCResidualRegressionRemainder :
    List (TerminalBN4ActivationCell PkgCResidualRegressionAtom Nat Nat) :=
  [{ key := pkgCResidualRegressionKey
     sign := .positive
     mass := 5 },
   { key := pkgCResidualRegressionOtherKey
     sign := .negative
     mass := 2 },
   { key := pkgCResidualRegressionKey
     sign := .negative
     mass := 1 }]

def pkgCResidualRegressionLedger :
    List (TerminalBN4ActivationCell PkgCResidualRegressionAtom Nat Nat) :=
  pkgCResidualRegressionPair.restorationCancellationCells
      pkgCResidualRegressionRestorer ++
    pkgCResidualRegressionRemainder

def pkgCResidualRegressionEmbedding :
    TerminalPkgCAmbientBN4LedgerEmbedding pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualRegressionLedger
      pkgCResidualRegressionRemainder :=
  ⟨List.Perm.refl _⟩

def pkgCResidualRegressionReorderedLedger :
    List (TerminalBN4ActivationCell PkgCResidualRegressionAtom Nat Nat) :=
  pkgCResidualRegressionRemainder ++
    pkgCResidualRegressionPair.restorationCancellationCells
      pkgCResidualRegressionRestorer

def pkgCResidualRegressionReorderedEmbedding :
    TerminalPkgCAmbientBN4LedgerEmbedding pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualRegressionReorderedLedger
      pkgCResidualRegressionRemainder :=
  ⟨by
    unfold pkgCResidualRegressionReorderedLedger
      pkgCResidualRegressionRemainder
      TerminalPkgCSeparatingPair.restorationCancellationCells
      terminalPkgCRestorationCancellationCellsForAtoms
      terminalPkgCRestorationCancellationCellsForAtom
    decide⟩

example : terminalBN4ResidualLedgerOver
      (terminalBN4CanonicalKeys pkgCResidualRegressionLedger)
      pkgCResidualRegressionLedger =
    terminalBN4ResidualLedgerOver
      (terminalBN4CanonicalKeys pkgCResidualRegressionLedger)
      pkgCResidualRegressionRemainder :=
  pkgCResidualRegressionEmbedding.canonicalResidualLedger_eq_remainder

example : terminalBN4ResidualLedgerOver
      (terminalBN4CanonicalKeys pkgCResidualRegressionReorderedLedger)
      pkgCResidualRegressionReorderedLedger =
    terminalBN4ResidualLedgerOver
      (terminalBN4CanonicalKeys pkgCResidualRegressionReorderedLedger)
      pkgCResidualRegressionRemainder :=
  pkgCResidualRegressionReorderedEmbedding.canonicalResidualLedger_eq_remainder

example : (terminalBN4CancelAtKey pkgCResidualRegressionLedger
      pkgCResidualRegressionKey).residualCells
      pkgCResidualRegressionKey =
    [{ key := pkgCResidualRegressionKey
       sign := .positive
       mass := 4 }] := by
  decide

example : (terminalBN4CancelAtKey pkgCResidualRegressionLedger
      pkgCResidualRegressionOtherKey).residualCells
      pkgCResidualRegressionOtherKey =
    [{ key := pkgCResidualRegressionOtherKey
       sign := .negative
       mass := 2 }] := by
  decide

example (cell : TerminalBN4ActivationCell PkgCResidualRegressionAtom Nat Nat)
    (member : cell ∈ pkgCResidualRegressionRemainder) :
    cell.key ∈ terminalBN4CanonicalKeys pkgCResidualRegressionLedger :=
  pkgCResidualRegressionEmbedding.remainderKey_mem_ambientCanonicalKeys
    cell member

def pkgCResidualEmptyRegressionLedger :
    List (TerminalBN4ActivationCell PkgCResidualRegressionAtom Nat Nat) :=
  pkgCResidualRegressionPair.restorationCancellationCells
    pkgCResidualRegressionRestorer

def pkgCResidualEmptyRegressionEmbedding :
    TerminalPkgCAmbientBN4LedgerEmbedding pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualEmptyRegressionLedger [] :=
  ⟨by simp [pkgCResidualEmptyRegressionLedger]⟩

example : terminalBN4ResidualLedgerOver
      (terminalBN4CanonicalKeys pkgCResidualEmptyRegressionLedger)
      pkgCResidualEmptyRegressionLedger = [] :=
  TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty
    pkgCResidualEmptyRegressionEmbedding rfl

def pkgCResidualRegressionMismatchTag :
    TerminalPkgCAmbientBN4LedgerBindingOutcome pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualRegressionLedger [] -> Nat
  | .embedded _ => 0
  | .mismatch _ => 1

example : pkgCResidualRegressionMismatchTag
    (classifyTerminalPkgCAmbientBN4LedgerBinding
      pkgCResidualRegressionPair pkgCResidualRegressionRestorer
      pkgCResidualRegressionLedger []) = 1 := by
  decide

def pkgCResidualRegressionReductionTag :
    TerminalPkgCAmbientBN4ResidualReductionOutcome pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualRegressionLedger
      pkgCResidualRegressionRemainder → Nat
  | .reduced _ _ => 0
  | .mismatch _ => 1

example : pkgCResidualRegressionReductionTag
    (classifyTerminalPkgCAmbientBN4ResidualReduction
      pkgCResidualRegressionPair pkgCResidualRegressionRestorer
      pkgCResidualRegressionLedger pkgCResidualRegressionRemainder) = 0 := by
  decide

def pkgCResidualRegressionReductionMismatchTag :
    TerminalPkgCAmbientBN4ResidualReductionOutcome pkgCResidualRegressionPair
      pkgCResidualRegressionRestorer pkgCResidualRegressionLedger [] → Nat
  | .reduced _ _ => 0
  | .mismatch _ => 1

example : pkgCResidualRegressionReductionMismatchTag
    (classifyTerminalPkgCAmbientBN4ResidualReduction
      pkgCResidualRegressionPair pkgCResidualRegressionRestorer
      pkgCResidualRegressionLedger []) = 1 := by
  decide

example
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {saturation : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate saturation}
    {result : TerminalComputedBCELAnchorNucleus problem}
    {ambient : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) Nat Nat)}
    {ConsumerAtom FullCandidate : Type}
    {system : TerminalV54ConsumerSystem ConsumerAtom}
    {pair : TerminalPkgCSeparatingPair system}
    {restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        Nat Nat Nat Nat Nat Nat Nat)}
    (bridge : TerminalPkgCComputedAmbientBN4Cancellation result ambient pair
      restorer) :
    Nonempty (TerminalPkgCComputedAmbientBN4ResidualReduction bridge) :=
  ⟨bridge.residualReduction⟩

#print axioms terminalBN4ResidualCells_add_common
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.residualCells_eq_remainder
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.residualLedgerOver_eq_remainder
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.remainderKey_mem_ambientCanonicalKeys
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_eq_remainder
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.canonicalResidualLedger_empty_of_remainder_empty
#print axioms classifyTerminalPkgCAmbientBN4ResidualReduction_exhaustive
#print axioms TerminalPkgCComputedAmbientBN4Cancellation.residualReduction
#print axioms TerminalPkgCComputedAmbientBN4Cancellation.residualLedger_empty_of_remainder_empty

end DirectWire
end PNP
