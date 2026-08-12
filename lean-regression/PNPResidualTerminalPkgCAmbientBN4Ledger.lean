import PNP.ResidualTerminalPkgCAmbientBN4Ledger

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev PkgCAmbientRegressionAtom := Fin 4

def pkgCAmbientRegressionSystem :
    TerminalV54ConsumerSystem PkgCAmbientRegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def pkgCAmbientRegressionPair :
    TerminalPkgCSeparatingPair pkgCAmbientRegressionSystem :=
  terminalPkgCSeparatingPairOfFound pkgCAmbientRegressionSystem
    [0, 1] [2] (by decide)

structure PkgCAmbientRegressionFullCandidate where
  atom : PkgCAmbientRegressionAtom
  payload : Nat
deriving DecidableEq

def pkgCAmbientRegressionKey :
    TerminalBN4ActivationKey PkgCAmbientRegressionAtom Nat Nat :=
  { atom := 3
    semanticSignature := 17
    transportType := 23 }

def pkgCAmbientRegressionCoordinate (atom : PkgCAmbientRegressionAtom) :
    TerminalBN5ShadowCoordinate PkgCAmbientRegressionAtom Nat Nat Nat Nat Nat
      Nat Nat :=
  { key := pkgCAmbientRegressionKey
    frontier := atom.val
    chargeOwner := atom.val + 10
    obligation := atom.val + 20
    originKernel := atom.val + 30
    modeProjection := atom.val + 40 }

def pkgCAmbientRegressionRestorer : TerminalPkgCTypedRestorer
    PkgCAmbientRegressionAtom PkgCAmbientRegressionFullCandidate
      (TerminalBN5ShadowCoordinate PkgCAmbientRegressionAtom Nat Nat Nat Nat
        Nat Nat Nat) where
  quotientCoordinate := pkgCAmbientRegressionCoordinate
  restore := fun atom => { atom := atom, payload := atom.val + 50 }
  fullCoordinate := fun candidate =>
    pkgCAmbientRegressionCoordinate candidate.atom
  restore_preserves_coordinate := by
    intro atom
    rfl

def pkgCAmbientRegressionRemainder :
    List (TerminalBN4ActivationCell PkgCAmbientRegressionAtom Nat Nat) :=
  [{ key := pkgCAmbientRegressionKey
     sign := .positive
     mass := 5 }]

def pkgCAmbientRegressionLedger :
    List (TerminalBN4ActivationCell PkgCAmbientRegressionAtom Nat Nat) :=
  pkgCAmbientRegressionPair.restorationCancellationCells
      pkgCAmbientRegressionRestorer ++
    pkgCAmbientRegressionRemainder

def pkgCAmbientRegressionEmbedding :
    TerminalPkgCAmbientBN4LedgerEmbedding pkgCAmbientRegressionPair
      pkgCAmbientRegressionRestorer pkgCAmbientRegressionLedger
      pkgCAmbientRegressionRemainder :=
  ⟨List.Perm.refl _⟩

example : pkgCAmbientRegressionLedger.length = 7 := by decide

example : terminalBN4PositiveMass pkgCAmbientRegressionLedger
    pkgCAmbientRegressionKey = 8 := by decide

example : terminalBN4NegativeMass pkgCAmbientRegressionLedger
    pkgCAmbientRegressionKey = 3 := by decide

example : terminalBN4InputSignedMass pkgCAmbientRegressionLedger
    pkgCAmbientRegressionKey = 5 := by decide

example : terminalBN4InputSignedMass pkgCAmbientRegressionRemainder
    pkgCAmbientRegressionKey = 5 := by decide

example : ((((terminalBN4CancelAtKey pkgCAmbientRegressionLedger
    pkgCAmbientRegressionKey).residualCells pkgCAmbientRegressionKey).map
      TerminalBN4ActivationCell.signedContribution).sum) = 5 := by decide

example : terminalBN4InputSignedMass pkgCAmbientRegressionLedger
      pkgCAmbientRegressionKey =
    terminalBN4InputSignedMass pkgCAmbientRegressionRemainder
      pkgCAmbientRegressionKey :=
  pkgCAmbientRegressionEmbedding.signedMass_eq_remainder
    pkgCAmbientRegressionKey

example : ((((terminalBN4CancelAtKey pkgCAmbientRegressionLedger
      pkgCAmbientRegressionKey).residualCells pkgCAmbientRegressionKey).map
        TerminalBN4ActivationCell.signedContribution).sum) =
    terminalBN4InputSignedMass pkgCAmbientRegressionRemainder
      pkgCAmbientRegressionKey :=
  pkgCAmbientRegressionEmbedding.residualSignedContribution_eq_remainder
    pkgCAmbientRegressionKey

def pkgCAmbientRegressionBindingTag :
    TerminalPkgCAmbientBN4LedgerBindingOutcome pkgCAmbientRegressionPair
      pkgCAmbientRegressionRestorer pkgCAmbientRegressionLedger
      pkgCAmbientRegressionRemainder -> Nat
  | .embedded _ => 0
  | .mismatch _ => 1

example : pkgCAmbientRegressionBindingTag
    (classifyTerminalPkgCAmbientBN4LedgerBinding
      pkgCAmbientRegressionPair pkgCAmbientRegressionRestorer
      pkgCAmbientRegressionLedger pkgCAmbientRegressionRemainder) = 0 :=
  by decide

def pkgCAmbientRegressionMismatchTag :
    TerminalPkgCAmbientBN4LedgerBindingOutcome pkgCAmbientRegressionPair
      pkgCAmbientRegressionRestorer pkgCAmbientRegressionLedger [] -> Nat
  | .embedded _ => 0
  | .mismatch _ => 1

example : pkgCAmbientRegressionMismatchTag
    (classifyTerminalPkgCAmbientBN4LedgerBinding
      pkgCAmbientRegressionPair pkgCAmbientRegressionRestorer
      pkgCAmbientRegressionLedger []) = 1 := by decide

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
    (kernel : TerminalComputedBN4ActivationCancellation result ambient)
    (pair : TerminalPkgCSeparatingPair system)
    (restorer : TerminalPkgCTypedRestorer ConsumerAtom FullCandidate
      (TerminalBN5ShadowCoordinate
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        Nat Nat Nat Nat Nat Nat Nat))
    (remainder : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) Nat Nat))
    (embedding : TerminalPkgCAmbientBN4LedgerEmbedding pair restorer ambient
      remainder) :
    Nonempty (TerminalPkgCComputedAmbientBN4Cancellation result ambient pair
      restorer) :=
  ⟨kernel.pkgCAmbientCancellation pair restorer remainder embedding⟩

#print axioms terminalBN4PositiveMass_perm
#print axioms terminalBN4NegativeMass_perm
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.cellMultiplicity
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.signedMass_eq_remainder
#print axioms TerminalPkgCAmbientBN4LedgerEmbedding.residualSignedContribution_eq_remainder
#print axioms classifyTerminalPkgCAmbientBN4LedgerBinding_exhaustive
#print axioms TerminalPkgCComputedAmbientBN4Cancellation.generatedCell_usesCanonicalAtom
#print axioms terminalPkgC_computedAmbientBN4_silence_singletonizes

end DirectWire
end PNP
