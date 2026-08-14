import PNP.ResidualTerminalPacketTypedRealizerContract

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Concrete data-only gain and typed-bot rows -/

def typedRealizerZeroGateIdentity : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def typedRealizerAcceptedBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := typedRealizerZeroGateIdentity
  pairing := []
  unmatched := [0]

def typedRealizerMalformedBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := redundantIdentityImplementation
  pairing := [(0, 0)]
  unmatched := []

def typedRealizerEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun rank => decide (rank = (1 : Fin 3))
  budgetActive := fun rank => decide (rank = (2 : Fin 3))

def typedRealizerEnvironmentWithUnfaithfulZero :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun selector => decide (selector ≠ (0 : Fin 3))
  hnActive := typedRealizerEnvironment.hnActive
  budgetActive := typedRealizerEnvironment.budgetActive

def typedRealizerGainClaim : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3 :=
  .gain typedRealizerAcceptedBlueprint

def typedRealizerHNClaim : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3 :=
  .bot (.hn (1 : Fin 3))

def typedRealizerBudgetClaim : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3 :=
  .bot (.budget (2 : Fin 3))

def typedRealizerLowerSeedClaim : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3 :=
  .bot (.lowerSeed (1 : Fin 3))

example : typedRealizerGainClaim.check typedRealizerEnvironment
    (0 : Fin 3) = true := by
  rfl

example : typedRealizerHNClaim.check typedRealizerEnvironment
    (1 : Fin 3) = true := by
  rfl

example : typedRealizerBudgetClaim.check typedRealizerEnvironment
    (2 : Fin 3) = true := by
  rfl

example : typedRealizerLowerSeedClaim.check typedRealizerEnvironment
    (2 : Fin 3) = true := by
  rfl

example : (.bot (.hn (0 : Fin 3)) : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3).check
      typedRealizerEnvironment (1 : Fin 3) = false := by
  rfl

example : (.bot (.budget (2 : Fin 3)) : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3).check
      typedRealizerEnvironment (1 : Fin 3) = false := by
  rfl

example : typedRealizerLowerSeedClaim.check
    typedRealizerEnvironmentWithUnfaithfulZero (2 : Fin 3) = true := by
  rfl

example : (.bot (.lowerSeed (0 : Fin 3)) :
    TerminalPacketTypedRealizerClaim redundantIdentityImplementation
      (Fin 3) 3).check typedRealizerEnvironmentWithUnfaithfulZero
        (2 : Fin 3) = false := by
  rfl

example : (.gain typedRealizerMalformedBlueprint :
    TerminalPacketTypedRealizerClaim redundantIdentityImplementation
      (Fin 3) 3).check typedRealizerEnvironment (0 : Fin 3) = false := by
  rfl

/-! ## Complete arbitrary finite faithful-table validation -/

def typedRealizerClaims (selector : Fin 3) :
    TerminalPacketTypedRealizerClaim redundantIdentityImplementation
      (Fin 3) 3 :=
  if selector = (0 : Fin 3) then
    typedRealizerGainClaim
  else if selector = (1 : Fin 3) then
    typedRealizerHNClaim
  else
    typedRealizerLowerSeedClaim

def typedRealizerClaimsWithStaticReject (selector : Fin 3) :
    TerminalPacketTypedRealizerClaim redundantIdentityImplementation
      (Fin 3) 3 :=
  if selector = (0 : Fin 3) then
    .gain typedRealizerMalformedBlueprint
  else
    typedRealizerClaims selector

example : checkTerminalPacketFaithfulRealizerClaims (allFin 3)
    typedRealizerEnvironment typedRealizerClaims = true := by
  rfl

example : checkTerminalPacketFaithfulRealizerClaims (allFin 3)
    typedRealizerEnvironment typedRealizerClaimsWithStaticReject = false := by
  rfl

example : typedRealizerGainClaim.Sound typedRealizerEnvironment
    (0 : Fin 3) :=
  (typedRealizerGainClaim.evidenceOfCheck typedRealizerEnvironment
    (0 : Fin 3) (by rfl)).sound

example : typedRealizerHNClaim.Sound typedRealizerEnvironment
    (1 : Fin 3) :=
  (typedRealizerHNClaim.evidenceOfCheck typedRealizerEnvironment
    (1 : Fin 3) (by rfl)).sound

example : typedRealizerBudgetClaim.Sound typedRealizerEnvironment
    (2 : Fin 3) :=
  (typedRealizerBudgetClaim.evidenceOfCheck typedRealizerEnvironment
    (2 : Fin 3) (by rfl)).sound

example : typedRealizerLowerSeedClaim.Sound typedRealizerEnvironment
    (2 : Fin 3) :=
  (typedRealizerLowerSeedClaim.evidenceOfCheck typedRealizerEnvironment
    (2 : Fin 3) (by rfl)).sound

example : typedRealizerClaims (2 : Fin 3) |>.Sound
    typedRealizerEnvironment (2 : Fin 3) :=
  checkTerminalPacketFaithfulRealizerClaims_sound (allFin 3)
    typedRealizerEnvironment typedRealizerClaims (by rfl)
    (2 : Fin 3) (mem_allFin (2 : Fin 3)) (by rfl)

/-! ## Canonical-family theorem remains arbitrary and input-relative -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkFaithful = true)
    (handle : family.PacketSelectorHandle)
    (faithful : table.environment.faithful handle = true) :
    (table.claim handle).Sound table.environment handle :=
  terminalBN6_packet_typed_realizer_contract table accepted handle faithful

end DirectWire
end PNP
