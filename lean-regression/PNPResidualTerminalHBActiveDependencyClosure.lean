import PNP.ResidualTerminalHBActiveDependencyClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Ranked total table and no-outcome activity scans -/

def hbActiveRankTuple3 (rank : Fin 3) : TerminalResidualRank :=
  TerminalResidualRank.mk rank.val 0 0 0 0 0 0 0 0 0

def hbActiveDescendingDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (2 : Fin 3) then [.budget (1 : Fin 3)] else []
  | .budget rank =>
      if rank = (1 : Fin 3) then [.hn (0 : Fin 3)] else []

def hbActiveDescendingTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbActiveRankTuple3
  dependencies := hbActiveDescendingDependencies

def hbActiveCyclicDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (2 : Fin 3) then [.budget (1 : Fin 3)] else []
  | .budget rank =>
      if rank = (1 : Fin 3) then [.hn (2 : Fin 3)] else []

def hbActiveCyclicTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbActiveRankTuple3
  dependencies := hbActiveCyclicDependencies

def hbAllInactiveEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun _rank => false
  budgetActive := fun _rank => false

def hbDanglingActiveEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun rank => decide (rank = (2 : Fin 3))
  budgetActive := fun _rank => false

def hbDescendingActiveChainEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun rank =>
    decide (rank = (2 : Fin 3) ∨ rank = (0 : Fin 3))
  budgetActive := fun rank => decide (rank = (1 : Fin 3))

def hbCyclicActiveEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun rank => decide (rank = (2 : Fin 3))
  budgetActive := fun rank => decide (rank = (1 : Fin 3))

example : hbAllInactiveEnvironment.hbActive (.hn (1 : Fin 3)) = false := by
  rfl

example : hbAllInactiveEnvironment.hbActive (.budget (1 : Fin 3)) = false := by
  rfl

example : hbActiveDescendingTable.checkActiveDependencyClosed
    hbAllInactiveEnvironment = true := by
  rfl

example : hbActiveDescendingTable.checkNoOutcomeActiveClosure
    hbAllInactiveEnvironment = true := by
  rfl

/-- An active node whose listed dependency is inactive is rejected. -/
example : hbActiveDescendingTable.checkActiveDependencyClosed
    hbDanglingActiveEnvironment = false := by
  rfl

/-- A finite descending active chain is rejected at its active base row. -/
example : hbActiveDescendingTable.checkActiveDependencyClosed
    hbDescendingActiveChainEnvironment = false := by
  rfl

/-- A locally closed active cycle passes the local scan but fails the
    independent exact-rank table check. -/
example : hbActiveCyclicTable.checkActiveDependencyClosed
    hbCyclicActiveEnvironment = true := by
  rfl

example : hbActiveCyclicTable.checkNoOutcomeActiveClosure
    hbCyclicActiveEnvironment = false := by
  rfl

example : hbActiveDescendingTable.ActiveDependencyClosed
    hbAllInactiveEnvironment :=
  (hbActiveDescendingTable.checkActiveDependencyClosed_eq_true_iff
    hbAllInactiveEnvironment).mp (by rfl)

example : hbActiveDescendingTable.NoOutcomeActiveClosureValid
    hbAllInactiveEnvironment :=
  (hbActiveDescendingTable.checkNoOutcomeActiveClosure_eq_true_iff
    hbAllInactiveEnvironment).mp (by rfl)

example : ∀ node : TerminalPacketHBNode 3,
    hbAllInactiveEnvironment.hbActive node = false :=
  hbActiveDescendingTable.noActive_of_noOutcomeActiveClosure
    hbAllInactiveEnvironment (by rfl)

example : hbAllInactiveEnvironment.hnActive (2 : Fin 3) = false :=
  hbActiveDescendingTable.hnActive_eq_false
    hbAllInactiveEnvironment (by rfl) _

example : hbAllInactiveEnvironment.budgetActive (1 : Fin 3) = false :=
  hbActiveDescendingTable.budgetActive_eq_false
    hbAllInactiveEnvironment (by rfl) _

/-! ## HN/BUD bot elimination preserves gain and lower-seed branches -/

def hbActiveLowerSeedClaim : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3 :=
  .bot (.lowerSeed (1 : Fin 3))

example : hbActiveLowerSeedClaim.check hbAllInactiveEnvironment
    (2 : Fin 3) = true := by
  rfl

example : hbActiveLowerSeedClaim.HBActiveClosureSound
    hbAllInactiveEnvironment (2 : Fin 3) hbActiveDescendingTable :=
  (hbActiveLowerSeedClaim.evidenceOfCheck hbAllInactiveEnvironment
    (2 : Fin 3) (by rfl)).hbActiveClosureSound
      hbActiveDescendingTable (by rfl)

example : (.bot (.hn (1 : Fin 3)) : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3).check
      hbAllInactiveEnvironment (2 : Fin 3) = false := by
  rfl

example : (.bot (.budget (1 : Fin 3)) : TerminalPacketTypedRealizerClaim
    redundantIdentityImplementation (Fin 3) 3).check
      hbAllInactiveEnvironment (2 : Fin 3) = false := by
  rfl

/-! ## Canonical typed-realizer composition remains arbitrary -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (handle : family.PacketSelectorHandle)
    (faithful : realizerTable.environment.faithful handle = true) :
    (realizerTable.claim handle).HBActiveClosureSound
        realizerTable.environment handle dependencyTable ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends :=
  terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract
    realizerTable dependencyTable realizerAccepted closureAccepted handle
    faithful

end DirectWire
end PNP
