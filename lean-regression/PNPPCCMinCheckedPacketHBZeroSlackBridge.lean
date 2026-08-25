import PNP.PCCMinCheckedPacketHBZeroSlackBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketHBZeroSlackBridgeRegression

/-! ## Empty terminal branch with no positive residual slack -/

def emptyFamily : TerminalBN6GroupedFamily Unit Unit where
  carrier := []
  carrierNodup := by simp
  groups := []
  groupCarrier := by simp
  groupFootprintLarge := by simp
  groupFootprintsNodup := by simp
  cutValue := 1
  cutValuePositive := by decide

abbrev EmptyHandle := emptyFamily.PacketSelectorHandle

instance : DecidableEq EmptyHandle := by
  unfold EmptyHandle TerminalBN6GroupedFamily.PacketSelectorHandle
  infer_instance

def emptyTable {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    TerminalPacketTypedRealizerTable current emptyFamily 0 where
  environment :=
    { rankOf := fun handle => nomatch handle
      faithful := fun handle => nomatch handle
      hnActive := fun rank => nomatch rank
      budgetActive := fun rank => nomatch rank }
  claim := fun handle => nomatch handle

def emptyDependencyTable : TerminalPacketHBDependencyTable 0 where
  rankTuple := fun rank => nomatch rank
  dependencies := fun node => nomatch node

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (emptyTable current).checkEveryClaim = true := by
  rfl

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (emptyTable current).checkFaithful = true :=
  (emptyTable current).checkFaithful_of_checkEveryClaim rfl

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    emptyDependencyTable.checkNoOutcomeActiveClosure
      (emptyTable current).environment = true := by
  rfl

def emptyBridgeData {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (notPositive : ¬0 < residualSlack current) :
    PCCMinCheckedPacketHBZeroSlackData current Unit Unit where
  family := emptyFamily
  rankCount := 0
  table := emptyTable current
  claimsAccepted := by rfl
  dependencyTable := emptyDependencyTable
  hbClosureAccepted := by rfl
  faithfulOfPositiveSlack := fun positive =>
    False.elim (notPositive positive)

theorem emptyRankSilence {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (notPositive : ¬0 < residualSlack current) :
    ∀ rank selector,
      selector ∈ (emptyBridgeData current notPositive).table.selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            (emptyBridgeData current notPositive).family.PacketSelectorHandle
            (emptyBridgeData current notPositive).rankCount,
          (emptyBridgeData current notPositive).table.checkedOutcome
              (emptyBridgeData current notPositive).claimsAccepted selector =
            .blocked reason := by
  intro rank
  exact Fin.elim0 rank

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (notPositive : ¬0 < residualSlack current) :
    residualSlack current = 0 :=
  (emptyBridgeData current notPositive).zeroSlackOfSilence_sound
    (emptyRankSilence current notPositive)

/-! ## Total loop adapter -/

/-- Exhaustive reference-minimum fixture used only to exercise the recursive
loop adapter.  It is not a polynomial construction of the PCCMin stages. -/
def referenceFixtureBuilder :
    PCCMinCheckedPacketHBZeroSlackOracleBuilder where
  Atom := fun _current => Unit
  Payload := fun _current => Unit
  atomDecidableEq := fun _current => inferInstance
  build := fun current =>
    if positive : 0 < residualSlack current then
      { NoHereditary := Empty
        NoBudget := Empty
        hResolve := .gain (referenceMinimumImplementation current)
          (referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
            positive)
        budgetResolve := fun impossible => nomatch impossible
        selectorData := fun impossible => nomatch impossible }
    else
      { NoHereditary := Unit
        NoBudget := Unit
        hResolve := .noRoute ()
        budgetResolve := fun _ => .noRoute ()
        selectorData := fun _ _ => emptyBridgeData current positive }

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeCheckedPacketHBZeroSlackLoop
      pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current :=
  pccmin_normalize_checked_packet_hb_zeroslack_loop_checked_complete
    pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current

end PCCMinCheckedPacketHBZeroSlackBridgeRegression
end DirectWire
end PNP
