import PNP.PCCMinCheckedPacketBN6HBZeroSlackBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6HBZeroSlackBridgeRegression

/-! ## General BN6/computed-faithfulness boundary -/

example {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (positive : 0 < residualSlack current) :
    TerminalBN6PacketConclusion data.family :=
  data.positivePacketOfPositiveSlack positive

example {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount)
    (positive : 0 < residualSlack current) :
    ∃ handle : data.family.PacketSelectorHandle,
      data.rawTable.withComputedPacketSelectorFaithfulness.environment.faithful
        handle = true :=
  data.faithfulOfPositiveSlack positive

example {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    (data : PCCMinCheckedPacketBN6HBZeroSlackData
      current Atom rankCount) :
    PCCMinCheckedPacketHBZeroSlackData current Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount) :=
  data.toCheckedPacketHBZeroSlackData

/-! ## A terminal branch where positive slack is refuted -/

def twoAnchorEmptyFamily : TerminalBN6GroupedFamily Bool
    (TerminalPacketSelectorFaithfulnessPayload 0) where
  carrier := [false, true]
  carrierNodup := by decide
  groups := []
  groupCarrier := by simp
  groupFootprintLarge := by simp
  groupFootprintsNodup := by simp
  cutValue := 1
  cutValuePositive := by decide

abbrev EmptyHandle := twoAnchorEmptyFamily.PacketSelectorHandle

instance : DecidableEq EmptyHandle := by
  unfold EmptyHandle TerminalBN6GroupedFamily.PacketSelectorHandle
  infer_instance

def emptyRawTable {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    TerminalPacketTypedRealizerTable current twoAnchorEmptyFamily 0 where
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
    (emptyRawTable current).withComputedPacketSelectorFaithfulness.checkEveryClaim =
      true := by
  rfl

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    twoAnchorEmptyFamily.checkPacketSelectorRoutesClear
      (emptyRawTable current).environment.rankOf = true := by
  rfl

def emptyBridgeData {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (notPositive : ¬0 < residualSlack current) :
    PCCMinCheckedPacketBN6HBZeroSlackData current Bool 0 where
  family := twoAnchorEmptyFamily
  rawTable := emptyRawTable current
  claimsAccepted := by rfl
  dependencyTable := emptyDependencyTable
  hbClosureAccepted := by rfl
  routesClear := by rfl
  carrierAtLeastTwo := by decide
  constantActivationOfPositiveSlack := fun positive =>
    False.elim (notPositive positive)

theorem emptyRankSilence {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (notPositive : ¬0 < residualSlack current) :
    ∀ rank selector,
      selector ∈ ((emptyBridgeData current notPositive).rawTable.withComputedPacketSelectorFaithfulness
          ).selectorsAtRank rank →
        ∃ reason : TerminalPacketTypedRealizerBot
            (emptyBridgeData current notPositive).family.PacketSelectorHandle 0,
          ((emptyBridgeData current notPositive).rawTable.withComputedPacketSelectorFaithfulness
              ).checkedOutcome
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
    PCCMinCheckedPacketBN6HBZeroSlackOracleBuilder where
  Atom := fun _current => Bool
  atomDecidableEq := fun _current => inferInstance
  rankCount := fun _current => 0
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
    let execution := runPCCMinNormalizeCheckedPacketBN6HBZeroSlackLoop
      pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations ≤ residualSlack current :=
  pccmin_normalize_checked_packet_bn6_hb_zeroslack_loop_checked_complete
    pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current

end PCCMinCheckedPacketBN6HBZeroSlackBridgeRegression
end DirectWire
end PNP
