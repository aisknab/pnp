import PNP.PCCMinCheckedPacketRankedSelector

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketRankedSelectorRegression

/-! ## Two canonical Packet handles -/

abbrev Atom := Fin 3

def consumer01 : TerminalV54ConsumerSystem Atom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[0], [1]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def consumer12 : TerminalV54ConsumerSystem Atom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem consumer01_singletonized :
    consumer01.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer member
  simp [consumer01] at member
  rcases member with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem consumer12_singletonized :
    consumer12.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer member
  simp [consumer12] at member
  rcases member with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

def group01 : TerminalBN6GroupedCell Atom Unit where
  consumerSystem := consumer01
  singletonized := consumer01_singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := () }]
  atomsNonempty := by simp

def group12 : TerminalBN6GroupedCell Atom Unit where
  consumerSystem := consumer12
  singletonized := consumer12_singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := () }]
  atomsNonempty := by simp

def packetFamily : TerminalBN6GroupedFamily Atom Unit where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  groups := [group01, group12]
  groupCarrier := by
    intro cell member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> rfl
  groupFootprintLarge := by
    intro cell member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;>
      simp [group01, group12, consumer01, consumer12,
        TerminalBN6GroupedCell.footprint,
        TerminalV54ConsumerSystem.singletonFootprint]
  groupFootprintsNodup := by
    simp [group01, group12, consumer01, consumer12,
      TerminalBN6GroupedCell.footprint,
      TerminalV54ConsumerSystem.singletonFootprint]
  cutValue := 1
  cutValuePositive := by decide

abbrev Handle := packetFamily.PacketSelectorHandle

instance : DecidableEq Handle := by
  unfold Handle TerminalBN6GroupedFamily.PacketSelectorHandle
  infer_instance

def handle0 : Handle := ⟨0, by decide⟩
def handle1 : Handle := ⟨1, by decide⟩

def rankedEnvironment :
    TerminalPacketTypedRealizerEnvironment Handle 2 where
  rankOf := fun handle => handle
  faithful := fun _handle => true
  hnActive := fun rank => decide (rank = (0 : Fin 2))
  budgetActive := fun rank => decide (rank = (0 : Fin 2))

/-! ## Checked data-only claims -/

def zeroGateIdentity : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def acceptedBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := zeroGateIdentity
  pairing := []
  unmatched := [0]

def malformedBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := redundantIdentityImplementation
  pairing := [(0, 0)]
  unmatched := []

def gainTable : TerminalPacketTypedRealizerTable
    redundantIdentityImplementation packetFamily 2 where
  environment := rankedEnvironment
  claim := fun handle =>
    if handle = handle0 then .bot (.hn 0)
    else .gain acceptedBlueprint

def hnTable : TerminalPacketTypedRealizerTable
    redundantIdentityImplementation packetFamily 2 where
  environment := rankedEnvironment
  claim := fun _handle => .bot (.hn 0)

def budgetTable : TerminalPacketTypedRealizerTable
    redundantIdentityImplementation packetFamily 2 where
  environment := rankedEnvironment
  claim := fun _handle => .bot (.budget 0)

def lowerSeedTable : TerminalPacketTypedRealizerTable
    redundantIdentityImplementation packetFamily 2 where
  environment := rankedEnvironment
  claim := fun handle =>
    if handle = handle0 then .bot (.hn 0)
    else .bot (.lowerSeed handle0)

def malformedGainTable : TerminalPacketTypedRealizerTable
    redundantIdentityImplementation packetFamily 2 where
  environment := rankedEnvironment
  claim := fun _handle => .gain malformedBlueprint

example : gainTable.checkEveryClaim = true := by rfl
example : hnTable.checkEveryClaim = true := by rfl
example : budgetTable.checkEveryClaim = true := by rfl
example : lowerSeedTable.checkEveryClaim = true := by rfl
example : malformedGainTable.checkEveryClaim = false := by rfl

example :
    match gainTable.checkedOutcome (by rfl) handle1 with
    | .gain next _verified => next = zeroGateIdentity
    | .blocked _reason => False := by
  rfl

example :
    match hnTable.checkedOutcome (by rfl) handle0 with
    | .blocked (.hn rank) => rank = (0 : Fin 2)
    | _ => False := by
  rfl

example :
    match budgetTable.checkedOutcome (by rfl) handle1 with
    | .blocked (.budget rank) => rank = (0 : Fin 2)
    | _ => False := by
  rfl

example :
    match lowerSeedTable.checkedOutcome (by rfl) handle1 with
    | .blocked (.lowerSeed lower) => lower = handle0
    | _ => False := by
  rfl

/-! ## Exact rank rows and later-rank gain -/

example : gainTable.selectorsAtRank (0 : Fin 2) = [handle0] := by
  rfl

example : gainTable.selectorsAtRank (1 : Fin 2) = [handle1] := by
  rfl

example : handle1 ∈
    gainTable.selectorsAtRank (rankedEnvironment.rankOf handle1) :=
  gainTable.mem_assignedSelectorRank handle1

def laterRankGainData : PCCMinCheckedPacketSelectorData
    redundantIdentityImplementation Atom Unit where
  family := packetFamily
  rankCount := 2
  table := gainTable
  claimsAccepted := by rfl
  zeroSlackOfSilence := by
    intro allBlocked
    obtain ⟨reason, impossible⟩ :=
      allBlocked (1 : Fin 2) handle1
        ((gainTable.mem_selectorsAtRank_iff (1 : Fin 2) handle1).mpr rfl)
    cases impossible

def isLaterRankZeroGateGain :
    PCCMinRankedSelectorScanOutcome
      laterRankGainData.toRankedSelectorPlan → Bool
  | .gain rank selector _member next _verified =>
      decide (rank.val = 1) && decide (selector.val = 1) &&
        decide (next.gateCount = 0)
  | .silent _allBlocked => false

example : isLaterRankZeroGateGain
    (scanPCCMinRankedSelectors laterRankGainData.toRankedSelectorPlan) = true := by
  native_decide

def laterRankGainOraclePlan :
    PCCMinCheckedPacketRankOrderedOraclePlan
      redundantIdentityImplementation Atom Unit where
  NoHereditary := Unit
  NoBudget := Unit
  hResolve := .noRoute ()
  budgetResolve := fun _ => .noRoute ()
  selectorData := fun _ _ => laterRankGainData

example :
    match laterRankGainOraclePlan.toRankOrderedOraclePlan.route with
    | .gain next _verified => next = zeroGateIdentity
    | _ => False := by
  rfl

/-! ## Complete silence and explicit ZeroSlack closure -/

def zeroSlackHNTable : TerminalPacketTypedRealizerTable
    zeroGateIdentity packetFamily 2 where
  environment := rankedEnvironment
  claim := fun _handle => .bot (.hn 0)

def silentData : PCCMinCheckedPacketSelectorData zeroGateIdentity Atom Unit where
  family := packetFamily
  rankCount := 2
  table := zeroSlackHNTable
  claimsAccepted := by rfl
  zeroSlackOfSilence := fun _allBlocked =>
    { minimum := (residualSlack_eq_zero_iff_minimum zeroGateIdentity).mp (by rfl) }

def silentOraclePlan :
    PCCMinCheckedPacketRankOrderedOraclePlan zeroGateIdentity Atom Unit where
  NoHereditary := Unit
  NoBudget := Unit
  hResolve := .noRoute ()
  budgetResolve := fun _ => .noRoute ()
  selectorData := fun _ _ => silentData

theorem silentAllBlocked :
    ∀ rank selector,
      selector ∈ silentData.toRankedSelectorPlan.selectorsAt rank →
        ∃ reason, silentData.toRankedSelectorPlan.realize rank selector =
          .blocked reason := by
  intro rank selector _member
  exact ⟨.hn (0 : Fin 2), rfl⟩

def isSilentScan :
    PCCMinRankedSelectorScanOutcome silentData.toRankedSelectorPlan → Bool
  | .silent _allBlocked => true
  | .gain _rank _selector _member _next _verified => false

example : isSilentScan
    (scanPCCMinRankedSelectors silentData.toRankedSelectorPlan) = true := by
  native_decide

def isZeroSlackOutcome : PCCMinOracleOutcome zeroGateIdentity → Bool
  | .zeroSlack _result => true
  | _ => false

example : isZeroSlackOutcome
    silentOraclePlan.toRankOrderedOraclePlan.route = true := by
  native_decide

example : IsSemanticallyMinimum zeroGateIdentity :=
  (silentData.zeroSlackOfSilence silentAllBlocked).minimum

/-! ## Total loop composition -/

def emptyFamily : TerminalBN6GroupedFamily Unit Unit where
  carrier := []
  carrierNodup := by simp
  groups := []
  groupCarrier := by simp
  groupFootprintLarge := by simp
  groupFootprintsNodup := by simp
  cutValue := 1
  cutValuePositive := by decide

/-- Exhaustive reference-minimum fixture used only to exercise the recursive
loop adapter.  It is not a polynomial construction of the PCCMin oracle. -/
def referenceFixtureBuilder : PCCMinCheckedPacketRankOrderedOracleBuilder where
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
        selectorData := fun _ _ =>
          { family := emptyFamily
            rankCount := 0
            table :=
              { environment :=
                  { rankOf := fun handle => nomatch handle
                    faithful := fun handle => nomatch handle
                    hnActive := fun rank => nomatch rank
                    budgetActive := fun rank => nomatch rank }
                claim := fun handle => nomatch handle }
            claimsAccepted := by rfl
            zeroSlackOfSilence := fun _ =>
              { minimum :=
                  (residualSlack_eq_zero_iff_minimum current).mp
                    (Nat.eq_zero_of_not_pos positive) } } }

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeCheckedPacketRankOrderedOracleLoop
      pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current :=
  pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete
    pccMinRankOrderedIdentityFixtureNormalizer referenceFixtureBuilder current

end PCCMinCheckedPacketRankedSelectorRegression
end DirectWire
end PNP
