import PNP.ResidualTerminalBN6HypergraphPacket

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Two-anchor pair packet -/

abbrev BN6TwoAtom := Fin 2

def bn6TwoConsumerSystem : TerminalV54ConsumerSystem BN6TwoAtom where
  carrier := [0, 1]
  carrierNodup := by decide
  consumers := [[0], [1]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem bn6TwoSingletonized :
    bn6TwoConsumerSystem.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6TwoConsumerSystem] at consumerMember
  rcases consumerMember with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

def bn6TwoGroup : TerminalBN6GroupedCell BN6TwoAtom String where
  consumerSystem := bn6TwoConsumerSystem
  singletonized := bn6TwoSingletonized
  atoms := [{ mass := 5, massPositive := by decide, payload := "pair" }]
  atomsNonempty := by simp

def bn6TwoFamily : TerminalBN6GroupedFamily BN6TwoAtom String where
  carrier := [0, 1]
  carrierNodup := by decide
  groups := [bn6TwoGroup]
  groupCarrier := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    rfl
  groupFootprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  groupFootprintsNodup := by decide
  cutValue := 5
  cutValuePositive := by decide

theorem bn6TwoConstant : bn6TwoFamily.ConstantActivation := by
  intro cut cutSublist cutNonempty cutProper
  have cutMember := terminalV53_sublist_mem_terminalListSubsets cutSublist
  simp [bn6TwoFamily, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalBN6GroupedFamily.activationWeight,
    bn6TwoFamily, bn6TwoGroup, bn6TwoConsumerSystem,
    TerminalV54ConsumerSystem.cutActivationBool,
    TerminalV54ConsumerSystem.requestBool, terminalV54Complement,
    TerminalBN6GroupedCell.mass]

example : TerminalBN6PacketConclusion bn6TwoFamily :=
  terminalBN6_hypergraph_packet bn6TwoFamily (by decide) bn6TwoConstant

example : bn6TwoFamily.hypergraph.footprintWeight [0, 1] = 5 := by decide

example : bn6TwoFamily.HasPayloadAt [0, 1] := by
  apply bn6TwoFamily.hasPayloadAt_of_footprintWeight_positive
  decide

/-! ## Three-anchor mixed balanced-triple/full-span packet -/

abbrev BN6ThreeAtom := Fin 3

def bn6ThreePair01System : TerminalV54ConsumerSystem BN6ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[0], [1]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def bn6ThreePair02System : TerminalV54ConsumerSystem BN6ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def bn6ThreePair12System : TerminalV54ConsumerSystem BN6ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def bn6ThreeFullSystem : TerminalV54ConsumerSystem BN6ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[0], [1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem bn6ThreePair01Singletonized :
    bn6ThreePair01System.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6ThreePair01System] at consumerMember
  rcases consumerMember with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem bn6ThreePair02Singletonized :
    bn6ThreePair02System.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6ThreePair02System] at consumerMember
  rcases consumerMember with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

theorem bn6ThreePair12Singletonized :
    bn6ThreePair12System.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6ThreePair12System] at consumerMember
  rcases consumerMember with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem bn6ThreeFullSingletonized :
    bn6ThreeFullSystem.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6ThreeFullSystem] at consumerMember
  rcases consumerMember with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

def bn6ThreePair01Group : TerminalBN6GroupedCell BN6ThreeAtom String where
  consumerSystem := bn6ThreePair01System
  singletonized := bn6ThreePair01Singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := "pair-01" }]
  atomsNonempty := by simp

def bn6ThreePair02Group : TerminalBN6GroupedCell BN6ThreeAtom String where
  consumerSystem := bn6ThreePair02System
  singletonized := bn6ThreePair02Singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := "pair-02" }]
  atomsNonempty := by simp

def bn6ThreePair12Group : TerminalBN6GroupedCell BN6ThreeAtom String where
  consumerSystem := bn6ThreePair12System
  singletonized := bn6ThreePair12Singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := "pair-12" }]
  atomsNonempty := by simp

def bn6ThreeFullGroup : TerminalBN6GroupedCell BN6ThreeAtom String where
  consumerSystem := bn6ThreeFullSystem
  singletonized := bn6ThreeFullSingletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := "full" }]
  atomsNonempty := by simp

def bn6ThreeFamily : TerminalBN6GroupedFamily BN6ThreeAtom String where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  groups := [bn6ThreePair01Group, bn6ThreePair02Group,
    bn6ThreePair12Group, bn6ThreeFullGroup]
  groupCarrier := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl | rfl
    all_goals rfl
  groupFootprintLarge := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl | rfl
    all_goals decide
  groupFootprintsNodup := by decide
  cutValue := 3
  cutValuePositive := by decide

theorem bn6ThreeConstant : bn6ThreeFamily.ConstantActivation := by
  intro cut cutSublist cutNonempty cutProper
  have cutMember := terminalV53_sublist_mem_terminalListSubsets cutSublist
  simp [bn6ThreeFamily, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalBN6GroupedFamily.activationWeight,
    bn6ThreeFamily, bn6ThreePair01Group, bn6ThreePair02Group,
    bn6ThreePair12Group, bn6ThreeFullGroup,
    bn6ThreePair01System, bn6ThreePair02System,
    bn6ThreePair12System, bn6ThreeFullSystem,
    TerminalV54ConsumerSystem.cutActivationBool,
    TerminalV54ConsumerSystem.requestBool, terminalV54Complement,
    TerminalBN6GroupedCell.mass]

example : TerminalBN6PacketConclusion bn6ThreeFamily :=
  terminalBN6_hypergraph_packet bn6ThreeFamily (by decide)
    bn6ThreeConstant

example :
    bn6ThreeFamily.hypergraph.footprintWeight [0, 1] = 1 ∧
    bn6ThreeFamily.hypergraph.footprintWeight [0, 2] = 1 ∧
    bn6ThreeFamily.hypergraph.footprintWeight [1, 2] = 1 ∧
    bn6ThreeFamily.hypergraph.footprintWeight [0, 1, 2] = 1 := by
  decide

example : bn6ThreeFamily.HasPayloadAt [0, 1] ∧
    bn6ThreeFamily.HasPayloadAt [0, 1, 2] := by
  constructor
  · apply bn6ThreeFamily.hasPayloadAt_of_footprintWeight_positive
    decide
  · apply bn6ThreeFamily.hasPayloadAt_of_footprintWeight_positive
    decide

/-! ## Four-anchor full-span packet -/

abbrev BN6FourAtom := Fin 4

def bn6FourFullSystem : TerminalV54ConsumerSystem BN6FourAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [1], [2], [3]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem bn6FourFullSingletonized :
    bn6FourFullSystem.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [bn6FourFullSystem] at consumerMember
  rcases consumerMember with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def bn6FourFullGroup : TerminalBN6GroupedCell BN6FourAtom String where
  consumerSystem := bn6FourFullSystem
  singletonized := bn6FourFullSingletonized
  atoms := [{ mass := 7, massPositive := by decide, payload := "full-4" }]
  atomsNonempty := by simp

def bn6FourFamily : TerminalBN6GroupedFamily BN6FourAtom String where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  groups := [bn6FourFullGroup]
  groupCarrier := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    rfl
  groupFootprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  groupFootprintsNodup := by decide
  cutValue := 7
  cutValuePositive := by decide

theorem bn6FourConstant : bn6FourFamily.ConstantActivation := by
  intro cut cutSublist cutNonempty cutProper
  have cutMember := terminalV53_sublist_mem_terminalListSubsets cutSublist
  simp [bn6FourFamily, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalBN6GroupedFamily.activationWeight,
    bn6FourFamily, bn6FourFullGroup, bn6FourFullSystem,
    TerminalV54ConsumerSystem.cutActivationBool,
    TerminalV54ConsumerSystem.requestBool, terminalV54Complement,
    TerminalBN6GroupedCell.mass]

example : TerminalBN6PacketConclusion bn6FourFamily :=
  terminalBN6_hypergraph_packet bn6FourFamily (by decide)
    bn6FourConstant

example :
    bn6FourFamily.hypergraph.footprintWeight [0, 1] = 0 ∧
    bn6FourFamily.hypergraph.footprintWeight [0, 1, 2] = 0 ∧
    bn6FourFamily.hypergraph.footprintWeight [0, 1, 2, 3] = 7 := by
  decide

/-! ## Hostile boundaries -/

/-- A repeated exact footprint is not a grouped family. -/
example : ¬([bn6ThreePair01Group, bn6ThreePair01Group].map
    TerminalBN6GroupedCell.footprint).Nodup := by
  decide

def bn6HostileNonsingletonSystem :
    TerminalV54ConsumerSystem (Fin 3) where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

/-- The V54-to-BN6 bridge rejects a disjoint nonsingleton consumer. -/
example : ¬bn6HostileNonsingletonSystem.DisjointPairsSingletonized := by
  intro singletonized
  have disjoint : TerminalV54Disjoint ([0, 1] : List (Fin 3)) [2] := by
    simp [TerminalV54Disjoint]
  obtain ⟨leftAtom, _rightAtom, leftEquation, _rightEquation⟩ :=
    singletonized [0, 1] (by simp [bn6HostileNonsingletonSystem])
      [2] (by simp [bn6HostileNonsingletonSystem]) disjoint
  have lengths := congrArg List.length leftEquation
  simp at lengths

def bn6HostileHeavyPair02Group :
    TerminalBN6GroupedCell BN6ThreeAtom String where
  consumerSystem := bn6ThreePair02System
  singletonized := bn6ThreePair02Singletonized
  atoms := [{ mass := 2, massPositive := by decide, payload := "heavy-02" }]
  atomsNonempty := by simp

def bn6HostileUnequalPairFamily :
    TerminalBN6GroupedFamily BN6ThreeAtom String where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  groups := [bn6ThreePair01Group, bn6HostileHeavyPair02Group,
    bn6ThreePair12Group]
  groupCarrier := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl
    all_goals rfl
  groupFootprintLarge := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl
    all_goals decide
  groupFootprintsNodup := by decide
  cutValue := 2
  cutValuePositive := by decide

example : bn6HostileUnequalPairFamily.activationWeight [0] = 3 := by decide
example : bn6HostileUnequalPairFamily.activationWeight [1] = 2 := by decide

/-- Unequal pair masses fail the exact constant-cut premise. -/
example : ¬bn6HostileUnequalPairFamily.ConstantActivation := by
  intro constant
  have declared := constant [0] (by decide) (by simp) (by decide)
  have actual : bn6HostileUnequalPairFamily.activationWeight [0] = 3 := by
    decide
  rw [actual] at declared
  simp [bn6HostileUnequalPairFamily] at declared

#print axioms terminalBN6_hypergraph_packet
#print axioms TerminalBN6GroupedFamily.cutWeight_eq_activationWeight
#print axioms TerminalBN6GroupedFamily.hasPayloadAt_of_footprintWeight_positive

end DirectWire
end PNP
