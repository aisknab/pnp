import PNP.ResidualTerminalConstantCutHypergraphRigidity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev V53TwoAtom := Fin 2

def v53TwoAnchorSystem : TerminalV53Hypergraph V53TwoAtom where
  carrier := [0, 1]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 5
  cutValuePositive := by simp

theorem v53TwoAnchorConstant :
    v53TwoAnchorSystem.ConstantProperCuts := by
  intro cut proper
  have cutMember :=
    terminalV53_sublist_mem_terminalListSubsets proper.1
  simp [v53TwoAnchorSystem, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalV53Hypergraph.ProperCut,
    TerminalV53Hypergraph.cutWeight,
    TerminalV53Hyperedge.cutContribution,
    TerminalV53Hyperedge.crossesBool, v53TwoAnchorSystem]

example :
    v53TwoAnchorSystem.footprintWeight v53TwoAnchorSystem.carrier = 5 := by
  decide

example :
    v53TwoAnchorSystem.footprintWeight v53TwoAnchorSystem.carrier =
      v53TwoAnchorSystem.cutValue :=
  (terminalV53_constantCut_hypergraph_rigidity v53TwoAnchorSystem
    (by decide) v53TwoAnchorConstant).1 (by decide)

abbrev V53ThreeAtom := Fin 3

def v53ThreeAnchorSystem : TerminalV53Hypergraph V53ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  cells := [
    { footprint := [0, 1], mass := 1 },
    { footprint := [0, 2], mass := 1 },
    { footprint := [1, 2], mass := 1 },
    { footprint := [0, 1, 2], mass := 1 }
  ]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl | rfl
    all_goals decide
  footprintLarge := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl | rfl
    all_goals simp
  massPositive := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl | rfl
    all_goals simp
  cutValue := 3
  cutValuePositive := by simp

theorem v53ThreeAnchorConstant :
    v53ThreeAnchorSystem.ConstantProperCuts := by
  intro cut proper
  have cutMember :=
    terminalV53_sublist_mem_terminalListSubsets proper.1
  simp [v53ThreeAnchorSystem, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalV53Hypergraph.ProperCut,
    TerminalV53Hypergraph.cutWeight,
    TerminalV53Hyperedge.cutContribution,
    TerminalV53Hyperedge.crossesBool, v53ThreeAnchorSystem]

example :
    v53ThreeAnchorSystem.footprintWeight [0, 1] = 1 ∧
    v53ThreeAnchorSystem.footprintWeight [0, 2] = 1 ∧
    v53ThreeAnchorSystem.footprintWeight [1, 2] = 1 ∧
    v53ThreeAnchorSystem.footprintWeight v53ThreeAnchorSystem.carrier = 1 := by
  decide

example : ∃ p,
    (∀ footprint, footprint.Sublist v53ThreeAnchorSystem.carrier ->
      footprint.length = 2 ->
      v53ThreeAnchorSystem.footprintWeight footprint = p) ∧
    v53ThreeAnchorSystem.footprintWeight v53ThreeAnchorSystem.carrier +
      2 * p = v53ThreeAnchorSystem.cutValue :=
  (terminalV53_constantCut_hypergraph_rigidity v53ThreeAnchorSystem
    (by decide) v53ThreeAnchorConstant).2.1 (by decide)

abbrev V53FourAtom := Fin 4

def v53FourAnchorSystem : TerminalV53Hypergraph V53FourAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1, 2, 3], mass := 7 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 7
  cutValuePositive := by simp

theorem v53FourAnchorConstant :
    v53FourAnchorSystem.ConstantProperCuts := by
  intro cut proper
  have cutMember :=
    terminalV53_sublist_mem_terminalListSubsets proper.1
  simp [v53FourAnchorSystem, terminalListSubsets] at cutMember
  rcases cutMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [TerminalV53Hypergraph.ProperCut,
    TerminalV53Hypergraph.cutWeight,
    TerminalV53Hyperedge.cutContribution,
    TerminalV53Hyperedge.crossesBool, v53FourAnchorSystem]

example :
    v53FourAnchorSystem.footprintWeight [0, 1] = 0 ∧
    v53FourAnchorSystem.footprintWeight [0, 1, 2] = 0 ∧
    v53FourAnchorSystem.footprintWeight v53FourAnchorSystem.carrier = 7 := by
  decide

example :
    (∀ footprint, footprint.Sublist v53FourAnchorSystem.carrier ->
      2 ≤ footprint.length ->
      footprint ≠ v53FourAnchorSystem.carrier ->
      v53FourAnchorSystem.footprintWeight footprint = 0) ∧
    v53FourAnchorSystem.footprintWeight v53FourAnchorSystem.carrier =
      v53FourAnchorSystem.cutValue :=
  (terminalV53_constantCut_hypergraph_rigidity v53FourAnchorSystem
    (by decide) v53FourAnchorConstant).2.2 (by decide)

/-- Hostile data with unequal pair weights fails the constant-cut premise:
    the singleton cuts at anchors `0` and `2` have different values. -/
def v53HostileUnequalPairSystem : TerminalV53Hypergraph V53ThreeAtom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  cells := [
    { footprint := [0, 1], mass := 1 },
    { footprint := [0, 2], mass := 2 },
    { footprint := [1, 2], mass := 1 }
  ]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl
    all_goals decide
  footprintLarge := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl
    all_goals simp
  massPositive := by
    intro cell cellMember
    simp at cellMember
    rcases cellMember with rfl | rfl | rfl
    all_goals simp
  cutValue := 2
  cutValuePositive := by simp

example : v53HostileUnequalPairSystem.cutWeight [0] = 3 := by decide
example : v53HostileUnequalPairSystem.cutWeight [2] = 3 := by decide
example : v53HostileUnequalPairSystem.cutWeight [1] = 2 := by decide
example : ¬ v53HostileUnequalPairSystem.ConstantProperCuts := by
  intro constant
  have zeroProper : v53HostileUnequalPairSystem.ProperCut [0] := by
    refine ⟨?_, by simp, ?_⟩
    · exact List.Sublist.cons_cons 0
        (List.Sublist.cons 1
          (List.Sublist.cons 2 List.Sublist.slnil))
    · intro singletonCarrier
      have lengths := congrArg List.length singletonCarrier
      simp [v53HostileUnequalPairSystem] at lengths
  have declared := constant [0] zeroProper
  have actual : v53HostileUnequalPairSystem.cutWeight [0] = 3 := by decide
  change v53HostileUnequalPairSystem.cutWeight [0] = 2 at declared
  rw [actual] at declared
  simp at declared

#print axioms terminalV53_constantCut_hypergraph_rigidity
#print axioms TerminalV53Hypergraph.threeAnchor_rigidity
#print axioms TerminalV53Hypergraph.fourAnchor_rigidity

end DirectWire
end PNP
