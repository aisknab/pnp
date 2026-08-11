import PNP.ResidualTerminalConsumerAntichainNormalForm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev V54RegressionAtom := Fin 4

def v54RegressionSingletonSystem :
    TerminalV54ConsumerSystem V54RegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem v54RegressionSingletonized :
    v54RegressionSingletonSystem.DisjointPairsSingletonized := by
  intro left leftMember right rightMember disjoint
  have leftCases : left = [0] ∨ left = [2] := by
    simpa [v54RegressionSingletonSystem] using leftMember
  have rightCases : right = [0] ∨ right = [2] := by
    simpa [v54RegressionSingletonSystem] using rightMember
  rcases leftCases with leftEqual | leftEqual <;>
    rcases rightCases with rightEqual | rightEqual
  all_goals subst left; subst right
  · exact False.elim (disjoint 0 (by simp) (by simp))
  · exact ⟨0, 2, rfl, rfl⟩
  · exact ⟨2, 0, rfl, rfl⟩
  · exact False.elim (disjoint 2 (by simp) (by simp))

/-- The two singleton consumers lie on opposite sides, so both `kappa` and
    the singleton-footprint cut indicator are one. -/
def v54RegressionCrossingSummary : Bool × Bool :=
  (v54RegressionSingletonSystem.cutActivationBool [0, 1],
    v54RegressionSingletonSystem.cutIndicatorBool [0, 1])

example : v54RegressionCrossingSummary = (true, true) := by decide

/-- Putting both singleton consumers on the same side makes both values zero. -/
def v54RegressionNoncrossingSummary : Bool × Bool :=
  (v54RegressionSingletonSystem.cutActivationBool [0, 2],
    v54RegressionSingletonSystem.cutIndicatorBool [0, 2])

example : v54RegressionNoncrossingSummary = (false, false) := by decide

example (cut : List V54RegressionAtom) :
    v54RegressionSingletonSystem.cutActivationBool cut =
      v54RegressionSingletonSystem.cutIndicatorBool cut :=
  terminalV54_consumerAntichain_normal_form
    v54RegressionSingletonSystem v54RegressionSingletonized cut

/-- A nonsingleton disjoint consumer pair makes `kappa` nonzero but is not a
    singleton footprint.  This hostile case demonstrates why the exact PkgC
    singletonization premise cannot be omitted. -/
def v54RegressionNonsingletonSystem :
    TerminalV54ConsumerSystem V54RegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def v54RegressionNonsingletonSummary : Bool × Bool :=
  (v54RegressionNonsingletonSystem.cutActivationBool [0, 1],
    v54RegressionNonsingletonSystem.cutIndicatorBool [0, 1])

example : v54RegressionNonsingletonSummary = (true, false) := by decide

/-- Intersecting minimal consumers admit no disjoint pair and no active cut. -/
def v54RegressionIntersectingSystem :
    TerminalV54ConsumerSystem V54RegressionAtom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  consumers := [[0, 1], [1, 2]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

def v54RegressionIntersectingAnyActive : Bool :=
  (terminalListSubsets v54RegressionIntersectingSystem.carrier).any
    v54RegressionIntersectingSystem.cutActivationBool

example : v54RegressionIntersectingAnyActive = false := by decide

example : ¬ v54RegressionSingletonSystem.RequestActive [] :=
  v54RegressionSingletonSystem.requestActive_empty_false

#print axioms terminalV54_cutActivation_nonzero_iff_disjoint_consumers
#print axioms terminalV54_consumerAntichain_normal_form_iff
#print axioms terminalV54_consumerAntichain_normal_form

end DirectWire
end PNP
