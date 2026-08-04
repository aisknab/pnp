import PNP.ResidualTerminalSaturation

namespace PNP
namespace DirectWire

abbrev terminalSaturationRegressionRecord :=
  TerminalPrimitiveRecord 1 1 2 8

def terminalSaturationRegressionProfileSystem : TerminalProfileSystem 1 2 8 :=
  { role := fun coordinate =>
      match coordinate.val with
      | 0 => .origin
      | 1 => .kernel
      | 2 => .obligation
      | 3 => .prefix
      | 4 => .budget
      | 5 => .saturation
      | 6 => .direction
      | _ => .charge
    observe := fun _implementation _coordinate => false }

def terminalSaturationInterfaceStart : terminalSaturationRegressionRecord :=
  .interface ⟨0, by decide⟩

def terminalSaturationGate : terminalSaturationRegressionRecord :=
  .gate ⟨0, by decide⟩

def terminalSaturationBoundary : terminalSaturationRegressionRecord :=
  .boundary ⟨0, by decide⟩

def terminalSaturationProfile0 : terminalSaturationRegressionRecord :=
  .profile ⟨0, by decide⟩

def terminalSaturationProfile1 : terminalSaturationRegressionRecord :=
  .profile ⟨1, by decide⟩

def terminalSaturationProfile2 : terminalSaturationRegressionRecord :=
  .profile ⟨2, by decide⟩

def terminalSaturationProfile3 : terminalSaturationRegressionRecord :=
  .profile ⟨3, by decide⟩

def terminalSaturationProfile4 : terminalSaturationRegressionRecord :=
  .profile ⟨4, by decide⟩

def terminalSaturationProfile5 : terminalSaturationRegressionRecord :=
  .profile ⟨5, by decide⟩

def terminalSaturationProfile6 : terminalSaturationRegressionRecord :=
  .profile ⟨6, by decide⟩

def terminalSaturationProfile7 : terminalSaturationRegressionRecord :=
  .profile ⟨7, by decide⟩

def terminalSaturationUnrelatedInterface : terminalSaturationRegressionRecord :=
  .interface ⟨1, by decide⟩

/-- One chain exercises all ten named saturation mechanisms.  Edge orientation
    is always included record first, required record second. -/
def terminalSaturationRegressionSystem : TerminalSaturationSystem 1 1 2 8 :=
  { profileSystem := terminalSaturationRegressionProfileSystem
    requires := fun kind dependent required =>
      match kind with
      | .interfaceConsumer => decide (
          required = terminalSaturationGate ∧
            dependent = terminalSaturationInterfaceStart)
      | .gateSource => decide (
          required = terminalSaturationBoundary ∧
            dependent = terminalSaturationGate)
      | .origin => decide (
          required = terminalSaturationProfile0 ∧
            dependent = terminalSaturationBoundary)
      | .kernel => decide (
          required = terminalSaturationProfile1 ∧
            dependent = terminalSaturationProfile0)
      | .obligation => decide (
          required = terminalSaturationProfile2 ∧
            dependent = terminalSaturationProfile1)
      | .prefixTail => decide (
          required = terminalSaturationProfile3 ∧
            dependent = terminalSaturationProfile2)
      | .budget => decide (
          required = terminalSaturationProfile4 ∧
            dependent = terminalSaturationProfile3)
      | .saturation => decide (
          required = terminalSaturationProfile5 ∧
            dependent = terminalSaturationProfile4)
      | .direction => decide (
          required = terminalSaturationProfile6 ∧
            dependent = terminalSaturationProfile5)
      | .charge => decide (
          required = terminalSaturationProfile7 ∧
            dependent = terminalSaturationProfile6) }

def terminalSaturationRegressionSeed : TerminalRawSupport 1 1 2 8 :=
  fun record => record = terminalSaturationInterfaceStart

def terminalSaturationRegressionLargerSeed : TerminalRawSupport 1 1 2 8 :=
  fun record =>
    record = terminalSaturationInterfaceStart ∨
      record = terminalSaturationUnrelatedInterface

theorem terminalSaturationRegressionSeed_subset_larger :
    terminalSaturationRegressionSeed.Subset
      terminalSaturationRegressionLargerSeed := by
  intro record member
  exact Or.inl member

theorem terminalSaturationRegression_start_present :
    terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationInterfaceStart :=
  terminalSaturate_extensive terminalSaturationRegressionSystem
    terminalSaturationRegressionSeed terminalSaturationInterfaceStart rfl

/-- The ten-edge path demonstrates genuine transitive closure rather than a
    one-step expansion. -/
theorem terminalSaturationRegression_all_rules_reach_final :
    terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile7 := by
  have step0 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationGate :=
    TerminalSaturationGenerated.close
      (kind := .interfaceConsumer)
      terminalSaturationRegression_start_present (by rfl)
  have step1 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationBoundary :=
    TerminalSaturationGenerated.close (kind := .gateSource) step0 (by rfl)
  have step2 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile0 :=
    TerminalSaturationGenerated.close (kind := .origin) step1 (by rfl)
  have step3 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile1 :=
    TerminalSaturationGenerated.close (kind := .kernel) step2 (by rfl)
  have step4 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile2 :=
    TerminalSaturationGenerated.close (kind := .obligation) step3 (by rfl)
  have step5 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile3 :=
    TerminalSaturationGenerated.close (kind := .prefixTail) step4 (by rfl)
  have step6 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile4 :=
    TerminalSaturationGenerated.close (kind := .budget) step5 (by rfl)
  have step7 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile5 :=
    TerminalSaturationGenerated.close (kind := .saturation) step6 (by rfl)
  have step8 : terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationProfile6 :=
    TerminalSaturationGenerated.close (kind := .direction) step7 (by rfl)
  exact TerminalSaturationGenerated.close (kind := .charge) step8 (by rfl)

private theorem terminalSaturationRegression_no_edge_to_unrelated
    (kind : TerminalSaturationRuleKind)
    (dependent : terminalSaturationRegressionRecord) :
    terminalSaturationRegressionSystem.requires kind dependent
      terminalSaturationUnrelatedInterface = false := by
  cases kind <;> rfl

theorem terminalSaturationRegression_unrelated_absent :
    ¬terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed terminalSaturationUnrelatedInterface := by
  intro generated
  have avoidsUnrelated :
      (terminalSaturate terminalSaturationRegressionSystem
        terminalSaturationRegressionSeed).Subset
          (fun record => record ≠ terminalSaturationUnrelatedInterface) :=
    terminalSaturate_least terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed
      (fun record => record ≠ terminalSaturationUnrelatedInterface)
      (by
        intro record member equalsUnrelated
        change record = terminalSaturationInterfaceStart at member
        exact (by decide : terminalSaturationUnrelatedInterface ≠
          terminalSaturationInterfaceStart) (equalsUnrelated.symm.trans member))
      (by
        intro kind dependent required _present edge equalsUnrelated
        subst required
        rw [terminalSaturationRegression_no_edge_to_unrelated] at edge
        exact Bool.noConfusion edge)
  exact avoidsUnrelated terminalSaturationUnrelatedInterface generated rfl

example :
    (terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed).Subset
    (terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionLargerSeed) :=
  terminalSaturate_monotone terminalSaturationRegressionSystem
    terminalSaturationRegressionSeed terminalSaturationRegressionLargerSeed
    terminalSaturationRegressionSeed_subset_larger

example :
    terminalSaturate terminalSaturationRegressionSystem
        (terminalSaturate terminalSaturationRegressionSystem
          terminalSaturationRegressionSeed) =
      terminalSaturate terminalSaturationRegressionSystem
        terminalSaturationRegressionSeed :=
  terminalSaturate_idempotent terminalSaturationRegressionSystem
    terminalSaturationRegressionSeed

example :
    (terminalSaturate terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed).Closed
        terminalSaturationRegressionSystem :=
  terminalSaturate_closed terminalSaturationRegressionSystem
    terminalSaturationRegressionSeed

example :
    (saturateSupport terminalSaturationRegressionSystem
      terminalSaturationRegressionSeed).fixed =
      terminalSaturate_idempotent terminalSaturationRegressionSystem
        terminalSaturationRegressionSeed := rfl

example : allTerminalPrimitiveRecords 0 0 0 0 = [] := by rfl

example : terminalSaturationGate ∈ allTerminalPrimitiveRecords 1 1 2 8 :=
  mem_allTerminalPrimitiveRecords terminalSaturationGate

example : terminalSaturationBoundary ∈ allTerminalPrimitiveRecords 1 1 2 8 :=
  mem_allTerminalPrimitiveRecords terminalSaturationBoundary

example : terminalSaturationInterfaceStart ∈
    allTerminalPrimitiveRecords 1 1 2 8 :=
  mem_allTerminalPrimitiveRecords terminalSaturationInterfaceStart

example : terminalSaturationProfile7 ∈ allTerminalPrimitiveRecords 1 1 2 8 :=
  mem_allTerminalPrimitiveRecords terminalSaturationProfile7

/-! A two-record cycle remains a finite fixed point. -/

def terminalSaturationCycleProfileSystem : TerminalProfileSystem 0 0 2 :=
  { role := fun _coordinate => .saturation
    observe := fun _implementation _coordinate => false }

def terminalSaturationCycleFirst : TerminalPrimitiveRecord 0 0 0 2 :=
  .profile ⟨0, by decide⟩

def terminalSaturationCycleSecond : TerminalPrimitiveRecord 0 0 0 2 :=
  .profile ⟨1, by decide⟩

def terminalSaturationCycleSystem : TerminalSaturationSystem 0 0 0 2 :=
  { profileSystem := terminalSaturationCycleProfileSystem
    requires := fun kind dependent required =>
      match kind with
      | .saturation => decide (
          (required = terminalSaturationCycleSecond ∧
            dependent = terminalSaturationCycleFirst) ∨
          (required = terminalSaturationCycleFirst ∧
            dependent = terminalSaturationCycleSecond))
      | _ => false }

def terminalSaturationCycleSeed : TerminalRawSupport 0 0 0 2 :=
  fun record => record = terminalSaturationCycleFirst

theorem terminalSaturationCycle_reaches_second :
    terminalSaturate terminalSaturationCycleSystem
      terminalSaturationCycleSeed terminalSaturationCycleSecond :=
  TerminalSaturationGenerated.close
    (kind := .saturation)
    (terminalSaturate_extensive terminalSaturationCycleSystem
      terminalSaturationCycleSeed terminalSaturationCycleFirst rfl)
    (by rfl)

example :
    terminalSaturate terminalSaturationCycleSystem
        (terminalSaturate terminalSaturationCycleSystem
          terminalSaturationCycleSeed) =
      terminalSaturate terminalSaturationCycleSystem
        terminalSaturationCycleSeed :=
  terminalSaturate_idempotent terminalSaturationCycleSystem
    terminalSaturationCycleSeed

end DirectWire
end PNP
