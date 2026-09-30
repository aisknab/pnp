import PNP.NANDGuardedSpineJointCoverage
import PNP.NANDJointAsymmetricBound

set_option autoImplicit false
set_option Elab.async false

/-! Every arbitrary proper support of the guarded spine is minimum against
all independent-boundary equivalent NAND programs. Both ends share a primary
input, so the joint physical bounds, not scalar sums, close the proof. -/

namespace PNP.DirectWire.GuardedSpineSupportMinimum
open GuardedSpineFamily (candidate)
open GuardedSpineOpenPrefix
open GuardedSpineOpenSegments
open GuardedSpineJointCoverage
open EssentialInputBound (Essential)
open TightDemandSymmetry (inputSwap)

variable {profileWidth : Nat}

private theorem equivalent_output (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord)
    (output : Fin (terminalInterfacePorts (candidate n) records).length)
    (node : Fin (n + 2))
    (origin : (terminalInterfacePorts (candidate n) records).get output = node) :
    (fun valuation => (word.source output).eval valuation (program.eval valuation)) =
      (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation node) := by
  funext valuation
  have same := equivalent valuation output
  change (word.source output).eval valuation (program.eval valuation) =
    (extractTerminalSupport (candidate n) records).extractedCandidate.semantics valuation output at same
  rw [extractTerminalSupport_semantics] at same
  change (word.source output).eval valuation (program.eval valuation) =
    terminalOpenGateEvaluation (candidate n) records valuation
      ((terminalInterfacePorts (candidate n) records).get output) at same
  rw [origin] at same
  exact same

private theorem prefix_features (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord)
    (last : Fin (n + 1)) (through : Through n records last.val)
    (output : Fin (terminalInterfacePorts (candidate n) records).length)
    (origin : (terminalInterfacePorts (candidate n) records).get output = last.castSucc) :
    (word.source output).eval (fun _ => false) (program.eval (fun _ => false)) = true ∧
      ∀ first second : Fin (terminalBoundaryPorts (candidate n).program records).length,
        first ≠ second →
        Essential (fun input => (word.source output).eval input (program.eval input)) first →
        Essential (fun input => (word.source output).eval input (program.eval input)) second →
        ∃ input, (word.source output).eval input (program.eval input) ≠
          (word.source output).eval (inputSwap first second input)
            (program.eval (inputSwap first second input)) := by
  have same := equivalent_output n records gates program word equivalent output last.castSucc origin
  have valueSame (valuation) := congrFun same valuation
  refine ⟨?_,?_⟩
  · rw [valueSame]
    exact prefix_false n last.val (by have h := last.isLt; omega) records through
  · intro first second different firstEssential secondEssential
    rw [same] at firstEssential secondEssential
    obtain ⟨valuation,changed⟩ := prefix_asymmetric n last.val
      (by have h := last.isLt; omega) records through first second different firstEssential secondEssential
    refine ⟨valuation,?_⟩
    rw [valueSame,valueSame]
    exact changed

/-- Arbitrary selections containing the first but not last gate are minimum. -/
theorem first_only_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (firstSelected : terminalGateSelected records 0 = true)
    (lastOutside : terminalGateSelected records (Fin.last (n + 1)) = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates := by
  have proper : ∃ node, terminalGateSelected records node = false :=
    ⟨Fin.last (n + 1),lastOutside⟩
  obtain ⟨last,through,exported⟩ := proper_prefix_export n records firstSelected proper
  obtain ⟨output,origin⟩ := List.mem_iff_get.mp exported
  obtain ⟨atFalse,asymmetric⟩ := prefix_features n records gates program word equivalent last through output origin
  have joint := equivalent_joint_essential n records proper gates program word equivalent
  have bound := JointAsymmetricBound.asymmetric_bound program (List.ofFn word.source) joint
    (word.source output) (List.mem_ofFn.mpr ⟨output,rfl⟩) atFalse asymmetric
  rw [List.length_ofFn] at bound
  have count := GuardedSpineCounts.first_only_count n records firstSelected lastOutside
  omega

/-- Proper selections containing both ends retain the actual shared guard and
are minimum even against replacements with arbitrary sharing and constants. -/
theorem both_ends_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (firstSelected : terminalGateSelected records 0 = true)
    (lastSelected : terminalGateSelected records (Fin.last (n + 1)) = true)
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates := by
  obtain ⟨last,through,exported⟩ := proper_prefix_export n records firstSelected proper
  obtain ⟨left,originLeft⟩ := List.mem_iff_get.mp exported
  have finalExport := (GuardedSpineCuts.last_interface_iff n records).mpr lastSelected
  obtain ⟨right,originRight⟩ := List.mem_iff_get.mp finalExport
  have distinct : left ≠ right := by
    intro same
    have nodes := originLeft.symm.trans
      ((congrArg (fun output => (terminalInterfacePorts (candidate n) records).get output) same).trans originRight)
    have values := congrArg (fun node : Fin (n + 2) => node.val) nodes
    change last.val = n + 1 at values
    have bound := last.isLt
    omega
  have prefixBound : last.val ≤ n := by have h := last.isLt; omega
  let common := prefixPort n last.val prefixBound records through 0
  have commonWire : (terminalBoundaryPorts (candidate n).program records).get common = .input 0 := by
    rw [prefixPort_get]
    apply congrArg TerminalSupportWire.input
    exact Fin.ext rfl
  have leftSame := equivalent_output n records gates program word equivalent left last.castSucc originLeft
  have rightSame := equivalent_output n records gates program word equivalent right (Fin.last (n + 1)) originRight
  have shared := (prefix_final_common_port n records last through lastSelected proper common).mpr commonWire
  have leftEssential : Essential (fun input => (word.source left).eval input (program.eval input)) common := by
    rw [leftSame]
    exact shared.1
  have rightEssential : Essential (fun input => (word.source right).eval input (program.eval input)) common := by
    rw [rightSame]
    exact shared.2
  have onlyCommon : ∀ index,
      Essential (fun input => (word.source left).eval input (program.eval input)) index →
      Essential (fun input => (word.source right).eval input (program.eval input)) index → index = common := by
    intro index leftEss rightEss
    rw [leftSame] at leftEss
    rw [rightSame] at rightEss
    have wire := (prefix_final_common_port n records last through lastSelected proper index).mp ⟨leftEss,rightEss⟩
    apply Fin.ext
    exact (List.getElem_inj (terminalBoundaryPorts_nodup (candidate n).program records)).mp
      (wire.trans commonWire.symm)
  obtain ⟨atFalse,asymmetric⟩ := prefix_features n records gates program word equivalent last through left originLeft
  have joint := equivalent_joint_essential n records proper gates program word equivalent
  have bound := JointAsymmetricBound.two_output_positions_bound program word joint left right distinct
    common leftEssential rightEssential onlyCommon atFalse asymmetric
  have count := GuardedSpineCounts.both_ends_count n records firstSelected lastSelected
  omega

/-- Complete proper-support result. The only exclusion is the full selected
gate set; no interval, component, rank, coverage or minimum certificate is supplied. -/
theorem proper_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates := by
  cases firstSelected : terminalGateSelected records 0 with
  | false => exact without_first_minimum n records firstSelected gates program word equivalent
  | true =>
      cases lastSelected : terminalGateSelected records (Fin.last (n + 1)) with
      | false => exact first_only_minimum n records firstSelected lastSelected gates program word equivalent
      | true => exact both_ends_minimum n records firstSelected lastSelected proper gates program word equivalent

end PNP.DirectWire.GuardedSpineSupportMinimum
