import PNP.NANDGuardedSpineOpenSegments

set_option autoImplicit false
set_option Elab.async false

/-! Every actual boundary port of a proper guarded-spine support is essential
to an exported function. Transport to all semantically equivalent replacements
preserves output positions, including repeated demanded source values. -/

namespace PNP.DirectWire.GuardedSpineJointCoverage
open GuardedSpineFamily (candidate)
open GuardedSpineOpenPrefix
open GuardedSpineOpenSegments
open EssentialInputBound DemandDeficit

variable {profileWidth : Nat}

private theorem forward_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (remaining : Nat) (first : Fin (n + 2)) (endAt : first.val + remaining = n + 1)
    (selected : terminalGateSelected records first = true) :
    ∃ last : Fin (n + 2), first.val ≤ last.val ∧
      last ∈ terminalInterfacePorts (candidate n) records ∧
      ∀ node : Fin (n + 2), first.val ≤ node.val → node.val ≤ last.val →
        terminalGateSelected records node = true := by
  induction remaining generalizing first with
  | zero =>
      refine ⟨first,Nat.le_refl _,?_,?_⟩
      · apply (GuardedSpineCuts.interface_iff n records first).mpr
        exact ⟨selected,Or.inl (by omega)⟩
      · intro node after before
        have same : node = first := Fin.ext (by omega)
        rw [same]
        exact selected
  | succ remaining ih =>
      let next : Fin (n + 2) := ⟨first.val + 1,by omega⟩
      cases nextSelected : terminalGateSelected records next with
      | false =>
          refine ⟨first,Nat.le_refl _,?_,?_⟩
          · apply (GuardedSpineCuts.interface_iff n records first).mpr
            exact ⟨selected,Or.inr ⟨next,rfl,nextSelected⟩⟩
          · intro node after before
            have same : node = first := Fin.ext (by omega)
            rw [same]
            exact selected
      | true =>
          have remainingEnd : next.val + remaining = n + 1 := by
            change first.val + 1 + remaining = n + 1
            omega
          rcases ih next remainingEnd nextSelected with ⟨last,after,exported,interval⟩
          refine ⟨last,by change first.val + 1 ≤ last.val at after; omega,exported,?_⟩
          intro node fromFirst before
          by_cases sameValue : node.val = first.val
          · have same : node = first := Fin.ext sameValue
            rw [same]
            exact selected
          · apply interval node
            · change first.val + 1 ≤ node.val
              omega
            · exact before

/-- Follow a selected run to a real output interface without assuming a partition. -/
theorem selected_reaches_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (first : Fin (n + 2)) (selected : terminalGateSelected records first = true) :
    ∃ last : Fin (n + 2), first.val ≤ last.val ∧
      last ∈ terminalInterfacePorts (candidate n) records ∧
      ∀ node : Fin (n + 2), first.val ≤ node.val → node.val ≤ last.val →
        terminalGateSelected records node = true :=
  forward_export n records (n + 1 - first.val) first (by have h := first.isLt; omega) selected

private theorem boundary_lookup_injective (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    Function.Injective (fun index : Fin (terminalBoundaryPorts (candidate n).program records).length =>
      (terminalBoundaryPorts (candidate n).program records).get index) := by
  intro left right same
  apply Fin.ext
  exact (List.getElem_inj (terminalBoundaryPorts_nodup (candidate n).program records)).mp same

private theorem proper_initial_bound (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (last : Fin (n + 2)) (through : Through n records last.val) : last.val ≤ n := by
  by_cases bound : last.val ≤ n
  · exact bound
  · rcases proper with ⟨node,outside⟩
    have selected := through node (by have h := node.isLt; omega)
    rw [selected] at outside
    cases outside

private theorem prefix_wire_essential (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (last : Fin (n + 2)) (bound : last.val ≤ n) (through : Through n records last.val)
    (primary : Fin (n + 1)) (before : primary.val ≤ last.val)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (wire : (terminalBoundaryPorts (candidate n).program records).get port = .input primary) :
    Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) port := by
  apply (prefix_essential_iff n last.val bound records through port).mpr
  refine ⟨⟨primary.val,by omega⟩,?_⟩
  apply boundary_lookup_injective n records
  dsimp only
  rw [prefixPort_get,wire]

private theorem segment_wire_essential (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length)
    (index : Fin (length + 1))
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (wire : (terminalBoundaryPorts (candidate n).program records).get port =
      segmentWire n start length bound index) :
    Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
      ⟨start + length,by omega⟩) port := by
  apply (segment_essential_iff n start length bound positive records span port).mpr
  refine ⟨index,?_⟩
  apply boundary_lookup_injective n records
  dsimp only
  rw [segmentPort_get,wire]

private theorem guard_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (wire : (terminalBoundaryPorts (candidate n).program records).get port = .input 0) :
    ∃ last : Fin (n + 2), last ∈ terminalInterfacePorts (candidate n) records ∧
      Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) port := by
  have member : TerminalSupportWire.input 0 ∈ terminalBoundaryPorts (candidate n).program records := by
    rw [← wire]
    exact List.get_mem _ port
  rcases (GuardedSpineCuts.guard_boundary_iff n records).mp member with first | finalSelected
  · rcases proper_prefix_export n records first proper with ⟨last,through,exported⟩
    refine ⟨last.castSucc,exported,?_⟩
    exact prefix_wire_essential n records last.castSucc (by change last.val ≤ n; have h := last.isLt; omega)
      through 0 (by simp only [Fin.val_zero]; omega) port wire
  · rcases proper_final_component n records finalSelected proper with
      ⟨start,length,positive,total,span⟩
    have bound : start + length ≤ n + 1 := Nat.le_of_eq total
    have essential := segment_wire_essential n start length bound positive records span
      (Fin.last length) port (by
        rw [wire]
        have nonzero : length ≠ 0 := by omega
        simp only [segmentWire,Fin.val_last,dif_neg nonzero,dif_pos total])
    have lastIndex : (⟨start + length,by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
      Fin.ext total
    rw [lastIndex] at essential
    exact ⟨Fin.last (n + 1),(GuardedSpineCuts.last_interface_iff n records).mpr finalSelected,essential⟩

private theorem fresh_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (primary : Fin (n + 1)) (positiveInput : 0 < primary.val)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (wire : (terminalBoundaryPorts (candidate n).program records).get port = .input primary) :
    ∃ last : Fin (n + 2), last ∈ terminalInterfacePorts (candidate n) records ∧
      Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) port := by
  have member : TerminalSupportWire.input primary ∈ terminalBoundaryPorts (candidate n).program records := by
    rw [← wire]
    exact List.get_mem _ port
  have selected := (GuardedSpineCuts.fresh_boundary_iff n records primary positiveInput).mp member
  rcases selected_reaches_export n records primary.castSucc selected with
    ⟨last,after,exported,interval⟩
  change primary.val ≤ last.val at after
  have selectedLast := interval last after (Nat.le_refl _)
  rcases selected_component n records last.val last.isLt selectedLast with
    initial | ⟨start,length,positive,total,span⟩
  · exact ⟨last,exported,prefix_wire_essential n records last
      (proper_initial_bound n records proper last initial) initial primary after port wire⟩
  · have bound : start + length ≤ n + 1 := by have h := last.isLt; omega
    have gapBefore : start < primary.val := by
      by_cases reverse : primary.val ≤ start
      · have outside := span.1 ⟨start,by omega⟩ rfl
        have inside := interval ⟨start,by omega⟩ reverse (by change start ≤ last.val; omega)
        rw [inside] at outside
        cases outside
      · omega
    let index : Fin (length + 1) := ⟨primary.val - start,by omega⟩
    have indexPositive : index.val ≠ 0 := by change primary.val - start ≠ 0; omega
    have inputValue : start + index.val = primary.val := by change start + (primary.val - start) = primary.val; omega
    have notFinal : start + index.val ≠ n + 1 := by have h := primary.isLt; omega
    have essential := segment_wire_essential n start length bound positive records span index port (by
      rw [wire]
      simp only [segmentWire,dif_neg indexPositive,dif_neg notFinal]
      apply congrArg TerminalSupportWire.input
      apply Fin.ext
      exact inputValue.symm)
    have lastIndex : (⟨start + length,by omega⟩ : Fin (n + 2)) = last := Fin.ext total
    rw [lastIndex] at essential
    exact ⟨last,exported,essential⟩

private theorem gate_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (producer : Fin (n + 2))
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (wire : (terminalBoundaryPorts (candidate n).program records).get port = .gate producer) :
    ∃ last : Fin (n + 2), last ∈ terminalInterfacePorts (candidate n) records ∧
      Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) port := by
  have member : TerminalSupportWire.gate producer ∈ terminalBoundaryPorts (candidate n).program records := by
    rw [← wire]
    exact List.get_mem _ port
  rcases (GuardedSpineCuts.gate_boundary_iff n records producer).mp member with
    ⟨outside,consumer,next,selected⟩
  rcases selected_reaches_export n records consumer selected with ⟨last,after,exported,interval⟩
  have selectedLast := interval last after (Nat.le_refl _)
  rcases selected_component n records last.val last.isLt selectedLast with
    initial | ⟨start,length,positive,total,span⟩
  · have inside := initial producer (by omega)
    rw [inside] at outside
    cases outside
  · have bound : start + length ≤ n + 1 := by have h := last.isLt; omega
    have gapEqual : start = producer.val := by
      by_cases earlier : start < producer.val
      · have inside := span.2 producer earlier (by omega)
        rw [inside] at outside
        cases outside
      · by_cases later : producer.val < start
        · have atGap := span.1 ⟨start,by omega⟩ rfl
          have inside := interval ⟨start,by omega⟩ (by change consumer.val ≤ start; omega)
            (by change start ≤ last.val; omega)
          rw [inside] at atGap
          cases atGap
        · omega
    have essential := segment_wire_essential n start length bound positive records span 0 port (by
      rw [wire]
      simp only [segmentWire,Fin.val_zero]
      apply congrArg TerminalSupportWire.gate
      exact Fin.ext gapEqual.symm)
    have lastIndex : (⟨start + length,by omega⟩ : Fin (n + 2)) = last := Fin.ext total
    rw [lastIndex] at essential
    exact ⟨last,exported,essential⟩

/-- Every actual incoming port of a proper support is essential to an export. -/
theorem boundary_essential_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length) :
    ∃ last : Fin (n + 2), last ∈ terminalInterfacePorts (candidate n) records ∧
      Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) port := by
  cases wire : (terminalBoundaryPorts (candidate n).program records).get port with
  | input primary =>
      by_cases zero : primary.val = 0
      · have same : primary = 0 := Fin.ext zero
        rw [same] at wire
        exact guard_export n records proper port wire
      · exact fresh_export n records proper primary (Nat.pos_of_ne_zero zero) port wire
  | gate producer => exact gate_export n records producer port wire

/-- The coverage is for the actual ordered extracted output functions. -/
theorem extracted_joint_essential (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length) :
    ∃ output : Fin (terminalInterfacePorts (candidate n) records).length,
      Essential (fun valuation =>
        (extractTerminalSupport (candidate n) records).extractedCandidate.semantics valuation output) port := by
  rcases boundary_essential_export n records proper port with ⟨last,member,essential⟩
  rcases List.mem_iff_get.mp member with ⟨output,origin⟩
  refine ⟨output,?_⟩
  have same : (fun valuation =>
      (extractTerminalSupport (candidate n) records).extractedCandidate.semantics valuation output) =
      (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation last) := by
    funext valuation
    rw [extractTerminalSupport_semantics]
    change terminalOpenGateEvaluation (candidate n) records valuation
      ((terminalInterfacePorts (candidate n) records).get output) = _
    rw [origin]
  rw [same]
  exact essential

/-- Arbitrary equivalent replacements inherit joint essentiality. Output source
values are not deduplicated; the list retains every output position. -/
theorem equivalent_joint_essential (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    JointEssential program (List.ofFn word.source) := by
  intro port
  rcases extracted_joint_essential n records proper port with ⟨output,essential⟩
  refine ⟨word.source output,List.mem_ofFn.mpr ⟨output,rfl⟩,?_⟩
  have same : (fun valuation => (word.source output).eval valuation (program.eval valuation)) =
      (fun valuation => (extractTerminalSupport (candidate n) records).extractedCandidate.semantics
        valuation output) := by
    funext valuation
    exact equivalent valuation output
  rw [same]
  exact essential

theorem equivalent_fanin_bound (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (proper : ∃ node, terminalGateSelected records node = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (terminalBoundaryPorts (candidate n).program records).length ≤
      (terminalInterfacePorts (candidate n) records).length + gates := by
  have lower := joint_required_length program (List.ofFn word.source)
    (equivalent_joint_essential n records proper gates program word equivalent)
  have upper := required_length program (List.ofFn word.source)
  rw [List.length_ofFn] at upper
  exact Nat.le_trans lower upper

/-- First complete minimum case: every support omitting the initial gate is
minimum against every equivalent NAND program, with arbitrary sharing. -/
theorem without_first_minimum (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (firstOutside : terminalGateSelected records 0 = false)
    (gates : Nat)
    (program : Program (terminalBoundaryPorts (candidate n).program records).length gates)
    (word : DirectWireWord (terminalBoundaryPorts (candidate n).program records).length gates
      (terminalInterfacePorts (candidate n) records).length)
    (equivalent : Equivalent program word
      (extractTerminalSupport (candidate n) records).extractedCandidate.program
      (extractTerminalSupport (candidate n) records).extractedCandidate.directWireWord) :
    (extractTerminalSupport (candidate n) records).gateCount ≤ gates := by
  have lower := equivalent_fanin_bound n records ⟨0,firstOutside⟩ gates program word equivalent
  have count := GuardedSpineCounts.without_first_count n records firstOutside
  omega

end PNP.DirectWire.GuardedSpineJointCoverage
