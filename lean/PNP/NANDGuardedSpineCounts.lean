import PNP.NANDGuardedSpineCuts

set_option autoImplicit false
set_option Elab.async false

/-! Exact cardinalities of the production guarded-spine cut. The finite
transition counters count the actual selector; they do not replace extraction. -/

namespace PNP.DirectWire.GuardedSpineCounts
open GuardedSpineFamily (candidate)
open GuardedSpineCuts

private def indicator (flag : Bool) : Nat := if flag then 1 else 0
private def countFin {width : Nat} (predicate : Fin width → Bool) : Nat :=
  (allFin width).countP predicate

private theorem bool_ext {left right : Bool} (same : left = true ↔ right = true) :
    left = right := by
  cases left <;> cases right
  · rfl
  · exact Bool.noConfusion (same.mpr rfl)
  · exact Bool.noConfusion (same.mp rfl)
  · rfl

private theorem count_congr {width : Nat} (left right : Fin width → Bool)
    (same : ∀ index, left index = right index) : countFin left = countFin right :=
  congrArg countFin (funext same)

private theorem count_succ {width : Nat} (predicate : Fin (width + 1) → Bool) :
    countFin predicate = countFin (fun index : Fin width => predicate index.succ) + indicator (predicate 0) := by
  simp only [countFin,allFin,List.countP_cons,List.countP_map,Function.comp_def,indicator]
  have firstIndex : (⟨0,Nat.zero_lt_succ width⟩ : Fin (width + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_zero]
  rw [firstIndex]

private theorem count_last {width : Nat} (predicate : Fin (width + 1) → Bool) :
    countFin predicate = countFin (fun index : Fin width => predicate index.castSucc) +
      indicator (predicate (Fin.last width)) := by
  induction width with
  | zero => rw [count_succ]; rfl
  | succ width ih =>
      have whole := count_succ predicate
      have shifted := ih (fun index : Fin (width + 1) => predicate index.succ)
      have initialCount := count_succ (fun index : Fin (width + 1) => predicate index.castSucc)
      change countFin (fun index : Fin (width + 1) => predicate index.succ) =
        countFin (fun index : Fin width => predicate index.succ.castSucc) +
          indicator (predicate (Fin.last (width + 1))) at shifted
      have firstIndex : ((0 : Fin (width + 1)).castSucc : Fin (width + 2)) = 0 := by
        apply Fin.ext
        simp only [Fin.val_castSucc,Fin.val_zero]
      rw [firstIndex] at initialCount
      change countFin (fun index : Fin (width + 1) => predicate index.castSucc) =
        countFin (fun index : Fin width => predicate index.succ.castSucc) + indicator (predicate 0) at initialCount
      omega

private theorem count_balance {alpha : Type} (items : List alpha)
    (first second third fourth : alpha → Bool)
    (pointwise : ∀ item, indicator (first item) + indicator (second item) =
      indicator (third item) + indicator (fourth item)) :
    items.countP first + items.countP second = items.countP third + items.countP fourth := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      have point := pointwise head
      unfold indicator at point
      simp only [List.countP_cons]
      omega

/-- Unselected-to-selected transitions between adjacent physical gates. -/
def rises {width : Nat} (selected : Fin (width + 1) → Bool) : Nat :=
  countFin (fun index : Fin width => !selected index.castSucc && selected index.succ)

/-- Selected-to-unselected transitions between adjacent physical gates. -/
def falls {width : Nat} (selected : Fin (width + 1) → Bool) : Nat :=
  countFin (fun index : Fin width => selected index.castSucc && !selected index.succ)

/-- Fragment starts and ends balance, including the two external endpoints. -/
theorem transition_balance {width : Nat} (selected : Fin (width + 1) → Bool) :
    rises selected + (if selected 0 then 1 else 0) =
      falls selected + (if selected (Fin.last width) then 1 else 0) := by
  have localBalance := count_balance (allFin width)
    (fun index : Fin width => !selected index.castSucc && selected index.succ)
    (fun index : Fin width => selected index.castSucc)
    (fun index : Fin width => selected index.castSucc && !selected index.succ)
    (fun index : Fin width => selected index.succ) (by
      intro index
      cases selected index.castSucc <;> cases selected index.succ <;> rfl)
  change rises selected + countFin (fun index : Fin width => selected index.castSucc) =
    falls selected + countFin (fun index : Fin width => selected index.succ) at localBalance
  have first := count_succ selected
  have last := count_last selected
  unfold indicator at first last
  omega

private theorem selection_count {width : Nat} (selected : Fin width → Bool) :
    (terminalSelectedGateIndices selected).length = countFin selected := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [count_last]
      simp only [terminalSelectedGateIndices]
      cases last : selected (Fin.last width) <;>
        simp only [last,Bool.false_eq_true,if_false,if_true,List.length_append,
          List.length_map,List.length_cons,List.length_nil,ih,indicator,Nat.add_zero]

private theorem rise_true (left right : Bool) :
    (!left && right) = true ↔ left = false ∧ right = true := by
  cases left <;> cases right <;> decide

private theorem fall_true (left right : Bool) :
    (left && !right) = true ↔ left = true ∧ right = false := by
  cases left <;> cases right <;> decide

variable {profileWidth : Nat}

private theorem input_guard (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    terminalBoundaryWire (candidate n).program records (.input 0) =
      (terminalGateSelected records 0 || terminalGateSelected records (Fin.last (n + 1))) := by
  apply bool_ext
  rw [← mem_terminalBoundaryPorts_iff,guard_boundary_iff,Bool.or_eq_true]

private theorem input_fresh (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) (index : Fin n) :
    terminalBoundaryWire (candidate n).program records (.input index.succ) =
      terminalGateSelected records index.succ.castSucc :=
  bool_ext ((mem_terminalBoundaryPorts_iff _ _ _).symm.trans
    (fresh_boundary_iff n records index.succ (by simp only [Fin.val_succ]; omega)))

private theorem gate_step (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) (index : Fin (n + 1)) :
    terminalBoundaryWire (candidate n).program records (.gate index.castSucc) =
      (!terminalGateSelected records index.castSucc && terminalGateSelected records index.succ) := by
  apply bool_ext
  rw [← mem_terminalBoundaryPorts_iff,gate_boundary_iff,rise_true]
  constructor
  · rintro ⟨outside,consumer,next,selected⟩
    have same : consumer = index.succ := Fin.ext next
    exact ⟨outside,same ▸ selected⟩
  · rintro ⟨outside,selected⟩
    exact ⟨outside,index.succ,rfl,selected⟩

private theorem gate_final (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    terminalBoundaryWire (candidate n).program records (.gate (Fin.last (n + 1))) = false := by
  apply bool_ext
  constructor
  · intro found
    obtain ⟨_,consumer,next,_⟩ := (gate_boundary_iff n records _).mp
      ((mem_terminalBoundaryPorts_iff _ _ _).mpr found)
    have upper := consumer.isLt
    change consumer.val = (n + 1) + 1 at next
    exfalso
    omega
  · intro impossible
    cases impossible

private theorem interface_step (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) (index : Fin (n + 1)) :
    terminalInterfaceGate (candidate n) records index.castSucc =
      (terminalGateSelected records index.castSucc && !terminalGateSelected records index.succ) :=
  bool_ext (((mem_terminalInterfacePorts_iff _ _ _).symm.trans
    (interface_succ_iff n records index)).trans (fall_true _ _).symm)

private theorem interface_final (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    terminalInterfaceGate (candidate n) records (Fin.last (n + 1)) =
      terminalGateSelected records (Fin.last (n + 1)) :=
  bool_ext ((mem_terminalInterfacePorts_iff _ _ _).symm.trans (last_interface_iff n records))

private theorem boundary_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    (terminalBoundaryPorts (candidate n).program records).length =
      countFin (fun index : Fin n => terminalGateSelected records index.succ.castSucc) +
      indicator (terminalGateSelected records 0 || terminalGateSelected records (Fin.last (n + 1))) +
      rises (terminalGateSelected records) := by
  have inputCount := count_succ (fun index : Fin (n + 1) =>
    terminalBoundaryWire (candidate n).program records (.input index))
  rw [input_guard,count_congr _ _ (input_fresh n records)] at inputCount
  have gateCount := count_last (fun index : Fin (n + 2) =>
    terminalBoundaryWire (candidate n).program records (.gate index))
  rw [gate_final,count_congr _ _ (gate_step n records)] at gateCount
  change countFin (fun index : Fin (n + 2) =>
    terminalBoundaryWire (candidate n).program records (.gate index)) =
      rises (terminalGateSelected records) + 0 at gateCount
  rw [terminalBoundaryPorts_reference,allTerminalSupportWires,
    ← List.countP_eq_length_filter,List.countP_append,List.countP_map,List.countP_map]
  change countFin (fun index : Fin (n + 1) =>
      terminalBoundaryWire (candidate n).program records (.input index)) +
    countFin (fun index : Fin (n + 2) =>
      terminalBoundaryWire (candidate n).program records (.gate index)) = _
  omega

private theorem output_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    (terminalInterfacePorts (candidate n) records).length =
      falls (terminalGateSelected records) +
        indicator (terminalGateSelected records (Fin.last (n + 1))) := by
  change ((allFin (n + 2)).filter (terminalInterfaceGate (candidate n) records)).length = _
  rw [← List.countP_eq_length_filter]
  change countFin (terminalInterfaceGate (candidate n) records) = _
  rw [count_last,interface_final,count_congr _ _ (interface_step n records)]
  rfl

private theorem gate_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    (extractTerminalSupport (candidate n) records).gateCount =
      countFin (fun index : Fin n => terminalGateSelected records index.succ.castSucc) +
      indicator (terminalGateSelected records 0) +
      indicator (terminalGateSelected records (Fin.last (n + 1))) := by
  rw [extractTerminalSupport_gateCount]
  change (terminalSelectedGateIndices (terminalGateSelected records)).length = _
  rw [selection_count,count_last,count_succ]
  rfl

/-- Exact arithmetic for every selection, including the empty and full ones.
No proper-support, contiguity or distinct-record premise is needed. -/
theorem exact_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    (terminalBoundaryPorts (candidate n).program records).length +
      (if terminalGateSelected records 0 then 1 else 0) +
      (if terminalGateSelected records 0 && terminalGateSelected records (Fin.last (n + 1)) then 1 else 0) =
    (extractTerminalSupport (candidate n) records).gateCount +
      (terminalInterfacePorts (candidate n) records).length := by
  have boundary := boundary_count n records
  have output := output_count n records
  have gates := gate_count n records
  have balance := transition_balance (terminalGateSelected records)
  have endpoints :
      indicator (terminalGateSelected records 0 || terminalGateSelected records (Fin.last (n + 1))) +
      indicator (terminalGateSelected records 0 && terminalGateSelected records (Fin.last (n + 1))) =
      indicator (terminalGateSelected records 0) +
      indicator (terminalGateSelected records (Fin.last (n + 1))) := by
    cases terminalGateSelected records 0 <;> cases terminalGateSelected records (Fin.last (n + 1)) <;> rfl
  unfold indicator at boundary output gates endpoints
  omega

theorem both_ends_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (first : terminalGateSelected records 0 = true)
    (last : terminalGateSelected records (Fin.last (n + 1)) = true) :
    (terminalBoundaryPorts (candidate n).program records).length + 2 =
      (extractTerminalSupport (candidate n) records).gateCount +
        (terminalInterfacePorts (candidate n) records).length := by
  have counted := exact_count n records
  rw [first,last] at counted
  change (terminalBoundaryPorts (candidate n).program records).length + 1 + 1 = _ at counted
  omega

theorem first_only_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (first : terminalGateSelected records 0 = true)
    (last : terminalGateSelected records (Fin.last (n + 1)) = false) :
    (terminalBoundaryPorts (candidate n).program records).length + 1 =
      (extractTerminalSupport (candidate n) records).gateCount +
        (terminalInterfacePorts (candidate n) records).length := by
  have counted := exact_count n records
  rw [first,last] at counted
  change (terminalBoundaryPorts (candidate n).program records).length + 1 + 0 = _ at counted
  omega

theorem without_first_count (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (first : terminalGateSelected records 0 = false) :
    (terminalBoundaryPorts (candidate n).program records).length =
      (extractTerminalSupport (candidate n) records).gateCount +
        (terminalInterfacePorts (candidate n) records).length := by
  have counted := exact_count n records
  rw [first] at counted
  change (terminalBoundaryPorts (candidate n).program records).length + 0 + 0 = _ at counted
  omega

end PNP.DirectWire.GuardedSpineCounts
