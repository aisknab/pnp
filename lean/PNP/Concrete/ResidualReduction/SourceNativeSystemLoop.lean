import PNP.Concrete.ResidualReduction.SourceNativeSystemRow

/-! Arbitrarily long row-group conversion by the actual protected counter.
Each step consumes a row and pops the pending count. A failed read clears that
count, so malformed groups stop without executing a caller-supplied witness. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemLoop
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

theorem capture_pending (target : SourceNativeSystemCapture.Target) (r : Store 14) (s : Saved) :
    (SourceNativeSystemCapture.captured target r s).pending = s.pending ∨
      (SourceNativeSystemCapture.captured target r s).pending = [] := by
  unfold SourceNativeSystemCapture.captured
  split
  · cases target <;> exact Or.inl rfl
  · exact Or.inr rfl

theorem sourced_pending (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (SourceNativeSystemRow.sourced input n kind s).pending = s.pending ∨
      (SourceNativeSystemRow.sourced input n kind s).pending = [] := by
  cases kind with
  | zero => exact capture_pending .payload _ s
  | one => exact capture_pending .payload _ s
  | product =>
    let label := SourceNativeSystemLabel.result input n s
    have first : label.pending = s.pending ∨ label.pending = [] := capture_pending .left _ s
    have second := capture_pending .payload
      (SourceNativeTermsInput.result label.stream n true) label
    rcases second with same | failed
    · rcases first with sameLabel | failedLabel
      · exact Or.inl (same.trans sameLabel)
      · exact Or.inr (same.trans failedLabel)
    · exact Or.inr failed

theorem row_pending (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (SourceNativeSystemRow.result input n kind s).pending = s.pending ∨
      (SourceNativeSystemRow.result input n kind s).pending = [] := by
  unfold SourceNativeSystemRow.result SourceNativeSystemRow.committed
  split
  · rw [SourceNativeSystemRows.pending_preserved]
    exact sourced_pending input n kind s
  · exact sourced_pending input n kind s

def after (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) : Saved :=
  let r := SourceNativeSystemRow.result s.stream n kind s
  {r with pending := r.pending.tail}
def step (kind : SourceNativeSystemRow.Kind) : Block 24 :=
  .seq (SourceNativeSystemRow.block kind) (pop .pending)
def stepFuel (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) : Nat :=
  SourceNativeSystemRow.fuel s.stream n kind s + 1

theorem step_exec (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (step kind) (work s.stream [] s) (stepFuel n kind s)
      (work (after n kind s).stream [] (after n kind s)) := by
  have first := SourceNativeSystemRow.block_exec s.stream n kind s dimension
  let r := SourceNativeSystemRow.result s.stream n kind s
  have last := pop_exec .pending
    (Frame.join (SourceScalarState.work r.stream).store (Store.empty 5)) r
  exact Exec.seq first last

def result : Nat → Nat → SourceNativeSystemRow.Kind → Saved → Saved
  | 0,_,_,s => s
  | count + 1,n,kind,s =>
    let next := after n kind s
    if (SourceNativeSystemRow.result s.stream n kind s).pending = [] then next
    else result count n kind next
def fuel : Nat → Nat → SourceNativeSystemRow.Kind → Saved → Nat
  | 0,_,_,_ => 1
  | count + 1,n,kind,s =>
    1 + (stepFuel n kind s +
      if (SourceNativeSystemRow.result s.stream n kind s).pending = [] then 1
      else fuel count n kind (after n kind s))
def block (kind : SourceNativeSystemRow.Kind) : Block 24 := .loop Field.pending.slot (step kind)

theorem after_dimension (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (after n kind s).dimension = s.dimension := SourceNativeSystemRow.dimension_preserved _ _ _ _
theorem after_constant (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (after n kind s).constant = s.constant := SourceNativeSystemRow.constant_preserved _ _ _ _
theorem after_stream_bound (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (after n kind s).stream.length ≤ s.stream.length := SourceNativeSystemRow.stream_bound _ _ _ _

theorem block_exec (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (pending : s.pending = List.replicate count true)
    (dimension : s.dimension = List.replicate n true) :
    Exec (block kind) (work s.stream [] s) (fuel count n kind s)
      (work (result count n kind s).stream [] (result count n kind s)) := by
  induction count generalizing s with
  | zero =>
    have read : (work s.stream [] s).get Field.pending.slot = [] := (field_get .pending _ s).trans pending
    exact Exec.loopStop read
  | succ count ih =>
    have read : (work s.stream [] s).get Field.pending.slot =
        true :: List.replicate count true := by
      exact (field_get .pending _ s).trans (by rw [Field.word,pending,List.replicate_succ])
    have checked := step_exec n kind s dimension
    have dim := (after_dimension n kind s).trans dimension
    by_cases failed : (SourceNativeSystemRow.result s.stream n kind s).pending = []
    · have empty : (after n kind s).pending = [] := by
        change (SourceNativeSystemRow.result s.stream n kind s).pending.tail = []
        rw [failed]
        rfl
      have stop : Exec (block kind) (work (after n kind s).stream [] (after n kind s)) 1
          (work (after n kind s).stream [] (after n kind s)) :=
        Exec.loopStop ((field_get .pending _ (after n kind s)).trans empty)
      simpa only [fuel,result,failed,↓reduceIte,block] using Exec.loopStep read checked stop
    · have unchanged : (SourceNativeSystemRow.result s.stream n kind s).pending = s.pending :=
        (row_pending s.stream n kind s).resolve_right failed
      have remaining : (after n kind s).pending = List.replicate count true := by
        change (SourceNativeSystemRow.result s.stream n kind s).pending.tail = _
        rw [unchanged,pending,List.replicate_succ,List.tail_cons]
      have rest := ih (after n kind s) remaining dim
      simpa only [fuel,result,failed,↓reduceIte,block] using Exec.loopStep read checked rest

theorem dimension_preserved (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result count n kind s).dimension = s.dimension := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    simp only [result]
    split
    · exact after_dimension n kind s
    · exact (ih (after n kind s)).trans (after_dimension n kind s)

theorem constant_preserved (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result count n kind s).constant = s.constant := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    simp only [result]
    split
    · exact after_constant n kind s
    · exact (ih (after n kind s)).trans (after_constant n kind s)

theorem stream_bound (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result count n kind s).stream.length ≤ s.stream.length := by
  induction count generalizing s with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    simp only [result]
    split
    · exact after_stream_bound n kind s
    · exact Nat.le_trans (ih (after n kind s)) (after_stream_bound n kind s)

theorem pending_empty (count n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (pending : s.pending = List.replicate count true) :
    (result count n kind s).pending = [] := by
  induction count generalizing s with
  | zero => exact pending
  | succ count ih =>
    by_cases failed : (SourceNativeSystemRow.result s.stream n kind s).pending = []
    · simp only [result,after,failed,↓reduceIte,List.tail_nil]
    · have unchanged : (SourceNativeSystemRow.result s.stream n kind s).pending = s.pending :=
        (row_pending s.stream n kind s).resolve_right failed
      have remaining : (after n kind s).pending = List.replicate count true := by
        change (SourceNativeSystemRow.result s.stream n kind s).pending.tail = _
        rw [unchanged,pending,List.replicate_succ,List.tail_cons]
      simpa only [result,failed,↓reduceIte] using ih (after n kind s) remaining

theorem fuel_bound (count n limit : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (size : s.stream.length ≤ limit) (dimension : n ≤ 2 * limit)
    (constant : s.constant.length ≤ n + 1) :
    fuel count n kind s ≤ count * (51 * (limit * limit) + 151 * limit + 179) + 1 := by
  induction count generalizing s with
  | zero => simp only [fuel,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ count ih =>
    have first := SourceNativeSystemRow.polynomial_bound s.stream n limit kind s size dimension constant
    have restSize := Nat.le_trans (after_stream_bound n kind s) size
    have restConstant : (after n kind s).constant.length ≤ n + 1 := by
      rw [after_constant]
      exact constant
    have rest := ih (after n kind s) restSize restConstant
    have product : (count + 1) * (51 * (limit * limit) + 151 * limit + 179) =
        count * (51 * (limit * limit) + 151 * limit + 179) +
          (51 * (limit * limit) + 151 * limit + 179) := Nat.succ_mul _ _
    rw [product]
    unfold fuel stepFuel
    split <;> omega

end PNP.Concrete.ResidualReduction.SourceNativeSystemLoop
