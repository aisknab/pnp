import PNP.Concrete.ResidualReduction.SourceNativeSystemHeader

/-! Capture actual subroutine output and source position, then clear scratch.
A failed subroutine clears system validity and the pending row count. Success
never revives a previously invalid system. Only the designated payload changes. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemCapture
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

inductive Target where | left | payload
def Target.field : Target → Field | .left => .left | .payload => .payload
def recorded (target : Target) (r : Store 14) (s : Saved) : Saved :=
  match target with
  | .left => {s with stream := r.get 0,left := r.get 8}
  | .payload => {s with stream := r.get 0,payload := r.get 8}
def success (r : Store 14) : Bool := match r.get 4 with | true :: _ => true | _ => false
def captured (target : Target) (r : Store 14) (s : Saved) : Saved :=
  if success r then recorded target r s else {recorded target r s with active := [],pending := []}

theorem recorded_stream (target : Target) (r : Store 14) (s : Saved) :
    (recorded target r s).stream = r.get 0 := by cases target <;> rfl
theorem captured_stream (target : Target) (r : Store 14) (s : Saved) :
    (captured target r s).stream = r.get 0 := by
  unfold captured
  split <;> cases target <;> rfl
theorem captured_dimension (target : Target) (r : Store 14) (s : Saved) :
    (captured target r s).dimension = s.dimension := by
  unfold captured
  split <;> cases target <;> rfl

def dispatch : Block 24 := .branch 4 reject reject clean
def block (target : Target) : Block 24 :=
  .seq (save .stream 0) (.seq (save target.field 8) dispatch)
def fuel (r : Store 14) : Nat := 1 + (1 + if success r then 17 else 19)

theorem block_exec (target : Target) (r : Store 14) (s : Saved) :
    Exec (block target) (full r s) (fuel r) (work (r.get 0) [] (captured target r s)) := by
  have first := save_exec .stream r s 0
  have second : Exec (save target.field 8) (full r {s with stream := r.get 0}) 1
      (full r (recorded target r s)) := by
    cases target <;> exact save_exec _ r {s with stream := r.get 0} 8
  have read : (full r (recorded target r s)).get 4 = r.get 4 := working_get r _ 4
  cases signal : r.get 4 with
  | nil =>
    rw [signal] at read
    have bad : Exec reject (full r (recorded target r s)) 18
        (work (r.get 0) [] {recorded target r s with active := [],pending := []}) := by
      simpa only [recorded_stream] using reject_exec r (recorded target r s)
    have last : Exec dispatch (full r (recorded target r s)) 19
        (work (r.get 0) [] {recorded target r s with active := [],pending := []}) := Exec.empty read bad
    simpa only [block,fuel,captured,success,signal,Bool.false_eq_true,↓reduceIte,fieldSet] using
      Exec.seq first (Exec.seq second last)
  | cons bit rest =>
    rw [signal] at read
    cases bit with
    | false =>
      have bad : Exec reject (full r (recorded target r s)) 18
          (work (r.get 0) [] {recorded target r s with active := [],pending := []}) := by
        simpa only [recorded_stream] using reject_exec r (recorded target r s)
      have last : Exec dispatch (full r (recorded target r s)) 19
          (work (r.get 0) [] {recorded target r s with active := [],pending := []}) := Exec.zero read bad
      simpa only [block,fuel,captured,success,signal,Bool.false_eq_true,↓reduceIte,fieldSet] using
        Exec.seq first (Exec.seq second last)
    | true =>
      have good : Exec clean (full r (recorded target r s)) 16 (work (r.get 0) [] (recorded target r s)) := by
        simpa only [recorded_stream] using clean_exec r (recorded target r s)
      have last : Exec dispatch (full r (recorded target r s)) 17 (work (r.get 0) [] (recorded target r s)) :=
        Exec.one read good
      simpa only [block,fuel,captured,success,signal,↓reduceIte,fieldSet] using
        Exec.seq first (Exec.seq second last)

theorem fuel_bound (r : Store 14) : fuel r ≤ 21 := by
  unfold fuel
  cases success r <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

end PNP.Concrete.ResidualReduction.SourceNativeSystemCapture
