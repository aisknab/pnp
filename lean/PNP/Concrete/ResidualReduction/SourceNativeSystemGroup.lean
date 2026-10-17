import PNP.Concrete.ResidualReduction.SourceNativeSystemLoop

/-! Complete counted row-group reader. The loop count comes from the actual
strict unary header, not from an initial register or a supplied list. Both
successful groups and malformed inputs have a uniform encoded-size bound. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemGroup
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def prepared (input : BitString) (count : Nat) (s : Saved) : Saved :=
  {s with stream := input,pending := List.replicate count true}
def prepare : Block 24 := .seq (save .pending 1) clean
theorem prepare_exec (input : BitString) (count : Nat) (s : Saved) :
    Exec prepare (withCore (SourceNativeRowIndex.state input count true) {s with stream := input})
      17 (work input [] (prepared input count s)) := by
  let r := Frame.join (SourceNativeRowIndex.state input count true).store (Store.empty 5)
  exact Exec.seq (save_exec .pending r {s with stream := input} 1)
    (clean_exec r (prepared input count s))

def accepted (kind : SourceNativeSystemRow.Kind) : Block 24 :=
  .seq prepare (SourceNativeSystemLoop.block kind)
def dispatch (kind : SourceNativeSystemRow.Kind) : Block 24 :=
  .branch 4 reject (accepted kind) (accepted kind)
def block (kind : SourceNativeSystemRow.Kind) : Block 24 :=
  .seq SourceNativeSystemHeader.headers (dispatch kind)
def result (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) : Saved :=
  let h := MatrixStrictHeader.scan input
  if h.terminated then SourceNativeSystemLoop.result h.count n kind (prepared h.rest h.count s)
  else {s with stream := h.rest,pending := [],active := []}
def fuel (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) : Nat :=
  let h := MatrixStrictHeader.scan input
  MatrixStrictHeader.blockFuel input + 1 +
    (1 + if h.terminated then 17 + SourceNativeSystemLoop.fuel h.count n kind (prepared h.rest h.count s) else 18)

theorem block_exec (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (dimension : s.dimension = List.replicate n true) :
    Exec (block kind) (work input [] s) (fuel input n kind s)
      (work (result input n kind s).stream [] (result input n kind s)) := by
  have first := SourceNativeSystemHeader.headers_exec input s
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    let h := MatrixStrictHeader.scan input
    let r := SourceNativeRowIndex.state h.rest h.count false
    let saved := {s with stream := h.rest}
    have last : Exec (dispatch kind) (withCore r saved) 19
        (work h.rest [] {saved with pending := [],active := []}) :=
      Exec.empty rfl (reject_exec (Frame.join r.store (Store.empty 5)) saved)
    simp only [SourceNativeSystemHeader.headerResult,flag] at first
    simpa only [block,fuel,result,flag,Bool.false_eq_true,↓reduceIte,h,r,saved] using
      Exec.seq first last
  | true =>
    let h := MatrixStrictHeader.scan input
    let saved := prepared h.rest h.count s
    have loop := SourceNativeSystemLoop.block_exec h.count n kind saved rfl dimension
    have body := Exec.seq (prepare_exec h.rest h.count s) loop
    have last : Exec (dispatch kind)
        (withCore (SourceNativeRowIndex.state h.rest h.count true) {s with stream := h.rest})
        (1 + (17 + SourceNativeSystemLoop.fuel h.count n kind saved))
        (work (SourceNativeSystemLoop.result h.count n kind saved).stream []
          (SourceNativeSystemLoop.result h.count n kind saved)) := Exec.one rfl body
    simp only [SourceNativeSystemHeader.headerResult,flag] at first
    simpa only [block,fuel,result,flag,↓reduceIte,h,saved] using Exec.seq first last

theorem dimension_preserved (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result input n kind s).dimension = s.dimension := by
  unfold result
  dsimp only
  split
  · exact SourceNativeSystemLoop.dimension_preserved _ _ _ _
  · rfl

theorem constant_preserved (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result input n kind s).constant = s.constant := by
  unfold result
  dsimp only
  split
  · exact SourceNativeSystemLoop.constant_preserved _ _ _ _
  · rfl

theorem stream_bound (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result input n kind s).stream.length ≤ input.length := by
  have header := MatrixStrictHeader.scan_size input
  have rest : (MatrixStrictHeader.scan input).rest.length ≤ input.length := by omega
  unfold result
  dsimp only
  split
  · exact Nat.le_trans (SourceNativeSystemLoop.stream_bound _ _ _ _) rest
  · exact rest

theorem pending_empty (input : BitString) (n : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved) :
    (result input n kind s).pending = [] := by
  unfold result
  dsimp only
  split
  · exact SourceNativeSystemLoop.pending_empty _ _ _ _ rfl
  · rfl

theorem polynomial_bound (input : BitString) (n limit : Nat) (kind : SourceNativeSystemRow.Kind) (s : Saved)
    (size : input.length ≤ limit) (dimension : n ≤ 2 * limit)
    (constant : s.constant.length ≤ n + 1) :
    fuel input n kind s ≤ limit * (51 * (limit * limit) + 151 * limit + 179) + 4 * limit + 29 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have counts := MatrixStrictHeader.scan_size input
  have countBound : (MatrixStrictHeader.scan input).count ≤ limit := by omega
  have restBound : (MatrixStrictHeader.scan input).rest.length ≤ limit := by omega
  have loop := SourceNativeSystemLoop.fuel_bound (MatrixStrictHeader.scan input).count n limit kind
    (prepared (MatrixStrictHeader.scan input).rest (MatrixStrictHeader.scan input).count s)
    restBound dimension constant
  have product := Nat.mul_le_mul_right (51 * (limit * limit) + 151 * limit + 179) countBound
  unfold fuel
  dsimp only
  split <;> omega

end PNP.Concrete.ResidualReduction.SourceNativeSystemGroup
