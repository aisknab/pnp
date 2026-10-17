import PNP.Concrete.ResidualReduction.SourceNativeSystemLabel

/-! Literal row serialization into two protected reverse buffers. Linear rows
are accumulated separately from product rows so the final family can retain
b/e/a order while the source is read in b/a/e order. The emitted row counter is
incremented only by this actual append routine. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemRows
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

inductive Kind where | linear | product
def Kind.left : Kind → Field | .linear => .payload | .product => .left
def Kind.right : Kind → Field | .linear => .constant | .product => .payload
def Kind.buffer : Kind → Field | .linear => .rows | .product => .products
def word (kind : Kind) (s : Saved) : BitString :=
  false :: (kind.left.word s ++ kind.right.word s)
def stored (kind : Kind) (bytes : BitString) (s : Saved) : Saved :=
  match kind with
  | .linear => {s with rows := bytes,total := true :: s.total}
  | .product => {s with products := bytes,total := true :: s.total}
def result (kind : Kind) (s : Saved) : Saved :=
  stored kind ((word kind s).reverse ++ kind.buffer.word s) s

def prepare (kind : Kind) : Block 24 :=
  .seq (load kind.right 8) (.seq (load kind.left 5) (.action (.clear 0)))
def arrange (kind : Kind) : Block 24 := .seq (.action (.copy 3 8)) (load kind.buffer 8)
def finish (kind : Kind) : Block 24 :=
  .seq (save kind.buffer 8) (.seq (push .total true) clean)
def block (kind : Kind) : Block 24 := .seq (prepare kind)
  (.seq (core SourceChartedSuccessorWords.prepend)
    (.seq (.action (.push 8 false))
      (.seq (arrange kind) (.seq (core ClauseQuery.reverseLoop) (finish kind)))))
def fuel (kind : Kind) (s : Saved) : Nat :=
  8 * (kind.left.word s).length + 4 * (word kind s).length + 34

theorem finish_exec (kind : Kind) (r : Registers) (s : Saved) :
    Exec (finish kind) (withCore r s) 18 (work s.stream [] (stored kind r.output s)) := by
  let scratch := Frame.join r.store (Store.empty 5)
  cases kind with
  | linear =>
    exact Exec.seq (save_exec .rows scratch s 8)
      (Exec.seq (push_exec .total scratch {s with rows := r.output} true)
        (clean_exec scratch {s with rows := r.output,total := true :: s.total}))
  | product =>
    exact Exec.seq (save_exec .products scratch s 8)
      (Exec.seq (push_exec .total scratch {s with products := r.output} true)
        (clean_exec scratch {s with products := r.output,total := true :: s.total}))

theorem block_exec (kind : Kind) (input : BitString) (s : Saved) :
    Exec (block kind) (work input [] s) (fuel kind s)
      (work s.stream [] (result kind s)) := by
  let base := SourceScalarState.work []
  let left := kind.left.word s
  let right := kind.right.word s
  let ready := SourceChartedSuccessorWords.prependReady base left right
  let joined := SourceChartedSuccessorWords.prepended base left right
  let row := {base with output := word kind s}
  let reverseReady := {base with excess := word kind s,output := kind.buffer.word s}
  let reversed := {base with output := (word kind s).reverse ++ kind.buffer.word s}
  have first : Exec (prepare kind) (work input [] s) 3 (withCore ready s) := by
    cases kind <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have concatenate : Exec SourceChartedSuccessorWords.prepend ready.store
      (8 * left.length + 9) joined.store := SourceChartedSuccessorWords.prepend_exec base left right
  have tag : Exec (.action (.push (8 : Fin 24) false)) (withCore joined s) 1 (withCore row s) :=
    .action _ _
  have arrangeRow : Exec (arrange kind) (withCore row s) 2 (withCore reverseReady s) := by
    cases kind <;> exact Exec.seq (.action _ _) (.action _ _)
  have reversal : Exec ClauseQuery.reverseLoop reverseReady.store
      (4 * (word kind s).length + 1) reversed.store := by
    exact ClauseQuery.reverse_exec {base with output := kind.buffer.word s} (word kind s)
  have last : Exec (finish kind) (withCore reversed s) 18 (work s.stream [] (result kind s)) :=
    finish_exec kind reversed s
  have checked := Exec.seq first (Exec.seq (core_exec concatenate s)
    (Exec.seq tag (Exec.seq arrangeRow (Exec.seq (core_exec reversal s) last))))
  have cost : fuel kind s =
      3 + ((8 * left.length + 9) + (1 + (2 + ((4 * (word kind s).length + 1) + 18)))) := by
    unfold fuel left
    omega
  simpa only [block,cost] using checked

theorem stream_preserved (kind : Kind) (s : Saved) : (result kind s).stream = s.stream := by
  cases kind <;> rfl
theorem dimension_preserved (kind : Kind) (s : Saved) : (result kind s).dimension = s.dimension := by
  cases kind <;> rfl
theorem pending_preserved (kind : Kind) (s : Saved) : (result kind s).pending = s.pending := by
  cases kind <;> rfl
theorem active_preserved (kind : Kind) (s : Saved) : (result kind s).active = s.active := by
  cases kind <;> rfl
theorem total_length (kind : Kind) (s : Saved) : (result kind s).total.length = s.total.length + 1 := by
  cases kind <;> rfl
theorem buffer_eq (kind : Kind) (s : Saved) :
    kind.buffer.word (result kind s) = (word kind s).reverse ++ kind.buffer.word s := by
  cases kind <;> rfl
theorem word_length (kind : Kind) (s : Saved) :
    (word kind s).length = (kind.left.word s).length + (kind.right.word s).length + 1 := by
  simp only [word,List.length_cons,List.length_append]
theorem fuel_bound (kind : Kind) (s : Saved) (n : Nat)
    (left : (kind.left.word s).length ≤ n + 1)
    (right : (kind.right.word s).length ≤ n + 1) :
    fuel kind s ≤ 16 * n + 54 := by
  unfold fuel
  rw [word_length]
  omega

end PNP.Concrete.ResidualReduction.SourceNativeSystemRows
