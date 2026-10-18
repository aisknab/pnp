import PNP.Concrete.ResidualReduction.SourceNativeSystemSerialize

/-! Closed native-system-to-family converter. Only input register zero is
initially populated. Invalid state or a nonempty trailing suffix emits a failure
tag; every typed native system emits its exact complete target family packet. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def failure : Block 24 := .action (.push 8 false)
def trailer : Block 24 := .branch 0 SourceNativeSystemSerialize.block failure failure
def trailerWord (s : Saved) : BitString :=
  if s.stream.isEmpty then SourceNativeSystemSerialize.word s else [false]
def trailerFuel (s : Saved) : Nat :=
  1 + if s.stream.isEmpty then SourceNativeSystemSerialize.fuel s else 1

theorem trailer_exec (s : Saved) :
    Exec trailer (work s.stream [] s) (trailerFuel s) (work s.stream (trailerWord s) s) := by
  cases stream : s.stream with
  | nil =>
    have read : (work s.stream [] s).get 0 = [] := stream
    have checked : Exec trailer (work s.stream [] s) (1 + SourceNativeSystemSerialize.fuel s)
        (work s.stream (SourceNativeSystemSerialize.word s) s) :=
      Exec.empty read (SourceNativeSystemSerialize.block_exec s.stream s)
    simpa only [trailer,trailerFuel,trailerWord,stream,List.isEmpty_nil,↓reduceIte] using checked
  | cons bit rest =>
    have read : (work s.stream [] s).get 0 = bit :: rest := stream
    have bad : Exec failure (work s.stream [] s) 1 (work s.stream [false] s) := .action _ _
    cases bit with
    | false =>
      simpa only [trailer,trailerFuel,trailerWord,stream,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] using
        (Exec.zero read bad : Exec trailer _ (1 + 1) _)
    | true =>
      simpa only [trailer,trailerFuel,trailerWord,stream,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] using
        (Exec.one read bad : Exec trailer _ (1 + 1) _)

def dispatch : Block 24 := .branch Field.active.slot failure failure trailer
def dispatchWord (s : Saved) : BitString :=
  if SourceNativeSystemRow.active s then trailerWord s else [false]
def dispatchFuel (s : Saved) : Nat :=
  1 + if SourceNativeSystemRow.active s then trailerFuel s else 1

theorem dispatch_exec (s : Saved) :
    Exec dispatch (work s.stream [] s) (dispatchFuel s) (work s.stream (dispatchWord s) s) := by
  have read : (work s.stream [] s).get Field.active.slot = s.active := field_get .active _ s
  have bad : Exec failure (work s.stream [] s) 1 (work s.stream [false] s) := .action _ _
  cases flag : s.active with
  | nil =>
    rw [flag] at read
    simpa only [dispatch,dispatchFuel,dispatchWord,SourceNativeSystemRow.active,flag,Bool.false_eq_true,↓reduceIte] using
      (Exec.empty read bad : Exec dispatch _ (1 + 1) _)
  | cons bit rest =>
    rw [flag] at read
    cases bit with
    | false =>
      simpa only [dispatch,dispatchFuel,dispatchWord,SourceNativeSystemRow.active,flag,Bool.false_eq_true,↓reduceIte] using
        (Exec.zero read bad : Exec dispatch _ (1 + 1) _)
    | true =>
      simpa only [dispatch,dispatchFuel,dispatchWord,SourceNativeSystemRow.active,flag,↓reduceIte] using
        (Exec.one read (trailer_exec s) : Exec dispatch _ (1 + trailerFuel s) _)

theorem dispatch_bound (s : Saved) : dispatchFuel s ≤ SourceNativeSystemSerialize.fuel s + 3 := by
  unfold dispatchFuel trailerFuel
  split
  · split <;> omega
  · omega

def block : Block 24 := .seq SourceNativeSystemParse.block dispatch
def answer (input : BitString) : BitString := dispatchWord (SourceNativeSystemParse.result input)
def fuel (input : BitString) : Nat :=
  SourceNativeSystemParse.fuel input + dispatchFuel (SourceNativeSystemParse.result input)
def budget (L : Nat) : Nat := 17 * SourceNativeSystemParse.budget L + 16 * L + 29

theorem block_exec (input : BitString) :
    Exec block (initial input) (fuel input)
      (work (SourceNativeSystemParse.result input).stream (answer input) (SourceNativeSystemParse.result input)) :=
  Exec.seq (SourceNativeSystemParse.block_exec input) (dispatch_exec (SourceNativeSystemParse.result input))

theorem fuel_bound (input : BitString) : fuel input ≤ budget input.length := by
  have parser := SourceNativeSystemParse.fuel_bound input
  have products := SourceNativeSystemParse.field_bound input .products
  have rows := SourceNativeSystemParse.field_bound input .rows
  have total := SourceNativeSystemParse.field_bound input .total
  have dimension := SourceNativeSystemParse.field_bound input .dimension
  have writer := SourceNativeSystemSerialize.fuel_bound (SourceNativeSystemParse.result input)
    (input.length + SourceNativeSystemParse.budget input.length + 1) products rows total dimension
  have branches := dispatch_bound (SourceNativeSystemParse.result input)
  unfold fuel budget
  omega

theorem invalid_answer (input : BitString) (invalid : (SourceNativeSystemParse.result input).active = []) :
    answer input = [false] := by
  simp only [answer,dispatchWord,SourceNativeSystemRow.active,invalid,Bool.false_eq_true,↓reduceIte]

theorem trailing_answer (input : BitString) (extra : (SourceNativeSystemParse.result input).stream ≠ []) :
    answer input = [false] := by
  unfold answer dispatchWord trailerWord
  split
  · cases stream : (SourceNativeSystemParse.result input).stream with
    | nil => exact False.elim (extra stream)
    | cons bit rest => rfl
  · rfl

theorem canonical_answer {c : Nat} (D : NativeSparseSystem.System c) :
    answer (natural c ++ (NativeSystemCodec.systemCodec c).encode D) = SourceNativeEncoding.familyPacket D := by
  have parsed : SourceNativeSystemParse.result (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceNativeSystemParse.canonical D [] := by
    simpa only [List.append_nil] using SourceNativeSystemParse.canonical_result D []
  simp only [answer,parsed,dispatchWord,SourceNativeSystemRow.active,
    SourceNativeSystemParse.canonical_active,↓reduceIte,trailerWord,SourceNativeSystemParse.canonical_stream,
    List.isEmpty_nil,SourceNativeSystemSerialize.canonical_word]

theorem canonical_extra {c : Nat} (D : NativeSparseSystem.System c)
    (suffix : BitString) (extra : suffix ≠ []) :
    answer (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)) = [false] := by
  apply trailing_answer
  simpa only [SourceNativeSystemParse.canonical_result,SourceNativeSystemParse.canonical_stream] using extra

def parserPolynomial : NatPolynomial :=
  .add (.mul (.constant 2) (.mul .variable (.add (.mul (.constant 51) (.mul .variable .variable)) (.linear 151 179))))
    (.add (.mul (.constant 51) (.mul .variable .variable)) (.linear 180 298))
def sourceFuel : NatPolynomial := .add (.mul (.constant 17) parserPolynomial) (.linear 16 30)
theorem parserPolynomial_eval (L : Nat) : parserPolynomial.eval L = SourceNativeSystemParse.budget L := by
  simp only [parserPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant,
    NatPolynomial.eval_variable,NatPolynomial.eval_linear,SourceNativeSystemParse.budget,Nat.add_assoc]
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = budget L + 1 := by
  simp only [sourceFuel,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant,
    parserPolynomial_eval,NatPolynomial.eval_linear,budget]
  omega

end PNP.Concrete.ResidualReduction.SourceNativeSystemInput
