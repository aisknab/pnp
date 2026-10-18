import PNP.Concrete.ResidualReduction.SourceReductionChain
import PNP.Concrete.ResidualReduction.NativeSourceCoordinates
import PNP.Concrete.NativeNormalization.NativeBitCodec

/-! Finite encodings of the complete source-reduction result and its history.
The size bound below applies to the actual source-derived chain. It is a
representation bound, not an execution-time bound or a complete SAT solver. -/

namespace PNP.Concrete.ResidualReduction.SourceEncoding
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

def unitCodec : Codec Unit where
  encode _ := []
  parse bits := some ((), bits)
  roundtrip := by intro a suffix; cases a; rfl
  sound := by intro bits a suffix h; cases a; cases h; rfl

/-- The tag is encoded before the data whose type it determines. -/
def dependentCodec {A : Type} {B : A → Type} (tag : Codec A)
    (payload : (a : A) → Codec (B a)) : Codec (Sigma B) where
  encode x := tag.encode x.1 ++ (payload x.1).encode x.2
  parse bits := (tag.parse bits).bind fun (a, rest) =>
    ((payload a).parse rest).bind fun (b, suffix) => some (⟨a, b⟩, suffix)
  roundtrip := by
    rintro ⟨a, b⟩ suffix
    simp only [List.append_assoc, tag.roundtrip, Option.bind_some,
      (payload a).roundtrip]
  sound := by
    intro bits x suffix h
    cases ht : tag.parse bits with
    | none => simp only [ht, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨a, rest⟩
      cases hp : (payload a).parse rest with
      | none => simp only [ht, Option.bind_some, hp, Option.bind_none] at h; cases h
      | some last =>
        rcases last with ⟨b, tail⟩
        have he : ((⟨a, b⟩ : Sigma B), tail) = (x, suffix) := by
          simpa only [ht, Option.bind_some, hp, Option.some.injEq] using h
        cases he
        simpa only [List.append_assoc] using
          (congrArg (fun rest => tag.encode a ++ rest)
            ((payload a).sound rest b _ hp)).trans (tag.sound bits a rest ht)

def tupleCodec {Z : Type} (base : Codec Z) : (n : Nat) → Codec (Tuple Z n)
  | 0 => base
  | n + 1 => pairCodec bitCodec (tupleCodec base n)

def pointCodec (n : Nat) : Codec (Point n) := tupleCodec unitCodec n
def affineCodec (n : Nat) : Codec (Affine n) := tupleCodec bitCodec n

theorem point_bytes {n : Nat} (x : Point n) :
    (pointCodec n).encode x = NativeSource.pointBytes x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    change b :: (pointCodec n).encode x = b :: NativeSource.pointBytes x
    rw [ih x]

theorem point_length {n : Nat} (x : Point n) :
    ((pointCodec n).encode x).length = n := by
  rw [point_bytes, NativeSource.pointBytes_length]

theorem affine_length {n : Nat} (a : Affine n) :
    ((affineCodec n).encode a).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change ((affineCodec n).encode a).length + 1 = (n + 1) + 1
    rw [ih a]

def rowCodec (n : Nat) : Codec (Row n) :=
  mappedCodec (pairCodec bitCodec (pairCodec (affineCodec n) (affineCodec n)))
    (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (fun r => (r.selected, r.left, r.right))
    (by intro r; cases r; rfl)
    (by rintro ⟨b, a, c⟩; rfl)

def familyCodec (n : Nat) : Codec (Family n) := listCodec (rowCodec n)

theorem row_length {n : Nat} (r : Row n) :
    ((rowCodec n).encode r).length = 2 * n + 3 := by
  change ([r.selected] ++ ((affineCodec n).encode r.left ++
    (affineCodec n).encode r.right)).length = _
  simp only [List.length_append, List.length_cons, List.length_nil, affine_length]
  omega

theorem family_length {n : Nat} (F : Family n) :
    ((familyCodec n).encode F).length ≤ (2 * n + 4) * F.length + 1 :=
  list_length_bound (rowCodec n) F (2 * n + 3)
    (fun r _ => Nat.le_of_eq (row_length r))

def stepCodec (n m : Nat) : Codec (ConstructedStep n m) :=
  mappedCodec
    (pairCodec (pointCodec m) (pairCodec (finCodec (n + 1))
      (pairCodec (pointCodec n) (familyCodec n))))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    (fun s => (s.weights, s.pivot, s.tail, s.output))
    (by intro s; cases s; rfl)
    (by rintro ⟨w, p, t, o⟩; rfl)

def stepBound (n m : Nat) : Nat :=
  m + (n + 1) + n + ((2 * n + 4) * m + 1)

theorem step_length {n m : Nat} (s : ConstructedStep n m)
    (rows : s.output.length = m) :
    ((stepCodec n m).encode s).length ≤ stepBound n m := by
  have hp : ((finCodec (n + 1)).encode s.pivot).length ≤ n + 1 := by
    change (natural s.pivot.val).length ≤ n + 1
    rw [natural_length]
    exact Nat.succ_le_of_lt s.pivot.isLt
  have hf := family_length s.output
  rw [rows] at hf
  change ((pointCodec m).encode s.weights ++
    ((finCodec (n + 1)).encode s.pivot ++
      ((pointCodec n).encode s.tail ++ (familyCodec n).encode s.output))).length ≤ _
  simp only [List.length_append, point_length]
  unfold stepBound
  omega

def recordCodec : Codec StepRecord :=
  mappedCodec
    (dependentCodec natCodec fun n => dependentCodec (familyCodec (n + 1))
      fun F => stepCodec n F.length)
    (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (fun q => ⟨q.dimension, ⟨q.source, q.step⟩⟩)
    (by intro q; cases q; rfl)
    (by rintro ⟨n, F, s⟩; rfl)

def recordBound (n m : Nat) : Nat :=
  (n + 1) + ((2 * (n + 1) + 4) * m + 1) + stepBound n m

theorem record_length (q : StepRecord) (rows : q.step.output.length = q.source.length) :
    (recordCodec.encode q).length ≤ recordBound q.dimension q.source.length := by
  have hf := family_length q.source
  have hs := step_length q.step rows
  change (natural q.dimension ++ ((familyCodec (q.dimension + 1)).encode q.source ++
    (stepCodec q.dimension q.source.length).encode q.step)).length ≤ _
  simp only [List.length_append, natural_length]
  unfold recordBound
  omega

theorem stepBound_mono {n N : Nat} (m : Nat) (h : n ≤ N) :
    stepBound n m ≤ stepBound N m := by
  have hm := Nat.mul_le_mul_right m (show 2 * n + 4 ≤ 2 * N + 4 by omega)
  unfold stepBound
  omega

theorem recordBound_mono {n N : Nat} (m : Nat) (h : n ≤ N) :
    recordBound n m ≤ recordBound N m := by
  have hs := stepBound_mono m h
  have hm := Nat.mul_le_mul_right m
    (show 2 * (n + 1) + 4 ≤ 2 * (N + 1) + 4 by omega)
  unfold recordBound
  omega

/-- Row counts and dimensions are derived from the selected linked chain,
not assumed for a list of separately valid or caller-supplied steps. -/
theorem linked_record_bounds {n d : Nat} {F : Family n} {history : List StepRecord}
    {G : Family d} (linked : Linked F history G) :
    ∀ q ∈ history, q.dimension ≤ n ∧ q.source.length = F.length ∧
      q.step.output.length = F.length := by
  induction linked with
  | refl F => intro q member; cases member
  | @step n d F s rest G selected tail ih =>
    intro q member
    have rows : s.output.length = F.length := (globalStep_sound F s selected).1
    rcases List.mem_cons.mp member with head | later
    · subst q
      exact ⟨Nat.le_succ n, rfl, rows⟩
    · obtain ⟨dimension, sourceRows, outputRows⟩ := ih q later
      exact ⟨Nat.le_trans dimension (Nat.le_succ n), sourceRows.trans rows,
        outputRows.trans rows⟩

theorem history_length (n : Nat) (F : Family n) :
    ((listCodec recordCodec).encode (reduce n F).history).length ≤
      (recordBound n F.length + 1) * n + 1 := by
  have bound := list_length_bound recordCodec (reduce n F).history
    (recordBound n F.length) (by
      intro q member
      obtain ⟨dimension, sourceRows, outputRows⟩ :=
        linked_record_bounds (reduce_trace_linked n F) q member
      have qr : q.step.output.length = q.source.length := outputRows.trans sourceRows.symm
      have hq := record_length q qr
      rw [sourceRows] at hq
      exact Nat.le_trans hq (recordBound_mono F.length dimension))
  exact Nat.le_trans bound (Nat.add_le_add_right
    (Nat.mul_le_mul_left (recordBound n F.length + 1) (reduce_step_bound n F)) 1)

/-- Finite data only: the semantic lift/project functions are not serialized. -/
structure ReductionData where
  dimension : Nat
  core : Family dimension
  history : List StepRecord

def toData {n : Nat} (r : Reduction n) : ReductionData :=
  ⟨r.dimension, r.core, r.history⟩

def dataCodec : Codec ReductionData :=
  mappedCodec
    (dependentCodec natCodec fun d =>
      pairCodec (familyCodec d) (listCodec recordCodec))
    (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (fun r => ⟨r.dimension, (r.core, r.history)⟩)
    (by intro r; cases r; rfl)
    (by rintro ⟨d, F, history⟩; rfl)

theorem data_roundtrip (r : ReductionData) :
    dataCodec.decode (dataCodec.encode r) = some r := decode_encode _ _

theorem data_canonical (bits : BitString) (r : ReductionData) :
    dataCodec.decode bits = some r ↔ dataCodec.encode r = bits :=
  decode_eq_some_iff _ _ _

theorem data_injective : Function.Injective dataCodec.encode := encode_injective _

theorem data_length (r : ReductionData) :
    (dataCodec.encode r).length = r.dimension + 1 +
      ((familyCodec r.dimension).encode r.core).length +
      ((listCodec recordCodec).encode r.history).length := by
  change (natural r.dimension ++ ((familyCodec r.dimension).encode r.core ++
    (listCodec recordCodec).encode r.history)).length = _
  simp only [List.length_append, natural_length]
  omega

/-- An explicit polynomial in the original dimension and original row count.
All saved sources, selected weights, pivots, tails and successor rows count. -/
def dataBound (n m : Nat) : Nat :=
  (n + 1) + ((2 * n + 4) * m + 1) + ((recordBound n m + 1) * n + 1)

theorem reduce_encoded_bound (n : Nat) (F : Family n) :
    (dataCodec.encode (toData (reduce n F))).length ≤ dataBound n F.length := by
  have dimension : (reduce n F).dimension ≤ n := by
    have accounting := reduce_dimension_accounting n F
    omega
  have core := family_length (reduce n F).core
  rw [reduce_row_count] at core
  have coreMono := Nat.mul_le_mul_right F.length
    (show 2 * (reduce n F).dimension + 4 ≤ 2 * n + 4 by omega)
  have history := history_length n F
  rw [data_length]
  change (reduce n F).dimension + 1 +
    ((familyCodec (reduce n F).dimension).encode (reduce n F).core).length +
    ((listCodec recordCodec).encode (reduce n F).history).length ≤ _
  unfold dataBound
  omega

end PNP.Concrete.ResidualReduction.SourceEncoding
