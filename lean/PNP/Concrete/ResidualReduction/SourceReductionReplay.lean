import PNP.Concrete.ResidualReduction.SourceReductionEncoding

/-! Recover the semantic reduction maps from finite encoded history.
Parsing checks syntax, not arbitrary-history validity. The semantic theorem
below applies to the exact source-generated reduction, without a supplied
trace premise. No runtime or terminal-completeness claim is made here. -/

namespace PNP.Concrete.ResidualReduction.SourceEncoding
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

def liftHistory (n d : Nat) : List StepRecord → Point d → Option (Point n)
  | [], z => if h : d = n then some (h ▸ z) else none
  | q :: rest, z =>
    if h : q.dimension + 1 = n then
      (liftHistory q.dimension d rest z).map fun y =>
        h ▸ decode (markSource q.source q.step.weights) q.step.pivot q.step.tail y
    else none

def projectHistory (n d : Nat) : List StepRecord → Point n → Option (Point d)
  | [], x => if h : n = d then some (h ▸ x) else none
  | q :: rest, x =>
    if h : n = q.dimension + 1 then
      projectHistory q.dimension d rest (encode q.step.pivot q.step.tail (h ▸ x))
    else none

def Replays {n : Nat} (r : Reduction n) : Prop :=
  (∀ z, liftHistory n r.dimension r.history z = some (r.lift z)) ∧
  (∀ x, projectHistory n r.dimension r.history x = some (r.project x))

theorem keep_replays {n : Nat} (F : Family n) : Replays (keep F) := by
  constructor
  · intro z; change liftHistory n n [] z = some z
    exact dif_pos rfl
  · intro x; change projectHistory n n [] x = some x
    exact dif_pos rfl

theorem prepend_replays {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (r : Reduction n) (h : Replays r) :
    Replays (prepend F s r) := by
  constructor
  · intro z
    change liftHistory (n + 1) r.dimension (⟨n, F, s⟩ :: r.history) z =
        some (decode (markSource F s.weights) s.pivot s.tail (r.lift z))
    rw [liftHistory, dif_pos rfl, h.1 z]
    rfl
  · intro x
    change projectHistory (n + 1) r.dimension (⟨n, F, s⟩ :: r.history) x =
      some (r.project (encode s.pivot s.tail x))
    rw [projectHistory, dif_pos rfl]
    exact h.2 _

theorem reduce_replays (n : Nat) (F : Family n) : Replays (reduce n F) := by
  induction n with
  | zero => exact keep_replays F
  | succ n ih =>
    cases selected : globalStep F with
    | none => simpa only [reduce, selected] using keep_replays F
    | some s =>
      simpa only [reduce, selected] using
        prepend_replays F s (reduce n s.output) (ih s.output)

/-- Replay a generated result on a syntactically decoded terminal witness.
A successful parse alone does not certify an arbitrary trace or witness. -/
def recoverBytes (sourceDimension : Nat) (result witness : BitString) : Option BitString :=
  (dataCodec.decode result).bind fun r =>
    ((pointCodec r.dimension).decode witness).bind fun z =>
      (liftHistory sourceDimension r.dimension r.history z).map NativeSource.pointBytes

def projectBytes (sourceDimension : Nat) (result witness : BitString) : Option BitString :=
  (dataCodec.decode result).bind fun r =>
    ((pointCodec sourceDimension).decode witness).bind fun x =>
      (projectHistory sourceDimension r.dimension r.history x).map (pointCodec r.dimension).encode

theorem recover_reduce (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    recoverBytes n (dataCodec.encode (toData (reduce n F)))
      ((pointCodec (reduce n F).dimension).encode z) =
        some (NativeSource.pointBytes ((reduce n F).lift z)) := by
  simp only [recoverBytes, Option.bind_some, toData,
    NativeNormalization.NativeBitCodec.decode_encode]
  rw [(reduce_replays n F).1 z]
  rfl

theorem project_reduce (n : Nat) (F : Family n) (x : Point n) :
    projectBytes n (dataCodec.encode (toData (reduce n F))) ((pointCodec n).encode x) =
      some ((pointCodec (reduce n F).dimension).encode ((reduce n F).project x)) := by
  simp only [projectBytes, Option.bind_some, toData,
    NativeNormalization.NativeBitCodec.decode_encode]
  rw [(reduce_replays n F).2 x]
  rfl

theorem recover_reduced_model (n : Nat) (F : Family n) (z : Point (reduce n F).dimension)
    (model : models (reduce n F).core z = true) :
    ∃ x : Point n,
      recoverBytes n (dataCodec.encode (toData (reduce n F)))
        ((pointCodec (reduce n F).dimension).encode z) = some (NativeSource.pointBytes x) ∧
      models F x = true := by
  exact ⟨(reduce n F).lift z, recover_reduce n F z,
    (reduce_model_map n F z).symm.trans model⟩

theorem recover_project_model (n : Nat) (F : Family n) (x : Point n)
    (model : models F x = true) :
    (projectBytes n (dataCodec.encode (toData (reduce n F))) ((pointCodec n).encode x)).bind
      (recoverBytes n (dataCodec.encode (toData (reduce n F)))) =
        some (NativeSource.pointBytes x) := by
  rw [project_reduce]
  simp only [Option.bind_some]
  rw [recover_reduce, reduce_source_roundtrip n F x model]

end PNP.Concrete.ResidualReduction.SourceEncoding
