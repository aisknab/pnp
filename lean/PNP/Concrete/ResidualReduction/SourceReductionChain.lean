import PNP.Concrete.ResidualReduction.SourceGlobalSelector

namespace PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.SourceBalance PNP.Concrete.ResidualReduction.SourceClosure

structure StepRecord where
  dimension : Nat
  source : Family (dimension+1)
  step : ConstructedStep dimension source.length

/-- Every saved step is linked to the preceding residual and to the exact
    terminal family; local step validity alone would not establish this. -/
inductive Linked : {n d : Nat} → Family n → List StepRecord → Family d → Prop where
  | refl {n : Nat} (F : Family n) : Linked F [] F
  | step {n d : Nat} (F : Family (n+1)) (s : ConstructedStep n F.length)
      (rest : List StepRecord) (G : Family d)
      (selected : globalStep F = some s) (tail : Linked s.output rest G) :
      Linked F (⟨n,F,s⟩::rest) G

structure Reduction (n : Nat) where
  dimension : Nat
  core : Family dimension
  lift : Point dimension → Point n
  project : Point n → Point dimension
  history : List StepRecord

def stopped : {n : Nat} → Family n → Prop
  | 0, _ => True
  | _+1, F => globalStep F = none

def keep {n : Nat} (F : Family n) : Reduction n :=
  ⟨n,F,id,id,[]⟩

def prepend {n : Nat} (F : Family (n+1)) (s : ConstructedStep n F.length)
    (r : Reduction n) : Reduction (n+1) :=
  ⟨r.dimension,r.core,
   (fun z => decode (markSource F s.weights) s.pivot s.tail (r.lift z)),
   (fun x => r.project (encode s.pivot s.tail x)),
   ⟨n,F,s⟩::r.history⟩

/-- Recursion is on the actual source dimension, not a caller-supplied fuel
    or promised progress certificate. A failed selector retains the input. -/
def reduce : (n : Nat) → Family n → Reduction n
  | 0, F => keep F
  | n+1, F =>
    match globalStep F with
    | none => keep F
    | some s => prepend F s (reduce n s.output)

def ReductionSound {n : Nat} (F : Family n) (r : Reduction n) : Prop :=
  r.core.length = F.length ∧
  (∀ z, models r.core z = models F (r.lift z)) ∧
  (∀ z, r.project (r.lift z) = z) ∧
  (∀ x, models F x = true → r.lift (r.project x) = x) ∧
  r.history.length + r.dimension = n ∧
  stopped r.core ∧
  (∀ q ∈ r.history, globalStep q.source = some q.step) ∧
  Linked F r.history r.core

theorem keep_sound {n : Nat} (F : Family n) (h : stopped F) :
    ReductionSound F (keep F) := by
  refine ⟨rfl,(fun _ => rfl),(fun _ => rfl),(fun _ _ => rfl),?_,h,?_,Linked.refl F⟩
  · exact Nat.zero_add n
  · intro q hq; cases hq

theorem prepend_sound {n : Nat} (F : Family (n+1)) (s : ConstructedStep n F.length)
    (h : globalStep F = some s) (r : Reduction n) (hr : ReductionSound s.output r) :
    ReductionSound F (prepend F s r) := by
  obtain ⟨hslen,hsmodels,hsproject,hslift,_⟩ := globalStep_sound F s h
  obtain ⟨hrlen,hrmodels,hrproject,hrlift,hrcount,hrstop,hrtrace,hrlink⟩ := hr
  refine ⟨hrlen.trans hslen,?_,?_,?_,?_,hrstop,?_,Linked.step F s r.history r.core h hrlink⟩
  · intro z
    exact (hrmodels z).trans (hsmodels (r.lift z))
  · intro z
    change r.project (encode s.pivot s.tail
      (decode (markSource F s.weights) s.pivot s.tail (r.lift z))) = z
    rw [hsproject,hrproject]
  · intro x hx
    have hz : models s.output (encode s.pivot s.tail x) = true := by
      rw [hsmodels,hslift x hx]
      exact hx
    change decode (markSource F s.weights) s.pivot s.tail
      (r.lift (r.project (encode s.pivot s.tail x))) = x
    rw [hrlift _ hz,hslift x hx]
  · change (r.history.length + 1) + r.dimension = n+1
    omega
  · intro q hq
    change q ∈ (⟨n,F,s⟩ : StepRecord)::r.history at hq
    rcases List.mem_cons.mp hq with he | ht
    · subst q; exact h
    · exact hrtrace q ht

theorem reduce_sound (n : Nat) (F : Family n) : ReductionSound F (reduce n F) := by
  induction n with
  | zero => exact keep_sound F True.intro
  | succ n ih =>
    cases h : globalStep F with
    | none => simpa only [reduce,h] using keep_sound F h
    | some s =>
      simpa only [reduce,h] using prepend_sound F s h (reduce n s.output) (ih s.output)

theorem reduce_row_count (n : Nat) (F : Family n) :
    (reduce n F).core.length = F.length :=
  (reduce_sound n F).1

theorem reduce_model_map (n : Nat) (F : Family n) :
    ∀ z, models (reduce n F).core z = models F ((reduce n F).lift z) :=
  (reduce_sound n F).2.1

theorem reduce_parameter_roundtrip (n : Nat) (F : Family n) :
    ∀ z, (reduce n F).project ((reduce n F).lift z) = z :=
  (reduce_sound n F).2.2.1

theorem reduce_source_roundtrip (n : Nat) (F : Family n) :
    ∀ x, models F x = true → (reduce n F).lift ((reduce n F).project x) = x :=
  (reduce_sound n F).2.2.2.1

theorem reduce_dimension_accounting (n : Nat) (F : Family n) :
    (reduce n F).history.length + (reduce n F).dimension = n :=
  (reduce_sound n F).2.2.2.2.1

theorem reduce_step_bound (n : Nat) (F : Family n) :
    (reduce n F).history.length ≤ n := by
  have h := reduce_dimension_accounting n F
  omega

theorem reduce_terminal (n : Nat) (F : Family n) : stopped (reduce n F).core :=
  (reduce_sound n F).2.2.2.2.2.1

theorem reduce_history_checked (n : Nat) (F : Family n) :
    ∀ q ∈ (reduce n F).history, globalStep q.source = some q.step :=
  (reduce_sound n F).2.2.2.2.2.2.1

theorem reduce_trace_linked (n : Nat) (F : Family n) :
    Linked F (reduce n F).history (reduce n F).core :=
  (reduce_sound n F).2.2.2.2.2.2.2

theorem reduce_satisfiable_iff (n : Nat) (F : Family n) :
    (∃ x, models F x = true) ↔ ∃ z, models (reduce n F).core z = true := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨(reduce n F).project x,?_⟩
    rw [reduce_model_map,reduce_source_roundtrip n F x hx]
    exact hx
  · rintro ⟨z,hz⟩
    exact ⟨(reduce n F).lift z,(reduce_model_map n F z).symm.trans hz⟩

/-- Only a zero-dimensional residual receives a verdict. A nonzero-dimensional
    stopped residual is deliberately reported as unknown. -/
def zeroVerdict : (n : Nat) → Family n → Option Bool
  | 0, F => some (models F ())
  | _+1, _ => none

def verdict {n : Nat} (F : Family n) : Option Bool :=
  let r := reduce n F
  zeroVerdict r.dimension r.core

theorem zeroVerdict_true_sound (n : Nat) (F : Family n)
    (h : zeroVerdict n F = some true) : ∃ x, models F x = true := by
  cases n with
  | zero =>
    refine ⟨(),?_⟩
    simpa only [zeroVerdict,Option.some.injEq] using h
  | succ n => simp only [zeroVerdict,reduceCtorEq] at h

theorem zeroVerdict_false_sound (n : Nat) (F : Family n)
    (h : zeroVerdict n F = some false) : ¬ ∃ x, models F x = true := by
  cases n with
  | zero =>
    have hf : models F () = false := by
      simpa only [zeroVerdict,Option.some.injEq] using h
    rintro ⟨x,hx⟩
    cases x
    rw [hf] at hx
    cases hx
  | succ n => simp only [zeroVerdict,reduceCtorEq] at h

theorem verdict_true_sound {n : Nat} (F : Family n) (h : verdict F = some true) :
    ∃ x, models F x = true :=
  (reduce_satisfiable_iff n F).mpr
    (zeroVerdict_true_sound (reduce n F).dimension (reduce n F).core h)

theorem verdict_false_sound {n : Nat} (F : Family n) (h : verdict F = some false) :
    ¬ ∃ x, models F x = true :=
  fun hx => zeroVerdict_false_sound (reduce n F).dimension (reduce n F).core h
    ((reduce_satisfiable_iff n F).mp hx)

end PNP.Concrete.ResidualReduction.SourceChain
