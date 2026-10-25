import PNP.Concrete.ResidualReduction.BooleanCoefficients

/-! Shared Boolean coefficient circuits for refutation reconstruction.
Gate numbers are absolute creation indices. The code is stored newest first,
but evaluation computes the older table once and appends one value. This module
does not search for a refutation or claim completeness of affine elimination. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationCircuit
open PNP.Concrete.ResidualReduction.FactoredContraction

def bitAt : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => bitAt bs i

theorem bitAt_append_old (bs cs : List Bool) (i : Nat) (h : i < bs.length) :
    bitAt (bs ++ cs) i = bitAt bs i := by
  induction bs generalizing i with
  | nil => simp only [List.length_nil] at h; omega
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using h)

theorem bitAt_append_new (bs : List Bool) (b : Bool) :
    bitAt (bs ++ [b]) bs.length = b := by
  induction bs with
  | nil => rfl
  | cons c bs ih => exact ih

inductive Gate (n : Nat) where
  | input : Affine n → Gate n
  | xorGate : Nat → Nat → Gate n
  | andGate : Nat → Nat → Gate n

abbrev Code (n : Nat) := List (Gate n)

def gateEval {n : Nat} (g : Gate n) (x : Point n) (values : List Bool) : Bool :=
  match g with
  | .input a => aEval a x
  | .xorGate i j => Bool.xor (bitAt values i) (bitAt values j)
  | .andGate i j => bitAt values i && bitAt values j

def evaluate {n : Nat} : Code n → Point n → List Bool
  | [], _ => []
  | g :: code, x =>
    let older := evaluate code x
    older ++ [gateEval g x older]

def value {n : Nat} (code : Code n) (x : Point n) (i : Nat) : Bool :=
  bitAt (evaluate code x) i

/-- Evaluate the graph once, then read every output from that shared table. -/
def outputs {n : Nat} (code : Code n) (x : Point n) (roots : List Nat) : List Bool :=
  let values := evaluate code x
  roots.map (bitAt values)

theorem outputs_eq_map_value {n : Nat} (code : Code n) (x : Point n) (roots : List Nat) :
    outputs code x roots = roots.map (value code x) := rfl

theorem evaluate_length {n : Nat} (code : Code n) (x : Point n) :
    (evaluate code x).length = code.length := by
  induction code with
  | nil => rfl
  | cons g code ih =>
    simp only [evaluate, List.length_append, List.length_cons, List.length_nil, ih]

theorem value_cons_old {n : Nat} (code : Code n) (g : Gate n)
    (x : Point n) (i : Nat) (h : i < code.length) :
    value (g :: code) x i = value code x i := by
  apply bitAt_append_old
  simpa only [evaluate_length] using h

theorem value_cons_new {n : Nat} (code : Code n) (g : Gate n) (x : Point n) :
    value (g :: code) x code.length = gateEval g x (evaluate code x) := by
  change bitAt (evaluate code x ++ [gateEval g x (evaluate code x)]) code.length = _
  rw [← evaluate_length code x]
  exact bitAt_append_new _ _

def Extends {n : Nat} (older newer : Code n) : Prop :=
  ∃ front, newer = front ++ older

theorem extends_refl {n : Nat} (code : Code n) : Extends code code :=
  ⟨[], rfl⟩

theorem extends_cons {n : Nat} (code : Code n) (g : Gate n) :
    Extends code (g :: code) := ⟨[g], rfl⟩

theorem extends_trans {n : Nat} {a b c : Code n}
    (hab : Extends a b) (hbc : Extends b c) : Extends a c := by
  obtain ⟨p, rfl⟩ := hab
  obtain ⟨q, rfl⟩ := hbc
  exact ⟨q ++ p, (List.append_assoc q p a).symm⟩

theorem extends_length {n : Nat} {a b : Code n} (h : Extends a b) :
    a.length ≤ b.length := by
  obtain ⟨p, rfl⟩ := h
  simp only [List.length_append]
  omega

theorem extends_value {n : Nat} {a b : Code n} (h : Extends a b)
    (x : Point n) (i : Nat) (hi : i < a.length) :
    value b x i = value a x i := by
  obtain ⟨p, rfl⟩ := h
  induction p with
  | nil => rfl
  | cons g p ih =>
    rw [List.cons_append, value_cons_old]
    · exact ih
    · simp only [List.length_append]
      omega

structure InputRow (n : Nat) where
  root : Nat
  coefficient : Bool
  cofactor : Affine n

def RootsBounded {n : Nat} (rows : List (InputRow n)) (code : Code n) : Prop :=
  ∀ r ∈ rows, r.root < code.length

theorem roots_mono {n : Nat} {rows : List (InputRow n)} {a b : Code n}
    (h : RootsBounded rows a) (he : Extends a b) : RootsBounded rows b := by
  intro r hr
  exact Nat.lt_of_lt_of_le (h r hr) (extends_length he)

def productSum {n : Nat} (rows : List (InputRow n)) (code : Code n) (x : Point n) : Bool :=
  match rows with
  | [] => false
  | r :: rs => Bool.xor (value code x r.root && aEval r.cofactor x)
      (productSum rs code x)

theorem productSum_extends {n : Nat} (rows : List (InputRow n)) {a b : Code n}
    (h : RootsBounded rows a) (he : Extends a b) (x : Point n) :
    productSum rows b x = productSum rows a x := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [productSum]
    rw [extends_value he x r.root (h r List.mem_cons_self)]
    exact congrArg (Bool.xor (value a x r.root && aEval r.cofactor x))
      (ih (fun r hr => h r (List.mem_cons_of_mem _ hr)))

def addProduct {n : Nat} (code : Code n) (acc : Nat) (r : InputRow n) : Code n :=
  .xorGate acc (code.length + 1) ::
  .andGate r.root code.length ::
  .input r.cofactor :: code

theorem addProduct_extends {n : Nat} (code : Code n) (acc : Nat) (r : InputRow n) :
    Extends code (addProduct code acc r) :=
  ⟨[.xorGate acc (code.length + 1), .andGate r.root code.length, .input r.cofactor], rfl⟩

theorem addProduct_length {n : Nat} (code : Code n) (acc : Nat) (r : InputRow n) :
    (addProduct code acc r).length = code.length + 3 := rfl

theorem addProduct_value {n : Nat} (code : Code n) (acc : Nat) (r : InputRow n)
    (ha : acc < code.length) (hr : r.root < code.length) (x : Point n) :
    value (addProduct code acc r) x (code.length + 2) =
      Bool.xor (value code x acc) (value code x r.root && aEval r.cofactor x) := by
  have hacc1 := value_cons_old code (.input r.cofactor) x acc ha
  have hacc2 := value_cons_old (.input r.cofactor :: code)
    (.andGate r.root code.length) x acc (by simp only [List.length_cons]; omega)
  have hroot := value_cons_old code (.input r.cofactor) x r.root hr
  have hleaf := value_cons_new code (.input r.cofactor) x
  have hprod := value_cons_new (.input r.cofactor :: code)
    (.andGate r.root code.length) x
  have hsum := value_cons_new
    (.andGate r.root code.length :: .input r.cofactor :: code)
    (.xorGate acc (code.length + 1)) x
  change value (addProduct code acc r) x (code.length + 2) =
    Bool.xor (value (.andGate r.root code.length :: .input r.cofactor :: code) x acc)
      (value (.andGate r.root code.length :: .input r.cofactor :: code) x (code.length + 1)) at hsum
  change value (.andGate r.root code.length :: .input r.cofactor :: code) x (code.length + 1) =
    (value (.input r.cofactor :: code) x r.root &&
      value (.input r.cofactor :: code) x code.length) at hprod
  change value (.input r.cofactor :: code) x code.length = aEval r.cofactor x at hleaf
  rw [hsum, hacc2, hacc1, hprod, hroot, hleaf]

def foldProducts {n : Nat} : List (InputRow n) → Nat → Code n → Code n × Nat
  | [], acc, code => (code, acc)
  | r :: rs, acc, code =>
    foldProducts rs (code.length + 2) (addProduct code acc r)

theorem foldProducts_extends {n : Nat} (rows : List (InputRow n)) (acc : Nat) (code : Code n) :
    Extends code (foldProducts rows acc code).1 := by
  induction rows generalizing acc code with
  | nil => exact extends_refl code
  | cons r rs ih =>
    exact extends_trans (addProduct_extends code acc r)
      (ih (code.length + 2) (addProduct code acc r))

theorem foldProducts_length {n : Nat} (rows : List (InputRow n)) (acc : Nat) (code : Code n) :
    (foldProducts rows acc code).1.length = code.length + 3 * rows.length := by
  induction rows generalizing acc code with
  | nil => simp only [foldProducts, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons r rs ih =>
    simp only [foldProducts, ih, addProduct_length, List.length_cons]
    omega

theorem foldProducts_root_bound {n : Nat} (rows : List (InputRow n)) (acc : Nat)
    (code : Code n) (ha : acc < code.length) :
    (foldProducts rows acc code).2 < (foldProducts rows acc code).1.length := by
  induction rows generalizing acc code with
  | nil => exact ha
  | cons r rs ih =>
    apply ih
    rw [addProduct_length]
    omega

theorem foldProducts_value {n : Nat} (rows : List (InputRow n)) (acc : Nat)
    (code : Code n) (ha : acc < code.length) (hr : RootsBounded rows code) (x : Point n) :
    value (foldProducts rows acc code).1 x (foldProducts rows acc code).2 =
      Bool.xor (value code x acc) (productSum rows code x) := by
  induction rows generalizing acc code with
  | nil => exact (Bool.xor_false _).symm
  | cons r rs ih =>
    have ht : RootsBounded rs code :=
      fun t ht => hr t (List.mem_cons_of_mem _ ht)
    have he := addProduct_extends code acc r
    have hb : code.length + 2 < (addProduct code acc r).length := by
      rw [addProduct_length]; omega
    rw [foldProducts, ih _ _ hb (roots_mono ht he)]
    rw [addProduct_value code acc r ha (hr r List.mem_cons_self),
      productSum_extends rs ht he x]
    exact Bool.xor_assoc _ _ _

def buildCorrection {n : Nat} (rows : List (InputRow n)) (code : Code n) : Code n × Nat :=
  foldProducts rows code.length (.input (aConst n false) :: code)

theorem buildCorrection_extends {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    Extends code (buildCorrection rows code).1 :=
  extends_trans (extends_cons code (.input (aConst n false))) (foldProducts_extends _ _ _)

theorem buildCorrection_length {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    (buildCorrection rows code).1.length = code.length + 1 + 3 * rows.length := by
  exact foldProducts_length _ _ _

theorem buildCorrection_root_bound {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    (buildCorrection rows code).2 < (buildCorrection rows code).1.length := by
  apply foldProducts_root_bound
  simp only [List.length_cons]
  omega

theorem buildCorrection_value {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (hr : RootsBounded rows code) (x : Point n) :
    value (buildCorrection rows code).1 x (buildCorrection rows code).2 =
      productSum rows code x := by
  have he := extends_cons code (.input (aConst n false))
  have hb : code.length < (.input (aConst n false) :: code).length := by
    simp only [List.length_cons]; omega
  unfold buildCorrection
  rw [foldProducts_value rows code.length _ hb (roots_mono hr he) x,
    value_cons_new, gateEval, aConst_eval, Bool.false_xor,
    productSum_extends rows hr he x]

def activeCount {n : Nat} : List (InputRow n) → Nat
  | [] => 0
  | r :: rs => (if r.coefficient then 1 else 0) + activeCount rs

theorem activeCount_le {n : Nat} (rows : List (InputRow n)) : activeCount rows ≤ rows.length := by
  induction rows with
  | nil => exact Nat.le_refl 0
  | cons r rs ih =>
    cases h : r.coefficient <;> simp only [activeCount, h, Bool.false_eq_true,
      ↓reduceIte, List.length_cons] <;> omega

def updateRoots {n : Nat} : List (InputRow n) → Nat → Code n → Code n × List Nat
  | [], _, code => (code, [])
  | r :: rs, correction, code =>
    if r.coefficient then
      let rest := updateRoots rs correction (.xorGate r.root correction :: code)
      (rest.1, code.length :: rest.2)
    else
      let rest := updateRoots rs correction code
      (rest.1, r.root :: rest.2)

theorem updateRoots_extends {n : Nat} (rows : List (InputRow n)) (h : Nat) (code : Code n) :
    Extends code (updateRoots rows h code).1 := by
  induction rows generalizing code with
  | nil => exact extends_refl code
  | cons r rs ih =>
    cases hc : r.coefficient with
    | false => simpa only [updateRoots, hc, Bool.false_eq_true, ↓reduceIte] using ih code
    | true =>
      simpa only [updateRoots, hc, ↓reduceIte] using
        extends_trans (extends_cons code (.xorGate r.root h)) (ih (.xorGate r.root h :: code))

theorem updateRoots_length {n : Nat} (rows : List (InputRow n)) (h : Nat) (code : Code n) :
    (updateRoots rows h code).1.length = code.length + activeCount rows := by
  induction rows generalizing code with
  | nil => rfl
  | cons r rs ih =>
    cases hc : r.coefficient <;>
      simp only [updateRoots, activeCount, hc, Bool.false_eq_true, ↓reduceIte, ih, List.length_cons] <;>
      omega

theorem updateRoots_count {n : Nat} (rows : List (InputRow n)) (h : Nat) (code : Code n) :
    (updateRoots rows h code).2.length = rows.length := by
  induction rows generalizing code with
  | nil => rfl
  | cons r rs ih =>
    cases hc : r.coefficient <;>
      simp only [updateRoots, hc, Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]

def expectedRoots {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (h : Nat) (x : Point n) : List Bool :=
  rows.map fun r => Bool.xor (value code x r.root) (r.coefficient && value code x h)

theorem expectedRoots_extends {n : Nat} (rows : List (InputRow n)) {a b : Code n}
    (hr : RootsBounded rows a) (he : Extends a b) (h : Nat) (hh : h < a.length) (x : Point n) :
    expectedRoots rows b h x = expectedRoots rows a h x := by
  unfold expectedRoots
  apply List.map_congr_left
  intro r hin
  rw [extends_value he x r.root (hr r hin), extends_value he x h hh]

theorem updateRoots_value {n : Nat} (rows : List (InputRow n)) (h : Nat)
    (code : Code n) (hh : h < code.length) (hr : RootsBounded rows code) (x : Point n) :
    (updateRoots rows h code).2.map (value (updateRoots rows h code).1 x) =
      expectedRoots rows code h x := by
  induction rows generalizing code with
  | nil => rfl
  | cons r rs ih =>
    have ht : RootsBounded rs code := fun t ht => hr t (List.mem_cons_of_mem _ ht)
    cases hc : r.coefficient with
    | false =>
      simp only [updateRoots, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        expectedRoots, List.map_cons, Bool.false_and, Bool.xor_false]
      rw [extends_value (updateRoots_extends rs h code) x r.root (hr r List.mem_cons_self)]
      exact congrArg (List.cons (value code x r.root)) (ih code hh ht)
    | true =>
      let newer := Gate.xorGate r.root h :: code
      have he : Extends code newer := extends_cons code (.xorGate r.root h)
      have hh' : h < newer.length := Nat.lt_of_lt_of_le hh (extends_length he)
      have hhead : code.length < newer.length := by
        simp only [newer, List.length_cons]; omega
      have first : value (updateRoots rs h newer).1 x code.length =
          Bool.xor (value code x r.root) (value code x h) := by
        rw [extends_value (updateRoots_extends rs h newer) x code.length hhead]
        exact value_cons_new code (.xorGate r.root h) x
      have tail := (ih newer hh' (roots_mono ht he)).trans
        (expectedRoots_extends rs ht he h hh x)
      simp only [updateRoots, hc, ↓reduceIte, List.map_cons, expectedRoots,
        List.map_cons, Bool.true_and]
      rw [first]
      exact congrArg (List.cons _) tail

def compile {n : Nat} (rows : List (InputRow n)) (code : Code n) : Code n × List Nat :=
  let correction := buildCorrection rows code
  updateRoots rows correction.2 correction.1

theorem compile_length {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    (compile rows code).1.length =
      code.length + 1 + 3 * rows.length + activeCount rows := by
  simp only [compile, updateRoots_length, buildCorrection_length]

theorem compile_growth {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    (compile rows code).1.length ≤ code.length + 4 * rows.length + 1 := by
  rw [compile_length]
  have h := activeCount_le rows
  omega

theorem compile_root_count {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    (compile rows code).2.length = rows.length :=
  updateRoots_count _ _ _

theorem compile_value {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (hr : RootsBounded rows code) (x : Point n) :
    (compile rows code).2.map (value (compile rows code).1 x) =
      rows.map (fun r => Bool.xor (value code x r.root)
        (r.coefficient && productSum rows code x)) := by
  have he := buildCorrection_extends rows code
  unfold compile
  rw [updateRoots_value rows _ _ (buildCorrection_root_bound rows code) (roots_mono hr he) x]
  unfold expectedRoots
  apply List.map_congr_left
  intro r hin
  rw [extends_value he x r.root (hr r hin), buildCorrection_value rows code hr x]

def gateValid {n : Nat} (older : Nat) : Gate n → Bool
  | .input _ => true
  | .xorGate i j => decide (i < older) && decide (j < older)
  | .andGate i j => decide (i < older) && decide (j < older)

def codeValid {n : Nat} : Code n → Bool
  | [] => true
  | g :: code => codeValid code && gateValid code.length g

/-- Fail closed for malformed input references. No identity oracle is used. -/
def compileChecked {n : Nat} (rows : List (InputRow n)) (code : Code n) :
    Option (Code n × List Nat) :=
  if codeValid code && rows.all (fun r => decide (r.root < code.length)) then
    some (compile rows code)
  else none

theorem addProduct_valid {n : Nat} (code : Code n) (acc : Nat) (r : InputRow n)
    (hc : codeValid code = true) (ha : acc < code.length) (hr : r.root < code.length) :
    codeValid (addProduct code acc r) = true := by
  have ha' : acc < code.length + 2 := by omega
  have hr' : r.root < code.length + 1 := by omega
  simp [addProduct, codeValid, gateValid, hc, ha', hr']

theorem foldProducts_valid {n : Nat} (rows : List (InputRow n)) (acc : Nat)
    (code : Code n) (hc : codeValid code = true) (ha : acc < code.length)
    (hr : RootsBounded rows code) :
    codeValid (foldProducts rows acc code).1 = true := by
  induction rows generalizing acc code with
  | nil => exact hc
  | cons r rs ih =>
    have ht : RootsBounded rs code := fun t ht => hr t (List.mem_cons_of_mem _ ht)
    apply ih
    · exact addProduct_valid code acc r hc ha (hr r List.mem_cons_self)
    · rw [addProduct_length]; omega
    · exact roots_mono ht (addProduct_extends code acc r)

theorem buildCorrection_valid {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (hc : codeValid code = true) (hr : RootsBounded rows code) :
    codeValid (buildCorrection rows code).1 = true := by
  apply foldProducts_valid
  · simpa only [codeValid, gateValid, Bool.and_true] using hc
  · simp only [List.length_cons]; omega
  · exact roots_mono hr (extends_cons code (.input (aConst n false)))

theorem updateRoots_valid {n : Nat} (rows : List (InputRow n)) (h : Nat)
    (code : Code n) (hc : codeValid code = true) (hh : h < code.length)
    (hr : RootsBounded rows code) :
    codeValid (updateRoots rows h code).1 = true := by
  induction rows generalizing code with
  | nil => exact hc
  | cons r rs ih =>
    have ht : RootsBounded rs code := fun t ht => hr t (List.mem_cons_of_mem _ ht)
    cases hw : r.coefficient with
    | false =>
      simpa only [updateRoots, hw, Bool.false_eq_true, ↓reduceIte] using ih code hc hh ht
    | true =>
      have he := extends_cons code (.xorGate r.root h)
      have valid : codeValid (.xorGate r.root h :: code) = true := by
        simp [codeValid, gateValid, hc, hh, hr r List.mem_cons_self]
      simpa only [updateRoots, hw, ↓reduceIte] using
        ih (.xorGate r.root h :: code) valid
          (Nat.lt_of_lt_of_le hh (extends_length he)) (roots_mono ht he)

theorem updateRoots_roots {n : Nat} (rows : List (InputRow n)) (h : Nat)
    (code : Code n) (hr : RootsBounded rows code) :
    ∀ i ∈ (updateRoots rows h code).2, i < (updateRoots rows h code).1.length := by
  induction rows generalizing code with
  | nil => intro i hi; cases hi
  | cons r rs ih =>
    have ht : RootsBounded rs code := fun t ht => hr t (List.mem_cons_of_mem _ ht)
    cases hw : r.coefficient with
    | false =>
      simp only [updateRoots, hw, Bool.false_eq_true, ↓reduceIte]
      intro i hi
      rcases List.mem_cons.mp hi with heq | hin
      · subst i
        exact Nat.lt_of_lt_of_le (hr r List.mem_cons_self)
          (extends_length (updateRoots_extends rs h code))
      · exact ih code ht i hin
    | true =>
      simp only [updateRoots, hw, ↓reduceIte]
      intro i hi
      rcases List.mem_cons.mp hi with heq | hin
      · subst i
        have hs : code.length < (.xorGate r.root h :: code).length := by
          simp only [List.length_cons]; omega
        exact Nat.lt_of_lt_of_le hs
          (extends_length (updateRoots_extends rs h (.xorGate r.root h :: code)))
      · exact ih (.xorGate r.root h :: code)
          (roots_mono ht (extends_cons code (.xorGate r.root h))) i hin

theorem compile_valid {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (hc : codeValid code = true) (hr : RootsBounded rows code) :
    codeValid (compile rows code).1 = true :=
  updateRoots_valid rows _ _ (buildCorrection_valid rows code hc hr)
    (buildCorrection_root_bound rows code) (roots_mono hr (buildCorrection_extends rows code))

theorem compile_roots {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (hr : RootsBounded rows code) :
    ∀ i ∈ (compile rows code).2, i < (compile rows code).1.length :=
  updateRoots_roots rows _ _ (roots_mono hr (buildCorrection_extends rows code))

private theorem and_true_parts : ∀ a b : Bool,
    (a && b) = true → a = true ∧ b = true := by decide

theorem all_roots_bounded {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (checked : rows.all (fun r => decide (r.root < code.length)) = true) :
    RootsBounded rows code := by
  induction rows with
  | nil => intro r hr; cases hr
  | cons r rs ih =>
    change (decide (r.root < code.length) &&
      rs.all (fun t => decide (t.root < code.length))) = true at checked
    obtain ⟨head, tail⟩ := and_true_parts _ _ checked
    intro t ht
    rcases List.mem_cons.mp ht with he | hin
    · subst t
      exact of_decide_eq_true head
    · exact ih tail t hin

theorem compileChecked_contract {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (result : Code n × List Nat) (checked : compileChecked rows code = some result) :
    result = compile rows code ∧ RootsBounded rows code ∧ codeValid result.1 = true ∧
      (∀ i ∈ result.2, i < result.1.length) ∧ result.2.length = rows.length := by
  cases hc : codeValid code && rows.all (fun r => decide (r.root < code.length)) with
  | false =>
    simp only [compileChecked, hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at checked
  | true =>
    have same : compile rows code = result := by
      simpa only [compileChecked, hc, ↓reduceIte, Option.some.injEq] using checked
    subst result
    obtain ⟨valid, bounds⟩ := and_true_parts _ _ hc
    have hr := all_roots_bounded rows code bounds
    exact ⟨rfl, hr, compile_valid rows code valid hr, compile_roots rows code hr,
      compile_root_count rows code⟩

theorem compileChecked_value {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (result : Code n × List Nat) (checked : compileChecked rows code = some result)
    (x : Point n) :
    result.2.map (value result.1 x) =
      rows.map (fun r => Bool.xor (value code x r.root)
        (r.coefficient && productSum rows code x)) := by
  obtain ⟨same, bounds, _⟩ := compileChecked_contract rows code result checked
  rw [same]
  exact compile_value rows code bounds x

theorem compileChecked_outputs {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (result : Code n × List Nat) (checked : compileChecked rows code = some result)
    (x : Point n) :
    outputs result.1 x result.2 =
      rows.map (fun r => Bool.xor (value code x r.root)
        (r.coefficient && productSum rows code x)) :=
  compileChecked_value rows code result checked x

theorem compileChecked_growth {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (result : Code n × List Nat) (checked : compileChecked rows code = some result) :
    result.1.length ≤ code.length + 4 * rows.length + 1 := by
  rw [(compileChecked_contract rows code result checked).1]
  exact compile_growth rows code

end PNP.Concrete.ResidualReduction.SharedRefutationCircuit
