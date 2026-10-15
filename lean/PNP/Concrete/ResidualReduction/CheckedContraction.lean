import PNP.Concrete.ResidualReduction.FactoredContraction

namespace PNP.Concrete.ResidualReduction.FactoredContraction

/-- Candidate coefficient data, checked against the computed source scalar. -/
inductive TailForm (n : Nat) where
  | affine (u : Affine n)
  | plane (a b u : Affine n)

def TailForm.polynomial {n : Nat} : TailForm n → Quadratic n
  | .affine u => qOfAffine u
  | .plane a b u => qAdd (qProduct a b) (qOfAffine u)

def TailForm.value {n : Nat} : TailForm n → Point n → Bool
  | .affine u, z => aEval u z
  | .plane a b u, z => planeValue a b u z

def TailForm.reduce {n : Nat} : TailForm n → Family (n + 1) → Option (Family n)
  | .affine u, rs => some (rs.map (affineRow u))
  | .plane a b u, rs => planeRows a b u rs

theorem TailForm.polynomial_eval {n : Nat} (f : TailForm n) (z : Point n) :
    qEval f.polynomial z = f.value z := by
  cases f with
  | affine u => exact qOfAffine_eval u z
  | plane a b u =>
    simp only [TailForm.polynomial, TailForm.value, qAdd_eval, qProduct_eval,
      qOfAffine_eval, planeValue]

theorem TailForm.reduce_sound {n : Nat} (f : TailForm n)
    (rs : Family (n + 1)) (out : Family n) (h : f.reduce rs = some out) :
    out.length = rs.length ∧
      ∀ z, models out z = models rs (f.value z, z) := by
  cases f with
  | affine u =>
    have he : rs.map (affineRow u) = out := by simpa [TailForm.reduce] using h
    cases he
    refine ⟨List.length_map (affineRow u), ?_⟩
    intro z
    exact models_map rs (affineRow u) (fun z => (aEval u z, z))
      (affineRow_eval u) z
  | plane a b u =>
    exact planeRows_sound a b u rs out h

/-- Checks the actual source coefficients and transforms every row. Failure is
    unknown, never an assertion that the source is unsatisfiable. -/
def contract {n : Nat} (rs : Family (n + 1)) (k : Fin (n + 1))
    (v : Point n) (f : TailForm n) : Option (Family n) :=
  let s := chartRows rs k v
  let q := scalar s
  if aEq q.1 (aConst n true) = true then
    if qEq q.2 f.polynomial = true then f.reduce s else none
  else none

theorem contract_checks {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out) :
    (scalar (chartRows rs k v)).1 = aConst n true ∧
    (scalar (chartRows rs k v)).2 = f.polynomial ∧
    f.reduce (chartRows rs k v) = some out := by
  unfold contract at h
  dsimp only at h
  split at h
  next hb =>
    split at h
    next hf =>
      exact ⟨(aEq_true_iff _ _).mp hb, (qEq_true_iff _ _).mp hf, h⟩
    next hf => simp at h
  next hb => simp at h

/-- The forward map does not require a supplied correctness certificate. -/
def encode {n : Nat} (k : Fin (n + 1)) (v : Point n)
    (x : Point (n + 1)) : Point n :=
  (chart k v x).2

/-- The eliminated bit is derived from the marked original source rows. -/
def decode {n : Nat} (rs : Family (n + 1)) (k : Fin (n + 1))
    (v : Point n) (z : Point n) : Point (n + 1) :=
  unchart k v (qEval (scalar (chartRows rs k v)).2 z, z)

theorem encode_decode {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (z : Point n) :
    encode k v (decode rs k v z) = z := by
  simp only [encode, decode, chart_unchart]

theorem contract_length {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out) :
    out.length = rs.length := by
  have hr := (contract_checks rs k v f out h).2.2
  have hl := (f.reduce_sound (chartRows rs k v) out hr).1
  simpa only [chartRows, List.length_map] using hl

theorem contract_models {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out) (z : Point n) :
    models out z = models rs (decode rs k v z) := by
  obtain ⟨_, hq, hr⟩ := contract_checks rs k v f out h
  have hm := (f.reduce_sound (chartRows rs k v) out hr).2 z
  simp only [decode, hq, TailForm.polynomial_eval]
  exact hm.trans (chartRows_models rs k v (f.value z, z))

private theorem qEval_succ {n : Nat} (q : Quadratic (n + 1))
    (x : Point (n + 1)) :
    qEval q x = Bool.xor (aEval q.1 x.2 && x.1) (qEval q.2 x.2) := by
  rcases q with ⟨d, q⟩
  rcases x with ⟨b, x⟩
  rfl

private theorem balancedBit :
    ∀ b h : Bool, Bool.xor (true && b) h = false → b = h := by
  decide

theorem decode_encode_of_balance {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n)
    (hb : (scalar (chartRows rs k v)).1 = aConst n true)
    (x : Point (n + 1)) (hx : models rs x = true) :
    decode rs k v (encode k v x) = x := by
  have hm : models (chartRows rs k v) (chart k v x) = true := by
    rw [chartRows_models, unchart_chart]
    exact hx
  have hs := scalar_zero_of_models (chartRows rs k v) (chart k v x) hm
  rw [qEval_succ, hb, aConst_eval] at hs
  have he := balancedBit (chart k v x).1
    (qEval (scalar (chartRows rs k v)).2 (chart k v x).2) hs
  change unchart k v
    (qEval (scalar (chartRows rs k v)).2 (chart k v x).2, (chart k v x).2) = x
  rw [← he]
  exact unchart_chart k v x

theorem decode_encode {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out)
    (x : Point (n + 1)) (hx : models rs x = true) :
    decode rs k v (encode k v x) = x :=
  decode_encode_of_balance rs k v (contract_checks rs k v f out h).1 x hx

theorem contract_satisfiable_iff {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out) :
    (∃ x, models rs x = true) ↔ (∃ z, models out z = true) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨encode k v x, ?_⟩
    rw [contract_models rs k v f out h, decode_encode rs k v f out h x hx]
    exact hx
  · rintro ⟨z, hz⟩
    exact ⟨decode rs k v z, (contract_models rs k v f out h z).symm.trans hz⟩

/-- All obligations of the accepted full-model bijection, including source row
    retention. This does not claim that every source admits a contraction. -/
theorem contract_full_model_bijection {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (f : TailForm n) (out : Family n)
    (h : contract rs k v f = some out) :
    out.length = rs.length ∧
    (∀ z, models out z = models rs (decode rs k v z)) ∧
    (∀ z, encode k v (decode rs k v z) = z) ∧
    (∀ x, models rs x = true → decode rs k v (encode k v x) = x) ∧
    ((∃ x, models rs x = true) ↔ (∃ z, models out z = true)) :=
  ⟨contract_length rs k v f out h, contract_models rs k v f out h,
    encode_decode rs k v, decode_encode rs k v f out h,
    contract_satisfiable_iff rs k v f out h⟩

end PNP.Concrete.ResidualReduction.FactoredContraction
