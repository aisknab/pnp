import PNP.Concrete.NativeNormalization.NativeSourceEquations

namespace PNP.Concrete.NativeNormalization.NativeCoefficients

open NativeBasis NativeSource NativeEquations

local infixl:65 " ⊕ᵦ " => Bool.xor

/-- Finite XOR coefficient lists. Repeated labels cancel by parity;
their length bounds the number of nonzero coefficients without requiring sorting. -/
abbrev Coefficients (c : Nat) := List (Row c)

def eval (u : RowValues c) : Coefficients c → Bool
  | [] => false
  | r :: rs => u r ⊕ᵦ eval u rs

private theorem xor_assoc (a b c : Bool) : (a ⊕ᵦ b) ⊕ᵦ c = a ⊕ᵦ (b ⊕ᵦ c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem xor_interchange (a b c d : Bool) :
    (a ⊕ᵦ b) ⊕ᵦ (c ⊕ᵦ d) = (a ⊕ᵦ c) ⊕ᵦ (b ⊕ᵦ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem eval_append (u : RowValues c) (xs ys : Coefficients c) :
    eval u (xs ++ ys) = eval u xs ⊕ᵦ eval u ys := by
  induction xs with
  | nil => simp [eval]
  | cons r rs ih => simp only [List.cons_append, eval, ih, xor_assoc]

theorem eval_linear (u v : RowValues c) (xs : Coefficients c) :
    eval (fun r => u r ⊕ᵦ v r) xs = eval u xs ⊕ᵦ eval v xs := by
  induction xs with
  | nil => rfl
  | cons r rs ih => simp only [eval, ih]; exact xor_interchange _ _ _ _

theorem eval_zero (xs : Coefficients c) : eval (fun _ => false) xs = false := by
  induction xs with
  | nil => rfl
  | cons r rs ih => simp [eval, ih]

theorem eval_duplicate (u : RowValues c) (r : Row c) (xs : Coefficients c) :
    eval u (r :: r :: xs) = eval u xs := by
  change u r ⊕ᵦ (u r ⊕ᵦ eval u xs) = eval u xs
  cases u r <;> cases eval u xs <;> rfl

def masked (bit : Bool) (xs : Coefficients c) : Coefficients c :=
  if bit then xs else []

theorem eval_masked (u : RowValues c) (bit : Bool) (xs : Coefficients c) :
    eval u (masked bit xs) = (bit && eval u xs) := by
  cases bit <;> simp [masked, eval]

def variableRow (S : Selection n c) (failed : Fin c) (j : Fin n) : Row c :=
  row S failed (.inl j)

def auxiliaryRow (S : Selection n c) (failed : Fin c) (i : Fin c) : Row c :=
  row S failed (.inr (.inl i))

def extraRow (S : Selection n c) (failed : Fin c) : Row c :=
  row S failed (.inr (.inr ()))

def ellTerms (S : Selection n c) (failed : Fin c) (j : Fin n) : Coefficients c :=
  if S.slot j = .middle then
    [variableRow S failed j, auxiliaryRow S failed (S.owner j)]
  else [variableRow S failed j]

def bTerms (S : Selection n c) (failed : Fin c) : Coefficients c :=
  extraRow S failed :: ellTerms S failed (anchor S failed)

def literalTerms (S : Selection n c) (failed : Fin c) (i : Fin c) (s : Slot) :
    Coefficients c :=
  ellTerms S failed (S.literal i s).index ++
    masked (sigma S (S.literal i s).index ⊕ᵦ (S.literal i s).positive) (bTerms S failed)

def auxiliaryTerms (S : Selection n c) (failed : Fin c) (i : Fin c) : Coefficients c :=
  if S.mode i = some .last then
    auxiliaryRow S failed i :: literalTerms S failed i .middle
  else [auxiliaryRow S failed i]

def companionTerms (S : Selection n c) (failed : Fin c) (r : Row c) : Coefficients c :=
  if r.2 then
    match S.mode r.1 with
    | some .last => auxiliaryTerms S failed r.1
    | _ => literalTerms S failed r.1 .last
  else
    match S.mode r.1 with
    | some .middle | some .last => literalTerms S failed r.1 .first
    | _ => literalTerms S failed r.1 .middle ++ auxiliaryTerms S failed r.1

def aTerms (S : Selection n c) (failed : Fin c) (r : Row c) : Coefficients c :=
  r :: companionTerms S failed r

/-- Used only for the unmatched, nonfailed first rows, whose complete
classification is proved from the actual source matching. -/
def imageTerms (S : Selection n c) (failed : Fin c) (i : Fin c) : Coefficients c :=
  (i,false) :: literalTerms S failed i .first

theorem eval_ellTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (j : Fin n) :
    eval u (ellTerms S failed j) = ellFrom S (pick S failed u) j := by
  by_cases h : S.slot j = .middle <;>
    simp [ellTerms, ellFrom, eval, h, pick, fromFn, variableRow, auxiliaryRow]

theorem eval_bTerms (S : Selection n c) (failed : Fin c) (u : RowValues c) :
    eval u (bTerms S failed) = bRow S failed u := by
  change (u (extraRow S failed) ⊕ᵦ eval u (ellTerms S failed (anchor S failed))) = _
  rw [eval_ellTerms]
  rfl

private theorem literal_algebra (l s p e : Bool) :
    (l ⊕ᵦ (s && e)) ⊕ᵦ (p && e) = l ⊕ᵦ ((s ⊕ᵦ p) && e) := by
  cases l <;> cases s <;> cases p <;> cases e <;> rfl

theorem eval_literalTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (i : Fin c) (s : Slot) :
    eval u (literalTerms S failed i s) = falseForm S i s (recovered S failed u) := by
  simp only [literalTerms, eval_append, eval_masked, eval_ellTerms, eval_bTerms]
  exact (literal_algebra _ _ _ _).symm

theorem eval_auxiliaryTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (i : Fin c) :
    eval u (auxiliaryTerms S failed i) = (recovered S failed u).t i := by
  by_cases h : S.mode i = some .last
  · simp only [auxiliaryTerms, h, if_pos, eval, eval_literalTerms]
    simp only [recovered, decode, decodeT, h, if_pos, falseForm]
    rfl
  · simp [auxiliaryTerms, h, eval, recovered, decode, decodeT, pick, fromFn, auxiliaryRow]

theorem eval_companionTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (r : Row c) :
    eval u (companionTerms S failed r) = companion S (recovered S failed u) r := by
  rcases r with ⟨i,b⟩
  cases b <;> cases hm : S.mode i with
  | none => simp [companionTerms, companion, hm, eval_append, eval_literalTerms, eval_auxiliaryTerms]
  | some s => cases s <;>
      simp [companionTerms, companion, hm, eval_append, eval_literalTerms, eval_auxiliaryTerms]

theorem eval_aTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (r : Row c) :
    eval u (aTerms S failed r) = aRow S failed u r := by
  change (u r ⊕ᵦ eval u (companionTerms S failed r)) = _
  rw [eval_companionTerms]
  rfl

theorem eval_imageTerms (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (i : Fin c) (h : S.mode i = none) :
    eval u (imageTerms S failed i) = imageRow S failed u (i,false) := by
  simp [imageTerms, eval, eval_literalTerms, imageRow, selected, h]

theorem ellTerms_length (S : Selection n c) (failed : Fin c) (j : Fin n) :
    (ellTerms S failed j).length ≤ 2 := by
  unfold ellTerms
  split <;> simp

theorem bTerms_length (S : Selection n c) (failed : Fin c) :
    (bTerms S failed).length ≤ 3 := by
  have h := ellTerms_length S failed (anchor S failed)
  simp only [bTerms, List.length_cons]
  omega

theorem literalTerms_length (S : Selection n c) (failed : Fin c) (i : Fin c) (s : Slot) :
    (literalTerms S failed i s).length ≤ 5 := by
  have he := ellTerms_length S failed (S.literal i s).index
  have hb := bTerms_length S failed
  unfold literalTerms masked
  split <;> simp only [List.length_append, List.length_nil] <;> omega

theorem auxiliaryTerms_length (S : Selection n c) (failed : Fin c) (i : Fin c) :
    (auxiliaryTerms S failed i).length ≤ 6 := by
  have hl := literalTerms_length S failed i .middle
  unfold auxiliaryTerms
  split <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem companionTerms_length (S : Selection n c) (failed : Fin c) (r : Row c) :
    (companionTerms S failed r).length ≤ 6 := by
  rcases r with ⟨i,b⟩
  have h₁ := literalTerms_length S failed i .first
  have h₂ := literalTerms_length S failed i .middle
  have h₃ := literalTerms_length S failed i .last
  have ht := auxiliaryTerms_length S failed i
  cases b <;> cases hm : S.mode i with
  | none => simp [companionTerms, hm, auxiliaryTerms] <;> omega
  | some s => cases s <;> simp [companionTerms, hm, auxiliaryTerms] <;> omega

theorem aTerms_length (S : Selection n c) (failed : Fin c) (r : Row c) :
    (aTerms S failed r).length ≤ 7 := by
  have h := companionTerms_length S failed r
  simp only [aTerms, List.length_cons]
  omega

theorem imageTerms_length (S : Selection n c) (failed : Fin c) (i : Fin c) :
    (imageTerms S failed i).length ≤ 6 := by
  have h := literalTerms_length S failed i .first
  simp only [imageTerms, List.length_cons]
  omega


end PNP.Concrete.NativeNormalization.NativeCoefficients
