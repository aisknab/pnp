import PNP.SignedTernary.CNF.Family
import PNP.Concrete.CNF

namespace PNP.SignedTernary.CNF
open PNP.SignedTernary.Field PNP.Concrete

/-- An actual width-n bit word, not a proposition standing for an assignment. -/
def readWord : (n : Nat) → (Fin n → Bool) → BitString
  | 0, _ => []
  | n+1, f => f ⟨0, Nat.zero_lt_succ n⟩ :: readWord n (fun i => f i.succ)

theorem readWord_length (n : Nat) (f : Fin n → Bool) : (readWord n f).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [readWord,List.length_cons,ih]

theorem readWord_at (n : Nat) (f : Fin n → Bool) (j : Nat) :
    assignmentAt (readWord n f) j =
      if h : j < n then some (f ⟨j,h⟩) else none := by
  induction n generalizing j with
  | zero => simp only [readWord,assignmentAt,Nat.not_lt_zero,dite_false]
  | succ n ih =>
    cases j with
    | zero => simp only [readWord,assignmentAt,Nat.zero_lt_succ,dif_pos]
    | succ j =>
      simp only [readWord,assignmentAt]
      rw [ih]
      by_cases h : j < n
      · simp only [h, Nat.succ_lt_succ_iff,dif_pos]
        rfl
      · simp only [h, Nat.succ_lt_succ_iff,dite_false]

theorem readWord_surjective (w : BitString) :
    ∃ f : Fin w.length → Bool, readWord w.length f = w := by
  induction w with
  | nil => exact ⟨(fun i => nomatch i), rfl⟩
  | cons b w ih =>
    obtain ⟨f,hf⟩ := ih
    refine ⟨Fin.cases b f, ?_⟩
    change b :: readWord w.length f = b :: w
    rw [hf]

abbrev Base (n : Nat) := Option (Fin n)

def literalForm (n : Nat) (l : CNFLiteral) : Form (Base n) :=
  if h : l.variableIndex < n then
    if l.positive then
      sub (.var (some ⟨l.variableIndex,h⟩)) (.var none)
    else
      sub (.neg (.var (some ⟨l.variableIndex,h⟩))) (.var none)
  else .zero

def baseWord {n : Nat} (g : F3) (f : Fin n → Bool) : Base n → F3
  | none => g
  | some i => encode g (f i)

def readBase {n : Nat} (base : Base n → F3) : Fin n → Bool :=
  fun i => decode (base none) (base (some i))

theorem base_signed {n : Nat} (g : F3) (hg : g ≠ .z) (f : Fin n → Bool) :
    ∀ i, baseWord g f i ≠ .z := by
  intro i
  cases i with
  | none => exact hg
  | some i => exact encode_nonzero g hg (f i)

theorem base_read {n : Nat} (base : Base n → F3) (hs : ∀ i, base i ≠ .z) :
    baseWord (base none) (readBase base) = base := by
  funext i
  cases i with
  | none => rfl
  | some i => exact encode_decode _ _ (hs none) (hs (some i))

theorem negative_read (g : F3) (b : Bool) :
    add (neg (encode g b)) (neg g) = bit g (!b) := by
  cases g <;> cases b <;> rfl

theorem literal_value {n : Nat} (g : F3) (f : Fin n → Bool) (l : CNFLiteral) :
    eval (baseWord g f) (literalForm n l) = bit g (checkLiteral l (readWord n f)) := by
  unfold checkLiteral
  rw [readWord_at]
  unfold literalForm
  by_cases h : l.variableIndex < n
  · simp only [h,dif_pos]
    cases hp : l.positive with
    | false =>
      simp only [Bool.false_eq_true,if_false,sub,eval,baseWord]
      rw [negative_read]
      cases f ⟨l.variableIndex,h⟩ <;> rfl
    | true =>
      simp only [if_true,sub,eval,baseWord]
      change readBit g (encode g (f ⟨l.variableIndex,h⟩)) = _
      rw [read_encode]
      cases f ⟨l.variableIndex,h⟩ <;> rfl
  · simp only [h,dite_false,eval,bit,Bool.false_eq_true,if_false]

theorem truthBit_bit (g : F3) (hg : g ≠ .z) (b : Bool) :
    truthBit (bit g b) = b := by
  cases g <;> cases b <;> simp_all [truthBit,bit]

theorem literal_bits {n : Nat} (g : F3) (f : Fin n → Bool) (l : CNFLiteral) :
    eval (baseWord g f) (literalForm n l) = .z ∨
      eval (baseWord g f) (literalForm n l) = g := by
  rw [literal_value]
  cases checkLiteral l (readWord n f)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem clause_bits {n : Nat} (g : F3) (f : Fin n → Bool) (c : List CNFLiteral) :
    Bits g (baseWord g f) (c.map (literalForm n)) := by
  induction c with
  | nil => exact True.intro
  | cons l ls ih => exact ⟨literal_bits g f l,ih⟩

theorem clause_truth {n : Nat} (g : F3) (hg : g ≠ .z) (f : Fin n → Bool)
    (c : List CNFLiteral) :
    truth (baseWord g f) (c.map (literalForm n)) = checkClause c (readWord n f) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons,truth,checkClause,literal_value,truthBit_bit g hg,ih]

def inputs (F : CNFFormula) : List (List (Form (Base F.variableCount))) :=
  F.clauses.map (fun c => c.map (literalForm F.variableCount))

theorem source_bits (F : CNFFormula) (g : F3) (f : Fin F.variableCount → Bool) :
    BankBits g (baseWord g f) (inputs F) := by
  unfold inputs
  induction F.clauses with
  | nil => exact True.intro
  | cons c cs ih => exact ⟨clause_bits g f c,ih⟩

theorem source_truth (F : CNFFormula) (g : F3) (hg : g ≠ .z)
    (f : Fin F.variableCount → Bool) :
    BankTruth (baseWord g f) (inputs F) ↔
      ClausesSatisfied F.clauses (readWord F.variableCount f) := by
  unfold inputs
  induction F.clauses with
  | nil => exact Iff.rfl
  | cons c cs ih =>
    change (truth (baseWord g f) (c.map (literalForm F.variableCount)) = true ∧ _) ↔ _
    rw [clause_truth _ hg,checkClause_eq_true_iff,ih]
    exact Iff.rfl

/-- Actual finite physical sites, with a shared original bit lane and fresh clause lanes. -/
abbrev Port (F : CNFFormula) := Sum (Base F.variableCount) (Bank (inputs F))

def equations (F : CNFFormula) : List (Form (Port F)) := compileBank none (inputs F)

def forms (F : CNFFormula) : List (Form (Port F)) :=
  pairRows (.var (.inl none)) (equations F)

def Model (F : CNFFormula) (w : Port F → F3) : Prop :=
  (∀ i, w i ≠ .z) ∧ RowsNonzero w (forms F)

def Feasible (F : CNFFormula) : Prop := ∃ w, Model F w

def readback (F : CNFFormula) (w : Port F → F3) : BitString :=
  readWord F.variableCount (readBase (fun i => w (.inl i)))

def donor (F : CNFFormula) (g : F3) (f : Fin F.variableCount → Bool) : Port F → F3 :=
  env (baseWord g f) (canonicalBank g (baseWord g f) (inputs F))

theorem split_env {α β : Type} (w : Sum α β → F3) :
    env (fun i => w (.inl i)) (fun i => w (.inr i)) = w := by
  funext i
  cases i <;> rfl

theorem source_read_bits (F : CNFFormula) (base : Base F.variableCount → F3)
    (hs : ∀ i, base i ≠ .z) : BankBits (base none) base (inputs F) := by
  have h := source_bits F (base none) (readBase base)
  rw [base_read base hs] at h
  exact h

theorem source_read_truth (F : CNFFormula) (base : Base F.variableCount → F3)
    (hs : ∀ i, base i ≠ .z) :
    BankTruth base (inputs F) ↔
      ClausesSatisfied F.clauses (readWord F.variableCount (readBase base)) := by
  have h := source_truth F (base none) (hs none) (readBase base)
  rw [base_read base hs] at h
  exact h

/-- Every satisfying physical sign word decodes to an actual width-correct source word. -/
theorem model_readback (F : CNFFormula) (w : Port F → F3) (hw : Model F w) :
    F.Satisfied (readback F w) := by
  have hr := (paired_rows_iff w (.var (.inl none)) (hw.1 (.inl none)) (equations F)).1 hw.2
  rw [← split_env w] at hr
  have hb := bank_sound none (fun i => w (.inl i)) (inputs F) (fun i => w (.inr i))
    (hw.1 (.inl none)) (source_read_bits F _ (fun i => hw.1 (.inl i)))
    (fun i => hw.1 (.inr i)) hr
  exact ⟨readWord_length _ _, (source_read_truth F _ (fun i => hw.1 (.inl i))).1 hb.1⟩

/-- The source word, gauge and every private auxiliary are constructed, not guessed. -/
theorem donor_model (F : CNFFormula) (g : F3) (hg : g ≠ .z)
    (f : Fin F.variableCount → Bool)
    (hf : ClausesSatisfied F.clauses (readWord F.variableCount f)) :
    Model F (donor F g f) := by
  constructor
  · intro i
    cases i with
    | inl i => exact base_signed g hg f i
    | inr i => exact canonical_bank_signed g hg (baseWord g f) (inputs F) i
  · apply (paired_rows_iff (donor F g f) (.var (.inl none)) hg (equations F)).2
    exact bank_complete none (baseWord g f) (inputs F) hg (source_bits F g f)
      ((source_truth F g hg f).2 hf)

theorem feasible_iff_satisfiable (F : CNFFormula) : Feasible F ↔ F.Satisfiable := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨readback F w, model_readback F w hw⟩
  · rintro ⟨w,hw⟩
    cases F with
    | mk n cs =>
      obtain ⟨hlen,hclauses⟩ := hw
      change w.length = n at hlen
      subst n
      obtain ⟨f,hf⟩ := readWord_surjective w
      refine ⟨donor ⟨w.length,cs⟩ .o f, donor_model ⟨w.length,cs⟩ .o (by intro h; cases h) f ?_⟩
      rw [hf]
      exact hclauses

theorem mapped_occurrences {α β : Type} (f : α → β) (cs : List (List α)) :
    occurrences (cs.map (fun c => c.map f)) = occurrences cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,occurrences,List.length_map,ih]

theorem equation_count (F : CNFFormula) :
    (equations F).length = 2*occurrences F.clauses + F.clauses.length := by
  rw [equations,bank_row_count]
  simp only [inputs,mapped_occurrences,List.length_map]

theorem form_count (F : CNFFormula) :
    (forms F).length = 4*occurrences F.clauses + 2*F.clauses.length := by
  rw [forms,pair_row_count,equation_count]
  omega

/-- Malformed inputs emit a real contradictory homogeneous pair, not an oracle bit. -/
def ParsedPort : Option CNFFormula → Type
  | none => Unit
  | some F => Port F

def parsedForms : (p : Option CNFFormula) → List (Form (ParsedPort p))
  | none => pairRows (.var ()) [.var ()]
  | some F => forms F

def ParsedFeasible (p : Option CNFFormula) : Prop :=
  ∃ w : ParsedPort p → F3, (∀ i, w i ≠ .z) ∧ RowsNonzero w (parsedForms p)

def rawPort (raw : BitString) := ParsedPort (decodeEncodedCNF raw)

def rawForms (raw : BitString) : List (Form (rawPort raw)) :=
  parsedForms (decodeEncodedCNF raw)

def RawFeasible (raw : BitString) : Prop :=
  ∃ w : rawPort raw → F3, (∀ i, w i ≠ .z) ∧ RowsNonzero w (rawForms raw)

theorem parsed_none_impossible : ¬ ParsedFeasible none := by
  rintro ⟨w,hs,hr⟩
  have he := (paired_rows_iff w (.var ()) (hs ()) [.var ()]).1 hr
  exact hs () he.1

/-- The strict all-bitstring endpoint, including malformed, zero-width, empty,
repeated and out-of-range literals, uses the repository's actual decoder. -/
theorem raw_iff_CNFSAT (raw : BitString) : RawFeasible raw ↔ CNFSAT raw := by
  change ParsedFeasible (decodeEncodedCNF raw) ↔
    ∃ F, decodeEncodedCNF raw = some F ∧ F.Satisfiable
  cases hd : decodeEncodedCNF raw with
  | none =>
    constructor
    · intro h
      exact False.elim (parsed_none_impossible h)
    · rintro ⟨F,hF,_⟩
      cases hF
  | some F =>
    constructor
    · intro h
      exact ⟨F,rfl,(feasible_iff_satisfiable F).1 h⟩
    · rintro ⟨F',hF,hs⟩
      cases hF
      exact (feasible_iff_satisfiable F).2 hs

theorem malformed_reject (raw : BitString) (hd : decodeEncodedCNF raw = none) :
    ¬ RawFeasible raw := by
  change ¬ ParsedFeasible (decodeEncodedCNF raw)
  rw [hd]
  exact parsed_none_impossible

theorem malformed_empty_control : ¬ RawFeasible [] :=
  malformed_reject [] rfl

end PNP.SignedTernary.CNF
