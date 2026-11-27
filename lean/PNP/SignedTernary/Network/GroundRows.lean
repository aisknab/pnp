import PNP.SignedTernary.CNF.Sites
import PNP.SignedTernary.Gate

namespace PNP.SignedTernary.Network
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.CNF PNP.Concrete

instance auxDecEq : (k : Nat) → DecidableEq (Aux k)
  | 0 => inferInstance
  | k+1 => letI := auxDecEq k; inferInstance

instance bankDecEq {α : Type} : (cs : List (List (Form α))) → DecidableEq (Bank cs)
  | [] => inferInstance
  | _::cs => letI := bankDecEq cs; inferInstance

def parsedSites : (p : Option CNFFormula) → List (ParsedPort p)
  | none => [()]
  | some F => portSites F

def parsedDecEq : (p : Option CNFFormula) → DecidableEq (ParsedPort p)
  | none => inferInstanceAs (DecidableEq Unit)
  | some F => inferInstanceAs (DecidableEq (Port F))

theorem parsedSites_complete (p : Option CNFFormula) :
    ∀ i, i ∈ parsedSites p := by
  cases p with
  | none => intro i; cases i; exact List.mem_cons_self
  | some F => exact portSites_complete F

def loadWord {α : Type} [DecidableEq α] :
    (sites : List α) → Vec sites.length → α → F3
  | [], _, _ => .z
  | a::as, x, i => if i = a then x.1 else loadWord as x.2 i

def storeWord {α : Type} (w : α → F3) : (sites : List α) → Vec sites.length
  | [] => ()
  | a::as => (w a,storeWord w as)

theorem load_store {α : Type} [DecidableEq α] (sites : List α) (w : α → F3)
    (i : α) (hi : i ∈ sites) : loadWord sites (storeWord w sites) i = w i := by
  induction sites with
  | nil => cases hi
  | cons a as ih =>
    simp only [loadWord,storeWord]
    by_cases h : i = a
    · subst i; rw [if_pos rfl]
    · rw [if_neg h]
      exact ih ((List.mem_cons).1 hi |>.resolve_left h)

theorem load_signed {α : Type} [DecidableEq α] (sites : List α)
    (x : Vec sites.length) (hx : Signed x) (i : α) (hi : i ∈ sites) :
    loadWord sites x i ≠ .z := by
  induction sites with
  | nil => cases hi
  | cons a as ih =>
    simp only [loadWord]
    by_cases h : i = a
    · rw [if_pos h]; exact hx.1
    · rw [if_neg h]
      exact ih x.2 hx.2 ((List.mem_cons).1 hi |>.resolve_left h)

theorem store_signed {α : Type} (sites : List α) (w : α → F3)
    (hw : ∀ i, w i ≠ .z) : Signed (storeWord w sites) := by
  induction sites with
  | nil => exact True.intro
  | cons a as ih => exact ⟨hw a,ih⟩

def unitRow {α : Type} [DecidableEq α] (i : α) : (sites : List α) → Vec sites.length
  | [] => ()
  | a::as => if i=a then (.o,zero as.length) else (.z,unitRow i as)

theorem dot_unitRow {α : Type} [DecidableEq α] (sites : List α) (i : α)
    (x : Vec sites.length) : dot (unitRow i sites) x = loadWord sites x i := by
  induction sites with
  | nil => rfl
  | cons a as ih =>
    by_cases h : i=a
    · simp only [unitRow,loadWord,h,if_pos,dot,one_mul]
      rw [dot_comm,dot_zero,add_zero]
    · simp only [unitRow,loadWord,h,if_false,dot,zero_mul,zero_add,ih]

def coeff {α : Type} [DecidableEq α] (sites : List α) : Form α → Vec sites.length
  | .zero => zero sites.length
  | .var i => unitRow i sites
  | .add r s => plus (coeff sites r) (coeff sites s)
  | .neg r => scale .t (coeff sites r)

theorem coeff_eval {α : Type} [DecidableEq α] (sites : List α) (r : Form α)
    (x : Vec sites.length) : dot (coeff sites r) x = eval (loadWord sites x) r := by
  induction r with
  | zero => change dot (zero sites.length) x = .z; rw [dot_comm,dot_zero]
  | var i => exact dot_unitRow sites i x
  | add r s ih it => rw [coeff,dot_plus_left,ih,it]; rfl
  | neg r ih =>
    rw [coeff,dot_scale_left,ih]
    change mul .t (eval (loadWord sites x) r) = neg (eval (loadWord sites x) r)
    cases eval (loadWord sites x) r <;> rfl

def matrix {α : Type} [DecidableEq α] (sites : List α) :
    (rs : List (Form α)) → Rows sites.length rs.length
  | [] => ()
  | r::rs => (coeff sites r,matrix sites rs)

theorem matrix_eval {α : Type} [DecidableEq α] (sites : List α)
    (rs : List (Form α)) (x : Vec sites.length) :
    Signed (applyRows (matrix sites rs) x) ↔ RowsNonzero (loadWord sites x) rs := by
  induction rs with
  | nil => exact Iff.rfl
  | cons r rs ih =>
    change (dot (coeff sites r) x ≠ .z ∧ Signed (applyRows (matrix sites rs) x)) ↔ _
    rw [coeff_eval,ih]
    exact Iff.rfl

theorem flat_iff {α : Type} [DecidableEq α] (sites : List α)
    (cover : ∀ i, i ∈ sites) (rs : List (Form α)) :
    (∃ x : Vec sites.length, Signed x ∧ Signed (applyRows (matrix sites rs) x)) ↔
    (∃ w : α → F3, (∀ i, w i ≠ .z) ∧ RowsNonzero w rs) := by
  constructor
  · rintro ⟨x,hx,hr⟩
    exact ⟨loadWord sites x,fun i => load_signed sites x hx i (cover i),(matrix_eval sites rs x).1 hr⟩
  · rintro ⟨w,hw,hr⟩
    refine ⟨storeWord w sites,store_signed sites w hw,(matrix_eval sites rs _).2 ?_⟩
    have he : loadWord sites (storeWord w sites) = w := by
      funext i
      exact load_store sites w i (cover i)
    rw [he]
    exact hr

def sourceMatrix (raw : BitString) :
    Rows (parsedSites (decodeEncodedCNF raw)).length (rawForms raw).length :=
  @matrix _ (parsedDecEq (decodeEncodedCNF raw))
    (parsedSites (decodeEncodedCNF raw)) (rawForms raw)

def FlatDonor (raw : BitString) : Prop :=
  ∃ x, Signed x ∧ Signed (applyRows (sourceMatrix raw) x)

theorem flat_iff_CNFSAT (raw : BitString) : FlatDonor raw ↔ CNFSAT raw := by
  letI := parsedDecEq (decodeEncodedCNF raw)
  exact (flat_iff (parsedSites (decodeEncodedCNF raw))
    (parsedSites_complete (decodeEncodedCNF raw)) (rawForms raw)).trans (raw_iff_CNFSAT raw)

end PNP.SignedTernary.Network
