import PNP.Concrete.NativeNormalization.NativeCircuit
import PNP.Concrete.NativeNormalization.NativeDimensionCache

namespace PNP.Concrete.NativeNormalization.NativeFrontend

open PNP.Concrete CNFCore NativeBasis NativeEquations NativeSparseSystem NativeTseitin

private theorem compact_length (F : CNFFormula) (ls : List CNFLiteral)
    (h : ∀ l ∈ ls, ∃ k, compactLiteral F l = some k) :
    (compactClause F ls).length = ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      obtain ⟨k, hk⟩ := h l (by simp)
      have ht := ih (fun a ha => h a (by simp [ha]))
      simpa [compactClause, hk] using congrArg Nat.succ ht

/-- Compaction does not drop occurrences from a well-formed retained clause. -/
theorem threeCore_of_shape (F : CNFFormula)
    (shape : ∀ ls ∈ F.clauses, ls.length = 3 ∧
      ∀ l ∈ ls, l.variableIndex < F.variableCount) : NativeSource.ThreeCore F := by
  intro i
  have hc := shape (clause F (atClause F i)) (source_member F (atClause F i))
  have full : ∀ l ∈ clause F (atClause F i), ∃ k, compactLiteral F l = some k := by
    intro l hl
    have hb := hc.2 l hl
    have hi := kept_neighbor_inside F (atClause F i) ⟨l.variableIndex, hb⟩
      (atClause_kept F i) (incidence_of_mem F _ _ l hl rfl)
    exact ⟨_, compactLiteral_of_inside F l hb hi⟩
  exact (compact_length F _ full).trans hc.1

theorem frontend_three (F : CNFFormula) : NativeSource.ThreeCore (frontend F) :=
  threeCore_of_shape _ (frontend_shape F)

def SparseBounds {c : Nat} (D : System c) : Prop :=
  D.b.length ≤ 3 ∧
  (∀ entry ∈ D.a, entry.2.length ≤ 7) ∧
  (∀ terms ∈ D.e, terms.length ≤ 6) ∧
  D.a.length = 2*c ∧ D.e.length ≤ c ∧ D.coefficientCount ≤ 20*c+3

/-- No unsupported-shape constructor remains in the full-input interface. -/
inductive Result where
  | model (assignment : BitString)
  | system (rows : Nat) (data : System rows) (recoverModel : RowValues rows → BitString)

def Correct (F : CNFFormula) : Result → Prop
  | .model a => F.Satisfied a
  | .system c D liftModel =>
      (F.Satisfiable ↔ ∃ u, D.Satisfied u) ∧
      (∀ u, D.Satisfied u → F.Satisfied (liftModel u)) ∧
      c = (positions (frontend F)).length ∧ SparseBounds D

private def finish (F : CNFFormula) (c : Nat)
    (hc : c = (positions (frontend F)).length)
    (r : Output c)
    (h : OutputCorrect (frontend F) (NativeDimensionCache.transportOutput hc r)) : Result :=
  match r with
  | .notThree => False.elim (by
      cases hc
      exact h (frontend_three F))
  | .model a => .model (recoverOriginal F a)
  | .system D liftModel => .system c D
      (fun u => recoverOriginal F (liftModel u))

/-- Deterministic source-only construction; proof arguments are generated internally. -/
def produce (F : CNFFormula) : Result :=
  let built := NativeDimensionCache.build (frontend F) (frontend_three F)
  finish F built.rows built.rows_eq built.result built.correct

private theorem finish_correct (F : CNFFormula) (c : Nat)
    (hc : c = (positions (frontend F)).length)
    (r : Output c)
    (h : OutputCorrect (frontend F) (NativeDimensionCache.transportOutput hc r)) :
    Correct F (finish F c hc r h) := by
  cases hc
  cases r with
  | notThree => exact False.elim (h (frontend_three F))
  | model a => exact frontend_recovery F a h
  | system D liftModel =>
      obtain ⟨he, hr, hb⟩ := h
      exact ⟨(frontend_satisfiable_iff F).symm.trans he,
        fun u hu => frontend_recovery F _ (hr u hu), rfl, hb⟩

theorem produce_correct (F : CNFFormula) : Correct F (produce F) :=
  finish_correct F _ _ _ _

inductive EncodedResult where
  | malformed
  | model (assignment : BitString)
  | system (rows : Nat) (data : System rows) (recoverModel : RowValues rows → BitString)

def encodeResult : Result → EncodedResult
  | .model a => .model a
  | .system c D liftModel => .system c D liftModel

/-- Every bitstring is handled by the existing strict source decoder. -/
def convert (bits : BitString) : EncodedResult :=
  match decodeEncodedCNF bits with
  | none => .malformed
  | some F => encodeResult (produce F)

def SourceModel (bits a : BitString) : Prop :=
  ∃ F, decodeEncodedCNF bits = some F ∧ F.Satisfied a

def EncodedCorrect (bits : BitString) : EncodedResult → Prop
  | .malformed => ¬ CNFSAT bits
  | .model a => SourceModel bits a
  | .system _ D liftModel =>
      (CNFSAT bits ↔ ∃ u, D.check u = true) ∧
      (∀ u, D.check u = true → SourceModel bits (liftModel u)) ∧ SparseBounds D

/-- This proves exact translation and checking, not a search algorithm for the system. -/
theorem convert_correct (bits : BitString) : EncodedCorrect bits (convert bits) := by
  unfold convert
  cases hd : decodeEncodedCNF bits with
  | none =>
      intro h
      obtain ⟨F, hF, _⟩ := h
      rw [hd] at hF
      cases hF
  | some F =>
      change EncodedCorrect bits (encodeResult (produce F))
      have hc := produce_correct F
      have hs : CNFSAT bits ↔ F.Satisfiable := by
        constructor
        · rintro ⟨G, hG, hsat⟩
          have eq : G = F := Option.some.inj (hG.symm.trans hd)
          subst G
          exact hsat
        · intro hsat
          exact ⟨F, hd, hsat⟩
      cases hr : produce F with
      | model a =>
          rw [hr] at hc
          exact ⟨F, hd, hc⟩
      | system c D liftModel =>
          rw [hr] at hc
          obtain ⟨he, hrec, _, hb⟩ := hc
          refine ⟨?_, ?_, hb⟩
          · exact hs.trans (he.trans (by simp only [System.check_iff]))
          · intro u hu
            exact ⟨F, hd, hrec u ((System.check_iff D u).mp hu)⟩


end PNP.Concrete.NativeNormalization.NativeFrontend
