import PNP.Concrete.ResidualReduction.SharedRefutationCircuit
import PNP.Concrete.ResidualReduction.SharedRefutationSourceLift

/-! A source-generated terminal refutation for zero-variable families.
The fixed circuit has chronological constants false at index zero and true at
index one. The roots select the first violated source row, preserving every
row position. No assignment enumeration, residual invariant, or solver is used. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationTerminal
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SharedRefutationCircuit
open PNP.Concrete.ResidualReduction.SharedRefutationSourceLift

/-- Code is newest first, so the false input has creation index zero. -/
def code : Code 0 :=
  [.input (aConst 0 true), .input (aConst 0 false)]

/-- Stop selecting after the first violated row; retain zero roots for all
remaining rows rather than truncating the source family. -/
def roots : Family 0 → List Nat
  | [] => []
  | r :: rows =>
      if r.eval () then 1 :: rows.map (fun _ => 0)
      else 0 :: roots rows

def certificate (rows : Family 0) : Code 0 × List Nat :=
  (code, roots rows)

theorem code_length : code.length = 2 := rfl
theorem code_valid : codeValid code = true := rfl
theorem value_zero : value code () 0 = false := rfl
theorem value_one : value code () 1 = true := rfl

theorem roots_length (rows : Family 0) : (roots rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    cases hr : r.eval () <;>
      simp only [roots, hr, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, List.length_map, ih]

theorem roots_bound (rows : Family 0) : ∀ i ∈ roots rows, i < 2 := by
  induction rows with
  | nil => intro i hi; cases hi
  | cons r rows ih =>
    cases hr : r.eval () with
    | false =>
      intro i hi
      simp only [roots, hr, Bool.false_eq_true, ↓reduceIte] at hi
      rcases List.mem_cons.mp hi with equal | member
      · subst i
        decide
      · exact ih i member
    | true =>
      intro i hi
      simp only [roots, hr, ↓reduceIte] at hi
      rcases List.mem_cons.mp hi with equal | member
      · subst i
        decide
      · obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
        decide

private theorem zero_roots_sum (rows : Family 0) :
    pairedSum ((rows.map (fun _ => 0)).map (value code ()))
      (rows.map (fun r => r.eval ())) = some false := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, value_zero, pairedSum,
      Bool.false_and, ih, Option.map, Bool.false_xor]

/-- Exact all-family identity, including satisfiable and empty terminal
families. A false terminal verdict therefore supplies its own refutation. -/
theorem scalar_identity (rows : Family 0) :
    pairedSum (outputs code () (roots rows))
      (rows.map (fun r => r.eval ())) = some (!models rows ()) := by
  change pairedSum ((roots rows).map (value code ()))
    (rows.map (fun r => r.eval ())) = some (!models rows ())
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    cases hr : r.eval () with
    | false =>
      simp only [roots, hr, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, value_zero, pairedSum, Bool.false_and,
        ih, Option.map, Bool.false_xor, models,
        Bool.not_false, Bool.true_and]
    | true =>
      simp only [roots, hr, ↓reduceIte, List.map_cons, value_one,
        pairedSum, zero_roots_sum, Option.map, Bool.true_and,
        Bool.xor_false, models, Bool.not_true, Bool.false_and,
        Bool.not_false]

theorem refutes (rows : Family 0) (verdict : models rows () = false) :
    pairedSum (outputs code () (roots rows))
      (rows.map (fun r => r.eval ())) = some true := by
  simpa only [verdict, Bool.not_false] using scalar_identity rows

theorem certificate_contract (rows : Family 0) :
    (certificate rows).1.length = 2 ∧
    codeValid (certificate rows).1 = true ∧
    (certificate rows).2.length = rows.length ∧
    (∀ i ∈ (certificate rows).2, i < (certificate rows).1.length) :=
  ⟨code_length, code_valid, roots_length rows, roots_bound rows⟩

theorem certificate_scalar_identity (rows : Family 0) :
    pairedSum (outputs (certificate rows).1 () (certificate rows).2)
      (rows.map (fun r => r.eval ())) = some (!models rows ()) :=
  scalar_identity rows

theorem certificate_refutes (rows : Family 0) (verdict : models rows () = false) :
    pairedSum (outputs (certificate rows).1 () (certificate rows).2)
      (rows.map (fun r => r.eval ())) = some true :=
  refutes rows verdict

end PNP.Concrete.ResidualReduction.SharedRefutationTerminal
