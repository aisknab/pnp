import PNP.Concrete.NativeNormalization.MeasuredCollections
import PNP.Concrete.NativeNormalization.MeasuredEncodedProducer

namespace PNP.Concrete.NativeNormalization.MeasuredCompilationPlan

open PNP.Concrete CNFToNAND MeasuredReach

/-- Word/list-operation charges only. Nat comparison and coordinate arithmetic
still require the eventual concrete encoded-machine refinement. -/
def literal (inputs : Nat) (l : CNFLiteral) : Measured (List CompilationAction) :=
  ⟨if l.variableIndex < inputs then
      if l.positive then [.push (.input l.variableIndex)]
      else [.push (.input l.variableIndex),.negate]
    else [.push (.constant false)],12⟩

theorem literal_value (inputs : Nat) (l : CNFLiteral) :
    (literal inputs l).value = literalPlan inputs l := by
  by_cases h : l.variableIndex < inputs <;>
    cases hp : l.positive <;> simp [literal,literalPlan,h,hp]

theorem literal_length (inputs : Nat) (l : CNFLiteral) :
    (literal inputs l).value.length ≤ 2 := by
  by_cases h : l.variableIndex < inputs <;>
    cases hp : l.positive <;> simp [literal,h,hp]

theorem literal_cost (inputs : Nat) (l : CNFLiteral) : (literal inputs l).cost = 12 := rfl

def clause (inputs : Nat) : List CNFLiteral → Measured (List CompilationAction)
  | [] => ⟨[.push (.constant false)],3⟩
  | l::ls =>
      let head := literal inputs l
      let tail := clause inputs ls
      let suffix := MeasuredCollections.append tail.value [.negate,.nand]
      let middle := MeasuredCollections.append [.negate] suffix.value
      let joined := MeasuredCollections.append head.value middle.value
      ⟨joined.value,head.cost+tail.cost+suffix.cost+middle.cost+joined.cost+10⟩

theorem clause_value (inputs : Nat) (ls : List CNFLiteral) :
    (clause inputs ls).value = clausePlan inputs ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [clause,MeasuredCollections.append_value,literal_value,ih,clausePlan]
      simp only [List.append_assoc]

theorem clause_length (inputs : Nat) (ls : List CNFLiteral) :
    (clause inputs ls).value.length ≤ 5*ls.length+1 := by
  induction ls with
  | nil => exact Nat.le_refl _
  | cons l ls ih =>
      have hh := literal_length inputs l
      simp only [clause,MeasuredCollections.append_value,List.length_append,
        List.length_cons,List.length_nil]
      omega

def clauseBound (n : Nat) : Nat := 5*n*n+40*n+3

theorem clause_cost (inputs : Nat) (ls : List CNFLiteral) :
    (clause inputs ls).cost ≤ clauseBound ls.length := by
  induction ls with
  | nil => exact Nat.le_refl _
  | cons l ls ih =>
      have hh := literal_length inputs l
      have ht := clause_length inputs ls
      simp only [clause,MeasuredCollections.append_cost,literal_cost,
        List.length_cons,List.length_nil]
      unfold clauseBound at *
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
      simp only [Nat.mul_assoc] at *
      omega

def clauses (inputs : Nat) : List (List CNFLiteral) → Measured (List CompilationAction)
  | [] => ⟨[.push (.constant true)],3⟩
  | ls::rest =>
      let head := clause inputs ls
      let tail := clauses inputs rest
      let suffix := MeasuredCollections.append tail.value [.nand,.negate]
      let joined := MeasuredCollections.append head.value suffix.value
      ⟨joined.value,head.cost+tail.cost+suffix.cost+joined.cost+10⟩

theorem clauses_value (inputs : Nat) (cs : List (List CNFLiteral)) :
    (clauses inputs cs).value = clausesPlan inputs cs := by
  induction cs with
  | nil => rfl
  | cons ls cs ih =>
      simp only [clauses,MeasuredCollections.append_value,clause_value,ih,clausesPlan]
      simp only [List.append_assoc]

def workSize (cs : List (List CNFLiteral)) : Nat := (cs.map List.length).sum+cs.length

theorem workSize_cons (ls : List CNFLiteral) (cs : List (List CNFLiteral)) :
    workSize (ls::cs) = ls.length+workSize cs+1 := by
  simp only [workSize,List.map_cons,List.sum_cons,List.length_cons]
  omega

theorem clauses_length (inputs : Nat) (cs : List (List CNFLiteral)) :
    (clauses inputs cs).value.length ≤ 5*workSize cs+1 := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons ls cs ih =>
      have hh := clause_length inputs ls
      simp only [clauses,MeasuredCollections.append_value,List.length_append,
        List.length_cons,List.length_nil,workSize_cons]
      omega

def workBound (n : Nat) : Nat := 10*n*n+60*n+3

theorem workBound_mono (a b : Nat) (h : a ≤ b) : workBound a ≤ workBound b := by
  have hs := Nat.mul_le_mul_left 10 (Nat.mul_le_mul h h)
  unfold workBound
  simp only [Nat.mul_assoc] at *
  omega

theorem clauses_cost (inputs : Nat) (cs : List (List CNFLiteral)) :
    (clauses inputs cs).cost ≤ workBound (workSize cs) := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons ls cs ih =>
      have hc := clause_cost inputs ls
      have hl := clause_length inputs ls
      have ht := clauses_length inputs cs
      simp only [clauses,MeasuredCollections.append_cost,workSize_cons]
      unfold clauseBound workBound at *
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
      simp only [Nat.mul_assoc] at *
      omega

def formula (F : CNFFormula) : Measured (List CompilationAction) :=
  let result := clauses F.variableCount F.clauses
  ⟨result.value,result.cost+1⟩

theorem formula_value (F : CNFFormula) : (formula F).value = formulaPlan F :=
  clauses_value F.variableCount F.clauses

theorem formula_cost (F : CNFFormula) :
    (formula F).cost ≤ workBound (workSize F.clauses)+1 :=
  Nat.add_le_add_right (clauses_cost F.variableCount F.clauses) 1

theorem decoded_size (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) : workSize F.clauses ≤ 5*bits.length+1 := by
  have hp := formulaPlan_length_le_encoded_bits bits F decoded
  have he := formulaPlan_length_exact F
  change literalCount F+F.clauses.length ≤ 5*bits.length+1
  omega

theorem decoded_formula_cost (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (formula F).cost ≤ workBound (5*bits.length+1)+1 :=
  Nat.le_trans (formula_cost F)
    (Nat.add_le_add_right (workBound_mono _ _ (decoded_size bits F decoded)) 1)

def workPolynomial : NatPolynomial :=
  let size : NatPolynomial := .add (.mul (.constant 5) .variable) (.constant 1)
  .add (.add (.add (.mul (.mul (.constant 10) size) size)
    (.mul (.constant 60) size)) (.constant 3)) (.constant 1)

theorem workPolynomial_eval (m : Nat) : workPolynomial.eval m = workBound (5*m+1)+1 := rfl

theorem decoded_formula_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (formula F).cost ≤ workPolynomial.eval bits.length := by
  rw [workPolynomial_eval]
  exact decoded_formula_cost bits F decoded


end PNP.Concrete.NativeNormalization.MeasuredCompilationPlan
