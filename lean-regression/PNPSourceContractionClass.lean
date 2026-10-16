import PNP

namespace PNP.Concrete.SourceClassRegression
open ResidualReduction.FactoredContraction
open ResidualReduction.SourceDirections
open ResidualReduction.SourceLine
open ResidualReduction.SourceBalance
open ResidualReduction.SourceClosure
open ResidualReduction.SourceChain
open ResidualReduction.SourceClass

-- Independent, arbitrary-dimension statements: no menu or coverage premise.
example {n : Nat} (F : Family n) (w : Point F.length) (v : Point n) :
    SemanticContraction F w v ↔ CoefficientContraction F w v :=
  semantic_iff_coefficient F w v

example {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c) :
    SemanticContraction F w v ↔
      ResidualReduction.SourceClass.Balanced F w v ∧ ChartQuadraticClosure F w c :=
  semantic_iff_chart F w v c hc

example {n : Nat} (F : Family (n+1))
    (h : ∃ w v, SemanticContraction F w v) :
    ∃ s, globalStep F = some s ∧ StepSound F s := by
  obtain ⟨s,hs⟩ := globalStep_complete_for_semantic F h
  exact ⟨s,hs,globalStep_sound F s hs⟩

example {n : Nat} (F : Family (n+1)) (h : globalStep F = none) :
    ¬ ∃ w v, SemanticContraction F w v :=
  globalStep_none_no_semantic F h

example {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (hb : ResidualReduction.SourceClass.Balanced F w v) (x : Point (n+1)) :
    decode (markSource F w) c.1 c.2 (encode c.1 c.2 x) = sourceRetraction F w v x :=
  decode_encode_eq_retraction F w v c hc hb x

example {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (hb : ResidualReduction.SourceClass.Balanced F w v)
    (hq : ChartQuadraticClosure F w c) : ∃ s, globalStep F = some s :=
  globalStep_complete_for_chart F w v c hc hb hq

-- Finite hostile guards are regression evidence, not theorem-progress credit.
private def emptySource : Family 1 := []

theorem exhausted_class_can_be_satisfiable :
    globalStep emptySource = none ∧ models emptySource (false,()) = true := by decide

private def x0 : Affine 4 := (true,(false,(false,(false,false))))
private def x1 : Affine 4 := (false,(true,(false,(false,false))))
private def x2 : Affine 4 := (false,(false,(true,(false,false))))
private def x3 : Affine 4 := (false,(false,(false,(true,false))))

private def cubicSource : Family 4 :=
  [⟨false,x0,aConst 4 true⟩,⟨false,x1,x2⟩,⟨false,x0,x3⟩]
private def cubicWeights : Point cubicSource.length := (true,(true,(false,())))
private def cubicDirection : Point 4 := (true,(false,(false,(false,()))))

theorem balance_does_not_supply_degree_closure :
    ResidualReduction.SourceClass.Balanced cubicSource cubicWeights cubicDirection := by
  constructor
  · decide
  · rintro ⟨a,b,c,d,⟨⟩⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The scalar omits the final source row, but closure must still preserve it.
    Its pullback is the cubic x1*x2*x3, so balance alone cannot justify a step. -/
theorem unselected_cubic_row_blocks_closure :
    ¬ SemanticContraction cubicSource cubicWeights cubicDirection := by
  intro hs
  have hc := semantic_implies_coefficient cubicSource cubicWeights cubicDirection hs
  have hr : (⟨false,x0,x3⟩ : Row 4) ∈ cubicSource :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have bad := hc.2 _ hr (false,(true,(false,(false,()))))
    (false,(false,(true,(false,())))) (false,(false,(false,(true,()))))
  change true = false at bad
  cases bad

private def constantSource : Family 1 :=
  [⟨false,(true,true),aConst 1 true⟩]

theorem affine_constants_are_retained :
    sourceRetraction constantSource (true,()) (true,()) (false,()) = (true,()) ∧
    sourceRetraction constantSource (true,()) (true,()) (true,()) = (true,()) ∧
    models constantSource (sourceRetraction constantSource (true,()) (true,()) (false,())) =
      true := ⟨rfl,rfl,rfl⟩

end PNP.Concrete.SourceClassRegression

#print axioms PNP.Concrete.SourceClassRegression.exhausted_class_can_be_satisfiable
#print axioms PNP.Concrete.SourceClassRegression.balance_does_not_supply_degree_closure
#print axioms PNP.Concrete.SourceClassRegression.unselected_cubic_row_blocks_closure
#print axioms PNP.Concrete.SourceClassRegression.affine_constants_are_retained

#eval IO.println "source-class-regressions-complete"
