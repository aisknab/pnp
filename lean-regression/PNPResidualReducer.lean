import PNP

namespace PNP.Concrete.ResidualReducerRegression

open NativeNormalization ResidualReduction.FactoredContraction ResidualReducer

-- These independent types cover arbitrary native systems and original bitstrings.
example {c : Nat} (D : NativeSparseSystem.System c)
    (x : Point (2*c)) :
    models (sourceFamily D) x = true ↔
      D.Satisfied (ResidualReduction.NativeSource.pointRows x) :=
  ResidualReduction.NativeSource.family_satisfied D x

example {c : Nat} (D : NativeSparseSystem.System c) :
    (sourceFamily D).length = 1+D.e.length+D.a.length :=
  ResidualReduction.NativeSource.family_row_count D

example {c : Nat} (D : NativeSparseSystem.System c) :
    (reduce D).core.length = 1+D.e.length+D.a.length :=
  ResidualReduction.NativeSource.reduced_row_count D

example {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduce D).dimension) :
    models (reduce D).core z = true ↔
      D.Satisfied (ResidualReduction.NativeSource.liftSystem D z) :=
  ResidualReduction.NativeSource.reduced_model_iff D z

example {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduce D).dimension) :
    ResidualReduction.NativeSource.projectSystem D
      (ResidualReduction.NativeSource.liftSystem D z) = z :=
  ResidualReduction.NativeSource.project_lift_system D z

example {c : Nat} (D : NativeSparseSystem.System c)
    (u : NativeEquations.RowValues c) (satisfied : D.Satisfied u) :
    ResidualReduction.NativeSource.liftSystem D
      (ResidualReduction.NativeSource.projectSystem D u) = u :=
  ResidualReduction.NativeSource.lift_project_system D u satisfied

example {c : Nat} (D : NativeSparseSystem.System c) :
    ResidualReduction.SourceChain.Linked (sourceFamily D)
      (reduce D).history (reduce D).core :=
  ResidualReduction.NativeSource.reduced_trace_linked D

example {c : Nat} (D : NativeSparseSystem.System c) :
    (reduce D).history.length+(reduce D).dimension = 2*c :=
  ResidualReduction.NativeSource.reduced_dimension_accounting D

example {c : Nat} (D : NativeSparseSystem.System c) :
    ResidualReduction.SourceChain.stopped (reduce D).core :=
  ResidualReduction.SourceChain.reduce_terminal (2*c) (sourceFamily D)

/-- Equality with the actually emitted packet, not a supplied correctness premise. -/
example (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (∃ z, models (reduce D).core z = true) ↔ CNFSAT input :=
  ResidualReduction.NativeSource.reduced_source_iff input c D decoded

example (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (z : Point (reduce D).dimension) (satisfied : models (reduce D).core z = true) :
    (recoverCertificate D z).length = 2*c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input)
        (recoverCertificate D z) = true :=
  ResidualReduction.NativeSource.lifted_certificate input c D decoded z satisfied

/-- This bounds only the number of reductions, not their total encoded work. -/
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (reduce D).history.length ≤ 30*input.length+12 :=
  ResidualReduction.NativeSource.source_step_bound input c D decoded

example (input : BitString) :
    decision input = ResidualReduction.NativeSource.packetVerdict
      (NativeSerializedNormalizer.packet input) :=
  ResidualReduction.NativeSource.sourceVerdict_packet input

example (input : BitString) (answer : decision input = some true) :
    CNFSAT input :=
  ResidualReduction.NativeSource.sourceVerdict_true_sound input answer

example (input : BitString) (answer : decision input = some false) :
    ¬ CNFSAT input :=
  ResidualReduction.NativeSource.sourceVerdict_false_sound input answer

example (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (remaining : (reduce D).dimension ≠ 0) :
    decision input = none :=
  ResidualReduction.NativeSource.sourceVerdict_unresolved input c D decoded remaining


-- Kernel guards exercise semantics only; these finite cases earn no proof credit.
private def positiveOnly : NativeSparseSystem.System 1 :=
  { b := [(0,false)], a := [], e := [] }

private def fixedModel : NativeSparseSystem.System 1 :=
  { b := [(0,false)], a := [], e := [[(0,true)]] }

private def impossible : NativeSparseSystem.System 1 :=
  { b := [], a := [], e := [] }

private def productGuard : NativeSparseSystem.System 1 :=
  { b := [(0,false)], a := [((0,true),[])], e := [] }

theorem positive_guard_retained :
    models (sourceFamily positiveOnly) (false,(false,())) = false := by decide

theorem linear_guard_retained :
    models (sourceFamily fixedModel) (true,(true,())) = false := by decide

theorem product_guard_retained :
    models (sourceFamily productGuard) (true,(true,())) = false := by decide

theorem duplicate_terms_cancel :
    aEval (ResidualReduction.NativeSource.sparseForm
      ([(0,false),(0,false)] : NativeCoefficients.Coefficients 1))
      (true,(false,())) = false := by decide

theorem coordinate_order_retained :
    ResidualReduction.NativeSource.pointBytes
      (ResidualReduction.NativeSource.sourcePoint
        (fun r : NativeEquations.Row 1 => !r.2)) = [true,false] := by decide

theorem unknown_can_be_satisfiable :
    ResidualReduction.NativeSource.packetVerdict (.system 1 positiveOnly) = none ∧
      models (sourceFamily positiveOnly) (true,(false,())) = true := by decide

theorem unknown_can_be_unsatisfiable :
    ResidualReduction.NativeSource.packetVerdict (.system 1 impossible) = none ∧
      (∀ x : Point 2, models (sourceFamily impossible) x = false) := by
  constructor
  · decide
  · rintro ⟨a,b,⟨⟩⟩
    cases a <;> cases b <;> decide

theorem zero_dimensional_success :
    (reduce fixedModel).dimension = 0 ∧
      ResidualReduction.NativeSource.packetVerdict (.system 1 fixedModel) = some true := by decide

theorem zero_dimensional_failure :
    ResidualReduction.NativeSource.packetVerdict
      (.system 0 { b := [], a := [], e := [] }) = some false := by decide

-- A non-model need not be reconstructed by project/lift.
theorem reconstruction_requires_a_model :
    ResidualReduction.NativeSource.pointBytes
      ((reduce fixedModel).lift ((reduce fixedModel).project (false,(false,())))) ≠
        [false,false] := by decide

end PNP.Concrete.ResidualReducerRegression

#print axioms PNP.Concrete.ResidualReducerRegression.positive_guard_retained
#print axioms PNP.Concrete.ResidualReducerRegression.linear_guard_retained
#print axioms PNP.Concrete.ResidualReducerRegression.product_guard_retained
#print axioms PNP.Concrete.ResidualReducerRegression.duplicate_terms_cancel
#print axioms PNP.Concrete.ResidualReducerRegression.coordinate_order_retained
#print axioms PNP.Concrete.ResidualReducerRegression.unknown_can_be_satisfiable
#print axioms PNP.Concrete.ResidualReducerRegression.unknown_can_be_unsatisfiable
#print axioms PNP.Concrete.ResidualReducerRegression.zero_dimensional_success
#print axioms PNP.Concrete.ResidualReducerRegression.zero_dimensional_failure
#print axioms PNP.Concrete.ResidualReducerRegression.reconstruction_requires_a_model

#eval IO.println "residual-reducer-regressions-complete: 16 general type contracts; 10 kernel guards"
