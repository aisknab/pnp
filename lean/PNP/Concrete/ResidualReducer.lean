/-
Copyright (c) 2026 PNP Labs.

Source-bound partial reduction of the complete normalized residual system.
All b/e/a constraints are retained. A nonzero-dimensional stopped core remains
unknown, not UNSAT. A step-count bound is not a total polynomial runtime proof.
No all-input residual solver, exact PCCMin or unconditional ZeroSlack is supplied.
-/
import PNP.Concrete.ResidualReduction.NativeSourceReduction

namespace PNP.Concrete.ResidualReducer

open NativeNormalization ResidualReduction.FactoredContraction

/-- Translate the complete actual sparse source, including its linear guards. -/
def sourceFamily {c : Nat} (D : NativeSparseSystem.System c) : Family (2*c) :=
  ResidualReduction.NativeSource.family D

/-- Compute source-derived steps until the selector stops or no coordinates remain. -/
def reduce {c : Nat} (D : NativeSparseSystem.System c) :
    ResidualReduction.SourceChain.Reduction (2*c) :=
  ResidualReduction.NativeSource.reduceSystem D

/-- Recover an encoded residual certificate from a remaining core assignment. -/
def recoverCertificate {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduce D).dimension) : BitString :=
  ResidualReduction.NativeSource.pointBytes ((reduce D).lift z)

/-- Sound partial verdict on the original input. None explicitly means unknown. -/
def decision (input : BitString) : Option Bool :=
  ResidualReduction.NativeSource.sourceVerdict input

theorem source_family_iff {c : Nat} (D : NativeSparseSystem.System c)
    (x : Point (2*c)) :
    models (sourceFamily D) x = true ↔
      D.Satisfied (ResidualReduction.NativeSource.pointRows x) :=
  ResidualReduction.NativeSource.family_satisfied D x

theorem source_family_rows {c : Nat} (D : NativeSparseSystem.System c) :
    (sourceFamily D).length = 1+D.e.length+D.a.length :=
  ResidualReduction.NativeSource.family_row_count D

theorem result_rows {c : Nat} (D : NativeSparseSystem.System c) :
    (reduce D).core.length = 1+D.e.length+D.a.length :=
  ResidualReduction.NativeSource.reduced_row_count D

theorem model_preservation {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduce D).dimension) :
    models (reduce D).core z = true ↔
      D.Satisfied (ResidualReduction.NativeSource.liftSystem D z) :=
  ResidualReduction.NativeSource.reduced_model_iff D z

theorem parameter_roundtrip {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduce D).dimension) :
    ResidualReduction.NativeSource.projectSystem D
      (ResidualReduction.NativeSource.liftSystem D z) = z :=
  ResidualReduction.NativeSource.project_lift_system D z

theorem source_model_roundtrip {c : Nat} (D : NativeSparseSystem.System c)
    (u : NativeEquations.RowValues c) (satisfied : D.Satisfied u) :
    ResidualReduction.NativeSource.liftSystem D
      (ResidualReduction.NativeSource.projectSystem D u) = u :=
  ResidualReduction.NativeSource.lift_project_system D u satisfied

theorem trace_linked {c : Nat} (D : NativeSparseSystem.System c) :
    ResidualReduction.SourceChain.Linked (sourceFamily D)
      (reduce D).history (reduce D).core :=
  ResidualReduction.NativeSource.reduced_trace_linked D

theorem dimension_accounting {c : Nat} (D : NativeSparseSystem.System c) :
    (reduce D).history.length+(reduce D).dimension = 2*c :=
  ResidualReduction.NativeSource.reduced_dimension_accounting D

theorem terminal {c : Nat} (D : NativeSparseSystem.System c) :
    ResidualReduction.SourceChain.stopped (reduce D).core :=
  ResidualReduction.SourceChain.reduce_terminal (2*c) (sourceFamily D)

/-- Equality with the actually emitted packet, not a supplied correctness premise. -/
theorem residual_source_iff (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (∃ z, models (reduce D).core z = true) ↔ CNFSAT input :=
  ResidualReduction.NativeSource.reduced_source_iff input c D decoded

theorem recover_certificate (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (z : Point (reduce D).dimension) (satisfied : models (reduce D).core z = true) :
    (recoverCertificate D z).length = 2*c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input)
        (recoverCertificate D z) = true :=
  ResidualReduction.NativeSource.lifted_certificate input c D decoded z satisfied

/-- This bounds only the number of reductions, not their total encoded work. -/
theorem step_bound (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (reduce D).history.length ≤ 30*input.length+12 :=
  ResidualReduction.NativeSource.source_step_bound input c D decoded

theorem decision_packet (input : BitString) :
    decision input = ResidualReduction.NativeSource.packetVerdict
      (NativeSerializedNormalizer.packet input) :=
  ResidualReduction.NativeSource.sourceVerdict_packet input

theorem decision_true_sound (input : BitString) (answer : decision input = some true) :
    CNFSAT input :=
  ResidualReduction.NativeSource.sourceVerdict_true_sound input answer

theorem decision_false_sound (input : BitString) (answer : decision input = some false) :
    ¬ CNFSAT input :=
  ResidualReduction.NativeSource.sourceVerdict_false_sound input answer

theorem decision_unknown (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (remaining : (reduce D).dimension ≠ 0) :
    decision input = none :=
  ResidualReduction.NativeSource.sourceVerdict_unresolved input c D decoded remaining

end PNP.Concrete.ResidualReducer
