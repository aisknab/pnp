import PNP.Concrete.ResidualReduction.SourceHistoryOutput
import PNP.Concrete.ResidualReduction.SourceReductionInputEncoding

/-! Polynomial source-instruction cost for the whole linked history, measured
in the original encoded family size. Successor packets cannot grow, and every
successful iteration removes one actual dimension. Raw input validation and
the physical compiler boundary are separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryBounds
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding

def stepPolynomial : NatPolynomial := .add SourceOriginalSuccessorBounds.sourceFuel
  (.add (.mul (.constant 8) (.mul .variable .variable)) (.linear 54 130))
theorem stepPolynomial_eval (L : Nat) :
    stepPolynomial.eval L = SourceOriginalSuccessorRaw.budget L + 8 * (L * L) + 54 * L + 131 := by
  simp only [stepPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant,
    NatPolynomial.eval_variable,NatPolynomial.eval_linear,SourceOriginalSuccessorBounds.sourceFuel_eval,
    SourceOriginalSuccessorRaw.budget]
  omega

theorem selected_bound {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length)
    (selected : globalStep F = some s) :
    SourceOriginalSuccessorRaw.budget (packet F).length + 62 + SourceHistoryRecord.fuel F s +
      SourceHistoryAdvance.fuel n F.length s.pivot.val ≤ stepPolynomial.eval (packet F).length := by
  have output := SourceOriginalSuccessorPolynomial.canonical_output_bound (n + 1) F
  simp only [SourceOriginalSuccessorRaw.canonicalAnswer,selected] at output
  change ((SourceEncoding.stepCodec n F.length).encode s).length + 1 ≤
    2 * ((packet F).length * (packet F).length) + 8 * (packet F).length + 5 at output
  have prefixSize : (recordPrefix F).length ≤ (packet F).length := by
    rw [positive_packet,List.length_cons]
    omega
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have rows := SourceMatrixEncoding.rowCount_bound (n + 1) F
  have pivot := s.pivot.isLt
  change n + 1 ≤ (packet F).length at dimension
  change F.length ≤ (packet F).length at rows
  rw [stepPolynomial_eval]
  unfold SourceHistoryRecord.fuel SourceHistoryAdvance.fuel
  omega

theorem fuel_bound_at (n : Nat) (F : Family n) (L : Nat) (input : (packet F).length ≤ L) :
    SourceHistoryLoop.fuel n F ≤ (n + 1) * stepPolynomial.eval L := by
  induction n with
  | zero =>
    simp only [SourceHistoryLoop.fuel,Nat.zero_add,Nat.one_mul,stepPolynomial_eval]
    omega
  | succ n ih =>
    have monotone := NatPolynomial.eval_mono stepPolynomial input
    cases selected : globalStep F with
    | none =>
      have one : SourceOriginalSuccessorRaw.budget (packet F).length + 65 ≤ stepPolynomial.eval L := by
        rw [stepPolynomial_eval] at monotone
        omega
      have multiple := Nat.mul_le_mul_right (stepPolynomial.eval L) (show 1 ≤ n + 1 + 1 by omega)
      simp only [Nat.one_mul] at multiple
      simpa only [SourceHistoryLoop.fuel,selected] using Nat.le_trans one multiple
    | some s =>
      have nextSize := Nat.le_trans (successor_packet_bound F s selected) input
      have tail := ih s.output nextSize
      have step := Nat.le_trans (selected_bound F s selected) monotone
      simp only [SourceHistoryLoop.fuel,selected,Nat.add_mul,Nat.one_mul] at tail ⊢
      omega

def loopPolynomial : NatPolynomial := .mul (.linear 1 1) stepPolynomial
theorem loop_bound (n : Nat) (F : Family n) :
    SourceHistoryLoop.fuel n F ≤ loopPolynomial.eval (packet F).length := by
  have bound := fuel_bound_at n F (packet F).length (Nat.le_refl _)
  have dimension := SourceMatrixEncoding.dimension_bound n F
  change n ≤ (packet F).length at dimension
  have multiple := Nat.mul_le_mul_right (stepPolynomial.eval (packet F).length)
    (Nat.add_le_add_right dimension 1)
  simpa only [loopPolynomial,NatPolynomial.eval_mul,NatPolynomial.eval_linear,Nat.one_mul] using
    Nat.le_trans bound multiple

def outputPolynomial : NatPolynomial :=
  .add (.mul (.constant 8) (SourceEncoding.dataPolynomial .variable .variable)) (.constant 23)
theorem output_bound (n : Nat) (F : Family n) :
    SourceHistoryOutput.fuel (reduce n F).core (reduce n F).history ≤
      outputPolynomial.eval (packet F).length := by
  have cost := SourceHistoryOutput.fuel_bound (reduce n F).core (reduce n F).history
  have storage := SourceEncoding.reduce_encoded_bound n F
  have dimensions := SourceMatrixEncoding.dimension_bound n F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  have monotone := SourceEncoding.dataBound_mono dimensions rows
  have bound := Nat.le_trans storage monotone
  change (SourceHistoryOutput.bytes (reduce n F).core (reduce n F).history).length ≤
    SourceEncoding.dataBound (packet F).length (packet F).length at bound
  simp only [outputPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant,
    SourceEncoding.dataPolynomial_eval,NatPolynomial.eval_variable]
  omega

def totalPolynomial : NatPolynomial := .add loopPolynomial outputPolynomial
theorem complete_bound (n : Nat) (F : Family n) :
    SourceHistoryLoop.fuel n F + SourceHistoryOutput.fuel (reduce n F).core (reduce n F).history ≤
      totalPolynomial.eval (packet F).length := by
  have loop := loop_bound n F
  have output := output_bound n F
  simp only [totalPolynomial,NatPolynomial.eval_add]
  omega

end PNP.Concrete.ResidualReduction.SourceHistoryBounds
