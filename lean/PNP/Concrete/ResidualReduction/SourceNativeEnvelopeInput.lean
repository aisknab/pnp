import PNP.Concrete.ResidualReduction.SourceNativeHistoryBridge

/-! Literal native-packet tag dispatch. All bitstrings terminate within one
closed polynomial bound. Canonical malformed, model, and system packets produce
the exact source-reduction encoding; no family is supplied by a caller. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEnvelopeInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

def reject : Block 64 := .action (.push 8 false)
def model : Block 64 := .seq (.action (.copy 8 0))
  (.seq (.action (.push 8 false)) (.action (.push 8 true)))
def consume (body : Block 64) : Block 64 := .seq (.action (.pop 0)) body
def modelTag : Block 64 := .branch 0 reject reject (consume model)
def systemTag : Block 64 := .branch 0 reject (consume SourceNativeHistoryBridge.block) reject
def kind : Block 64 := .branch 0 reject (consume modelTag) (consume systemTag)
def block : Block 64 := .branch 0 reject (consume kind) reject

def modelTagAnswer : BitString → BitString
  | true :: data => true :: false :: data
  | _ => [false]
def systemTagAnswer : BitString → BitString
  | false :: data => SourceNativeHistoryBridge.answer data
  | _ => [false]
def kindAnswer : BitString → BitString
  | false :: data => modelTagAnswer data
  | true :: data => systemTagAnswer data
  | [] => [false]
def answer : BitString → BitString
  | false :: data => kindAnswer data
  | _ => [false]

theorem reject_exec (input : BitString) :
    Exec reject (work input [] []) 1 (work input [false] []) := .action _ _
theorem model_exec (input : BitString) :
    Exec model (work input [] []) 3 (work input (true :: false :: input) []) := by
  have a : Exec (.action (.copy (8 : Fin 64) 0)) (work input [] []) 1 (work input input []) := .action _ _
  have b : Exec (.action (.push (8 : Fin 64) false)) (work input input []) 1
      (work input (false :: input) []) := .action _ _
  have c : Exec (.action (.push (8 : Fin 64) true)) (work input (false :: input) []) 1
      (work input (true :: false :: input) []) := .action _ _
  exact Exec.seq a (Exec.seq b c)
theorem consume_exec {body : Block 64} {data : BitString} {used : Nat} {after : Store 64}
    (run : Exec body (work data [] []) used after) (bit : Bool) :
    Exec (consume body) (work (bit :: data) [] []) (1 + used) after :=
  Exec.seq (.action _ _) run

theorem modelTag_exec (input : BitString) :
    ∃ used after, Exec modelTag (work input [] []) used after ∧ used ≤ 5 ∧
      after.get 8 = modelTagAnswer input := by
  cases input with
  | nil => exact ⟨2,_,Exec.empty rfl (reject_exec []),by omega,rfl⟩
  | cons bit data =>
    cases bit with
    | false => exact ⟨2,_,Exec.zero rfl (reject_exec (false :: data)),by omega,rfl⟩
    | true => exact ⟨5,_,Exec.one rfl (consume_exec (model_exec data) true),Nat.le_refl _,rfl⟩

theorem systemTag_exec (input : BitString) :
    ∃ used after, Exec systemTag (work input [] []) used after ∧
      used ≤ SourceNativeHistoryBridge.costPolynomial.eval input.length + 2 ∧
      after.get 8 = systemTagAnswer input := by
  cases input with
  | nil => exact ⟨2,_,Exec.empty rfl (reject_exec []),by omega,rfl⟩
  | cons bit data =>
    cases bit with
    | true => exact ⟨2,_,Exec.one rfl (reject_exec (true :: data)),by omega,rfl⟩
    | false =>
      obtain ⟨used,run,bound⟩ := SourceNativeHistoryBridge.block_exec data
      have mono := NatPolynomial.eval_mono SourceNativeHistoryBridge.costPolynomial
        (show data.length ≤ (false :: data).length by simp only [List.length_cons]; omega)
      exact ⟨1 + (1 + used),_,Exec.zero rfl (consume_exec run false),by omega,
        SourceNativeHistoryBridge.result_output data⟩

theorem kind_exec (input : BitString) :
    ∃ used after, Exec kind (work input [] []) used after ∧
      used ≤ SourceNativeHistoryBridge.costPolynomial.eval input.length + 7 ∧
      after.get 8 = kindAnswer input := by
  cases input with
  | nil => exact ⟨2,_,Exec.empty rfl (reject_exec []),by omega,rfl⟩
  | cons bit data =>
    cases bit with
    | false =>
      obtain ⟨used,after,run,bound,output⟩ := modelTag_exec data
      exact ⟨1 + (1 + used),after,Exec.zero rfl (consume_exec run false),by omega,output⟩
    | true =>
      obtain ⟨used,after,run,bound,output⟩ := systemTag_exec data
      have mono := NatPolynomial.eval_mono SourceNativeHistoryBridge.costPolynomial
        (show data.length ≤ (true :: data).length by simp only [List.length_cons]; omega)
      exact ⟨1 + (1 + used),after,Exec.one rfl (consume_exec run true),by omega,output⟩

def sourceFuel : NatPolynomial := .add SourceNativeHistoryBridge.costPolynomial (.constant 10)
theorem sourceFuel_eval (L : Nat) :
    sourceFuel.eval L = SourceNativeHistoryBridge.costPolynomial.eval L + 10 := rfl

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (initial input) used after ∧
      used + 1 ≤ sourceFuel.eval input.length ∧ after.get 8 = answer input := by
  rw [sourceFuel_eval]
  cases input with
  | nil => exact ⟨2,_,Exec.empty rfl (reject_exec []),by omega,rfl⟩
  | cons bit data =>
    cases bit with
    | true => exact ⟨2,_,Exec.one rfl (reject_exec (true :: data)),by omega,rfl⟩
    | false =>
      obtain ⟨used,after,run,bound,output⟩ := kind_exec data
      have mono := NatPolynomial.eval_mono SourceNativeHistoryBridge.costPolynomial
        (show data.length ≤ (false :: data).length by simp only [List.length_cons]; omega)
      exact ⟨1 + (1 + used),after,Exec.zero rfl (consume_exec run false),by omega,output⟩

theorem canonical_answer (packet : NativeOutputPacket.Packet) :
    answer (NativeOutputPacket.encode packet) = SourceEncoding.encodeNativePacket packet := by
  cases packet with
  | malformed => rfl
  | model assignment => rfl
  | system c D => exact SourceNativeHistoryBridge.canonical_answer D

end PNP.Concrete.ResidualReduction.SourceNativeEnvelopeInput
