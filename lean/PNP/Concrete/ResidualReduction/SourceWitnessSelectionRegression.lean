import PNP.Concrete.ResidualReduction.SourceWitnessSelection
import PNP.Concrete.ResidualReduction.SourceSelectionInvocation
import PNP.Concrete.ResidualReduction.SourcePlaneMenuRegression
import Lean

/-! First-success order, the essential construction-totality condition, dirty
scratch state, retained source words, canonical packet assembly and closed
query invocations. Runtime examples supplement but do not authorize proofs. -/

namespace PNP.Concrete.ResidualReduction.SourceWitnessSelection.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceClosure

private def query : Nat → Option Nat
  | 1 => some 7
  | 2 => some 9
  | _ => none
private def partialBuild : Nat → Option Nat
  | 0 => none
  | n + 1 => some (n + 1)

example : firstSome query [] = none := rfl
example : firstSome query [0,0,3] = none := rfl
example : firstSome query [0,1,2] = some 7 := rfl
example : firstSome query [0,2,1] = some 9 := rfl
example : firstSome query [2,2,1] = some 9 := rfl
example : firstSome (fun n => (some n).bind partialBuild) [0,1] = some 1 := rfl
example : (firstSome (fun n => some n) [0,1]).bind partialBuild = none := rfl
example : firstSome (fun n => (some n).bind partialBuild) [0,1] ≠
    (firstSome (fun n => some n) [0,1]).bind partialBuild := by decide

example (xs : List Nat) :
    firstSome (fun n => (query n).bind (fun x => some (x+1))) xs =
      (firstSome query xs).bind (fun x => some (x+1)) :=
  firstSome_bind_exact query (fun x => some (x+1)) xs (fun _ _ b _ => ⟨b+1,rfl⟩)

example {n : Nat} (F : Family (n+1)) : globalStep F = (choose F).bind (build F) := global_exact F
example {n : Nat} (F : Family (n+1)) : choose F = none ↔ globalStep F = none := choose_none_iff F
example {n : Nat} (F : Family (n+1)) (w : Choice (n+1) F.length) (h : choose F = some w) :
    ∃ s, build F w = some s ∧ globalStep F = some s ∧ StepSound F s := selected_step F w h
example {n : Nat} (F : Family (n+1)) (h : sourceAffineQuery F = none)
    (us : List (Affine (n+1))) :
    firstSome (lineCandidate F) us = (lineSearch F us).bind (build F) := line_search_exact F h us
example {n : Nat} (F : Family (n+1)) (h : sourceAffineQuery F = none)
    (ps : List (Affine (n+1) × Affine (n+1))) :
    firstSome (planeCandidate F) ps = (planeSearch F ps).bind (build F) := plane_search_exact F h ps

private def dirty : Store 3 := .cons [true,false] (.cons [false] (.cons [true,true] .nil))
private def saved : Store 2 := .cons [true,false,true] (.cons [false,false] .nil)
example : Exec (SourceSelectionFrame.reset 0) Store.nil 1 Store.nil := SourceSelectionFrame.reset_exec _
example : Exec (SourceSelectionFrame.reset 3) dirty 4 (Store.empty 3) := SourceSelectionFrame.reset_exec _
example : Exec (Frame.block 2 (SourceSelectionFrame.reset 3)) (Frame.join dirty saved) 4
    (Frame.join (Store.empty 3) saved) := SourceSelectionFrame.reset_framed dirty saved
example : Exec (SourceSelectionFrame.restart (0 : Fin 3) (1 : Fin 2)) (Frame.join dirty saved) 5
    (Frame.join ((Store.empty 3).set 0 [false,false]) saved) :=
  SourceSelectionFrame.restart_exec dirty saved 0 1
example : SourceLinePullback.transferStore
    ([0,2,0].map (Action.clear : Fin 3 → Action 3)) dirty =
    .cons [] (.cons [false] (.cons [] .nil)) := rfl

private def a : Affine 1 := (true,false)
private def b : Affine 1 := (false,false)
example : SourceSelectionPacket.bytes [true,false] [true,false] [true,false] [false] =
    [true,false,true,false,true,false,false] := rfl
example : (SourceSelectionPacket.terminal ([] : Family 1) [a]).output =
    [true,false,true,false,true,false,false] := by
  rw [SourceSelectionPacket.terminal_output]
  rfl
example : (SourceSelectionPacket.terminal ([] : Family 1) [a,b]).output =
    [true,false,true,true,false,true,false,false,false,false] := by
  rw [SourceSelectionPacket.terminal_output]
  rfl
example (dimension count normals family : BitString) :
    Exec SourceSelectionPacket.block (SourceSelectionPacket.ready dimension count normals family).store
      (8 * (SourceSelectionPacket.bytes dimension count normals family).length + 24)
      (SourceSelectionPacket.result dimension count normals family).store :=
  SourceSelectionPacket.block_exec dimension count normals family
example {n : Nat} (F : Family n) (alpha : Affine n) :
    8 * (SourceDirectionEncoding.codec.encode ⟨n,[alpha],F⟩).length + 24 ≤
      16 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 48 :=
  SourceSelectionPacket.line_instruction_bound F alpha
example {n : Nat} (F : Family n) (alpha beta : Affine n) :
    8 * (SourceDirectionEncoding.codec.encode ⟨n,[alpha,beta],F⟩).length + 24 ≤
      24 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 64 :=
  SourceSelectionPacket.plane_instruction_bound F alpha beta

example (r : Store 38) (d : SourceSelectionInvocation.Data) :
    Exec SourceSelectionInvocation.assemble (SourceSelectionInvocation.full r d)
      (8 * (SourceSelectionInvocation.word d).length + 68)
      (SourceSelectionInvocation.full
        (SourceSelectionInvocation.packetCore (SourceSelectionInvocation.packetResult d))
        (SourceSelectionInvocation.assembled d)) := SourceSelectionInvocation.assemble_exec r d

example {n : Nat} (F : Family n) (alpha : Affine n)
    (r : Store 38) (oldPacket oldOutput : BitString) :
    ∃ used after, Exec SourceSelectionInvocation.line
      (SourceSelectionInvocation.full r (SourceSelectionInvocation.initial F [alpha] oldPacket oldOutput)) used
      (SourceSelectionInvocation.full after
        (SourceSelectionInvocation.returned (SourceSelectionInvocation.initial F [alpha] oldPacket oldOutput)
          ((SourceLineOutput.codec n F.length).encode (SourceLine.sourceLineQuery F alpha)))) ∧
      used ≤ SourceLineRaw.sourceBudget (SourceDirectionEncoding.codec.encode ⟨n,[alpha],F⟩).length +
        8 * (SourceDirectionEncoding.codec.encode ⟨n,[alpha],F⟩).length + 109 :=
  SourceSelectionInvocation.line_family_exec F alpha r oldPacket oldOutput
example {n : Nat} (F : Family n) (alpha beta : Affine n)
    (r : Store 38) (oldPacket oldOutput : BitString) :
    ∃ used after, Exec SourceSelectionInvocation.plane
      (SourceSelectionInvocation.full r (SourceSelectionInvocation.initial F [alpha,beta] oldPacket oldOutput)) used
      (SourceSelectionInvocation.full after
        (SourceSelectionInvocation.returned (SourceSelectionInvocation.initial F [alpha,beta] oldPacket oldOutput)
          ((SourceAffineOutput.witnessCodec F.length n).encode (SourcePlane.sourcePlaneQuery F alpha beta)))) ∧
      used ≤ SourcePlaneRaw.sourceBudget (SourceDirectionEncoding.codec.encode ⟨n,[alpha,beta],F⟩).length +
        8 * (SourceDirectionEncoding.codec.encode ⟨n,[alpha,beta],F⟩).length + 109 :=
  SourceSelectionInvocation.plane_family_exec F alpha beta r oldPacket oldOutput
example (d : SourceSelectionInvocation.Data) (answer : BitString) :
    (SourceSelectionInvocation.returned d answer).family = d.family :=
  (SourceSelectionInvocation.returned_inputs d answer).2.2.2

#eval (show IO Unit from do
  let resetProgram := (SourceSelectionFrame.reset 3).program 0 2
  let cleared := BitRegister.run resetProgram 5 ⟨.running 0,dirty⟩
  if cleared.control != .accepted || cleared.store.get 0 != [] ||
      cleared.store.get 1 != [] || cleared.store.get 2 != [] then
    throw (IO.userError "Framed reset regression failed")
  let cases : List (SourceSelectionInvocation.Data × BitString) :=
    [(⟨[true,false],[true,false],[false,true],[true,false,false],[true],[true,true]⟩,
      [true,false,true,false,false,true,true,false,false]),
     (⟨[],[],[],[],[true],[false]⟩,[])]
  let assembly := SourceSelectionInvocation.assemble.program 0 42
  for (data,expected) in cases do
    let dirtyPrefix := ((Store.empty 38).set 8 [true,true]).set 37 [true,false,true]
    let final := BitRegister.run assembly 160 ⟨.running 0,SourceSelectionInvocation.full dirtyPrefix data⟩
    if final.control != .accepted || final.store.get 42 != expected ||
        final.store.get 41 != data.family || final.store.get 40 != data.normals ||
        final.store.get 43 != data.output then
      throw (IO.userError "Source-preserving packet assembly regression failed"))

run_cmd do
  for name in [
    ``SourceWitnessSelection.firstSome_bind_exact,
    ``SourceWitnessSelection.affine_total,
    ``SourceWitnessSelection.line_query_total,
    ``SourceWitnessSelection.plane_query_total,
    ``SourceWitnessSelection.line_search_exact,
    ``SourceWitnessSelection.plane_search_exact,
    ``SourceWitnessSelection.choose_total,
    ``SourceWitnessSelection.global_exact,
    ``SourceWitnessSelection.choose_none_iff,
    ``SourceWitnessSelection.selected_step,
    ``SourceSelectionFrame.cleared_get,
    ``SourceSelectionFrame.empty_get,
    ``SourceSelectionFrame.reset_store,
    ``SourceSelectionFrame.reset_exec,
    ``SourceSelectionFrame.reset_framed,
    ``SourceSelectionFrame.restart_exec,
    ``SourceSelectionFrame.invoke_exec,
    ``SourceSelectionFrame.result_saved,
    ``SourceSelectionFrame.other_saved,
    ``SourceSelectionPacket.block_exec,
    ``SourceSelectionPacket.result_output,
    ``SourceSelectionPacket.canonical_bytes,
    ``SourceSelectionPacket.canonical_exec,
    ``SourceSelectionPacket.terminal_output,
    ``SourceSelectionPacket.line_packet_length,
    ``SourceSelectionPacket.plane_packet_length,
    ``SourceSelectionPacket.line_instruction_bound,
    ``SourceSelectionPacket.plane_instruction_bound,
    ``SourceSelectionQueryCall.affine_exec,
    ``SourceSelectionQueryCall.plane_exec,
    ``SourceSelectionQueryCall.line_exec,
    ``SourceSelectionQueryCall.affine_call_exec,
    ``SourceSelectionQueryCall.plane_call_exec,
    ``SourceSelectionQueryCall.line_call_exec,
    ``SourceSelectionInvocation.loadWords_exec,
    ``SourceSelectionInvocation.prepare_exec,
    ``SourceSelectionInvocation.capture_exec,
    ``SourceSelectionInvocation.assemble_exec,
    ``SourceSelectionInvocation.line_exec,
    ``SourceSelectionInvocation.plane_exec,
    ``SourceSelectionInvocation.initial_word,
    ``SourceSelectionInvocation.line_family_exec,
    ``SourceSelectionInvocation.plane_family_exec,
    ``SourceSelectionInvocation.returned_inputs] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceWitnessSelection.global_exact
#print axioms PNP.Concrete.ResidualReduction.SourceSelectionFrame.reset_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectionPacket.canonical_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectionQueryCall.line_call_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectionInvocation.line_family_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectionInvocation.plane_family_exec

end PNP.Concrete.ResidualReduction.SourceWitnessSelection.Regression
