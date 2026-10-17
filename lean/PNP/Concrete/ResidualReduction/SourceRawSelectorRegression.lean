import PNP.Concrete.ResidualReduction.SourcePolynomialSelector
import Lean

/-! Raw selector integration regressions: exact Choice bytes, non-square line
witness fields, arbitrary stale state, malformed/trailing source packets, and
the actual all-input program. These fixtures supplement the uniform execution
and compiler proofs; they are not mathematical progress credit. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialSelector.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceSelectorResult
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)

private def weights : Point 2 := (true,(false,()))
private def direction : Point 1 := (true,())
private def normal : Affine 1 := (true,false)
private def other : Affine 1 := (false,true)
private def witness : LineWitness 1 2 := ⟨weights,(false,()),direction⟩

example : (SourceChoiceEncoding.codec 1 2).encode none = [false] := rfl
example : (SourceChoiceEncoding.codec 1 2).encode (some (affineChoice (weights,direction))) =
    [true,false,true,false,true] := rfl
example : (SourceChoiceEncoding.codec 1 2).encode (some (planeChoice (normal,other) (weights,direction))) =
    [true,true,true,false,false,true,true,false,true] := rfl
example : (SourceChoiceEncoding.codec 1 2).encode (some (lineChoice normal witness)) =
    [true,true,true,false,false,false,true,false,true] := by
  rw [SourceChoiceEncoding.line_bytes]
  rfl
example : (SourceChoiceEncoding.codec 1 2).encode (some (planeChoice (normal,other) (weights,direction))) ≠
    (SourceChoiceEncoding.codec 1 2).encode (some (lineChoice normal witness)) := by
  rw [SourceChoiceEncoding.line_bytes]
  decide

example {n m : Nat} (w : Option (Choice n m)) :
    (SourceChoiceEncoding.codec n m).decode ((SourceChoiceEncoding.codec n m).encode w) = some w :=
  SourceChoiceEncoding.roundtrip w
example (n : Nat) (alpha ws beta dir : BitString) (hb : beta.length = n) (hd : dir.length = n) :
    Exec SourceChoiceLine.block (SourceChoiceLine.ready n alpha ws beta dir).store
      (SourceChoiceLine.fuel n ws.length) (SourceSelectionPacket.ready alpha (beta ++ [false]) ws dir).store :=
  SourceChoiceLine.block_exec n alpha ws beta dir hb hd
example (r : Store 16) (input : BitString) :
    SourceSelectorInput.loaded r input = Frame.join r (SourceSelectorInput.loaderFrame input) :=
  SourceSelectorInput.loaded_eq r input
example {n : Nat} (F : Family n) :
    SourceSelectorInput.constructCost n F.length (SourceMatrixEncoding.familyBits F).length ≤
      SourceSelectorInput.constructPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length :=
  SourceSelectorInput.construct_bound F
example (input : BitString) :
    ∃ used after, Exec SourceRawSelector.block (SourceSelectorInput.rawStart input) used after ∧
      used ≤ SourceRawSelector.sourceBudget input.length ∧ after.get 8 = SourceRawSelector.answer input :=
  SourceRawSelector.block_exec input
example (input : BitString) (invalid : SourceMatrixEncoding.codec.decode input = none) :
    SourceRawSelector.answer input = [false] := SourceRawSelector.answer_malformed input invalid
example : SourceRawSelector.answer [] = [false] := rfl
example : SourceRawSelector.answer [true] = [false] := rfl
example : SourceRawSelector.answer [false] = [false] := rfl
example : SourceRawSelector.answer [false,false,true] = [false] := rfl
example : SourceRawSelector.answer [false,true,false] = [false] := rfl

example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example (input : BitString) : polynomial.output input = SourceRawSelector.answer input := polynomial_output input
example (n : Nat) (F : Family n) :
    (SourceChoiceEncoding.codec n F.length).decode
      (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n,F⟩)) = some (choose F) :=
  exact_decoded_choice n F
example {n : Nat} (F : Family (n + 1)) :
    (((SourceChoiceEncoding.codec (n + 1) F.length).decode
      (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩))).getD none).bind (build F) =
      SourceChain.globalStep F := global_step_exact F
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 48 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) : (polynomial.output input).length ≤ 4 * input.length + 4 :=
  polynomial_output_bound input

#eval (show IO Unit from do
  let cases : List (Nat × BitString × BitString × BitString × BitString) :=
    [(0,[true,false],[true,false,true],[],[]),
     (1,[true,false],[true,false],[false],[true]),
     (2,[false,true,false],[true,false,true],[true,false],[false,true]),
     (3,[true,false,true,false],[],[false,true,false],[true,false,false])]
  for (n,alpha,ws,beta,dir) in cases do
    let final := BitRegister.run (SourceChoiceLine.block.program 0 8)
      (SourceChoiceLine.fuel n ws.length + 1) ⟨.running 0,(SourceChoiceLine.ready n alpha ws beta dir).store⟩
    if final.control != .accepted || final.store.get 0 != dir ||
        final.store.get 1 != alpha || final.store.get 4 != ws ||
        final.store.get 5 != beta ++ [false] || final.store.get 6 != [] then
      throw (IO.userError "Line witness field reorder regression failed")
  let ws : Point 3 := (true,(false,(true,())))
  let dir : Point 2 := (false,(true,()))
  let beta : Point 2 := (true,(false,()))
  let alpha : Affine 2 := (false,(true,true))
  let second : Affine 2 := (true,(false,true))
  let lineWitness : LineWitness 2 3 := ⟨ws,beta,dir⟩
  let results : List (Result 2 3) := [.absent,.affine (ws,dir),.line alpha lineWitness,.plane (alpha,second) (ws,dir)]
  let dirty := (((Store.empty 38).set 0 [true,true]).set 7 [false,true]).set 37 [true,false]
  let held : SourceCandidateLoad.Held := ⟨[true,false],[false,true]⟩
  let saved : SourceSelectorState.Saved := ⟨[false,true,true],[false]⟩
  for result in results do
    let (count,normals,output) := match result with
      | .absent => ([true,true,true],[true,false],[false])
      | .affine w => (natural 0,[true,false],SourceCandidateSearch.optional SourceCandidateQueries.planePayload (some w))
      | .line a w => (natural 1,MatrixInstructions.affineWord a,
          SourceCandidateSearch.optional SourceCandidateQueries.linePayload (some w))
      | .plane p w => (natural 2,SourcePlaneMenuBytes.pairWord p,
          SourceCandidateSearch.optional SourceCandidateQueries.planePayload (some w))
    let data : Data := ⟨natural 2,count,normals,[true,false,true],[false,true,false],output⟩
    let final := BitRegister.run (SourceChoiceOutput.block.program 0 8) 1024
      ⟨.running 0,SourceSelectorState.full dirty data held saved⟩
    if final.control != .accepted || final.store.get 8 != (SourceChoiceEncoding.codec 2 3).encode (choice result) ||
        final.store.get 38 != data.dimension || final.store.get 40 != data.normals ||
        final.store.get 41 != data.family || final.store.get 42 != data.packet ||
        final.store.get 44 != held.pending || final.store.get 45 != held.width ||
        final.store.get 46 != saved.menu || final.store.get 47 != saved.width then
      throw (IO.userError "Canonical Choice serialization or retained-source regression failed")
  let malformed : List BitString :=
    [[],[true],[false],[true,false],[false,true,false],[false,false,true],[true,false,false,true]]
  for input in malformed do
    if (SourceMatrixEncoding.codec.decode input).isSome then
      throw (IO.userError "Malformed selector fixture accidentally became canonical")
    let mut final := BitRegister.initial program input
    for _ in [0:1024] do
      if final.control == .accepted then break
      final := BitRegister.run program 1 final
    if final.control != .accepted || final.store.get 8 != [false] then
      throw (IO.userError "Malformed selector input was not safely rejected")
  let sources : List (Sigma Family) :=
    [⟨0,[]⟩,⟨0,[⟨true,false,true⟩]⟩,⟨1,[]⟩,
     ⟨2,[⟨true,(true,(false,false)),(false,(true,false))⟩]⟩]
  for ⟨n,F⟩ in sources do
    let input := SourceMatrixEncoding.codec.encode ⟨n,F⟩
    let mut final := BitRegister.initial program input
    for _ in [0:50000] do
      if final.control == .accepted then break
      final := BitRegister.run program 1 final
    if final.control != .accepted ||
        final.store.get 8 != (SourceChoiceEncoding.codec n F.length).encode (choose F) then
      throw (IO.userError "Complete raw selector differs from the exact reference choice"))

run_cmd do
  for name in [
    ``SourceChoiceEncoding.none_bytes,
    ``SourceChoiceEncoding.affine_bytes,
    ``SourceChoiceEncoding.plane_bytes,
    ``SourceChoiceEncoding.line_bytes,
    ``SourceChoiceEncoding.roundtrip,
    ``SourceChoiceEncoding.bytes_bound,
    ``SourceChoiceEncoding.selected_bytes,
    ``SourceChoiceEncoding.selected_output_bound,
    ``SourceChoiceLine.reverse_exec,
    ``SourceChoiceLine.position_exec,
    ``SourceChoiceLine.direction_exec,
    ``SourceChoiceLine.saveDirection_exec,
    ``SourceChoiceLine.beta_exec,
    ``SourceChoiceLine.saveBeta_exec,
    ``SourceChoiceLine.weights_exec,
    ``SourceChoiceLine.finish_exec,
    ``SourceChoiceLine.block_exec,
    ``SourceChoiceOutput.working_get,
    ``SourceChoiceOutput.core_output,
    ``SourceChoiceOutput.count_get,
    ``SourceChoiceOutput.pop_count,
    ``SourceChoiceOutput.reject_exec,
    ``SourceChoiceOutput.affine_exec,
    ``SourceChoiceOutput.tags_exec,
    ``SourceChoiceOutput.plane_exec,
    ``SourceChoiceOutput.lineLoad_exec,
    ``SourceChoiceOutput.line_exec,
    ``SourceChoiceOutput.block_exec,
    ``SourceSelectorInput.loaded_eq,
    ``SourceSelectorInput.retain_exec,
    ``SourceSelectorInput.saveFamily_exec,
    ``SourceSelectorInput.saveWidth_exec,
    ``SourceSelectorInput.headerSeed_exec,
    ``SourceSelectorInput.capture_exec,
    ``SourceSelectorInput.handoff_exec,
    ``SourceSelectorInput.construct_exec,
    ``SourceSelectorInput.construct_bound,
    ``SourceRawSelector.answer_canonical,
    ``SourceRawSelector.answer_malformed,
    ``SourceRawSelector.process_exec,
    ``SourceRawSelector.loader_get,
    ``SourceRawSelector.failure_exec,
    ``SourceRawSelector.failure_output,
    ``SourceRawSelector.headers_exec,
    ``SourceRawSelector.complete_check,
    ``SourceRawSelector.short_check,
    ``SourceRawSelector.extra_check,
    ``SourceRawSelector.valid_exec,
    ``SourceRawSelector.failed_header,
    ``SourceRawSelector.failed_payload,
    ``SourceRawSelector.block_exec,
    ``SourceRawSelector.answer_length,
    ``SourcePolynomialSelector.sourceFuel_eval,
    ``SourcePolynomialSelector.source_result,
    ``SourcePolynomialSelector.acceptsWithin,
    ``SourcePolynomialSelector.source_output,
    ``SourcePolynomialSelector.polynomial_program,
    ``SourcePolynomialSelector.polynomial_output,
    ``SourcePolynomialSelector.polynomial_canonical,
    ``SourcePolynomialSelector.polynomial_malformed,
    ``SourcePolynomialSelector.exact_decoded_choice,
    ``SourcePolynomialSelector.global_step_exact,
    ``SourcePolynomialSelector.polynomial_machine_accepts,
    ``SourcePolynomialSelector.polynomial_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceChoiceOutput.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceSelectorInput.construct_exec
#print axioms PNP.Concrete.ResidualReduction.SourceRawSelector.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialSelector.acceptsWithin
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialSelector.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialSelector.global_step_exact

end PNP.Concrete.ResidualReduction.SourcePolynomialSelector.Regression
