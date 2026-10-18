import PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial
import Lean

/-! Closed native-system integration and physical compilation contracts.
Concrete executions compare the complete family encoding against the existing
native decoder and family codec, not against the new serializer's own answer.
The general theorems cover arbitrary systems and all-input resource bounds. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeAssemblyRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

example (input : BitString) :
    Exec SourceNativeSystemInput.block (initial input) (SourceNativeSystemInput.fuel input)
      (work (SourceNativeSystemParse.result input).stream (SourceNativeSystemInput.answer input)
        (SourceNativeSystemParse.result input)) := SourceNativeSystemInput.block_exec input
example (input : BitString) :
    SourceNativeSystemInput.fuel input ≤ SourceNativeSystemInput.budget input.length :=
  SourceNativeSystemInput.fuel_bound input
example (input : BitString) (field : Field) :
    (field.word (SourceNativeSystemParse.result input)).length ≤
      input.length + SourceNativeSystemParse.budget input.length + 1 :=
  SourceNativeSystemParse.field_bound input field
example {c : Nat} (D : NativeSparseSystem.System c) :
    SourceNativeSystemInput.answer (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceHistoryEncoding.packet (NativeSource.family D) := by
  rw [SourceNativeSystemInput.canonical_answer,SourceNativeEncoding.family_packet]
example {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (SourceNativeSystemParse.canonical D suffix).total =
      List.replicate (1 + D.e.length + D.a.length) true :=
  SourceNativeSystemParse.canonical_total D suffix
example {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) :
    (SourceNativeSystemParse.canonical D suffix).rows =
      (SourceNativeEncoding.oneRow D.b ++ encodeSeq SourceNativeEncoding.zeroRow D.e).reverse :=
  SourceNativeSystemParse.canonical_rows D suffix
example {c : Nat} (D : NativeSparseSystem.System c) (suffix : BitString) (extra : suffix ≠ []) :
    SourceNativeSystemInput.answer (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)) =
      [false] := SourceNativeSystemInput.canonical_extra D suffix extra
example (input : BitString) :
    (SourceNativeSystemPolynomial.polynomial.output input).length ≤
      input.length + SourceNativeSystemInput.sourceFuel.eval input.length :=
  SourceNativeSystemPolynomial.output_length input
example : SourceNativeSystemPolynomial.polynomial.program =
    .machine (CompilerIO.rawMachine SourceNativeSystemPolynomial.program)
      (CompilerIO.runtimePolynomial 24 SourceNativeSystemInput.sourceFuel) :=
  SourceNativeSystemPolynomial.polynomial_program
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine SourceNativeSystemPolynomial.program)
      ((CompilerIO.runtimePolynomial 24 SourceNativeSystemInput.sourceFuel).eval input.length) input = .accept :=
  SourceNativeSystemPolynomial.machine_accepts input
example {c : Nat} (D : NativeSparseSystem.System c) :
    SourceNativeSystemPolynomial.polynomial.output
        (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceHistoryEncoding.packet (NativeSource.family D) :=
  SourceNativeSystemPolynomial.history_input_canonical D
example : SourceNativeSystemInput.answer [] = [false] := by decide
example : SourceNativeSystemInput.answer [false,false,false,false] =
    SourceHistoryEncoding.packet (NativeSource.family (⟨[],[],[]⟩ : NativeSparseSystem.System 0)) := by decide

private def reference (input : BitString) : BitString :=
  match NativeOutputPacket.codec.decode ([false,true,false] ++ input) with
  | some (.system _ D) => SourceHistoryEncoding.packet (NativeSource.family D)
  | _ => [false]

private def check (counter : IO.Ref Nat) (input expected : BitString) (label : String) : IO Unit := do
  let start := initial input
  for i in List.finRange 24 do
    if start.get i != (if i.val == 0 then input else []) then
      throw (IO.userError "Closed native system has hidden initial data")
  let ticks := SourceNativeSystemInput.fuel input
  if ticks > SourceNativeSystemInput.budget input.length ||
      SourceNativeSystemInput.sourceFuel.eval input.length != SourceNativeSystemInput.budget input.length + 1 then
    throw (IO.userError "Closed native-system source polynomial differs")
  let actual := BitRegister.run SourceNativeSystemPolynomial.program (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted || actual.store.get 8 != expected then
    throw (IO.userError (label ++ ": closed output differs from independent native decoder"))
  let saved := SourceNativeSystemParse.result input
  let state := work saved.stream expected saved
  for i in List.finRange 24 do
    if actual.store.get i != state.get i then
      throw (IO.userError (label ++ ": final scratch or protected state differs"))
  counter.modify (· + 1)

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun xs => [false :: xs,true :: xs])

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  for c in [0,1,2,3] do
    let terms : NativeCoefficients.Coefficients c :=
      (List.finRange c).flatMap (fun i => [(i,false),(i,true)])
    let entries := terms.map (fun r => (r,terms ++ [r]))
    let systems : List (NativeSparseSystem.System c) :=
      [⟨[],[],[]⟩,⟨terms,entries,[terms,[],terms ++ terms]⟩,
       ⟨terms ++ terms,entries.reverse ++ entries,[terms.reverse,terms,[]]⟩]
    for D in systems do
      let input := natural c ++ (NativeSystemCodec.systemCodec c).encode D
      let expected := SourceHistoryEncoding.packet (NativeSource.family D)
      if reference input != expected then throw (IO.userError "Native source reference codec differs")
      check counter input expected "Complete native system"
      for suffix in [[false],[true,false]] do
        if reference (input ++ suffix) != [false] then
          throw (IO.userError "Reference codec accepted a trailing suffix")
        check counter (input ++ suffix) [false] "Trailing native-system bytes"
  IO.println "NATIVE_ASSEMBLY_PHASE: complete systems, both row orders, repeats and trailing rejection passed"
  for size in List.range 6 do
    for input in words size do
      check counter input (reference input) "Exhaustive short native-system bytes"
  IO.println s!"NATIVE_ASSEMBLY_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceNativeSystemCanonical.linearRows_frame,
    ``SourceNativeSystemCanonical.productRows_frame,
    ``SourceNativeSystemCanonical.linear_loop,
    ``SourceNativeSystemCanonical.product_loop,
    ``SourceNativeSystemCanonical.linear_group,
    ``SourceNativeSystemCanonical.product_group,
    ``SourceNativeSystemCanonical.linearRows_dimension,
    ``SourceNativeSystemCanonical.linearRows_constant,
    ``SourceNativeSystemCanonical.linearRows_active,
    ``SourceNativeSystemCanonical.linearRows_products,
    ``SourceNativeSystemCanonical.productRows_dimension,
    ``SourceNativeSystemCanonical.productRows_constant,
    ``SourceNativeSystemCanonical.productRows_active,
    ``SourceNativeSystemCanonical.productRows_rows,
    ``SourceNativeSystemCanonical.counter_push,
    ``SourceNativeSystemCanonical.linearRows_total,
    ``SourceNativeSystemCanonical.productRows_total,
    ``SourceNativeSystemCanonical.linearOne_rows,
    ``SourceNativeSystemCanonical.linearRows_rows,
    ``SourceNativeSystemCanonical.productRows_products,
    ``SourceNativeSystemBody.block_exec,
    ``SourceNativeSystemBody.dimension_preserved,
    ``SourceNativeSystemBody.constant_preserved,
    ``SourceNativeSystemBody.pending_empty,
    ``SourceNativeSystemBody.stream_bound,
    ``SourceNativeSystemBody.polynomial_bound,
    ``SourceNativeSystemBody.first_canonical,
    ``SourceNativeSystemBody.second_canonical,
    ``SourceNativeSystemBody.canonical_active,
    ``SourceNativeSystemBody.canonical_result,
    ``SourceNativeSystemBody.canonical_exec,
    ``SourceNativeSystemParse.block_exec,
    ``SourceNativeSystemParse.fuel_bound,
    ``SourceNativeSystemParse.result_bounded,
    ``SourceNativeSystemParse.field_bound,
    ``SourceNativeSystemParse.canonical_result,
    ``SourceNativeSystemParse.canonical_dimension,
    ``SourceNativeSystemParse.canonical_stream,
    ``SourceNativeSystemParse.canonical_active,
    ``SourceNativeSystemParse.canonical_total,
    ``SourceNativeSystemParse.canonical_rows,
    ``SourceNativeSystemParse.canonical_products,
    ``SourceNativeSystemParse.canonical_exec,
    ``SourceNativeSystemSerialize.reverseInto_exec,
    ``SourceNativeSystemSerialize.block_exec,
    ``SourceNativeSystemSerialize.fuel_bound,
    ``SourceNativeSystemSerialize.canonical_word,
    ``SourceNativeSystemInput.trailer_exec,
    ``SourceNativeSystemInput.dispatch_exec,
    ``SourceNativeSystemInput.dispatch_bound,
    ``SourceNativeSystemInput.block_exec,
    ``SourceNativeSystemInput.fuel_bound,
    ``SourceNativeSystemInput.invalid_answer,
    ``SourceNativeSystemInput.trailing_answer,
    ``SourceNativeSystemInput.canonical_answer,
    ``SourceNativeSystemInput.canonical_extra,
    ``SourceNativeSystemInput.parserPolynomial_eval,
    ``SourceNativeSystemInput.sourceFuel_eval,
    ``SourceNativeSystemPolynomial.source_result,
    ``SourceNativeSystemPolynomial.acceptsWithin,
    ``SourceNativeSystemPolynomial.source_output,
    ``SourceNativeSystemPolynomial.polynomial_program,
    ``SourceNativeSystemPolynomial.polynomial_output,
    ``SourceNativeSystemPolynomial.polynomial_canonical,
    ``SourceNativeSystemPolynomial.history_input_canonical,
    ``SourceNativeSystemPolynomial.rejects_trailing,
    ``SourceNativeSystemPolynomial.output_length,
    ``SourceNativeSystemPolynomial.machine_accepts]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"NATIVE_ASSEMBLY_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical.linear_group
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemCanonical.product_group
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemInput.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemInput.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemInput.canonical_answer
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial.history_input_canonical
#print axioms PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial.machine_accepts

end PNP.Concrete.ResidualReduction.SourceNativeAssemblyRegression
