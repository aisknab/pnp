import PNP.Concrete.ResidualReduction.SourceReplayProject
import Lean

/-! Theorems and literal executions for the new replay step boundary only.
The general contracts cover arbitrary dimensions and families. Finite runs
challenge constants, weights, both shear branches, every pivot and protected
fields; they do not replace the universal theorems or validate whole histories. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceReplayState
open PNP.Concrete.ResidualReduction.MatrixInstructions

example {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    decode (markSource F w) k v z = unchart k v (weightedValue F w (insert n k (false,z)),z) :=
  SourceReplayAlgebra.decode_direct F w k v z
example (r : Registers) {n : Nat} (f : Affine n) (z : Point n) (suffix : BitString) :
    Exec SourceReplayAffine.block
      ({r with input := affineWord f ++ suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z}).store
      (SourceReplayAffine.fuel n)
      ({r with input := suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z,remaining := [],mode := [],sign := [],output := aEval f z :: r.output}).store :=
  SourceReplayAffine.block_exec r f z suffix
example {n : Nat} (F : Family n) (w : Point F.length) (z : Point n) (out : BitString) :
    Exec SourceReplayValue.block
      (SourceReplayValue.work (SourceMatrixEncoding.familyBits F) z ((SourceEncoding.pointCodec F.length).encode w) out)
      (SourceReplayValue.fuel n F.length) (SourceReplayValue.work [] z [] (weightedValue F w z :: out)) :=
  SourceReplayValue.block_exec F w z out
example (r : Registers) {n : Nat} (k : Fin (n + 1)) (bit : Bool) (z : Point n) :
    Exec (SourceReplayPoint.splice bit)
      ({r with input := (SourceEncoding.pointCodec n).encode z,remaining := List.replicate k.val true,excess := []}).store
      (SourceReplayPoint.spliceFuel k.val)
      ({r with input := [],remaining := [],excess := [],output := (SourceEncoding.pointCodec (n + 1)).encode (insert n k (bit,z))}).store :=
  SourceReplayPoint.splice_point r k bit z
example {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (v z : Point n) :
    Exec SourceReplayDecode.block (work [] [] (data F w k v z))
      (SourceReplayDecode.fuel n F.length k.val (value F w k z))
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (decode (markSource F w) k v z))
        (evaluated (data F w k v z) (value F w k z))) :=
  SourceReplayDecode.block_exec F w k v z
example (n rows pivot L : Nat) (bit : Bool) (hn : n ≤ L) (hm : rows ≤ L) (hp : pivot ≤ n) :
    SourceReplayDecode.fuel n rows pivot bit ≤ SourceReplayDecode.costPolynomial.eval L :=
  SourceReplayDecode.bounded_cost n rows pivot L bit hn hm hp
example {n : Nat} (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) (s : Saved) :
    Exec SourceReplayProject.block (work [] [] (SourceReplayProject.data k v x s))
      (SourceReplayProject.fuel n k.val (cut n k x).1)
      (work [] ((SourceEncoding.pointCodec n).encode (encode k v x)) (SourceReplayProject.data k v x s)) :=
  SourceReplayProject.block_exec k v x s
example (n pivot : Nat) (bit : Bool) (hp : pivot ≤ n) :
    SourceReplayProject.fuel n pivot bit ≤ 20 * n + 20 :=
  SourceReplayProject.fuel_bound n pivot bit hp

private def points : (n : Nat) → List (Point n)
  | 0 => [()]
  | n + 1 => (points n).flatMap (fun p => [(false,p),(true,p)])
private def constantPoint : (n : Nat) → Bool → Point n
  | 0, _ => ()
  | n + 1, b => (b,constantPoint n b)
private def affine : {n : Nat} → Point n → Bool → Affine n
  | 0, (), b => b
  | _ + 1, (a,p), b => (a,affine p b)
private def families (n : Nat) : List (Family n) :=
  let zero := affine (constantPoint n false) false
  let one := affine (constantPoint n false) true
  let parity := affine (constantPoint n true) false
  let opposite := affine (constantPoint n true) true
  [[],[⟨false,one,one⟩],[⟨true,zero,opposite⟩],
    [⟨false,parity,one⟩,⟨true,one,opposite⟩]]
private def savedFixture : Saved :=
  ⟨[true,false],[false,true,true],[true],[false],[true,false],[false,true],[true,false,true]⟩
private def same {n : Nat} (counter : IO.Ref Nat) (p : Program n) (start expected : Store n)
    (fuel : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (fuel + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": instruction bound did not halt"))
  for i in List.finRange n do
    if actual.store.get i != expected.get i then throw (IO.userError (label ++ ": complete store differs"))
  counter.modify (· + 1)

#eval (show IO Unit from do
  let count ← IO.mkRef 0
  for n in [0,1,2] do
    for coefficients in points n do
      for z in points n do
        for b in [false,true] do
          let f := affine coefficients b
          let suffix := [false,true,false]
          let r : Registers := ⟨[],[false],[],[true,false],[],[],[false,true],[],[true,false]⟩
          let before := {r with input := affineWord f ++ suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z}
          let after := {before with input := suffix,remaining := [],mode := [],sign := [],output := aEval f z :: r.output}
          same count (SourceReplayAffine.block.program 0 8) before.store after.store
            (SourceReplayAffine.fuel n) "Affine constant and preserved suffix"
  IO.println "REPLAY_PHASE: affine constants and preserved fields passed"
  let branches ← IO.mkRef (false,false)
  let decoder := SourceReplayDecode.block.program 0 8
  for n in [0,1,2] do
    for k in List.finRange (n + 1) do
      for z in points n do
        for v in [constantPoint n false,constantPoint n true] do
          for F in families (n + 1) do
            for w in points F.length do
              let s := data F w k v z
              if s.bit != [] then throw (IO.userError "Replay starts with a supplied missing bit")
              let bit := qEval (scalar (chartRows (markSource F w) k v)).2 z
              branches.modify (fun seen => if bit then (seen.1,true) else (true,seen.2))
              let out := (SourceEncoding.pointCodec (n + 1)).encode (decode (markSource F w) k v z)
              let cost := SourceReplayDecode.fuel n F.length k.val bit
              if cost > SourceReplayDecode.costPolynomial.eval (max n F.length) then
                throw (IO.userError "Replay step exceeded its proved bound")
              same count decoder (work [] [] s) (work [] out (evaluated s bit)) cost "Exact original decode"
  if (← branches.get) != (true,true) then throw (IO.userError "Both reconstruction branches were not covered")
  IO.println "REPLAY_PHASE: original quadratic decode, weights and every pivot passed"
  let projector := SourceReplayProject.block.program 0 8
  for n in [0,1,2,3] do
    for k in List.finRange (n + 1) do
      for x in points (n + 1) do
        for v in [constantPoint n false,constantPoint n true] do
          let s := SourceReplayProject.data k v x savedFixture
          let cost := SourceReplayProject.fuel n k.val (cut n k x).1
          if cost > 20 * n + 20 then throw (IO.userError "Projection exceeded its proved bound")
          same count projector (work [] [] s)
            (work [] ((SourceEncoding.pointCodec n).encode (encode k v x)) s) cost "Exact chart projection"
  let F : Family 1 := [⟨false,(false,true),(false,true)⟩]
  let w : Point F.length := (true,())
  let start := work [] [] (data F w 0 () ())
  let cost := SourceReplayDecode.fuel 0 F.length 0 true
  let early := BitRegister.run decoder cost ⟨.running 0,start⟩
  if early.control == .accepted then throw (IO.userError "Replay accepted before the exact final instruction")
  IO.println s!"REPLAY_REGRESSIONS_GREEN: {← count.get} executions")

run_cmd do
  let names := [
    ``SourceReplayAlgebra.tail_value,
    ``SourceReplayAlgebra.decode_direct,
    ``SourceReplayAlgebra.insert_split,
    ``SourceReplayAlgebra.xor_bytes,
    ``SourceReplayAlgebra.unchart_false,
    ``SourceReplayAlgebra.unchart_true,
    ``SourceReplayAffine.finish_exec,
    ``SourceReplayAffine.block_exec,
    ``SourceReplayAffine.fuel_mono,
    ``SourceReplayValue.core_exec,
    ``SourceReplayValue.readWeight_exec,
    ``SourceReplayValue.readOutput_exec,
    ``SourceReplayValue.absorb_exec,
    ``SourceReplayValue.row_exec,
    ``SourceReplayValue.loop_exec,
    ``SourceReplayValue.block_exec,
    ``SourceReplayValue.fuel_mono,
    ``SourceReplayPoint.splice_words,
    ``SourceReplayPoint.splice_point,
    ``SourceReplayPoint.xor_point,
    ``SourceReplayPoint.shear_point,
    ``SourceReplayPoint.shearFuel_bound,
    ``SourceReplayState.core_exec,
    ``SourceReplayState.weighted_exec,
    ``SourceReplayState.clean_exec,
    ``SourceReplayEvaluate.zeroPoint_exec,
    ``SourceReplayEvaluate.setup_exec,
    ``SourceReplayEvaluate.capture_exec,
    ``SourceReplayEvaluate.block_exec,
    ``SourceReplayDecode.insert_sheared,
    ``SourceReplayDecode.reconstruct_exec,
    ``SourceReplayDecode.block_exec,
    ``SourceReplayDecode.fuel_bound,
    ``SourceReplayDecode.costPolynomial_eval,
    ``SourceReplayDecode.bounded_cost,
    ``SourceReplayProject.encode_direct,
    ``SourceReplayProject.cutPoint_exec,
    ``SourceReplayProject.block_exec,
    ``SourceReplayProject.fuel_bound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayAlgebra.decode_direct
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDecode.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDecode.bounded_cost
#print axioms PNP.Concrete.ResidualReduction.SourceReplayProject.block_exec

end PNP.Concrete.ResidualReduction.SourceReplayRegression
