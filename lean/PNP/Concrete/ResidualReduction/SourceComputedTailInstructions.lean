import PNP.Concrete.ResidualReduction.SourceComputedTailNormals

/-! Complete typed coefficient-to-tail construction. Both branches allocate
their scratch, read actual coefficients, perform the selected arithmetic and
emit the reversible existing TailForm encoding. The exact coefficient checks
for accepting this candidate remain separate and mandatory. Counts here are
source instructions, not yet physical register-copy machine costs. -/

namespace PNP.Concrete.ResidualReduction.SourceComputedTailInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data emptySaved Data zero)
open PNP.Concrete.ResidualReduction.SourceComputedTailState
open PNP.Concrete.ResidualReduction.SourceComputedTailEncoding

def selected (x : Extra) (right : Bool) : BitString := if right then x.right else x.left
def prependSetup (right : Bool) : Block 19 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 3 (SourceComputedTailNormals.destination right))) (.action (.clear 8))
def prependPrepare : Block 19 := .seq (.action (.copy 3 8)) (.action (.copy 8 0))
def prepend (right : Bool) : Block 19 := .seq (prependSetup right) <|
  .seq (core ClauseQuery.reverseLoop) <| .seq prependPrepare <|
  .seq (core ClauseQuery.reverseLoop) (.action (.clear 0))

theorem prepend_exec (right : Bool) (out : BitString) (s : Data) (x : Extra) :
    Exec (prepend right) (full {work [] with output := out} emptySaved s x)
      (8 * (selected x right).length + 8)
      (full {work [] with output := selected x right ++ out} emptySaved s x) := by
  let word := selected x right
  let ready := {work out with excess := word}
  let reversed := {work out with output := word.reverse}
  let prepared := {work out with excess := word.reverse,output := out}
  let done := {work out with output := word ++ out}
  have setup : Exec (.seq (.action (.copy 0 8))
      (.seq (.action (.copy 3 (SourceComputedTailNormals.destination right))) (.action (.clear 8))))
      (full {work [] with output := out} emptySaved s x) 3 (full ready emptySaved s x) := by
    cases right <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have rev : Exec ClauseQuery.reverseLoop ready.store (4 * word.length + 1) reversed.store := by
    simpa only [ready,reversed,work,List.append_nil] using ClauseQuery.reverse_exec (work out) word
  have prepare : Exec (.seq (.action (.copy (3 : Fin 19) 8)) (.action (.copy 8 0)))
      (full reversed emptySaved s x) 2 (full prepared emptySaved s x) :=
    Exec.seq (.action _ _) (.action _ _)
  have forward : Exec ClauseQuery.reverseLoop prepared.store (4 * word.length + 1) done.store := by
    simpa only [prepared,done,work,List.length_reverse,List.reverse_reverse] using
      ClauseQuery.reverse_exec {work out with output := out} word.reverse
  have clear : Exec (.action (.clear (0 : Fin 19))) (full done emptySaved s x) 1
      (full {work [] with output := word ++ out} emptySaved s x) := .action _ _
  have cost : 8 * word.length + 8 = 3 + ((4 * word.length + 1) + (2 + ((4 * word.length + 1) + 1))) := by omega
  have combined := Exec.seq setup (Exec.seq (core_exec rev emptySaved s x)
    (Exec.seq prepare (Exec.seq (core_exec forward emptySaved s x) clear)))
  simpa only [prepend,prependSetup,prependPrepare,word,cost] using combined

def serialize : Block 19 := .seq (prepend true) <| .seq (prepend false) (.action (.push 8 true))
def serializeFuel (n : Nat) : Nat := 16 * n + 33

theorem serialize_exec {n : Nat} (a b u : Affine n) (k : Fin (n + 1)) (s : Data) :
    Exec serialize (full {work [] with output := affineWord u} emptySaved s
      (extras k (affineWord a) (affineWord b))) (serializeFuel n)
      (full {work [] with output := (codec n).encode (.plane a b u)} emptySaved s
        (extras k (affineWord a) (affineWord b))) := by
  let x := extras k (affineWord a) (affineWord b)
  have right := prepend_exec true (affineWord u) s x
  have left := prepend_exec false (affineWord b ++ affineWord u) s x
  have tag : Exec (.action (.push (8 : Fin 19) true))
      (full {work [] with output := affineWord a ++ (affineWord b ++ affineWord u)} emptySaved s x) 1
      (full {work [] with output := (codec n).encode (.plane a b u)} emptySaved s x) := by
    rw [plane_bytes]
    exact .action _ _
  have cost : serializeFuel n = (8 * (n + 1) + 8) + ((8 * (n + 1) + 8) + 1) := by
    unfold serializeFuel
    omega
  simpa only [serialize,cost,selected,x,extras,↓reduceIte,Bool.false_eq_true,affineWord_length] using
    Exec.seq right (Exec.seq left tag)

def resultAccumulator {n : Nat} (q : Quadratic n) (k : Fin (n + 1)) :
    Option (Affine (n + 1) × Affine (n + 1)) → Quadratic n
  | none => q
  | some (a,b) => qAdd q (qProduct (tailNormal k a) (tailNormal k b))
def resultExtra {n : Nat} (k : Fin (n + 1)) :
    Option (Affine (n + 1) × Affine (n + 1)) → Extra
  | none => extras k [] []
  | some (a,b) => extras k (affineWord (tailNormal k a)) (affineWord (tailNormal k b))
def finished {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Store 19 :=
  full {work [] with output := (codec n).encode (computed q k normals)}
    emptySaved (data [] (resultAccumulator q k normals)) (resultExtra k normals)

def affine : Block 19 := .seq (scalar SourcePlaneRemainderInstructions.loadPolynomial) <|
  .seq (scalar SourcePlaneRemainderInstructions.extract) (.action (.push 8 false))
def affineFuel (n : Nat) : Nat := SourcePlaneRemainderInstructions.loadFuel n +
  ((2 + SourceQuadraticDiagonal.forwardFuel n) + 1)

theorem affine_exec {n : Nat} (q : Quadratic n) (k : Fin (n + 1)) (savedStream : BitString) :
    Exec affine (full (work (SourceQuadraticEncoding.word q)) emptySaved (data savedStream (zero n))
      (extras k [] [])) (affineFuel n) (finished q k none) := by
  let x := extras k [] []
  have load := scalar_exec (SourcePlaneRemainderInstructions.load_exec q (zero n) [] savedStream) x
  have extract := scalar_exec (SourcePlaneRemainderInstructions.extract_exec q) x
  have tag : Exec (.action (.push (8 : Fin 19) false))
      (full {work [] with output := affineWord (affinePart q)} emptySaved (data [] q) x) 1
      (finished q k none) := .action _ _
  simpa only [affine,affineFuel,List.append_nil,full,x] using
    Exec.seq load (Exec.seq extract tag)

def prepareProduct : Block 19 := .seq (.action (.copy 0 17)) <|
  .seq (.action (.copy 5 18)) (.action (.copy 1 12))
def plane : Block 19 := .seq SourceComputedTailNormals.pair <|
  .seq (scalar SourcePlaneRemainderInstructions.loadPolynomial) <| .seq prepareProduct <|
  .seq (product SourceQuadraticProduct.forwardBlock) <| .seq (scalar SourceScalarRow.accumulate) <|
  .seq (scalar SourcePlaneRemainderInstructions.extract) serialize
def planeFuel (n pivot : Nat) : Nat := SourceComputedTailNormals.pairFuel n pivot +
  (SourcePlaneRemainderInstructions.loadFuel n + (3 + (SourceQuadraticProduct.forwardFuel n +
    (SourceScalarRow.addFuel n + ((2 + SourceQuadraticDiagonal.forwardFuel n) + serializeFuel n)))))

theorem plane_exec {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (a b : Affine (n + 1)) (savedStream : BitString) :
    Exec plane
      (full (work (affineWord a ++ (affineWord b ++ SourceQuadraticEncoding.word q)))
        emptySaved (data savedStream (zero n)) (extras k [] []))
      (planeFuel n k.val) (finished q k (some (a,b))) := by
  let alpha := tailNormal k a
  let beta := tailNormal k b
  let x := extras k (affineWord alpha) (affineWord beta)
  have normals := SourceComputedTailNormals.pair_exec a b k (zero n)
    (SourceQuadraticEncoding.word q) savedStream [] []
  have load : Exec (scalar SourcePlaneRemainderInstructions.loadPolynomial)
      (full (work (SourceQuadraticEncoding.word q)) emptySaved
        (data (SourceQuadraticEncoding.word q) (zero n)) x)
      (SourcePlaneRemainderInstructions.loadFuel n) (state [] q x) := by
    simpa only [List.append_nil,full,state,SourceScalarState.state] using
      scalar_exec (SourcePlaneRemainderInstructions.load_exec q (zero n) []
        (SourceQuadraticEncoding.word q)) x
  have prep : Exec prepareProduct (state [] q x) 3
      (full (SourceQuadraticProduct.ready (work []) alpha beta) emptySaved (data [] q) x) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  obtain ⟨after,mul⟩ := SourceQuadraticProduct.forward_exec (work []) emptySaved alpha beta
  have add := scalar_exec (SourceScalarRow.accumulate_exec (qProduct alpha beta) q after []) x
  have extract := scalar_exec (SourcePlaneRemainderInstructions.extract_exec (qAdd q (qProduct alpha beta))) x
  have bytes := serialize_exec alpha beta (planeRemainder q alpha beta) k (data [] (qAdd q (qProduct alpha beta)))
  simpa only [plane,planeFuel,full,state,x,alpha,beta,finished,computed,resultExtra,
    resultAccumulator,planeRemainder,List.append_nil,work] using Exec.seq normals
    (Exec.seq load (Exec.seq prep (Exec.seq (product_exec mul (data [] q) x)
      (Exec.seq add (Exec.seq extract bytes)))))

def dispatch : Block 19 := .branch 0 .skip
  (.seq (.action (.pop 0)) affine) (.seq (.action (.pop 0)) plane)
def block : Block 19 := .seq (scalar SourceScalarInitialization.block) dispatch
def fuel (n pivot : Nat) (isPlane : Bool) : Nat :=
  SourceScalarInitialization.fuel n + (2 + if isPlane then planeFuel n pivot else affineFuel n)

theorem block_exec {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (initial (packet q normals) k) (fuel n k.val normals.isSome) (finished q k normals) := by
  let x := extras k [] []
  have start := scalar_exec (SourceScalarInitialization.block_exec n (packet q normals)) x
  cases normals with
  | none =>
    have pop : Exec (.action (.pop (0 : Fin 19)))
        (state (packet q none) (zero n) x) 1
        (full (work (SourceQuadraticEncoding.word q)) emptySaved (data (packet q none) (zero n)) x) := .action _ _
    have branch : Exec dispatch (state (packet q none) (zero n) x)
        (1 + (1 + affineFuel n)) (finished q k none) :=
      Exec.zero (source := (0 : Fin 19)) rfl (Exec.seq pop (affine_exec q k (packet q none)))
    have cost : fuel n k.val false = SourceScalarInitialization.fuel n + (1 + (1 + affineFuel n)) := by
      simp only [fuel,Bool.false_eq_true,↓reduceIte]
      omega
    simpa only [block,SourceComputedTailState.initial,state,full,x,Option.isSome,cost] using Exec.seq start branch
  | some p =>
    rcases p with ⟨a,b⟩
    have pop : Exec (.action (.pop (0 : Fin 19)))
        (state (packet q (some (a,b))) (zero n) x) 1
        (full (work (affineWord a ++ (affineWord b ++ SourceQuadraticEncoding.word q)))
          emptySaved (data (packet q (some (a,b))) (zero n)) x) := by
      rw [packet_some]
      exact .action _ _
    have branch : Exec dispatch (state (packet q (some (a,b))) (zero n) x)
        (1 + (1 + planeFuel n k.val)) (finished q k (some (a,b))) := by
      apply Exec.one (source := (0 : Fin 19))
      · rw [packet_some]
        rfl
      · exact Exec.seq pop (plane_exec q k a b (packet q (some (a,b))))
    have cost : fuel n k.val true = SourceScalarInitialization.fuel n + (1 + (1 + planeFuel n k.val)) := by
      simp only [fuel,↓reduceIte]
      omega
    simpa only [block,SourceComputedTailState.initial,state,full,x,Option.isSome,cost] using Exec.seq start branch

theorem affineFuel_exact (n pivot : Nat) : fuel n pivot false = 18 * quadraticBits n + 12 * n + 28 := by
  simp only [fuel,affineFuel,SourceScalarInitialization.fuel_exact,
    SourcePlaneRemainderInstructions.loadFuel,SourceQuadraticDiagonal.forwardFuel_exact,
    Bool.false_eq_true,↓reduceIte]
  omega
theorem planeFuel_exact (n pivot : Nat) :
    fuel n pivot true = 40 * quadraticBits n + 74 * n + 18 * pivot + 166 := by
  simp only [fuel,planeFuel,SourceComputedTailNormals.pairFuel,SourceComputedTailNormals.fuel,
    SourceScalarInitialization.fuel_exact,SourcePlaneRemainderInstructions.loadFuel,
    SourcePlaneRemainderInstructions.productFuel_exact,SourceScalarRow.addFuel,
    SourceQuadraticDiagonal.forwardFuel_exact,serializeFuel,↓reduceIte]
  omega
theorem fuel_source_bound {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    fuel n k.val normals.isSome ≤ 46 * (packet q normals).length := by
  have dim := SourceQuadraticDiagonalAlgebra.dimension_bound n
  have pivot := k.isLt
  cases normals with
  | none =>
    simp only [Option.isSome,affineFuel_exact,packet_none_length]
    omega
  | some p =>
    rcases p with ⟨a,b⟩
    simp only [Option.isSome,planeFuel_exact,packet_some_length]
    omega

theorem output_get {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (finished q k normals).get 8 = (codec n).encode (computed q k normals) := rfl
theorem output_decode {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (codec n).decode ((finished q k normals).get 8) = some (computed q k normals) := roundtrip _
theorem output_bound {n : Nat} (q : Quadratic n) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    ((finished q k normals).get 8).length ≤ 3 * (n + 1) + 1 := bytes_bound _
theorem output_existing {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (c : Fin (n + 1) × Point n) (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (codec n).decode ((finished (FactoredContraction.scalar (chartRows (markSource F w) c.1 c.2)).2 c.1 normals).get 8) =
      some (computedTail F w c normals) := by
  rw [output_decode,computed_eq]

end PNP.Concrete.ResidualReduction.SourceComputedTailInstructions
