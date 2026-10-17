import PNP.Concrete.ResidualReduction.SourceMenuScan

/-! Literal candidate emission from the computed coefficient scan. The three
records are prepended in reverse record order for exact right-fold insertion.
The whole source parser, sorted insertion and outer selector remain separate
obligations; this is not a complete contraction or solver runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuCandidates
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMenuBytes
open PNP.Concrete.ResidualReduction.SourceMenuScan

def occurrence (r : Registers) : Occurrence.Registers :=
  ⟨r.left, r.right, r.leftAccum, r.rightAccum, r.xorAccum,
    [r.leftFlag], [r.rightFlag], [r.xorFlag], r.output⟩
def reversed (r : Registers) : Registers :=
  {r with rightAccum := [], output := r.rightAccum.reverse ++ r.output}

theorem reverse_exec (r : Registers) :
    Exec ClauseQuery.reverseLoop r.store (4 * r.rightAccum.length + 1) (reversed r).store :=
  ClauseQuery.reverse_exec (occurrence r) r.rightAccum

def prepareLeft : Block 9 := .seq (.action (.copy 0 3)) <|
  .seq (.action (.copy 3 2)) (.action (.push 8 false))
def leftReady (r : Registers) : Registers :=
  {r with left := r.rightAccum, rightAccum := r.leftAccum, output := false :: r.output}
theorem prepareLeft_exec (r : Registers) :
    Exec prepareLeft r.store 3 (leftReady r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def prepareRight : Block 9 := .seq (.action (.copy 3 0)) (.action (.push 8 false))
def rightReady (r : Registers) : Registers :=
  {r with rightAccum := r.left, output := false :: r.output}
theorem prepareRight_exec (r : Registers) :
    Exec prepareRight r.store 2 (rightReady r).store := Exec.seq (.action _ _) (.action _ _)

def prepareXor : Block 9 := .seq (.action (.copy 3 4)) (.action (.push 8 false))
def xorReady (r : Registers) : Registers :=
  {r with rightAccum := r.xorAccum, output := false :: r.output}
theorem prepareXor_exec (r : Registers) :
    Exec prepareXor r.store 2 (xorReady r).store := Exec.seq (.action _ _) (.action _ _)

def emit : Block 9 := .seq prepareLeft <| .seq ClauseQuery.reverseLoop <|
  .seq prepareRight <| .seq ClauseQuery.reverseLoop <|
  .seq prepareXor ClauseQuery.reverseLoop
def emitFuel (r : Registers) : Nat :=
  4 * (r.leftAccum.length + r.rightAccum.length + r.xorAccum.length) + 10
def emitted (r : Registers) : Registers :=
  {r with
    left := r.rightAccum, rightAccum := [],
    output := r.xorAccum.reverse ++ (false ::
      (r.rightAccum.reverse ++ (false :: (r.leftAccum.reverse ++ (false :: r.output)))))}

theorem emit_exec (r : Registers) : Exec emit r.store (emitFuel r) (emitted r).store := by
  have first := prepareLeft_exec r
  have second := reverse_exec (leftReady r)
  have third := prepareRight_exec (reversed (leftReady r))
  have fourth := reverse_exec (rightReady (reversed (leftReady r)))
  have fifth := prepareXor_exec (reversed (rightReady (reversed (leftReady r))))
  have sixth := reverse_exec (xorReady (reversed (rightReady (reversed (leftReady r)))))
  have checked := Exec.seq first
    (Exec.seq second (Exec.seq third (Exec.seq fourth (Exec.seq fifth sixth))))
  have count : emitFuel r = 3 + ((4 * r.leftAccum.length + 1) +
      (2 + ((4 * r.rightAccum.length + 1) + (2 + (4 * r.xorAccum.length + 1))))) := by
    unfold emitFuel
    omega
  simpa only [emit, count, leftReady, rightReady, xorReady, reversed, emitted] using checked

def gate : Block 9 := .branch 5 .skip .skip
  (.branch 6 .skip .skip (.branch 7 .skip .skip emit))
def gateFuel (r : Registers) : Nat :=
  if r.leftFlag then
    if r.rightFlag then
      if r.xorFlag then 1 + (1 + (1 + emitFuel r)) else 4
    else 3
  else 2
def gateResult (r : Registers) : Registers :=
  if r.leftFlag then
    if r.rightFlag then
      if r.xorFlag then emitted r else r
    else r
  else r

theorem gate_exec (r : Registers) :
    Exec gate r.store (gateFuel r) (gateResult r).store := by
  cases r with
  | mk xs ys left right sum lf rf xf output =>
    cases lf <;> cases rf <;> cases xf
    all_goals simp only [gateFuel, gateResult, ↓reduceIte]
    all_goals first
      | exact Exec.zero rfl (Exec.skip _)
      | exact Exec.one rfl (Exec.zero rfl (Exec.skip _))
      | exact Exec.one rfl (Exec.one rfl (Exec.zero rfl (Exec.skip _)))
      | exact Exec.one (source := (5 : Fin 9)) rfl
          (Exec.one (source := (6 : Fin 9)) rfl (Exec.one (source := (7 : Fin 9)) rfl
          (emit_exec ⟨xs, ys, left, right, sum, true, true, true, output⟩)))

theorem gateFuel_bound (r : Registers) : gateFuel r ≤ emitFuel r + 3 := by
  unfold gateFuel emitFuel
  split
  · split
    · split <;> omega
    · omega
  · omega

def block : Block 9 := .seq SourceMenuScan.loop gate
def cost (xs ys output : BitString) : Nat :=
  SourceMenuScan.fuel xs ys + gateFuel (SourceMenuScan.result (start xs ys output) xs ys)
def result (xs ys output : BitString) : Registers :=
  gateResult (SourceMenuScan.result (start xs ys output) xs ys)

theorem block_exec (xs ys output : BitString) (sameLength : xs.length = ys.length) :
    Exec block (start xs ys output).store (cost xs ys output) (result xs ys output).store :=
  Exec.seq (SourceMenuScan.loop_exec (start xs ys output) xs ys sameLength)
    (gate_exec (SourceMenuScan.result (start xs ys output) xs ys))

theorem result_output (xs ys output : BitString) :
    (result xs ys output).store.get 8 =
      (if eligible xs ys then
        (List.zipWith Bool.xor xs ys ++ [false]) ++
          ((ys ++ [false]) ++ (xs ++ [false]))
      else []) ++ output := by
  change (result xs ys output).output = _
  cases hx : nonzero xs <;> cases hy : nonzero ys <;>
    cases hz : nonzero (List.zipWith Bool.xor xs ys)
  all_goals simp only [result, gateResult, SourceMenuScan.result, start,
    emitted, eligible, hx, hy, hz, Bool.false_or,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
    List.append_nil, List.reverse_reverse, List.nil_append, List.append_assoc,
    List.cons_append]

theorem cost_bound (xs ys output : BitString) (sameLength : xs.length = ys.length) :
    cost xs ys output ≤ 25 * xs.length + 14 := by
  have scan := SourceMenuScan.fuel_bound xs ys
  have emission := gateFuel_bound (SourceMenuScan.result (start xs ys output) xs ys)
  have zipLength : (List.zipWith Bool.xor xs ys).length = xs.length := by
    rw [List.length_zipWith, ← sameLength, Nat.min_self]
  have emissionCost : emitFuel (SourceMenuScan.result (start xs ys output) xs ys) =
      12 * xs.length + 10 := by
    simp only [emitFuel, SourceMenuScan.result, start, List.length_append, List.length_reverse,
      List.length_nil, Nat.add_zero, zipLength, ← sameLength]
    omega
  rw [emissionCost] at emission
  unfold cost
  omega

theorem row_output {n : Nat} (r : Row n) (output : BitString) :
    (result (normalBits r.left) (normalBits r.right) output).store.get 8 =
      matrixBits (rowNormals r).reverse ++ output := by
  rw [result_output, reversed_row_bytes]

theorem row_exec {n : Nat} (r : Row n) (output : BitString) :
    Exec block (start (normalBits r.left) (normalBits r.right) output).store
      (cost (normalBits r.left) (normalBits r.right) output)
      (result (normalBits r.left) (normalBits r.right) output).store :=
  block_exec _ _ _ ((normalBits_length r.left).trans (normalBits_length r.right).symm)

theorem row_cost_bound {n : Nat} (r : Row n) (output : BitString) :
    cost (normalBits r.left) (normalBits r.right) output ≤ 25 * n + 14 := by
  have checked := cost_bound (normalBits r.left) (normalBits r.right) output
    ((normalBits_length r.left).trans (normalBits_length r.right).symm)
  simpa only [normalBits_length] using checked

def program : Program 9 := block.program 0 8

theorem program_run {n : Nat} (r : Row n) (output : BitString) :
    BitRegister.run program (cost (normalBits r.left) (normalBits r.right) output + 1)
      ⟨.running 0, (start (normalBits r.left) (normalBits r.right) output).store⟩ =
      ⟨.accepted, (result (normalBits r.left) (normalBits r.right) output).store⟩ :=
  (row_exec r output).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceMenuCandidates
