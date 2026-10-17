import PNP.Concrete.ResidualReduction.SourceMenuRow

/-! A single finite program constructs the full candidate stream from an
arbitrary encoded source family. It consumes the codec's unary length header
and traverses the fixed-width source rows. Reversed candidate record order
matches the reference right-fold insertion. No menu or validity certificate
is supplied. Raw-input validation and sorting/dispatch remain open. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuRow

def bytes {n : Nat} (F : Family n) : BitString :=
  matrixBits (F.flatMap rowNormals).reverse

theorem matrixBits_append {n : Nat} (xs ys : List (Affine n)) :
    matrixBits (xs ++ ys) = matrixBits xs ++ matrixBits ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append, matrixBits, ih, List.append_assoc]

theorem bytes_nil (n : Nat) : bytes ([] : Family n) = [] := rfl
theorem bytes_cons {n : Nat} (r : Row n) (F : Family n) :
    bytes (r :: F) = bytes F ++ matrixBits (rowNormals r).reverse := by
  simp only [bytes, List.flatMap_cons, List.reverse_append, matrixBits_append]

def headerBody : Block 9 := .branch 0 (.action (.clear 6))
  (.seq (.action (.pop 0)) (.action (.clear 6))) (.action (.pop 0))
def headerLoop : Block 9 := .loop 6 headerBody
def header : Block 9 := .seq (.action (.push 6 true)) headerLoop

theorem headerLoop_exec (r : Registers) (m : Nat) (stream : BitString) :
    Exec headerLoop
      ({r with input := List.replicate m true ++ (false :: stream), active := [true]}).store
      (3 * m + 5) ({r with input := stream, active := []}).store := by
  induction m with
  | zero =>
    have bodyDone : Exec headerBody
        ({r with input := false :: stream, active := [true]}).store 3
        ({r with input := stream, active := []}).store :=
      Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
    have stopped : Exec headerLoop ({r with input := stream, active := []}).store 1
        ({r with input := stream, active := []}).store := Exec.loopStop rfl
    exact Exec.loopStep (source := (6 : Fin 9)) rfl bodyDone stopped
  | succ m ih =>
    have bodyDone : Exec headerBody
        ({r with input := true :: (List.replicate m true ++ (false :: stream)), active := [true]}).store 2
        ({r with input := List.replicate m true ++ (false :: stream), active := [true]}).store :=
      Exec.one rfl (.action _ _)
    have checked := Exec.loopStep (source := (6 : Fin 9)) rfl bodyDone ih
    have count : 3 * (m + 1) + 5 = 1 + (2 + (3 * m + 5)) := by omega
    simpa only [headerLoop, List.replicate_succ, List.cons_append, count] using checked

theorem header_exec (n m : Nat) (stream accumulator : BitString) :
    Exec header (SourceMenuRowInput.initial n (natural m ++ stream) accumulator).store
      (3 * m + 6) (SourceMenuRowInput.initial n stream accumulator).store := by
  let base := SourceMenuRowInput.initial n stream accumulator
  have first : Exec (.action (.push (6 : Fin 9) true))
      (SourceMenuRowInput.initial n (natural m ++ stream) accumulator).store 1
      ({base with input := List.replicate m true ++ (false :: stream), active := [true]}).store := by
    simp only [natural, List.append_assoc, List.singleton_append]
    exact Exec.action _ _
  have checked := Exec.seq first (headerLoop_exec base m stream)
  have count : 3 * m + 6 = 1 + (3 * m + 5) := by omega
  simpa only [header, count, base, SourceMenuRowInput.initial] using checked

def rows {n : Nat} (F : Family n) : BitString := encodeSeq (SourceEncoding.rowCodec n).encode F
def rowInitial {n : Nat} (F : Family n) (accumulator : BitString) (s : Saved) : Store 12 :=
  full (SourceMenuRowInput.initial n (rows F) accumulator) s
def initial {n : Nat} (F : Family n) (accumulator : BitString) (s : Saved) : Store 12 :=
  full (SourceMenuRowInput.initial n ((SourceEncoding.familyCodec n).encode F) accumulator) s
def terminal (n : Nat) (output : BitString) (s : Saved) : Store 12 :=
  full (SourceMenuRowInput.initial n [] output) s
def rowLoop : Block 12 := .loop 0 SourceMenuRow.block
def block : Block 12 := .seq (Frame.block 3 header) rowLoop

theorem rowLoop_exec {n : Nat} (F : Family n) (accumulator : BitString) (s : Saved) :
    ∃ used last, Exec rowLoop (rowInitial F accumulator s) used
      (terminal n (bytes F ++ accumulator) last) ∧
      used ≤ (43 * n + 50) * F.length + 1 := by
  induction F generalizing accumulator s with
  | nil =>
    refine ⟨1, s, ?_, ?_⟩
    · exact Exec.loopStop rfl
    · simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons r F ih =>
    let added := matrixBits (rowNormals r).reverse ++ accumulator
    let saved := SourceMenuRow.saved n (rows F) accumulator
    obtain ⟨used, last, rest, bound⟩ := ih added saved
    have row := SourceMenuRow.block_exec r (rows F) accumulator s
    have present : (rowInitial (r :: F) accumulator s).get 0 =
        r.selected :: (MatrixInstructions.affineWord r.left ++
          (MatrixInstructions.affineWord r.right ++ rows F)) := by
      change (SourceEncoding.rowCodec n).encode r ++ rows F = _
      rw [SourceMenuRowInput.row_bytes, List.cons_append, List.append_assoc]
    have checked := Exec.loopStep (source := (0 : Fin 12)) present row rest
    refine ⟨1 + (SourceMenuRow.cost r accumulator + used), last, ?_, ?_⟩
    · simpa only [rowLoop, bytes_cons, added, List.append_assoc] using checked
    · have rowBound := SourceMenuRow.cost_bound r accumulator
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem block_exec {n : Nat} (F : Family n) (accumulator : BitString) (s : Saved) :
    ∃ used last, Exec block (initial F accumulator s) used
      (terminal n (bytes F ++ accumulator) last) ∧
      used ≤ (43 * n + 53) * F.length + 7 := by
  have prepared := Frame.execution (header_exec n F.length (rows F) accumulator) s.store
  obtain ⟨used, last, checked, bound⟩ := rowLoop_exec F accumulator s
  refine ⟨(3 * F.length + 6) + used, last, Exec.seq prepared checked, ?_⟩
  simp only [Nat.add_mul] at bound ⊢
  omega

theorem candidate_count {n : Nat} (F : Family n) :
    (F.flatMap rowNormals).length ≤ 3 * F.length := by
  induction F with
  | nil => exact Nat.le_refl 0
  | cons r F ih =>
    have row := rowNormals_length_le r
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem bytes_bound {n : Nat} (F : Family n) :
    (bytes F).length ≤ (n + 1) * (3 * F.length) := by
  have count := Nat.mul_le_mul_left (n + 1) (candidate_count F)
  simpa only [bytes, matrixBits_length, List.length_reverse] using count

/-- Left-to-right insertion on reversed records is exactly the reference
right fold, not a different tie/order convention. -/
theorem reversed_fold {n : Nat} (us : List (Affine n)) :
    us.reverse.foldl (fun menu a => insertNormal a menu) [] = sortedNormals us := by
  induction us with
  | nil => rfl
  | cons a us ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih, sortedNormals]

theorem source_menu_link {n : Nat} (F : Family n) :
    (F.flatMap rowNormals).reverse.foldl (fun menu a => insertNormal a menu) [] = sourceMenu F :=
  reversed_fold _

def program : Program 12 := block.program 0 7

theorem program_run {n : Nat} (F : Family n) (accumulator : BitString) (s : Saved) :
    ∃ used last,
      BitRegister.run program (used + 1) ⟨.running 0, initial F accumulator s⟩ =
        ⟨.accepted, terminal n (bytes F ++ accumulator) last⟩ ∧
      (terminal n (bytes F ++ accumulator) last).get 7 = bytes F ++ accumulator ∧
      used + 1 ≤ (43 * n + 53) * F.length + 8 := by
  obtain ⟨used, last, checked, bound⟩ := block_exec F accumulator s
  exact ⟨used, last, checked.program_run 0 7, rfl, by omega⟩

end PNP.Concrete.ResidualReduction.SourceMenuFamily
