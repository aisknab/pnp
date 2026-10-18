import PNP.Concrete.ResidualReduction.SourceCandidateChoiceAlgebra

/-! Literal fixed-width candidate decision. Reading the eight computed corner
bits selects a fixed branch of the finite instruction tree. No matrix query,
search oracle or supplied acceptance certificate is a runtime primitive. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateChoice
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions (readInput readInput_exec)

def emit : BitString → Block 9
  | [] => .skip
  | bit :: rest => .seq (emit rest) (.action (.push 8 bit))
theorem emit_exec (r : Registers) (bits : BitString) :
    Exec (emit bits) r.store (bits.length + 1) ({r with output := bits ++ r.output}).store := by
  induction bits with
  | nil => exact Exec.skip _
  | cons bit bits ih =>
    have final : Exec (.action (.push (8 : Fin 9) bit)) ({r with output := bits ++ r.output}).store 1
        ({r with output := bit :: (bits ++ r.output)}).store := .action _ _
    simpa only [emit, List.length_cons, Nat.add_assoc, List.cons_append] using Exec.seq ih final

abbrev TruthBlock := Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Block 9
def readEight (next : TruthBlock) : Block 9 :=
  readInput fun a => readInput fun b => readInput fun c => readInput fun d =>
    readInput fun e => readInput fun f => readInput fun g => readInput fun h => next a b c d e f g h

theorem readEight_exec (r after : Registers) (a b c d e f g h : Bool)
    (next : TruthBlock) (used : Nat) (checked : Exec (next a b c d e f g h) r.store used after.store) :
    Exec (readEight next) ({r with input := a :: b :: c :: d :: e :: f :: g :: h :: r.input}).store
      (16 + used) after.store := by
  have h8 := readInput_exec r h (next a b c d e f g) used after checked
  have h7 := readInput_exec {r with input := h :: r.input} g
    (fun g => readInput (next a b c d e f g)) (2 + used) after h8
  have h6 := readInput_exec {r with input := g :: h :: r.input} f
    (fun f => readInput fun g => readInput (next a b c d e f g)) (2 + (2 + used)) after h7
  have h5 := readInput_exec {r with input := f :: g :: h :: r.input} e
    (fun e => readInput fun f => readInput fun g => readInput (next a b c d e f g))
    (2 + (2 + (2 + used))) after h6
  have h4 := readInput_exec {r with input := e :: f :: g :: h :: r.input} d
    (fun d => readInput fun e => readInput fun f => readInput fun g => readInput (next a b c d e f g))
    (2 + (2 + (2 + (2 + used)))) after h5
  have h3 := readInput_exec {r with input := d :: e :: f :: g :: h :: r.input} c
    (fun c => readInput fun d => readInput fun e => readInput fun f => readInput fun g => readInput (next a b c d e f g))
    (2 + (2 + (2 + (2 + (2 + used))))) after h4
  have h2 := readInput_exec {r with input := c :: d :: e :: f :: g :: h :: r.input} b
    (fun b => readInput fun c => readInput fun d => readInput fun e => readInput fun f => readInput fun g => readInput (next a b c d e f g))
    (2 + (2 + (2 + (2 + (2 + (2 + used)))))) after h3
  have h1 := readInput_exec {r with input := b :: c :: d :: e :: f :: g :: h :: r.input} a
    (fun a => readInput fun b => readInput fun c => readInput fun d => readInput fun e => readInput fun f => readInput fun g => readInput (next a b c d e f g))
    (2 + (2 + (2 + (2 + (2 + (2 + (2 + used))))))) after h2
  simpa only [readEight, ← Nat.add_assoc] using h1

def inputBits (A C : Corners) : BitString :=
  [A.firstFirst, A.firstSecond, A.secondFirst, A.secondSecond,
   C.firstFirst, C.firstSecond, C.secondFirst, C.secondSecond]
def block : Block 9 := readEight fun a b c d e f g h => emit (outputBits (choose ⟨a,b,c,d⟩ ⟨e,f,g,h⟩))
def fuel (A C : Corners) : Nat := 16 + ((outputBits (choose A C)).length + 1)

theorem block_exec (r : Registers) (A C : Corners) :
    Exec block ({r with input := inputBits A C ++ r.input}).store (fuel A C)
      ({r with output := outputBits (choose A C) ++ r.output}).store := by
  cases A with
  | mk a b c d =>
    cases C with
    | mk e f g h =>
      exact readEight_exec r _ a b c d e f g h _ _
        (emit_exec r (outputBits (choose ⟨a,b,c,d⟩ ⟨e,f,g,h⟩)))

theorem fuel_bound (A C : Corners) : fuel A C ≤ 22 := by
  have bound := output_length_bound (choose A C)
  unfold fuel
  omega

def program : Program 9 := block.program 0 8
theorem program_run (r : Registers) (A C : Corners) :
    BitRegister.run program (fuel A C + 1) ⟨.running 0, ({r with input := inputBits A C ++ r.input}).store⟩ =
      ⟨.accepted, ({r with output := outputBits (choose A C) ++ r.output}).store⟩ :=
  (block_exec r A C).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceCandidateChoice
