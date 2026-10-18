import PNP.Concrete.ResidualReduction.SourceQuadraticHead
import PNP.Concrete.NormalizerRegisterFrame

/-! Literal all-dimension affine-factor multiplication. Each iteration saves
the unconsumed factor tails, computes one exact triangular head, and restores
those tails for the next coordinate. The final constant is read explicitly.
The execution theorem counts all reads, copies, guards and emitted bits. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticProduct
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

structure Saved where
  left : BitString
  right : BitString
def Saved.store (s : Saved) : Store 2 := .cons s.left (.cons s.right .nil)
def full (r : Registers) (s : Saved) : Store 11 := Frame.join r.store s.store

def heads : {n : Nat} → Affine n → Affine n → BitString
  | 0,_,_ => []
  | _ + 1,(d,f),(e,g) => affineWord (SourceQuadraticHead.head d e f g) ++ heads f g

theorem word_split {n : Nat} (f g : Affine n) :
    SourceQuadraticEncoding.word (qProduct f g) = heads f g ++ [aConstant f && aConstant g] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨d,f⟩
    rcases g with ⟨e,g⟩
    rw [SourceQuadraticHead.product_word,ih]
    exact (List.append_assoc _ _ _).symm

def readLeft (next : Bool → Block 11) : Block 11 :=
  .branch 0 .skip (.seq (.action (.pop 0)) (next false))
    (.seq (.action (.pop 0)) (next true))
def readRight (next : Bool → Block 11) : Block 11 :=
  .branch 5 .skip (.seq (.action (.pop 5)) (next false))
    (.seq (.action (.pop 5)) (next true))

theorem readLeft_exec (r : Registers) (s : Saved) (b : Bool) (next : Bool → Block 11)
    (fuel : Nat) (after : Store 11) (checked : Exec (next b) (full r s) fuel after) :
    Exec (readLeft next) (full {r with input := b :: r.input} s) (2 + fuel) after := by
  have popped : Exec (.action (.pop (0 : Fin 11)))
      (full {r with input := b :: r.input} s) 1 (full r s) := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (0 : Fin 11)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (0 : Fin 11)) rfl (Exec.seq popped checked)

theorem readRight_exec (r : Registers) (s : Saved) (b : Bool) (next : Bool → Block 11)
    (fuel : Nat) (after : Store 11) (checked : Exec (next b) (full r s) fuel after) :
    Exec (readRight next) (full {r with mode := b :: r.mode} s) (2 + fuel) after := by
  have popped : Exec (.action (.pop (5 : Fin 11)))
      (full {r with mode := b :: r.mode} s) 1 (full r s) := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (5 : Fin 11)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (5 : Fin 11)) rfl (Exec.seq popped checked)

def prepare : Block 11 := .seq (.action (.pop 1)) <|
  .seq (.action (.copy 9 0)) <| .seq (.action (.copy 10 5)) (.action (.copy 2 1))
def restore : Block 11 := .seq (.action (.copy 0 9)) (.action (.copy 5 10))
def afterLeads (d e : Bool) : Block 11 := .seq prepare <|
  .seq (Frame.block 2 (SourceQuadraticHead.block d e)) restore
def body : Block 11 := readLeft fun d => readRight fun e => afterLeads d e

def ready (r : Registers) {n : Nat} (f g : Affine n) : Registers :=
  {r with input := affineWord f,mode := affineWord g,target := List.replicate n true,remaining := []}
def doneLoop (r : Registers) {n : Nat} (f g : Affine n) : Registers :=
  {r with input := [aConstant f],mode := [aConstant g],target := [],remaining := [],output := (heads f g).reverse ++ r.output}

theorem body_exec (r : Registers) (s : Saved) {n : Nat} (d e : Bool) (f g : Affine n) :
    Exec body (full (ready r (n := n + 1) (d,f) (e,g)) s) (7 * n + 16)
      (full (ready {r with output := (affineWord (SourceQuadraticHead.head d e f g)).reverse ++ r.output} f g)
        ⟨affineWord f,affineWord g⟩) := by
  let tails := {r with input := affineWord f,mode := affineWord g,target := List.replicate (n + 1) true,remaining := []}
  let saved : Saved := ⟨affineWord f,affineWord g⟩
  let loaded := {r with input := affineWord f,mode := affineWord g,target := List.replicate n true,remaining := List.replicate n true}
  let computed := {r with input := [],mode := [],target := List.replicate n true,remaining := [],output := (affineWord (SourceQuadraticHead.head d e f g)).reverse ++ r.output}
  let final := ready {r with output := (affineWord (SourceQuadraticHead.head d e f g)).reverse ++ r.output} f g
  have prep : Exec prepare (full tails s) 4 (full loaded saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have calculate : Exec (SourceQuadraticHead.block d e) loaded.store (SourceQuadraticHead.fuel n) computed.store := by
    simpa only [loaded,computed,List.append_nil] using
      SourceQuadraticHead.block_exec {r with target := List.replicate n true} d e f g [] []
  have restoreTails : Exec restore (full computed saved) 2 (full final saved) :=
    Exec.seq (.action _ _) (.action _ _)
  have rest : Exec (afterLeads d e) (full tails s) (4 + (SourceQuadraticHead.fuel n + 2)) (full final saved) :=
    Exec.seq prep (Exec.seq (Frame.execution calculate saved.store) restoreTails)
  have right := readRight_exec tails s e (fun e => afterLeads d e) _ _ rest
  have left := readLeft_exec {tails with mode := e :: tails.mode} s d
    (fun d => readRight fun e => afterLeads d e) _ _ right
  have cost : 7 * n + 16 = 2 + (2 + (4 + (SourceQuadraticHead.fuel n + 2))) := by
    simp only [SourceQuadraticHead.fuel]; omega
  simpa only [body,ready,tails,final,saved,affineWord_cons,cost] using left

def loop : Block 11 := .loop 1 body
def loopFuel : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + ((7 * n + 16) + loopFuel n)

theorem loop_exec (r : Registers) (s : Saved) {n : Nat} (f g : Affine n) :
    ∃ after : Saved, Exec loop (full (ready r f g) s) (loopFuel n) (full (doneLoop r f g) after) := by
  induction n generalizing r s with
  | zero =>
    refine ⟨s,?_⟩
    exact Exec.loopStop rfl
  | succ n ih =>
    rcases f with ⟨d,f⟩
    rcases g with ⟨e,g⟩
    let saved : Saved := ⟨affineWord f,affineWord g⟩
    let next := {r with output := (affineWord (SourceQuadraticHead.head d e f g)).reverse ++ r.output}
    obtain ⟨after,rest⟩ := ih next saved f g
    refine ⟨after,?_⟩
    have checked := Exec.loopStep (source := (1 : Fin 11)) rfl (body_exec r s d e f g) rest
    simpa only [loop,loopFuel,doneLoop,next,saved,heads,aConstant,List.reverse_append,List.append_assoc] using checked

def finish : Block 11 := readLeft fun d => readRight fun e => .action (.push 8 (d && e))
theorem finish_exec (r : Registers) (s : Saved) (d e : Bool) :
    Exec finish (full {r with input := d :: r.input,mode := e :: r.mode} s) 5
      (full {r with output := (d && e) :: r.output} s) := by
  unfold finish
  refine readLeft_exec {r with mode := e :: r.mode} s d _ 3 _ ?_
  refine readRight_exec r s e _ 1 _ ?_
  exact .action _ _

def block : Block 11 := .seq loop finish
def fuel (n : Nat) : Nat := loopFuel n + 5

theorem block_exec (r : Registers) (s : Saved) {n : Nat} (f g : Affine n) :
    ∃ after : Saved, Exec block (full (ready r f g) s) (fuel n)
      (full {r with input := [],mode := [],target := [],remaining := [],output := (SourceQuadraticEncoding.word (qProduct f g)).reverse ++ r.output} after) := by
  obtain ⟨after,first⟩ := loop_exec r s f g
  refine ⟨after,?_⟩
  have last : Exec finish (full (doneLoop r f g) after) 5
      (full {r with input := [],mode := [],target := [],remaining := [],output := (SourceQuadraticEncoding.word (qProduct f g)).reverse ++ r.output} after) := by
    have checked := finish_exec {r with input := [],mode := [],target := [],remaining := [],output := (heads f g).reverse ++ r.output} after (aConstant f) (aConstant g)
    simpa only [doneLoop,word_split,List.reverse_append,List.reverse_singleton,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using checked
  exact Exec.seq first last

theorem loopFuel_bound (n : Nat) : loopFuel n ≤ (7 * n + 17) * n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [loopFuel,Nat.mul_add,Nat.add_mul,Nat.mul_one] at ih ⊢
    omega
theorem fuel_bound (n : Nat) : fuel n ≤ (7 * n + 17) * n + 6 := by
  have bound := loopFuel_bound n
  unfold fuel
  omega

def forwardFinish : Block 11 := .seq (.action (.copy 3 8)) <|
  .seq (.action (.clear 8)) (Frame.block 2 ClauseQuery.reverseLoop)
def forwardBlock : Block 11 := .seq block forwardFinish
def forwardFuel (n : Nat) : Nat := fuel n + (4 * quadraticBits n + 3)

theorem forward_exec (r : Registers) (s : Saved) {n : Nat} (f g : Affine n) :
    ∃ after : Saved, Exec forwardBlock (full (ready {r with output := []} f g) s) (forwardFuel n)
      (full {r with input := [],mode := [],target := [],remaining := [],excess := [],output := SourceQuadraticEncoding.word (qProduct f g)} after) := by
  obtain ⟨after,first⟩ := block_exec {r with output := []} s f g
  refine ⟨after,?_⟩
  let reversed := {r with input := [],mode := [],target := [],remaining := [],output := (SourceQuadraticEncoding.word (qProduct f g)).reverse}
  let prepared := {reversed with excess := (SourceQuadraticEncoding.word (qProduct f g)).reverse,output := []}
  let final := {r with input := [],mode := [],target := [],remaining := [],excess := [],output := SourceQuadraticEncoding.word (qProduct f g)}
  have reverseOutput : Exec ClauseQuery.reverseLoop prepared.store (4 * quadraticBits n + 1) final.store := by
    simpa only [prepared,reversed,final,List.length_reverse,SourceQuadraticEncoding.word_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec {r with input := [],mode := [],target := [],remaining := [],output := []}
        (SourceQuadraticEncoding.word (qProduct f g)).reverse
  have finishOutput : Exec forwardFinish (full reversed after) (4 * quadraticBits n + 3) (full final after) := by
    have checked := Exec.seq (by exact .action _ _ : Exec (.action (.copy (3 : Fin 11) 8))
      (full reversed after) 1 (full {reversed with excess := (SourceQuadraticEncoding.word (qProduct f g)).reverse} after))
      (Exec.seq (by exact .action _ _ : Exec (.action (.clear (8 : Fin 11)))
        (full {reversed with excess := (SourceQuadraticEncoding.word (qProduct f g)).reverse} after) 1 (full prepared after))
        (Frame.execution reverseOutput after.store))
    have cost : 4 * quadraticBits n + 3 = 1 + (1 + (4 * quadraticBits n + 1)) := by omega
    simpa only [forwardFinish,cost,full] using checked
  have start : Exec block (full (ready {r with output := []} f g) s) (fuel n) (full reversed after) := by
    simpa only [reversed,List.append_nil] using first
  exact Exec.seq start finishOutput

theorem forwardFuel_bound (n : Nat) :
    forwardFuel n ≤ (7 * n + 17) * n + 4 * ((n + 1) * (n + 1)) + 9 := by
  have ticks := fuel_bound n
  have width := SourceQuadraticEncoding.word_bound (qOfAffine (aConst n false))
  rw [SourceQuadraticEncoding.word_length] at width
  unfold forwardFuel
  omega

theorem sourceFuel_bound {n : Nat} (f g : Affine n) :
    let L := (affineWord f ++ affineWord g).length
    forwardFuel n ≤ (7 * L + 17) * L + 4 * ((L + 1) * (L + 1)) + 9 := by
  dsimp only
  let L := (affineWord f ++ affineWord g).length
  have hn : n ≤ L := by
    simp only [L,List.length_append,affineWord_length]
    omega
  have productBound : (7 * n + 17) * n ≤ (7 * L + 17) * L :=
    Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hn) 17) hn
  have widthBound : (n + 1) * (n + 1) ≤ (L + 1) * (L + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.add_le_add_right hn 1)
  have bound := forwardFuel_bound n
  change forwardFuel n ≤ (7 * L + 17) * L + 4 * ((L + 1) * (L + 1)) + 9
  omega

end PNP.Concrete.ResidualReduction.SourceQuadraticProduct
