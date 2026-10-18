import PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions

/-! Complete encoded-map evaluation at one zero/unit parameter, including
all coordinate reads and output reordering. The parameter schedule is exactly
the original affine search schedule; it does not enumerate all parameter points. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def schedule (k : Nat) : List (Option (Fin k)) := none :: (List.finRange k).map some
theorem schedule_exact (k : Nat) : (schedule k).map parameter = SourcePlane.affineParameters k := by
  simp only [schedule, List.map_cons, List.map_map, parameter, SourcePlane.affineParameters,
    Function.comp_def]

private theorem point_map_cons {m k : Nat} (a : Affine k) (rest : AffineMap m k) (z : Point k) :
    (SourceEncoding.pointCodec (m + 1)).encode (mapEval (a, rest) z) =
      aEval a z :: (SourceEncoding.pointCodec m).encode (mapEval rest z) := rfl

def loop : Block 12 := .loop 0 rowBlock
def loopFuel (k : Nat) (q : Option (Fin k)) (rows : Nat) : Nat := (rowFuel k q + 1) * rows + 1

theorem loop_exec {m k : Nat} (forms : AffineMap m k) (q : Option (Fin k)) (stack output : BitString) :
    Exec loop (ready k q [] (mapBits forms) stack output).store (loopFuel k q m)
      (ready k q [] [] stack
        (((SourceEncoding.pointCodec m).encode (mapEval forms (parameter q))).reverse ++ output)).store := by
  induction m generalizing output with
  | zero => exact Exec.loopStop rfl
  | succ m ih =>
    rcases forms with ⟨a, rest⟩
    have first := rowBlock_exec a q (mapBits rest) stack output
    have last := ih rest (aEval a (parameter q) :: output)
    have present : ∃ bit tail, MatrixInstructions.affineWord a ++ mapBits rest = bit :: tail := by
      cases word : MatrixInstructions.affineWord a with
      | nil =>
        exfalso
        have size := MatrixInstructions.affineWord_length a
        rw [word] at size
        simp only [List.length_nil] at size
        omega
      | cons bit tail => exact ⟨bit, tail ++ mapBits rest, rfl⟩
    obtain ⟨bit, tail, head⟩ := present
    have entered : (ready k q [] (MatrixInstructions.affineWord a ++ mapBits rest) stack output).store.get 0 = bit :: tail := head
    have checked := Exec.loopStep (source := (0 : Fin 12)) entered first last
    have cost : loopFuel k q (m + 1) = 1 + (rowFuel k q + loopFuel k q m) := by
      simp only [loopFuel, Nat.mul_add, Nat.mul_one]; omega
    simpa only [loop, cost, mapBits_cons, point_map_cons, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append] using checked

def reorder : Block 12 :=
  .seq (.seq (.action (.copy 3 8)) (.action (.clear 8))) (lift ClauseQuery.reverseLoop)
theorem reorder_exec (k : Nat) (q : Option (Fin k)) (word : BitString) :
    Exec reorder (ready k q [] [] [] word.reverse).store (4 * word.length + 3)
      (ready k q [] [] [] word).store := by
  let before := ready k q [] [] [] word.reverse
  let prepared : State := {before with core := {before.core with excess := word.reverse, output := []}}
  have copied : Exec (.seq (.action (.copy (3 : Fin 12) 8)) (.action (.clear 8))) before.store 2 prepared.store :=
    Exec.seq (.action _ _) (.action _ _)
  have core : Exec ClauseQuery.reverseLoop prepared.core.store (4 * word.length + 1)
      (ready k q [] [] [] word).core.store := by
    simpa only [prepared, before, ready, SourcePolarInstructions.working, MatrixInstructions.base,
      List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (ready k q [] [] [] []).core word.reverse
  have lifted := lift_exec ClauseQuery.reverseLoop prepared (4 * word.length + 1)
    (ready k q [] [] [] word).core core
  have cost : 4 * word.length + 3 = 2 + (4 * word.length + 1) := by omega
  simpa only [reorder, cost, before, prepared, ready, SourcePolarInstructions.working,
    MatrixInstructions.base] using Exec.seq copied lifted

def block : Block 12 := .seq loop reorder
def fuel (k : Nat) (q : Option (Fin k)) (rows : Nat) : Nat := loopFuel k q rows + 4 * rows + 3
theorem block_exec {m k : Nat} (forms : AffineMap m k) (q : Option (Fin k)) :
    Exec block (ready k q [] (mapBits forms) [] []).store (fuel k q m)
      (ready k q [] [] [] ((SourceEncoding.pointCodec m).encode (mapEval forms (parameter q)))).store := by
  have first := loop_exec forms q [] []
  simp only [List.append_nil] at first
  have second := reorder_exec k q ((SourceEncoding.pointCodec m).encode (mapEval forms (parameter q)))
  simp only [SourceEncoding.point_length] at second
  have cost : fuel k q m = loopFuel k q m + (4 * m + 3) := by unfold fuel; omega
  simpa only [block, cost] using Exec.seq first second

theorem fuel_bound (k : Nat) (q : Option (Fin k)) (rows : Nat) :
    fuel k q rows ≤ (9 * k + 29) * rows + 4 := by
  have row := rowFuel_bound k q
  have total := Nat.mul_le_mul_right rows (show rowFuel k q + 1 ≤ 9 * k + 25 by omega)
  simp only [fuel, loopFuel, Nat.add_mul] at total ⊢
  omega

/-- This covers the actual map computed from source equations, with the same
coefficient order. The equality identifies the computed branch; it is not an
assumed discovery-completeness or activity premise. -/
theorem computed_candidate_exec {n : Nat} (F : Family n) (s : Space F.length)
    (_computed : solve F.length (SourceClosure.affineMaskRows F) = some s)
    (q : Option (Fin s.parameters)) :
    Exec block (ready s.parameters q [] (mapBits s.forms) [] []).store (fuel s.parameters q F.length)
      (ready s.parameters q [] [] []
        ((SourceEncoding.pointCodec F.length).encode (mapEval s.forms (parameter q)))).store :=
  block_exec s.forms q

theorem computed_fuel_bound {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) (q : Option (Fin s.parameters)) :
    fuel s.parameters q F.length ≤ (9 * F.length + 29) * F.length + 4 := by
  have bound := solve_some_parameter_bound (SourceClosure.affineMaskRows F) s computed
  have mono := Nat.mul_le_mul_right F.length (show 9 * s.parameters + 29 ≤ 9 * F.length + 29 by omega)
  exact Nat.le_trans (fuel_bound s.parameters q F.length) (by omega)

end PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions
