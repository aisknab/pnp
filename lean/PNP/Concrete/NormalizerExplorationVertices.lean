/-
Copyright (c) 2026 PNP Labs.

Build both complete ordered vertex ranges from the internal clause count
and original variable width. The finite ranges are enumerated by loops;
the caller supplies no vertex list or selection order.
-/

import PNP.Concrete.NormalizerExplorationBudget

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

def startVertices : Block 28 :=
  .seq (.action (.copy 2 20)) (.seq (.action (.clear 1)) (.action (.clear 3)))
def verticesStarted (r : State) : State :=
  r.withRegisters {r.registers with remaining := r.core.parent.currentIndex, target := [], excess := []}
theorem startVertices_exec (r : State) : Exec startVertices r.store 3 (verticesStarted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def range (tag : Bool) : Block 28 := liftCore (SearchVertices.loop tag)
def rangeResult (tag : Bool) (r : State) : State :=
  r.withRegisters (SearchVertices.whole tag r.registers).state
def rangeFuel (tag : Bool) (r : State) : Nat := (SearchVertices.whole tag r.registers).fuel
theorem range_exec (tag : Bool) (r : State) :
    Exec (range tag) r.store (rangeFuel tag r) (rangeResult tag r).store :=
  liftCore_exec _ r _ _ (SearchVertices.whole_exec tag r.registers)

def nextVertices : Block 28 := .seq reloadWidth (.action (.clear 1))
def verticesNext (r : State) : State := (widthReloaded r).withRegisters {(widthReloaded r).registers with target := []}
theorem nextVertices_exec (r : State) : Exec nextVertices r.store 2 (verticesNext r).store :=
  Exec.seq (reloadWidth_exec r) (.action _ _)

def leftBuilt (r : State) : State := rangeResult true (verticesStarted r)
def rightBuilt (r : State) : State := rangeResult false (verticesNext (leftBuilt r))
def verticesPrefix : Block 28 := .seq startVertices (.seq (range true) (.seq nextVertices (range false)))
def verticesPrefixFuel (r : State) : Nat :=
  3 + (rangeFuel true (verticesStarted r) + (2 + rangeFuel false (verticesNext (leftBuilt r))))
theorem verticesPrefix_exec (r : State) :
    Exec verticesPrefix r.store (verticesPrefixFuel r) (rightBuilt r).store :=
  Exec.seq (startVertices_exec r) <| Exec.seq (range_exec true (verticesStarted r)) <|
    Exec.seq (nextVertices_exec (leftBuilt r)) (range_exec false (verticesNext (leftBuilt r)))

def packVertices : Block 28 := liftCore ClauseQuery.pack
def verticesPacked (r : State) : State := r.withRegisters (ClauseQuery.packed r.registers)
theorem packVertices_exec (r : State) :
    Exec packVertices r.store (ClauseQuery.packFuel r.registers) (verticesPacked r).store :=
  liftCore_exec _ r _ _ (ClauseQuery.pack_exec r.registers)

def saveUnseen : Block 28 := .action (.copy 22 8)
def unseenSaved (r : State) : State := r.withCore {r.core with pending := r.registers.output}
theorem saveUnseen_exec (r : State) : Exec saveUnseen r.store 1 (unseenSaved r).store := .action _ _

def buildVertices : Block 28 := .seq verticesPrefix (.seq packVertices saveUnseen)
def verticesBuilt (r : State) : State := unseenSaved (verticesPacked (rightBuilt r))
def verticesFuel (r : State) : Nat :=
  verticesPrefixFuel r + (ClauseQuery.packFuel (rightBuilt r).registers + 1)
theorem buildVertices_exec (r : State) : Exec buildVertices r.store (verticesFuel r) (verticesBuilt r).store :=
  Exec.seq (verticesPrefix_exec r) (Exec.seq (packVertices_exec (rightBuilt r))
    (saveUnseen_exec (verticesPacked (rightBuilt r))))

theorem verticesBuilt_frame (r : State) :
    (verticesBuilt r).core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
      (verticesBuilt r).core.parent.graph.core.matching = r.core.parent.graph.core.matching ∧
        (verticesBuilt r).core.trace = r.core.trace ∧ (verticesBuilt r).remaining = r.remaining := ⟨rfl, rfl, rfl, rfl⟩

theorem leftBuilt_buffer (r : State) :
    (leftBuilt r).registers.excess =
      (SearchVertices.rangeBits true r.core.parent.currentIndex.length 0).reverse := by
  have checked := SearchVertices.whole_excess true (verticesStarted r).registers
  change (leftBuilt r).registers.excess =
    (SearchVertices.rangeBits true r.core.parent.currentIndex.length 0).reverse ++ [] at checked
  rw [List.append_nil] at checked
  exact checked

theorem rightBuilt_buffer (r : State) :
    (rightBuilt r).registers.excess =
      (SearchVertices.rangeBits false r.core.parent.targetIndex.length 0).reverse ++
        (SearchVertices.rangeBits true r.core.parent.currentIndex.length 0).reverse := by
  have checked := SearchVertices.whole_excess false (verticesNext (leftBuilt r)).registers
  change (rightBuilt r).registers.excess =
    (SearchVertices.rangeBits false r.core.parent.targetIndex.length 0).reverse ++
      (leftBuilt r).registers.excess at checked
  rw [leftBuilt_buffer] at checked
  exact checked

theorem verticesBuilt_pending (r : State) :
    (verticesBuilt r).core.pending = SearchVertices.encodeVertices
      (SearchVertices.vertices r.core.parent.currentIndex.length r.core.parent.targetIndex.length) := by
  change (rightBuilt r).registers.excess.reverse ++ [true, false] = _
  rw [rightBuilt_buffer, List.reverse_append, List.reverse_reverse, List.reverse_reverse,
    SearchVertices.encoded_vertices]

def rangesBound (clauses variables : Nat) : Nat :=
  (4 * clauses + 13) * clauses + (4 * variables + 13) * variables + 7

theorem verticesPrefixFuel_bound (r : State) :
    verticesPrefixFuel r ≤ rangesBound r.core.parent.currentIndex.length r.core.parent.targetIndex.length := by
  have left := SearchVertices.whole_fuel_bound true (verticesStarted r).registers
  have right := SearchVertices.whole_fuel_bound false (verticesNext (leftBuilt r)).registers
  change rangeFuel true (verticesStarted r) ≤
    (4 * (0 + r.core.parent.currentIndex.length) + 13) * r.core.parent.currentIndex.length + 1 at left
  change rangeFuel false (verticesNext (leftBuilt r)) ≤
    (4 * (0 + r.core.parent.targetIndex.length) + 13) * r.core.parent.targetIndex.length + 1 at right
  simp only [Nat.zero_add] at left right
  unfold verticesPrefixFuel rangesBound
  omega

theorem verticesFuel_bound (r : State) (bound : Nat) (size : r.store.Bounded bound) :
    verticesFuel r ≤ 5 * rangesBound r.core.parent.currentIndex.length r.core.parent.targetIndex.length +
      4 * bound + 13 := by
  have after := (verticesPrefix_exec r).bounded bound size
  have buffer := Store.get_length_le (rightBuilt r).store (3 : Fin 28) after
  change (rightBuilt r).registers.excess.length ≤ bound + verticesPrefixFuel r at buffer
  have prefixBound := verticesPrefixFuel_bound r
  change verticesPrefixFuel r + (4 * (rightBuilt r).registers.excess.length + 12 + 1) ≤ _
  omega

end PNP.Concrete.NormalizerBlocks.Exploration
