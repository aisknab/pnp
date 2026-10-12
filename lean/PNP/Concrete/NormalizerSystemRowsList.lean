/-
Copyright (c) 2026 PNP Labs.

Complete row-list serialization, including the derived item-count header.
Initialization, the unbounded row scan and final serialization are charged
once against a fixed polynomial in the initial register-size bound.
-/
import PNP.Concrete.NormalizerSystemRowsSemantics

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

def beginList : Block 29 :=
  .seq (.action (.copy 25 24))
    (.seq (.action (.clear 26)) (.seq (.action (.clear 27)) (.action (.clear 28))))
def begun (r : State) : State :=
  {r with remaining := r.rows,counter := [],count := [],buffer := []}
theorem beginList_exec (r : State) : Exec beginList r.store 4 (begun r).store := by
  let cursor : State := {r with remaining := r.rows}
  let ordinal : State := {cursor with counter := []}
  let count : State := {ordinal with count := []}
  have a : Exec (.action (.copy 25 24)) r.store 1 cursor.store := .action _ _
  have b : Exec (.action (.clear 26)) cursor.store 1 ordinal.store := .action _ _
  have c : Exec (.action (.clear 27)) ordinal.store 1 count.store := .action _ _
  have d : Exec (.action (.clear 28)) count.store 1 (begun r).store := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c d))

def loadPacket : Block 29 := .seq (.action (.copy 10 27)) (.action (.copy 11 28))
def packetLoaded (r : State) : State :=
  r.withCore (r.core.withDense {r.core.core.core with
    core := {r.core.core.core.core with variables := r.count,buffer := r.buffer}})
theorem loadPacket_exec (r : State) : Exec loadPacket r.store 2 (packetLoaded r).store :=
  Exec.seq (.action _ _) (.action _ _)
def finishList : Block 29 := .seq loadPacket (liftCore Coefficient.finish.block)
def finished (r : State) : State :=
  (packetLoaded r).withCore (Coefficient.finish.result (packetLoaded r).core)
def finishFuel (r : State) : Nat := 4*r.buffer.length+4*r.count.length+8
theorem finishList_exec (r : State) :
    Exec finishList r.store (finishFuel r) (finished r).store := by
  have checked := Exec.seq (loadPacket_exec r)
    (liftCore_exec _ (packetLoaded r) _ _ (Coefficient.finish.exec _))
  change Exec finishList r.store
    (2+(2+((4*r.buffer.length+1)+(2+(4*r.count.length+1))))) (finished r).store at checked
  have cost : 2+(2+((4*r.buffer.length+1)+(2+(4*r.count.length+1)))) = finishFuel r := by
    unfold finishFuel
    omega
  rw [cost] at checked
  exact checked
theorem finished_output (r : State) :
    (finished r).registers.output = r.count.reverse ++ false::r.buffer.reverse :=
  Coefficient.finish_output (packetLoaded r).core
theorem finished_shared (r : State) : (finished r).shared = r.shared :=
  congrArg (fun d : Coefficient.Data => {d with row := []}) (Coefficient.finish_data (packetLoaded r).core)
theorem finished_rows (r : State) : (finished r).rows = r.rows := rfl
theorem finishFuel_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    finishFuel r ≤ 8*n+8 := by
  have count := Store.get_length_le r.store (27 : Fin 29) bounded
  have buffer := Store.get_length_le r.store (28 : Fin 29) bounded
  change r.count.length ≤ n at count
  change r.buffer.length ≤ n at buffer
  unfold finishFuel
  omega
def encodePackets (packets : List BitString) : BitString :=
  List.replicate packets.length true ++ false::bytes packets
theorem finished_packets (before after : State) (packets : List BitString)
    (emptyCount : before.count = []) (emptyBuffer : before.buffer = [])
    (produced : Produced before after packets) :
    (finished after).registers.output = encodePackets packets := by
  rw [finished_output,produced.1,produced.2,emptyCount,emptyBuffer,
    List.append_nil,List.append_nil,Coefficient.reverse_replicate,List.reverse_reverse]
  rfl

def listBlock (iteration : Iteration) : Block 29 :=
  .seq beginList (.seq (loop iteration) finishList)
def listResult (iteration : Iteration) (r : State) : State :=
  finished (whole iteration (begun r)).state
def listFuel (iteration : Iteration) (r : State) : Nat :=
  4+((whole iteration (begun r)).fuel+finishFuel (whole iteration (begun r)).state)
theorem list_exec (iteration : Iteration) (r : State) :
    Exec (listBlock iteration) r.store (listFuel iteration r) (listResult iteration r).store :=
  Exec.seq (beginList_exec r) (Exec.seq (whole_exec iteration (begun r)) (finishList_exec _))
theorem list_shared (iteration : Iteration) (r : State) : (listResult iteration r).shared = r.shared :=
  (finished_shared _).trans (scan_shared iteration _ _)
theorem list_rows (iteration : Iteration) (r : State) : (listResult iteration r).rows = r.rows :=
  (finished_rows _).trans (scan_rows iteration _ _)

def scanBound (iteration : Iteration) : NatPolynomial :=
  .add (.mul .variable (.add (.constant 1) iteration.bound)) (.constant 1)
theorem begun_scan_bound (iteration : Iteration) (r : State) (n : Nat)
    (bounded : r.store.Bounded n) :
    (whole iteration (begun r)).fuel ≤ (scanBound iteration).eval n := by
  have rowBound := Store.get_length_le r.store (24 : Fin 29) bounded
  change r.rows.length ≤ n at rowBound
  have budget : (begun r).counter.length + r.rows.length ≤ n := by
    simpa only [begun,List.length_nil,Nat.zero_add] using rowBound
  have work := scan_fuel_bound iteration r.rows (begun r) n (shared_bounded r n bounded) budget
  have mul := Nat.mul_le_mul_right (1+iteration.bound.eval n) rowBound
  change (whole iteration (begun r)).fuel ≤ n*(1+iteration.bound.eval n)+1
  exact Nat.le_trans work (Nat.add_le_add_right mul 1)
def listBound (iteration : Iteration) : NatPolynomial :=
  .add (.linear 8 44) (.mul (.constant 9) (scanBound iteration))
theorem list_fuel_bound (iteration : Iteration) (r : State) (n : Nat)
    (bounded : r.store.Bounded n) :
    listFuel iteration r ≤ (listBound iteration).eval n := by
  have first := (beginList_exec r).bounded n bounded
  have scanWork := begun_scan_bound iteration r n bounded
  have after := (whole_exec iteration (begun r)).bounded (n+4) first
  have last := finishFuel_bound (whole iteration (begun r)).state
    (n+4+(whole iteration (begun r)).fuel) after
  change 4+((whole iteration (begun r)).fuel+finishFuel (whole iteration (begun r)).state) ≤
    (8*n+44)+9*(scanBound iteration).eval n
  omega
theorem list_result_bounded (iteration : Iteration) (r : State) (n : Nat)
    (bounded : r.store.Bounded n) :
    (listResult iteration r).store.Bounded (n+(listBound iteration).eval n) :=
  Store.bounded_mono ((list_exec iteration r).bounded n bounded)
    (Nat.add_le_add_left (list_fuel_bound iteration r n bounded) n)
theorem list_packets (iteration : Iteration) (r : State) (packets : List BitString)
    (produced : Produced (begun r) (whole iteration (begun r)).state packets) :
    (listResult iteration r).registers.output = encodePackets packets :=
  finished_packets (begun r) _ packets rfl rfl produced

end PNP.Concrete.NormalizerBlocks.SystemRows
