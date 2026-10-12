/-
Copyright (c) 2026 PNP Labs.

Closed input loading for path reconstruction: one target vertex followed
by the actual encoded trace. No path, success flag, or loop budget is
supplied in the input packet.
-/
import PNP.Concrete.NormalizerPathPhase

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def initial (input : BitString) : State := ⟨ParentQuery.initial input, [], []⟩
def tags : Block 23 := lift ParentQuery.tags
def tagged (input : BitString) : State := ⟨ParentQuery.tagged input, [], []⟩
theorem tags_exec (input : BitString) : Exec tags (initial input).store 2 (tagged input).store :=
  lift_exec _ (initial input) _ _ (ParentQuery.tags_exec input)

def saveTrace : Block 23 := lift ParentQuery.saveTrace
def traceSaved (r : State) : State := r.withCore (ParentQuery.traceSaved r.core)
theorem saveTrace_exec (r : State) : Exec saveTrace r.store 1 (traceSaved r).store :=
  lift_exec _ r _ _ (ParentQuery.saveTrace_exec r.core)

def loader : Block 23 := .seq tags (.seq readFollow (.seq saveTarget saveTrace))
def loaded (input : BitString) : State := traceSaved (targetSaved (followRead (tagged input)))
def loaderFuel (input : BitString) : Nat := 12 + TableInit.headerFuel input.tail
theorem loader_exec (input : BitString) : Exec loader (initial input).store (loaderFuel input) (loaded input).store := by
  have checked := Exec.seq (tags_exec input) <| Exec.seq (readFollow_exec (tagged input)) <|
    Exec.seq (saveTarget_exec (followRead (tagged input))) (saveTrace_exec (targetSaved (followRead (tagged input))))
  change Exec loader (initial input).store (2 + ((8 + TableInit.headerFuel input.tail) + (1 + 1))) (loaded input).store at checked
  have cost : 2 + ((8 + TableInit.headerFuel input.tail) + (1 + 1)) = loaderFuel input := by unfold loaderFuel; omega
  rw [cost] at checked
  exact checked

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 4 * input.length + 18 := by
  have header := TableInit.headerFuel_bound input.tail
  have tail := ParentQuery.input_tail_bound input
  unfold loaderFuel
  omega

theorem loaded_pending_bound (input : BitString) : (loaded input).core.pending.length ≤ input.length := by
  have header := Occurrence.header_input_bound input.tail (TableInit.seeded input.tail)
  exact Nat.le_trans header (ParentQuery.input_tail_bound input)

def encode (target : CNFLiteral) (trace : List TraceData.Row) : BitString :=
  target.positive :: TableInit.encodeCount target.variableIndex (TraceData.encode trace)

theorem loaded_canonical (target : CNFLiteral) (trace : List TraceData.Row) :
    (loaded (encode target trace)).core.targetIndex = List.replicate target.variableIndex true ∧
      ForwardEdge.present (loaded (encode target trace)).core.targetTag = target.positive ∧
        (loaded (encode target trace)).core.pending = TraceData.encode trace := by
  refine ⟨?_, rfl, ?_⟩
  · change (TableInit.readCount (TableInit.encodeCount target.variableIndex (TraceData.encode trace))).state.target = _
    rw [BatchPacket.header_canonical]
    rfl
  · change (TableInit.readCount (TableInit.encodeCount target.variableIndex (TraceData.encode trace))).state.input = _
    rw [BatchPacket.header_canonical]
    rfl

end PNP.Concrete.NormalizerBlocks.TracePath
