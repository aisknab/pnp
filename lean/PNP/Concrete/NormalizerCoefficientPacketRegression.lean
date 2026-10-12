import PNP.Concrete.NormalizerCoefficientPacket
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (rows : List Coefficient.Row) :
    Coefficient.encodeRows rows = List.replicate rows.length true ++ false::Coefficient.stream rows := rfl
example (routine : Coefficient.Routine) (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    (Coefficient.packet routine).fuel r ≤ (Coefficient.packet routine).bound.eval n :=
  (Coefficient.packet routine).cost r n h
example (routine : Coefficient.Routine) (r : Coefficient.State) (rows : List Coefficient.Row)
    (h : Coefficient.Emits (Coefficient.started r) (routine.result (Coefficient.started r)) rows) :
    ((Coefficient.packet routine).result r).registers.output = Coefficient.encodeRows rows :=
  Coefficient.packet_output routine r rows h
#print axioms Coefficient.reverseRoutine
#print axioms Coefficient.finish
#print axioms Coefficient.finish_output
#print axioms Coefficient.start
#print axioms Coefficient.packet
#print axioms Coefficient.reverse_replicate
#print axioms Coefficient.packet_output
#print axioms Coefficient.packet_data
end PNP.Concrete.NormalizerBlocks
