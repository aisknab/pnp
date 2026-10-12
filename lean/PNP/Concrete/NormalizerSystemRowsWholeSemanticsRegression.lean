import PNP.Concrete.NormalizerSystemRowsWholeSemantics
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (packets : Nat → List BitString) (count start : Nat) :
    SystemRows.packetsFrom packets count start =
      (List.finRange count).flatMap (fun i => packets (start+i.val)) :=
  SystemRows.packetsFrom_finRange packets count start
example (packet : BitString) :
    SystemRows.encodePackets [packet,packet] =
      [true,true,false] ++ packet ++ packet := by
  simp only [SystemRows.encodePackets,SystemRows.bytes,List.length_cons,List.length_nil,
    List.replicate_succ,List.replicate_zero,List.append_nil,List.cons_append,List.nil_append]
#print axioms SystemRows.packetsFrom_finRange
#print axioms SystemRows.list_packets_from
#print axioms SystemRows.list_packets_finRange
end PNP.Concrete.NormalizerBlocks
