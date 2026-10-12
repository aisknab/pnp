import PNP.Concrete.NormalizerBatchHeaders

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) (r : Occurrence.Registers) :
    (Occurrence.headerResult input r).state.excess = r.excess := Occurrence.header_excess input r
example (input : BitString) (r : Occurrence.Registers) (live : r.active ≠ []) (nonempty : input ≠ []) :
    (Occurrence.headerResult input r).state.input.length < input.length :=
  Occurrence.header_input_strict input r live nonempty
example (input : BitString) : (TableWrite.prepared input).excess = [] := TableWrite.prepared_excess input
example (input : BitString) (nonempty : input ≠ []) :
    (TableWrite.prepared input).input.length < input.length := TableWrite.prepared_input_strict input nonempty

#print axioms Occurrence.header_excess
#print axioms Occurrence.header_input_strict
#print axioms TableWrite.prepared_excess
#print axioms TableWrite.prepared_input_strict

end PNP.Concrete.NormalizerBlocks
