import PNP.Concrete.NormalizerCutSelectionLoader
namespace PNP.Concrete.NormalizerBlocks
example (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    (CutSelection.loaded tag (CutSelection.encode count trace)).trace = TraceData.encode trace :=
  (CutSelection.loaded_canonical tag count trace).1
example (tag : Bool) (input : BitString) :
    (CutSelection.loaded tag input).remaining.length ≤ 5 * input.length + 6 :=
  (CutSelection.loaded_size tag input).2
#print axioms CutSelection.start_exec
#print axioms CutSelection.loader_exec
#print axioms CutSelection.loaded_fields
#print axioms CutSelection.loaded_size
#print axioms CutSelection.loaderFuel_bound
#print axioms CutSelection.loaded_canonical
#print axioms CutSelection.front_exec
#print axioms CutSelection.frontFuel_eval
#print axioms CutSelection.frontSteps_bound
#print axioms CutSelection.scanned_buffer
end PNP.Concrete.NormalizerBlocks
