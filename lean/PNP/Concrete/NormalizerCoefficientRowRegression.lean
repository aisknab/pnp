import PNP.Concrete.NormalizerCoefficientRow
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : CoefficientRow.bits 0 false = [false,false] := rfl
example : CoefficientRow.bits 2 true = [true,true,false,true] := rfl
example (tag : Bool) (r : Coefficient.State) : (Coefficient.emitted tag r).count.length = r.count.length+1 := rfl
example (index : Coefficient.Index) (tag : Bool) (r : Coefficient.State) :
    (Coefficient.indexEmitted index tag r).data = r.data := rfl
#print axioms CoefficientRow.drain_exec
#print axioms CoefficientRow.emit_exec
#print axioms CoefficientRow.result_buffer
#print axioms CoefficientRow.bits_length
#print axioms Coefficient.emit_exec
#print axioms Coefficient.emitted_data
#print axioms Coefficient.emitted_buffers
#print axioms Coefficient.emitIndex_exec
#print axioms Coefficient.emitIndexFuel_eq
#print axioms Coefficient.emitAnswer_exec
#print axioms Coefficient.emitAnswerFuel_bound
end PNP.Concrete.NormalizerBlocks
