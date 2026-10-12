import PNP.Concrete.NormalizerSystemRowsPackets
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (a b c : SystemRows.State) (xs ys : List BitString)
    (first : SystemRows.Produced a b xs) (second : SystemRows.Produced b c ys) :
    SystemRows.Produced a c (xs++ys) := SystemRows.produced_trans a b c xs ys first second
example : SystemRows.bytes [[true,false],[false],[true,true]] = [true,false,false,true,true] := rfl
example (r : SystemRows.State) : (SystemRows.input r).row = r.counter := SystemRows.input_row r
#print axioms SystemRows.bytes_append
#print axioms SystemRows.produced_one
#print axioms SystemRows.produced_trans
#print axioms SystemRows.emit_produced
#print axioms SystemRows.advance_produced
#print axioms SystemRows.input_encoded
#print axioms SystemRows.result_output
#print axioms SystemRows.scan_produced
end PNP.Concrete.NormalizerBlocks
