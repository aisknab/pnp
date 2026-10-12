import PNP.Concrete.NormalizerSystemRowsState
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (routine : Coefficient.Routine) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    SystemRows.fuel routine r ≤ 19 + routine.bound.eval n :=
  SystemRows.fuel_bound routine r n fixed index
example (routine : Coefficient.Routine) (r : SystemRows.State) :
    (SystemRows.result routine r).buffer = r.buffer := (SystemRows.result_frame routine r).2.2.2.2
example (ctx : Coefficient.Context) (r : SystemRows.State) (encoded : ctx.Encoded r.core) :
    ctx.Encoded (SystemRows.loaded r).core := SystemRows.loaded_encoded ctx r encoded
#print axioms SystemRows.loadRow_exec
#print axioms SystemRows.loaded_data_bounded
#print axioms SystemRows.run_exec
#print axioms SystemRows.result_shared
#print axioms SystemRows.result_row
#print axioms SystemRows.fuel_bound
#print axioms SystemRows.result_core_bounded
#print axioms SystemRows.result_output_bound
#print axioms SystemRows.shared_bounded
#print axioms SystemRows.encoded_transport
end PNP.Concrete.NormalizerBlocks
