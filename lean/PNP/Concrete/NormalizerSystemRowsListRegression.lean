import PNP.Concrete.NormalizerSystemRowsList
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : SystemRows.encodePackets [] = [false] := rfl
example : SystemRows.encodePackets [[true,false],[false]] = [true,true,false,true,false,false] := rfl
example (iteration : SystemRows.Iteration) (r : SystemRows.State) (n : Nat)
    (bounded : r.store.Bounded n) :
    SystemRows.listFuel iteration r ≤ (SystemRows.listBound iteration).eval n :=
  SystemRows.list_fuel_bound iteration r n bounded
#print axioms SystemRows.beginList_exec
#print axioms SystemRows.finishList_exec
#print axioms SystemRows.finished_output
#print axioms SystemRows.finished_shared
#print axioms SystemRows.finishFuel_bound
#print axioms SystemRows.finished_packets
#print axioms SystemRows.list_exec
#print axioms SystemRows.list_shared
#print axioms SystemRows.list_rows
#print axioms SystemRows.begun_scan_bound
#print axioms SystemRows.list_fuel_bound
#print axioms SystemRows.list_result_bounded
#print axioms SystemRows.list_packets
end PNP.Concrete.NormalizerBlocks
