import PNP.Concrete.NormalizerCacheSigmaRead
namespace PNP.Concrete.NormalizerBlocks
example (r : CacheSigma.State) : CacheSigma.table false r = r.matching := rfl
example (r : CacheSigma.State) : CacheSigma.table true r = r.counter := rfl
example (flag : Bool) (r : CacheSigma.State) :
    (CacheSigma.tableRead flag r).core.formula = r.core.formula :=
  (CacheSigma.tableRead_fields flag r).1
example (flag : Bool) (r : CacheSigma.State) :
    Exec (CacheSigma.readTable flag) r.store (CacheSigma.readFuel flag r) (CacheSigma.tableRead flag r).store :=
  CacheSigma.readTable_exec flag r
#print axioms CacheSigma.loadTable_exec
#print axioms CacheSigma.prepareTable_exec
#print axioms CacheSigma.selectTable_exec
#print axioms CacheSigma.selectionFuel_bound
#print axioms CacheSigma.selected_output_bound
#print axioms CacheSigma.readTable_exec
#print axioms CacheSigma.readFuel_bound
#print axioms CacheSigma.tableRead_output_bound
#print axioms CacheSigma.tableRead_fields
#print axioms CacheSigma.tableRead_canonical
end PNP.Concrete.NormalizerBlocks
