import PNP.Concrete.NormalizerPathLoader
namespace PNP.Concrete.NormalizerBlocks
example : (TracePath.loaded (TracePath.encode ⟨false, 2⟩ [(⟨false, 2⟩, none)])).core.pending = TraceData.encode [(⟨false, 2⟩, none)] := by decide
example : (TracePath.loaded (TracePath.encode ⟨true, 0⟩ [])).core.targetIndex = [] := by decide
example : (TracePath.loaded []).core.pending = [] := by decide
#print axioms TracePath.loader_exec
#print axioms TracePath.loaderFuel_bound
#print axioms TracePath.loaded_pending_bound
#print axioms TracePath.loaded_canonical
end PNP.Concrete.NormalizerBlocks
