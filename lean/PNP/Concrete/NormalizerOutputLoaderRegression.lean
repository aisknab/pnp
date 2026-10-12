import PNP.Concrete.NormalizerOutputLoader
namespace PNP.Concrete.NormalizerBlocks
example : OutputLoader.WidthSlot.original.index.val = 36 := rfl
example : OutputLoader.WidthSlot.frontend.index.val = 37 := rfl
example (r : SystemAssembly.State) : (OutputLoader.clearFrontend.result r).b = r.b := rfl
#print axioms OutputLoader.saveWidth_store
#print axioms OutputLoader.block_exec
#print axioms OutputLoader.fuel_bound
#print axioms OutputLoader.loaded_bounded
end PNP.Concrete.NormalizerBlocks
