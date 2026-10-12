import PNP.Concrete.NormalizerSystemAssemblyPrepend
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : SystemAssembly.State) :
    ((SystemAssembly.prepend .a).result r).registers.output = r.a ++ r.registers.output :=
  SystemAssembly.prepend_output .a r
example (r : SystemAssembly.State) :
    ((SystemAssembly.prepend .b).result r).registers.output = r.b ++ r.registers.output :=
  SystemAssembly.prepend_output .b r
example (slot : SystemAssembly.PacketSlot) (r : SystemAssembly.State) :
    (SystemAssembly.prepend slot).fuel r = 8*(slot.word r).length+7 :=
  SystemAssembly.prepend_fuel slot r
#print axioms SystemAssembly.slot_read
#print axioms SystemAssembly.preparePrefix
#print axioms SystemAssembly.reversePrefix
#print axioms SystemAssembly.prepareAgain
#print axioms SystemAssembly.prepend
#print axioms SystemAssembly.prepend_output
#print axioms SystemAssembly.prepend_saved
#print axioms SystemAssembly.prepend_recovery
#print axioms SystemAssembly.prepend_shared
#print axioms SystemAssembly.prepend_rows
#print axioms SystemAssembly.prepend_fuel
end PNP.Concrete.NormalizerBlocks
