import PNP.Concrete.NormalizerBatchPacketLoader

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    Exec BatchPacket.loader (BatchPacket.seedState input).store (BatchPacket.loaderFuel input)
      (BatchPacket.loaded input).store := BatchPacket.loader_exec input
example (input : BitString) : BatchPacket.loaderFuel input ≤ 33 * input.length + 44 :=
  BatchPacket.loaderFuel_bound input
example (input : BitString) :
    (BatchPacket.loaded input).pending.length ≤ input.length ∧
      (BatchPacket.loaded input).table.length ≤ input.length := BatchPacket.loaded_size input
example (input : BitString) :
    (BatchPacket.coreResult input).output.length + (BatchPacket.coreResult input).input.length ≤ input.length :=
  BatchPacket.core_size input

#print axioms BatchPacket.core_exec
#print axioms BatchPacket.taken_size
#print axioms BatchPacket.core_size
#print axioms BatchPacket.coreFuel_bound
#print axioms BatchPacket.commit_exec
#print axioms BatchPacket.loader_exec
#print axioms BatchPacket.loaderFuel_bound
#print axioms BatchPacket.loaded_size

end PNP.Concrete.NormalizerBlocks
