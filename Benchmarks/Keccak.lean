import Ix.IxVM.Core
import Ix.IxVM.ByteStream
import Ix.IxVM.Keccak
import Benchmarks.HashCommon

def mergedToplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let tl ← IxVM.core.merge IxVM.byteStream
  tl.merge IxVM.keccak

def main : IO Unit := do
  let _ ← HashBench.run "prove keccak256" `keccak256_bench mergedToplevel
  return
