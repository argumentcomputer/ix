import Ix.IxVM.Core
import Ix.IxVM.ByteStream
import Ix.IxVM.Sha256
import Benchmarks.HashCommon

def mergedToplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let tl ← IxVM.core.merge IxVM.byteStream
  tl.merge IxVM.sha256

def main : IO Unit := do
  let _ ← HashBench.run "prove sha256" `sha256_bench mergedToplevel
  return
