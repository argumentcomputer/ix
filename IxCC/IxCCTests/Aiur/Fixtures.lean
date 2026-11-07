import IxCC.Aiur

namespace IxCCTests.Aiur

open IxCC.Aiur
open _root_.IxCC.Vendor.Aiur (G)

def call (function : Nat) (input : Nat := 0) (output : Nat := 9) : Message :=
  .function function [G.ofNat input] [G.ofNat output]

def provider (message : Message) (demands : List Message := []) (weight : G := 1)
    (active : Bool := true) : Row := ⟨active, message, weight, demands⟩

def leaf : Trace := ⟨[provider (call 0)], [call 0]⟩

def shared : Trace :=
  ⟨[provider (call 0) [call 1, call 1], provider (call 1) [] 2], [call 0]⟩

def negativeWeights : Trace :=
  ⟨[provider (call 0) [] 2, provider (call 0) [] ((0 : G) - 1)], [call 0]⟩

def missingProvider : Trace := ⟨[provider (call 0) [call 1]], [call 0]⟩

def inactiveProvider : Trace :=
  ⟨[provider (call 0) [call 1], provider (call 1) [] 1 false], [call 0]⟩

def inactiveJunk : Trace :=
  ⟨[provider (call 0), provider (call 1) [call 77] 0 false], [call 0]⟩

def wrongOutput : Trace :=
  ⟨[provider (call 0) [call 1 0 10], provider (call 1)], [call 0]⟩

def unusedProvider : Trace := ⟨[provider (call 0), provider (call 1)], [call 0]⟩

def memoryMessage (bucket pointer value : Nat) : Message :=
  .memory bucket (G.ofNat pointer) [G.ofNat value]

def witnessMemory : Trace :=
  ⟨[provider (call 0) [memoryMessage 1 7 42], provider (memoryMessage 1 7 42)], [call 0]⟩

def inconsistentMemory : Trace :=
  ⟨[provider (call 0) [memoryMessage 1 7 42, memoryMessage 1 7 43],
    provider (memoryMessage 1 7 42), provider (memoryMessage 1 7 43)], [call 0]⟩

def separateBuckets : Trace :=
  ⟨[provider (call 0) [memoryMessage 1 7 42, memoryMessage 2 7 43],
    provider (memoryMessage 1 7 42), provider (memoryMessage 2 7 43)], [call 0]⟩

def selfPointer : Trace :=
  ⟨[provider (call 0) [memoryMessage 1 7 7], provider (memoryMessage 1 7 7)], [call 0]⟩

/-- Balanced but circular: one public demand and one self-demand, weight two. -/
def selfCall : Trace := ⟨[provider (call 0) [call 0] 2], [call 0]⟩

def mutualCall : Trace :=
  ⟨[provider (call 0) [call 1] 2, provider (call 1) [call 0]], [call 0]⟩

/-- Counter edge, then a component-order edge, then a ranked edge. -/
def mixedMessage (index : Nat) : Message := call (index / 2) (index % 2)

def mixed : Trace :=
  ⟨(List.range 4).map (fun index => provider (mixedMessage index)
    (if index < 3 then [mixedMessage (index + 1)] else [])), [mixedMessage 0]⟩

def mixedStatic : StaticCertificate mixed.RowId mixed.Requires where
  facts := fun id => ⟨id.val / 2, G.ofNat (id.val % 2), id.val⟩
  ranked := fun order => order == 1
  edge := by decide

def memoryStatic : StaticCertificate witnessMemory.RowId witnessMemory.Requires where
  facts := fun id => ⟨id.val, 0, 0⟩
  ranked := fun _ => false
  edge := by decide

end IxCCTests.Aiur
