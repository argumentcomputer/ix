import Ix.Ixby.Basic

/-! A host representation of immutable byte builders. Append retains the old
chunks; freeze traverses them once in source order. The cached length is proved
equal to the sequence length, so capacity checks never flatten a builder. -/

namespace Compilatrix.Ixby.Runtime.Chunked

def flatten (chunks : List (Array UInt8)) : Array UInt8 :=
  chunks.reverse.foldl (· ++ ·) #[]

@[simp] theorem flatten_nil : flatten [] = #[] := rfl

@[simp] theorem flatten_cons (chunk : Array UInt8) (chunks : List (Array UInt8)) :
    flatten (chunk :: chunks) = flatten chunks ++ chunk := by
  simp [flatten]

structure Builder where
  chunks : List (Array UInt8)
  size : Nat
  size_eq : (flatten chunks).size = size
  deriving Repr

namespace Builder

def empty : Builder := ⟨[], 0, rfl⟩

instance : Inhabited Builder := ⟨empty⟩

def ofBytes (bytes : Array UInt8) : Builder :=
  ⟨[bytes], bytes.size, by simp⟩

def append (builder : Builder) (chunk : Array UInt8) : Builder :=
  if chunk.isEmpty then builder
  else ⟨chunk :: builder.chunks, builder.size + chunk.size,
    by simp [builder.size_eq]⟩

def freeze (builder : Builder) : Array UInt8 := flatten builder.chunks

@[simp] theorem freeze_empty : empty.freeze = #[] := rfl

@[simp] theorem freeze_ofBytes (bytes : Array UInt8) : (ofBytes bytes).freeze = bytes := by
  simp [ofBytes, freeze]

@[simp] theorem size_freeze (builder : Builder) : builder.freeze.size = builder.size :=
  builder.size_eq

@[simp] theorem freeze_append (builder : Builder) (chunk : Array UInt8) :
    (builder.append chunk).freeze = builder.freeze ++ chunk := by
  simp only [append]
  split
  · rename_i h
    simp only [Array.isEmpty_iff] at h
    simp [h]
  · simp [freeze]

@[simp] theorem size_append (builder : Builder) (chunk : Array UInt8) :
    (builder.append chunk).size = builder.size + chunk.size := by
  rw [← size_freeze, freeze_append, Array.size_append, size_freeze]

end Builder
end Compilatrix.Ixby.Runtime.Chunked
