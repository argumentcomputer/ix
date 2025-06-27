import Ix.Unsigned

namespace Binius

structure ChannelId where
  toUSize : USize
  deriving Inhabited

-- We can delete this later if we don't need it
structure ChannelAllocator where
  nextId : USize

def ChannelAllocator.init : ChannelAllocator := ⟨0⟩

def ChannelAllocator.next : ChannelAllocator → ChannelId × ChannelAllocator
  | ⟨nextId⟩ => (⟨nextId⟩, ⟨nextId + 1⟩)

def ChannelAllocator.nextN (self : ChannelAllocator) (n : Nat) :
    Array ChannelId × ChannelAllocator :=
  n.fold (init := (#[], self)) fun _ _ (channels, channelAllocator) =>
    let (channel, channelAllocator) := channelAllocator.next
    (channels.push channel, channelAllocator)

inductive FlushDirection
  | push | pull

instance : ToString FlushDirection where toString
  | .push => "push"
  | .pull => "pull"

@[extern "c_rs_add_u128_in_binary_field"]
opaque addUInt128InBinaryField : @& UInt128 → @& UInt128 → UInt128

@[extern "c_rs_mul_u128_in_binary_field"]
opaque mulUInt128InBinaryField : @& UInt128 → @& UInt128 → UInt128

@[extern "rs_mul_u64_in_binary_field"]
opaque mulUInt64InBinaryField : @& UInt64 → @& UInt64 → UInt64

@[extern "rs_pow_u64_in_binary_field"]
opaque powUInt64InBinaryField : (base : @& UInt64) → (exp : @& UInt64) → UInt64

@[extern "c_rs_pow_u128_in_binary_field"]
opaque powUInt128InBinaryField : (base : @& UInt128) → (exp : @& UInt64) → UInt128

@[extern "rs_inv_u64_in_binary_field"]
opaque invUInt64InBinaryField : @& UInt64 → UInt64

end Binius
