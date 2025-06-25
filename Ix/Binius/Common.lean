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

end Binius
