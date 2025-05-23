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

inductive FlushDirection
  | push | pull

instance : ToString FlushDirection where toString
  | .push => "push"
  | .pull => "pull"

end Binius
