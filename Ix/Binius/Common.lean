namespace Binius

structure OracleId where
  toUSize : USize
  deriving Inhabited

structure ChannelId where
  toUSize : USize
  deriving Inhabited

inductive FlushDirection
  | push | pull

instance : ToString FlushDirection where toString
  | .push => "push"
  | .pull => "pull"

end Binius
