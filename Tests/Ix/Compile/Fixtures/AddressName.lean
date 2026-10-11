import Init

universe u
inductive «#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» (α : Type u) : Type u where
  | first : Prod (List α) («#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» α) → «#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» α
  | second : Prod («#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» α) («#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» α) → «#4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01» α

inductive L2cAddressNameNeighbour (α : Type u) : Type u where
  | first : Prod (List α) (L2cAddressNameNeighbour α) → L2cAddressNameNeighbour α
  | second : Prod (L2cAddressNameNeighbour α) (L2cAddressNameNeighbour α) → L2cAddressNameNeighbour α
