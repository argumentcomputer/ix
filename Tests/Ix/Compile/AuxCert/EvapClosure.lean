/-! SCC split with an evaporated nested aux (`List B`, B split away), in a
closure compile: `Ix.EnvScope.collectDeps` may not bring in `List.rec`, the
evaporation alias target (aux_gen.rs:1273-1277). -/
namespace EvapClosure
mutual
inductive A where
  | mk : List B → A
inductive B where
  | leaf : B
end
end EvapClosure
