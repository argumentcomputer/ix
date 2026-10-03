/-! A user-written head beta-redex in a constructor field type. aux-gen
head-beta-reduces every minor field type (below.rs ~1484, brecon.rs ~1216);
Lean only reduces redexes created by instantiation. -/
namespace BetaField
inductive T
  | leaf
  | mk : (fun α : Type => α) Nat → T → T

def T.size : T → Nat
  | .leaf => 0
  | .mk _ t => t.size + 1
end BetaField
