module
public import Ix.CanonM

@[expose] public section
namespace Ix.Compile.SemanticPresence

/-- Complete source equality; the existing confirmation has a proved pure fallback. -/
structure Key where
  expr : Lean.Expr

instance : BEq Key := ⟨fun a b => @decide (a.expr = b.expr) (CanonM.confirm a.expr b.expr)⟩
instance : Hashable Key := ⟨fun key => hash key.expr⟩
instance : LawfulBEq Key where
  eq_of_beq {a b} same := by
    have equal := (@decide_eq_true_iff _ (CanonM.confirm a.expr b.expr)).mp same
    cases a; cases b; exact congrArg Key.mk equal
  rfl {a} := (@decide_eq_true_iff _ (CanonM.confirm a.expr a.expr)).mpr rfl

/-- Structural meaning of semantic-contract presence, independent of the native finder. -/
def spec : Lean.Expr → Bool
  | .app f a => spec f || spec a
  | .lam _ t b _ | .forallE _ t b _ => spec t || spec b
  | .letE _ t v b _ => spec t || spec v || spec b
  | .proj _ _ e => spec e
  | .mdata data e => !(Ix.SemanticContract.leanFields data).isEmpty || spec e
  | _ => false

/-- Iterate over the shared source graph. Hashes select buckets; exact
source equality confirms skips. The hasher argument permits collision
controls; the production caller uses Lean.Expr's existing hash. -/
def run [Hashable Key] (top : Lean.Expr) : Bool := Id.run do
  let mut seen : Std.HashSet Key := {}
  let mut stack := #[top]
  let mut found := false
  while !found && !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains ⟨e⟩ then continue
    seen := seen.insert ⟨e⟩
    match e with
    | .app fn arg => stack := stack.push fn |>.push arg
    | .lam _ type body _ | .forallE _ type body _ =>
      stack := stack.push type |>.push body
    | .letE _ type value body _ => stack := stack.push type |>.push value |>.push body
    | .proj _ _ value => stack := stack.push value
    | .mdata data inner =>
      if !(Ix.SemanticContract.leanFields data).isEmpty then found := true
      else stack := stack.push inner
    | _ => pure ()
  return found

end Ix.Compile.SemanticPresence
