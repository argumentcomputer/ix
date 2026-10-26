module
public import Ix.CanonM

@[expose] public section
namespace Ix.Compile.SemanticPresence

def spec : Lean.Expr → Bool
  | .app f a => spec f || spec a
  | .lam _ t b _ | .forallE _ t b _ => spec t || spec b
  | .letE _ t v b _ => spec t || spec v || spec b
  | .proj _ _ e => spec e
  | .mdata data e => !(Ix.SemanticContract.leanFields data).isEmpty || spec e
  | _ => false

/-- The source and proved result remain live together; an address is only a bucket. -/
structure Entry where
  source : Lean.Expr
  value : Bool
  correct : value = spec source

abbrev Memo := Std.HashMap USize Entry

def probe (memo : Memo) (bucket : USize) (e : Lean.Expr) : Option {v : Bool // v = spec e} :=
  match memo.get? bucket with
  | none => none
  | some entry => match CanonM.confirm entry.source e with
    | .isTrue equal => some ⟨entry.value, equal ▸ entry.correct⟩
    | .isFalse _ => none

/-- Every result is proved, including hits under arbitrary bucket collisions
and replacement entries. The key function is not a semantic callback. -/
def go (bucket : Lean.Expr → USize) (e : Lean.Expr) :
    StateT Memo Id {v : Bool // v = spec e} := do
  let key := bucket e
  if let some hit := probe (← get) key e then return hit
  let result : {v : Bool // v = spec e} ← match same : e with
    | .app f a | .lam _ f a _ | .forallE _ f a _ => do
      let first ← go bucket f
      if found : first.1 = true then
        pure ⟨true, by simp [same, spec, ← first.2, found]⟩
      else
        let second ← go bucket a
        pure ⟨second.1, by simp [same, spec, ← first.2, found, second.2]⟩
    | .letE _ type value body _ => do
      let first ← go bucket type
      if found : first.1 = true then
        pure ⟨true, by simp [same, spec, ← first.2, found]⟩
      else
        let second ← go bucket value
        if foundNext : second.1 = true then
          pure ⟨true, by simp [same, spec, ← first.2, ← second.2, found, foundNext]⟩
        else
          let third ← go bucket body
          pure ⟨third.1, by simp [same, spec, ← first.2, ← second.2, found, foundNext, third.2]⟩
    | .proj _ _ inner => do
      let child ← go bucket inner
      pure ⟨child.1, by simpa [same, spec] using child.2⟩
    | .mdata data inner => do
      if present : (!(Ix.SemanticContract.leanFields data).isEmpty) = true then
        pure ⟨true, by simp [same, spec, present]⟩
      else
        let child ← go bucket inner
        pure ⟨child.1, by simp [same, spec, present, child.2]⟩
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ =>
      pure ⟨false, by simp [same, spec]⟩
  modify fun memo => memo.insert key ⟨e, result.1, result.2⟩
  return result

def runWith (bucket : Lean.Expr → USize) (e : Lean.Expr) : Bool :=
  (Id.run ((go bucket e).run' {})).1

def run (e : Lean.Expr) : Bool := runWith CanonM.leanExprPtr e

theorem go_result (bucket : Lean.Expr → USize) (e : Lean.Expr) (memo : Memo) :
    (Id.run ((go bucket e).run memo)).1.1 = spec e :=
  (Id.run ((go bucket e).run memo)).1.2

theorem runWith_eq_spec (bucket : Lean.Expr → USize) (e : Lean.Expr) :
    runWith bucket e = spec e := (Id.run ((go bucket e).run' {})).2

theorem run_eq_spec (e : Lean.Expr) : run e = spec e := runWith_eq_spec _ e

end Ix.Compile.SemanticPresence
