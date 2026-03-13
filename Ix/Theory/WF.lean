/-
  Ix.Theory.WF: Well-formedness predicates for specification values.

  ValWF v d asserts that all fvar levels in v are below d,
  and all closure bodies are well-scoped relative to their environments.
-/
import Ix.Theory.Quote

namespace Ix.Theory

variable {L : Type}

mutual
/-- A value is well-formed at depth d. -/
inductive ValWF : SVal L → Nat → Prop where
  | sort : ValWF (.sort u) d
  | lit : ValWF (.lit n) d
  | lam : ValWF dom d → SExpr.ClosedN body (env.length + 1) →
          EnvWF env d → ValWF (.lam dom body env) d
  | pi : ValWF dom d → SExpr.ClosedN body (env.length + 1) →
         EnvWF env d → ValWF (.pi dom body env) d
  | neutral : HeadWF hd d → ListWF spine d → ValWF (.neutral hd spine) d

/-- A head is well-formed at depth d. -/
inductive HeadWF : SHead L → Nat → Prop where
  | fvar : level < d → HeadWF (.fvar level) d
  | const : HeadWF (.const cid levels) d

/-- A list of values is well-formed at depth d. -/
inductive ListWF : List (SVal L) → Nat → Prop where
  | nil : ListWF [] d
  | cons : ValWF v d → ListWF vs d → ListWF (v :: vs) d

/-- An environment is well-formed at depth d. -/
inductive EnvWF : List (SVal L) → Nat → Prop where
  | nil : EnvWF [] d
  | cons : ValWF v d → EnvWF env d → EnvWF (v :: env) d
end

/-! ## Monotonicity: well-formedness is preserved when depth increases -/

mutual
def ValWF.mono (h : d ≤ d') : ValWF v d → ValWF (L := L) v d'
  | .sort => .sort
  | .lit => .lit
  | .lam hd hc he => .lam (hd.mono h) hc (he.mono h)
  | .pi hd hc he => .pi (hd.mono h) hc (he.mono h)
  | .neutral hh hs => .neutral (hh.mono h) (hs.mono h)

def HeadWF.mono (h : d ≤ d') : HeadWF hd d → HeadWF (L := L) hd d'
  | .fvar hl => .fvar (Nat.lt_of_lt_of_le hl h)
  | .const => .const

def ListWF.mono (h : d ≤ d') : ListWF l d → ListWF (L := L) l d'
  | .nil => .nil
  | .cons hv hs => .cons (hv.mono h) (hs.mono h)

def EnvWF.mono (h : d ≤ d') : EnvWF env d → EnvWF (L := L) env d'
  | .nil => .nil
  | .cons hv he => .cons (hv.mono h) (he.mono h)
end

/-! ## Environment lookup preserves WF -/

def EnvWF.getElem? : EnvWF env d → (h_i : i < env.length) →
    ∃ v, env[i]? = some v ∧ ValWF (L := L) v d
  | .cons hv _, (h : i < _ + 1) => match i, h with
    | 0, _ => ⟨_, rfl, hv⟩
    | j + 1, h => by
      simp [List.getElem?_cons_succ]
      exact EnvWF.getElem? (by assumption) (Nat.lt_of_succ_lt_succ h)
  | .nil, h => absurd h (Nat.not_lt_zero _)

/-! ## ListWF append/snoc -/

def ListWF.append : ListWF l1 d → ListWF l2 d → ListWF (L := L) (l1 ++ l2) d
  | .nil, h2 => h2
  | .cons hv hs, h2 => .cons hv (hs.append h2)

theorem ListWF.snoc (h1 : ListWF l d) (h2 : ValWF (L := L) v d) : ListWF (l ++ [v]) d :=
  h1.append (.cons h2 .nil)

end Ix.Theory
