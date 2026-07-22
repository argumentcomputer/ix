import Ix.Tc.Env
import Lean4Lean.Verify.VLCtx

/-!
# `KVLCtx` — the translation-side local context (M2)

The Ix.Tc analogue of lean4lean's `VLCtx`: a list of local declarations,
each optionally tagged with the `FVarId` that addresses it (plus that
entry's fvar dependency list, used by the M3 well-formedness layer).
Entries tagged `none` are addressable only by de Bruijn index — this is
what lets ONE context type absorb the checker's dual context (de Bruijn
`ctx`/`letVals` arrays + fvar `LocalContext`) in M3 (decision F6).

Design notes:
- `VLocalDecl` is reused from the upstream dep verbatim: it is
  `VExpr`-valued and fvar-agnostic (Theory-shaped despite living in
  upstream's Verify tree), so its `liftN`/`inst`/`instL` lemmas
  transfer. Only the fvar-keyed list structure is re-stated, keyed by
  `Ix.Tc.FVarId` (the checker's per-`TypeChecker` `UInt64` ids) instead
  of `Lean.FVarId`.
- `find?` mirrors upstream exactly: a bvar hit on a `vlam` produces
  `.bvar 0` lifted by the depth walked; a hit on a `vlet` produces the
  let VALUE (lifted) — let-bound variables are inlined at use sites,
  which is why `VExpr` has no `letE` constructor and `toCtx` drops
  `vlet` entries.
- Typing-level well-formedness (`KVLCtx.WF`) lives with the translation
  relation in `Verify/Trans.lean` (mirroring upstream's placement);
  only the fvar-structural `FVWF` is here.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLevel VLocalDecl)

/-- Translation-side local context: declarations optionally addressable
    by an `FVarId` (with its dependency list), innermost first. -/
def KVLCtx := List (Option (FVarId × List FVarId) × VLocalDecl)

namespace KVLCtx

/-- Number of de Bruijn-addressable (untagged) entries. -/
def bvars : KVLCtx → Nat
  | [] => 0
  | (none, _) :: Δ => bvars Δ + 1
  | (some _, _) :: Δ => bvars Δ

/-- All entries are fvar-tagged — the closed-by-fvars fragment. -/
abbrev NoBV (Δ : KVLCtx) : Prop := Δ.bvars = 0

/-- One step of variable resolution: `none` consumes a bvar level,
    `some fv` consumes a matching fvar reference. -/
def next : Option (FVarId × List FVarId) → Nat ⊕ FVarId →
    Option (Nat ⊕ FVarId)
  | none, .inl 0 => none
  | none, .inl (n+1) => some (.inl n)
  | some _, .inl n => some (.inl n)
  | none, .inr fv' => some (.inr fv')
  | some (fv, _), .inr fv' => if fv == fv' then none else some (.inr fv')

/-- Resolve a variable reference to its (value, type) pair, lifted to
    the reference site. The value of a `vlam` is `.bvar 0`; the value of
    a `vlet` is the let body — inlining lets at use sites. -/
def find? : KVLCtx → Nat ⊕ FVarId → Option (VExpr × VExpr)
  | [], _ => none
  | (ofv, d) :: Δ, v =>
    match next ofv v with
    | none => some (d.value, d.type)
    | some v => do
      let (e, A) ← find? Δ v
      some (e.liftN d.depth, A.liftN d.depth)

/-- Weakening action on variable references (fvars are unaffected). -/
def liftVar (n k : Nat) : Nat ⊕ FVarId → Nat ⊕ FVarId
  | .inl i => .inl (if i < k then i else i + n)
  | .inr fv => .inr fv

/-- The fvar ids declared in the context, innermost first. -/
def fvars (Δ : KVLCtx) : List FVarId := Δ.filterMap (·.1.map (·.1))

@[simp] theorem fvars_nil : fvars [] = [] := rfl

@[simp] theorem fvars_cons_none {Δ : KVLCtx} {d : VLocalDecl} :
    fvars ((none, d) :: Δ) = fvars Δ := rfl

@[simp] theorem fvars_cons_some {Δ : KVLCtx} {fv : FVarId × List FVarId}
    {d : VLocalDecl} : fvars ((some fv, d) :: Δ) = fv.1 :: fvars Δ := rfl

/-- The bare `VExpr` type context: `vlam` types only (`vlet`s do not
    create bvars on the `VExpr` side). -/
def toCtx : KVLCtx → List VExpr
  | [] => []
  | (_, .vlam ty) :: Δ => ty :: toCtx Δ
  | (_, .vlet _ _) :: Δ => toCtx Δ

/-- Universe-parameter instantiation, entrywise. -/
def instL (Δ : KVLCtx) (ls : List VLevel) : KVLCtx :=
  match Δ with
  | [] => []
  | (ofv, d) :: Δ => (ofv, d.instL ls) :: instL Δ ls

/-- Fvar-structural well-formedness: each tagged entry's id is fresh
    for the tail, and its recorded dependencies are declared in the
    tail. (Typing-level `WF` lives in `Verify/Trans.lean`.) -/
def FVWF : KVLCtx → Prop
  | [] => True
  | (ofv, _) :: (Δ : KVLCtx) =>
    FVWF Δ ∧ ∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars

end KVLCtx

end Ix.Tc
