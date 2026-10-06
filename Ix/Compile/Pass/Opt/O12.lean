/- # O12: structural recursion over a collapsed pair with different arms (the shared pair-valued helper `fg`)

## Contract
Input: an occurrence `x.brecOn.{u} ms t Fs e` over a collapsed, unsplit
block `b` (`Opt.CollapseRec`) in the value of a definition `c` (`Occ.site`),
where O10 declined (the two arms differ): the block has **one slot** whose
class has **two** members `A`, `B` (no parameters, no indices; Lean's
motives and handlers closed terms; the motive universe `u` not `0` and the
universe arguments without parameters). Lean's functions are `A.f := λ t.
A.brecOn mA mB t A.f._f B.g._f` and `B.g := λ t. B.brecOn mA mB t A.f._f
B.g._f`.

Output: `proj_{pos(x)} (fg t) e` with the canonical constants (emitted with
the block, reserved names, D14):
* `fg := λ (t : X). ρ.brecOn.{max 1 u} Pair t G : (t : X) → PProd (m₀ t)
  (m₁ t)`, the **shared pair-valued helper**, where `Pair := λ t. PProd (m₀
  t) (m₁ t)` and `G := λ t f. ⟨F′₀ t f, F′₁ t f⟩`;
* `F′ᵢ`: the handlers re-typed over the Ix below at `Pair` (`p._ix_retyped.s` for
  Lean's `p.s`), a leaf value of member `j` read as `.1` then the pair's
  component of `j` (`.1`/`.2`).
The pair's order `(m₀, m₁)` is **by content**: each member's handler is
re-typed with its own component first (a form that does not depend on the
order), and the member whose form is smaller (`canonKey`: binder names
dropped, constants by compiled address) comes first; equal forms give the
same `fg` in either order. `A.f := λ t. (fg t).1` (or `.2`).

## Faithfulness (proof-justified; the statement Phase B formalises)
Write `B_A t := A.brecOn mA mB t F_A F_B`, `B_B t := B.brecOn mA mB t F_A F_B`
(Lean's, over the images). **Lemma O12** (joint induction; the old plan's
"pair form"). For every `t : X`:

    (fg t).1 = B_{m₀} t   ∧   (fg t).2 = B_{m₁} t

*Proof*, by induction on `t` with `ρ` at the Prop motive `λ t. (fg t).1 =
B₀ t ∧ (fg t).2 = B₁ t`. `fg t ≡δβ ρ.brecOn Pair t G`, and by Pass 2's
`ρ.brecOn.eq` it equals `G t (L′ t) = ⟨F′₀ t (L′ t), F′₁ t (L′ t)⟩` with
`L′ t` the Ix below value at `Pair`; by Lean's `M.brecOn.eq`, `B_i t = F_i t
(L_i t)`. Case `t = c fs`: the leaves of `L′ (c fs)` are `⟨fg f, L′ f⟩`, those
of `L_i (c fs)` are `⟨B_j f, L_j f⟩` (`j` the member of field `f`'s type).
`F′ᵢ` is `F_i` with each leaf value `.1` replaced by `.1.(pos j)` and the
below types replaced, and every use of a below value at a constructor is
such a path (side condition), so `F′ᵢ (c fs) (L′ (c fs)) ≡βπ body_i[v_f :=
(fg f).(pos j)]` and `F_i (c fs) (L_i (c fs)) ≡βπ body_i[v_f := B_j f]`; by
the induction hypothesis `(fg f).(pos j) = B_j f`, so the components are
equal by `congrArg`, and the pair's projections give the two equations. ∎
The baseline occurrence is `img(x.brecOn) a⃗ ≡δβ B_x t e`; the output is
`(fg t).(pos x) e` (congruence). **Corollary**: the rewritten `c` equals
`base(c)` by `funext` and `congrArg`.

**Where the output goes (decision 5, D1).** The output `(fg t).(pos x)` is
written into the canonical forms `A.f._ix`, `B.g._ix` (Lean's functions
renamed, with their types); the Lean names `A.f`, `B.g` keep their baselines
(the image's `brecOn`, convertible to Lean's term) and are recorded
non-canonical (cause O12; against the collapsed twin they have no
counterpart at all, `COLLAPSE-ARMS`). The proof term of `A.f._ix = A.f` is
the Corollary (`funext`, `congrArg` with the conjunct of Lemma O12, the
joint induction with `ρ`); not convertible at open terms, equal by ι at
closed ones (`fg` unfolds, `ρ.brecOn` computes). No caller is read; the
content order reads the canonical forms of the handlers' references
(`OptEnv.canonAddrOf`).

## Canonicity
`fg` depends on the class (canonical), the image's `ρ`, the motives and the
handlers' bodies only, and the pair order is a function of the content, so
the permuted presentation (the members and functions declared in the other
order) gives the same `fg`, and the same `A.f._ix`, `B.g._ix`. The Lean names
`A.f`, `B.g` have no counterpart in the collapsed twin (one inductive, one
pair-valued function), so they are faithful only (`COLLAPSE-ARMS`); `fg` is
the canonical constant.

## Side condition and fallback
Decidable: `readCollapseRec`; one slot of two members; no parameters or
indices; motives and handlers closed; the motive universe not `0`, no level
parameters; both handlers definitions; re-typing succeeds (every below
value at a constructor used through a leaf-value path); `ρ.brecOn`, `ρ.below`
resolve; `pjAllowed` (the value of a definition). Otherwise no `_ix` form
is emitted for the occurrence (the faithful paired image).
Classes of three or more members (C8b) are declined: the content order of
the other members would need a canonical order of the remaining
components (recorded `COLLAPSE-ARMS`).

## Non-canonical set and evidence
`COLLAPSE-ARMS`: the Lean names over a collapsed pair with different arms
(against the collapsed twin); classes of three. Evidence:
`Tests/Ix/Compile/Pass/O10O12Collapse.lean` (C5's `A.f`/`B.g` against the
permuted presentation: `fg`, `A.f`, `B.g` byte-equal; value pins). Library
load 0.
-/
module
public import Ix.Compile.Pass.Opt.CollapseRec
public import Ix.Compile.Image.Develop
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo DefinitionVal)
open Ix.Compile.Canon (mkAppN substLevel normalizeLevel looseAtLeast)

def levelKey : Level → String
  | .zero _ => "0"
  | .succ l _ => s!"s({levelKey l})"
  | .max a b _ => s!"m({levelKey a},{levelKey b})"
  | .imax a b _ => s!"i({levelKey a},{levelKey b})"
  | .param n _ => s!"p({n.pretty})"
  | .mvar n _ => s!"v({n.pretty})"

def levelHasParam : Level → Bool
  | .succ l _ => levelHasParam l
  | .max a b _ | .imax a b _ => levelHasParam a || levelHasParam b
  | .param .. | .mvar .. => true
  | _ => false

/-- A content key of a term: binder names and metadata dropped, constants by
compiled address (by name when not compiled). -/
def canonKey (addr? : Name → Option Address) : Expr → String
  | .bvar i _ => s!"#{i}"
  | .sort l _ => s!"S{levelKey l}"
  | .const n ls _ =>
    let c := match addr? n with
      | some a => toString a
      | none => n.pretty
    s!"C{c}" ++ ls.foldl (fun s l => s ++ "." ++ levelKey l) ""
  | .app f a _ => s!"({canonKey addr? f} {canonKey addr? a})"
  | .lam _ t b _ _ => s!"(L {canonKey addr? t} {canonKey addr? b})"
  | .forallE _ t b _ _ => s!"(P {canonKey addr? t} {canonKey addr? b})"
  | .letE _ t v b _ _ => s!"(Z {canonKey addr? t} {canonKey addr? v} {canonKey addr? b})"
  | .lit l _ => match l with
    | .natVal n => s!"N{n}"
    | .strVal s => s!"T{s.length}:{s}"
  | .mdata _ e _ => canonKey addr? e
  | .proj s i e _ =>
    let c := match addr? s with
      | some a => toString a
      | none => s.pretty
    s!"(J{c}.{i} {canonKey addr? e})"
  | e => s!"?{e.getHash}"

/-- `m t` with a λ motive β-reduced. -/
def applyMotive (m t : Expr) : Option Expr :=
  match Ix.Compile.Image.instantiate m #[t] with
  | .ok e => some e
  | .error _ => none

def O12.apply (env : OptEnv) (o : Occ) : Option (Expr × Array ConstantInfo) := do
  let cr ← readCollapseRec env o
  let s := cr.s
  if s.slots.size != 1 || s.np != 0 || s.ni != 0 then none
  let cls ← s.slots[0]?
  if cls.size != 2 then none
  if o.us.any levelHasParam then none
  -- closed motives and handlers (no variable of the site)
  let closed := fun (e : Expr) => looseAtLeast e (1 <<< 62)
  if !(cr.ms.all closed && cr.hs.all closed) then none
  let u ← o.us[0]?
  if Ix.Compile.Image.isAlwaysZero u then none
  let i0 ← cls[0]?
  let i1 ← cls[1]?
  -- the major's type (the motives' binder)
  let .lam _ T _ _ _ := (← cr.ms[i0]?) | none
  let ls := s.ixLevels.map (substLevel s.levelParams o.us)
  let ixBRecOn ← ixAuxOf s.ixRec .kBRecOn
  if !env.resolves ixBRecOn then none
  let nPProd := Ix.Compile.Image.nPProd
  let pairOf : Array Nat → Option Expr := fun ord => do
    let a ← applyMotive (← cr.ms[ord[0]!]?) (Expr.mkBVar 0)
    let b ← applyMotive (← cr.ms[ord[1]!]?) (Expr.mkBVar 0)
    pure (Expr.mkLam (Name.mkStr Name.mkAnon "t") T
      (mkAppN (Expr.mkConst nPProd #[u, u]) #[a, b]) .default)
  let retypeFor : Array Nat → Option CRetype := fun ord => do
    let pair ← pairOf ord
    let pos := fun (j : Nat) => if j == ord[0]! then [0] else [1]
    cr.retype env #[pair] (fun _ => some ls) (some pos)
  -- the content order: each handler re-typed with its own component first
  let keyOf : Nat → Nat → Option String := fun i other => do
    let rt ← retypeFor #[i, other]
    let (h, cs) ← retypeHandler env rt (← cr.hs[i]?)
    let v := (cs[0]?.bind fun c => match c with | .defnInfo d => some d.value | _ => none).getD h
    pure (canonKey env.canonAddrOf v)
  let k0 ← keyOf i0 i1
  let k1 ← keyOf i1 i0
  let ord : Array Nat := if k1 < k0 then #[i1, i0] else #[i0, i1]
  let pair ← pairOf ord
  let rt ← retypeFor ord
  let (f0, c0) ← retypeHandler env rt (← cr.hs[ord[0]!]?)
  let (f1, c1) ← retypeHandler env rt (← cr.hs[ord[1]!]?)
  let .const g0 _ _ := (← cr.hs[ord[0]!]?) | none
  let .str gp _ _ := g0 | none
  let fgName := Name.mkStr (Name.mkStr gp ixComponent) "fg"
  -- G := λ (t : X) (f : ρ.below Pair t). ⟨F′₀ t f, F′₁ t f⟩
  let ixBelow ← ixAuxOf s.ixRec .kBelow
  let belowT := mkAppN (Expr.mkConst ixBelow ls) #[pair, Expr.mkBVar 0]
  let m0t ← applyMotive (← cr.ms[ord[0]!]?) (Expr.mkBVar 1)
  let m1t ← applyMotive (← cr.ms[ord[1]!]?) (Expr.mkBVar 1)
  let gBody := mkAppN (Expr.mkConst Ix.Compile.Image.nPProdMk #[u, u])
    #[m0t, m1t, mkAppN f0 #[Expr.mkBVar 1, Expr.mkBVar 0], mkAppN f1 #[Expr.mkBVar 1, Expr.mkBVar 0]]
  let G := Expr.mkLam (Name.mkStr Name.mkAnon "t") T
    (Expr.mkLam (Name.mkStr Name.mkAnon "f") belowT gBody .default) .default
  let fgValue := Expr.mkLam (Name.mkStr Name.mkAnon "t") T
    (mkAppN (Expr.mkConst ixBRecOn ls) #[pair, Expr.mkBVar 0, G]) .default
  let a0 ← applyMotive (← cr.ms[ord[0]!]?) (Expr.mkBVar 0)
  let a1 ← applyMotive (← cr.ms[ord[1]!]?) (Expr.mkBVar 0)
  let fgType := Expr.mkForallE (Name.mkStr Name.mkAnon "t") T
    (mkAppN (Expr.mkConst nPProd #[u, u]) #[a0, a1]) .default
  let fg : DefinitionVal :=
    { cnst := { name := fgName, levelParams := #[], type := fgType }, value := fgValue,
      hints := .abbrev, safety := .safe, all := #[fgName] }
  let xi ← cr.b.all.idxOf? cr.x
  let pos := if xi == ord[0]! then 0 else 1
  if !pjAllowed o then none
  let out := mkAppN (Expr.mkProj nPProd pos (Expr.mkApp (Expr.mkConst fgName #[]) (← cr.tail[0]?))) cr.rest
  return (out, c0 ++ c1 ++ #[.defnInfo fg])

end Ix.Compile.Pass.Opt

end
