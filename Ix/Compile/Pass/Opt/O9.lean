/- # O9: structural recursion over a split block with a cross field (the Ix `brecOn` with re-pathed handlers)

## Contract
Input: an occurrence `x.brecOn.{u,us} ps ms is t Fs e` (Lean's telescope
`np + nm + ni + 1 + nm`, then `e`) in the value of a definition `c`
(`Occ.site`), where `x` is a member of a changed block `b` that is **split
and not collapsed**, `x`'s Ix component is `{x}` alone (`img(x.rec)` has one
Ix motive, Lean's motive of `x`), Lean's recursor has one motive per member
(no nested auxiliary), and some constructor of `x` has a field into another
component, so `img(x.rec)` is not a selection (O4's case) but a head shape
whose minors relocate the cross hypotheses (§4.2 step 4.2). Structural
recursion elaborates to exactly this: `c := λ xs. x.brecOn ms t c._f F′s`,
with `c._f : (t : x) → x.below ms t → R` (`@[reducible]`).

Lean's `x.below ms (k fs)` at a constructor `k` is the right-nested
`PProd` of one leaf `PProd (m_f f) (below f)` per field `f` whose type is a
member of the Lean block (no leaf: `PUnit`; one leaf: the leaf itself),
measured on Lean 4.34.1 (`pp.explicit`). The Ix `ρ.below msel (k fs)` of
the component has the leaves of the fields into the component only (Pass
2 builds it by Lean's construction on the canonical component, aux-oracle
gate). So a handler reads field `f`'s recursive value at a **path**: Lean's
`.2ʲ.1.1` (`.2ʲ.1` for the last leaf `j = k-1`), Ix's `.2ʲ′.1.1` with `j′`
the position of `f` among the component's leaves.

Output: `ρ.brecOn.{u,us} ps msel is t F′ e` with `msel` the component's
motive (`img(x.rec)`'s selection), `ρ.brecOn` the Ix `brecOn` (D14 display
name) and `F′` the major's handler **re-typed**: every `x.below ps ms is s`
replaced by `ρ.below ps msel is s`, and every path into a below value at a
constructor re-pathed `.2ʲ.1.1 ↦ .2ʲ′.1.1`. When Lean's handler is a
constant `g` (`c._f`), `F′` is the canonical constant `g′` (reserved name
`p._ix_retyped.s` for `g = p.s`, D14) with the re-typed type and value and `g`'s
hints, emitted with the block (`Translate.RwState.canon`); a λ handler is
re-typed in place. The handlers of the other components are dropped.

## Faithfulness (proof-justified; the statement Phase B formalises)
Let `B := x.brecOn ps ms is · Fs` (Lean's, over `img(x.rec)`, Def 3.5) and
`B′ := ρ.brecOn ps msel is · F′`. **Lemma O9.** Under the side condition,
`∀ is t, B is t = B′ is t` (in `m_x is t`).

*Proof*, by induction on `t` with `ρ` (the component's recursor), at the
Prop motive `λ is t. B is t = B′ is t`. Both `brecOn`s satisfy their
equation lemma (Lean's `x.brecOn.eq`, the Ix `ρ.brecOn.eq`, Pass 2):
`B is t = F_x is t (L is t)` and `B′ is t = F′ is t (L′ is t)`, `L`, `L′`
the below values Lean's and the Ix `brecOn.go` build. Case `t = k fs`:
* `L (k fs)` is the Lean tuple whose leaf for field `f` is `⟨B f, L f⟩`
  (cross fields included, computed with the other components' handlers),
  `L′ (k fs)` the Ix tuple with leaves `⟨B′ f, L′ f⟩` for the component's
  fields only (ι of both `below`/`go` at a constructor);
* the side condition says every occurrence of the below value in `F_x`'s
  body at `k` is under a path `.2ʲ.1.1` to a component field `f` (never a
  cross field, never the whole value, never a `.2` into the nested below),
  and `F′`'s body is `F_x`'s with those paths replaced by `.2ʲ′.1.1` and
  the below types replaced; so `F_x (k fs) (L (k fs)) ≡βπ body[v_f := B f]`
  and `F′ (k fs) (L′ (k fs)) ≡βπ body[v_f := B′ f]` (after the matcher's ι at
  `k`, which both sides share);
* by the induction hypotheses `B f = B′ f` for every component field `f`
  (they are exactly the recursive fields of `ρ`), so the two sides are
  equal by `congrArg (λ v⃗. body[v⃗])`.
∎ The baseline occurrence is `img(x.brecOn) a⃗ ≡δβ B is t e`, the output is
`B′ is t e` (congruence for `e`). **Corollary**: the rewritten `c` equals
`base(c)` by `funext` and `congrArg`. The canonical `g′` is a new
constant: it is `g` re-typed, and the lemma's `F′` is `g′` by δ; `g` itself
keeps its Lean name, type and value (faithful).

**Where the output goes (decision 5, D1).** The output is written into the
canonical form `c._ix` (Lean's `c` renamed, with `c`'s type), which then
reads `ρ.brecOn … c._ix_retyped._f`, Lean's own shape over the canonical component;
the Lean name `c` keeps its baseline (the image's `brecOn` over Lean's
handler `c._f`, convertible to Lean's term) and is recorded non-canonical
with the cause O9. The proof term of `c._ix = c` is the Corollary
(`funext`, `congrArg` with Lemma O9, an induction with `ρ` that uses both
`brecOn` equation lemmas); the forms are not convertible at an open major
(the below values have different layouts), only at closed values (both
`brecOn`s compute by ι). No caller is read: an open unfolding of `c` at a
constructor (`len_succ : (A.a b x).len = x.len + 1 := rfl`) checks against
`c`'s unchanged form.

## Canonicity
For the canonical twin (the component declared alone, the block's universes
and parameters kept), Lean elaborates the same function to `ρ.brecOn msel t
c._f` with `c._f`'s body over the component's below: the paths are the
re-pathed ones and the rest of the term is the same up to the renaming
(ORA §3, `A.len._f`: "the only term difference is the path into `below`").
The output depends on the image's selection (canonical), the leaf layout
of the canonical component, and the arguments; the reference and sharing
tables are derived from the final term (§4.7 (e)).

## Side condition and fallback
Decidable: `classify` gives `brecOn`; `b` split, not collapsed; `img(x.rec)`
has a head shape that is not a selection, with one Ix motive; Lean's
recursor has one motive per member; Lean's `brecOn` has the standard
telescope and the recursor's universe parameters; `m ≥ n`; O5 accepts the
levels; `ρ.brecOn` and `ρ.below` resolve; every constructor field of `x`
is either not about the block, or a member of the block (no nested or
reflexive occurrence); the major's handler is a λ or a definition `g`, and
re-typing succeeds (every below path re-pathable, no other occurrence of a
below value at a constructor, no Lean `below`/`brecOn` of the block left);
`pjAllowed` (the value of a definition). Otherwise no `c._ix` is emitted
for the occurrence (the image's `brecOn`, faithful).

## Non-canonical set and evidence
Lean's `c._f` keeps its Lean type (over Lean's `below`): faithful, and not
the twin's (`ORDER-STMT`-like: a statement that follows the grouping);
its canonical counterpart is `c._ix_retyped._f`. A handler that reads a cross
field's recursive value (a clique over the split block, C2's `A.cnt` with
`B.cnt`) declines: that is O14's repacking over a split block (A5).
Evidence: `Tests/Ix/Compile/Pass/O9Split.lean` (twin pairs byte-equal with
the switch on for the `_ix` forms, the Lean names unchanged and recorded,
value pins and an open unfolding by `rfl`, checked by the three kernels). Library load 0.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O4
public import Ix.Compile.Pass.Opt.O5
public import Ix.Compile.Pass.Opt.Packed
public import Ix.Compile.Pass.Names
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo DefinitionVal)
open Ix.Compile.Canon (mkAppN getAppFnArgs stripMdata mentionsAnyName)

/-- For one constructor: Lean's below leaves (one per field whose type is a
member of the block, in field order), each mapped to its Ix leaf (a field
into the component) or `none` (a cross field); and the Ix leaf count. -/
structure LeafMap where
  map : Array (Option Nat)
  ixLeaves : Nat
  deriving Inhabited

/-- The leaf map of constructor `k` of `x` (component `{x}`), or `none` when
a field mentions the block other than as a member applied (nested,
reflexive). -/
def leafMapOf (const? : Name → Option ConstantInfo) (all : Array Name) (x : Name) (np : Nat)
    (k : Name) : Option LeafMap := do
  let some (.ctorInfo cv) := const? k | none
  let blk : Std.HashSet Name := all.foldl (·.insert ·) {}
  let mut ty := cv.cnst.type
  for _ in [0:np] do
    match stripMdata ty with
    | .forallE _ _ b _ _ => ty := b
    | _ => none
  let mut map : Array (Option Nat) := #[]
  let mut n := 0
  for _ in [0:cv.numFields] do
    match stripMdata ty with
    | .forallE _ d b _ _ =>
      match (getAppFnArgs (stripMdata d)).1 with
      | .const h _ _ =>
        if blk.contains h then
          if h == x then
            map := map.push (some n)
            n := n + 1
          else map := map.push none
        else if mentionsAnyName blk d then none
      | _ => if mentionsAnyName blk d then none
      ty := b
    | _ => none
  return { map, ixLeaves := n }

/-- The data of one re-typing. -/
structure Retype where
  /-- Lean's `x.below`. -/
  belowN : Name
  /-- Its argument count (`np + nm + ni + 1`). -/
  nArgs : Nat
  np : Nat
  nm : Nat
  /-- The Ix `ρ.below`. -/
  ixBelow : Name
  /-- The recursor shape (selection and O5's level rule). -/
  shape : RecShape
  /-- The constructors of `x` and their leaf maps. -/
  leaves : Std.HashMap Name LeafMap
  /-- The block's Lean `below`/`brecOn` family: must not remain. -/
  forbidden : Std.HashSet Name

/-- The constructor of a below type at a constructor (`x.below ps ms is (k fs)`). -/
def Retype.atCtor (rt : Retype) (ty : Expr) : Option LeafMap := do
  let (h, args) := getAppFnArgs (stripMdata ty)
  let .const n _ _ := h | none
  if n != rt.belowN || args.size != rt.nArgs then none
  let .const k _ _ := (getAppFnArgs (stripMdata args.back!)).1 | none
  rt.leaves.get? k

/-- A chain of projections ending in a variable: the variable's index and
the projections (index, structure), innermost first. -/
def projChain : Expr → List (Nat × Name) → Option (Nat × List (Nat × Name))
  | .proj s i e _, acc =>
    match e with
    | .bvar k _ => some (k, (i, s) :: acc)
    | _ => projChain e ((i, s) :: acc)
  | _, _ => none

/-- Re-path Lean's path (innermost first) to a field's recursive value:
`.2ʲ.1.1 …` (`.2ʲ.1 …` at the last leaf) ↦ the Ix path to the same value
(`.1` included), and the length of the copied remainder `…`. -/
def repath (lm : LeafMap) (path : List Nat) : Option (List Nat × Nat) := do
  let k := lm.map.size
  if k == 0 then none
  -- leading `.2`s select the leaf
  let mut j := 0
  let mut p := path
  while j + 1 < k do
    match p with
    | 1 :: rest => j := j + 1; p := rest
    | _ => break
  if j + 1 < k then
    match p with
    | 0 :: rest => p := rest
    | _ => none
  -- the leaf's `.1`: the recursive value
  let rest ← match p with
    | 0 :: rest => some rest
    | _ => none
  let j' ← (lm.map[j]?).join
  let sel := List.replicate j' 1 ++ (if j' + 1 < lm.ixLeaves then [0] else [])
  return (sel ++ [0], rest.length)

/-- Re-type a term (see the module docstring); `ctx` gives the leaf map of
each bound variable typed as a below value at a constructor. -/
def Retype.go (rt : Retype) : Nat → List (Option LeafMap) → Expr → Option Expr
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
    match e with
    | .bvar k _ => match ctx[k]? with
      | some (some _) => none
      | _ => some e
    | .const n _ _ => if rt.forbidden.contains n then none else some e
    | .app .. => do
      let (h, args) := getAppFnArgs e
      match h with
      | .const n us _ =>
        if n == rt.belowN && args.size == rt.nArgs then
          let args' ← args.mapM (rt.go fuel ctx)
          let ls ← O5.levels rt.shape us
          let ms ← pick (args'.extract rt.np (rt.np + rt.nm)) rt.shape.motiveSrc
          return mkAppN (Expr.mkConst rt.ixBelow ls)
            (args'.extract 0 rt.np ++ ms ++ args'.extract (rt.np + rt.nm) args'.size)
        if rt.forbidden.contains n then none
        let args' ← args.mapM (rt.go fuel ctx)
        return mkAppN h args'
      | _ =>
        let h' ← rt.go fuel ctx h
        let args' ← args.mapM (rt.go fuel ctx)
        return mkAppN h' args'
    | .proj s i x _ =>
      match projChain e [] with
      | some (k, chain) =>
        match ctx[k]?, chain.head? with
        | some (some lm), some (_, pprod) => do
          -- `chain` is innermost first; the leaf part is `PProd`, the rest is copied
          let (sel, restLen) ← repath lm (chain.map (·.1))
          let rest := chain.drop (chain.length - restLen)
          let inner := sel.foldl (fun acc j => Expr.mkProj pprod j acc) (Expr.mkBVar k)
          return rest.foldl (fun acc (j, sn) => Expr.mkProj sn j acc) inner
        | _, _ => do return Expr.mkProj s i (← rt.go fuel ctx x)
      | none => do return Expr.mkProj s i (← rt.go fuel ctx x)
    | .lam n t b bi _ => do
      let t' ← rt.go fuel ctx t
      let b' ← rt.go fuel (rt.atCtor t :: ctx) b
      return Expr.mkLam n t' b' bi
    | .forallE n t b bi _ => do
      let t' ← rt.go fuel ctx t
      let b' ← rt.go fuel (rt.atCtor t :: ctx) b
      return Expr.mkForallE n t' b' bi
    | .letE n t v b nd _ => do
      let t' ← rt.go fuel ctx t
      let v' ← rt.go fuel ctx v
      let b' ← rt.go fuel (none :: ctx) b
      return Expr.mkLetE n t' v' b' nd
    | .mdata md x _ => do return Expr.mkMData md (← rt.go fuel ctx x)
    | _ => some e

/-- The recursion bound of a re-typing: far above any handler's depth. -/
def retypeFuel : Nat := 1 <<< 16

/-- The reserved name of the re-typed handler for the Lean constant `p.s`:
`p._ix_retyped.s` (D14, `Names.retypedName`; distinct from the clique
hook's `p._ix.s`). -/
def reservedOf : Name → Option Name := retypedName

def O9.apply (env : OptEnv) (o : Occ) : Option (Expr × Array ConstantInfo) := do
  let (k, r) ← classify o.head
  if k != .kBRecOn then none
  let b ← env.blockOf o.head
  if !b.change.split || b.change.collapse then none
  let s ← b.shapes.get? r
  if s.isSelection then none
  let some (.recInfo rv) := env.const? r | none
  if rv.numMotives != b.all.size then none
  if s.motiveSrc.size != 1 then none
  let mi ← s.motiveSrc[0]?
  let x ← b.all[mi]?
  if r != recNameOf x none then none
  let n ← standardTelescope env s .kBRecOn o.head
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let ixBRecOn ← ixAuxOf s.ixRec .kBRecOn
  let ixBelow ← ixAuxOf s.ixRec .kBelow
  if !env.resolves ixBRecOn || !env.resolves ixBelow then none
  let some (.inductInfo iv) := env.const? x | none
  let mut leaves : Std.HashMap Name LeafMap := {}
  for c in iv.ctors do
    leaves := leaves.insert c (← leafMapOf env.const? b.all x s.np c)
  let forbidden : Std.HashSet Name := b.all.foldl (init := {}) fun acc m =>
    acc.insert (Name.mkStr m "below") |>.insert (Name.mkStr m "brecOn")
  let rt : Retype := { belowN := belowNameOf r, nArgs := s.np + s.nm + s.ni + 1, np := s.np,
                       nm := s.nm, ixBelow, shape := s, leaves, forbidden }
  let a := o.args
  let ps := a.extract 0 s.np
  let ms ← pick (a.extract s.np (s.np + s.nm)) s.motiveSrc
  let tail := a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1)
  let hs := a.extract (s.np + s.nm + s.ni + 1) n
  let rest := a.extract n a.size
  let h ← hs[mi]?
  let (h', canon) ← match h with
    | .const g gus _ => do
      let some (.defnInfo gv) := env.const? g | none
      let ty' ← rt.go retypeFuel [] gv.cnst.type
      let v' ← rt.go retypeFuel [] gv.value
      let g' ← reservedOf g
      let dv : DefinitionVal :=
        { gv with cnst := { gv.cnst with name := g', type := ty' }, value := v', all := #[g'] }
      pure (Expr.mkConst g' gus, #[ConstantInfo.defnInfo dv])
    | _ => do pure (← rt.go retypeFuel [] h, #[])
  if !pjAllowed o then none
  return (mkAppN (Expr.mkConst ixBRecOn ls) (ps ++ ms ++ tail ++ #[h'] ++ rest), canon)

end Ix.Compile.Pass.Opt

end
