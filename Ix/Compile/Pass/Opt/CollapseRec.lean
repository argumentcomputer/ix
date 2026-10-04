/- # Structural recursion over a collapsed block: shared data of O10 and O12

## Contract
Input: an occurrence `x.brecOn.{u,us} ps ms is t Fs e` (Lean's telescope
`np + nm + ni + 1 + nm`) in the value of a definition (`Occ.site`), where
`x` is a member of a changed block `b` that is **collapsed and not split**
(one component, no nested auxiliary, no evaporation). Structural recursion
over such a block elaborates to it: each function `fᵢ := λ t. Mᵢ.brecOn ms
t F⃗` with one handler per member, `Fᵢ = fᵢ._f : (t : Mᵢ) → Mᵢ.below ms t →
Rᵢ` (Lean 4.34.1, `pp.explicit`).

Output (no term is rewritten here): the reading every collapse pass of
structural recursion needs:
* the slot classes of `img(x.rec)` (`Opt.Packed`) and the Ix recursor of
  every slot (from the images of the members' recursors);
* **re-typing** of a handler: every Lean `M.below ps ms is s` (`M` a member)
  becomes `ρ_M.below ps Ms′ is s`, `ρ_M` the Ix recursor of `M`'s slot and
  `Ms′` the new motives (one per slot); a path into a below value at a
  constructor is mapped by `leafPath` (O10: the identity; O12: the leaf
  value `.1` followed by the projection of the field's member out of the
  slot's tuple). A collapse keeps every field of a constructor (one
  component), so Lean's below and the Ix below have the same leaves, in the
  same order (§4.2: members of a class are structurally equal);
* `agreeAddr`: equality after compilation of two re-typed handlers, where
  two constants agree when the collapse renaming makes them one name, or
  when both are already compiled to one address (matchers of the two
  functions, for instance, which O8 made the class's single-member form).

## Faithfulness
Nothing is rewritten here; see O10 and O12.

## Canonicity
The reading depends on Pass 1's classes, the images and the arguments;
`agreeAddr` reads compiled addresses of the arguments' constants, which are
compiled before the occurrence's block (they are its references).

## Side condition and fallback
A reading that fails makes the passes decline (the faithful baseline).

## Non-canonical set and evidence
See O10 and O12. Evidence: `Tests/Ix/Compile/Pass/O10O12Collapse.lean`.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O4
public import Ix.Compile.Pass.Opt.O9
public import Ix.Compile.Pass.Opt.Packed
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo DefinitionVal)
open Ix.Compile.Canon (mkAppN getAppFnArgs stripMdata replaceConstNames)

/-- Equality after compilation (see the module docstring): α-equality where
constants agree under the renaming or by their compiled addresses. -/
def agreeAddr (ren : Std.HashMap Name Name) (addr? : Name → Option Address) : Expr → Expr → Bool
  | .bvar i _, .bvar j _ => i == j
  | .sort u _, .sort v _ => u == v
  | .const a us _, .const b vs _ =>
    us == vs && (a == b || (ren.getD a a) == (ren.getD b b) ||
      (match addr? a, addr? b with
        | some x, some y => x == y
        | _, _ => false))
  | .app f a _, .app g b _ => agreeAddr ren addr? f g && agreeAddr ren addr? a b
  | .lam _ t b _ _, .lam _ t' b' _ _ => agreeAddr ren addr? t t' && agreeAddr ren addr? b b'
  | .forallE _ t b _ _, .forallE _ t' b' _ _ => agreeAddr ren addr? t t' && agreeAddr ren addr? b b'
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ =>
    agreeAddr ren addr? t t' && agreeAddr ren addr? v v' && agreeAddr ren addr? b b'
  | .lit a _, .lit b _ => a == b
  | .mdata _ a _, b => agreeAddr ren addr? a b
  | a, .mdata _ b _ => agreeAddr ren addr? a b
  | .proj s i a _, .proj s' i' b _ => (ren.getD s s) == (ren.getD s' s') && i == i' && agreeAddr ren addr? a b
  | _, _ => false

/-- The reading of a collapsed block's `brecOn` occurrence. -/
structure CollapseRec where
  b : OptBlock
  /-- The packed shape of the major's recursor. -/
  s : PackedShape
  /-- The major's member and its Lean motive index. -/
  x : Name
  /-- The slot of each Lean motive (member, by `all` index). -/
  slotOf : Array Nat
  /-- The Ix recursor of each slot. -/
  slotRec : Array Name
  /-- The Lean telescope's length (`np + nm + ni + 1 + nm`). -/
  n : Nat
  ps : Array Expr
  ms : Array Expr
  tail : Array Expr
  hs : Array Expr
  rest : Array Expr

/-- Read a `brecOn` occurrence over a collapsed, unsplit block. -/
def readCollapseRec (env : OptEnv) (o : Occ) : Option CollapseRec := do
  let (k, r) ← classify o.head
  if k != .kBRecOn then none
  let b ← env.blockOf o.head
  let ch := b.change
  if !ch.collapse || ch.split || ch.evaporation then none
  let some (.recInfo rv) := env.const? r | none
  if rv.numMotives != b.all.size then none
  let s ← b.packed? env r
  let flat := s.slots.foldl (· ++ ·) #[]
  if flat.size != s.nm || (List.range s.nm).any (!flat.contains ·) then none
  let x ← b.all.find? (recNameOf · none == r)
  let ci ← env.const? o.head
  if ci.getCnst.levelParams != s.levelParams then none
  let n := s.np + s.nm + s.ni + 1 + s.nm
  if forallArity ci.getCnst.type != n then none
  if o.args.size < n then none
  let mut slotOf : Array Nat := Array.replicate s.nm 0
  for (cls, kk) in s.slots.zipIdx do
    for i in cls do slotOf := slotOf.set! i kk
  -- the Ix recursor of each slot, from its members' images
  let mut slotRec : Array Name := #[]
  for cls in s.slots do
    let i ← cls[0]?
    let m ← b.all[i]?
    let sm ← b.packed? env (recNameOf m none)
    slotRec := slotRec.push sm.ixRec
  let a := o.args
  return { b, s, x, slotOf, slotRec, n
           ps := a.extract 0 s.np, ms := a.extract s.np (s.np + s.nm)
           tail := a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1)
           hs := a.extract (s.np + s.nm + s.ni + 1) n, rest := a.extract n a.size }

/-- For one constructor of a member: the Lean motive (member index) of each
below leaf (each field whose type is a member), or `none` when a field
mentions the block other than as a member applied. -/
def leafMembers (const? : Name → Option ConstantInfo) (all : Array Name) (np : Nat) (k : Name) :
    Option (Array Nat) := do
  let some (.ctorInfo cv) := const? k | none
  let blk : Std.HashSet Name := all.foldl (·.insert ·) {}
  let mut ty := cv.cnst.type
  for _ in [0:np] do
    match stripMdata ty with
    | .forallE _ _ b _ _ => ty := b
    | _ => none
  let mut out : Array Nat := #[]
  for _ in [0:cv.numFields] do
    match stripMdata ty with
    | .forallE _ d b _ _ =>
      match (getAppFnArgs (stripMdata d)).1 with
      | .const h _ _ =>
        match all.idxOf? h with
        | some i => out := out.push i
        | none => if Ix.Compile.Canon.mentionsAnyName blk d then none
      | _ => if Ix.Compile.Canon.mentionsAnyName blk d then none
      ty := b
    | _ => none
  return out

/-- How a re-typing maps a below value at a constructor: `none` keeps every
path (and allows bare uses: the two below types are the same after the
renaming), `some f` re-paths the leaf-value path of a leaf of Lean motive
`i` by appending `f i` after its `.1`, and forbids bare uses. -/
structure CRetype where
  /-- Lean's `M.below` of every member ↦ the member index. -/
  belows : Std.HashMap Name Nat
  nArgs : Nat
  np : Nat
  nm : Nat
  /-- The Ix `below` of each slot. -/
  ixBelow : Array Name
  slotOf : Array Nat
  /-- The new motives, one per slot. -/
  motives : Array Expr
  /-- The Ix `below`'s universe arguments at an occurrence's levels. -/
  levels : Array Level → Option (Array Level)
  /-- Each constructor of the block ↦ its leaves' Lean motives. -/
  leaves : Std.HashMap Name (Array Nat)
  /-- The re-path of a leaf value (`none`: identity). -/
  extra : Option (Nat → List Nat)
  /-- The block's other Lean `below`/`brecOn` names: must not remain. -/
  forbidden : Std.HashSet Name

def CRetype.atCtor (rt : CRetype) (ty : Expr) : Option (Array Nat) := do
  let (h, args) := getAppFnArgs (stripMdata ty)
  let .const n _ _ := h | none
  if !rt.belows.contains n || args.size != rt.nArgs then none
  let .const k _ _ := (getAppFnArgs (stripMdata args.back!)).1 | none
  rt.leaves.get? k

/-- Re-path a leaf-value path (innermost first, Lean's right-nested leaves,
`.2ʲ.1` then `.1`) for `extra`; the selection is unchanged (same leaves). -/
def crepath (lvs : Array Nat) (extra : Nat → List Nat) (path : List Nat) : Option (List Nat × Nat) := do
  let k := lvs.size
  if k == 0 then none
  let mut j := 0
  let mut p := path
  while j + 1 < k do
    match p with
    | 1 :: rest => j := j + 1; p := rest
    | _ => break
  let mut sel : List Nat := List.replicate j 1
  if j + 1 < k then
    match p with
    | 0 :: rest => p := rest; sel := sel ++ [0]
    | _ => none
  let rest ← match p with
    | 0 :: rest => some rest
    | _ => none
  let i ← lvs[j]?
  return (sel ++ [0] ++ extra i, rest.length)

def CRetype.go (rt : CRetype) : Nat → List (Option (Array Nat)) → Expr → Option Expr
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
    match e with
    | .bvar k _ => match ctx[k]?, rt.extra with
      | some (some _), some _ => none
      | _, _ => some e
    | .const n _ _ => if rt.forbidden.contains n || rt.belows.contains n then none else some e
    | .app .. => do
      let (h, args) := getAppFnArgs e
      match h with
      | .const n us _ =>
        if let some mi := rt.belows.get? n then
          if args.size != rt.nArgs then none
          let args' ← args.mapM (rt.go fuel ctx)
          let ls ← rt.levels us
          let sl ← rt.slotOf[mi]?
          let ixB ← rt.ixBelow[sl]?
          return mkAppN (Expr.mkConst ixB ls)
            (args'.extract 0 rt.np ++ rt.motives ++ args'.extract (rt.np + rt.nm) args'.size)
        if rt.forbidden.contains n then none
        return mkAppN h (← args.mapM (rt.go fuel ctx))
      | _ => return mkAppN (← rt.go fuel ctx h) (← args.mapM (rt.go fuel ctx))
    | .proj s i x _ =>
      match projChain e [], rt.extra with
      | some (k, chain), some ex =>
        match ctx[k]?, chain.head? with
        | some (some lvs), some (_, pprod) => do
          let (sel, restLen) ← crepath lvs ex (chain.map (·.1))
          let rest := chain.drop (chain.length - restLen)
          let inner := sel.foldl (fun acc j => Expr.mkProj pprod j acc) (Expr.mkBVar k)
          return rest.foldl (fun acc (j, sn) => Expr.mkProj sn j acc) inner
        | _, _ => do return Expr.mkProj s i (← rt.go fuel ctx x)
      | _, _ => do return Expr.mkProj s i (← rt.go fuel ctx x)
    | .lam n t b bi _ => do
      return Expr.mkLam n (← rt.go fuel ctx t) (← rt.go fuel (rt.atCtor t :: ctx) b) bi
    | .forallE n t b bi _ => do
      return Expr.mkForallE n (← rt.go fuel ctx t) (← rt.go fuel (rt.atCtor t :: ctx) b) bi
    | .letE n t v b nd _ => do
      return Expr.mkLetE n (← rt.go fuel ctx t) (← rt.go fuel ctx v) (← rt.go fuel (none :: ctx) b) nd
    | .mdata md x _ => do return Expr.mkMData md (← rt.go fuel ctx x)
    | _ => some e

/-- The re-typing data of a collapsed-block occurrence, for new motives
`motives` (one per slot), levels `levels` and leaf re-path `extra`. -/
def CollapseRec.retype (env : OptEnv) (cr : CollapseRec) (motives : Array Expr)
    (levels : Array Level → Option (Array Level)) (extra : Option (Nat → List Nat)) : Option CRetype := do
  let mut belows : Std.HashMap Name Nat := {}
  let mut leaves : Std.HashMap Name (Array Nat) := {}
  let mut forbidden : Std.HashSet Name := {}
  for (m, i) in cr.b.all.zipIdx do
    belows := belows.insert (Name.mkStr m "below") i
    forbidden := forbidden.insert (Name.mkStr m "brecOn")
    let some (.inductInfo iv) := env.const? m | none
    for c in iv.ctors do
      leaves := leaves.insert c (← leafMembers env.const? cr.b.all cr.s.np c)
  let ixBelow ← cr.slotRec.mapM (ixAuxOf · .kBelow)
  if ixBelow.any (!env.resolves ·) then none
  return { belows, nArgs := cr.s.np + cr.s.nm + cr.s.ni + 1, np := cr.s.np, nm := cr.s.nm,
           ixBelow, slotOf := cr.slotOf, motives, levels, leaves, extra, forbidden }

/-- Re-type a handler: a constant `g` (Lean's `f._f`) becomes the canonical
constant `p._ix.s` (`g = p.s`) with re-typed type and value; another term
is re-typed in place. -/
def retypeHandler (env : OptEnv) (rt : CRetype) (h : Expr) : Option (Expr × Array ConstantInfo) := do
  let (hd, args) := getAppFnArgs h
  match hd with
  | .const g gus _ =>
    let some (.defnInfo gv) := env.const? g | none
    let ty' ← rt.go retypeFuel [] gv.cnst.type
    let v' ← rt.go retypeFuel [] gv.value
    let g' ← reservedOf g
    let args' ← args.mapM (rt.go retypeFuel [])
    let dv : DefinitionVal :=
      { gv with cnst := { gv.cnst with name := g', type := ty' }, value := v', all := #[g'] }
    pure (mkAppN (Expr.mkConst g' gus) args', #[.defnInfo dv])
  | _ => pure (← rt.go retypeFuel [] h, #[])

end Ix.Compile.Pass.Opt

end
