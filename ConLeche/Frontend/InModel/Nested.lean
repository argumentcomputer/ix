module

public import ConLeche.Frontend.InModel.Mutual

@[expose] public section

/-!
# In-process models of a NESTED (or nested-and-mutual) block (task #200, B3)

lean-inductive-models' nested rung, on `ConLeche.Expr`, fused with the
mutual rung: the kernel's own nested→mutual reduction is READ OFF THE
EXPORTED RECURSOR FAMILY instead of being re-derived — motive `m`'s
domain `∀ ı⃗ (t : Carrier_m p⃗ ı⃗), Sort ℓ` names the member (a real
member `T_m p⃗ ı⃗` or a *mimic* `I As ı⃗`, the container instantiated at
its pins), each minor's telescope names the member's constructor with
its fields, and the `ih` binders say which fields recurse to which
member.  The auxiliary family has one member per motive; a mimic's
constructors are the container's at the pins, every field that is a
member or mimic carrier rewritten to `aux p⃗ (tag.m p⃗ e⃗)`.

The public slots then need an isomorphism per mimic `j` between the
container `Carrier_j` (over the *model* names) and `aux p⃗ (tag.(r+j))`:

* `pack_j` by the container's recursor, `unpack_j` by `aux.rec` (all
  mimics at once, `_impl.unpack`), `unpackPack_j : unpack (pack x) = x`
  by the container's recursor and `packUnpack_j : pack (unpack s) = s`
  by `aux.rec` (all at once, `_impl.packUnpack`), the congruences by
  `Eq.rec` (`congrPack_j`, and one chain builder for the round-trips);
* `C._model` packs its mimic-typed fields; `_impl.rec` is `aux.rec` at
  the motive `M_m` at a real member and `M_{r+j} ∘ unpack_j` at a mimic,
  with the public minors adapted — a mimic constructor's by unpacking
  its mimic-typed fields (no transport: `unpack` computes on it), a real
  constructor's by unpacking them and transporting the result along
  `packUnpack_j` at each packed position; `T_m.rec._model` applies it at
  the member's tag, `T_1.rec_j._model` at `pack_j x` and comes back
  along `unpackPack_j x`;
* the iota theorems: `Eq.refl` where nothing moves, otherwise one
  `Eq.rec` per packed position over the statement generalised at that
  position (`u_k := unpack (pack f_k)`, `h_k : u_k = z_k`), whose
  innermost base reduces to `Eq.refl` by δι (every transport is along
  a proof that reduces to `Eq.refl` at `h_k := Eq.refl`), and whose
  instance at `(f_k, unpackPack_j f_k)` is the statement by proof
  irrelevance of the transports' proofs;
* `proj_i` of a structure-like owner by `aux.rec` at a constant motive
  (unpacking a packed field), its iota by `unpackPack_j` or `Eq.refl`.

Declines (the residual): a field mentioning the block other than as a
whole member/mimic carrier (an occurrence under a binder — infinitary
nesting), a container that is itself nested or mutual or whose mimics
form a cycle (B4), a reflexive member, a `Prop` block with a large
eliminator, a container field a later container field depends on, an
index domain whose sort not even a ceiling bounds (`Kit.sortCeil`,
task #227).  (Members' parameter telescopes and sorts are not
compared: task #218, `Mutual.lean`'s header.)

KNOWN GAP, not a decline (task #227's finding): a member whose index
DOMAIN mentions a parameter — `inductive NB (α : Type) (a₀ : α) : α →
Type` nesting through `List`, or `NB4 (α : Type) : List α → Type` —
gets a `_impl.rec` the fold REJECTS (an application type mismatch at
the tag dispatch), where official accepts the block.  It is older than
the ceiling and independent of it: the same block with a closed index
domain (`Nat`) installs, and the same domain in a MUTUAL block installs.
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-- A member of the auxiliary family: a real member of the block or a
mimic (a nested occurrence `I As`, the container at its pins). -/
structure Mem where
  /-- position among the motives -/
  tag : Nat
  /-- the block member (`some m`) or the mimic ordinal (`none`, see `j`) -/
  real? : Option Nat
  /-- mimic ordinal (0-based; meaningful when `real? = none`) -/
  j : Nat
  /-- the carrier's head: `T_m` at a real member, the container `I` at a mimic -/
  I : Name
  /-- the carrier's levels -/
  lv : List Level
  /-- the pins (the container's parameters), at the parameter frame;
  empty at a real member (whose parameters are the block's) -/
  pins : List Expr
  /-- the index count -/
  nIdx : Nat
  /-- the index telescope, at the parameter frame -/
  idxBs : List Expr
  deriving Repr, Inhabited

/-- One constructor of the auxiliary family. -/
structure ACtor where
  /-- the member it belongs to -/
  mem : Nat
  /-- the public constructor name (the container's at a mimic) and levels -/
  cname : Name
  clv : List Level
  /-- field count -/
  nF : Nat
  /-- the field binders, each at its own frame over the parameter frame -/
  doms : List Expr
  /-- per field: the member it recurses to, or `none` -/
  kinds : List (Option Nat)
  /-- the residual's index expressions, at the fields' frame -/
  idx : List Expr
  /-- the global minor index -/
  J : Nat
  /-- the rule index within the member's recursor -/
  jIn : Nat
  deriving Repr, Inhabited

/-- A container group (B4): the mimics that are one container's
recursor family instantiated at the pins, in the container's motive
order, with each member's recursor name; `lv`/`pins` are the
container's levels and pins (shared by the group), `large` whether its
recursors carry an elimination level. -/
structure Group where
  tags : List Nat
  recNames : List Name
  lv : List Level
  pins : List Expr
  nPI : Nat
  large : Bool
  deriving Repr, Inhabited

/-- The family read off the block. -/
structure Family where
  T : Name
  lps : List Name
  nP : Nat
  /-- the parameter binders (from the first former) -/
  pbs : List Expr
  u : Level
  /-- the real member count -/
  r : Nat
  mems : List Mem
  ctors : List ACtor
  large : Bool
  elim : Name
  deriving Repr, Inhabited

/-! ## Carriers and the family rewrite -/

/-- Member `mem`'s carrier at `o` binders below the parameter frame,
at index arguments `idx`; `rn` renames a real member to its model. -/
def carrierAt (fam : Family) (mem : Mem) (o : Nat) (idx : List Expr) (model : Bool) : Expr :=
  match mem.real? with
  | some _ =>
    Expr.mkAppN (.const (if model then modelName mem.I else mem.I) mem.lv) (varsAt o fam.nP ++ idx)
  | none =>
    let pins := mem.pins.map fun p =>
      let p := p.liftLooseBVars o 0
      if model then p.renameConsts (fun x => if fam.mems.any (fun m => m.real?.isSome && m.I == x) then modelName x else x) else p
    Expr.mkAppN (.const mem.I mem.lv) (pins ++ idx)

/-- `aux p⃗ (tag.mem p⃗ idx)` at `o` binders below the parameter frame. -/
def auxAt (fam : Family) (tag : Nat) (o : Nat) (idx : List Expr) : Expr :=
  Expr.mkAppN (constP (auxName fam.T) fam.lps)
    (varsAt o fam.nP ++ [Expr.mkAppN (constP (tagCtorName fam.T tag) fam.lps) (varsAt o fam.nP ++ idx)])

/-- Is `e`, at `o` binders below the parameter frame, a member's carrier
at some index arguments?  Returns the member's tag and the index
arguments. -/
def matchCarrier (fam : Family) (o : Nat) (e : Expr) : Option (Nat × List Expr) :=
  match e.getAppFn with
  | .const x us =>
    let args := e.getAppArgs
    fam.mems.findSome? fun mem =>
      if mem.I == x && us == mem.lv then
        match mem.real? with
        | some _ =>
          if args.length == fam.nP + mem.nIdx && args.take fam.nP == varsAt o fam.nP then
            some (mem.tag, args.drop fam.nP)
          else none
        | none =>
          let nPI := mem.pins.length
          if args.length == nPI + mem.nIdx &&
              args.take nPI == mem.pins.map (·.liftLooseBVars o 0) then
            some (mem.tag, args.drop nPI)
          else none
      else none
  | _ => none

mutual

/-- Rewrite every whole carrier occurrence into the auxiliary family
(`o` binders below the parameter frame at entry).

One memoized DAG walk, keyed by the node and the binder offset `o`
(which shifts under binders, so a node's answer is not a function of
the node alone), and dropped after each call.  No spec lemma, as in
`InModel.mentionsAnyGo`: the modeller is untrusted and what it emits
is checked at install.  Without the memo the rebuild runs once per
path — `tests/e2e/tower_nested.ndjson`. -/
partial def specAllGo (fam : Family) (memo : Std.HashMap (Expr × Nat) Expr)
    (o : Nat) (e : Expr) : Expr × Std.HashMap (Expr × Nat) Expr :=
  match matchCarrier fam o e with
  | some (tag, idx) =>
    let (idx', memo) := specAllGoList fam memo o idx
    (auxAt fam tag o idx', memo)
  | none =>
    match e with
    | .bvar i => (.bvar i, memo)
    | .sort u => (.sort u, memo)
    | .fvar i t => (.fvar i t, memo)
    | .const n us => (.const n us, memo)
    | .lit l => (.lit l, memo)
    | e =>
      match memo[(e, o)]? with
      | some r => (r, memo)
      | none =>
        let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
          match e with
          | .app f a =>
            let (f', memo) := specAllGo fam memo o f
            let (a', memo) := specAllGo fam memo o a
            (.app f' a', memo)
          | .lam d b m =>
            let (d', memo) := specAllGo fam memo o d
            let (b', memo) := specAllGo fam memo (o + 1) b
            (.lam d' b' m, memo)
          | .forallE d b m =>
            let (d', memo) := specAllGo fam memo o d
            let (b', memo) := specAllGo fam memo (o + 1) b
            (.forallE d' b' m, memo)
          | .letE t v b =>
            let (t', memo) := specAllGo fam memo o t
            let (v', memo) := specAllGo fam memo o v
            let (b', memo) := specAllGo fam memo (o + 1) b
            (.letE t' v' b', memo)
          | .proj s i x =>
            let (x', memo) := specAllGo fam memo o x
            (.proj s i x', memo)
          | e => (e, memo)
        (r, memo.insert (e, o) r)

@[inherit_doc specAllGo]
partial def specAllGoList (fam : Family) (memo : Std.HashMap (Expr × Nat) Expr)
    (o : Nat) : List Expr → List Expr × Std.HashMap (Expr × Nat) Expr
  | [] => ([], memo)
  | x :: xs =>
    let (y, memo) := specAllGo fam memo o x
    let (ys, memo) := specAllGoList fam memo o xs
    (y :: ys, memo)

end

@[inherit_doc specAllGo]
def specAll (fam : Family) (o : Nat) (e : Expr) : Expr :=
  (specAllGo fam {} o e).1

/-! ## Reading the family off the recursor -/

/-- Strip every leading `∀`, returning binders and body. -/
def stripAllPis (e : Expr) : List (Expr × BinderMeta) × Expr :=
  match e with
  | .forallE d b m => let (bs, r) := stripAllPis b; ((d, m) :: bs, r)
  | e => ([], e)

/-- Read the members off the motives of the first recursor's type
(after the parameters): motive `m`'s domain `∀ ı⃗ (t : C), Sort ℓ`. -/
def readMems (lps : List Name) (nP : Nat) (types : List IndTypeRec)
    (motives : List Expr) : Except String (List Mem) := do
  let r := types.length
  let memberNames := types.map (·.cv.name)
  let mut out : List Mem := []
  for m in List.range motives.length do
    -- motive `m`'s domain sits under the `m` earlier motive binders,
    -- which it never mentions: lower it to the parameter frame
    let dom := (motives.getD m default).lowerBVars m 0
    let (bs, body) := stripAllPis dom
    let .sort _ := body | throw s!"motive {m} does not end in a sort"
    let some (carr, _) := bs.getLast?
      | throw s!"motive {m} has no major binder"
    let nIdx := bs.length - 1
    let idxBs := piBinders (bs.take nIdx)
    match carr.getAppFn with
    | .const I us =>
      let args := carr.getAppArgs
      if m < r then
        -- a real member, in order
        unless I == memberNames.getD m .anonymous do
          throw s!"motive {m} is not member {memberNames.getD m .anonymous}"
        unless us == lps.map .param && args == varsAt nIdx nP ++ varsAt 0 nIdx do
          throw s!"motive {m}: the member's carrier is not at its parameters and indices"
        unless (types.getD m default).nIdx == nIdx do
          throw s!"motive {m}: index count differs from the member's"
        out := out ++ [⟨m, some m, 0, I, us, [], nIdx, idxBs⟩]
      else
        if memberNames.contains I then
          throw s!"motive {m}: a member's carrier among the mimics"
        unless args.length ≥ nIdx && args.drop (args.length - nIdx) == varsAt 0 nIdx do
          throw s!"motive {m}: the mimic's carrier does not end in its index variables"
        let pins := args.take (args.length - nIdx)
        -- the pins live at the parameter frame: no index variable in them
        let pinsP := pins.map (Expr.lowerBVars nIdx 0)
        unless pinsP.map (Expr.liftLooseBVars nIdx 0) == pins do
          throw s!"motive {m}: a pin mentions an index variable"
        if pins.any (fun p => (stripAllPis p).1.length > 0 && false) then
          throw "unreachable"
        out := out ++ [⟨m, none, m - r, I, us, pinsP, nIdx, idxBs⟩]
    | _ => throw s!"motive {m}: carrier head is not a constant"
  pure out

/-- Read the constructors off the minors: minor `J`'s domain
`∀ f⃗ ih⃗, motive_m e⃗ (C As f⃗)`, `nF` from the rules. -/
def readCtors (fam : Family) (M : Nat) (minors : List Expr)
    (nFOf : Name → Nat → Except String Nat) : Except String (List ACtor) := do
  let mut out : List ACtor := []
  let mut perMem : List Nat := fam.mems.map fun _ => 0
  for J in List.range minors.length do
    let dom := minors.getD J default
    let (bs, body) := stripAllPis dom
    -- the motive: `bvar (bs.length + J + (M - 1 - m))`
    let .bvar mv := body.getAppFn | throw s!"minor {J}: codomain head is not a motive"
    unless mv ≥ bs.length + J && mv < bs.length + J + M do
      throw s!"minor {J}: codomain head is not a motive"
    let mem := M - 1 - (mv - bs.length - J)
    let margs := body.getAppArgs
    let some capp := margs.getLast? | throw s!"minor {J}: no major"
    let .const cname clv := capp.getAppFn | throw s!"minor {J}: major head is not a constructor"
    let nF ← nFOf cname mem
    unless nF ≤ bs.length do throw s!"minor {J}: fewer binders than fields"
    let nIh := bs.length - nF
    -- the field domains, lowered to the parameter frame (the motives
    -- and earlier minors sit between the parameters and the fields)
    -- (head-β-reduced: a container at a dependent pin `I α (fun _ => T α)`
    -- leaves `(fun _ => T α) k` in the kernel's minor)
    let doms : List Expr := (List.range nF).map fun i =>
      let (d, _) := bs.getD i default
      betaHead (d.lowerBVars (M + J) i)
    -- the kinds, by the carrier match at each field's frame
    let kinds : List (Option Nat) := (List.range nF).map fun i =>
      (matchCarrier fam i (doms.getD i default)).map (·.1)
    let nRec := kinds.filter (·.isSome) |>.length
    unless nRec == nIh do
      throw s!"minor {J} ({cname}): {nIh} inductive hypotheses for {nRec} recursive fields"
    -- every other field must not mention the block at all
    let memberNames := fam.mems.filterMap fun m => if m.real?.isSome then some m.I else none
    for i in List.range nF do
      if (kinds.getD i none).isNone && mentionsAny memberNames (doms.getD i default) then
        throw s!"field {i} of {cname} mentions the block other than as a whole member or \
          container occurrence (nested under a binder)"
    -- the residual's index expressions at the fields' frame
    let idx := (margs.take (margs.length - 1)).map fun e =>
      (e.lowerBVars nIh 0).lowerBVars (M + J) nF
    let jIn := perMem.getD mem 0
    perMem := perMem.set mem (jIn + 1)
    out := out ++ [⟨mem, cname, clv, nF, doms, kinds, idx, J, jIn⟩]
  pure out

/-! ## Emission helpers -/

/-- `Eq.{ℓ} α a b`. -/
def mkEq (ℓ : Level) (α a b : Expr) : Expr := Expr.mkAppN (.const eqName [ℓ]) [α, a, b]

/-- `Eq.refl.{ℓ} α a`. -/
def mkRefl (ℓ : Level) (α a : Expr) : Expr := Expr.mkAppN (.const eqReflName [ℓ]) [α, a]

/-- `@Eq.rec.{ℓm, ℓα} α a motive refl b h`. -/
def mkEqRec (ℓm ℓα : Level) (α a motive refl b h : Expr) : Expr :=
  Expr.mkAppN (.const (eqName.str "rec") [ℓm, ℓα]) [α, a, motive, refl, b, h]

/-- Lift every entry. -/
def liftAll (n : Nat) (es : List Expr) : List Expr := es.map (·.liftLooseBVars n 0)

/-- The congruence chain (Prop motives): given a spine builder `F`
(closed over the current frame), argument lists `l⃗`, `r⃗` (equal at
unmoved positions), the moved positions with their equations
`e_k : l_k = r_k` and their types, a proof of `F l⃗ = F r⃗`:
`S'_k := F l⃗ = F (r_1..r_k, l_{k+1}..)`, `S'_n = Eq.refl`,
`S'_{k-1}` from `S'_k` by `Eq.rec` on `e_k` (motive
`λ z _, F l⃗ = F (r_1..r_{k-1}, z, l_{k+1}..)`).  `α`/`ℓα` are the
spine's type and its sort. -/
partial def congrChain (ℓα : Level) (α : Expr) (F : Nat → List Expr → Expr) (ls rs : List Expr)
    (moved : List (Nat × Expr × Expr × Level)) : Expr :=
  go 0
where
  go (k : Nat) : Expr :=
    match moved[k]? with
    | none => mkRefl ℓα α (F 0 ls)
    | some (pos, e, ty, ℓty) =>
      -- the motive over `z` at position `pos`: positions of earlier
      -- moved entries at `r`, later ones at `l`; `F o` builds the spine
      -- `o` binders below the chain's frame
      -- `S'_k`: the first `k` moved positions at `l`, the later ones at `r`
      -- (unmoved positions agree)
      let mid : List Expr := (List.range ls.length).map fun i =>
        if (moved.drop k).any (·.1 == i) then rs.getD i default else ls.getD i default
      let motive : Expr := .lam ty
        (.lam
          (mkEq ℓty (ty.liftLooseBVars 1 0) ((ls.getD pos default).liftLooseBVars 1 0) (.bvar 0))
          (mkEq ℓα (α.liftLooseBVars 2 0)
            (F 2 (liftAll 2 ls))
            (F 2 ((liftAll 2 mid).set pos (.bvar 1)))) bm) bm
      mkEqRec .zero ℓty ty (ls.getD pos default) motive (go (k + 1)) (rs.getD pos default) e

/-! ## The nested rung -/

/-- The generic in-process rung: mutual, nested, both.  (The mutual rung
of `Mutual.lean` is the special case without mimics; it stays as the
B1/B2 landing.) -/
def genNested (ctx : Ctx) (b : BlockRec) : Except String (List Declaration) := do
  let t0 :: _ := b.types | throw "empty block"
  let T := t0.cv.name
  let lps := t0.cv.levelParams
  let nP := t0.nP
  let r := b.types.length
  for t in b.types do
    unless !t.isReflexive do throw s!"reflexive member {t.cv.name}"
    unless t.cv.levelParams == lps && t.nP == nP do
      throw s!"member {t.cv.name}: level parameters or parameter count differ"
  let some (pbs0, .sort u) := t0.cv.type.stripPis (nP + t0.nIdx)
    | throw s!"former {T} is not a telescope ending in a sort"
  -- the first member's parameter binders and sort: the telescope of
  -- everything generated below (task #218: the other members'
  -- telescopes and sorts are NOT compared here — the fold's typing of
  -- the public slots, emitted at each member's own declared type, is
  -- official's `is_def_eq` / `is_equivalent` check; `Mutual.lean`'s
  -- header)
  let pbs := piBinders (pbs0.take nP)
  for t in b.types do
    match t.cv.type.stripPis (nP + t.nIdx) with
    | some (_, .sort _) => pure ()
    | _ => throw s!"former {t.cv.name} is not a telescope ending in a sort"
  -- the first recursor's telescope: parameters, `M` motives, `n` minors
  let some r0 := b.recs.find? (·.cv.name == T.str "rec") | throw s!"no recursor {T}.rec"
  let M := r0.nM
  let n := r0.nm
  unless M ≥ r do throw "fewer motives than members"
  let some (_, afterP) := r0.cv.type.stripPis nP | throw "recursor: parameter telescope"
  let some (motiveBs, afterM) := afterP.stripPis M | throw "recursor: motive telescope"
  let some (minorBs, _) := afterM.stripPis n | throw "recursor: minor telescope"
  -- the members: real ones and mimics
  let mems ← readMems lps nP b.types (motiveBs.map (·.1))
  let large? : Option Name :=
    match r0.cv.levelParams with
    | e :: rest => if rest == lps && !lps.contains e then some e else none
    | [] => none
  let large := large?.isSome
  let elim := large?.getD (freshLevelName lps)
  let rlps := if large then elim :: lps else lps
  let fam0 : Family := ⟨T, lps, nP, pbs, u, r, mems, [], large, elim⟩
  -- the recursor of each member: `T_m.rec` at a real member, `T.rec_j`
  -- (1-based) at a mimic
  let recOf : Mem → Except String IndRecRec := fun mem => do
    let nm := match mem.real? with
      | some m => (b.types.getD m default).cv.name.str "rec"
      | none => T.str s!"rec_{mem.j + 1}"
    match b.recs.find? (·.cv.name == nm) with
    | some rr => pure rr
    | none => throw s!"no recursor {nm}"
  for mem in mems do
    let rr ← recOf mem
    unless rr.nP == nP && rr.nM == M && rr.nm == n && rr.nI == mem.nIdx do
      throw s!"recursor {rr.cv.name}: unexpected telescope"
    unless rr.cv.levelParams == rlps do throw s!"recursor {rr.cv.name}: eliminator shape differs"
  -- field counts: a real constructor's from the block, a mimic's from
  -- the member's recursor rules
  let nFOf : Name → Nat → Except String Nat := fun cname mem => do
    let some memR := mems.find? (·.tag == mem) | throw "unreachable"
    match memR.real? with
    | some _ =>
      match b.ctors.find? (·.cv.name == cname) with
      | some c => pure c.nF
      | none => throw s!"constructor {cname} not in the block"
    | none =>
      let rr ← recOf memR
      match rr.rules.find? (·.ctor == cname) with
      | some rule => pure rule.nfields
      | none => throw s!"no rule for {cname} in {rr.cv.name}"
  let ctors ← readCtors fam0 M (minorBs.map (·.1)) nFOf
  let fam : Family := { fam0 with ctors := ctors }
  unless ctors.length == n do throw "minor count"
  -- the real members' constructors must be the block's, in order
  for m in List.range r do
    let t := b.types.getD m default
    let own := ctors.filter (·.mem == m)
    unless own.map (·.cname) == t.ctors do
      throw s!"member {t.cv.name}: constructors differ from the recursor's minors"
  -- containers: CONTAINER GROUPS (B4).  A container's whole recursor
  -- family — its real members and its own mimics, instantiated at the
  -- pins — is among our mimics (the kernel flattens nesting), so every
  -- mimic belongs to the group of its container's family, in the
  -- container's motive order; `pack`/`unpackPack` for a group are one
  -- application of each group member's recursor with the group's
  -- motives.  A plain container is a singleton group.
  let mimics := mems.filter (·.real?.isNone)
  let mut groups : List Group := []
  for mem in mimics do
    if groups.any (·.tags.contains mem.tag) then continue
    let some cb := ctx.blocks mem.I | throw s!"container {mem.I}: no block record"
    let cI0 := cb.types.getD 0 default
    let I1 := cI0.cv.name
    let lpsI := cI0.cv.levelParams
    let nPI := cI0.nP
    unless nPI == mem.pins.length do throw s!"container {mem.I}: parameter count"
    unless lpsI.length == mem.lv.length do throw s!"container {mem.I}: level count"
    let some rI := cb.recs.find? (·.cv.name == I1.str "rec") | throw s!"container {I1}: no recursor"
    let MI := rI.nM
    let some (_, afterPI) := rI.cv.type.stripPis nPI | throw s!"container {I1}: recursor parameters"
    let some (motivesI, _) := afterPI.stripPis MI | throw s!"container {I1}: recursor motives"
    let memsI ← readMems lpsI nPI cb.types (motivesI.map (·.1))
    let mut tags : List Nat := []
    let mut recNames : List Name := []
    for memI in memsI do
      -- the family member's carrier at the pins: instantiate the
      -- container's parameters (under the member's index binders)
      -- (the carrier under the member's `nIdx` index binders: the
      -- container's parameters sit above them)
      let carrI := carrierAt ⟨I1, lpsI, nPI, [], .zero, cb.types.length, memsI, [], false, .anonymous⟩
        memI memI.nIdx (varsAt 0 memI.nIdx) false
      -- levels first (the container's level names may coincide with the
      -- block's, which the pins mention), then the pins
      let carr := substParams memI.nIdx nPI (mem.pins.map (·.liftLooseBVars memI.nIdx 0))
        (carrI.instantiateLevelParams lpsI mem.lv)
      let some (t, _) := matchCarrier fam memI.nIdx carr
        | throw s!"container {mem.I}: family member {memI.I} at the pins is not among the mimics"
      tags := tags ++ [t]
      recNames := recNames ++ [match memI.real? with
        | some m => (cb.types.getD m default).cv.name.str "rec"
        | none => I1.str s!"rec_{memI.j + 1}"]
    let large := rI.cv.levelParams.length == lpsI.length + 1
    groups := groups ++ [⟨tags, recNames, mem.lv, mem.pins, nPI, large⟩]
  -- dependency order among the groups: a group needs another when a
  -- field of one of its constructors has a carrier outside the group
  let groupOf : Nat → Option Group := fun t => groups.find? (·.tags.contains t)
  let depsOfGroup : Group → List Nat := fun g =>
    (ctors.filter (fun c => g.tags.contains c.mem)).foldl (fun acc c =>
      acc ++ c.kinds.filterMap fun k => match k with
        | some t => if t ≥ r && !g.tags.contains t then some t else none
        | none => none) []
  let mut order : List Group := []
  let mut pending := groups
  let mut progress := true
  while progress && !pending.isEmpty do
    progress := false
    for g in pending do
      if (depsOfGroup g).all (fun d => order.any (·.tags.contains d)) then
        order := order ++ [g]
        pending := pending.filter (·.tags != g.tags)
        progress := true
  unless pending.isEmpty do
    throw s!"the container groups form a cycle: {pending.map (·.tags)}"
  let _ := groupOf
  let isProp := Level.isEquiv u .zero == some true
  if isProp && large then
    throw "Prop block with a large eliminator (the auxiliary family eliminates into Prop only)"
  let ℓ := structElimLevel elim large
  let rlvls : List Level := if large then ℓ :: lps.map .param else lps.map .param
  let elimTag := if large then elim else freshLevelName lps
  let blockNames := (b.types.map (·.cv.name)) ++ b.ctors.map (·.cv.name) ++ b.recs.map (·.cv.name)
  let rnF : Name → Name := fun x => if blockNames.contains x then modelName x else x
  let rn : Expr → Expr := Expr.renameConsts rnF
  let tag := tagName T
  let aux := auxName T
  let mut out : Array Declaration := #[]
  let mut heights : List (Name × Nat) := []
  let hOf : List (Name × Nat) → Name → Nat := fun hs x =>
    match hs.find? (·.1 == x) with
    | some (_, h) => h
    | none => ctx.heights x
  let push := fun (o : Array Declaration) (hs : List (Name × Nat)) (nm : Name) (l : List Name)
      (ty v : Expr) =>
    let h := hintFor (hOf hs) v
    (o.push (.defnDecl ⟨nm, l, ty⟩ v h), (nm, hintHeight h) :: hs)
  -- ---------------------------------------------------------------
  -- 1. the tag block
  let mut W : Level := .succ .zero
  for mem in mems do
    for j in List.range mem.nIdx do
      let ctxJ := (pbs ++ (mem.idxBs.take j)).reverse
      let dom := (mem.idxBs.getD j default)
      let some ℓj := idxSort ctx.tbl ctxJ (dom.renameConsts rnF)
        | throw s!"cannot bound the sort of index {j} of member {mem.tag} (the tag's universe)"
      W := .max W ℓj
  let tagTy ← need "tag type" (Expr.replacePiBody nP t0.cv.type (.sort W))
  let tagCtors : List (Name × Nat × Expr × List Nat) ← mems.mapM fun mem => do
    let ty ← need "tag constructor type" (Expr.replacePiBody nP t0.cv.type
      (mkPis (mem.idxBs.map fun d => specAll fam 0 d)
        (Expr.mkAppN (constP tag lps) (varsAt mem.nIdx nP))))
    pure (tagCtorName T mem.tag, mem.nIdx, ty, [])
  let tagRecTy ← need "tag recursor type" (recTy tag lps elimTag true nP 0 tagTy tagCtors)
  let tagRules ← mems.mapM fun mem => do
    let rhs ← need "tag rule"
      (recRhs tag lps elimTag true nP 0 tagTy tagCtors (tag.str "rec") (.param elimTag :: lps.map .param) mem.tag)
    pure (RecRule.mk (tagCtorName T mem.tag) mem.nIdx 0 .inert rhs false false false)
  out := out.push (.indDecl
    ([.indInfo ⟨tag, lps, tagTy⟩ {}] ++
     tagCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
     [.recInfo ⟨tag.str "rec", elimTag :: lps, tagRecTy⟩ (nP + 1 + M) (nP + 1 + M) tagRules])
    nP)
  -- 2. the auxiliary family
  let auxTy ← need "aux type" (Expr.replacePiBody nP t0.cv.type
    (.forallE (Expr.mkAppN (constP tag lps) (varsAt 0 nP)) (.sort u) bm))
  let auxCtors : List (Name × Nat × Expr × List Nat) ← ctors.mapM fun c => do
    let doms' := (List.range c.nF).map fun i =>
      specAll fam i (c.doms.getD i default)
    let ty ← need "aux constructor type" (Expr.replacePiBody nP t0.cv.type
      (mkPis doms' (auxAt fam c.mem c.nF c.idx)))
    pure (auxCtorName T c.mem c.cname, c.nF, ty,
      (List.range c.nF).filter fun i => (c.kinds.getD i none).isSome)
  let auxRecTy ← need "aux recursor type" (recTy aux lps elim large nP 1 auxTy auxCtors)
  let auxRules ← (List.range n).mapM fun j => do
    let rhs ← need "aux rule"
      (recRhs aux lps elim large nP 1 auxTy auxCtors (aux.str "rec") rlvls j)
    pure (RecRule.mk (auxCtors.getD j default).1
      (auxCtors.getD j default).2.1 0 .inert rhs false false false)
  out := out.push (.indDecl
    ([.indInfo ⟨aux, lps, auxTy⟩ {}] ++
     auxCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
     [.recInfo ⟨aux.str "rec", rlps, auxRecTy⟩ (nP + 1 + n + 1) (nP + 1 + n) auxRules])
    nP)
  -- ---------------------------------------------------------------
  -- shared builders
  let auxCtorName' := fun (c : ACtor) => auxCtorName T c.mem c.cname
  -- the spec'd field domains of a constructor at `o` extra binders
  -- below the parameter frame (field `i` sits `o + i` below)
  let specDoms := fun (c : ACtor) (o : Nat) => (List.range c.nF).map fun i =>
    specAll fam (o + i) ((c.doms.getD i default).liftLooseBVars o i)
  -- the model-side field domains (public spelling renamed)
  let modelDoms := fun (c : ACtor) (o : Nat) => (List.range c.nF).map fun i =>
    rn ((c.doms.getD i default).liftLooseBVars o i)
  -- a field's index arguments off its domain, at `o'` below the
  -- field's own frame
  let fieldIdx := fun (c : ACtor) (i : Nat) (o' : Nat) =>
    ((matchCarrier fam i (c.doms.getD i default)).map (·.2)).getD [] |>.map (·.liftLooseBVars o' 0)
  -- `tag.rec p⃗ (λ i', ∀ s, aux p⃗ i' → Sort ℓs) branches i s` at frame
  -- `o` below the parameters, given the per-member branches (each a
  -- term at frame `o + 3`... no: branches are built by the caller at
  -- frame `o`, the motive λ adds binders itself)
  let tagDispatch := fun (o : Nat) (ℓs : Level) (branches : List Expr) (i s : Expr) =>
    let motTag : Expr := .lam
      (Expr.mkAppN (constP tag lps) (varsAt o nP))
      (.forallE
        (Expr.mkAppN (constP aux lps) (varsAt (o + 1) nP ++ [.bvar 0])) (.sort ℓs) bm) bm
    Expr.mkAppN (.const (tag.str "rec") (Level.imax u (.succ ℓs) :: lps.map .param))
      (varsAt o nP ++ [motTag] ++ branches ++ [i, s])
  -- the dispatching motive `λ i s, tag.rec … i s` at frame `o`, with
  -- the branches built at frame `o + 2`
  let dispatchMotive := fun (o : Nat) (ℓs : Level) (branchesAt : Nat → List Expr) =>
    Expr.lam (Expr.mkAppN (constP tag lps) (varsAt o nP))
      (.lam (Expr.mkAppN (constP aux lps) (varsAt (o + 1) nP ++ [.bvar 0]))
        (tagDispatch (o + 2) ℓs (branchesAt (o + 2)) (.bvar 1) (.bvar 0)) bm) bm
  -- a member's branch `λ ı⃗ s, body` at frame `o` (the body built at
  -- frame `o + nIdx + 1`)
  -- (index binders of a member at frame `o`: the domains at their own
  -- frames, lifted past the `o` extras)
  let idxBsAt := fun (mem : Mem) (o : Nat) => (List.range mem.nIdx).map fun j =>
    (specAll fam j (mem.idxBs.getD j default)).liftLooseBVars o j
  let idxBsAtM := fun (mem : Mem) (o : Nat) => (List.range mem.nIdx).map fun j =>
    (rn (mem.idxBs.getD j default)).liftLooseBVars o j
  let packName := fun (j : Nat) => implName T s!"pack_{j}"
  let unpackName := fun (j : Nat) => implName T s!"unpack_{j}"
  let unpackPackName := fun (j : Nat) => implName T s!"unpackPack_{j}"
  let packUnpackName := fun (j : Nat) => implName T s!"packUnpack_{j}"
  let congrPackName := fun (j : Nat) => implName T s!"congrPack_{j}"
  let unpackAll := implName T "unpack"
  let packUnpackAll := implName T "packUnpack"
  let recAll := implName T "rec"
  -- `pack_j p⃗ idx x`, `unpack_j p⃗ idx s` … applications at frame `o`
  let appImpl := fun (nm : Name) (o : Nat) (idx : List Expr) (args : List Expr) =>
    Expr.mkAppN (constP nm lps) (varsAt o nP ++ idx ++ args)
  -- the model-side carrier of a member at frame `o`
  let carrM := fun (mem : Mem) (o : Nat) (idx : List Expr) => carrierAt fam mem o idx true
  -- the ih positions of a constructor: the k-th recursive field is the k-th ih
  let ihPos := fun (c : ACtor) (i : Nat) => ((List.range i).filter fun i' => (c.kinds.getD i' none).isSome).length
  let nIhOf := fun (c : ACtor) => (c.kinds.filter (·.isSome)).length
  -- ---------------------------------------------------------------
  -- 2b. the member models `T_m._model := λ p⃗ ı⃗, aux p⃗ (tag.m p⃗ ı⃗)` — the
  -- model-side carriers of the mimics mention them
  for m in List.range r do
    let t := b.types.getD m default
    let nI := t.nIdx
    let value ← need "member model" (Expr.pisToLams (nP + nI) t.cv.type
      (auxAt fam m nI (varsAt 0 nI)))
    (out, heights) := push out heights (modelName t.cv.name) lps t.cv.type value
  -- 3. `_impl.unpack : ∀ p⃗ (i : tag p⃗) (s : aux p⃗ i), MotU i s`
  --    `MotU`: the identity carrier at a real member, `Carrier_j` at a mimic
  let motU := fun (o : Nat) => dispatchMotive o u fun o2 =>
    mems.map fun mem => mkLams (idxBsAt mem o2 ++ [auxAt fam mem.tag (o2 + mem.nIdx) (varsAt 0 mem.nIdx)])
      (match mem.real? with
       | some _ => auxAt fam mem.tag (o2 + mem.nIdx + 1) (varsAt 1 mem.nIdx)
       | none => carrM mem (o2 + mem.nIdx + 1) (varsAt 1 mem.nIdx))
  -- the unpack minors at frame `o`: `λ f⃗' ih⃗, body`
  let unpackMinors := fun (o : Nat) => ctors.map fun c =>
    let nIh := nIhOf c
    let fbs := specDoms c o
    let ihbs := (List.range c.nF).filterMap fun i =>
      match c.kinds.getD i none with
      | some t =>
        let k := ihPos c i
        -- at the ih's frame: `o + nF + k` below the parameters
        let fo := c.nF + k
        some <| Expr.mkAppN (motU (o + fo))
            [Expr.mkAppN (constP (tagCtorName T t) lps) (varsAt (o + fo) nP ++ (fieldIdx c i (fo - i))),
             .bvar (fo - 1 - i)]
      | none => none
    let D := o + c.nF + nIh
    let fieldVar := fun (i : Nat) => Expr.bvar (nIh + c.nF - 1 - i)
    let ihVar := fun (i : Nat) => Expr.bvar (nIh - 1 - ihPos c i)
    let body := match (mems.getD c.mem default).real? with
      | some _ =>
        Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (c.nF + nIh) nP ++ (List.range c.nF).map fieldVar)
      | none =>
        let mem := mems.getD c.mem default
        -- a mimic-typed field is its (unpacked) inductive hypothesis; a
        -- real-member field passes through unchanged (its hypothesis is
        -- an opaque `aux.rec` rebuild, not the field)
        Expr.mkAppN (.const c.cname c.clv)
          ((carrM mem (c.nF + nIh) []).getAppArgs.take mem.pins.length ++
           (List.range c.nF).map fun i =>
             match c.kinds.getD i none with
             | some t' => if t' ≥ r then ihVar i else fieldVar i
             | none => fieldVar i)
    let _ := D
    mkLams (fbs ++ ihbs) body
  let unpackAllTy := mkPis (pbs ++ [Expr.mkAppN (constP tag lps) (varsAt 0 nP),
      Expr.mkAppN (constP aux lps) (varsAt 1 nP ++ [.bvar 0])])
    (Expr.mkAppN (motU 2) [.bvar 1, .bvar 0])
  let unpackAllVal := mkLams pbs
    (Expr.mkAppN (.const (aux.str "rec") ((if large then [u] else []) ++ lps.map .param))
      (varsAt 0 nP ++ [motU 0] ++ unpackMinors 0))
  if !large && !isProp then throw "small eliminator on a non-Prop block"
  (out, heights) := push out heights unpackAll lps unpackAllTy unpackAllVal
  -- 4. per container group, in dependency order: `pack_j` and
  --    `unpackPack_j` for every member by that member's container
  --    recursor at the group's motives, `unpack_j`/`congrPack_j` per member
  for g in order do
    let cRec := fun (k : Nat) (ℓe : Level) =>
      Expr.const (g.recNames.getD k .anonymous) ((if g.large then [ℓe] else []) ++ g.lv)
    if !g.large && !(Level.isEquiv u .zero == some true) then
      throw s!"container of group {g.tags} eliminates into Prop only but the block is not Prop"
    let pinsAt := fun (o : Nat) => (carrM (mems.getD (g.tags.getD 0 0) default) o []).getAppArgs.take g.nPI
    let inGroup := fun (k : Option Nat) => match k with
      | some t' => g.tags.contains t'
      | none => false
    -- the group's constructors, in the container family's order
    let gctors := g.tags.foldl (fun acc t => acc ++ ctors.filter (·.mem == t)) []
    -- the pack motives at frame `o`: `λ ı⃗ x, aux p⃗ (tag.t ı⃗)` per member
    let packMotives := fun (o : Nat) => g.tags.map fun t =>
      let mem := mems.getD t default
      mkLams (idxBsAtM mem o ++ [carrM mem (o + mem.nIdx) (varsAt 0 mem.nIdx)])
        (auxAt fam t (o + mem.nIdx + 1) (varsAt 1 mem.nIdx))
    -- the pack minors at frame `o`
    let packMinors := fun (o : Nat) => gctors.map fun c =>
      let grpRec := (List.range c.nF).filter fun i => inGroup (c.kinds.getD i none)
      let nIhI := grpRec.length
      let gbs := modelDoms c o
      let ihbs := grpRec.map fun i =>
        let k := (grpRec.filter (· < i)).length
        let fo := c.nF + k
        auxAt fam ((c.kinds.getD i none).getD 0) (o + fo) (fieldIdx c i (fo - i))
      let gVar := fun (i : Nat) => Expr.bvar (nIhI + c.nF - 1 - i)
      let ihVarI := fun (i : Nat) => Expr.bvar (nIhI - 1 - (grpRec.filter (· < i)).length)
      let fo := c.nF + nIhI
      mkLams (gbs ++ ihbs)
        (Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (o + fo) nP ++
          (List.range c.nF).map fun i =>
            match c.kinds.getD i none with
            | some t' =>
              if g.tags.contains t' then ihVarI i
              else if t' ≥ r then
                let mem' := mems.getD t' default
                appImpl (packName mem'.j) (o + fo) (fieldIdx c i (fo - i)) [gVar i]
              else gVar i
            | none => gVar i))
    for k in List.range g.tags.length do
      let t := g.tags.getD k 0
      let mem := mems.getD t default
      let j := mem.j
      let nI := mem.nIdx
      let o0 := nI + 1
      let bsX := pbs ++ idxBsAtM mem 0 ++ [carrM mem nI (varsAt 0 nI)]
      let packTy := mkPis bsX (auxAt fam t o0 (varsAt 1 nI))
      let packVal := mkLams bsX
        (Expr.mkAppN (cRec k u)
          (pinsAt o0 ++ packMotives o0 ++ packMinors o0 ++ varsAt 1 nI ++ [.bvar 0]))
      (out, heights) := push out heights (packName j) lps packTy packVal
    for t in g.tags do
      let mem := mems.getD t default
      let j := mem.j
      let nI := mem.nIdx
      let o0 := nI + 1
      -- `unpack_j`
      let bsS := pbs ++ idxBsAtM mem 0 ++ [auxAt fam t nI (varsAt 0 nI)]
      let unpackTy := mkPis bsS (carrM mem o0 (varsAt 1 nI))
      let unpackVal := mkLams bsS
        (Expr.mkAppN (constP unpackAll lps)
          (varsAt o0 nP ++ [Expr.mkAppN (constP (tagCtorName T t) lps) (varsAt o0 nP ++ varsAt 1 nI), .bvar 0]))
      (out, heights) := push out heights (unpackName j) lps unpackTy unpackVal
      -- `congrPack_j`
      let carrAt := fun (o : Nat) => carrM mem o (varsAt (o - nI) nI)
      let cpBs := pbs ++ idxBsAtM mem 0 ++
        [carrAt nI, carrAt (nI + 1),
         mkEq u (carrAt (nI + 2)) (.bvar 1) (.bvar 0)]
      let packApp := fun (o : Nat) (x : Expr) => appImpl (packName j) o (varsAt (o - nI) nI) [x]
      let cpTy := mkPis cpBs (mkEq u (auxAt fam t (nI + 3) (varsAt 3 nI)) (packApp (nI + 3) (.bvar 2)) (packApp (nI + 3) (.bvar 1)))
      let cpVal := mkLams cpBs
        (mkEqRec .zero u (carrAt (nI + 3)) (.bvar 2)
          (.lam (carrAt (nI + 3))
            (.lam (mkEq u (carrAt (nI + 4)) (.bvar 3) (.bvar 0))
              (mkEq u (auxAt fam t (nI + 5) (varsAt 5 nI)) (packApp (nI + 5) (.bvar 4)) (packApp (nI + 5) (.bvar 1))) bm) bm)
          (mkRefl u (auxAt fam t (nI + 3) (varsAt 3 nI)) (packApp (nI + 3) (.bvar 2)))
          (.bvar 1) (.bvar 0))
      (out, heights) := push out heights (congrPackName j) lps cpTy cpVal
    -- `unpackPack_j` for every member, by its container recursor into Prop
    let upStmtOf := fun (mem : Mem) (o : Nat) (idx : List Expr) (x : Expr) =>
      mkEq u (carrM mem o idx) (appImpl (unpackName mem.j) o idx [appImpl (packName mem.j) o idx [x]]) x
    let upMotives := fun (o : Nat) => g.tags.map fun t =>
      let mem := mems.getD t default
      mkLams (idxBsAtM mem o ++ [carrM mem (o + mem.nIdx) (varsAt 0 mem.nIdx)])
        (upStmtOf mem (o + mem.nIdx + 1) (varsAt 1 mem.nIdx) (.bvar 0))
    let upMinors := fun (o : Nat) => gctors.map fun c =>
      let memC := mems.getD c.mem default
      let grpRec := (List.range c.nF).filter fun i => inGroup (c.kinds.getD i none)
      let nIhI := grpRec.length
      let gbs := modelDoms c o
      let fo := c.nF + nIhI
      let gVarAt := fun (i : Nat) (o' : Nat) => Expr.bvar (o' + nIhI + c.nF - 1 - i)
      let ihbs := grpRec.map fun i =>
        let k := (grpRec.filter (· < i)).length
        let fo' := c.nF + k
        let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
        upStmtOf mem' (o + fo') (fieldIdx c i (fo' - i)) (.bvar (fo' - 1 - i))
      -- the spine's pins are the constructor's OWN container's (a group
      -- member's container differs from the group's head container)
      let F := fun (o' : Nat) (args : List Expr) =>
        Expr.mkAppN (.const c.cname c.clv)
          ((carrM memC (o + fo + o') []).getAppArgs.take memC.pins.length ++ args)
      let ls := (List.range c.nF).map fun i =>
        match c.kinds.getD i none with
        | some t' =>
          if t' ≥ r then
            let mem' := mems.getD t' default
            let idx := fieldIdx c i (fo - i)
            appImpl (unpackName mem'.j) (o + fo) idx [appImpl (packName mem'.j) (o + fo) idx [gVarAt i 0]]
          else gVarAt i 0
        | none => gVarAt i 0
      let rs := (List.range c.nF).map fun i => gVarAt i 0
      let moved := (List.range c.nF).filterMap fun i =>
        match c.kinds.getD i none with
        | some t' =>
          if g.tags.contains t' then
            some (i, Expr.bvar (nIhI - 1 - (grpRec.filter (· < i)).length),
              carrM (mems.getD t' default) (o + fo) (fieldIdx c i (fo - i)), u)
          else if t' ≥ r then
            let mem' := mems.getD t' default
            let idx := fieldIdx c i (fo - i)
            some (i, appImpl (unpackPackName mem'.j) (o + fo) idx [gVarAt i 0], carrM mem' (o + fo) idx, u)
          else none
        | none => none
      mkLams (gbs ++ ihbs)
        (congrChain u (carrM memC (o + fo) (c.idx.map (·.liftLooseBVars nIhI 0))) F ls rs moved)
    for k in List.range g.tags.length do
      let t := g.tags.getD k 0
      let mem := mems.getD t default
      let nI := mem.nIdx
      let o0 := nI + 1
      let bsX := pbs ++ idxBsAtM mem 0 ++ [carrM mem nI (varsAt 0 nI)]
      let upTy := mkPis bsX (upStmtOf mem o0 (varsAt 1 nI) (.bvar 0))
      let upVal := mkLams bsX
        (Expr.mkAppN (cRec k .zero)
          (pinsAt o0 ++ upMotives o0 ++ upMinors o0 ++ varsAt 1 nI ++ [.bvar 0]))
      out := out.push (.thmDecl ⟨unpackPackName mem.j, lps, upTy⟩ upVal)
  -- 5. `_impl.packUnpack : ∀ p⃗ i s, MotPU i s` (all mimics at once)
  let motPU := fun (o : Nat) => dispatchMotive o .zero fun o2 =>
    mems.map fun mem =>
      let sAt := fun (o' : Nat) => auxAt fam mem.tag o' (varsAt (o' - (o2 + mem.nIdx)) mem.nIdx)
      mkLams (idxBsAt mem o2 ++ [sAt (o2 + mem.nIdx)])
        (let o3 := o2 + mem.nIdx + 1
         match mem.real? with
         | some _ => mkEq u (sAt o3) (.bvar 0) (.bvar 0)
         | none =>
           let idx := varsAt 1 mem.nIdx
           mkEq u (sAt o3)
             (appImpl (packName mem.j) o3 idx [appImpl (unpackName mem.j) o3 idx [.bvar 0]]) (.bvar 0))
  let puMinors := fun (o : Nat) => ctors.map fun c =>
    let nIh := nIhOf c
    let fbs := specDoms c o
    let fo := c.nF + nIh
    let fieldVar := fun (i : Nat) => Expr.bvar (nIh + c.nF - 1 - i)
    let ihVar := fun (i : Nat) => Expr.bvar (nIh - 1 - ihPos c i)
    let ihbs := (List.range c.nF).filterMap fun i =>
      match c.kinds.getD i none with
      | some t =>
        let k := ihPos c i
        let fo' := c.nF + k
        some <| Expr.mkAppN (motPU (o + fo'))
            [Expr.mkAppN (constP (tagCtorName T t) lps) (varsAt (o + fo') nP ++ fieldIdx c i (fo' - i)),
             .bvar (fo' - 1 - i)]
      | none => none
    let self := Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (o + fo) nP ++ (List.range c.nF).map fieldVar)
    let body := match (mems.getD c.mem default).real? with
      | some _ => mkRefl u (auxAt fam c.mem (o + fo) (c.idx.map (·.liftLooseBVars nIh 0))) self
      | none =>
        let F := fun (o' : Nat) (args : List Expr) => Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (o + fo + o') nP ++ args)
        let ls := (List.range c.nF).map fun i =>
          match c.kinds.getD i none with
          | some t' =>
            if t' ≥ r then
              let mem' := mems.getD t' default
              let idx := fieldIdx c i (fo - i)
              appImpl (packName mem'.j) (o + fo) idx [appImpl (unpackName mem'.j) (o + fo) idx [fieldVar i]]
            else fieldVar i
          | none => fieldVar i
        let rs := (List.range c.nF).map fieldVar
        let moved := (List.range c.nF).filterMap fun i =>
          match c.kinds.getD i none with
          | some t' =>
            if t' ≥ r then some (i, ihVar i, auxAt fam t' (o + fo) (fieldIdx c i (fo - i)), u) else none
          | none => none
        congrChain u (auxAt fam c.mem (o + fo) (c.idx.map (·.liftLooseBVars nIh 0))) F ls rs moved
    mkLams (fbs ++ ihbs) body
  let puTy := mkPis (pbs ++ [Expr.mkAppN (constP tag lps) (varsAt 0 nP),
      Expr.mkAppN (constP aux lps) (varsAt 1 nP ++ [.bvar 0])])
    (Expr.mkAppN (motPU 2) [.bvar 1, .bvar 0])
  let puVal := mkLams pbs
    (Expr.mkAppN (.const (aux.str "rec") ((if large then [Level.zero] else []) ++ lps.map .param))
      (varsAt 0 nP ++ [motPU 0] ++ puMinors 0))
  out := out.push (.thmDecl ⟨packUnpackAll, lps, puTy⟩ puVal)
  for mem in mimics do
    let t := mem.tag
    let nI := mem.nIdx
    let o0 := nI + 1
    let idx := varsAt 1 nI
    let bs := pbs ++ idxBsAtM mem 0 ++ [auxAt fam t nI (varsAt 0 nI)]
    let ty := mkPis bs (mkEq u (auxAt fam t o0 idx)
      (appImpl (packName mem.j) o0 idx [appImpl (unpackName mem.j) o0 idx [.bvar 0]]) (.bvar 0))
    let v := mkLams bs (Expr.mkAppN (constP packUnpackAll lps)
      (varsAt o0 nP ++ [Expr.mkAppN (constP (tagCtorName T t) lps) (varsAt o0 nP ++ idx), .bvar 0]))
    out := out.push (.thmDecl ⟨packUnpackName mem.j, lps, ty⟩ v)
  -- ---------------------------------------------------------------
  -- 6. the constructor models
  for c in ctors do
    if c.mem < r then
      let some pc := b.ctors.find? (·.cv.name == c.cname) | throw "unreachable"
      let ty := rn pc.cv.type
      let nF := c.nF
      let value ← need "constructor model" (Expr.pisToLams (nP + nF) ty
        (Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt nF nP ++
          (List.range nF).map fun i =>
            match c.kinds.getD i none with
            | some t' =>
              if t' ≥ r then
                appImpl (packName (mems.getD t' default).j) nF (fieldIdx c i (nF - i)) [.bvar (nF - 1 - i)]
              else .bvar (nF - 1 - i)
            | none => .bvar (nF - 1 - i))))
      (out, heights) := push out heights (modelName c.cname) lps ty value
  -- 7. `_impl.rec : ∀ p⃗ M⃗ S⃗ (i : tag p⃗) (s : aux p⃗ i), MotR i s`
  let rP := nP + M + n
  let some (prefixBs, _) := (rn r0.cv.type).stripPis rP | throw "recursor prefix"
  let prefixBsL := piBinders prefixBs
  -- the motive variables at frame `o` below the prefix's end
  let motVar := fun (o : Nat) (m : Nat) => Expr.bvar (o + n + (M - 1 - m))
  let minVar := fun (o : Nat) (J : Nat) => Expr.bvar (o + (n - 1 - J))
  -- `MotR` at frame `o` (below the prefix's end; the parameters sit
  -- `o + M + n` below their frame)
  let motR := fun (o : Nat) => dispatchMotive (o + M + n) ℓ fun o2 =>
    -- `o2` is below the parameter frame; below the prefix's end: `o2 - M - n`
    let oo := o2 - M - n
    mems.map fun mem =>
      match mem.real? with
      | some m => motVar oo m
      | none =>
        let sAt := fun (o' : Nat) => auxAt fam mem.tag o' (varsAt (o' - (o2 + mem.nIdx)) mem.nIdx)
        mkLams (idxBsAt mem o2 ++ [sAt (o2 + mem.nIdx)])
          (let o3 := o2 + mem.nIdx + 1
           Expr.mkAppN (motVar (oo + mem.nIdx + 1) mem.tag)
             (varsAt 1 mem.nIdx ++ [appImpl (unpackName mem.j) o3 (varsAt 1 mem.nIdx) [.bvar 0]]))
  -- the adapted minors at frame `o` below the prefix's end
  let recMinors := fun (o : Nat) => ctors.map fun c =>
    let nIh := nIhOf c
    let oP := o + M + n   -- below the parameters
    let fbs := specDoms c oP
    let fo := c.nF + nIh
    let fieldVar := fun (i : Nat) => Expr.bvar (nIh + c.nF - 1 - i)
    let ihVar := fun (i : Nat) => Expr.bvar (nIh - 1 - ihPos c i)
    let ihbs := (List.range c.nF).filterMap fun i =>
      match c.kinds.getD i none with
      | some t =>
        let k := ihPos c i
        let fo' := c.nF + k
        some <| Expr.mkAppN (motR (o + fo'))
            [Expr.mkAppN (constP (tagCtorName T t) lps) (varsAt (oP + fo') nP ++ fieldIdx c i (fo' - i)),
             .bvar (fo' - 1 - i)]
      | none => none
    -- the public minor applied: fields (unpacked where mimic-typed) and the ihs
    let unpacked := fun (i : Nat) =>
      match c.kinds.getD i none with
      | some t' =>
        if t' ≥ r then
          appImpl (unpackName (mems.getD t' default).j) (oP + fo) (fieldIdx c i (fo - i)) [fieldVar i]
        else fieldVar i
      | none => fieldVar i
    let X := Expr.mkAppN (minVar (o + fo) c.J)
      ((List.range c.nF).map unpacked ++ (List.range c.nF).filterMap fun i =>
        if (c.kinds.getD i none).isSome then some (ihVar i) else none)
    let body := match (mems.getD c.mem default).real? with
      | none => X
      | some m =>
        -- transports along `packUnpack_j f'_k` at each packed position
        let packed := (List.range c.nF).filter fun i =>
          match c.kinds.getD i none with | some t' => t' ≥ r | none => false
        let idxC := c.idx.map (·.liftLooseBVars nIh 0)
        let spineAt := fun (o' : Nat) (args : List Expr) =>
          Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (oP + fo + o') nP ++ args)
        let motApp := fun (o' : Nat) (args : List Expr) =>
          Expr.mkAppN (motVar (o + fo + o') m) (liftAll o' idxC ++ [spineAt o' args])
        let packUnpackOf := fun (i : Nat) =>
          let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
          let idx := fieldIdx c i (fo - i)
          (appImpl (packName mem'.j) (oP + fo) idx [appImpl (unpackName mem'.j) (oP + fo) idx [fieldVar i]],
           appImpl (packUnpackName mem'.j) (oP + fo) idx [fieldVar i],
           auxAt fam mem'.tag (oP + fo) idx)
        let rec go (ks : List Nat) (done : List Nat) (acc : Expr) : Expr :=
          match ks with
          | [] => acc
          | k :: rest =>
            let (pu, prf, ty) := packUnpackOf k
            let args := fun (o' : Nat) (z : Expr) => (List.range c.nF).map fun i =>
              if i == k then z
              else if done.contains i then (fieldVar i).liftLooseBVars o' 0
              else if packed.contains i then (packUnpackOf i).1.liftLooseBVars o' 0
              else (fieldVar i).liftLooseBVars o' 0
            let motive : Expr := .lam ty
              (.lam (mkEq u (ty.liftLooseBVars 1 0) (pu.liftLooseBVars 1 0) (.bvar 0))
                (motApp 2 (args 2 (.bvar 1))) bm) bm
            go rest (done ++ [k]) (mkEqRec ℓ u ty pu motive acc (fieldVar k) prf)
        go packed [] X
    mkLams (fbs ++ ihbs) body
  let recAllTy := mkPis (prefixBsL ++ [Expr.mkAppN (constP tag lps) (varsAt (M + n) nP),
      Expr.mkAppN (constP aux lps) (varsAt (M + n + 1) nP ++ [.bvar 0])])
    (Expr.mkAppN (motR 2) [.bvar 1, .bvar 0])
  let recAllVal := mkLams prefixBsL
    (Expr.mkAppN (.const (aux.str "rec") rlvls) (varsAt (M + n) nP ++ [motR 0] ++ recMinors 0))
  (out, heights) := push out heights recAll rlps recAllTy recAllVal
  -- 8. the recursor models
  for mem in mems do
    let rr ← recOf mem
    let ty := rn rr.cv.type
    let nI := mem.nIdx
    let D := rP + nI + 1
    let e := nI + 1
    let prefixVars := varsAt (e + M + n) nP ++ varsAt (e + n) M ++ varsAt e n
    let tagApp := Expr.mkAppN (constP (tagCtorName T mem.tag) lps) (varsAt (e + M + n) nP ++ varsAt 1 nI)
    let body := match mem.real? with
      | some _ => Expr.mkAppN (constP recAll rlps) (prefixVars ++ [tagApp, .bvar 0])
      | none =>
        let idx := varsAt 1 nI
        let oP := e + M + n
        let packX := appImpl (packName mem.j) oP idx [.bvar 0]
        let carr := carrM mem oP idx
        let inner := Expr.mkAppN (constP recAll rlps) (prefixVars ++ [tagApp, packX])
        let up := appImpl (unpackName mem.j) oP idx [packX]
        mkEqRec ℓ u carr up
          (.lam carr
            (.lam (mkEq u (carr.liftLooseBVars 1 0) (up.liftLooseBVars 1 0) (.bvar 0))
              (Expr.mkAppN (motVar (e + 2) mem.tag) (liftAll 2 idx ++ [.bvar 1])) bm) bm)
          inner (.bvar 0) (appImpl (unpackPackName mem.j) oP idx [.bvar 0])
    let value ← need "recursor model" (Expr.pisToLams D ty body)
    (out, heights) := push out heights (modelName rr.cv.name) rlps ty value
  -- 9. the iota theorems
  for mem in mems do
    let rr ← recOf mem
    let own := ctors.filter (·.mem == mem.tag)
    for c in own do
      let nF := c.nF
      let _nIh := nIhOf c
      -- statement frame: prefix (rP) then the fields
      let oP := nF + M + n           -- below the parameters at the statement's end
      let fieldBs := modelDoms c (M + n)
      let fields := (List.range nF).map fun i => Expr.bvar (nF - 1 - i)
      let prefixVars := varsAt (nF + M + n) nP ++ varsAt (nF + n) M ++ varsAt nF n
      let idxC := c.idx.map (rn)   -- at the fields' frame over the parameters: lift past M + n
      let idxC := idxC.map (·.liftLooseBVars (M + n) nF)
      let ctorApp := match mem.real? with
        | some _ => Expr.mkAppN (constP (modelName c.cname) lps) (varsAt oP nP ++ fields)
        | none => Expr.mkAppN (.const c.cname c.clv) ((carrM mem oP []).getAppArgs.take mem.pins.length ++ fields)
      let α := Expr.mkAppN (.bvar (nF + n + (M - 1 - mem.tag))) (idxC ++ [ctorApp])
      let lhs := Expr.mkAppN (.const (modelName rr.cv.name) rlvls) (prefixVars ++ idxC ++ [ctorApp])
      let ihApp := fun (i : Nat) =>
        let t' := (c.kinds.getD i none).getD 0
        let mem' := mems.getD t' default
        let rn' := match mem'.real? with
          | some m' => modelName ((b.types.getD m' default).cv.name.str "rec")
          | none => modelName (T.str s!"rec_{mem'.j + 1}")
        let idxI := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF)
        Expr.mkAppN (.const rn' rlvls) (prefixVars ++ idxI ++ [.bvar (nF - 1 - i)])
      let rhs := Expr.mkAppN (.bvar (nF + (n - 1 - c.J)))
        (fields ++ (List.range nF).filterMap fun i =>
          if (c.kinds.getD i none).isSome then some (ihApp i) else none)
      let stmt := mkPis (prefixBsL ++ fieldBs) (mkEq ℓ α lhs rhs)
      let packed := (List.range nF).filter fun i =>
        match c.kinds.getD i none with | some t' => t' ≥ r | none => false
      let proof ← if packed.isEmpty then
          need "iota proof" (Expr.pisToLams (rP + nF) stmt (mkRefl ℓ α lhs))
        else do
          -- the generalised statement over `(z_k, h_k)` at the packed
          -- positions, innermost base `Eq.refl`
          let uOf := fun (o' : Nat) (i : Nat) =>
            let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
            let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
            appImpl (unpackName mem'.j) (oP + o') idx [appImpl (packName mem'.j) (oP + o') idx [(Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0]]
          let eOf := fun (o' : Nat) (i : Nat) =>
            let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
            let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
            appImpl (unpackPackName mem'.j) (oP + o') idx [(Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0]
          let carrOf := fun (o' : Nat) (i : Nat) =>
            let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
            let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
            carrM mem' (oP + o') idx
          -- R_k: the aux recursor at `pack f_k` (`_impl.rec … (tag.j e⃗) (pack f_k)`)
          let rOf := fun (o' : Nat) (i : Nat) =>
            let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
            let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
            Expr.mkAppN (constP recAll rlps) (liftAll o' prefixVars ++
              [Expr.mkAppN (constP (tagCtorName T mem'.tag) lps) (varsAt (oP + o') nP ++ idx),
               appImpl (packName mem'.j) (oP + o') idx [(Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0]])
          -- the real-kind ihs through the model recursors
          -- generalisation state: for each packed position, either
          -- `.fixed` (at `f_k, e_k`), `.gen d` (bound `z_k`/`h_k` at
          -- depth `d`: `z = bvar (d+1)`, `h = bvar d` relative to the
          -- current frame offset), or `.base` (at `u_k`, `Eq.refl`)
          let stmtAt := fun (o' : Nat) (zs : Nat → Option Expr) (hs : Nat → Option Expr) =>
            -- zs/hs: for packed k, the generalised value/proof at frame o' (none = fixed at f/e)
            let zOf := fun (k : Nat) => (zs k).getD ((Expr.bvar (nF - 1 - k)).liftLooseBVars o' 0)
            let hOfk := fun (k : Nat) => (hs k).getD (eOf o' k)
            let fieldsG := (List.range nF).map fun i =>
              if packed.contains i then zOf i else (Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0
            let idxCG := liftAll o' idxC
            let ctorAppG := match mem.real? with
              | some _ => Expr.mkAppN (constP (modelName c.cname) lps) (varsAt (oP + o') nP ++ fieldsG)
              | none => Expr.mkAppN (.const c.cname c.clv) ((carrM mem (oP + o') []).getAppArgs.take mem.pins.length ++ fieldsG)
            let αG := Expr.mkAppN (motVar (nF + o') mem.tag) (idxCG ++ [ctorAppG])
            -- RHS: the minor at the generalised fields, transported ihs at packed positions
            let rhsG := Expr.mkAppN (minVar (nF + o') c.J)
              (fieldsG ++ (List.range nF).filterMap fun i =>
                match c.kinds.getD i none with
                | some t' =>
                  if t' ≥ r then
                    let carr := carrOf o' i
                    let mem' := mems.getD t' default
                    let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
                    some (mkEqRec ℓ u carr (uOf o' i)
                      (.lam carr
                        (.lam (mkEq u (carr.liftLooseBVars 1 0) ((uOf o' i).liftLooseBVars 1 0) (.bvar 0))
                          (Expr.mkAppN (motVar (nF + o' + 2) mem'.tag) (liftAll 2 idx ++ [.bvar 1])) bm) bm)
                      (rOf o' i) (zOf i) (hOfk i))
                  else some ((ihApp i).liftLooseBVars o' 0)
                | none => none)
            -- LHS: the unfolded recursor: at a real member the transport
            -- chain over the packed positions applied to X; at a mimic
            -- the outer transport along the congruence chain
            let X := Expr.mkAppN (minVar (nF + o') c.J)
              ((List.range nF).map (fun i => if packed.contains i then uOf o' i else (Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0) ++
               (List.range nF).filterMap fun i =>
                 match c.kinds.getD i none with
                 | some t' => if t' ≥ r then some (rOf o' i) else some ((ihApp i).liftLooseBVars o' 0)
                 | none => none)
            let lhsG := match mem.real? with
              | some _ =>
                let packOf := fun (o'' : Nat) (i : Nat) (x : Expr) =>
                  let mem' := mems.getD ((c.kinds.getD i none).getD 0) default
                  let idx := fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll (o' + o'')
                  appImpl (packName mem'.j) (oP + o' + o'') idx [x]
                let spineAt := fun (o'' : Nat) (args : List Expr) =>
                  Expr.mkAppN (constP (auxCtorName' c) lps) (varsAt (oP + o' + o'') nP ++ args)
                let motApp := fun (o'' : Nat) (args : List Expr) =>
                  Expr.mkAppN (motVar (nF + o' + o'') mem.tag) (liftAll o'' idxCG ++ [spineAt o'' args])
                let rec goT (ks : List Nat) (done : List Nat) (acc : Expr) : Expr :=
                  match ks with
                  | [] => acc
                  | k :: rest =>
                    let auxTyK := auxAt fam ((c.kinds.getD k none).getD 0) (oP + o')
                      (fieldIdx c k (nF - k) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o')
                    let args := fun (o'' : Nat) (z : Expr) => (List.range nF).map fun i =>
                      if i == k then z
                      else if packed.contains i then
                        (if done.contains i then packOf o'' i ((zOf i).liftLooseBVars o'' 0)
                         else packOf o'' i ((uOf o' i).liftLooseBVars o'' 0))
                      else (Expr.bvar (nF - 1 - i)).liftLooseBVars (o' + o'') 0
                    let motive : Expr := .lam auxTyK
                      (.lam (mkEq u (auxTyK.liftLooseBVars 1 0) (packOf 1 k ((uOf o' k).liftLooseBVars 1 0)) (.bvar 0))
                        (motApp 2 (args 2 (.bvar 1))) bm) bm
                    let mem' := mems.getD ((c.kinds.getD k none).getD 0) default
                    let idx := fieldIdx c k (nF - k) |>.map rn |>.map (·.liftLooseBVars (M + n) nF) |> liftAll o'
                    let cp := appImpl (congrPackName mem'.j) (oP + o') idx [uOf o' k, zOf k, hOfk k]
                    goT rest (done ++ [k]) (mkEqRec ℓ u auxTyK (packOf 0 k (uOf o' k)) motive acc (packOf 0 k (zOf k)) cp)
                goT packed [] X
              | none =>
                let pinsAt := fun (o'' : Nat) => (carrM mem (oP + o' + o'') []).getAppArgs.take mem.pins.length
                let F := fun (o'' : Nat) (args : List Expr) => Expr.mkAppN (.const c.cname c.clv) (pinsAt o'' ++ args)
                let ls := (List.range nF).map fun i => if packed.contains i then uOf o' i else (Expr.bvar (nF - 1 - i)).liftLooseBVars o' 0
                let rs := fieldsG
                let moved := packed.map fun k => (k, hOfk k, carrOf o' k, u)
                let carr := carrM mem (oP + o') idxCG
                let chain := congrChain u carr F ls rs moved
                mkEqRec ℓ u carr (F 0 ls)
                  (.lam carr
                    (.lam (mkEq u (carr.liftLooseBVars 1 0) ((F 0 ls).liftLooseBVars 1 0) (.bvar 0))
                      (Expr.mkAppN (motVar (nF + o' + 2) mem.tag) (liftAll 2 idxCG ++ [.bvar 1])) bm) bm)
                  X (F 0 rs) chain
            (αG, lhsG, rhsG)
          -- nest the generalisations: outermost over the first packed position
          let rec nest (ks : List Nat) (o' : Nat) (zs : Nat → Option Expr) (hs : Nat → Option Expr) : Expr :=
            match ks with
            | [] =>
              let (αG, lhsG, _) := stmtAt o' zs hs
              mkRefl ℓ αG lhsG
            | k :: rest =>
              -- J on `e_k` with motive `λ z h, stmt[z_k := z, h_k := h]`
              let carr := carrOf o' k
              let zs' := fun (i : Nat) => if i == k then some (Expr.bvar 1) else (zs i).map (·.liftLooseBVars 2 0)
              let hs' := fun (i : Nat) => if i == k then some (Expr.bvar 0) else (hs i).map (·.liftLooseBVars 2 0)
              let (αM, lhsM, rhsM) := stmtAt (o' + 2) zs' hs'
              let motive : Expr := .lam carr
                (.lam (mkEq u (carr.liftLooseBVars 1 0) ((uOf o' k).liftLooseBVars 1 0) (.bvar 0))
                  (mkEq ℓ αM lhsM rhsM) bm) bm
              -- the base: position k at `u_k`, `Eq.refl`
              let zsB := fun (i : Nat) => if i == k then some (uOf o' k) else zs i
              let hsB := fun (i : Nat) => if i == k then some (mkRefl u carr (uOf o' k)) else hs i
              mkEqRec .zero u carr (uOf o' k) motive (nest rest o' zsB hsB) ((Expr.bvar (nF - 1 - k)).liftLooseBVars o' 0) (eOf o' k)
          let body := nest packed 0 (fun _ => none) (fun _ => none)
          need "iota proof" (Expr.pisToLams (rP + nF) stmt body)
      out := out.push (.thmDecl ⟨iotaName rr.cv.name c.jIn, rlps, stmt⟩ proof)
  -- 10. projection artifacts of structure-like non-Prop real members
  -- (under a LARGE eliminator only: `Mutual.lean` step 7)
  let genTypes : List (Name × List Name × Expr) :=
    (b.types.map fun t => (modelName t.cv.name, lps, t.cv.type)) ++
    (b.ctors.map fun c => (modelName c.cv.name, lps, rn c.cv.type))
  let tbl' : ConstTable := fun x =>
    match genTypes.find? (·.1 == x) with
    | some (_, l, ty) => some (l, ty)
    | none => ctx.tbl x
  if !isProp && large then
    for m in List.range r do
      let t := b.types.getD m default
      let own := ctors.filter (·.mem == m)
      let [c] := own | continue
      if t.nIdx != 0 then continue
      let nF := c.nF
      let some pc := b.ctors.find? (·.cv.name == c.cname) | continue
      let cty := rn pc.cv.type
      let some (cbs, _) := cty.stripPis (nP + nF) | continue
      let mut stop := false
      for i in List.range nF do
        if stop then continue
        let ctxI := ((cbs.take (nP + i)).map (·.1)).reverse
        let dom := (cbs.getD (nP + i) default).1
        let some ℓi := sortOf tbl' ctxI dom | stop := true; continue
        let args := structProjPs nP ++ (List.range i).map fun j =>
          Expr.mkAppN (constP (projModelName t.cv.name j) lps) (structProjPs nP ++ [.bvar 0])
        let some (.forallE fdom _ _) := Expr.instPisAtLift args cty | stop := true; continue
        let some pty := Expr.replacePiBody nP t.cv.type
            (.forallE
              (Expr.mkAppN (constP (modelName t.cv.name) lps) (varsAt 0 nP)) fdom bm)
          | stop := true; continue
        -- the value: `λ p⃗ x, aux.rec p⃗ MotP minorsP (tag.m p⃗) x`
        let motP := fun (o : Nat) => dispatchMotive o ℓi fun o2 =>
          mems.map fun mem =>
            let sAt := fun (o' : Nat) => auxAt fam mem.tag o' (varsAt (o' - (o2 + mem.nIdx)) mem.nIdx)
            mkLams (idxBsAt mem o2 ++ [sAt (o2 + mem.nIdx)])
              (if mem.tag == m then
                -- `F_i[f_j := proj_j p⃗ s]`, at frame o2 + 1
                let argsS := structProjPs nP ++ (List.range i).map fun j =>
                  Expr.mkAppN (constP (projModelName t.cv.name j) lps) (structProjPs nP ++ [.bvar 0])
                match Expr.instPisAtLift argsS cty with
                | some (.forallE fd _ _) => fd.liftLooseBVars (o2 + 1 - 1) 1 |> fun x => x.liftLooseBVars 0 0 |> fun _ =>
                    -- fd is at frame `p⃗, x`: lift the parameters past the extras
                    fd.liftLooseBVars o2 1
                | _ => .sort .zero
               else .const punitName [ℓi])
        let minorsP := fun (o : Nat) => ctors.map fun c' =>
          let nIh := nIhOf c'
          let fbs := specDoms c' o
          let ihbs := (List.range c'.nF).filterMap fun i' =>
            match c'.kinds.getD i' none with
            | some t' =>
              let k := ihPos c' i'
              let fo' := c'.nF + k
              some <| Expr.mkAppN (motP (o + fo'))
                  [Expr.mkAppN (constP (tagCtorName T t') lps) (varsAt (o + fo') nP ++ fieldIdx c' i' (fo' - i')),
                   .bvar (fo' - 1 - i')]
            | none => none
          let fo := c'.nF + nIh
          let fieldVar := fun (i' : Nat) => Expr.bvar (nIh + c'.nF - 1 - i')
          let body := if c'.mem == m then
              match c'.kinds.getD i none with
              | some t' =>
                if t' ≥ r then
                  appImpl (unpackName (mems.getD t' default).j) (o + fo) (fieldIdx c' i (fo - i)) [fieldVar i]
                else fieldVar i
              | none => fieldVar i
            else .const punitUnitName [ℓi]
          mkLams (fbs ++ ihbs) body
        let pval := mkLams (pbs ++ [Expr.mkAppN (constP (modelName t.cv.name) lps) (varsAt 0 nP)])
          (Expr.mkAppN (.const (aux.str "rec") ((if large then [ℓi] else []) ++ lps.map .param))
            (varsAt 1 nP ++ [motP 1] ++ minorsP 1 ++
             [Expr.mkAppN (constP (tagCtorName T m) lps) (varsAt 1 nP), .bvar 0]))
        (out, heights) := push out heights (projModelName t.cv.name i) lps pty pval
        -- `proj_i.iota`
        let fields := (List.range nF).map fun l => Expr.bvar (nF - 1 - l)
        let slot := dom.liftLooseBVars (nF - i) 0
        let lhs := Expr.mkAppN (constP (projModelName t.cv.name i) lps)
          (varsAt nF nP ++ [Expr.mkAppN (constP (modelName c.cname) lps) (varsAt nF nP ++ fields)])
        let stmt := mkPis (piBinders cbs) (mkEq ℓi slot lhs (.bvar (nF - 1 - i)))
        let pf := match c.kinds.getD i none with
          | some t' =>
            if t' ≥ r then
              appImpl (unpackPackName (mems.getD t' default).j) nF (fieldIdx c i (nF - i) |>.map rn) [.bvar (nF - 1 - i)]
            else mkRefl ℓi slot (.bvar (nF - 1 - i))
          | none => mkRefl ℓi slot (.bvar (nF - 1 - i))
        let some pfL := Expr.pisToLams (nP + nF) stmt pf | stop := true; continue
        out := out.push (.thmDecl ⟨(projModelName t.cv.name i).str "iota", lps, stmt⟩ pfL)
  pure out.toList

end ConLeche.Frontend.InModel
