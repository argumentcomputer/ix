module

public import Ix.Compile.BinderData
public import Ix.LeanIngress.Expr

public section

/-!
# Binder data read off a record's Lean source

A binder's datum is the zero-ness of its codomain's sort. Most binders show it
in their source without any inference, and this reader takes exactly those:

* **a ∀-run**: the run's body is a type; its sort is read off its head. A sort
  `Sort u` has sort `Sort (u+1)`, never zero. An application `c a₁ … aₙ` of a
  constant whose declared type is exactly `n` ∀s followed by `Sort s` has sort
  `s` at the application's levels; so does an application of a bound variable
  whose declared type has that shape. A body that is itself a ∀ reads its own
  body (the zero-ness of `imax u v` is that of `v`).
* **a λ-run**: every λ of the run has the zero-ness of the sort of the run's
  type, which the reader carries in from where the λ-run stands: a theorem's
  value (always zero), a definition's value (its type's), a `let`'s value (its
  declared type's), an argument of an application of a constant or a bound
  variable (the zero-ness of the sort of the head's domain at that position,
  read as above), a recursor's rule right-hand side (its elimination level's).
  It passes unchanged into the run's body, a `let`'s body and a share.

Anything else (a body headed by a projection, a redex, a match whose motive
computes a sort, a constant whose type is not syntactically such a telescope)
is not read, and the record falls to IxC's pass (`Ix.Compile.KernelAnnotate`):
the reader never guesses. Every datum it does read is the one IxC's pass
computes, because the source is Lean-checked and Lean's conversion has no
equality reflection: an argument's inferred type is definitionally its head's
domain there, and definitionally equal types have equivalent sorts.

The numbering of the data and of share variants is the compiler's
(`Ix.CompileM.withBinderSection`), as IxC's pass gives it: the record's tree
numbers the nodes, a share's entry is read once per context of the variables it
can name, and a variant is a distinct node list.
-/

namespace Ix.Compile.BinderRead

open Ix.Kernel (PropWhen)
open Ix.LeanIngress (Numbering ingressLevel)
open IxVM.PwHints (Node Block)

/-- How the reader finds a constant's declaration. -/
abbrev Find := Ix.Name → Option Ix.ConstantInfo

/-- `e` without its `mdata` wrappers. -/
def unmeta : Ix.Expr → Ix.Expr
  | .mdata _ e _ => unmeta e
  | e => e

/-- A spine's head (without `mdata`) and its argument count. -/
def headArgs : Ix.Expr → Ix.Expr × Nat
  | .app f _ _ => let (h, n) := headArgs f; (h, n + 1)
  | .mdata _ e _ => headArgs e
  | e => (e, 0)

/-- `t` past exactly `n` leading ∀s. -/
def peelN : Nat → Ix.Expr → Option Ix.Expr
  | 0, t => some (unmeta t)
  | n + 1, t => match unmeta t with
    | .forallE _ _ b _ _ => peelN n b
    | _ => none

/-- The `n`-th ∀-domain of `t`, with the domains before it, innermost first. -/
def domainAt : Nat → Ix.Expr → List (Option Ix.Expr) → Option (Ix.Expr × List (Option Ix.Expr))
  | n, t, acc => match unmeta t, n with
    | .forallE _ d _ _ _, 0 => some (d, acc)
    | .forallE _ d b _ _, n + 1 => domainAt n b (some d :: acc)
    | _, _ => none

/-- A constant's own numbering of its level parameters: their positions. -/
def posIn (names : Array Ix.Name) (n : Ix.Name) : Nat :=
  (names.findIdx? (Ix.Name.beqRaw · n)).getD names.size

/-- A definition whose value returns one of its own arguments (`outParam`,
`optParam`, `autoParam`, `semiOutParam`, `id`): its arity and which argument. -/
def wrapperOf : Ix.ConstantInfo → Option (Nat × Nat)
  | .defnInfo d =>
    let rec go : Nat → Ix.Expr → Option (Nat × Nat)
      | m, .lam _ _ b _ _ => go (m + 1) b
      | m, .mdata _ e _ => go m e
      | m, .bvar j _ => if j < m then some (m, m - 1 - j) else none
      | _, _ => none
    go 0 d.value
  | _ => none

/-- The arguments of a spine, outermost first. -/
def spineArgs : Ix.Expr → Array Ix.Expr → Array Ix.Expr
  | .app f a _, acc => spineArgs f (acc.push a)
  | .mdata _ e _, acc => spineArgs e acc
  | _, acc => acc

/-- `t` with argument-returning definitions at its head unfolded (δβ, exact):
`outParam T ↦ T`. -/
def unwrap (find : Find) : Nat → Ix.Expr → Ix.Expr
  | 0, t => t
  | fuel + 1, t =>
    let t := unmeta t
    match headArgs t with
    | (.const c _ _, n) =>
      match (find c).bind wrapperOf with
      | some (m, i) =>
        if m ≤ n then
          let args := (spineArgs t #[]).reverse
          match args[i]? with
          | some a => unwrap find fuel (args.extract m args.size |>.foldl (fun f x => Ix.Expr.mkApp f x) a)
          | none => t
        else t
      | none => t
    | _ => t

/-- The final sort of a ∀-telescope `t`, if it is syntactically a sort. -/
def leafSort : Ix.Expr → Option Ix.Level
  | .sort l _ => some l
  | .forallE _ _ b _ _ => leafSort b
  | .mdata _ e _ => leafSort e
  | _ => none

/-- **The zero-ness of the sort of the type `t`, read syntactically.** `σ`
numbers the level parameters `t` and `ctx` (the types of `t`'s loose variables,
innermost first) are written over, and `sub` maps levels in that numbering to
the reader's. `none` where the reading does not apply. -/
def sortPw (find : Find) (σ : Ix.Name → Nat) (sub : Ix.Kernel.Level → Ix.Kernel.Level) :
    Nat → List (Option Ix.Expr) → Ix.Expr → Option PropWhen
  | 0, _, _ => none
  | fuel + 1, ctx, t =>
    match unwrap find 8 t with
    | .sort _ _ => some .never
    | .forallE _ d b _ _ => sortPw find σ sub fuel (some d :: ctx) b
    | t =>
      let (h, n) := headArgs t
      let lvl? : Option Ix.Kernel.Level := match h with
        | .const c us _ => do
          let ci ← find c
          let cv := ci.getCnst
          let .sort l _ := unwrap find 8 (← peelN n cv.type) | none
          let lc ← (ingressLevel (posIn cv.levelParams) l).toOption
          let us' ← (us.toList.mapM (ingressLevel σ)).toOption
          pure (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us' lc)
        | .bvar i _ => do
          let ty ← (ctx[i]?).join
          let .sort l _ := unwrap find 8 (← peelN n ty) | none
          (ingressLevel σ l).toOption
        | _ => none
      lvl?.map fun l => Ix.Kernel.Level.zeronessOf (sub l)

/-- The zero-ness of the sort of the domain at `idx` of the type of the spine
head `h` (a constant, or a bound variable under `ctx`): what an argument there
has as its type's sort. -/
def argPw (find : Find) (σ : Ix.Name → Nat) (ctx : List (Option Ix.Expr)) (h : Ix.Expr)
    (idx : Nat) : Option PropWhen :=
  match h with
  | .const c us _ => do
    let ci ← find c
    let cv := ci.getCnst
    let (d, before) ← domainAt idx cv.type []
    let us' ← (us.toList.mapM (ingressLevel σ)).toOption
    sortPw find (posIn cv.levelParams) (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us')
      64 before d
  | .bvar i _ => do
    let ty ← (ctx[i]?).join
    let (d, before) ← domainAt idx ty []
    sortPw find σ id 64 (before ++ ctx.drop (i + 1)) d
  | _ => none

/-! ## The reading of a record -/

/-- What a record's reading reads. -/
structure Cx where
  find : Find
  /-- the root's numbering of level parameters -/
  σ : Numbering
  sharing : Array Ixon.Expr
  bounds : Array Nat

/-- A source level parameter's index in the record's numbering (the inverse of
`Numbering.pos`: a large eliminator's source numbers its motive universe last,
the record first). -/
def Cx.recordParam (cx : Cx) (p : Nat) : Nat :=
  if cx.σ.large then (if p + 1 == cx.σ.names.size then 0 else p + 1) else p

/-- The node of a datum, its parameters in the record's numbering. -/
def Cx.nodeOf (cx : Cx) (pw : PropWhen) : Node :=
  match pw.toList? with
  | none => .binder none
  | some ps => .binder (some ((ps.map cx.recordParam).toArray.qsort (· < ·)))

/-- The reading's state: the sharing entries' variants (by node list) and
blocks, and the memo of share sites (entry, the types its variables can name,
the expectation, the source term). -/
structure RState where
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × List (Option Address) × Option PropWhen × Address) Nat := {}

/-- A reading fails (`none`) at the first binder it cannot read. -/
abbrev RM := StateT RState Option
/-- An entry's reading: its nodes' data, by ordinal. -/
abbrev NM := StateT (Array Node) RM

private def reserve : NM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : NM Unit :=
  modify fun nodes => nodes.set! ord n

private def variantOf (n : Nat) (nodes : Array Node) : RM Nat := do
  let st ← get
  let table := st.variants.getD n {}
  match table[nodes]? with
  | some v => pure v
  | none =>
    let v := table.size
    set { st with variants := st.variants.insert n (table.insert nodes v)
                  blocks := st.blocks.push ⟨1, n, v, nodes⟩ }
    pure v

/-- A run of binders of one kind in the record's tree and its source: each
binder's domain in both, then both bodies. -/
def binderRun (pi : Bool) : Ixon.Expr → Ix.Expr → Array (Ixon.Expr × Ix.Expr) →
    Ixon.Expr × Ix.Expr × Array (Ixon.Expr × Ix.Expr)
  | e@(.lam _ t b), x, acc => match unmeta x with
    | .lam _ ty body _ _ => if pi then (e, x, acc) else binderRun pi b body (acc.push (t, ty))
    | _ => (e, x, acc)
  | e@(.all _ _ t b), x, acc => match unmeta x with
    | .forallE _ ty body _ _ => if pi then binderRun pi b body (acc.push (t, ty)) else (e, x, acc)
    | _ => (e, x, acc)
  | e, x, acc => (e, x, acc)

/-- Bounds the reading's depth. -/
def readFuel : Nat := 1 <<< 24

/-- **The reading of one entry's tree `e` beside its source `x`**, under `ctx`
(the types of the bound variables, innermost first; `none` for a `let`'s), with
`ex` the zero-ness of the sort of `x`'s type where it is known. Every numbered
node of `e` gets its datum at its ordinal; the reading fails where a datum is not
read. -/
def read : Nat → Cx → List (Option Ix.Expr) → Option PropWhen → Ixon.Expr → Ix.Expr → NM Unit
  | 0, _, _, _, _, _ => failure
  | fuel + 1, cx, ctx, ex, e, x =>
    match e, unmeta x with
    | .var _, .bvar .. => pure ()
    | .app f a, .app xf xa _ => do
      read fuel cx ctx none f xf
      let (h, n) := headArgs xf
      read fuel cx ctx (argPw cx.find cx.σ.pos ctx h n) a xa
    | .lam .., .lam .. | .all .., .forallE .. => do
      let pi := e matches .all ..
      let (leafE, leafX, bs) := binderRun pi e x #[]
      let mut inner := ctx
      let mut ords : Array Nat := #[]
      for h : j in [:bs.size] do
        let (t, ty) := bs[j]
        ords := ords.push (← reserve)
        read fuel cx inner none t ty
        inner := some ty :: inner
      read fuel cx inner (if pi then none else ex) leafE leafX
      let pw? := if pi then sortPw cx.find cx.σ.pos id 64 inner leafX else ex
      let some pw := pw? | failure
      let node := cx.nodeOf pw
      for ord in ords do setNode ord node
    | .letE _ t v b, .letE _ ty val body _ _ => do
      read fuel cx ctx none t ty
      read fuel cx ctx (sortPw cx.find cx.σ.pos id 64 ctx ty) v val
      read fuel cx (some ty :: ctx) ex b body
    | .prj _ _ v, .proj _ _ xv _ => read fuel cx ctx none v xv
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, (ctx.take (cx.bounds[n]?.getD 0)).map (·.map Ix.Expr.getHash), ex, x.getHash)
      let variant ← match (← getThe RState).memo[key]? with
        | some v => pure v
        | none => do
          let some entry := cx.sharing[n]? | failure
          let ((), nodes) ← ((read fuel cx ctx ex entry x).run #[] : RM (Unit × Array Node))
          let v ← variantOf n nodes
          modifyThe RState fun st => { st with memo := st.memo.insert key v }
          pure v
      setNode ord (.share variant)
    | .sort _, .sort .. | .ref .., .const .. | .recur .., .const .. | .str _, .lit .. | .nat _, .lit .. =>
      pure ()
    | _, _ => failure

/-! ## A record's roots and their expectations -/

/-- A root's source, its numbering, and the zero-ness of its type's sort where
the reading needs it (a value's, a rule right-hand side's). -/
structure Root where
  σ : Numbering
  x : Ix.Expr
  ex : Option PropWhen := none

/-- The zero-ness of the sort of a definition's type `ty`, numbered by `σ`. -/
def typePw (find : Find) (σ : Numbering) (ty : Ix.Expr) : Option PropWhen :=
  sortPw find σ.pos id 64 [] ty

/-- A member's roots, in section order, when its kind is the record member's
(`IxVM.PwHints.roots`): a definition's type and value, an axiom's or a
quotient's type, an inductive's type and its constructors' types, a recursor's
type and its rules' right-hand sides. -/
def memberRoots (find : Find) (ci : Ix.ConstantInfo) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Option (Array Root)
  | .inl (.defn _) | .inr (.defn _) =>
    let σ : Numbering := ⟨ci.getCnst.levelParams, false⟩
    match ci with
    | .defnInfo d => some #[⟨σ, d.cnst.type, none⟩, ⟨σ, d.value, typePw find σ d.cnst.type⟩]
    | .thmInfo t => some #[⟨σ, t.cnst.type, none⟩, ⟨σ, t.value, some (PropWhen.ifAllZero [])⟩]
    | .opaqueInfo o => some #[⟨σ, o.cnst.type, none⟩, ⟨σ, o.value, typePw find σ o.cnst.type⟩]
    | _ => none
  | .inr (.axio _) => match ci with
    | .axiomInfo a => some #[⟨⟨a.cnst.levelParams, false⟩, a.cnst.type, none⟩]
    | _ => none
  | .inr (.quot _) => match ci with
    | .quotInfo q => some #[⟨⟨q.cnst.levelParams, false⟩, q.cnst.type, none⟩]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => do
      guard (v.rules.size == r.rules.size)
      let indLevels := match v.all[0]?.bind find with
        | some (.inductInfo i) => i.cnst.levelParams.size
        | _ => v.cnst.levelParams.size
      let σ : Numbering := ⟨v.cnst.levelParams, v.cnst.levelParams.size == indLevels + 1⟩
      -- a rule's right-hand side has the sort of its motive's codomain: the
      -- elimination level
      let elim : Option PropWhen := do
        let (motive, _) ← domainAt v.numParams v.cnst.type []
        let l ← leafSort motive
        let l' ← (ingressLevel σ.pos l).toOption
        pure (Ix.Kernel.Level.zeronessOf l')
      some ((#[⟨σ, v.cnst.type, none⟩] : Array Root) ++ v.rules.map fun rule => (⟨σ, rule.rhs, elim⟩ : Root))
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let ctors ← v.ctors.mapM fun n => match find n with
        | some (.ctorInfo k) => some (⟨⟨k.cnst.levelParams, false⟩, k.cnst.type, none⟩ : Root)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some ((#[⟨⟨v.cnst.levelParams, false⟩, v.cnst.type, none⟩] : Array Root) ++ ctors)
    | _ => none
  | _ => none

/-- The block's members, as the record lists them. -/
def members (c : Ixon.Constant) : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) :=
  match c.info with
  | .muts ms => ms.map .inl
  | info => #[.inr info]

/-- **The section of a block record, read off its members' sources** (`names`,
in the record's member order), or `none` where some binder is not read. -/
def section? (find : Find) (names : Array Ix.Name) (c : Ixon.Constant) :
    Option (Array Ixon.BinderBlock) := do
  let ms := members c
  guard (ms.size == names.size)
  let mut roots : Array Root := #[]
  for (m, n) in ms.zip names do
    let ci ← find n
    roots := roots ++ (← memberRoots find ci m)
  let rs := IxVM.PwHints.roots c
  guard (roots.size == rs.size)
  let bounds := IxVM.PwHints.bounds c.sharing
  let act : RM (Array Block) := do
    let mut out := #[]
    for h : i in [:rs.size] do
      let some r := roots[i]? | failure
      let cx : Cx := { find, σ := r.σ, sharing := c.sharing, bounds }
      let ((), nodes) ← (read readFuel cx [] r.ex rs[i] r.x).run #[]
      out := out.push ⟨0, i, 0, nodes⟩
    return out
  let (blocks, st) ← act.run {}
  (Ix.Compile.BinderData.sectionOf c (blocks ++ st.blocks)).toOption

end Ix.Compile.BinderRead

end
