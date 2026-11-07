import IxCC.Anf.Walk

/-! # P4: bounded specialisation

`Anf.Specialize` (design note 02 §8, P4). A **decision** asks for the calls
of a global `g` from a caller `f` to be specialised on the parameters of a
mask. At each such call site the pass

1. checks the mask with the **fixed-parameter checker** (`fixedIn`): every
   call of `g` in `g`'s own body passes each masked parameter unchanged
   (else the site is left alone);
2. builds each masked argument's **value tree** from the caller's
   definitions in scope: constructors (never one whose contract is
   `unique`, 06 S37), literals, function globals and local functions (whose
   free variables are followed in turn); an unknown value is a **hole**,
   i.e. an extra parameter (Lean's abstraction), and so is every operand
   left when the tree walk runs out of fuel;
3. keys the specialisation `GKey.spec (key g) args` (D19), with `args` one
   `ArgKey` per parameter: the masked argument's tree over constructor keys,
   literals and global keys (a local function is named by its origin,
   `glob (lam f [inv, i])`, the `i`-th λ of `f`'s body in invocation `inv`,
   which determines its body and free variables), and `hole k` for an
   unmasked parameter or an abstracted value. A specialisation this run
   made with an equal key is shared when it is exactly the one this site
   would build (same arity, same body calling itself);
3. otherwise creates the specialisation: parameters are the holes;
   a prologue rebuilds the known definitions (a copy of each needed
   binding, in their original order), then `g`'s body follows with each
   masked parameter bound to its tree and every call of `g` whose masked
   arguments are exactly those values redirected to the specialisation;
4. calls it with the holes' values. The generic `g` is kept.

The pass is correct for every decision list (a decision that fails the
checker, or a site where no masked argument is known, changes nothing).
Recursion is structural or on fuel, maps are `NatMap`s (kernel-evaluable,
D17). Mutually recursive groups are not copied (Phase 1): calls from other
members of `g`'s group keep calling the generic `g`. -/

namespace IxCC.Anf.Specialize

open IxCC.Ixon
open Walk (Ent)

/-- In caller `caller`, specialise the calls of `callee` on the parameters
marked `true`. -/
structure Decision where
  caller : GlobalId
  callee : GlobalId
  mask : List Bool
  deriving Repr, Inhabited

structure Cert where
  /-- The invocation number (names local functions in keys). -/
  inv : Nat := 0
  decisions : List Decision := []
  deriving Repr, Inhabited

/-- What a caller level holds, when known. -/
inductive Def where
  | con (c : Key.CtorKey) (fs : List Opd)
  | lit (n : Nat)
  /-- A function global's closure. -/
  | glob (g : GlobalId)
  /-- A local function: its definition depth, parameters, body and pre-order
  index in the caller. -/
  | fn (d : Nat) (ps : List V3.BinderContract) (body : Exp) (idx : Nat)
  | blank

/-! ## The fixed-parameter checker -/

/-- Every masked argument of every call of `g` in `e` is the parameter
itself (parameter `i` is level `i`; `e` is under `d` binders). -/
def fixedArgs (mask : List Bool) (d : Nat) (as : List Atom) : Bool :=
  as.length == mask.length &&
  (as.zipIdx.zip mask).all fun ((a, i), m) => !m || a == .var (d - 1 - i)

mutual

def fixedIn (g : GlobalId) (mask : List Bool) (d : Nat) : Exp → Bool
  | .bind _ b e => fixedInBind g mask d b && fixedIn g mask (d + 1) e
  | .join n _ b e => fixedIn g mask (d + n) b && fixedIn g mask d e
  | .case _ alts dflt => fixedInAlts g mask d alts && fixedInOpt g mask d dflt
  | .tick e => fixedIn g mask d e
  | .jump .. | .ret _ | .trap => true

def fixedInBind (g : GlobalId) (mask : List Bool) (d : Nat) : Bind → Bool
  | .call g' as => g' != g || fixedArgs mask d as
  | .fn ps b => fixedIn g mask (d + ps.length) b
  | _ => true

def fixedInAlts (g : GlobalId) (mask : List Bool) (d : Nat) : List Alt → Bool
  | [] => true
  | .mk _ n b :: as => fixedIn g mask (d + n) b && fixedInAlts g mask d as

def fixedInOpt (g : GlobalId) (mask : List Bool) (d : Nat) : Option Exp → Bool
  | none => true
  | some e => fixedIn g mask d e

end

/-- The checker on a global: `mask` has its arity and holds. -/
def fixedOk (gd : GDef) (g : GlobalId) (mask : List Bool) : Bool :=
  mask.length == gd.ps.length && fixedIn g mask gd.ps.length gd.body

/-! ## Value trees, holes and keys -/

/-- Where a hole's value comes from at the call site. -/
inductive HoleSrc where
  /-- An unmasked parameter's argument. -/
  | param (i : Nat)
  /-- A caller variable (by level) whose value is not known. -/
  | level (l : Nat)
  /-- A constant operand without a key (□, a string). -/
  | atom (o : Opd)
  deriving Inhabited

/-- The state of the tree walk at one site. -/
structure Trees where
  holes : List HoleSrc := []
  /-- Levels that are holes, with their hole index. -/
  levelHoles : List (Nat × Nat) := []
  /-- Levels to rebuild in the prologue. -/
  needed : List Nat := []

def Trees.hole (t : Trees) (s : HoleSrc) : Trees × Nat :=
  ({ t with holes := t.holes ++ [s] }, t.holes.length)

def Trees.levelHole (t : Trees) (l : Nat) : Trees × Nat :=
  match t.levelHoles.lookup l with
  | some h => (t, h)
  | none =>
    let (t, h) := t.hole (.level l)
    ({ t with levelHoles := t.levelHoles ++ [(l, h)] }, h)

/-- Distinct elements, first occurrences first (structural). -/
def dedup (xs : List Nat) : List Nat :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

/-- Insert into an ascending list (structural). -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Ascending order (insertion sort; the lists are short). -/
def sortNats (xs : List Nat) : List Nat := xs.foldl (fun acc x => insertSorted x acc) []

/-- Key of a global. -/
def gkey (P : Program) (g : GlobalId) : Key.GKey := ((P.global? g).map (·.key)).getD (.dispatch 0)

/-- Rebuild level `l` in the prologue (once). -/
def Trees.need (t : Trees) (l : Nat) : Trees :=
  if t.needed.contains l then t else { t with needed := t.needed ++ [l] }

/-- An unknown value: a hole (one per level). -/
def Trees.holeOf (t : Trees) : Opd → Trees × Key.ArgKey
  | .lvl l => let (t, h) := t.levelHole l; (t, .hole h)
  | o => let (t, h) := t.hole (.atom o); (t, .hole h)

/-- Every operand of a list unknown: holes. -/
def Trees.holesOf (t : Trees) : List Opd → Trees × List Key.ArgKey
  | [] => (t, [])
  | o :: os =>
    let (t, k) := t.holeOf o
    let (t, ks) := t.holesOf os
    (t, k :: ks)

mutual

/-- The key of an operand's value tree, collecting holes and needed
levels. -/
def tree (P : Program) (defs : Src.NatMap Def) (fkey : Key.GKey) (inv : Nat) :
    Nat → Trees → Opd → Trees × Key.ArgKey
  | 0, t, o => t.holeOf o
  | fuel + 1, t, o =>
    match o with
    | .lit (.nat n) => (t, .lit n)
    | .lvl l =>
      -- a shared definition is described again in full (the key describes
      -- the value) and rebuilt once
      match defs.get? l with
      | some (.con c fs) =>
        let (t, ks) := trees P defs fkey inv fuel (t.need l) fs
        (t, .con c ks)
      | some (.lit n) => (t, .lit n)
      | some (.glob g) => (t.need l, .glob (gkey P g))
      | some (.fn df ps b idx) =>
        let frees := (dedup (b.free ps.length)).map fun j => Opd.lvl (df - 1 - j)
        let (t, _) := trees P defs fkey inv fuel (t.need l) frees
        (t, .glob (.lam fkey [inv, idx]))
      | _ => t.holeOf o
    | o => t.holeOf o

def trees (P : Program) (defs : Src.NatMap Def) (fkey : Key.GKey) (inv : Nat) :
    Nat → Trees → List Opd → Trees × List Key.ArgKey
  -- out of fuel: the remaining operands are holes (never dropped: a dropped
  -- field would be rebuilt as □)
  | 0, t, os => t.holesOf os
  | _, t, [] => (t, [])
  | fuel + 1, t, o :: os =>
    let (t, k) := tree P defs fkey inv fuel t o
    let (t, ks) := trees P defs fkey inv fuel t os
    (t, k :: ks)

end

/-! ## Building a specialisation -/

/-- The operand of a caller operand inside the specialisation: a rebuilt
level, a hole's parameter, or the literal a level is known to hold. -/
def mapOpd (defs : Src.NatMap Def) (m : List (Nat × Opd)) : Opd → Opd
  | .lvl l =>
    match m.lookup l, defs.get? l with
    | some o, _ => o
    | none, some (.lit n) => .lit (.nat n)
    | none, _ => .box
  | o => o

/-- The prologue: rebuild the needed levels (ascending) from target level
`t`, returning the binders (outermost first) and the level map. -/
def prologue (P : Program) (defs : Src.NatMap Def) (m : List (Nat × Opd)) (t : Nat) :
    List Nat → Except String (List Bind × List (Nat × Opd))
  | [] => pure ([], m)
  | l :: ls => do
    let b ← match defs.get? l with
      | some (.con c fs) => pure (Bind.con c (fs.map fun o => (mapOpd defs m o).atom t))
      | some (.glob g) => pure (Bind.glob g)
      | some (.fn df ps body _) => do
        let n := ps.length
        let captured := (List.range df).map fun j => Ent.opd (mapOpd defs m (.lvl (df - 1 - j)))
        let (body', _) ← (Walk.walk { prog := P } Walk.fuel
          { σ := Walk.entsOf (paramOpds t n) ++ captured }
          { d := t + n, dj := 0, facts := .leaf } body .ret).run {}
        pure (Bind.fn ps body')
      | _ => throw s!"specialize: level {l} has no definition"
    let (bs, m) ← prologue P defs ((l, .lvl t) :: m) (t + 1) ls
    return (b :: bs, m)

/-- Wrap binders around a body. -/
def binds : List Bind → Exp → Exp
  | [], e => e
  | b :: bs, e => .bind freshLet b (binds bs e)

/-- The state of the pass. -/
structure St where
  /-- The program so far: the input's globals (callers rewritten) and the
  specialisations created. -/
  prog : Program
  /-- The next local function's pre-order index in the current caller. -/
  fns : Nat := 0
  specs : Nat := 0

abbrev M := StateT St (Except String)

/-- One argument of a site: a masked argument's value tree (and its root),
or a hole for an unmasked one. -/
def siteStep (src : Program) (defs : Src.NatMap Def) (fkey : Key.GKey) (inv : Nat)
    (acc : Trees × List Key.ArgKey × List (Nat × Opd)) (x : (Opd × Nat) × Bool) :
    Trees × List Key.ArgKey × List (Nat × Opd) :=
  let (t, ks, roots) := acc
  let ((o, i), masked) := x
  if masked then
    let (t, k) := tree src defs fkey inv (4 * src.size + 1024) t o
    (t, ks ++ [k], roots ++ [(i, o)])
  else
    let (t, h) := t.hole (.param i)
    (t, ks ++ [.hole h], roots)

/-- A site's trees, its keys parameter by parameter, and its masked
arguments' roots. -/
def siteTrees (src : Program) (defs : Src.NatMap Def) (fkey : Key.GKey) (inv : Nat) (d : Nat)
    (mask : List Bool) (as : List Atom) : Trees × List Key.ArgKey × List (Nat × Opd) :=
  ((as.map (·.opd d)).zipIdx.zip mask).foldl (siteStep src defs fkey inv) (({} : Trees), [], [])

/-- The arguments of a specialised call: each hole's value at the site. -/
def siteArgs (t : Trees) (d : Nat) (as : List Atom) : List Atom :=
  t.holes.map fun
    | .param i => as.getD i .box
    | .level l => Opd.atom d (.lvl l)
    | .atom o => o.atom d

/-- A masked parameter's operand in the specialisation's frame. -/
def specFixed (defs : Src.NatMap Def) (roots : List (Nat × Opd)) (m : List (Nat × Opd)) (i : Nat) :
    Option Opd :=
  (roots.lookup i).map fun o => mapOpd defs m o

/-- The hole of an unmasked parameter. -/
def holeIdx (t : Trees) (i : Nat) : Option Nat :=
  ((t.holes.zipIdx.find? fun (s, _) => match s with
    | .param j => j == i
    | _ => false) : Option (HoleSrc × Nat)).map (·.2)

/-- A parameter's operand in the specialisation's frame. -/
def specParam (defs : Src.NatMap Def) (roots : List (Nat × Opd)) (m : List (Nat × Opd)) (t : Trees)
    (i : Nat) : Opd :=
  match specFixed defs roots m i with
  | some o => o
  | none => .lvl ((holeIdx t i).getD 0)

/-- The redirection of calls of `g` to the specialisation `s`. -/
def specRedirect (defs : Src.NatMap Def) (roots : List (Nat × Opd)) (m : List (Nat × Opd)) (t : Trees)
    (g : GlobalId) (n : Nat) (s : GlobalId) : Walk.Redirect :=
  { g, spec := s, fixedArgs := (List.range n).map (specFixed defs roots m)
    holes := t.holes.zipIdx.map fun (h, k) => match h with
      | .param i => .param i
      | _ => .fixed (.lvl k) }

/-- The specialisation a site builds, calling itself as `s`: holes are its
parameters, the prologue rebuilds the needed definitions, then `g`'s body
walked with each parameter bound to its operand and calls redirected. -/
def buildSpec (src : Program) (defs : Src.NatMap Def) (t : Trees) (roots : List (Nat × Opd))
    (g : GlobalId) (gd : GDef) (key : Key.GKey) (s : GlobalId) : Except String GDef := do
  let H := t.holes.length
  let m0 : List (Nat × Opd) := t.levelHoles.map fun (l, h) => (l, .lvl h)
  let (pro, m) ← prologue src defs m0 H (sortNats t.needed)
  let n := gd.ps.length
  let σ := (List.range n).reverse.map fun i => Ent.opd (specParam defs roots m t i)
  let r := specRedirect defs roots m t g n s
  let (body, _) ← (Walk.walk { prog := src, redirect := some r } Walk.fuel { σ }
    { d := H + pro.length, dj := 0, facts := .leaf } gd.body .ret).run {}
  let ps := t.holes.map fun
    | .param i => gd.ps.getD i {}
    | _ => {}
  return { key, ps, result := gd.result, body := binds pro body }

/-- The specialisation for a site, shared with an equal-keyed global that is
exactly what this site builds, created otherwise; `none` when no masked
argument is known. -/
def specialize (src : Program) (inv : Nat) (fkey : Key.GKey) (defs : Src.NatMap Def) (d : Nat)
    (g : GlobalId) (gd : GDef) (mask : List Bool) (as : List Atom) :
    M (Option (GlobalId × List Atom)) := do
  let (t, keys, roots) := siteTrees src defs fkey inv d mask as
  -- nothing known, or nothing left to pass (a specialisation is a function,
  -- never a CAF): leave the call
  if t.holes.isEmpty || roots.all (fun (_, o) => match o with
      | .lvl l => (t.levelHoles.lookup l).isSome
      | .lit (.nat _) => false
      | _ => true) then
    return none
  let key := Key.GKey.spec gd.key keys
  let st ← get
  let args := siteArgs t d as
  let create := do
    let s := st.prog.size
    let spec ← liftM (buildSpec src defs t roots g gd key s)
    let gs := st.prog.globalList.map (fun (p : GlobalId × GDef) => p.2)
    set { st with prog := st.prog.withGlobals (gs ++ [spec]),
                  specs := st.specs + 1 }
    return some (s, args)
  -- a specialisation this run made with this key is shared when it is exactly
  -- the one this site would build (same arity and body, calling itself); the
  -- input's globals never are (a later caller's rewrite may change them)
  match st.prog.globalList.find? (fun (s', gd') => decide (src.size ≤ s') && decide (gd'.key = key)) with
  | some (s, gd') =>
    let spec ← liftM (buildSpec src defs t roots g gd key s)
    if spec.ps.length == gd'.ps.length && spec.body.beq gd'.body then return some (s, args)
    else create
  | none => create
where
  liftM {α : Type} (x : Except String α) : M α := StateT.lift x

/-- The definition a binding gives its level. -/
def defOf (d : Nat) (defs : Src.NatMap Def) (c : V3.LetContract) (b : Bind) (idx : Nat) : Def :=
  match b with
  | .con cc as =>
    if c.binder.value.owned == .unique then .blank else .con cc (as.map (·.opd d))
  | .atom (.lit (.nat n)) => .lit n
  | .atom (.var i) => (defs.get? (d - 1 - i)).getD .blank
  | .glob g => .glob g   -- only recorded for function globals (checked by the caller)
  | .fn ps body => .fn d ps body idx
  | _ => .blank

/-- Rewrite a caller body (in place; levels are depths). -/
def rewrite (src : Program) (inv : Nat) (fkey : Key.GKey) (D : List (GlobalId × List Bool)) :
    Nat → Src.NatMap Def → Nat → Exp → M Exp
  | 0, _, _, _ => throw "specialize: fuel"
  | fuel + 1, defs, d, e =>
    let blank := fun (defs : Src.NatMap Def) (base n : Nat) =>
      (List.range n).foldl (fun m i => m.insert (base + i) Def.blank) defs
    match e with
    | .bind c b body => do
      let idx ← match b with
        | .fn .. => modifyGet fun s => (s.fns, { s with fns := s.fns + 1 })
        | _ => pure 0
      let b' ← match b with
        | .fn ps fb => do
          let fb' ← rewrite src inv fkey D fuel (blank defs d ps.length) (d + ps.length) fb
          pure (Bind.fn ps fb')
        | .call g as =>
          match D.lookup g, src.global? g with
          | some mask, some gd =>
            if fixedOk gd g mask then do
              match ← specialize src inv fkey defs d g gd mask as with
              | some (s, args) => pure (Bind.call s args)
              | none => pure b
            else pure b
          | _, _ => pure b
        | _ => pure b
      let df := match b with
        | .glob g => if ((src.arity? g).getD 0) > 0 then Def.glob g else Def.blank
        | _ => defOf d defs c b idx
      return .bind c b' (← rewrite src inv fkey D fuel (defs.insert d df) (d + 1) body)
    | .join n r jb body =>
      return .join n r (← rewrite src inv fkey D fuel (blank defs d n) (d + n) jb)
        (← rewrite src inv fkey D fuel defs d body)
    | .case x alts dflt => do
      let alts' ← alts.mapM fun a =>
        match a with
        | .mk key n b => return .mk key n (← rewrite src inv fkey D fuel (blank defs d n) (d + n) b)
      let dflt' ← match dflt with
        | some e => some <$> rewrite src inv fkey D fuel defs d e
        | none => pure none
      return .case x alts' dflt'
    | .tick b => return .tick (← rewrite src inv fkey D fuel defs d b)
    | e => pure e

/-- P4 re-run on its certificate. -/
def run (cert : Cert) (P : Program) : Except String Program := do
  let step := fun (st : St) ((f, gd) : GlobalId × GDef) => do
    let D := (cert.decisions.filter (·.caller == f)).map fun d => (d.callee, d.mask)
    if D.isEmpty then pure st else
    let n := gd.ps.length
    let (body, st) ← (rewrite P cert.inv gd.key D (4 * gd.body.nodes + 64)
      (Src.NatMap.ofList ((List.range n).map (·, Def.blank))) n gd.body).run { st with fns := 0 }
    let gs := st.prog.globalList.map fun (g, gd') => if g == f then { gd' with body } else gd'
    pure { st with prog := st.prog.withGlobals gs }
  let st ← P.globalList.foldlM step { prog := P }
  return st.prog

/-! ## The default oracle (`produce`; not on the recheck path) -/

/-- The parameters a self-recursive global passes unchanged to every call of
itself (none if it never calls itself). -/
def fixedMask (g : GlobalId) (gd : GDef) : List Bool :=
  if (gd.body.sites.contains g) then
    (List.range gd.ps.length).map fun i =>
      fixedIn g ((List.range gd.ps.length).map (· == i)) gd.ps.length gd.body
  else []

structure Budgets where
  /-- Specialisations per invocation (Lean's `maxRecSpecialize` is 64). -/
  maxSpecs : Nat := 64
  deriving Repr, Inhabited

/-- Lean's `@[specialize]` default for fixed instance and higher-order
arguments: in every caller, specialise each self-recursive callee on the
parameters it passes unchanged to itself (sites whose masked arguments are
all unknown are left alone by the pass). -/
def produce (_B : Budgets) (inv : Nat) (P : Program) : Cert :=
  let masks := P.globalList.map fun (g, gd) => (g, fixedMask g gd)
  let ds := P.globalList.flatMap fun (f, gd) =>
    gd.body.sites.eraseDups.filterMap fun g =>
      match masks.lookup g with
      | some mask => if g != f && mask.any id then some { caller := f, callee := g, mask } else none
      | none => none
  { inv, decisions := ds }

end IxCC.Anf.Specialize
