import IxCCCorrect.Shape2Check

/-!
# An untrusted shape producer (`IxCCCorrect.Shape2Produce`)

`produce p root` proposes a certificate (`Cert`) for a checked source program: the
instances a root reaches, the enumerations and the table of data entries. **Nothing
here is proved and nothing needs to be**: the certificate is checked by
`certOk` (`IxCCCorrect.Shape2Check`), and a wrong proposal is refused there.

How it works. Shapes are read off the declared types of constants, which the checker
never looks at. A type is evaluated to a small value (`TV`): the shape of its
members, "a proposition" (members are proofs, shape `irr`), a type-level function (a
motive, a type constructor argument), or unknown. Evaluating an inductive applied to
its parameters creates the table entry of that instance (`mkData`), whose field
shapes are read off the constructors' types under the parameters. From the root, each
instance's body is walked (`walk`); at every application of a constant, the shape of
that use is the constant's declared type read under the type arguments of the use
(`piShape`), and an argument is irrelevant where the application says so. Unknown
means `irr`. Everything is by fuel.

**Fields whose type quantifies over types** (a method of a dictionary: `bind : ∀ {α β},
m α → (α → m β) → m β`) have no shape of their own. Their shape is the intersection of
the shapes they are *used* at: a use is an instance of the structure's projection
function, whose type arguments are ground at the use. The argument that builds such a
field (a *site*) is not walked where it stands; it is walked once per use, with the
type arguments of that use bound to its leading λs, so that what it calls is
instantiated at the use's types. A field nobody uses gets `any`.

Known limits (each a refusal by the checker, never an unsound acceptance): a
`let`-bound λ, type arguments the instance of a polymorphic constant does not carry
to an inner λ, recursors' rule bodies (not walked), a method read by matching on the
dictionary rather than through its projection function, polymorphic recursion (no
finite set of instances).
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape2.Produce

open IxCC.Src

/-- What a type-level term evaluates to. -/
inductive TV where
  /-- a type whose members have this shape -/
  | sh (s : Shape)
  /-- a proposition: its members are proofs -/
  | prop
  /-- a type-level function: a λ with its environment and levels -/
  | clo (ls : Levels) (env : List TV) (lam : Term)
  /-- a value, or a type the producer does not understand -/
  | opaque
  deriving Inhabited

/-- The shape of the members of a type. -/
def TV.shape : TV → Shape
  | .sh s => s
  | _ => .irr

/-- A type-level value flattened, to tell the instances of a data type apart. -/
inductive Atom where
  | sh (s : Shape)
  | prop
  | opaque
  | clo (ls : Levels) (lam : Term) (n : Nat)
  deriving BEq

def TV.atoms : Nat → TV → List Atom
  | 0, _ => [.opaque]
  | _ + 1, .sh s => if s == .irr then [.opaque] else [.sh s]
  | _ + 1, .prop => [.opaque]
  | _ + 1, .opaque => [.opaque]
  | n + 1, .clo ls env t => .clo ls t env.length :: env.flatMap (TV.atoms n)

structure St where
  insts : List (CId × Levels × Shape) := []
  enums : List (CId × List CId) := []
  datas : List DataDecl := []
  /-- the instances of data types met so far, with their table index -/
  keys : List ((CId × Levels × List Atom) × Nat) := []
  /-- instances whose bodies are still to be walked, with the type arguments of the use -/
  todo : List (CId × Levels × Shape × List TV) := []
  /-- type-evaluation steps left: when they run out, every type is unknown -/
  gas : Nat := 400000
  /-- fields whose shape is taken from their uses: entry and field -/
  polys : List (Nat × Nat) := []
  /-- the uses of such a field: entry, field, the shape and the type arguments of the use -/
  uses : List (Nat × Nat × Shape × List TV) := []
  /-- where such a field is built: entry, field, the argument with its levels and environment -/
  sites : List (Nat × Nat × Levels × List TV × Term) := []
  /-- walks still to do: a site's argument at the type arguments of a use -/
  later : List (Levels × List TV × List TV × Term) := []

abbrev M := StateM St

def finalSort : Term → Option Ixon.Univ
  | .pi _ _ t => finalSort t
  | .sort u => some u
  | _ => none

/-- A type of types: a sort, or a function into one. -/
def sortish : Term → Bool
  | .sort _ => true
  | .pi _ _ c => sortish c
  | _ => false

/-- Does the type quantify over types among its leading binders? -/
def polyTy : Term → Bool
  | .pi _ d c => sortish d || polyTy c
  | _ => false

mutual

/-- Evaluate a term as a type. -/
def tyEval (p : Program) : Nat → Levels → List TV → Term → M TV
  | 0, _, _, _ => pure .opaque
  | fuel + 1, ls, env, t => do
    let s ← get
    if s.gas == 0 then return .opaque
    set { s with gas := s.gas - 1 }
    match t with
    | .var i => pure (env.getD i .opaque)
    | .sort _ => pure (.sh .irr)
    | .lam _ _ _ => pure (.clo ls env t)
    | .pi _ d c => do
      let dv ← tyEval p fuel ls env d
      let cv ← tyEval p fuel ls (.opaque :: env) c
      match cv with
      | .prop => pure .prop
      | .sh .irr => pure (.sh .irr)
      | _ => pure (.sh (.fn dv.shape cv.shape))
    | _ => do
      let (h, args) := t.spine
      let argTVs ← args.mapM fun a => tyEval p fuel ls env a.1
      match h with
      | .var i => tyApply p fuel (env.getD i .opaque) argTVs
      | .lam _ _ _ => tyApply p fuel (.clo ls env h) argTVs
      | .const c us => tyConst p fuel (us.map (evalUniv ls)) c argTVs
      | _ => pure .opaque

/-- Apply a type-level value to arguments. -/
def tyApply (p : Program) : Nat → TV → List TV → M TV
  | 0, _, _ => pure .opaque
  | _ + 1, f, [] => pure f
  | fuel + 1, .clo ls env (.lam _ _ body), a :: rest => do
    let r ← tyEval p fuel ls (a :: env) body
    tyApply p fuel r rest
  | _ + 1, _, _ => pure .opaque

/-- A constant as a type: `Nat`, an inductive at its parameters, or a definition
unfolded. -/
def tyConst (p : Program) : Nat → Levels → CId → List TV → M TV
  | 0, _, _, _ => pure .opaque
  | fuel + 1, ls, c, args =>
    if some c == p.known.nat then pure (.sh .nat)
    else
      match p.decl? c with
      | some (.induct _ _ np ni ty ctors) =>
        let isProp := match finalSort ty with
          | some u => evalUniv ls u == 0
          | none => false
        if isProp then pure .prop
        else if np == 0 && ni == 0 && ctors.all (fun k =>
            match p.decl? k with
            | some (.ctor _ _ _ _ _ nf _) => nf == 0
            | _ => false) then do
          modify fun s =>
            if s.enums.any (·.1 == c) then s else { s with enums := s.enums ++ [(c, ctors)] }
          pure (.sh (.enum c))
        else mkData p fuel ls c np ctors (args.take np)
      | some (.defn _ _ _ _ v) => do
        let f ← tyEval p fuel ls [] v
        tyApply p fuel f args
      | _ => pure .opaque

/-- The table entry of an inductive at parameters, created on first use. A structure's
field whose type quantifies over types is entered as `any` and listed in `polys`. -/
def mkData (p : Program) : Nat → Levels → CId → Nat → List CId → List TV → M TV
  | 0, _, _, _, _, _ => pure .opaque
  | fuel + 1, ls, ind, np, ctors, params => do
    let key := (ind, ls, params.flatMap (TV.atoms 4))
    let s ← get
    match s.keys.lookup key with
    | some d => pure (.sh (.data d))
    | none =>
      let d := s.datas.length
      let blank : DataDecl :=
        { ind, params := List.replicate np .irr, ctors := [], struct := false }
      set { s with datas := s.datas ++ [blank], keys := (key, d) :: s.keys }
      let cs ← ctors.mapM fun k => do
        match p.decl? k with
        | some (.ctor _ _ _ _ _ nf ty) =>
          let fl ← fieldShapes p fuel ls [] params nf ty
          pure (k, fl)
        | _ => pure (k, [])
      let single := ctors.length == 1
      let polyFields := if single then
          (cs.flatMap fun e => e.2.zipIdx.filterMap fun (f, j) => if f.2 then some (d, j) else none)
        else []
      let entry : DataDecl :=
        { ind, params := List.replicate np .irr
          ctors := cs.map fun e => (e.1, e.2.map fun f => if f.2 && single then Shape.any else f.1)
          struct := single }
      modify fun s => { s with datas := s.datas.set d entry, polys := s.polys ++ polyFields }
      pure (.sh (.data d))

/-- The field shapes of a constructor: its type's binders after the parameters, each
with whether its type quantifies over types. -/
def fieldShapes (p : Program) :
    Nat → Levels → List TV → List TV → Nat → Term → M (List (Shape × Bool))
  | 0, _, _, _, _, _ => pure []
  | fuel + 1, ls, env, pv :: params, nf, .pi _ _ c =>
    fieldShapes p fuel ls (pv :: env) params nf c
  | fuel + 1, ls, env, [], nf + 1, .pi _ d c => do
    let dv ← tyEval p fuel ls env d
    let rest ← fieldShapes p fuel ls (.opaque :: env) [] nf c
    pure ((dv.shape, polyTy d) :: rest)
  | _ + 1, _, _, _, _, _ => pure []

end

/-- The shape of a use of a constant: its declared type, read with the binder of each
supplied argument bound to the argument's type-level value, an argument's domain `irr`
where the use passes it irrelevantly (`none`: as the binder says). -/
def piShape (p : Program) : Nat → Levels → List TV → List (Option Bool × TV) → Term → M Shape
  | 0, _, _, _, _ => pure .irr
  | fuel + 1, ls, env, args, .pi b d c => do
    let dv ← tyEval p fuel ls env d
    let isPropSort := match d with
      | .sort u => evalUniv ls u == 0
      | _ => false
    let (irrPos, tv, rest) := match args with
      | (i, tv) :: rest => (i.getD (b.rel.irrAt ls), tv, rest)
      | [] => (b.rel.irrAt ls, TV.opaque, [])
    let bound := if isPropSort then TV.prop else tv
    let r ← piShape p fuel ls (bound :: env) rest c
    pure (.fn (if irrPos then .irr else dv.shape) r)
  | fuel + 1, ls, env, _, t => do
    let v ← tyEval p fuel ls env t
    pure v.shape

/-- A constructor's instance takes its field shapes from a table of entries. -/
def refix (p : Program) (datas : List DataDecl) (c : CId) (σ : Shape) : Shape :=
  match p.table.resolveOf c, p.decl? c with
  | none, some (.ctor _ _ _ _ np nf _) =>
    match resAfter (np + nf) σ with
    | .data d =>
      match datas[d]? with
      | some D =>
        match D.ctors.lookup c with
        | some fl => arrows (argsUpTo np σ ++ fl) (.data d)
        | none => σ
      | none => σ
    | _ => σ
  | _, _ => σ

/-- The term SrcEval runs for a constant, if it unfolds one. -/
def bodyOf (p : Program) (c : CId) : Option Term :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => some body
  | some _ => none
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => some v
    | _ => none

def peel : Term → Nat × Term
  | .lam _ _ t =>
    match peel t with
    | (n, b) => (n + 1, b)
  | t => (0, t)

/-- A structure's projection function `fun params self => self.i`: its parameter count
and field. -/
def projFn (p : Program) (c : CId) : Option (Nat × Nat) :=
  match bodyOf p c with
  | some t =>
    match peel t with
    | (n + 1, .proj _ i (.var 0)) => some (n, i)
    | _ => none
  | none => none

/-- Record a use of a constant, and queue its body. A use of the projection function of
a field taken from its uses is one of that field's uses. -/
def addInst (p : Program) (fuel : Nat) (ls : Levels) (c : CId) (infos : List (Option Bool × TV)) :
    M Shape := do
  let σ0 ← match p.decl? c with
    | some d => piShape p fuel ls [] infos d.type
    | none => pure Shape.irr
  let σ := refix p (← get).datas c σ0
  let s ← get
  if !s.insts.contains (c, ls, σ) then
    set { s with insts := s.insts ++ [(c, ls, σ)]
                 todo := s.todo ++ [(c, ls, σ, infos.map Prod.snd)] }
  match projFn p c with
  | some (np, i) =>
    match argAt np σ with
    | .data d =>
      let s ← get
      let F := resAfter (np + 1) σ
      if s.polys.contains (d, i) && !(s.uses.any fun u => u.1 == d && u.2.1 == i && u.2.2.1 == F) then
        let targs := (infos.drop (np + 1)).map Prod.snd
        let new := (s.sites.filter fun x => x.1 == d && x.2.1 == i).map fun x =>
          (x.2.2.1, x.2.2.2.1, targs, x.2.2.2.2)
        set { s with uses := s.uses ++ [(d, i, F, targs)], later := s.later ++ new }
    | _ => pure ()
  | none => pure ()
  pure σ

/-- Record where a field taken from its uses is built, and queue its walks. -/
def addSite (d j : Nat) (ls : Levels) (env : List TV) (t : Term) : M Unit := do
  let s ← get
  if s.sites.any fun x => x.1 == d && x.2.1 == j && x.2.2.1 == ls && x.2.2.2.2 == t then pure ()
  else
    let new := (s.uses.filter fun u => u.1 == d && u.2.1 == j).map fun u => (ls, env, u.2.2.2, t)
    let dflt := if isLam t then [] else [(ls, env, [], t)]
    set { s with sites := s.sites ++ [(d, j, ls, env, t)], later := s.later ++ new ++ dflt }

/-- The arguments of a constructor application that build fields taken from uses:
recorded as sites, and returned so that they are not walked in place. -/
def ctorSites (p : Program) (ls : Levels) (env : List TV) (c : CId) (σ : Shape)
    (args : List Term.Arg) : M (List Nat) := do
  match p.table.resolveOf c, p.decl? c with
  | none, some (.ctor _ _ _ _ np nf _) =>
    match resAfter (np + nf) σ with
    | .data d =>
      let s ← get
      let js := (List.range nf).filter fun j => s.polys.contains (d, j) && (args[np + j]?).isSome
      js.forM fun j =>
        match args[np + j]? with
        | some a => addSite d j ls env a.1
        | none => pure ()
      pure (js.map fun j => np + j)
    | _ => pure []
  | _, _ => pure []

/-- Walk a term SrcEval runs at levels `ls`, recording the constants it uses. `pend`
are the type-level values of the leading λs' binders, or of the arguments a constant
at the head is still to receive. -/
def walk (p : Program) : Nat → Levels → List TV → List TV → Term → M Unit
  | 0, _, _, _, _ => pure ()
  | fuel + 1, ls, env, pend, t =>
    match t with
    | .lam _ _ body =>
      match pend with
      | tv :: pend' => walk p fuel ls (tv :: env) pend' body
      | [] => walk p fuel ls (.opaque :: env) [] body
    | .letE _ _ r ty v body => do
      if !r.irrAt ls then walk p fuel ls env [] v
      let tv ← match ty with
        | .sort _ => tyEval p fuel ls env v
        | _ => pure TV.opaque
      walk p fuel ls (tv :: env) [] body
    | .proj _ _ e => walk p fuel ls env [] e
    | .var _ | .sort _ | .pi _ _ _ | .natLit _ | .strLit _ => pure ()
    | _ => do
      let (h, args) := t.spine
      let infos ← args.mapM fun a => do
        let tv ← if a.2.2 == Rel.type then tyEval p fuel ls env a.1 else pure TV.opaque
        pure (some (a.2.2.irrAt ls), tv)
      let skip ← match h with
        | .const c us => do
          let σ ← addInst p fuel (us.map (evalUniv ls)) c
            (infos ++ pend.map fun tv => (none, tv))
          ctorSites p ls env c σ args
        | _ => do
          walk p fuel ls env [] h
          pure []
      args.zipIdx.forM fun a => do
        if !a.1.2.2.irrAt ls && !skip.contains a.2 then walk p fuel ls env [] a.1.1

/-- Walk the next queued site, or the body of the next queued instance. -/
def step (p : Program) (fuel : Nat) : M Bool := do
  let s ← get
  match s.later with
  | (ls, env, pend, t) :: rest =>
    set { s with later := rest }
    walk p fuel ls env pend t
    pure true
  | [] =>
    match s.todo with
    | [] => pure false
    | (c, ls, σ, targs) :: rest =>
      set { s with todo := rest }
      match p.table.resolveOf c with
      | some (.eqn _ body) => walk p fuel ls [] targs body
      | some (.csimp g us _) =>
        modify fun s =>
          let e := (g, us.map (evalUniv ls), σ)
          if s.insts.contains e then s
          else { s with insts := s.insts ++ [e]
                        todo := s.todo ++ [(g, us.map (evalUniv ls), σ, targs)] }
      | some _ => pure ()
      | none =>
        match p.decl? c with
        | some (.defn .defn .safe _ _ v) => walk p fuel ls [] targs v
        | _ => pure ()
      pure true

def loop (p : Program) (fuel : Nat) : Nat → M Unit
  | 0 => pure ()
  | n + 1 => do
    if (← step p fuel) then loop p fuel n

/-- The intersection of the shapes a field is used at; `any` if it is not used. -/
def interOf : List Shape → Shape
  | [] => .any
  | [σ] => σ
  | σ :: rest => .inter σ (interOf rest)

/-- **The proposed certificate** for root constant `root` of `p`, and, for each field
taken from its uses, its entry, its index and the number of shapes it is used at. -/
def produceWith (p : Program) (root : CId) (fuel : Nat := 400) (steps : Nat := 20000) :
    Cert × List (Nat × Nat × Nat) :=
  let m : M Unit := do
    let _ ← addInst p fuel [] root []
    loop p fuel steps
  let s := (m.run {}).2
  let usesOf := fun (d j : Nat) => (s.uses.filter fun u => u.1 == d && u.2.1 == j).map fun u => u.2.2.1
  let datas := s.datas.zipIdx.map fun e =>
    { e.1 with ctors := e.1.ctors.map fun k =>
        (k.1, k.2.zipIdx.map fun f =>
          if s.polys.contains (e.2, f.2) then interOf (usesOf e.2 f.2) else f.1) }
  let insts := (s.insts.map fun e => (e.1, e.2.1, refix p datas e.1 e.2.2)).eraseDups
  ({ insts, enums := s.enums, datas }, s.polys.map fun x => (x.1, x.2, (usesOf x.1 x.2).length))

/-- **The proposed certificate** for root constant `root` of `p`. -/
def produce (p : Program) (root : CId) (fuel : Nat := 400) (steps : Nat := 20000) : Cert :=
  (produceWith p root fuel steps).1

end IxCC.Correct.Shape2.Produce
