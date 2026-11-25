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

Known limits (each a refusal by the checker, never an unsound acceptance): a
type-level function as a parameter of a data type (the entry's key forgets it), a
`let`-bound λ, type arguments the instance of a polymorphic constant does not carry
to an inner λ, recursors' rule bodies (not walked).
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

structure St where
  insts : List (CId × Levels × Shape) := []
  enums : List (CId × List CId) := []
  datas : List DataDecl := []
  /-- the instances of data types met so far, with their table index -/
  keys : List ((CId × Levels × List Shape) × Nat) := []
  /-- instances whose bodies are still to be walked, with the type arguments of the use -/
  todo : List (CId × Levels × Shape × List TV) := []

abbrev M := StateM St

def finalSort : Term → Option Ixon.Univ
  | .pi _ _ t => finalSort t
  | .sort u => some u
  | _ => none

mutual

/-- Evaluate a term as a type. -/
def tyEval (p : Program) : Nat → Levels → List TV → Term → M TV
  | 0, _, _, _ => pure .opaque
  | fuel + 1, ls, env, t =>
    match t with
    | .var i => pure (env.getD i .opaque)
    | .sort _ => pure (.sh .irr)
    | .lam _ _ _ => pure (.clo ls env t)
    | .pi _ d c => do
      let dv ← tyEval p fuel ls env d
      let cv ← tyEval p fuel ls (.opaque :: env) c
      match cv with
      | .prop => pure .prop
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

/-- The table entry of an inductive at parameters, created on first use. -/
def mkData (p : Program) : Nat → Levels → CId → Nat → List CId → List TV → M TV
  | 0, _, _, _, _, _ => pure .opaque
  | fuel + 1, ls, ind, np, ctors, params => do
    let key := (ind, ls, params.map TV.shape)
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
      let entry : DataDecl :=
        { ind, params := List.replicate np .irr, ctors := cs, struct := ctors.length == 1 }
      modify fun s => { s with datas := s.datas.set d entry }
      pure (.sh (.data d))

/-- The field shapes of a constructor: its type's binders after the parameters. -/
def fieldShapes (p : Program) : Nat → Levels → List TV → List TV → Nat → Term → M (List Shape)
  | 0, _, _, _, _, _ => pure []
  | fuel + 1, ls, env, pv :: params, nf, .pi _ _ c =>
    fieldShapes p fuel ls (pv :: env) params nf c
  | fuel + 1, ls, env, [], nf + 1, .pi _ d c => do
    let dv ← tyEval p fuel ls env d
    let rest ← fieldShapes p fuel ls (.opaque :: env) [] nf c
    pure (dv.shape :: rest)
  | _ + 1, _, _, _, _, _ => pure []

end

/-- The shape of a use of a constant: its declared type, read with the binder of each
supplied argument bound to the argument's type-level value, an argument's domain `irr`
where the use passes it irrelevantly. -/
def piShape (p : Program) : Nat → Levels → List TV → List (Bool × TV) → Term → M Shape
  | 0, _, _, _, _ => pure .irr
  | fuel + 1, ls, env, args, .pi b d c => do
    let dv ← tyEval p fuel ls env d
    let isPropSort := match d with
      | .sort u => evalUniv ls u == 0
      | _ => false
    let (irrPos, tv, rest) := match args with
      | (i, tv) :: rest => (i, tv, rest)
      | [] => (b.rel.irrAt ls, TV.opaque, [])
    let bound := if isPropSort then TV.prop else tv
    let r ← piShape p fuel ls (bound :: env) rest c
    pure (.fn (if irrPos then .irr else dv.shape) r)
  | fuel + 1, ls, env, _, t => do
    let v ← tyEval p fuel ls env t
    pure v.shape

/-- A constructor's instance takes its field shapes from the table entry of its
result. -/
def fixCtor (p : Program) (c : CId) (σ : Shape) : M Shape := do
  match p.table.resolveOf c, p.decl? c with
  | none, some (.ctor _ _ _ _ np nf _) =>
    match resAfter (np + nf) σ with
    | .data d =>
      let s ← get
      match s.datas[d]? with
      | some D =>
        match D.ctors.lookup c with
        | some fl => pure (arrows (argsUpTo np σ ++ fl) (.data d))
        | none => pure σ
      | none => pure σ
    | _ => pure σ
  | _, _ => pure σ

/-- Record a use of a constant, and queue its body. -/
def addInst (p : Program) (fuel : Nat) (ls : Levels) (c : CId) (infos : List (Bool × TV)) :
    M Unit := do
  let σ0 ← match p.decl? c with
    | some d => piShape p fuel ls [] infos d.type
    | none => pure Shape.irr
  let σ ← fixCtor p c σ0
  let s ← get
  if s.insts.contains (c, ls, σ) then pure ()
  else set { s with insts := s.insts ++ [(c, ls, σ)]
                    todo := s.todo ++ [(c, ls, σ, infos.map Prod.snd)] }

/-- Walk a term SrcEval runs at levels `ls`, recording the constants it uses. `pend`
are the type-level values of the leading λs' binders. -/
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
        pure (a.2.2.irrAt ls, tv)
      match h with
      | .const c us => addInst p fuel (us.map (evalUniv ls)) c infos
      | _ => walk p fuel ls env [] h
      args.forM fun a => do
        if !a.2.2.irrAt ls then walk p fuel ls env [] a.1

/-- Walk the body of the next queued instance. -/
def step (p : Program) (fuel : Nat) : M Bool := do
  let s ← get
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

/-- **The proposed certificate** for root constant `root` of `p`. -/
def produce (p : Program) (root : CId) (fuel : Nat := 400) (steps : Nat := 20000) : Cert :=
  let m : M Unit := do
    addInst p fuel [] root []
    loop p fuel steps
  let s := (m.run {}).2
  { insts := s.insts, enums := s.enums, datas := s.datas }

end IxCC.Correct.Shape2.Produce
