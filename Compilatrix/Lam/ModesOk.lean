import Compilatrix.Lam.Syntax

/-! # Static by-name positions

`Lam.ModesOk P` (design note 02 §4.3), ANF's precondition: a `name` λ binder
only ever receives `name` slots and a `strict` binder only `val` slots, so
ANF conversion knows statically which variables hold thunks. It is decided
by `modesOk`, a syntactic check:

* A `name` binder has a **dispatch signature**: the argument modes of the
  spines it heads (all of them must agree; none means `[]`). A binder whose
  signature has a `name` is a *minor* binder of an erased recursor.
* `name` λs appear only in the leading telescope of a `byName` or `recStar`
  global, or as a `name` argument at a glob-headed spine position whose
  binder's signature has a `name` (a recursor minor); such a λ's leading
  modes are exactly that signature followed by strict binders, and its own
  `name` binders (IH binders) have signatures without `name`.
* A glob-headed spine passes each argument with its binder's mode, and
  covers every `name` binder of the global's telescope; a spine headed by a
  `name` variable passes the variable's signature, likewise covered. A
  `name` argument whose binder's signature has a `name` is such a λ or a
  forwarded variable with the same signature.
* Every other application is strict; a global with `name` binders is used
  only as a spine head, and a variable whose signature has a `name` only as
  a spine head or a forwarded argument.

The checks recurse on an explicit fuel (spines are lists). -/

namespace Compilatrix.Lam

/-- What a variable holds: a value, or a thunk with its dispatch signature. -/
inductive Kind where
  | strict
  | name (sig : List Mode)
  deriving DecidableEq, Repr, Inhabited

namespace Term

/-- Head and arguments (with modes) of an application spine. -/
def spine (t : Term) : Term × List (Term × Mode) :=
  go t []
where
  go : Term → List (Term × Mode) → Term × List (Term × Mode)
    | .app f a m, acc => go f ((a, m) :: acc)
    | t, acc => (t, acc)

/-- Leading λs: their modes and the body. -/
def telescope : Term → List Mode × Term
  | .lam m _ b => let (ms, body) := telescope b; (m :: ms, body)
  | t => ([], t)

mutual

/-- The argument modes of every spine headed by the variable at level `lvl`,
for a term under `d` binders. `inSpine` marks the function position of an
application, which belongs to an enclosing spine. -/
def dispatches (lvl d : Nat) (inSpine : Bool) : Term → List (List Mode)
  | .app f a m =>
    let here := if inSpine then [] else
      match spine (.app f a m) with
      | (.var i, args) => if i < d && d - 1 - i == lvl then [args.map (·.2)] else []
      | _ => []
    here ++ dispatches lvl d true f ++ dispatches lvl d false a
  | .lam _ _ b => dispatches lvl (d + 1) false b
  | .letE _ v b => dispatches lvl d false v ++ dispatches lvl (d + 1) false b
  | .con _ fs | .prim _ fs => dispatchesList lvl d fs
  | .case s alts dflt =>
    dispatches lvl d false s ++ dispatchesAlts lvl d alts ++ dispatchesOpt lvl d dflt
  | .proj _ _ s | .tick s => dispatches lvl d false s
  | .var _ | .glob _ | .lit _ | .box | .trap => []

def dispatchesList (lvl d : Nat) : List Term → List (List Mode)
  | [] => []
  | t :: ts => dispatches lvl d false t ++ dispatchesList lvl d ts

def dispatchesAlts (lvl d : Nat) : List Alt → List (List Mode)
  | [] => []
  | .mk _ n b :: as => dispatches lvl (d + n) false b ++ dispatchesAlts lvl d as

def dispatchesOpt (lvl d : Nat) : Option Term → List (List Mode)
  | none => []
  | some t => dispatches lvl d false t

end

end Term

namespace ModesOk

/-- A global's leading telescope: binder modes and dispatch signatures. -/
structure GInfo where
  tele : List Mode := []
  sigs : List (List Mode) := []
  deriving Inhabited

def hasName (ms : List Mode) : Bool := ms.any (· == .name)

/-- The dispatch signature of the binder at level `lvl` of a body under `d`
binders. -/
def sigOf (lvl d : Nat) (body : Term) : Except String (List Mode) :=
  match body.dispatches lvl d false with
  | [] => .ok []
  | s :: rest =>
    if rest.all (· == s) then .ok s
    else .error s!"binder at level {lvl} is dispatched with different modes"

/-- Kinds of a telescope's binders (outermost first) over depth `d`. -/
def teleKinds (ms : List Mode) (d : Nat) (body : Term) : Except String (List Kind) :=
  let n := ms.length
  (ms.zipIdx).mapM fun (m, i) =>
    match m with
    | .strict => pure .strict
    | .name => return .name (← sigOf (d + i) (d + n) body)

def info (t : Term) : Except String (GInfo × List Kind) := do
  let (ms, body) := t.telescope
  let kinds ← teleKinds ms 0 body
  return ({ tele := ms, sigs := kinds.map fun | .strict => [] | .name s => s }, kinds)

/-- The mode and signature expected at argument position `i`. -/
def expected (tele : List Mode) (sigs : List (List Mode)) (i : Nat) : Mode × List Mode :=
  (tele.getD i .strict, sigs.getD i [])

/-- Every `name` position of `ms` is covered by `n` arguments. -/
def covered (ms : List Mode) (n : Nat) : Bool :=
  (ms.zipIdx).all fun (m, i) => m == .strict || i < n

mutual

/-- Check a term in a plain position, under variable kinds `env` (innermost
first). -/
def check (G : Src.NatMap GInfo) : Nat → List Kind → Term → Except String Unit
  | 0, _, _ => .error "fuel"
  | fuel + 1, env, t =>
    match t with
    | .var i =>
      match env[i]? with
      | some (.name sig) =>
        if hasName sig then .error s!"minor variable #{i} used as a value" else .ok ()
      | some .strict => .ok ()
      | none => .error s!"variable #{i} out of scope"
    | .glob g =>
      if hasName ((G.get? g).map (·.tele) |>.getD []) then .error s!"by-name global {g} escapes"
      else .ok ()
    | .lam m _ b =>
      if m == .name then .error "a by-name λ in a plain position"
      else check G fuel (.strict :: env) b
    | .app .. =>
      let (h, args) := t.spine
      match h with
      | .glob g =>
        let gi := (G.get? g).getD {}
        if !covered gi.tele args.length then .error s!"partial application of by-name global {g}"
        else checkArgs G fuel env gi.tele gi.sigs 0 args
      | .var i =>
        match env[i]? with
        | some (.name sig) =>
          if !covered sig args.length then .error s!"partial dispatch of minor variable #{i}"
          else checkArgs G fuel env sig [] 0 args
        | some .strict => checkArgs G fuel env [] [] 0 args
        | none => .error s!"variable #{i} out of scope"
      | h => do
        check G fuel env h
        checkArgs G fuel env [] [] 0 args
    | .letE _ v b => do
      check G fuel env v
      check G fuel (.strict :: env) b
    | .con _ fs | .prim _ fs => checkList G fuel env fs
    | .case s alts dflt => do
      check G fuel env s
      checkAlts G fuel env alts
      match dflt with
      | some d => check G fuel env d
      | none => pure ()
    | .proj _ _ s | .tick s => check G fuel env s
    | .lit _ | .box | .trap => .ok ()

def checkList (G : Src.NatMap GInfo) : Nat → List Kind → List Term → Except String Unit
  | 0, _, _ => .error "fuel"
  | _, _, [] => .ok ()
  | fuel + 1, env, t :: ts => do
    check G fuel env t
    checkList G fuel env ts

def checkAlts (G : Src.NatMap GInfo) : Nat → List Kind → List Alt → Except String Unit
  | 0, _, _ => .error "fuel"
  | _, _, [] => .ok ()
  | fuel + 1, env, .mk _ n b :: as => do
    check G fuel (List.replicate n .strict ++ env) b
    checkAlts G fuel env as

/-- Arguments of a spine whose head's binders have modes `tele` and
signatures `sigs`. -/
def checkArgs (G : Src.NatMap GInfo) : Nat → List Kind → List Mode → List (List Mode) → Nat →
    List (Term × Mode) → Except String Unit
  | 0, _, _, _, _, _ => .error "fuel"
  | _, _, _, _, _, [] => .ok ()
  | fuel + 1, env, tele, sigs, i, (a, m) :: rest => do
    let (want, sig) := expected tele sigs i
    if m != want then throw s!"argument {i} passed {repr m}, binder is {repr want}"
    if m == .name then checkNameArg G fuel env sig a else check G fuel env a
    checkArgs G fuel env tele sigs (i + 1) rest

/-- A `name` argument for a binder with dispatch signature `sig`. -/
def checkNameArg (G : Src.NatMap GInfo) : Nat → List Kind → List Mode → Term → Except String Unit
  | 0, _, _, _ => .error "fuel"
  | fuel + 1, env, sig, a =>
    if !hasName sig then check G fuel env a else
    match a with
    | .var i =>
      match env[i]? with
      | some (.name sig') =>
        if sig' == sig then .ok () else .error s!"forwarded minor #{i} has another signature"
      | _ => .error s!"a by-name minor #{i} that is not a minor binder"
    | .lam .. =>
      let (ms, body) := a.telescope
      if ms.take sig.length != sig || (ms.drop sig.length).any (· == .name) then
        .error "a minor λ whose leading modes differ from its dispatch"
      else
        match teleKinds ms env.length body with
        | .error e => .error e
        | .ok kinds =>
          if kinds.any (fun | .name s => hasName s | .strict => false) then
            .error "a minor's by-name binder is itself dispatched by name"
          else check G fuel (kinds.reverse ++ env) body
    | _ => .error "a by-name minor that is not a λ-telescope or a forwarded minor"

end

def fuel : Nat := 1 <<< 20

/-- Check a program: each global's leading telescope, then its body. Keys
other than `byName` and `recStar` have strict telescopes. -/
def run (P : Program) : Except String Unit := do
  let gs := P.globalList
  let infos ← gs.mapM fun (g, gl) => do
    let (gi, _) ← (info gl.body).mapError (s!"global {g} ({gl.key.render}): " ++ ·)
    return (g, gi)
  let G : Src.NatMap GInfo := Src.NatMap.ofList infos
  for (g, gl) in gs do
    let (gi, kinds) ← (info gl.body).mapError (s!"global {g}: " ++ ·)
    match gl.key with
    | .byName .. | .recStar .. => pure ()
    | _ => if hasName gi.tele then throw s!"global {g} ({gl.key.render}) has by-name binders"
    let (_, body) := gl.body.telescope
    (check G fuel kinds.reverse body).mapError (s!"global {g} ({gl.key.render}): " ++ ·)

end ModesOk

/-- ANF's precondition, decided by its checker. -/
def modesOk (P : Program) : Bool := (ModesOk.run P).isOk

def ModesOk (P : Program) : Prop := modesOk P = true

instance (P : Program) : Decidable (ModesOk P) := inferInstanceAs (Decidable (_ = true))

end Compilatrix.Lam
