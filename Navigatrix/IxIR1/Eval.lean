import Navigatrix.IxIR1.Basic

/-!
# The IxIR₁ store semantics

Fueled big-step interpreter in the house style, now state-passing: a
`Store` of nodes threads through everything. Two jobs at once:

1. **Semantic anchor**: the specification `reuse_sound` and both
   IxIR₀ → IxIR₁ lowerings (no-RC and RC-fallback) are proved
   against. Fuel is the usual totality device.
2. **Dynamic discipline checker**: the mode rules are enforced at
   runtime — `dup`/`drop` demand a live *shared* node, `reuse`/`free`
   a live *unique* one, every access demands liveness — with
   violations reported as `Err.mem`, distinct from ordinary
   stuckness. Well-moded lowered code never trips them; that
   unstuckness claim is the future static well-formedness theorem.

The store also counts: allocations, in-place reuses, frees (explicit
and refcount-zero), and RC operations. Cost attaches to IxIR₁
instructions (gate A), and the counters make memory-behavior claims
checkable — see `Examples.lean` for "reversing a unique list
allocates nothing" as a `#guard`.

Conventions: `pap` nodes are allocated shared (function values are
freely copyable; `dup`/`drop` manage them, `reuse`/`free` reject
them). Deep drop expects shared children under shared nodes
(whole-value modes — gate B); a unique child under a shared node is a
memory error. Scalars (`lit`, `◻`) are inert everywhere.
-/

namespace Navigatrix.IxIR1

open Navigatrix.Ixon (Address Owned)
open Navigatrix.IxIR0 (Literal)

/-- Runtime values: scalars or locations. -/
inductive RVal where
  | loc (l : Nat)
  | lit (l : Literal)
  | erased
  deriving BEq, Repr, Inhabited

inductive Node where
  | ctorN (cid : CtorId) (fields : Array RVal)
  | papN (f : Address) (arity : Nat) (args : Array RVal)
  deriving BEq, Repr, Inhabited

structure NodeBox where
  world : Owned
  rc : Nat
  node : Node
  deriving Repr

structure Store where
  nodes : Array (Option NodeBox) := #[]
  allocs : Nat := 0
  reuses : Nat := 0
  frees : Nat := 0
  rcops : Nat := 0
  deriving Repr

def Store.allocNode (s : Store) (world : Owned) (n : Node) : Store × Nat :=
  ({ s with nodes := s.nodes.push (some ⟨world, 1, n⟩)
            allocs := s.allocs + 1 },
   s.nodes.size)

def Store.get? (s : Store) (l : Nat) : Option NodeBox :=
  (s.nodes[l]?).bind id

def Store.setBox (s : Store) (l : Nat) (b : NodeBox) : Store :=
  { s with nodes := s.nodes.set! l (some b) }

def Store.kill (s : Store) (l : Nat) : Store :=
  { s with nodes := s.nodes.set! l none, frees := s.frees + 1 }

def Store.rcTick (s : Store) : Store := { s with rcops := s.rcops + 1 }

/-- Number of live nodes — `0` at the end of a run is leak-freedom. -/
def Store.live (s : Store) : Nat :=
  s.nodes.foldl (fun n b => if b.isSome then n + 1 else n) 0

inductive Err where
  | fuel
  | stuck (msg : String)
  /-- A memory-discipline violation: the dynamic mode checker fired. -/
  | mem (msg : String)
  | unknownRef (adr : Address)
  deriving BEq, Repr

structure Ctx where
  decls : Env
  oracle : Address → List RVal → Option RVal := fun _ _ => none

def resolveAtom (env : List RVal) : Atom → Except Err RVal
  | .var i =>
    match env[i]? with
    | some v => .ok v
    | none => .error (.stuck s!"unbound variable {i}")
  | .lit l => .ok (.lit l)
  | .erased => .ok .erased

def resolveAtoms (env : List RVal) (as' : Array Atom) :
    Except Err (List RVal) :=
  as'.foldlM (fun acc a => do pure (acc ++ [← resolveAtom env a])) []

def Alt.cidx : Alt → Nat
  | .mk c _ _ => c

def declArity : Decl → Nat
  | .fn d => d.arity
  | .extern ar => ar

mutual

def runCode (ctx : Ctx) (fuel : Nat) (cur : FnDef) (store : Store)
    (env : List RVal) (c : Code) : Except Err (Store × RVal) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match c with
    | .ret a => do
      let v ← resolveAtom env a
      .ok (store, v)
    | .letOp op rest => do
      let (store', v) ← runOp ctx fuel cur store env op
      runCode ctx fuel cur store' (v :: env) rest
    | .case scrut peelNat alts => do
      match ← resolveAtom env scrut with
      | .loc l =>
        match store.get? l with
        | none => .error (.mem s!"case on a dead location {l}")
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            match alts.find? (fun alt => alt.cidx == cid.cidx) with
            | none => .error (.stuck s!"no case alternative for tag {cid.cidx}")
            | some (.mk _ nf body) =>
              if fields.size != nf then
                .error (.stuck "case field-count mismatch")
              else
                runCode ctx fuel cur store
                  (fields.foldl (fun e f => f :: e) env) body
          | .papN .. => .error (.stuck "case on a pap node")
      | .lit (.nat n) =>
        if peelNat then
          match n with
          | 0 =>
            match alts.find? (fun alt => alt.cidx == 0) with
            | some (.mk _ 0 body) => runCode ctx fuel cur store env body
            | _ => .error (.stuck "nat-peel: missing nullary 0-alternative")
          | n + 1 =>
            match alts.find? (fun alt => alt.cidx == 1) with
            | some (.mk _ 1 body) =>
              runCode ctx fuel cur store (.lit (.nat n) :: env) body
            | _ => .error (.stuck "nat-peel: missing unary 1-alternative")
        else .error (.stuck "case on a literal (peelNat disabled)")
      | _ => .error (.stuck "case on a non-node value")
  termination_by fuel

def runOp (ctx : Ctx) (fuel : Nat) (cur : FnDef) (store : Store)
    (env : List RVal) (op : Op) : Except Err (Store × RVal) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match op with
    | .pure a => do
      let v ← resolveAtom env a
      .ok (store, v)
    | .alloc world cid args => do
      let vs ← resolveAtoms env args
      let (store', l) := store.allocNode world (.ctorN cid vs.toArray)
      .ok (store', .loc l)
    | .reuse target cid args => do
      let vs ← resolveAtoms env args
      match ← resolveAtom env target with
      | .loc l =>
        match store.get? l with
        | none => .error (.mem s!"reuse of a dead location {l}")
        | some box =>
          match box.world with
          | .shared => .error (.mem "reuse of a shared node")
          | .unique =>
            let store' := store.setBox l ⟨.unique, 1, .ctorN cid vs.toArray⟩
            .ok ({ store' with reuses := store'.reuses + 1 }, .loc l)
      | _ => .error (.mem "reuse of a non-location")
    | .free target => do
      match ← resolveAtom env target with
      | .loc l =>
        match store.get? l with
        | none => .error (.mem s!"free of a dead location {l}")
        | some box =>
          match box.world with
          | .shared => .error (.mem "free of a shared node")
          | .unique => .ok (store.kill l, .erased)
      | _ => .error (.mem "free of a non-location")
    | .dup target => do
      match ← resolveAtom env target with
      | .loc l =>
        match store.get? l with
        | none => .error (.mem s!"dup of a dead location {l}")
        | some box =>
          match box.world with
          | .unique => .error (.mem "dup of a unique node")
          | .shared =>
            .ok ((store.setBox l { box with rc := box.rc + 1 }).rcTick,
              .loc l)
      | v => .ok (store, v)
    | .drop target => do
      match ← resolveAtom env target with
      | v@(.loc _) => do
        let store' ← dropVal ctx fuel store v
        .ok (store', .erased)
      | _ => .ok (store, .erased)
    | .fetch target i => do
      match ← resolveAtom env target with
      | .loc l =>
        match store.get? l with
        | none => .error (.mem s!"fetch from a dead location {l}")
        | some box =>
          match box.node with
          | .ctorN _ fields =>
            match fields[i]? with
            | some v => .ok (store, v)
            | none => .error (.stuck s!"fetch field {i} out of range")
          | .papN .. => .error (.stuck "fetch from a pap node")
      | _ => .error (.stuck "fetch from a non-location")
    | .call f args => do
      let vs ← resolveAtoms env args
      invoke ctx fuel f vs store
    | .callSelf args => do
      let vs ← resolveAtoms env args
      if vs.length != cur.arity then
        .error (.stuck "callSelf arity mismatch")
      else
        runCode ctx fuel cur store vs.reverse cur.body
    | .papp f args => do
      let vs ← resolveAtoms env args
      match ctx.decls f with
      | none => .error (.unknownRef f)
      | some d =>
        if vs.length < declArity d then
          let (store', l) :=
            store.allocNode .shared (.papN f (declArity d) vs.toArray)
          .ok (store', .loc l)
        else .error (.stuck "papp with saturating arguments (use call)")
    | .apply f args => do
      let fv ← resolveAtom env f
      let vs ← resolveAtoms env args
      applyGo ctx fuel store fv vs
    | .extern f args => do
      let vs ← resolveAtoms env args
      match ctx.oracle f vs with
      | some v => .ok (store, v)
      | none => .error (.unknownRef f)
  termination_by fuel

/-- Enter a known declaration with saturated arguments. -/
def invoke (ctx : Ctx) (fuel : Nat) (f : Address) (args : List RVal)
    (store : Store) : Except Err (Store × RVal) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match ctx.decls f with
    | none => .error (.unknownRef f)
    | some (.fn d) =>
      if args.length != d.arity then
        .error (.stuck "call arity mismatch")
      else runCode ctx fuel d store args.reverse d.body
    | some (.extern ar) =>
      if args.length != ar then
        .error (.stuck "extern arity mismatch")
      else
        match ctx.oracle f args with
        | some v => .ok (store, v)
        | none => .error (.unknownRef f)
  termination_by fuel

/-- The apply chain: under-fill builds a new pap, saturation calls,
over-fill calls then applies the rest to the result. -/
def applyGo (ctx : Ctx) (fuel : Nat) (store : Store) (fv : RVal)
    (args : List RVal) : Except Err (Store × RVal) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match fv with
    | .loc l =>
      match store.get? l with
      | none => .error (.mem s!"apply of a dead location {l}")
      | some box =>
        match box.node with
        | .papN f ar got =>
          let total := got.toList ++ args
          if total.length < ar then
            let (store', l') :=
              store.allocNode .shared (.papN f ar total.toArray)
            .ok (store', .loc l')
          else if total.length == ar then
            invoke ctx fuel f total store
          else do
            let (store', r) ← invoke ctx fuel f (total.take ar) store
            applyGo ctx fuel store' r (total.drop ar)
        | .ctorN .. => .error (.stuck "apply of a constructor node")
    | _ => .error (.stuck "apply of a non-node value")
  termination_by fuel

/-- Perceus-style deep drop of a shared value: decrement, and at zero
free the node and drop its children. -/
def dropVal (ctx : Ctx) (fuel : Nat) (store : Store) (v : RVal) :
    Except Err Store :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match v with
    | .lit _ => .ok store
    | .erased => .ok store
    | .loc l =>
      match store.get? l with
      | none => .error (.mem s!"drop of a dead location {l}")
      | some box =>
        match box.world with
        | .unique => .error (.mem "drop of a unique node")
        | .shared =>
          let store := store.rcTick
          if box.rc == 1 then
            let store := store.kill l
            match box.node with
            | .ctorN _ fields => dropMany ctx fuel store fields.toList
            | .papN _ _ args => dropMany ctx fuel store args.toList
          else
            .ok (store.setBox l { box with rc := box.rc - 1 })
  termination_by fuel

def dropMany (ctx : Ctx) (fuel : Nat) (store : Store) (vs : List RVal) :
    Except Err Store :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match vs with
    | [] => .ok store
    | v :: rest => do
      let store' ← dropVal ctx fuel store v
      dropMany ctx fuel store' rest
  termination_by fuel

end

/-- Run a top-level code sequence in a fresh store (the `cur` frame is
the code itself, so `callSelf` at top level re-enters it). -/
def runMain (ctx : Ctx) (c : Code) (fuel : Nat := 100000) :
    Except Err (Store × RVal) :=
  runCode ctx fuel ⟨0, c⟩ {} [] c

end Navigatrix.IxIR1
