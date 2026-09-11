import Ix.Compiler.IxIR1.Basic

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

Ownership calling convention (what the lowering's RC insertion is
built against): every heap-bearing argument position **consumes** one
ownership of its value — `alloc`/`reuse` fields, `call`/`callSelf`/
`papp` arguments, `ret`, and `pure` all take their operands' references
with them. The v1 `extern` ABI is scalar-only in both directions, so no
heap ownership crosses it; locations are rejected before or after the
oracle call. `apply` consumes its function value *and* its
arguments: `applyGo` first dups the pap's stored arguments (they gain
a new owner — the successor pap or the callee) and then drops the
applied pap itself, so under/over-fill chains reclaim intermediate
paps without caller-side bookkeeping. The borrowing exceptions are
`fetch` (project without consuming — dup the field to own it) and
`case` scrutiny; `dup`/`drop` are the explicit ownership adjustments
in the shared world, `free` (shallow) and `dropU` (deep, the affine
death compilation) the reclamations in the unique one.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR0 (Literal)

/-- Runtime values: scalars or locations. -/
inductive RVal where
  | loc (l : Nat)
  | lit (l : Literal)
  | erased
  deriving BEq, Repr, Inhabited

/-- The v1 extern ABI admits no heap ownership: literals and `◻` cross
the boundary, locations do not. -/
def RVal.isScalar : RVal → Bool
  | .loc _ => false
  | .lit _ | .erased => true

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

/-- Invoke the v1 scalar-only oracle. Rejecting locations on both sides makes
the ownership convention explicit: no heap root is silently consumed or
created by an extern call. -/
def callScalarOracle (ctx : Ctx) (f : Address) (args : List RVal) :
    Except Err RVal :=
  if !args.all RVal.isScalar then
    .error (.mem "extern heap arguments require an ownership policy")
  else
    match ctx.oracle f args with
    | none => .error (.unknownRef f)
    | some v =>
      if v.isScalar then .ok v
      else .error (.mem "extern heap results require an ownership policy")

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

private theorem List.resolveAtomsFrom_length (environment : List RVal) :
    ∀ (atoms : List Atom) (accumulator output : List RVal),
      atoms.foldlM
        (fun values atom => do
          pure (values ++ [← resolveAtom environment atom]))
        accumulator = .ok output →
      output.length = accumulator.length + atoms.length := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output run
      simp only [List.foldlM_nil] at run
      cases run
      simp
  | cons atom atoms ih =>
      intro accumulator output run
      simp only [List.foldlM_cons] at run
      cases resolved : resolveAtom environment atom with
      | error error =>
          rw [resolved] at run
          simp only [bind, Except.bind] at run
          contradiction
      | ok value =>
          rw [resolved] at run
          simp only [bind, Except.bind] at run
          have tail := ih (accumulator ++ [value]) output run
          simp only [List.length_append, List.length_singleton] at tail
          simp only [List.length_cons]
          omega

/-- Successful simultaneous operand resolution preserves vector length. -/
theorem resolveAtoms_length {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (run : resolveAtoms environment atoms = .ok values) :
    values.length = atoms.size := by
  unfold resolveAtoms at run
  rw [← Array.foldlM_toList] at run
  have length :=
    List.resolveAtomsFrom_length environment atoms.toList [] values run
  simpa using length

def Alt.cidx : Alt → Nat
  | .mk c _ _ => c

/-- Add one owner to each value: the internal half of `applyGo`'s
convention (the pap's stored arguments gain the successor pap or the
callee as a new owner). Mirrors `Op.dup`: shared and live demanded,
scalars inert. -/
def dupVals (store : Store) (vs : List RVal) : Except Err Store :=
  vs.foldlM (init := store) fun store v =>
    match v with
    | .loc l =>
      match store.get? l with
      | none => .error (.mem s!"dup of a dead location {l}")
      | some box =>
        match box.world with
        | .unique => .error (.mem "dup of a unique node")
        | .shared =>
          .ok ((store.setBox l { box with rc := box.rc + 1 }).rcTick)
    | _ => .ok store

def declArity : Decl → Nat
  | .fn d => d.arity
  | .extern ar => ar

/-- Dynamic PAP entry is valid for compiler functions explicitly marked safe
and for scalar-only externs. Saturated direct calls do not consult this bit. -/
def declPapSafe : Decl → Bool
  | .fn d => d.papSafe
  | .extern _ => true

/-- Executable result-world check. Scalars are ownership-polymorphic;
a returned location must be live in the function's declared world. -/
def RVal.hasWorld (store : Store) (world : Owned) : RVal → Bool
  | .loc l =>
    match store.get? l with
    | some box => box.world == world
    | none => false
  | .lit _ | .erased => true

/-- Enforce a function declaration's result ownership at its dynamic
boundary. This catches malformed hand-written IxIR₁ even though lowered
programs establish the same fact statically. -/
def checkResultWorld (world : Owned) (out : Store × RVal) :
    Except Err (Store × RVal) :=
  if out.2.hasWorld out.1 world then .ok out
  else .error (.mem "function result ownership mismatch")

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
    | .dropU target => do
      match ← resolveAtom env target with
      | v@(.loc _) => do
        let store' ← dropUVal ctx fuel store v
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
      else do
        let out ← runCode ctx fuel cur store vs.reverse cur.body
        checkResultWorld cur.result out
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
      let v ← callScalarOracle ctx f vs
      .ok (store, v)
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
      else do
        let out ← runCode ctx fuel d store args.reverse d.body
        checkResultWorld d.result out
    | some (.extern ar) =>
      if args.length != ar then
        .error (.stuck "extern arity mismatch")
      else
        match callScalarOracle ctx f args with
        | .ok v => .ok (store, v)
        | .error e => .error e
  termination_by fuel

/-- The apply chain: under-fill builds a new pap, saturation calls,
over-fill calls then applies the rest to the result. Consuming: the
stored arguments are dup'd (their new owner is the successor pap or
the callee) and the applied pap itself is dropped, so chains reclaim
their intermediates. -/
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
        | .papN f ar got => do
          let store ← dupVals store got.toList
          let store ← dropVal ctx fuel store (.loc l)
          let total := got.toList ++ args
          if total.length < ar then
            let (store', l') :=
              store.allocNode .shared (.papN f ar total.toArray)
            .ok (store', .loc l')
          else if total.length == ar then
            match ctx.decls f with
            | none => .error (.unknownRef f)
            | some declaration =>
              if declPapSafe declaration then
                invoke ctx fuel f total store
              else
                .error (.stuck
                  "shared pap targets a non-pap-safe declaration")
          else do
            match ctx.decls f with
            | none => .error (.unknownRef f)
            | some declaration =>
              if declPapSafe declaration then
                let (store', r) ← invoke ctx fuel f (total.take ar) store
                applyGo ctx fuel store' r (total.drop ar)
              else
                .error (.stuck
                  "shared pap targets a non-pap-safe declaration")
        | .ctorN .. => .error (.stuck "apply of a constructor node")
    | .erased => do
      let store ← dropMany ctx fuel store args
      .ok (store, .erased)
    | .lit _ => .error (.stuck "apply of a non-node value")
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

/-- Deep-free of a unique tree: kill the node, recurse into fields.
Whole-value modes are enforced (a shared child under a unique node is
a memory error, symmetric to deep drop's unique-under-shared); no
refcounts are touched. Pap nodes are always shared, so a unique pap
is corrupt by construction and faults. -/
def dropUVal (ctx : Ctx) (fuel : Nat) (store : Store) (v : RVal) :
    Except Err Store :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match v with
    | .lit _ => .ok store
    | .erased => .ok store
    | .loc l =>
      match store.get? l with
      | none => .error (.mem s!"dropU of a dead location {l}")
      | some box =>
        match box.world with
        | .shared => .error (.mem "dropU of a shared node")
        | .unique =>
          match box.node with
          | .ctorN _ fields => dropManyU ctx fuel (store.kill l) fields.toList
          | .papN .. => .error (.mem "dropU of a pap node")
  termination_by fuel

def dropManyU (ctx : Ctx) (fuel : Nat) (store : Store) (vs : List RVal) :
    Except Err Store :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match vs with
    | [] => .ok store
    | v :: rest => do
      let store' ← dropUVal ctx fuel store v
      dropManyU ctx fuel store' rest
  termination_by fuel

end

/-- A successful source return exposes the resolved value and confirms that
the store is unchanged.  This is the terminal inversion rule used by later
small-step simulations. -/
theorem runCode_ret_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {atom : Atom}
    {output : Store × RVal}
    (run : runCode ctx (fuel + 1) cur store env (.ret atom) = .ok output) :
    ∃ value,
      resolveAtom env atom = .ok value ∧ output = (store, value) := by
  rw [runCode.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env atom with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      exact ⟨value, rfl, (Except.ok.inj run).symm⟩

/-- A successful source `letOp` splits at the exact evaluator boundary:
first the operation succeeds, then the continuation succeeds at the same
smaller fuel. -/
theorem runCode_letOp_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {operation : Op} {rest : Code}
    {output : Store × RVal}
    (run : runCode ctx (fuel + 1) cur store env (.letOp operation rest) =
      .ok output) :
    ∃ middle value,
      runOp ctx fuel cur store env operation = .ok (middle, value) ∧
        runCode ctx fuel cur middle (value :: env) rest = .ok output := by
  rw [runCode.eq_def] at run
  dsimp only at run
  cases operationRun : runOp ctx fuel cur store env operation with
  | error error =>
      rw [operationRun] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok operationOutput =>
      obtain ⟨middle, value⟩ := operationOutput
      rw [operationRun] at run
      simp only [bind, Except.bind] at run
      exact ⟨middle, value, rfl, run⟩

/-- A successful `pure` operation is exactly atom resolution and cannot
change the store. -/
theorem runOp_pure_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {atom : Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.pure atom) = .ok output) :
    ∃ value,
      resolveAtom env atom = .ok value ∧ output = (store, value) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env atom with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      exact ⟨value, rfl, (Except.ok.inj run).symm⟩

/-- A successful ordinary allocation exposes its resolved field vector and
the exact fresh-node result chosen by the source store. -/
theorem runOp_alloc_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.alloc world cid arguments) = .ok output) :
    ∃ values,
      resolveAtoms env arguments = .ok values ∧
        output =
          ((store.allocNode world (.ctorN cid values.toArray)).1,
            .loc (store.allocNode world (.ctorN cid values.toArray)).2) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtoms env arguments with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      exact ⟨values, rfl, (Except.ok.inj run).symm⟩

/-- A successful in-place reuse exposes all three dynamic checks and the
exact rewritten unique node selected by the source store. -/
theorem runOp_reuse_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {cid : CtorId}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.reuse target cid arguments) = .ok output) :
    ∃ values location box,
      resolveAtoms env arguments = .ok values ∧
        resolveAtom env target = .ok (.loc location) ∧
        store.get? location = some box ∧
        box.world = .unique ∧
        output =
          ({ store.setBox location
              ⟨.unique, 1, .ctorN cid values.toArray⟩ with
            reuses :=
              (store.setBox location
                ⟨.unique, 1, .ctorN cid values.toArray⟩).reuses + 1 },
            .loc location) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases argumentsResolved : resolveAtoms env arguments with
  | error error =>
      rw [argumentsResolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [argumentsResolved] at run
      simp only [bind, Except.bind] at run
      cases targetResolved : resolveAtom env target with
      | error error =>
          rw [targetResolved] at run
          contradiction
      | ok value =>
          rw [targetResolved] at run
          cases value with
          | lit literal => contradiction
          | erased => contradiction
          | loc location =>
              simp only at run
              cases found : store.get? location with
              | none =>
                  rw [found] at run
                  contradiction
              | some box =>
                  rw [found] at run
                  simp only at run
                  cases worldEq : box.world with
                  | shared =>
                      rw [worldEq] at run
                      contradiction
                  | unique =>
                      rw [worldEq] at run
                      exact ⟨values, location, box, rfl, rfl, found,
                        worldEq, (Except.ok.inj run).symm⟩

/-- A successful shallow free exposes the live unique box selected by its
operand and the exact killed-store result. -/
theorem runOp_free_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.free target) = .ok output) :
    ∃ location box,
      resolveAtom env target = .ok (.loc location) ∧
        store.get? location = some box ∧
        box.world = .unique ∧
        output = (store.kill location, .erased) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env target with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases value with
      | lit literal => contradiction
      | erased => contradiction
      | loc location =>
          simp only at run
          cases found : store.get? location with
          | none =>
              rw [found] at run
              contradiction
          | some box =>
              rw [found] at run
              simp only at run
              cases worldEq : box.world with
              | shared =>
                  rw [worldEq] at run
                  contradiction
              | unique =>
                  rw [worldEq] at run
                  exact ⟨location, box, rfl, found, worldEq,
                    (Except.ok.inj run).symm⟩

/-- A successful projection exposes the selected live constructor node and
the exact field returned without changing the store. -/
theorem runOp_fetch_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {field : Nat}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.fetch target field) =
      .ok output) :
    ∃ location box identity fields value,
      resolveAtom env target = .ok (.loc location) ∧
        store.get? location = some box ∧
        box.node = .ctorN identity fields ∧
        fields[field]? = some value ∧
        output = (store, value) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env target with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok resolvedValue =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases resolvedValue with
      | lit literal => contradiction
      | erased => contradiction
      | loc location =>
          simp only at run
          cases found : store.get? location with
          | none =>
              rw [found] at run
              contradiction
          | some box =>
              rw [found] at run
              simp only at run
              cases nodeEq : box.node with
              | papN function supplied =>
                  rw [nodeEq] at run
                  contradiction
              | ctorN identity fields =>
                  rw [nodeEq] at run
                  simp only at run
                  cases fieldEq : fields[field]? with
                  | none =>
                      rw [fieldEq] at run
                      contradiction
                  | some value =>
                      rw [fieldEq] at run
                      exact ⟨location, box, identity, fields, value,
                        rfl, found, nodeEq, fieldEq,
                        (Except.ok.inj run).symm⟩

/-- A successful `dup` exposes either the live shared node whose reference
count was incremented or the inert scalar that passed through unchanged. -/
theorem runOp_dup_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.dup target) = .ok output) :
    ∃ value,
      resolveAtom env target = .ok value ∧
        match value with
        | .loc location =>
          ∃ box,
            store.get? location = some box ∧
              box.world = .shared ∧
              output =
                ((store.setBox location { box with rc := box.rc + 1 }).rcTick,
                  .loc location)
        | .lit _ | .erased => output = (store, value) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env target with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases value with
      | lit literal =>
          exact ⟨.lit literal, rfl, (Except.ok.inj run).symm⟩
      | erased =>
          exact ⟨.erased, rfl, (Except.ok.inj run).symm⟩
      | loc location =>
          simp only at run
          cases found : store.get? location with
          | none =>
              rw [found] at run
              contradiction
          | some box =>
              rw [found] at run
              simp only at run
              cases worldEq : box.world with
              | unique =>
                  rw [worldEq] at run
                  contradiction
              | shared =>
                  rw [worldEq] at run
                  refine ⟨.loc location, rfl, box, found, worldEq, ?_⟩
                  simpa [worldEq] using (Except.ok.inj run).symm

/-- A successful shared drop either delegates the selected location to
`dropVal` or leaves the store unchanged for an inert scalar. -/
theorem runOp_drop_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.drop target) = .ok output) :
    ∃ value,
      resolveAtom env target = .ok value ∧
        match value with
        | .loc location =>
          ∃ store',
            dropVal ctx fuel store (.loc location) = .ok store' ∧
              output = (store', .erased)
        | .lit _ | .erased => output = (store, .erased) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env target with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases value with
      | lit literal =>
          exact ⟨.lit literal, rfl, (Except.ok.inj run).symm⟩
      | erased =>
          exact ⟨.erased, rfl, (Except.ok.inj run).symm⟩
      | loc location =>
          simp only at run
          cases dropped : dropVal ctx fuel store (.loc location) with
          | error error =>
              rw [dropped] at run
              contradiction
          | ok store' =>
              rw [dropped] at run
              exact ⟨.loc location, rfl, store', dropped,
                (Except.ok.inj run).symm⟩

/-- A successful unique drop either delegates the selected location to
`dropUVal` or leaves the store unchanged for an inert scalar. -/
theorem runOp_dropU_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.dropU target) = .ok output) :
    ∃ value,
      resolveAtom env target = .ok value ∧
        match value with
        | .loc location =>
          ∃ store',
            dropUVal ctx fuel store (.loc location) = .ok store' ∧
              output = (store', .erased)
        | .lit _ | .erased => output = (store, .erased) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env target with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases value with
      | lit literal =>
          exact ⟨.lit literal, rfl, (Except.ok.inj run).symm⟩
      | erased =>
          exact ⟨.erased, rfl, (Except.ok.inj run).symm⟩
      | loc location =>
          simp only at run
          cases dropped : dropUVal ctx fuel store (.loc location) with
          | error error =>
              rw [dropped] at run
              contradiction
          | ok store' =>
              rw [dropped] at run
              exact ⟨.loc location, rfl, store', dropped,
                (Except.ok.inj run).symm⟩

/-- A successful direct call exposes argument resolution and the exact
`invoke` boundary used by the source evaluator. -/
theorem runOp_call_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {function : Address}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.call function arguments) = .ok output) :
    ∃ values,
      resolveAtoms env arguments = .ok values ∧
        invoke ctx fuel function values store = .ok output := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtoms env arguments with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      exact ⟨values, rfl, run⟩

/-- A successful self call exposes the exact recursive body run and its
result-world boundary check. -/
theorem runOp_callSelf_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {arguments : Array Atom}
    {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env (.callSelf arguments) =
      .ok output) :
    ∃ values bodyOutput,
      resolveAtoms env arguments = .ok values ∧
        values.length = cur.arity ∧
        runCode ctx fuel cur store values.reverse cur.body = .ok bodyOutput ∧
        checkResultWorld cur.result bodyOutput = .ok output := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtoms env arguments with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      by_cases arity : values.length = cur.arity
      · simp [arity] at run
        cases bodyRun : runCode ctx fuel cur store values.reverse cur.body with
        | error error =>
            rw [bodyRun] at run
            contradiction
        | ok bodyOutput =>
            rw [bodyRun] at run
            exact ⟨values, bodyOutput, rfl, arity, bodyRun, run⟩
      · simp [arity] at run

/-- A successful partial application exposes the retained declaration,
strict under-saturation, and the exact allocated pap node. -/
theorem runOp_papp_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {function : Address}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.papp function arguments) = .ok output) :
    ∃ values declaration,
      resolveAtoms env arguments = .ok values ∧
        ctx.decls function = some declaration ∧
        values.length < declArity declaration ∧
        output =
          ((store.allocNode .shared
            (.papN function (declArity declaration) values.toArray)).1,
            .loc (store.allocNode .shared
              (.papN function (declArity declaration) values.toArray)).2) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtoms env arguments with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases found : ctx.decls function with
      | none =>
          rw [found] at run
          contradiction
      | some declaration =>
          rw [found] at run
          by_cases undersaturated : values.length < declArity declaration
          · simp only [undersaturated, ↓reduceIte] at run
            exact ⟨values, declaration, rfl, rfl, undersaturated,
              (Except.ok.inj run).symm⟩
          · simp only [undersaturated, ↓reduceIte] at run
            contradiction

/-- A successful dynamic application exposes both resolver boundaries and
the exact `applyGo` computation delegated to by `runOp`. -/
theorem runOp_apply_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {function : Atom}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.apply function arguments) = .ok output) :
    ∃ functionValue values,
      resolveAtom env function = .ok functionValue ∧
        resolveAtoms env arguments = .ok values ∧
        applyGo ctx fuel store functionValue values = .ok output := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases functionResolved : resolveAtom env function with
  | error error =>
      rw [functionResolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok functionValue =>
      rw [functionResolved] at run
      simp only [bind, Except.bind] at run
      cases argumentsResolved : resolveAtoms env arguments with
      | error error =>
          rw [argumentsResolved] at run
          contradiction
      | ok values =>
          rw [argumentsResolved] at run
          exact ⟨functionValue, values, rfl, rfl, run⟩

/-- A successful trusted extern call exposes scalar-oracle evaluation and
confirms that the source store is unchanged. -/
theorem runOp_extern_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {function : Address}
    {arguments : Array Atom} {output : Store × RVal}
    (run : runOp ctx (fuel + 1) cur store env
      (.extern function arguments) = .ok output) :
    ∃ values value,
      resolveAtoms env arguments = .ok values ∧
        callScalarOracle ctx function values = .ok value ∧
        output = (store, value) := by
  rw [runOp.eq_def] at run
  dsimp only at run
  cases argumentsResolved : resolveAtoms env arguments with
  | error error =>
      rw [argumentsResolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok values =>
      rw [argumentsResolved] at run
      simp only [bind, Except.bind] at run
      cases oracleRun : callScalarOracle ctx function values with
      | error error =>
          rw [oracleRun] at run
          contradiction
      | ok value =>
          rw [oracleRun] at run
          exact ⟨values, value, rfl, oracleRun,
            (Except.ok.inj run).symm⟩

/-- The successful branches of a known-address source invocation, indexed by
the smaller fuel used for a function body. -/
inductive InvokeSuccess (ctx : Ctx) (fuel : Nat) (function : Address)
    (arguments : List RVal) (store : Store) (output : Store × RVal) : Prop
  | fn {definition : FnDef} {bodyOutput : Store × RVal}
      (declaration : ctx.decls function = some (.fn definition))
      (arity : arguments.length = definition.arity)
      (bodyRun : runCode ctx fuel definition store arguments.reverse
        definition.body = .ok bodyOutput)
      (resultRun : checkResultWorld definition.result bodyOutput = .ok output)
  | extern {arity : Nat} {value : RVal}
      (declaration : ctx.decls function = some (.extern arity))
      (argumentsArity : arguments.length = arity)
      (oracleRun : callScalarOracle ctx function arguments = .ok value)
      (outputEq : output = (store, value))

/-- Every successful `invoke` has positive fuel and selects exactly one of
the function-body or scalar-extern branches above. -/
theorem invoke_success {ctx : Ctx} {fuel : Nat} {function : Address}
    {arguments : List RVal} {store : Store} {output : Store × RVal}
    (run : invoke ctx fuel function arguments store = .ok output) :
    ∃ bodyFuel,
      fuel = bodyFuel + 1 ∧
        InvokeSuccess ctx bodyFuel function arguments store output := by
  cases fuel with
  | zero =>
      rw [invoke.eq_def] at run
      contradiction
  | succ bodyFuel =>
      rw [invoke.eq_def] at run
      dsimp only at run
      cases found : ctx.decls function with
      | none =>
          rw [found] at run
          contradiction
      | some declaration =>
          rw [found] at run
          cases declaration with
          | fn definition =>
              by_cases arity : arguments.length = definition.arity
              · simp [arity] at run
                cases bodyRun : runCode ctx bodyFuel definition store
                    arguments.reverse definition.body with
                | error error =>
                    rw [bodyRun] at run
                    simp only [bind, Except.bind] at run
                    contradiction
                | ok bodyOutput =>
                    rw [bodyRun] at run
                    simp only [bind, Except.bind] at run
                    exact ⟨bodyFuel, rfl,
                      .fn found arity bodyRun run⟩
              · simp [arity] at run
          | extern expectedArity =>
              by_cases arity : arguments.length = expectedArity
              · simp [arity] at run
                cases oracleRun : callScalarOracle ctx function arguments with
                | error error =>
                    rw [oracleRun] at run
                    contradiction
                | ok value =>
                    rw [oracleRun] at run
                    exact ⟨bodyFuel, rfl,
                      .extern found arity oracleRun
                        (Except.ok.inj run).symm⟩
              · simp [arity] at run

/-- The three successful source-case shapes.  The relation retains the exact
selected source alternative and the recursive branch run, while ruling out
all stuck scrutinee, tag, and field-arity paths. -/
inductive RunCodeCaseSuccess (ctx : Ctx) (fuel : Nat) (cur : FnDef)
    (store : Store) (env : List RVal) (scrutinee : Atom) (peelNat : Bool)
    (alternatives : Array Alt) (output : Store × RVal) : Prop
  | ctorBranch {location : Nat} {box : NodeBox} {cid : CtorId}
      {fields : Array RVal} {fieldCount : Nat} {body : Code}
      (resolved : resolveAtom env scrutinee = .ok (.loc location))
      (found : store.get? location = some box)
      (node : box.node = .ctorN cid fields)
      (selected : alternatives.find? (fun alternative =>
        alternative.cidx == cid.cidx) =
          some (.mk cid.cidx fieldCount body))
      (fieldArity : fields.size = fieldCount)
      (branchRun : runCode ctx fuel cur store
        (fields.toList.reverse ++ env) body = .ok output)
  | natZero {body : Code}
      (peels : peelNat = true)
      (resolved : resolveAtom env scrutinee = .ok (.lit (.nat 0)))
      (selected : alternatives.find? (fun alternative =>
        alternative.cidx == 0) = some (.mk 0 0 body))
      (branchRun : runCode ctx fuel cur store env body = .ok output)
  | natSucc {predecessor : Nat} {body : Code}
      (peels : peelNat = true)
      (resolved : resolveAtom env scrutinee =
        .ok (.lit (.nat (predecessor + 1))))
      (selected : alternatives.find? (fun alternative =>
        alternative.cidx == 1) = some (.mk 1 1 body))
      (branchRun : runCode ctx fuel cur store
        (.lit (.nat predecessor) :: env) body = .ok output)

/-- A successful source `case` determines one exact recursive branch at the
same smaller fuel. -/
theorem runCode_case_success {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {scrutinee : Atom} {peelNat : Bool}
    {alternatives : Array Alt} {output : Store × RVal}
    (run : runCode ctx (fuel + 1) cur store env
      (.case scrutinee peelNat alternatives) = .ok output) :
    RunCodeCaseSuccess ctx fuel cur store env scrutinee peelNat alternatives
      output := by
  rw [runCode.eq_def] at run
  dsimp only at run
  cases resolved : resolveAtom env scrutinee with
  | error error =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok value =>
      rw [resolved] at run
      simp only [bind, Except.bind] at run
      cases value with
      | erased => contradiction
      | loc location =>
          simp only at run
          cases found : store.get? location with
          | none =>
              rw [found] at run
              contradiction
          | some box =>
              rw [found] at run
              simp only at run
              cases nodeEq : box.node with
              | papN function arity captured =>
                  rw [nodeEq] at run
                  contradiction
              | ctorN cid fields =>
                  rw [nodeEq] at run
                  simp only at run
                  cases selected : alternatives.find? (fun alternative =>
                      alternative.cidx == cid.cidx) with
                  | none =>
                      rw [selected] at run
                      contradiction
                  | some alternative =>
                      rw [selected] at run
                      cases alternative with
                      | mk tag fieldCount body =>
                          simp only at run
                          by_cases fieldArity : fields.size = fieldCount
                          · simp [fieldArity] at run
                            have matched :
                                ((.mk tag fieldCount body : Alt).cidx ==
                                  cid.cidx) = true :=
                              Array.find?_some
                                (p := fun alternative : Alt =>
                                  alternative.cidx == cid.cidx)
                                (a := .mk tag fieldCount body)
                                (xs := alternatives) selected
                            have tagEq : tag = cid.cidx :=
                              beq_iff_eq.mp matched
                            subst tag
                            exact .ctorBranch resolved found nodeEq selected
                              fieldArity run
                          · simp [fieldArity] at run
      | lit literal =>
          cases literal with
          | str string => contradiction
          | nat number =>
              cases peelNat with
              | false => contradiction
              | true =>
                  simp only at run
                  cases number with
                  | zero =>
                      cases selected : alternatives.find? (fun alternative =>
                          alternative.cidx == 0) with
                      | none =>
                          rw [selected] at run
                          contradiction
                      | some alternative =>
                          rw [selected] at run
                          cases alternative with
                          | mk tag fieldCount body =>
                              cases fieldCount with
                              | zero =>
                                  have matched :
                                      ((.mk tag 0 body : Alt).cidx == 0) =
                                        true :=
                                    Array.find?_some
                                      (p := fun alternative : Alt =>
                                        alternative.cidx == 0)
                                      (a := .mk tag 0 body)
                                      (xs := alternatives) selected
                                  have tagEq : tag = 0 :=
                                    beq_iff_eq.mp matched
                                  subst tag
                                  exact .natZero rfl resolved selected run
                              | succ fieldCount => contradiction
                  | succ predecessor =>
                      cases selected : alternatives.find? (fun alternative =>
                          alternative.cidx == 1) with
                      | none =>
                          rw [selected] at run
                          contradiction
                      | some alternative =>
                          rw [selected] at run
                          cases alternative with
                          | mk tag fieldCount body =>
                              cases fieldCount with
                              | zero => contradiction
                              | succ remaining =>
                                  cases remaining with
                                  | zero =>
                                      have matched :
                                          ((.mk tag 1 body : Alt).cidx == 1) =
                                            true :=
                                        Array.find?_some
                                          (p := fun alternative : Alt =>
                                            alternative.cidx == 1)
                                          (a := .mk tag 1 body)
                                          (xs := alternatives) selected
                                      have tagEq : tag = 1 :=
                                        beq_iff_eq.mp matched
                                      subst tag
                                      exact .natSucc rfl resolved selected run
                                  | succ remaining => contradiction

/-- Run a top-level code sequence in a fresh store (the `cur` frame is
the code itself, so `callSelf` at top level re-enters it). -/
def runMain (ctx : Ctx) (c : Code) (fuel : Nat := 100000) :
    Except Err (Store × RVal) :=
  runCode ctx fuel ⟨0, .shared, false, c⟩ {} [] c

/-- Run a closed top-level code sequence at its declared result world and
check that world at the public boundary.  Unlike `runMain`, this form also
installs the declared world in the synthetic current function, so a
top-level `callSelf` observes the same result contract as the enclosing
entry. -/
def runOwnedMain (ctx : Ctx) (result : Owned) (c : Code)
    (fuel : Nat := 100000) : Except Err (Store × RVal) := do
  let out ← runCode ctx fuel ⟨0, result, false, c⟩ {} [] c
  checkResultWorld result out

end Ix.Compiler.IxIR1
