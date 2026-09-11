import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.IxIR1.Readdress

/-!
# Semantic transport for IxIR₁ address renaming

Content addressing changes declaration keys and every reference to those
keys.  Runtime heaps also retain addresses in constructor identities and PAP
nodes, so semantic transport must cover the whole evaluator state rather than
only its input code.

This module first defines the structural action of an arbitrary address map
on evaluator state and errors.  `Ctx.Renames` is the exact forward lookup and
oracle compatibility required by the evaluator; it intentionally permits
non-injective maps when declarations with the same image are semantically the
same, which is the case used by exact-content deduplication.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address)

namespace Readdress

namespace Node

/-- Apply an address map to the identities retained in a heap node. -/
def mapAddresses (rename : Address → Address) : Node → Node
  | .ctorN constructor fields =>
      .ctorN (CtorId.mapAddresses rename constructor) fields
  | .papN function arity arguments =>
      .papN (rename function) arity arguments

end Node

namespace NodeBox

/-- Apply an address map beneath one live heap cell. -/
def mapAddresses (rename : Address → Address) (box : NodeBox) : NodeBox :=
  { box with node := Node.mapAddresses rename box.node }

end NodeBox

namespace Store

/-- Apply an address map to every live or dead heap cell.  Locations,
ownership, reference counts, and all cost counters remain unchanged. -/
def mapAddresses (rename : Address → Address) (store : Store) : Store :=
  { store with
      nodes := store.nodes.map (Option.map (NodeBox.mapAddresses rename)) }

end Store

namespace Err

/-- Address action on evaluator failures.  Only a closed-world lookup failure
retains an address. -/
def mapAddresses (rename : Address → Address) : Err → Err
  | .fuel => .fuel
  | .stuck message => .stuck message
  | .mem message => .mem message
  | .unknownRef address => .unknownRef (rename address)

end Err

/-- Address action on a store-returning evaluator result. -/
def mapStoreResult (rename : Address → Address) :
    Except Err Store → Except Err Store
  | .ok store => .ok (Store.mapAddresses rename store)
  | .error error => .error (Err.mapAddresses rename error)

/-- Address action on an ordinary evaluator result.  Runtime values contain
locations and scalars but no declaration addresses. -/
def mapRunResult (rename : Address → Address) :
    Except Err (Store × RVal) → Except Err (Store × RVal)
  | .ok (store, value) => .ok (Store.mapAddresses rename store, value)
  | .error error => .error (Err.mapAddresses rename error)

/-- Address action on a scalar/runtime-value evaluator result. -/
def mapValueResult (rename : Address → Address) :
    Except Err RVal → Except Err RVal
  | .ok value => .ok value
  | .error error => .error (Err.mapAddresses rename error)

/-- Address action on a list-of-runtime-values evaluator result. -/
def mapValuesResult (rename : Address → Address) :
    Except Err (List RVal) → Except Err (List RVal)
  | .ok values => .ok values
  | .error error => .error (Err.mapAddresses rename error)

@[simp] private theorem except_ok_bind {Error Value Result : Type}
    (value : Value) (next : Value → Except Error Result) :
    (Except.ok value >>= next) = next value := rfl

@[simp] private theorem except_error_bind {Error Value Result : Type}
    (error : Error) (next : Value → Except Error Result) :
    (Except.error error >>= next) = Except.error error := rfl

@[simp] theorem mapRunResult_ok (rename : Address → Address)
    (store : Store) (value : RVal) :
    mapRunResult rename (.ok (store, value)) =
      .ok (Store.mapAddresses rename store, value) := rfl

@[simp] theorem mapRunResult_error (rename : Address → Address)
    (error : Err) :
    mapRunResult rename (.error error) =
      .error (Err.mapAddresses rename error) := rfl

@[simp] theorem mapStoreResult_ok (rename : Address → Address)
    (store : Store) :
    mapStoreResult rename (.ok store) =
      .ok (Store.mapAddresses rename store) := rfl

@[simp] theorem mapStoreResult_error (rename : Address → Address)
    (error : Err) :
    mapStoreResult rename (.error error) =
      .error (Err.mapAddresses rename error) := rfl

@[simp] theorem Err.mapAddresses_fuel (rename : Address → Address) :
    Err.mapAddresses rename .fuel = .fuel := rfl

@[simp] theorem Err.mapAddresses_stuck (rename : Address → Address)
    (message : String) :
    Err.mapAddresses rename (.stuck message) = .stuck message := rfl

@[simp] theorem Err.mapAddresses_mem (rename : Address → Address)
    (message : String) :
    Err.mapAddresses rename (.mem message) = .mem message := rfl

@[simp] theorem Err.mapAddresses_unknownRef (rename : Address → Address)
    (address : Address) :
    Err.mapAddresses rename (.unknownRef address) =
      .unknownRef (rename address) := rfl

namespace Ctx

/-- The target context is the forward image of the source context at every
address that the source evaluator can request.  The oracle condition is
separate because extern declarations and direct `extern` operations both
consult it. -/
structure Renames (rename : Address → Address) (before after : Ctx) : Prop where
  decls : ∀ address,
    after.decls (rename address) =
      (before.decls address).map (Decl.mapAddresses rename)
  oracle : ∀ address arguments,
    after.oracle (rename address) arguments = before.oracle address arguments

end Ctx

@[simp] theorem declPapSafe_mapAddresses (rename : Address → Address)
    (declaration : Decl) :
    declPapSafe (Decl.mapAddresses rename declaration) =
      declPapSafe declaration := by
  cases declaration <;> rfl

/-! ## Certified readdressing contexts -/

private theorem envOfList_some_mem
    {entries : List (Address × Decl)} {address : Address} {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    (address, declaration) ∈ entries := by
  unfold Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × Decl => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

theorem Result.main_eq_mapAddresses {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true) :
    result.main =
      Code.mapAddresses (Renaming.apply result.addressMap) main := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  exact (Code.structurallyEq_eq_true_iff _ _).mp haudit.1.1

theorem Result.lookup_eq_mapAddresses {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList raw address = some declaration) :
    Env.ofList result.declarations
        (Renaming.apply result.addressMap address) =
      some (Decl.mapAddresses
        (Renaming.apply result.addressMap) declaration) := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  have hmember : (address, declaration) ∈ raw :=
    envOfList_some_mem hlookup
  have hentry := (List.all_eq_true.mp haudit.1.2)
    (address, declaration) hmember
  cases hemitted : Env.ofList result.declarations
      (Renaming.apply result.addressMap address) with
  | none => simp [hlookup, hemitted] at hentry
  | some emitted =>
      have hequal : emitted =
          Decl.mapAddresses (Renaming.apply result.addressMap) declaration :=
        (Decl.structurallyEq_eq_true_iff _ _).mp (by
          simpa [hlookup, hemitted] using hentry)
      simp [hequal]

theorem Result.lookup_stable {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList result.declarations address = some declaration) :
    Decl.mapAddresses (Renaming.apply result.addressMap) declaration =
      declaration := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  have hmember : (address, declaration) ∈ result.declarations :=
    envOfList_some_mem hlookup
  have hentry := (List.all_eq_true.mp haudit.2)
    (address, declaration) hmember
  exact (Decl.structurallyEq_eq_true_iff _ _).mp (by
    simpa [hlookup] using hentry)

/-- The theorem-facing source environment contains the raw declaration at
every successful raw lookup.  At an otherwise-unbound address it supplies
the stable emitted lookup of the renamed key; these aliases are exactly what
makes the context relation total after new content keys are introduced. -/
def Result.preAddressEnv (result : Result)
    (raw : List (Address × Decl)) : Env :=
  fun address =>
    match Env.ofList raw address with
    | some declaration => some declaration
    | none =>
        Env.ofList result.declarations
          (Renaming.apply result.addressMap address)

/-- Evaluator context for the emitted, content-addressed artifact. -/
def Result.addressedCtx (result : Result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Ctx :=
  { decls := Env.ofList result.declarations, oracle }

/-- Pull the addressed oracle back along the same map used for declarations.
Raw lookups remain exact; stable aliases cover newly introduced target keys. -/
def Result.preAddressCtx (result : Result)
    (raw : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Ctx :=
  { decls := result.preAddressEnv raw
    oracle := fun address arguments =>
      oracle (Renaming.apply result.addressMap address) arguments }

@[simp] theorem Result.preAddressCtx_decls_of_lookup
    (result : Result) (raw : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList raw address = some declaration) :
    (result.preAddressCtx raw oracle).decls address = some declaration := by
  simp [Result.preAddressCtx, Result.preAddressEnv, hlookup]

/-- A successful semantic audit constructs the exact total context relation
consumed by evaluator equivariance. -/
theorem Result.renames_preAddressCtx {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true)
    (oracle : Address → List RVal → Option RVal) :
    Ctx.Renames (Renaming.apply result.addressMap)
      (result.preAddressCtx raw oracle) (result.addressedCtx oracle) := by
  constructor
  · intro address
    simp only [Result.preAddressCtx, Result.addressedCtx,
      Result.preAddressEnv]
    cases hraw : Env.ofList raw address with
    | some declaration =>
        simpa [hraw] using result.lookup_eq_mapAddresses haudit hraw
    | none =>
        simp only
        cases hemitted : Env.ofList result.declarations
            (Renaming.apply result.addressMap address) with
        | none => simp
        | some declaration =>
            have hstable := result.lookup_stable haudit hemitted
            simp [hstable]
  · intro address arguments
    rfl

/-! ## Structural evaluator-state laws -/

@[simp] theorem NodeBox.mapAddresses_world (rename : Address → Address)
    (box : NodeBox) :
    (NodeBox.mapAddresses rename box).world = box.world := rfl

@[simp] theorem NodeBox.mapAddresses_rc (rename : Address → Address)
    (box : NodeBox) :
    (NodeBox.mapAddresses rename box).rc = box.rc := rfl

@[simp] theorem NodeBox.mapAddresses_node (rename : Address → Address)
    (box : NodeBox) :
    (NodeBox.mapAddresses rename box).node =
      Node.mapAddresses rename box.node := rfl

@[simp] theorem Store.mapAddresses_allocs (rename : Address → Address)
    (store : Store) :
    (Store.mapAddresses rename store).allocs = store.allocs := rfl

@[simp] theorem Store.mapAddresses_reuses (rename : Address → Address)
    (store : Store) :
    (Store.mapAddresses rename store).reuses = store.reuses := rfl

@[simp] theorem Store.mapAddresses_frees (rename : Address → Address)
    (store : Store) :
    (Store.mapAddresses rename store).frees = store.frees := rfl

@[simp] theorem Store.mapAddresses_rcops (rename : Address → Address)
    (store : Store) :
    (Store.mapAddresses rename store).rcops = store.rcops := rfl

@[simp] theorem Store.mapAddresses_empty (rename : Address → Address) :
    Store.mapAddresses rename ({} : Store) = {} := by
  simp [Store.mapAddresses]

@[simp] theorem Store.get?_mapAddresses (rename : Address → Address)
    (store : Store) (location : Nat) :
    (Store.mapAddresses rename store).get? location =
      (store.get? location).map (NodeBox.mapAddresses rename) := by
  simp only [Store.mapAddresses, Store.get?, Array.getElem?_map]
  cases hcell : store.nodes[location]? with
  | none => simp
  | some cell =>
      cases cell <;> simp

@[simp] theorem Store.mapAddresses_setBox (rename : Address → Address)
    (store : Store) (location : Nat) (box : NodeBox) :
    Store.mapAddresses rename (store.setBox location box) =
      (Store.mapAddresses rename store).setBox location
        (NodeBox.mapAddresses rename box) := by
  simp [Store.mapAddresses, Store.setBox]

@[simp] theorem Store.mapAddresses_kill (rename : Address → Address)
    (store : Store) (location : Nat) :
    Store.mapAddresses rename (store.kill location) =
      (Store.mapAddresses rename store).kill location := by
  simp [Store.mapAddresses, Store.kill]

@[simp] theorem Store.mapAddresses_rcTick (rename : Address → Address)
    (store : Store) :
    Store.mapAddresses rename store.rcTick =
      (Store.mapAddresses rename store).rcTick := by
  simp [Store.mapAddresses, Store.rcTick]

@[simp] theorem Store.mapAddresses_allocNode_fst
    (rename : Address → Address) (store : Store)
    (world : Ixon.Owned) (node : Node) :
    Store.mapAddresses rename (store.allocNode world node).1 =
      ((Store.mapAddresses rename store).allocNode world
        (Node.mapAddresses rename node)).1 := by
  simp [Store.mapAddresses, Store.allocNode, NodeBox.mapAddresses]

@[simp] theorem Store.mapAddresses_allocNode_snd
    (rename : Address → Address) (store : Store)
    (world : Ixon.Owned) (node : Node) :
    (store.allocNode world node).2 =
      ((Store.mapAddresses rename store).allocNode world
        (Node.mapAddresses rename node)).2 := by
  simp [Store.mapAddresses, Store.allocNode]

@[simp] theorem Store.mapAddresses_countReuse
    (rename : Address → Address) (store : Store) :
    Store.mapAddresses rename { store with reuses := store.reuses + 1 } =
      { Store.mapAddresses rename store with
        reuses := (Store.mapAddresses rename store).reuses + 1 } := by
  simp [Store.mapAddresses]

@[simp] theorem RVal.hasWorld_mapAddresses
    (rename : Address → Address) (store : Store)
    (world : Ixon.Owned) (value : RVal) :
    value.hasWorld (Store.mapAddresses rename store) world =
      value.hasWorld store world := by
  cases value with
  | loc location =>
      cases hbox : store.get? location <;> simp [RVal.hasWorld, hbox]
  | lit literal => simp [RVal.hasWorld]
  | erased => simp [RVal.hasWorld]

theorem checkResultWorld_mapAddresses
    (rename : Address → Address) (world : Ixon.Owned)
    (out : Store × RVal) :
    checkResultWorld world
        (Store.mapAddresses rename out.1, out.2) =
      mapRunResult rename (checkResultWorld world out) := by
  rcases out with ⟨store, value⟩
  by_cases hworld : value.hasWorld store world
  · simp [checkResultWorld, mapRunResult, hworld]
  · simp [checkResultWorld, mapRunResult, Err.mapAddresses, hworld]

theorem resolveAtom_mapValueResult (rename : Address → Address)
    (environment : List RVal) (atom : Atom) :
    mapValueResult rename (resolveAtom environment atom) =
      resolveAtom environment atom := by
  cases atom with
  | var index =>
      cases hvalue : environment[index]? <;>
        simp [resolveAtom, mapValueResult, Err.mapAddresses, hvalue]
  | lit literal => simp [resolveAtom, mapValueResult]
  | erased => simp [resolveAtom, mapValueResult]

private theorem resolveAtomsList_mapValuesResult
    (rename : Address → Address) (environment : List RVal)
    (atoms : List Atom) (initial : List RVal) :
    mapValuesResult rename
        (atoms.foldlM (fun accumulated atom => do
          pure (accumulated ++ [← resolveAtom environment atom])) initial) =
      atoms.foldlM (fun accumulated atom => do
        pure (accumulated ++ [← resolveAtom environment atom])) initial := by
  induction atoms generalizing initial with
  | nil =>
      change (Except.ok initial : Except Err (List RVal)) = .ok initial
      rfl
  | cons atom rest ih =>
      simp only [List.foldlM_cons]
      cases hresolve : resolveAtom environment atom with
      | ok value =>
          change mapValuesResult rename
              (rest.foldlM (fun accumulated atom => do
                pure (accumulated ++ [← resolveAtom environment atom]))
                (initial ++ [value])) =
            rest.foldlM (fun accumulated atom => do
              pure (accumulated ++ [← resolveAtom environment atom]))
              (initial ++ [value])
          exact ih (initial ++ [value])
      | error error =>
          have hmapped := resolveAtom_mapValueResult rename environment atom
          simp [hresolve, mapValueResult] at hmapped
          change Except.error (Err.mapAddresses rename error) =
            Except.error error
          rw [hmapped]

theorem resolveAtoms_mapValuesResult (rename : Address → Address)
    (environment : List RVal) (atoms : Array Atom) :
    mapValuesResult rename (resolveAtoms environment atoms) =
      resolveAtoms environment atoms := by
  simp only [resolveAtoms, ← Array.foldlM_toList]
  exact resolveAtomsList_mapValuesResult rename environment atoms.toList []

theorem Err.mapAddresses_of_resolveAtom_error
    (rename : Address → Address) (environment : List RVal) (atom : Atom)
    {error : Err} (herror : resolveAtom environment atom = .error error) :
    Err.mapAddresses rename error = error := by
  have hmapped := resolveAtom_mapValueResult rename environment atom
  simpa [herror, mapValueResult] using hmapped

theorem Err.mapAddresses_of_resolveAtoms_error
    (rename : Address → Address) (environment : List RVal)
    (atoms : Array Atom) {error : Err}
    (herror : resolveAtoms environment atoms = .error error) :
    Err.mapAddresses rename error = error := by
  have hmapped := resolveAtoms_mapValuesResult rename environment atoms
  simpa [herror, mapValuesResult] using hmapped

@[simp] theorem Alt.cidx_mapAddresses (rename : Address → Address)
    (alternative : Alt) :
    (Alt.mapAddresses rename alternative).cidx = alternative.cidx := by
  cases alternative <;> rfl

private theorem AltList.find?_mapAddresses (rename : Address → Address)
    (constructor : Nat) (alternatives : List Alt) :
    (AltList.mapAddresses rename alternatives).find?
        (fun alternative => alternative.cidx == constructor) =
      (alternatives.find?
        (fun alternative => alternative.cidx == constructor)).map
          (Alt.mapAddresses rename) := by
  induction alternatives with
  | nil => rfl
  | cons alternative rest ih =>
      cases alternative with
      | mk cidx fields body =>
          simp only [AltList.mapAddresses, Alt.mapAddresses, Alt.cidx,
            List.find?_cons]
          by_cases hmatch : cidx == constructor
          · simp only [hmatch, Option.map_some]
            rfl
          · simp only [hmatch]
            exact ih

theorem AltArray.find?_mapAddresses (rename : Address → Address)
    (constructor : Nat) (alternatives : Array Alt) :
    ((AltList.mapAddresses rename alternatives.toList).toArray.find?
        (fun alternative => alternative.cidx == constructor)) =
      (alternatives.find?
        (fun alternative => alternative.cidx == constructor)).map
          (Alt.mapAddresses rename) := by
  simpa only [← Array.find?_toList, List.toList_toArray] using
    AltList.find?_mapAddresses rename constructor alternatives.toList

@[simp] theorem Decl.declArity_mapAddresses (rename : Address → Address)
    (declaration : Decl) :
    declArity (Decl.mapAddresses rename declaration) =
      declArity declaration := by
  cases declaration <;> rfl

@[simp] theorem FnDef.mapAddresses_arity (rename : Address → Address)
    (definition : FnDef) :
    (FnDef.mapAddresses rename definition).arity = definition.arity := rfl

@[simp] theorem FnDef.mapAddresses_result (rename : Address → Address)
    (definition : FnDef) :
    (FnDef.mapAddresses rename definition).result = definition.result := rfl

@[simp] theorem FnDef.mapAddresses_body (rename : Address → Address)
    (definition : FnDef) :
    (FnDef.mapAddresses rename definition).body =
      Code.mapAddresses rename definition.body := rfl

/-- Reference-count duplication is insensitive to declaration addresses and
commutes with the heap action exactly. -/
theorem dupVals_mapAddresses (rename : Address → Address)
    (store : Store) (values : List RVal) :
    dupVals (Store.mapAddresses rename store) values =
      mapStoreResult rename (dupVals store values) := by
  induction values generalizing store with
  | nil =>
      change Except.ok (Store.mapAddresses rename store) =
        mapStoreResult rename (Except.ok store)
      rfl
  | cons value rest ih =>
      cases value with
      | lit literal =>
          change dupVals (Store.mapAddresses rename store) rest =
            mapStoreResult rename (dupVals store rest)
          exact ih store
      | erased =>
          change dupVals (Store.mapAddresses rename store) rest =
            mapStoreResult rename (dupVals store rest)
          exact ih store
      | loc location =>
          cases hbox : store.get? location with
          | none =>
              simp only [dupVals, List.foldlM_cons,
                Store.get?_mapAddresses, hbox, Option.map_none]
              change Except.error
                  (.mem s!"dup of a dead location {location}") =
                mapStoreResult rename
                  (Except.error (.mem s!"dup of a dead location {location}"))
              rfl
          | some box =>
              cases hworld : box.world with
              | unique =>
                  simp only [dupVals, List.foldlM_cons,
                    Store.get?_mapAddresses, hbox, Option.map_some,
                    NodeBox.mapAddresses_world, hworld]
                  change Except.error (.mem "dup of a unique node") =
                    mapStoreResult rename
                      (Except.error (.mem "dup of a unique node"))
                  rfl
              | shared =>
                  simp only [dupVals, List.foldlM_cons,
                    Store.get?_mapAddresses, hbox, Option.map_some,
                    NodeBox.mapAddresses_world, hworld]
                  let next :=
                    (store.setBox location
                      { box with rc := box.rc + 1 }).rcTick
                  have hnext :
                      ((Store.mapAddresses rename store).setBox location
                        { world := .shared
                          rc := (NodeBox.mapAddresses rename box).rc + 1
                          node := (NodeBox.mapAddresses rename box).node }).rcTick =
                        Store.mapAddresses rename next := by
                    simp [next, NodeBox.mapAddresses, hworld]
                  have hsourceNext :
                      (store.setBox location
                        { world := .shared
                          rc := box.rc + 1
                          node := box.node }).rcTick = next := by
                    simp [next, hworld]
                  rw [hnext]
                  rw [hsourceNext]
                  change dupVals (Store.mapAddresses rename next) rest =
                    mapStoreResult rename (dupVals next rest)
                  exact ih next

/-- The scalar-only oracle boundary commutes with a context renaming. -/
theorem callScalarOracle_mapAddresses
    {rename : Address → Address} {before after : Ctx}
    (contexts : Ctx.Renames rename before after)
    (function : Address) (arguments : List RVal) :
    callScalarOracle after (rename function) arguments =
      mapValueResult rename
        (callScalarOracle before function arguments) := by
  simp only [callScalarOracle, contexts.oracle function arguments]
  split
  · simp_all [mapValueResult, Err.mapAddresses]
  · cases horacle : before.oracle function arguments with
    | none => simp [mapValueResult, Err.mapAddresses]
    | some value =>
        by_cases hvalue : value.isScalar
        · simp [hvalue, mapValueResult]
        · simp [hvalue, mapValueResult, Err.mapAddresses]

/-! ## Fueled evaluator equivariance -/

/-- All mutually recursive evaluator entries commute with an address map at
one common fuel index.  Packaging them together mirrors the evaluator's
termination argument and lets every successor case consume the complete
strictly-smaller hypothesis. -/
structure EvalTransportAt (rename : Address → Address)
    (before after : Ctx) (fuel : Nat) : Prop where
  runCode : ∀ (current : FnDef) (store : Store)
      (environment : List RVal) (code : Code),
    runCode after fuel (FnDef.mapAddresses rename current)
        (Store.mapAddresses rename store) environment
        (Code.mapAddresses rename code) =
      mapRunResult rename
        (runCode before fuel current store environment code)
  runOp : ∀ (current : FnDef) (store : Store)
      (environment : List RVal) (operation : Op),
    runOp after fuel (FnDef.mapAddresses rename current)
        (Store.mapAddresses rename store) environment
        (Op.mapAddresses rename operation) =
      mapRunResult rename
        (runOp before fuel current store environment operation)
  invoke : ∀ (function : Address) (arguments : List RVal) (store : Store),
    IxIR1.invoke after fuel (rename function) arguments
        (Store.mapAddresses rename store) =
      mapRunResult rename
        (IxIR1.invoke before fuel function arguments store)
  applyGo : ∀ (store : Store) (function : RVal) (arguments : List RVal),
    IxIR1.applyGo after fuel (Store.mapAddresses rename store)
        function arguments =
      mapRunResult rename
        (IxIR1.applyGo before fuel store function arguments)
  dropVal : ∀ (store : Store) (value : RVal),
    IxIR1.dropVal after fuel (Store.mapAddresses rename store) value =
      mapStoreResult rename (IxIR1.dropVal before fuel store value)
  dropMany : ∀ (store : Store) (values : List RVal),
    IxIR1.dropMany after fuel (Store.mapAddresses rename store) values =
      mapStoreResult rename (IxIR1.dropMany before fuel store values)
  dropUVal : ∀ (store : Store) (value : RVal),
    IxIR1.dropUVal after fuel (Store.mapAddresses rename store) value =
      mapStoreResult rename (IxIR1.dropUVal before fuel store value)
  dropManyU : ∀ (store : Store) (values : List RVal),
    IxIR1.dropManyU after fuel (Store.mapAddresses rename store) values =
      mapStoreResult rename (IxIR1.dropManyU before fuel store values)

/-- Exact evaluator equivariance at every fuel. -/
theorem evalTransportAt {rename : Address → Address} {before after : Ctx}
    (contexts : Ctx.Renames rename before after) :
    ∀ fuel, EvalTransportAt rename before after fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [runCode, runOp, IxIR1.invoke, IxIR1.applyGo,
          IxIR1.dropVal, IxIR1.dropMany, IxIR1.dropUVal,
          IxIR1.dropManyU, mapRunResult, mapStoreResult,
          Err.mapAddresses]
  | succ fuel smaller =>
      refine {
        runCode := ?_
        runOp := ?_
        invoke := ?_
        applyGo := ?_
        dropVal := ?_
        dropMany := ?_
        dropUVal := ?_
        dropManyU := ?_ }
      · intro current store environment code
        cases code with
        | ret atom =>
            simp only [runCode, Code.mapAddresses]
            cases hresolve : resolveAtom environment atom with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment atom hresolve
                simp [mapRunResult, hmapped]
            | ok value => simp [mapRunResult]
        | letOp operation rest =>
            simp only [runCode, Code.mapAddresses]
            rw [smaller.runOp current store environment operation]
            cases hop : runOp before fuel current store environment operation with
            | error error =>
                change Except.error (Err.mapAddresses rename error) =
                  mapRunResult rename (Except.error error)
                rfl
            | ok out =>
                rcases out with ⟨next, value⟩
                simp only [mapRunResult]
                exact smaller.runCode current next (value :: environment) rest
        | case scrutinee peelNat alternatives =>
            simp only [runCode, Code.mapAddresses]
            cases hresolve : resolveAtom environment scrutinee with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment scrutinee hresolve
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | erased => simp [mapRunResult, Err.mapAddresses]
                | lit literal =>
                    cases literal with
                    | str string => simp [mapRunResult, Err.mapAddresses]
                    | nat number =>
                        cases peelNat with
                        | false => simp [mapRunResult, Err.mapAddresses]
                        | true =>
                            cases number with
                            | zero =>
                                simp only [except_ok_bind]
                                rw [AltArray.find?_mapAddresses rename 0
                                  alternatives]
                                cases halt : alternatives.find?
                                    (fun alternative =>
                                      alternative.cidx == 0) with
                                | none =>
                                    simp [mapRunResult,
                                      Err.mapAddresses]
                                | some alternative =>
                                    cases alternative with
                                    | mk constructor fields body =>
                                        cases fields with
                                        | zero =>
                                            simp only [Option.map_some,
                                              Alt.mapAddresses]
                                            exact smaller.runCode current store
                                              environment body
                                        | succ fields =>
                                            simp [Alt.mapAddresses,
                                              mapRunResult,
                                              Err.mapAddresses]
                            | succ predecessor =>
                                simp only [except_ok_bind]
                                rw [AltArray.find?_mapAddresses rename 1
                                  alternatives]
                                cases halt : alternatives.find?
                                    (fun alternative =>
                                      alternative.cidx == 1) with
                                | none =>
                                    simp [mapRunResult,
                                      Err.mapAddresses]
                                | some alternative =>
                                    cases alternative with
                                    | mk constructor fields body =>
                                        cases fields with
                                        | zero =>
                                            simp [Alt.mapAddresses,
                                              mapRunResult,
                                              Err.mapAddresses]
                                        | succ fields =>
                                            cases fields with
                                            | zero =>
                                                simp only [Option.map_some,
                                                  Alt.mapAddresses]
                                                exact smaller.runCode current
                                                  store
                                                  (.lit (.nat predecessor) ::
                                                    environment)
                                                  body
                                            | succ fields =>
                                                simp [Alt.mapAddresses,
                                                  mapRunResult,
                                                  Err.mapAddresses]
                | loc location =>
                    simp only [except_ok_bind]
                    cases hbox : store.get? location with
                    | none =>
                        simp [Store.get?_mapAddresses, hbox, mapRunResult,
                          Err.mapAddresses]
                    | some box =>
                        simp only [Store.get?_mapAddresses, hbox,
                          Option.map_some, NodeBox.mapAddresses_node]
                        cases hnode : box.node with
                        | papN function arity arguments =>
                            simp [Node.mapAddresses, mapRunResult,
                              Err.mapAddresses]
                        | ctorN constructor fields =>
                            simp only [Node.mapAddresses,
                              CtorId.mapAddresses]
                            rw [AltArray.find?_mapAddresses rename
                              constructor.cidx alternatives]
                            cases halt : alternatives.find?
                                (fun alternative =>
                                  alternative.cidx == constructor.cidx) with
                            | none =>
                                simp [mapRunResult, Err.mapAddresses]
                            | some alternative =>
                                cases alternative with
                                | mk alternativeConstructor fieldCount body =>
                                    simp only [Option.map_some,
                                      Alt.mapAddresses]
                                    by_cases hsize :
                                        fields.size != fieldCount
                                    · simp [hsize, mapRunResult,
                                        Err.mapAddresses]
                                    · simp only [hsize]
                                      exact smaller.runCode current store
                                        (fields.foldl
                                          (fun accumulated field =>
                                            field :: accumulated)
                                          environment)
                                        body
      · intro current store environment operation
        cases operation with
        | pure atom =>
            simp only [runOp, Op.mapAddresses]
            cases hresolve : resolveAtom environment atom with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment atom hresolve
                simp [mapRunResult, hmapped]
            | ok value => simp [mapRunResult]
        | alloc world constructor atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hresolve : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hresolve
                simp [mapRunResult, hmapped]
            | ok values =>
                change Except.ok
                    (((Store.mapAddresses rename store).allocNode world
                      (.ctorN (CtorId.mapAddresses rename constructor)
                        values.toArray)).1,
                      RVal.loc
                        (((Store.mapAddresses rename store).allocNode world
                          (.ctorN (CtorId.mapAddresses rename constructor)
                            values.toArray)).2)) =
                  Except.ok
                    (Store.mapAddresses rename
                      ((store.allocNode world
                        (.ctorN constructor values.toArray)).1),
                      RVal.loc
                        ((store.allocNode world
                          (.ctorN constructor values.toArray)).2))
                simp [Store.mapAddresses_allocNode_fst, Node.mapAddresses]
                exact
                  (Store.mapAddresses_allocNode_snd rename store world
                    (.ctorN constructor values.toArray)).symm
        | reuse target constructor atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hatoms : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hatoms
                simp [mapRunResult, hmapped]
            | ok values =>
                cases htarget : resolveAtom environment target with
                | error error =>
                    have hmapped := Err.mapAddresses_of_resolveAtom_error
                      rename environment target htarget
                    simp [mapRunResult, hmapped]
                | ok value =>
                    cases value with
                    | lit literal =>
                        simp [mapRunResult, Err.mapAddresses]
                    | erased =>
                        simp [mapRunResult, Err.mapAddresses]
                    | loc location =>
                        cases hbox : store.get? location with
                        | none =>
                            simp [Store.get?_mapAddresses, hbox, mapRunResult,
                              Err.mapAddresses]
                        | some box =>
                            cases hworld : box.world with
                            | shared =>
                                simp [Store.get?_mapAddresses, hbox, hworld,
                                  mapRunResult, Err.mapAddresses]
                            | unique =>
                                simp only [except_ok_bind,
                                  Store.get?_mapAddresses, hbox,
                                  Option.map_some, NodeBox.mapAddresses_world,
                                  hworld]
                                change Except.ok
                                    ({ ((Store.mapAddresses rename store).setBox
                                      location
                                      ⟨.unique, 1,
                                        .ctorN
                                          (CtorId.mapAddresses rename constructor)
                                          values.toArray⟩) with
                                      reuses :=
                                        ((Store.mapAddresses rename store).setBox
                                          location
                                          ⟨.unique, 1,
                                            .ctorN
                                              (CtorId.mapAddresses rename
                                                constructor)
                                              values.toArray⟩).reuses + 1 },
                                      RVal.loc location) =
                                  Except.ok
                                    (Store.mapAddresses rename
                                      { (store.setBox location
                                        ⟨.unique, 1,
                                          .ctorN constructor values.toArray⟩) with
                                        reuses :=
                                          (store.setBox location
                                            ⟨.unique, 1,
                                              .ctorN constructor
                                                values.toArray⟩).reuses + 1 },
                                      RVal.loc location)
                                simp [NodeBox.mapAddresses,
                                  Node.mapAddresses]
        | free target =>
            simp only [runOp, Op.mapAddresses]
            cases htarget : resolveAtom environment target with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment target htarget
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | lit literal => simp [mapRunResult, Err.mapAddresses]
                | erased => simp [mapRunResult, Err.mapAddresses]
                | loc location =>
                    cases hbox : store.get? location with
                    | none =>
                        simp [Store.get?_mapAddresses, hbox, mapRunResult,
                          Err.mapAddresses]
                    | some box =>
                        cases hworld : box.world with
                        | shared =>
                            simp [Store.get?_mapAddresses, hbox, hworld,
                              mapRunResult, Err.mapAddresses]
                        | unique =>
                            simp [Store.get?_mapAddresses, hbox, hworld,
                              mapRunResult]
        | dup target =>
            simp only [runOp, Op.mapAddresses]
            cases htarget : resolveAtom environment target with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment target htarget
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | lit literal => simp [mapRunResult]
                | erased => simp [mapRunResult]
                | loc location =>
                    cases hbox : store.get? location with
                    | none =>
                        simp [Store.get?_mapAddresses, hbox, mapRunResult,
                          Err.mapAddresses]
                    | some box =>
                        cases hworld : box.world with
                        | unique =>
                            simp [Store.get?_mapAddresses, hbox, hworld,
                              mapRunResult, Err.mapAddresses]
                        | shared =>
                            simp only [except_ok_bind,
                              Store.get?_mapAddresses, hbox,
                              Option.map_some, NodeBox.mapAddresses_world,
                              hworld]
                            simp [mapRunResult, NodeBox.mapAddresses, hworld]
        | drop target =>
            simp only [runOp, Op.mapAddresses]
            cases htarget : resolveAtom environment target with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment target htarget
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | lit literal => simp [mapRunResult]
                | erased => simp [mapRunResult]
                | loc location =>
                    simp only [except_ok_bind]
                    rw [smaller.dropVal store (.loc location)]
                    cases hdrop : IxIR1.dropVal before fuel store
                        (.loc location) with
                    | error error =>
                        change Except.error (Err.mapAddresses rename error) =
                          mapRunResult rename (Except.error error)
                        rfl
                    | ok next =>
                        change Except.ok
                            (Store.mapAddresses rename next, RVal.erased) =
                          mapRunResult rename
                            (Except.ok (next, RVal.erased))
                        rfl
        | dropU target =>
            simp only [runOp, Op.mapAddresses]
            cases htarget : resolveAtom environment target with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment target htarget
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | lit literal => simp [mapRunResult]
                | erased => simp [mapRunResult]
                | loc location =>
                    simp only [except_ok_bind]
                    rw [smaller.dropUVal store (.loc location)]
                    cases hdrop : IxIR1.dropUVal before fuel store
                        (.loc location) with
                    | error error =>
                        change Except.error (Err.mapAddresses rename error) =
                          mapRunResult rename (Except.error error)
                        rfl
                    | ok next =>
                        change Except.ok
                            (Store.mapAddresses rename next, RVal.erased) =
                          mapRunResult rename
                            (Except.ok (next, RVal.erased))
                        rfl
        | fetch target field =>
            simp only [runOp, Op.mapAddresses]
            cases htarget : resolveAtom environment target with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment target htarget
                simp [mapRunResult, hmapped]
            | ok value =>
                cases value with
                | lit literal => simp [mapRunResult, Err.mapAddresses]
                | erased => simp [mapRunResult, Err.mapAddresses]
                | loc location =>
                    simp only [except_ok_bind]
                    cases hbox : store.get? location with
                    | none =>
                        simp [Store.get?_mapAddresses, hbox, mapRunResult,
                          Err.mapAddresses]
                    | some box =>
                        simp only [Store.get?_mapAddresses, hbox,
                          Option.map_some, NodeBox.mapAddresses_node]
                        cases hnode : box.node with
                        | papN function arity arguments =>
                            simp [Node.mapAddresses, mapRunResult,
                              Err.mapAddresses]
                        | ctorN constructor fields =>
                            simp only [Node.mapAddresses]
                            cases hfield : fields[field]? with
                            | none =>
                                simp [mapRunResult, Err.mapAddresses]
                            | some value => simp [mapRunResult]
        | call function atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hresolve : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hresolve
                simp [mapRunResult, hmapped]
            | ok arguments =>
                exact smaller.invoke function arguments store
        | callSelf atoms =>
            simp only [runOp, Op.mapAddresses,
              FnDef.mapAddresses_arity, FnDef.mapAddresses_body,
              FnDef.mapAddresses_result]
            cases hresolve : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hresolve
                simp [mapRunResult, hmapped]
            | ok arguments =>
                simp only [except_ok_bind]
                by_cases harity : arguments.length != current.arity
                · simp [harity, mapRunResult, Err.mapAddresses]
                · simp only [harity]
                  rw [smaller.runCode current store arguments.reverse
                    current.body]
                  cases hrun : runCode before fuel current store
                      arguments.reverse current.body with
                  | error error =>
                      change Except.error (Err.mapAddresses rename error) =
                        mapRunResult rename (Except.error error)
                      rfl
                  | ok out =>
                      rcases out with ⟨resultStore, value⟩
                      simp only [mapRunResult]
                      exact checkResultWorld_mapAddresses rename current.result
                        (resultStore, value)
        | papp function atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hresolve : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hresolve
                simp [mapRunResult, hmapped]
            | ok arguments =>
                simp only [contexts.decls function]
                cases hdecl : before.decls function with
                | none =>
                    simp [mapRunResult, Err.mapAddresses]
                | some declaration =>
                    simp only [Option.map_some,
                      Decl.declArity_mapAddresses]
                    by_cases hless : arguments.length < declArity declaration
                    · simp only [except_ok_bind, hless]
                      change Except.ok
                          (((Store.mapAddresses rename store).allocNode .shared
                            (.papN (rename function)
                              (declArity declaration) arguments.toArray)).1,
                            RVal.loc
                              (((Store.mapAddresses rename store).allocNode
                                .shared (.papN (rename function)
                                  (declArity declaration)
                                  arguments.toArray)).2)) =
                        Except.ok
                          (Store.mapAddresses rename
                            ((store.allocNode .shared
                              (.papN function (declArity declaration)
                                arguments.toArray)).1),
                            RVal.loc
                              ((store.allocNode .shared
                                (.papN function (declArity declaration)
                                  arguments.toArray)).2))
                      simp [Store.mapAddresses_allocNode_fst,
                        Node.mapAddresses]
                      exact
                        (Store.mapAddresses_allocNode_snd rename store .shared
                          (.papN function (declArity declaration)
                            arguments.toArray)).symm
                    · simp [hless, mapRunResult, Err.mapAddresses]
        | apply function atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hfunction : resolveAtom environment function with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtom_error
                  rename environment function hfunction
                simp [mapRunResult, hmapped]
            | ok value =>
                cases harguments : resolveAtoms environment atoms with
                | error error =>
                    have hmapped := Err.mapAddresses_of_resolveAtoms_error
                      rename environment atoms harguments
                    simp [mapRunResult, hmapped]
                | ok arguments =>
                    simp only [except_ok_bind]
                    exact smaller.applyGo store value arguments
        | extern function atoms =>
            simp only [runOp, Op.mapAddresses]
            cases hresolve : resolveAtoms environment atoms with
            | error error =>
                have hmapped := Err.mapAddresses_of_resolveAtoms_error
                  rename environment atoms hresolve
                simp [mapRunResult, hmapped]
            | ok arguments =>
                simp only [except_ok_bind]
                rw [callScalarOracle_mapAddresses contexts]
                cases horacle : callScalarOracle before function arguments with
                | error error =>
                    change Except.error (Err.mapAddresses rename error) =
                      mapRunResult rename (Except.error error)
                    rfl
                | ok value =>
                    change Except.ok
                        (Store.mapAddresses rename store, value) =
                      mapRunResult rename (Except.ok (store, value))
                    rfl
      · intro function arguments store
        simp only [IxIR1.invoke, contexts.decls function]
        cases hdecl : before.decls function with
        | none =>
            simp [mapRunResult, Err.mapAddresses]
        | some declaration =>
            cases declaration with
            | extern arity =>
                simp only [Option.map_some, Decl.mapAddresses]
                by_cases harity : arguments.length != arity
                · simp [harity, mapRunResult, Err.mapAddresses]
                · simp only [harity]
                  rw [callScalarOracle_mapAddresses contexts]
                  cases horacle : callScalarOracle before function arguments with
                  | error error =>
                      simp [mapValueResult, mapRunResult]
                  | ok value =>
                      simp [mapValueResult, mapRunResult]
            | fn definition =>
                simp only [Option.map_some, Decl.mapAddresses]
                simp only [FnDef.mapAddresses_arity,
                  FnDef.mapAddresses_body, FnDef.mapAddresses_result]
                by_cases harity : arguments.length != definition.arity
                · simp [harity, mapRunResult, Err.mapAddresses]
                · simp only [harity]
                  rw [smaller.runCode definition store arguments.reverse
                    definition.body]
                  cases hrun : runCode before fuel definition store
                      arguments.reverse definition.body with
                  | error error =>
                      change Except.error (Err.mapAddresses rename error) =
                        mapRunResult rename (Except.error error)
                      rfl
                  | ok out =>
                      rcases out with ⟨resultStore, value⟩
                      simp only [mapRunResult]
                      exact checkResultWorld_mapAddresses rename
                        definition.result (resultStore, value)
      · intro store function arguments
        cases function with
        | lit literal =>
            simp [IxIR1.applyGo, mapRunResult, Err.mapAddresses]
        | erased =>
            simp only [IxIR1.applyGo]
            rw [smaller.dropMany store arguments]
            cases hdrop : IxIR1.dropMany before fuel store arguments with
            | error error =>
                change Except.error (Err.mapAddresses rename error) =
                  mapRunResult rename (Except.error error)
                rfl
            | ok next =>
                change Except.ok (Store.mapAddresses rename next, RVal.erased) =
                  mapRunResult rename (Except.ok (next, RVal.erased))
                rfl
        | loc location =>
            simp only [IxIR1.applyGo, Store.get?_mapAddresses]
            cases hbox : store.get? location with
            | none =>
                simp [mapRunResult, Err.mapAddresses]
            | some box =>
                simp only [Option.map_some,
                  NodeBox.mapAddresses_node]
                cases hnode : box.node with
                | ctorN constructor fields =>
                    simp [Node.mapAddresses, mapRunResult,
                      Err.mapAddresses]
                | papN called arity captured =>
                    simp only [Node.mapAddresses]
                    rw [dupVals_mapAddresses rename store captured.toList]
                    cases hdup : dupVals store captured.toList with
                    | error error =>
                        change Except.error (Err.mapAddresses rename error) =
                          mapRunResult rename (Except.error error)
                        rfl
                    | ok duplicated =>
                        simp only [mapStoreResult]
                        change (do
                            let dropped ← IxIR1.dropVal after fuel
                              (Store.mapAddresses rename duplicated)
                              (.loc location)
                            let total := captured.toList ++ arguments
                            if total.length < arity then
                              let (next, fresh) := dropped.allocNode .shared
                                (.papN (rename called) arity total.toArray)
                              .ok (next, .loc fresh)
                            else if total.length == arity then
                              match after.decls (rename called) with
                              | none => .error (.unknownRef (rename called))
                              | some declaration =>
                                if declPapSafe declaration then
                                  IxIR1.invoke after fuel (rename called)
                                    total dropped
                                else .error (.stuck
                                  "shared pap targets a non-pap-safe declaration")
                            else
                              match after.decls (rename called) with
                              | none => .error (.unknownRef (rename called))
                              | some declaration =>
                                if declPapSafe declaration then do
                                  let (next, value) ← IxIR1.invoke after fuel
                                    (rename called) (total.take arity) dropped
                                  IxIR1.applyGo after fuel next value
                                    (total.drop arity)
                                else .error (.stuck
                                  "shared pap targets a non-pap-safe declaration")) =
                          mapRunResult rename (do
                            let dropped ← IxIR1.dropVal before fuel duplicated
                              (.loc location)
                            let total := captured.toList ++ arguments
                            if total.length < arity then
                              let (next, fresh) := dropped.allocNode .shared
                                (.papN called arity total.toArray)
                              .ok (next, .loc fresh)
                            else if total.length == arity then
                              match before.decls called with
                              | none => .error (.unknownRef called)
                              | some declaration =>
                                if declPapSafe declaration then
                                  IxIR1.invoke before fuel called total dropped
                                else .error (.stuck
                                  "shared pap targets a non-pap-safe declaration")
                            else
                              match before.decls called with
                              | none => .error (.unknownRef called)
                              | some declaration =>
                                if declPapSafe declaration then do
                                  let (next, value) ← IxIR1.invoke before fuel
                                    called (total.take arity) dropped
                                  IxIR1.applyGo before fuel next value
                                    (total.drop arity)
                                else .error (.stuck
                                  "shared pap targets a non-pap-safe declaration"))
                        rw [smaller.dropVal duplicated (.loc location)]
                        cases hdrop : IxIR1.dropVal before fuel duplicated
                            (.loc location) with
                        | error error =>
                            change Except.error
                                (Err.mapAddresses rename error) =
                              mapRunResult rename (Except.error error)
                            rfl
                        | ok dropped =>
                            simp only [mapStoreResult]
                            let total := captured.toList ++ arguments
                            change (if total.length < arity then
                                let (next, fresh) :=
                                  (Store.mapAddresses rename dropped).allocNode
                                    .shared
                                    (.papN (rename called) arity total.toArray)
                                .ok (next, .loc fresh)
                              else if total.length == arity then
                                match after.decls (rename called) with
                                | none => .error (.unknownRef (rename called))
                                | some declaration =>
                                  if declPapSafe declaration then
                                    IxIR1.invoke after fuel (rename called)
                                      total (Store.mapAddresses rename dropped)
                                  else .error (.stuck
                                    "shared pap targets a non-pap-safe declaration")
                              else
                                match after.decls (rename called) with
                                | none => .error (.unknownRef (rename called))
                                | some declaration =>
                                  if declPapSafe declaration then do
                                    let (next, value) ← IxIR1.invoke after fuel
                                      (rename called) (total.take arity)
                                      (Store.mapAddresses rename dropped)
                                    IxIR1.applyGo after fuel next value
                                      (total.drop arity)
                                  else .error (.stuck
                                    "shared pap targets a non-pap-safe declaration")) =
                              mapRunResult rename
                                (if total.length < arity then
                                  let (next, fresh) := dropped.allocNode .shared
                                    (.papN called arity total.toArray)
                                  .ok (next, .loc fresh)
                                else if total.length == arity then
                                  match before.decls called with
                                  | none => .error (.unknownRef called)
                                  | some declaration =>
                                    if declPapSafe declaration then
                                      IxIR1.invoke before fuel called total dropped
                                    else .error (.stuck
                                      "shared pap targets a non-pap-safe declaration")
                                else
                                  match before.decls called with
                                  | none => .error (.unknownRef called)
                                  | some declaration =>
                                    if declPapSafe declaration then do
                                      let (next, value) ← IxIR1.invoke before fuel
                                        called (total.take arity) dropped
                                      IxIR1.applyGo before fuel next value
                                        (total.drop arity)
                                    else .error (.stuck
                                      "shared pap targets a non-pap-safe declaration"))
                            by_cases hless : total.length < arity
                            · simp only [hless]
                              change Except.ok
                                  (((Store.mapAddresses rename dropped).allocNode
                                    .shared (.papN (rename called) arity
                                      total.toArray)).1,
                                    RVal.loc
                                      (((Store.mapAddresses rename dropped).allocNode
                                        .shared (.papN (rename called) arity
                                          total.toArray)).2)) =
                                Except.ok
                                  (Store.mapAddresses rename
                                    ((dropped.allocNode .shared
                                      (.papN called arity total.toArray)).1),
                                    RVal.loc
                                      ((dropped.allocNode .shared
                                        (.papN called arity total.toArray)).2))
                              simp [Store.mapAddresses_allocNode_fst,
                                Node.mapAddresses]
                              exact
                                (Store.mapAddresses_allocNode_snd rename dropped
                                  .shared
                                  (.papN called arity total.toArray)).symm
                            · simp only [hless]
                              rw [contexts.decls called]
                              cases hdecl : before.decls called with
                              | none =>
                                  simp [hdecl, mapRunResult, Err.mapAddresses]
                              | some declaration =>
                                simp only [hdecl, Option.map_some,
                                  declPapSafe_mapAddresses]
                                cases hpapsafe : declPapSafe declaration with
                                | false =>
                                  simp [hpapsafe, mapRunResult,
                                    Err.mapAddresses]
                                | true =>
                                  simp only [hpapsafe, if_true]
                                  by_cases hequal : total.length == arity
                                  · simp only [hequal]
                                    exact smaller.invoke called total dropped
                                  · simp only [hequal]
                                    rw [smaller.invoke called (total.take arity)
                                      dropped]
                                    cases hinvoke : IxIR1.invoke before fuel
                                        called (total.take arity) dropped with
                                    | error error =>
                                        change Except.error
                                            (Err.mapAddresses rename error) =
                                          mapRunResult rename
                                            (Except.error error)
                                        rfl
                                    | ok out =>
                                        rcases out with ⟨calledStore, value⟩
                                        simp only [mapRunResult]
                                        exact smaller.applyGo calledStore value
                                          (total.drop arity)
      · intro store value
        cases value with
        | lit literal => simp [IxIR1.dropVal, mapStoreResult]
        | erased => simp [IxIR1.dropVal, mapStoreResult]
        | loc location =>
            simp only [IxIR1.dropVal, Store.get?_mapAddresses]
            cases hbox : store.get? location with
            | none =>
                simp [mapStoreResult, Err.mapAddresses]
            | some box =>
                simp only [Option.map_some,
                  NodeBox.mapAddresses_world]
                cases hworld : box.world with
                | unique =>
                    simp [mapStoreResult, Err.mapAddresses]
                | shared =>
                    simp only
                    by_cases hone : box.rc == 1
                    · simp only [hone, ↓reduceIte,
                        NodeBox.mapAddresses_rc]
                      cases hnode : box.node with
                      | ctorN constructor fields =>
                          simp only [hnode, NodeBox.mapAddresses_node,
                            Node.mapAddresses]
                          simpa only [Store.mapAddresses_rcTick,
                            Store.mapAddresses_kill] using
                            smaller.dropMany (store.rcTick.kill location)
                              fields.toList
                      | papN function arity arguments =>
                          simp only [hnode, NodeBox.mapAddresses_node,
                            Node.mapAddresses]
                          simpa only [Store.mapAddresses_rcTick,
                            Store.mapAddresses_kill] using
                            smaller.dropMany (store.rcTick.kill location)
                              arguments.toList
                    · simp only [hone, NodeBox.mapAddresses_rc]
                      simp [Bool.false_eq_true, mapStoreResult,
                        NodeBox.mapAddresses]
      · intro store values
        cases values with
        | nil => simp [IxIR1.dropMany, mapStoreResult]
        | cons value rest =>
            simp only [IxIR1.dropMany]
            rw [smaller.dropVal store value]
            cases hdrop : IxIR1.dropVal before fuel store value with
            | error error =>
                change Except.error (Err.mapAddresses rename error) =
                  mapStoreResult rename (Except.error error)
                rfl
            | ok next =>
                simp only [mapStoreResult]
                exact smaller.dropMany next rest
      · intro store value
        cases value with
        | lit literal => simp [IxIR1.dropUVal, mapStoreResult]
        | erased => simp [IxIR1.dropUVal, mapStoreResult]
        | loc location =>
            simp only [IxIR1.dropUVal, Store.get?_mapAddresses]
            cases hbox : store.get? location with
            | none =>
                simp [mapStoreResult, Err.mapAddresses]
            | some box =>
                simp only [Option.map_some,
                  NodeBox.mapAddresses_world]
                cases hworld : box.world with
                | shared =>
                    simp [mapStoreResult, Err.mapAddresses]
                | unique =>
                    simp only
                    cases hnode : box.node with
                    | ctorN constructor fields =>
                        simp only [hnode, NodeBox.mapAddresses_node,
                          Node.mapAddresses]
                        simpa only [Store.mapAddresses_kill] using
                          smaller.dropManyU (store.kill location)
                            fields.toList
                    | papN function arity arguments =>
                        simp [hnode, NodeBox.mapAddresses_node,
                          Node.mapAddresses, mapStoreResult,
                          Err.mapAddresses]
      · intro store values
        cases values with
        | nil => simp [IxIR1.dropManyU, mapStoreResult]
        | cons value rest =>
            simp only [IxIR1.dropManyU]
            rw [smaller.dropUVal store value]
            cases hdrop : IxIR1.dropUVal before fuel store value with
            | error error =>
                change Except.error (Err.mapAddresses rename error) =
                  mapStoreResult rename (Except.error error)
                rfl
            | ok next =>
                simp only [mapStoreResult]
                exact smaller.dropManyU next rest

/-! ## Public evaluator transport interface -/

/-- Code evaluation is equivariant under every context-compatible address
renaming.  This exposes the bundled mutual-induction result without requiring
clients to mention `EvalTransportAt`. -/
theorem runCode_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (fuel : Nat) (current : FnDef) (store : Store)
    (environment : List RVal) (code : Code) :
    runCode after fuel (FnDef.mapAddresses rename current)
        (Store.mapAddresses rename store) environment
        (Code.mapAddresses rename code) =
      mapRunResult rename
        (runCode before fuel current store environment code) :=
  (evalTransportAt contexts fuel).runCode current store environment code

/-- Single-operation evaluation is equivariant under every compatible
address renaming. -/
theorem runOp_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (fuel : Nat) (current : FnDef) (store : Store)
    (environment : List RVal) (operation : Op) :
    runOp after fuel (FnDef.mapAddresses rename current)
        (Store.mapAddresses rename store) environment
        (Op.mapAddresses rename operation) =
      mapRunResult rename
        (runOp before fuel current store environment operation) :=
  (evalTransportAt contexts fuel).runOp current store environment operation

/-- Known-function invocation is equivariant under a compatible address
renaming. -/
theorem invoke_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (fuel : Nat) (function : Address) (arguments : List RVal)
    (store : Store) :
    IxIR1.invoke after fuel (rename function) arguments
        (Store.mapAddresses rename store) =
      mapRunResult rename
        (IxIR1.invoke before fuel function arguments store) :=
  (evalTransportAt contexts fuel).invoke function arguments store

/-- Dynamic application is equivariant under every context-compatible
address renaming. Runtime values themselves need no mapping: declaration
identities occur only in the context and in heap-resident PAP nodes. -/
theorem applyGo_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (fuel : Nat) (store : Store) (function : RVal)
    (arguments : List RVal) :
    IxIR1.applyGo after fuel (Store.mapAddresses rename store)
        function arguments =
      mapRunResult rename
        (IxIR1.applyGo before fuel store function arguments) :=
  (evalTransportAt contexts fuel).applyGo store function arguments

/-- Successful reference-count duplication on a renamed heap reflects to the
original heap and preserves an exact heap preimage. -/
theorem dupVals_success_preimage {rename : Address → Address}
    {store store' : Store} {values : List RVal}
    (run : dupVals (Store.mapAddresses rename store) values = .ok store') :
    ∃ sourceStore',
      dupVals store values = .ok sourceStore' ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [dupVals_mapAddresses] at run
  cases sourceRun : dupVals store values with
  | error error => simp [sourceRun, mapStoreResult] at run
  | ok sourceStore' =>
      simp only [sourceRun, mapStoreResult, Except.ok.injEq] at run
      exact ⟨sourceStore', rfl, run.symm⟩

/-- Successful shared destruction on a renamed heap reflects to the original
context and preserves an exact heap preimage. -/
theorem dropVal_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {store store' : Store} {value : RVal}
    (run : IxIR1.dropVal after fuel (Store.mapAddresses rename store) value =
      .ok store') :
    ∃ sourceStore',
      IxIR1.dropVal before fuel store value = .ok sourceStore' ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [(evalTransportAt contexts fuel).dropVal] at run
  cases sourceRun : IxIR1.dropVal before fuel store value with
  | error error => simp [sourceRun, mapStoreResult] at run
  | ok sourceStore' =>
      simp only [sourceRun, mapStoreResult, Except.ok.injEq] at run
      exact ⟨sourceStore', rfl, run.symm⟩

/-- Successful destruction of a list of shared values on a renamed heap
reflects to the original context and preserves an exact heap preimage. -/
theorem dropMany_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {store store' : Store} {values : List RVal}
    (run : IxIR1.dropMany after fuel (Store.mapAddresses rename store) values =
      .ok store') :
    ∃ sourceStore',
      IxIR1.dropMany before fuel store values = .ok sourceStore' ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [(evalTransportAt contexts fuel).dropMany] at run
  cases sourceRun : IxIR1.dropMany before fuel store values with
  | error error => simp [sourceRun, mapStoreResult] at run
  | ok sourceStore' =>
      simp only [sourceRun, mapStoreResult, Except.ok.injEq] at run
      exact ⟨sourceStore', rfl, run.symm⟩

/-- A successful dynamic application on a renamed heap comes from a
successful application on the original heap. No injectivity or surjectivity
of the address map is needed because the input heap is already an exact image
and mapped errors cannot become successes. -/
theorem applyGo_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {store store' : Store} {function : RVal}
    {arguments : List RVal} {value : RVal}
    (run : IxIR1.applyGo after fuel (Store.mapAddresses rename store)
      function arguments = .ok (store', value)) :
    ∃ sourceStore',
      IxIR1.applyGo before fuel store function arguments =
          .ok (sourceStore', value) ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [applyGo_mapAddresses contexts] at run
  cases sourceRun : IxIR1.applyGo before fuel store function arguments with
  | error error => simp [sourceRun, mapRunResult] at run
  | ok output =>
      obtain ⟨sourceStore', sourceValue⟩ := output
      simp only [sourceRun, mapRunResult, Except.ok.injEq,
        Prod.mk.injEq] at run
      obtain ⟨storeEq, valueEq⟩ := run
      subst sourceValue
      exact ⟨sourceStore', rfl, storeEq.symm⟩

/-- Successful renamed code execution reflects to a successful source run
with the same runtime value and a heap preimage. -/
theorem runCode_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {current : FnDef} {store store' : Store}
    {environment : List RVal} {code : Code} {value : RVal}
    (run : runCode after fuel (FnDef.mapAddresses rename current)
      (Store.mapAddresses rename store) environment
      (Code.mapAddresses rename code) = .ok (store', value)) :
    ∃ sourceStore',
      runCode before fuel current store environment code =
          .ok (sourceStore', value) ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [runCode_mapAddresses contexts] at run
  cases sourceRun : runCode before fuel current store environment code with
  | error error => simp [sourceRun, mapRunResult] at run
  | ok output =>
      obtain ⟨sourceStore', sourceValue⟩ := output
      simp only [sourceRun, mapRunResult, Except.ok.injEq,
        Prod.mk.injEq] at run
      obtain ⟨storeEq, valueEq⟩ := run
      subst sourceValue
      exact ⟨sourceStore', rfl, storeEq.symm⟩

/-- Successful renamed operation execution reflects to a successful source
operation and a heap preimage. -/
theorem runOp_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {current : FnDef} {store store' : Store}
    {environment : List RVal} {operation : Op} {value : RVal}
    (run : runOp after fuel (FnDef.mapAddresses rename current)
      (Store.mapAddresses rename store) environment
      (Op.mapAddresses rename operation) = .ok (store', value)) :
    ∃ sourceStore',
      runOp before fuel current store environment operation =
          .ok (sourceStore', value) ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [runOp_mapAddresses contexts] at run
  cases sourceRun : runOp before fuel current store environment operation with
  | error error => simp [sourceRun, mapRunResult] at run
  | ok output =>
      obtain ⟨sourceStore', sourceValue⟩ := output
      simp only [sourceRun, mapRunResult, Except.ok.injEq,
        Prod.mk.injEq] at run
      obtain ⟨storeEq, valueEq⟩ := run
      subst sourceValue
      exact ⟨sourceStore', rfl, storeEq.symm⟩

/-- Successful invocation of a renamed declaration reflects to the original
declaration and produces a heap preimage. -/
theorem invoke_success_preimage {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    {fuel : Nat} {function : Address} {arguments : List RVal}
    {store store' : Store} {value : RVal}
    (run : IxIR1.invoke after fuel (rename function) arguments
      (Store.mapAddresses rename store) = .ok (store', value)) :
    ∃ sourceStore',
      IxIR1.invoke before fuel function arguments store =
          .ok (sourceStore', value) ∧
        store' = Store.mapAddresses rename sourceStore' := by
  rw [invoke_mapAddresses contexts] at run
  cases sourceRun : IxIR1.invoke before fuel function arguments store with
  | error error => simp [sourceRun, mapRunResult] at run
  | ok output =>
      obtain ⟨sourceStore', sourceValue⟩ := output
      simp only [sourceRun, mapRunResult, Except.ok.injEq,
        Prod.mk.injEq] at run
      obtain ⟨storeEq, valueEq⟩ := run
      subst sourceValue
      exact ⟨sourceStore', rfl, storeEq.symm⟩

/-- A fresh-store top-level run has exactly the renamed result, including
renamed errors and address-bearing heap nodes. -/
theorem runMain_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (code : Code) (fuel : Nat := 100000) :
    runMain after (Code.mapAddresses rename code) fuel =
      mapRunResult rename (runMain before code fuel) := by
  simpa [runMain, FnDef.mapAddresses] using
    (runCode_mapAddresses contexts fuel
      (⟨0, .shared, false, code⟩ : FnDef) ({} : Store) [] code)

/-- The concrete content-addressing pass preserves a top-level run exactly.
The source side uses the certified pre-address context: it agrees with every
raw lookup and adds only stable aliases for newly introduced content keys. -/
theorem runMain_of_run_eq_ok
    {source generated : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : Readdress.run source generated main = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      mapRunResult (Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx (source ++ generated) oracle)
          main fuel) := by
  have haudit := semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  exact runMain_mapAddresses
    (result.renames_preAddressCtx haudit oracle) main fuel

/-- Successful raw execution therefore produces the same runtime value,
the address-renamed heap, and identical instruction-level cost counters. -/
theorem runMain_success_of_run_eq_ok
    {source generated : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : Readdress.run source generated main = .ok result)
    (oracle : Address → List RVal → Option RVal)
    {fuel : Nat} {store : Store} {value : RVal}
    (hsource :
      runMain (result.preAddressCtx (source ++ generated) oracle) main fuel =
        .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main fuel =
      .ok (Store.mapAddresses (Renaming.apply result.addressMap) store,
        value) := by
  rw [runMain_of_run_eq_ok hrun oracle fuel, hsource]
  rfl

end Readdress

end Ix.Compiler.IxIR1
