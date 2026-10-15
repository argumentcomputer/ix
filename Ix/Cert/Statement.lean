import Ix.Cert.Compile
import Ix.LeanIngress.Theorems
import Ix.Ixon.Authenticated.Theorems
import IxC.Kernel.Ixon.Values

/-! # The certification statements, in terms of IxC

One checker, two front ends:

* **Source mode.** `Ix.CanonM` turns a Lean environment into an
  `Ix.Environment`, the compiler's input. `Ix.LeanIngress.checkSource` hands
  its constants, under Lean's own names, to IxC's verified fold
  `Ix.Kernel.Cached.checkDecls`, under the fixed Source role table (each
  role bound to its Lean name) with the evidence the environment's certificate
  theorems give (`Ix.LeanIngress.sourceEvidence`). IxC's model of the result
  is the source semantics.
* **Ixon mode.** The compiled artifact's records, as the bytes their
  addresses are computed over, go through the certified entry at BLAKE3,
  `Ixon.Authenticated.checkBytes`, with a role table's binding section (the
  default table, `Ix.Kernel.Admission.defaultBinding`, where a statement fixes
  one).

`compile` (`Ix.Cert.Compile`) relates them. Every statement is per root:
`checkSource` is all or nothing, and every real environment has `partial` or
`unsafe` constants, which decline, so a statement about a whole Init or
Mathlib would be vacuous. A statement is about the closure of a list of roots
under `DependsOn` (`IsClosure`), and on the Ixon side about the records that
the closure's published addresses reach (`CompiledReach`).

Statements (`def … : Prop`) and the theorems proved now:

* `SourceConsistent`, `IxonConsistent`: nothing either mode accepts has
  `False`'s role key as its type (for every role table, on the Ixon side) (`sourceConsistent`, `ixonConsistent`);
* `IxonAuthentic`: every accepted record and blob, and the role table's
  section, is stored under the pure BLAKE3 hash of its bytes (`ixonAuthentic`);
* `SourceValueSound`, `IxonValueSound`: every accepted environment has a
  value model (`sourceValueSound`, `ixonValueSound`). The Source statements
  hold for every grouping function, and so at the compiler's, `blocksOf`
  (`sourceConsistent_blocksOf`, `sourceValueSound_blocksOf`);
* `CompileCorrect`: if Source accepts a closure and no constant of it failed
  in the compiler's report (`NoFailure`, decidable), the compiler published
  the closure, Ixon accepts the compiled closure, and every value model of the
  compiled environment, read through `reading`, is one of the source's
  (`Commutes`). Stated, not proved;
* `CompileCovers`: the compiler publishes an input constant exactly when its
  report does not list it as failed. Proved (`compileCovers`), by
  construction: `compileReport` checks it and fails otherwise (CQ2.27). So
  `CompileCorrect` is equivalent to the same statement hypothesised on the
  artifact publishing the closure (`compileCorrect_iff_published`);
* `CompileAuthentic`: every record and blob `compile` returns is stored under
  the pure BLAKE3 hash of its bytes. Proved (`compileAuthentic`), by
  construction: `compileReport` re-hashes them with the admission hash and
  fails on a mismatch (CQ2.27);
* `ClosureCorrect`: the computed closure is the closure. Proved
  (`closureCorrect`, in `Ix.Cert.Closure`);
* `RenamingLemma`: the fold commutes with renaming a Source run's keys to
  compiled ones by `Key.map f`, for every `f` injective on the run's ids
  (`RenamingHyp`). Stated, not proved.

No reverse statement ("Ixon accepts, so Source accepts") is made: the two
modes' evidence differs (Ixon's comes with the table, Source's from the
certificate theorems in the checked environment, so a closure without them
declines `Nat.div`, `Nat.mod`, `Nat.shiftLeft` and their dependents in Source
only); and fuel can run out on either side alone.

The statements are frozen in `Ix.Cert.Audit`, and checked on fixtures in
`Tests.Ix.Cert.Statement`. -/

namespace Ix.Cert

open Ix.Kernel (Env Model Denotes SetTheory LevelParam BVarIdx ConstRef falseName)
open Ix.Kernel.Admission (Limits Records Binding)

universe w

/-! ## Source mode -/

/-- The constants `ci` refers to in the compiler's reference graph
(`Ix.graphConst`): the constants in its type and value, the structures it
projects from, an inductive's constructors, a constructor's inductive, and a
recursor's rule constructors and right-hand sides. -/
def refsOf (ci : Ix.ConstantInfo) : Ix.Set Ix.Name :=
  (Ix.GraphM.run { consts := {} } .init (Ix.graphConst ci)).1

/-- **The closure relation**: the constant `a` of `env` needs `b`. These are
the reference graph's edges and the edges the ingress's grouping needs
(`Ix.LeanIngress.groupsOf`): an inductive needs its whole block and every
recursor whose block starts at the same first member, and a recursor needs
its block. -/
def DependsOn (env : Ix.Environment) (a b : Ix.Name) : Prop :=
  ∃ ci, env.consts.get? a = some ci ∧
    ((refsOf ci).contains b = true ∨
      match ci with
      | .inductInfo v => v.all.contains b = true ∨ ∃ first rv, v.all[0]? = some first ∧
          env.consts.get? b = some (.recInfo rv) ∧ rv.all[0]? = some first
      | .recInfo rv => rv.all.contains b = true
      | _ => False)

/-- `n` is in the closure of `roots` in `env`. -/
inductive Reaches (env : Ix.Environment) (roots : List Ix.Name) : Ix.Name → Prop
  | root {n : Ix.Name} : roots.contains n = true → Reaches env roots n
  | step {a b : Ix.Name} : Reaches env roots a → DependsOn env a b → Reaches env roots b

/-- `sub` holds exactly the constants of `env` that `roots` reach. The
statements hold for every such `sub`, whatever the layout of its map. -/
def IsClosure (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) : Prop :=
  ∀ n, (Reaches env roots n → sub.consts.get? n = env.consts.get? n) ∧
    (¬ Reaches env roots n → sub.consts.get? n = none)

/-- **Source acceptance, per root**: Source mode accepts the closure `sub` of
`roots` in `env`, grouped by `condense sub`, and installs `envS`. The
grouping is a function of the environment, never a free input: the
compiler's is `blocksOf`. -/
def SourceAccepts (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment)
    (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source) : Prop :=
  IsClosure env roots sub ∧ Ix.LeanIngress.checkSource sub (condense sub) = .ok envS

/-- Structural equality of names. `Ix.Name`'s `==` compares the stored hashes
only, so two names with one hash field are `==` without being equal. -/
def nameEq : Ix.Name → Ix.Name → Bool
  | .anonymous h, .anonymous h' => h == h'
  | .str p s h, .str p' s' h' => h == h' && s == s' && nameEq p p'
  | .num p i h, .num p' i' h' => h == h' && i == i' && nameEq p p'
  | _, _ => false

/-- The recursors of `env`, each with the first member of the block it
eliminates, keyed by that member. -/
def recursorsByBlock (env : Ix.Environment) : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)) :=
  env.consts.fold (init := {}) fun m n ci =>
    match ci with
    | .recInfo rv =>
      match rv.all[0]? with
      | some first => m.insert first ((m.getD first #[]).push (first, n))
      | none => m
    | _ => m

/-- The names `DependsOn` relates a constant `ci` to. An inductive's
recursors are those whose block's first member is the inductive block's,
compared structurally (`nameEq`) as `DependsOn` compares them; the map's
lookup compares the hash fields only. -/
def dependencies (recursors : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)))
    (ci : Ix.ConstantInfo) : Array Ix.Name :=
  (refsOf ci).toArray ++
    match ci with
    | .inductInfo v =>
      v.all ++ match v.all[0]? with
        | some first => ((recursors.getD first #[]).filter (nameEq ·.1 first)).map (·.2)
        | none => #[]
    | .recInfo rv => rv.all
    | _ => #[]

/-- One step of the closure's worklist (a stack): take the top name; if it
is new and a constant of `env`, mark it and push the names it needs. -/
def closureStep (env : Ix.Environment) (recursors : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name))) :
    Ix.Set Ix.Name × List Ix.Name → (Ix.Set Ix.Name × List Ix.Name) ⊕ Ix.Set Ix.Name
  | (seen, []) => .inr seen
  | (seen, n :: todo) =>
    if seen.contains n then .inl (seen, todo)
    else match env.consts.get? n with
      | none => .inl (seen, todo)
      | some ci => .inl (seen.insert n, (dependencies recursors ci).toList ++ todo)

/-- The worklist run from a state to its end: the names marked. -/
def closureLoop (env : Ix.Environment) (s : Ix.Set Ix.Name × List Ix.Name) : Ix.Set Ix.Name :=
  Id.run (repeatM (fun s => pure (closureStep env (recursorsByBlock env) s)) s)

/-- The closure of `roots` in `env`, computed by a worklist. -/
def closure (env : Ix.Environment) (roots : List Ix.Name) : Ix.Environment :=
  let seen := closureLoop env (∅, roots)
  { consts := env.consts.filter fun n _ => seen.contains n }

/-- **The computed closure is the closure.** Proved (`Ix.Cert.closureCorrect`,
`Ix.Cert.Closure`). -/
def ClosureCorrect : Prop :=
  ∀ env roots, IsClosure env roots (closure env roots)

/-! ## Ixon mode -/

/-- The record stored at `a`, decoded. -/
def recordAt (ixe : Ixon.Env) (a : Address) : Option Ixon.Constant :=
  (ixe.consts.get? a).bind (·.get?)

/-- The record that a reference to the record `c` at `a` resolves to: a
projection's block, otherwise `a` itself
(`Benchmarks.Kernel.CheckIxeStep.owner`). -/
def ownerOf (a : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => a

/-- `b` is a record that the record at `a` needs: its block, if `a` is a
projection, or a record of its reference table. -/
def RecordEdge (ixe : Ixon.Env) (a b : Address) : Prop :=
  ∃ c, recordAt ixe a = some c ∧
    ((ownerOf a c = b ∧ b ≠ a) ∨ (c.refs.contains b = true ∧ ixe.consts.contains b = true))

/-- `a` is in the compiled closure of the seed addresses `S`. -/
inductive CompiledReach (ixe : Ixon.Env) (S : Address → Prop) : Address → Prop
  | seed {a : Address} : S a → ixe.consts.contains a = true → CompiledReach ixe S a
  | step {a b : Address} : CompiledReach ixe S a → RecordEdge ixe a b → CompiledReach ixe S b

/-- The record at `a` must follow `b`: a reference of `a` resolves to `b`,
another record. -/
def RecordRef (ixe : Ixon.Env) (a b : Address) : Prop :=
  ∃ c, recordAt ixe a = some c ∧
    ∃ r ∈ c.refs, ∃ cr, recordAt ixe r = some cr ∧ ownerOf r cr = b ∧ b ≠ a

/-- `order` lists the compiled closure of `S`, each record once, and no
record before one it references. The fold also needs edges the references
do not show (literal support, the `Nat` operations' certificate ground); an
accepting order respects those too. Locality, a later proof, makes the
verdict the same for every order that respects them all. -/
structure ClosureOrder (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) : Prop where
  nodup : order.Nodup
  complete : ∀ a, a ∈ order ↔ CompiledReach ixe S a
  ordered : order.Pairwise fun a b => ¬ RecordRef ixe a b

/-- The records at `order`, each with its stored bytes
(`Ixon.LazyConstant.rawBytes`, the bytes its address is computed over). -/
def recordsOf (ixe : Ixon.Env) (order : List Address) : Records :=
  order.filterMap fun a => (ixe.consts.get? a).map fun lc => (a, lc.rawBytes)

/-- The blobs the records at `order` reference. -/
def blobsOf (ixe : Ixon.Env) (order : List Address) : Ix.Kernel.Ingress.Blobs :=
  let used : Std.HashSet Address := order.foldl (init := {}) fun s a =>
    match recordAt ixe a with
    | some c => c.refs.foldl (·.insert ·) s
    | none => s
  ixe.blobs.toList.filter fun b => used.contains b.1

def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- The hints the artifact ships (`Ixon.Env.anonHints`, per address: for an
alias fiber, the merge of its names' hints), read at the address the
compiler registers them under: a definition block member's projection
record, otherwise the record. The environment check reads them the same way
(`Benchmarks.Kernel.CheckIxeStep.Hints`). -/
def hintsOf (ixe : Ixon.Env) : ConstRef Address → Option Ix.Kernel.ReducibilityHint :=
  let projAt : Std.HashMap (ConstRef Address) Address :=
    ixe.consts.fold (init := {}) fun m a lc =>
      match lc.get? with
      | some c =>
        match c.info with
        | .dPrj p => m.insert (.member p.block p.idx.toNat) a
        | _ => m
      | none => m
  fun r => hintOf <$> ixe.anonHints.get? ((projAt.get? r).getD r.block)

/-- **Ixon acceptance** of the compiled closure of `S`: the certified entry
at BLAKE3 accepts the role table `binding` and the records of `order` with
their stored bytes, the blobs they reference and the artifact's hints, and
installs `envA`. `limits` are resource bounds only. -/
def IxonAccepts (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop) (order : List Address)
    (envA : Env .anon) : Prop :=
  ClosureOrder ixe S order ∧
    Ixon.Authenticated.checkBytes binding limits (recordsOf ixe order) (blobsOf ixe order)
      (hintsOf ixe) = .ok envA

/-- The addresses the artifact publishes for the constants of `sub`
(`Ixon.Env.named`): the seeds of the compiled closure. -/
def Seed (ixe : Ixon.Env) (sub : Ix.Environment) (a : Address) : Prop :=
  ∃ n ci named, sub.consts.get? n = some ci ∧ ixe.named.get? n = some named ∧ named.addr = a

/-- The artifact publishes every constant of `sub`: the compiler compiled
the whole closure. A block that fails to compile is left out with its
dependents, and the compile still succeeds. -/
def Published (ixe : Ixon.Env) (sub : Ix.Environment) : Prop :=
  ∀ n ci, sub.consts.get? n = some ci → ∃ named, ixe.named.get? n = some named

/-! ### What the compile reports

`compileReport` returns, with the environment, every constant it left out
(`Failures`). The statements are hypothesised on that report: "no constant of
the closure failed" is decidable from the compile's own output, without
looking into the artifact. -/

/-- `Ix.Name`'s `==` compares the stored hashes, which are `Address`es, whose
`==` is equality: an equivalence, and `Hashable` hashes the stored hash. -/
theorem name_beq_iff {a b : Ix.Name} : (a == b) = true ↔ a.getHash = b.getHash :=
  Address.beq_iff_eq

instance : EquivBEq Ix.Name where
  rfl := name_beq_iff.mpr rfl
  symm h := name_beq_iff.mpr (name_beq_iff.mp h).symm
  trans h₁ h₂ := name_beq_iff.mpr ((name_beq_iff.mp h₁).trans (name_beq_iff.mp h₂))

instance : LawfulHashable Ix.Name where
  hash_eq a b h := by
    show hash a.getHash = hash b.getHash
    rw [name_beq_iff.mp h]

/-- **No constant of `sub` failed** in the compile that reported
`failures`. Decidable (`NoFailure.instDecidable`). -/
def NoFailure (failures : Failures) (sub : Ix.Environment) : Prop :=
  ∀ n ci, sub.consts.get? n = some ci → failures.failed n = false

theorem Failures.failed_congr (failures : Failures) {a b : Ix.Name} (h : (a == b) = true) :
    failures.failed a = failures.failed b := by
  unfold Failures.failed
  rw [Std.HashMap.contains_congr (m := failures.ungrounded) h,
    Std.HashMap.contains_congr (m := failures.blocks) h]

theorem noFailure_iff (failures : Failures) (sub : Ix.Environment) :
    NoFailure failures sub ↔ (sub.consts.keys.all fun n => !failures.failed n) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    have hc : sub.consts.contains k = true := by
      rw [← Std.HashMap.contains_keys]; exact List.elem_eq_true_of_mem hk
    rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hc
    obtain ⟨ci, hci⟩ := hc
    simp [h k ci hci]
  · intro h n ci hn
    have hc : sub.consts.keys.contains n = true := by
      rw [Std.HashMap.contains_keys, Std.HashMap.contains_eq_isSome_getElem?]
      exact Option.isSome_iff_exists.mpr ⟨ci, hn⟩
    obtain ⟨k, hk, hnk⟩ := List.contains_iff_exists_mem_beq.mp hc
    have := h k hk
    rw [failures.failed_congr hnk]
    simpa using this

instance NoFailure.instDecidable (failures : Failures) (sub : Ix.Environment) :
    Decidable (NoFailure failures sub) :=
  decidable_of_iff _ (noFailure_iff failures sub).symm

/-- **Coverage.** `compileReport` accounts for every input constant once:
it is published (`Ixon.Env.named`) exactly when it did not fail. The ground
filter records what it removes; the driver records every member of a block
that failed, including a refused claim or payload and a withdrawn promotion
(CQ2.3, CQ2.4, CQ2.6); and the readiness rule (CQ2.6) fails a block whose
dependency failed instead of leaving it unscheduled. A failed block publishes
nothing (CQ2.4b, CQ2.6). Proved (`compileCovers`): `compileReport` checks it
on its own result and fails otherwise (`checkReport`, CQ2.27), so it holds by
construction, whatever the driver's loop does. So `NoFailure` and
`Published` agree on every closure (`CompileCorrect.published`,
`CompileCorrect.of_published`, `compileCorrect_iff_published`). -/
def CompileCovers : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures),
    compileReport env = .ok (ixe, failures) → ∀ n ci, env.consts.get? n = some ci →
      ((∃ named, ixe.named.get? n = some named) ↔ failures.failed n = false)

/-! ## Value models

The public `Ix.Kernel.Model` constrains types only: a definition may denote
any inhabitant of its type. A value model also makes every stored definition
denote its value. That is what the fold's soundness proof provides
(`Ix.Kernel.Cached.checkDecls_model_defn_values`). Not covered: theorem and
opaque values (the fold records none), the definitional equalities of
inductive types (recursor rules, structure eta) and of the quotient (its
computation rule), and level-parameter irrelevance. -/

/-- A model of `env` in which every stored definition denotes its value. -/
structure ValueModel (V : Type w) [SetTheory V] (env : Env md) extends Model V env where
  defn_value : ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md)
      (hint : Ix.Kernel.ReducibilityHint), Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes cval env φ ρ value (cval cv.name φ)

/-! ## The reading τ -/

/-- The address the artifact publishes for the source key `k`: the entry of
`Ixon.Env.named` whose name the ingress keys `k` (`Ix.LeanIngress.ingressKey`). -/
def publishedAddress (ixe : Ixon.Env) (k : Ix.Kernel.Key .source) : Option Address :=
  (ixe.named.toList.find? fun (m, _) => Ix.LeanIngress.nameIs m k).map (·.2.addr)

/-- The reader's context of an Ixon run: the one `Ixon.Authenticated.checkBytes`
reads the decoded records against, under the admitted role table and its
prelude (`Ix.Kernel.Admission.checkBytes_reading`). -/
def admissionContext (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (order : List Address) : Option (Ix.Kernel.Reader.Ctx .anon) := do
  let t ← (Ix.Kernel.Admission.admitBinding Address.blake3Pure binding).toOption
  let pre ← (Ix.Kernel.Reader.preludeFor t).toOption
  let constants ← (Ix.Kernel.Admission.decodeRecords limits (recordsOf ixe order)).toOption
  pure (Ix.Kernel.Admission.streamContext Address.blake3Pure t pre constants (blobsOf ixe order)
    (hintsOf ixe))

/-- **The reading τ**: the compiled term the artifact reads the source
constant `c` as. That is the constant the reader keys `c`'s published
address by, applied to `c`'s own level parameters by position, so that
compiled parameter `i` is source parameter `i`. The key is the reader's
(`Ix.Kernel.Reader.Ctx.keyAt`): the role key where the table binds the
reference the address resolves to, otherwise the input key of the published
address itself.

Several source names can share an address (α-equal constants, one record).
They then read as the same constant, so a commuting source model gives them
one value (`Commutes.alias`). -/
def reading (ixe : Ixon.Env) (cx : Ix.Kernel.Reader.Ctx .anon) (c : Ix.Kernel.ConstantInfo .source) :
    Option (Ix.Kernel.Expr .anon) := do
  let a ← publishedAddress ixe c.name
  let k ← (cx.keyAt a).toOption
  pure (.const k (c.toConstantVal.levelParams.map .param))

/-! ## Commutation -/

/-- **Commutation.** Every value model of the compiled environment `envA`,
read through `τ`, is a value model of the source environment `envS`: there
is a value model of `envS` in which every source constant denotes what its
reading denotes in the compiled model. So everything the source entails,
including the value of each definition, holds of its compiled reading. -/
def Commutes (τ : Ix.Kernel.ConstantInfo .source → Option (Ix.Kernel.Expr .anon)) (envS : Env .source) (envA : Env .anon) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : ValueModel V envA), ∃ N : ValueModel V envS,
    ∀ c ∈ envS.consts, ∀ t, τ c = some t →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval envA φ ρ t (N.cval c.name φ)

/-- **The compiler's addresses are pure BLAKE3.** Every record of `compile`'s
output is stored under `Address.blake3Pure` of its stored bytes, and so is
every blob. The compiler computes every content address (record, projection,
blob) with `Address.admissionHash`, which is `Address.blake3Pure` in the logic
(`Address.admissionHash_eq`) and runs as the Rust BLAKE3, so this is a
property of `compile`, not an assumption that the two BLAKE3s agree. Proved
(`compileAuthentic`): `compileReport` re-hashes every record and blob of its
result with the admission hash and fails on any mismatch (`checkReport`,
CQ2.27), so it holds by construction. Its definitional steps
(`blockAddr_mk'`, `storedRecord_authentic`) say why the check passes. -/
def CompileAuthentic : Prop :=
  ∀ (env : Ix.Environment) (ixe : Ixon.Env), compile env = .ok ixe →
    (∀ a lc, ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
      ∀ a bytes, ixe.blobs.get? a = some bytes → a = Address.blake3Pure bytes

/-- A block result's address is pure BLAKE3 of its stored bytes. -/
theorem blockAddr_mk' (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta)
    (projections : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta)) :
    (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockAddr =
      Address.blake3Pure (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes :=
  rfl

/-- A record stored as the compiler's output stores it (`compileEnvAux`'s
`assembleEnv`: the bytes as their own buffer), under the admission hash of
those bytes, is at pure BLAKE3 of its stored bytes. -/
theorem storedRecord_authentic (bytes : ByteArray) :
    Address.admissionHash bytes =
      Address.blake3Pure ({ buf := bytes, len := bytes.size } : Ixon.LazyConstant).rawBytes := by
  simp [Address.admissionHash_eq, Ixon.LazyConstant.rawBytes]

/-- **The compiled closure is accepted and commutes**: Ixon accepts the
compiled closure of the addresses `ixe` publishes for `sub` under the default
role table, within some resource limits and in some order that respects its
references, and the compiled environment commutes with the source `envS`
through the reading. -/
def IxonCommutes (ixe : Ixon.Env) (sub : Ix.Environment) (envS : Env .source) : Prop :=
  ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
  ∃ limits order envA cx, IxonAccepts binding limits ixe (Seed ixe sub) order envA ∧
    admissionContext binding limits ixe order = some cx ∧
      Commutes.{w} (reading ixe cx) envS envA

/-- **Compiler correctness, forward, per root.** Suppose Source accepts the
closure `sub` of `roots` in `env`, grouped as the compiler groups it,
`compileReport env` returns `ixe` with `failures`, and no constant of `sub`
failed (`NoFailure`, decidable from the report). Then `ixe` publishes every
constant of `sub`, and the compiled closure is accepted and commutes with
the source (`IxonCommutes`).

This is partial correctness. A closure that Source rejects or declines, a
compile that fails, and a closure with a failed constant are outside the
statement. Under `CompileCovers`, which is proved (`compileCovers`), it is
the statement hypothesised on `Published` instead of `NoFailure`
(`CompileCorrect.published`, `CompileCorrect.of_published`,
`compileCorrect_iff_published`). -/
def CompileCorrect : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source)
    (ixe : Ixon.Env) (failures : Failures),
    SourceAccepts blocksOf env roots sub envS → compileReport env = .ok (ixe, failures) →
    NoFailure failures sub → Published ixe sub ∧ IxonCommutes.{w} ixe sub envS

/-- `compile` succeeds exactly when `compileReport` does, with its
environment. -/
theorem compile_eq_ok {env : Ix.Environment} {ixe : Ixon.Env} :
    compile env = .ok ixe ↔ ∃ failures, compileReport env = .ok (ixe, failures) := by
  unfold compile
  cases compileReport env with
  | error e =>
    show Except.error e = Except.ok ixe ↔ ∃ failures, Except.error e = Except.ok (ixe, failures)
    simp
  | ok p =>
    obtain ⟨a, f⟩ := p
    show Except.ok a = Except.ok ixe ↔ ∃ failures, Except.ok (a, f) = Except.ok (ixe, failures)
    constructor
    · intro h; cases h; exact ⟨f, rfl⟩
    · rintro ⟨_, h⟩; cases h; rfl

/-- A constant of a closure is a constant of the environment. -/
theorem IsClosure.mem_env {env sub : Ix.Environment} {roots : List Ix.Name}
    (h : IsClosure env roots sub) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : sub.consts.get? n = some ci) : env.consts.get? n = some ci := by
  by_cases hr : Reaches env roots n
  · rw [← (h n).1 hr]; exact hn
  · rw [(h n).2 hr] at hn; cases hn

/-- Under `CompileCovers`, `CompileCorrect` gives the statement hypothesised
on `Published`: the closure is published, so none of it failed. -/
theorem CompileCorrect.published (hcov : CompileCovers) (h : CompileCorrect.{w}) :
    ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source)
      (ixe : Ixon.Env), SourceAccepts blocksOf env roots sub envS → compile env = .ok ixe →
      Published ixe sub → IxonCommutes.{w} ixe sub envS := by
  intro env roots sub envS ixe hs hc hp
  obtain ⟨failures, hr⟩ := compile_eq_ok.mp hc
  refine (h env roots sub envS ixe failures hs hr fun n ci hn => ?_).2
  exact (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mp (hp n ci hn)

/-- Under `CompileCovers`, the statement hypothesised on `Published` gives
`CompileCorrect`: a closure none of whose constants failed is published. -/
theorem CompileCorrect.of_published (hcov : CompileCovers)
    (h : ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment)
      (envS : Env .source) (ixe : Ixon.Env), SourceAccepts blocksOf env roots sub envS →
      compile env = .ok ixe → Published ixe sub → IxonCommutes.{w} ixe sub envS) :
    CompileCorrect.{w} := by
  intro env roots sub envS ixe failures hs hr hf
  have hp : Published ixe sub := fun n ci hn =>
    (hcov env ixe failures hr n ci (hs.1.mem_env hn)).mpr (hf n ci hn)
  exact ⟨hp, h env roots sub envS ixe hs (compile_eq_ok.mpr ⟨failures, hr⟩) hp⟩

/-! ### Coverage and authenticity, by construction (CQ2.27)

`compileReport` checks its own result (`checkReport`) and fails on any
inconsistency, so both properties follow from the checks alone, with no
invariant of the driver's loop. -/

/-- `compileReport` succeeds only through its checks: its result is
`compileUnchecked`'s, and passes `checkReport`. -/
theorem compileReport_ok {env : Ix.Environment} {out : Ixon.Env × Failures}
    (h : compileReport env = .ok out) :
    compileUnchecked env = .ok out ∧ checkReport env out = .ok () := by
  have e : compileReport env = Except.bind (compileUnchecked env)
      (fun o => Except.bind (checkReport env o) fun _ => Except.ok o) := rfl
  rw [e] at h
  revert h
  cases compileUnchecked env with
  | error err => intro h; cases h
  | ok o =>
    intro h
    change Except.bind (checkReport env o) (fun _ => Except.ok o) = Except.ok out at h
    revert h
    cases hc : checkReport env o with
    | error err => intro h; cases h
    | ok u =>
      intro h
      cases u
      have ho : o = out := Except.ok.inj h
      subst ho
      exact ⟨rfl, hc⟩

/-- `checkReport` passes exactly when nothing is uncovered and nothing is
unauthentic. -/
theorem checkReport_ok {env : Ix.Environment} {out : Ixon.Env × Failures}
    (h : checkReport env out = .ok ()) :
    uncovered env out.1 out.2 = [] ∧ unauthentic out.1 = [] := by
  unfold checkReport at h
  revert h
  cases uncovered env out.1 out.2 <;> cases unauthentic out.1 <;> simp

/-- **Coverage, proved** (CQ2.27): `compileReport` publishes an input
constant exactly when it does not report it as failed. -/
theorem compileCovers : CompileCovers := by
  intro env ixe failures h n ci hn
  have hcov : uncovered env ixe failures = [] := (checkReport_ok (compileReport_ok h).2).1
  have hk : env.consts.keys.contains n = true := by
    rw [Std.HashMap.contains_keys, Std.HashMap.contains_eq_isSome_getElem?]
    exact Option.isSome_iff_exists.mpr ⟨ci, hn⟩
  obtain ⟨k, hk, hnk⟩ := List.contains_iff_exists_mem_beq.mp hk
  have hne : (ixe.named.contains k == failures.failed k) = false := by
    have := List.filter_eq_nil_iff.mp hcov k hk
    simpa using this
  rw [← failures.failed_congr hnk, ← Std.HashMap.contains_congr (m := ixe.named) hnk] at hne
  have hpub : (∃ named, ixe.named.get? n = some named) ↔ ixe.named.contains n = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
    rfl
  rw [hpub]
  revert hne
  cases ixe.named.contains n <;> cases failures.failed n <;> simp

/-- **Authenticity, proved** (CQ2.27): every record and blob `compile`
returns is stored under the pure BLAKE3 hash of its bytes. -/
theorem compileAuthentic : CompileAuthentic := by
  intro env ixe hc
  obtain ⟨failures, h⟩ := compile_eq_ok.mp hc
  have hu : unauthentic ixe = [] := (checkReport_ok (compileReport_ok h).2).2
  unfold unauthentic at hu
  obtain ⟨hr, hb⟩ := List.append_eq_nil_iff.mp hu
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hr hb
  refine ⟨fun a lc hlc => ?_, fun a bytes hblob => ?_⟩
  · have := hr (a, lc) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hlc)
    simpa [Address.admissionHash_eq] using this
  · have := hb (a, bytes) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hblob)
    simpa [Address.admissionHash_eq] using this

/-- **`CompileCorrect` on the report is `CompileCorrect` on the artifact**
(proved): with coverage proved, the statement hypothesised on `NoFailure`
and the one hypothesised on `Published` are equivalent. -/
theorem compileCorrect_iff_published : CompileCorrect.{w} ↔
    ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source)
      (ixe : Ixon.Env), SourceAccepts blocksOf env roots sub envS → compile env = .ok ixe →
      Published ixe sub → IxonCommutes.{w} ixe sub envS :=
  ⟨CompileCorrect.published compileCovers, CompileCorrect.of_published compileCovers⟩

/-! ## The theorems that hold now -/

/-- **Source consistency, per root**: under every grouping function, nothing
Source accepts has `False`'s role key as its type. -/
def SourceConsistent : Prop :=
  ∀ (condense : Ix.Environment → Ix.CondensedBlocks) (V : Type w) [SetTheory V]
    (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source),
    SourceAccepts condense env roots sub envS →
      ∀ ci ∈ envS.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Ixon consistency**: under every role table, nothing Ixon accepts has
`False`'s role key as its type. -/
def IxonConsistent : Prop :=
  ∀ (V : Type w) [SetTheory V] (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon), IxonAccepts binding limits ixe S order envA →
      ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Authenticity**: every record Ixon accepts is stored under the pure
BLAKE3 hash of its bytes, and so is every blob and the role table's section. -/
def IxonAuthentic : Prop :=
  ∀ (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon),
    IxonAccepts binding limits ixe S order envA →
      (∀ a ∈ order, ∀ lc, ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
        (∀ b ∈ blobsOf ixe order, b.1 = Address.blake3Pure b.2) ∧
        Address.blake3Pure binding.bytes = binding.address

/-- **Source value soundness**: every environment Source accepts has a value
model. -/
def SourceValueSound : Prop :=
  ∀ (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment) (roots : List Ix.Name)
    (sub : Ix.Environment) (envS : Env .source), SourceAccepts condense env roots sub envS →
      ∀ (V : Type w) [SetTheory V], Nonempty (ValueModel V envS)

/-- **Ixon value soundness**: every environment Ixon accepts has a value
model, under every role table, so `Commutes` is not vacuous. -/
def IxonValueSound : Prop :=
  ∀ (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon),
    IxonAccepts binding limits ixe S order envA → ∀ (V : Type w) [SetTheory V], Nonempty (ValueModel V envA)

theorem sourceConsistent : SourceConsistent.{w} := by
  intro _ V _ _ _ _ _ h
  exact Ix.LeanIngress.checkSource_no_proof_of_False V h.2

theorem ixonConsistent : IxonConsistent.{w} := by
  intro V _ _ _ _ _ _ _ h
  exact Ixon.Authenticated.checkBytes_no_proof_of_False V h.2

theorem ixonAuthentic : IxonAuthentic := by
  intro _ _ ixe _ order _ h
  obtain ⟨ha, hb⟩ := Ixon.Authenticated.checkBytes_authentic h.2
  refine ⟨fun a hmem lc hlc => ?_, fun b hmem => ha.2 b hmem, hb⟩
  exact ha.1 (a, lc.rawBytes) (List.mem_filterMap.mpr ⟨a, hmem, by simp only [hlc, Option.map_some]⟩)

theorem sourceValueSound : SourceValueSound.{w} := by
  intro _ _ _ _ envS h V _
  obtain ⟨_, _, _, _, hc⟩ := Ix.LeanIngress.checkSource_reading h.2
  obtain ⟨M, hM⟩ := Ix.Kernel.Cached.checkDecls_model_defn_values V _ _ envS hc
  exact ⟨{ M with defn_value := hM }⟩

theorem ixonValueSound : IxonValueSound.{w} := by
  intro _ _ _ _ _ _ h V _
  obtain ⟨M, hM⟩ := Ix.Kernel.Admission.checkBytes_has_model_values (hash := Address.blake3Pure) V h.2
  exact ⟨{ M with defn_value := hM }⟩

/-! The Source theorems hold for every grouping function, which is stronger
than for the compiler's. At the compiler's own grouping, `blocksOf` (the one
`CompileCorrect` names), they stand on the three standard axioms as well:
`blocksOf` is total (CQ1.15) and reaches no `native_decide` axiom (CQ1.2,
CQ2.1), which was the reason the statements quantify over the grouping. -/

/-- `sourceConsistent` at the compiler's grouping, `blocksOf`. -/
theorem sourceConsistent_blocksOf (V : Type w) [SetTheory V] (env : Ix.Environment)
    (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source)
    (h : SourceAccepts blocksOf env roots sub envS) :
    ∀ ci ∈ envS.consts, ci.toConstantVal.type = .const falseName [] → False :=
  sourceConsistent blocksOf V env roots sub envS h

/-- `sourceValueSound` at the compiler's grouping, `blocksOf`. -/
theorem sourceValueSound_blocksOf (env : Ix.Environment) (roots : List Ix.Name)
    (sub : Ix.Environment) (envS : Env .source) (h : SourceAccepts blocksOf env roots sub envS)
    (V : Type w) [SetTheory V] : Nonempty (ValueModel V envS) :=
  sourceValueSound blocksOf env roots sub envS h V

/-- **Aliases collapse.** Source constants that read as the same compiled
term get one value in the commuting source model. -/
theorem Commutes.alias {τ : Ix.Kernel.ConstantInfo .source → Option (Ix.Kernel.Expr .anon)} {envS : Env .source} {envA : Env .anon}
    (h : Commutes.{w} τ envS envA) (V : Type w) [SetTheory V] (M : ValueModel V envA) :
    ∃ N : ValueModel V envS,
      (∀ c ∈ envS.consts, ∀ t, τ c = some t →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval envA φ ρ t (N.cval c.name φ)) ∧
      ∀ c₁ ∈ envS.consts, ∀ c₂ ∈ envS.consts, ∀ t, τ c₁ = some t → τ c₂ = some t →
        ∀ φ : LevelParam → Nat, N.cval c₁.name φ = N.cval c₂.name φ := by
  obtain ⟨N, hN⟩ := h V M
  refine ⟨N, hN, fun c₁ h₁ c₂ h₂ t e₁ e₂ φ => ?_⟩
  let ρ : BVarIdx → V := fun _ => SetTheory.univChain 0
  exact Ix.Kernel.Denotes_functional (hN c₁ h₁ t e₁ φ ρ) (hN c₂ h₂ t e₂ φ ρ)

/-! ## The renaming lemma

IXC-PLAN §12 and SP3-PARAMETRICITY §9: the fold commutes with renaming the
input keys, up to error messages. The bridge from Source to Ixon renames a
source key to a compiled one by `Key.map f`, `f` taking a Lean name to the
address the artifact publishes for it; it applies the lemma after an
alias-collapse step, because that map is not injective. -/

namespace Rename

variable (σ : Ix.Kernel.Key md → Ix.Kernel.Key md')

def expr : Ix.Kernel.Expr md → Ix.Kernel.Expr md'
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (expr t)
  | .sort u => .sort u
  | .const n us => .const (σ n) us
  | .app f a => .app (expr f) (expr a)
  | .lam t b m => .lam (expr t) (expr b) m
  | .forallE t b m => .forallE (expr t) (expr b) m
  | .letE t v b l => .letE (expr t) (expr v) (expr b) l
  | .lit l => .lit l
  | .proj n i e => .proj (σ n) i (expr e)

def constantVal (cv : Ix.Kernel.ConstantVal md) : Ix.Kernel.ConstantVal md' :=
  { name := σ cv.name, levelParams := cv.levelParams, type := expr σ cv.type }

def recRuleFire : Ix.Kernel.RecRuleFire md → Ix.Kernel.RecRuleFire md'
  | .inert => .inert
  | .plain => .plain
  | .nested lvls pins => .nested lvls (pins.map (expr σ))

def recRule (r : Ix.Kernel.RecRule md) : Ix.Kernel.RecRule md' :=
  { ctor := σ r.ctor, nfields := r.nfields, ctorParams := r.ctorParams,
    fire := recRuleFire σ r.fire, rhs := expr σ r.rhs, k := r.k, eta := r.eta,
    paramsBlind := r.paramsBlind }

def indCaps (c : Ix.Kernel.IndCaps md) : Ix.Kernel.IndCaps md' :=
  { eta := c.eta, etaCtor := c.etaCtor.map σ, etaParams := c.etaParams,
    etaFields := c.etaFields, unitlike := c.unitlike, unitParams := c.unitParams,
    ruleK := c.ruleK, sortZ := c.sortZ }

def projTable (t : Ix.Kernel.ProjTable md) : Ix.Kernel.ProjTable md' :=
  { structName := σ t.structName, levelParams := t.levelParams, numParams := t.numParams,
    ctor := σ t.ctor, numFields := t.numFields, structSort := t.structSort,
    bodies := t.bodies.map (expr σ), guards := t.guards, off := t.off }

def constantInfo : Ix.Kernel.ConstantInfo md → Ix.Kernel.ConstantInfo md'
  | .axiomInfo v => .axiomInfo (constantVal σ v)
  | .defnInfo v e h => .defnInfo (constantVal σ v) (expr σ e) h
  | .thmInfo v e => .thmInfo (constantVal σ v) (expr σ e)
  | .indInfo v caps => .indInfo (constantVal σ v) (indCaps σ caps)
  | .ctorInfo v nP nF => .ctorInfo (constantVal σ v) nP nF
  | .recInfo v major pre rules => .recInfo (constantVal σ v) major pre (rules.map (recRule σ))
  | .projInfo tbl => .projInfo (projTable σ tbl)

def declaration : Ix.Kernel.Declaration md → Ix.Kernel.Declaration md'
  | .axiomDecl v => .axiomDecl (constantVal σ v)
  | .defnDecl v e h => .defnDecl (constantVal σ v) (expr σ e) h
  | .thmDecl v e => .thmDecl (constantVal σ v) (expr σ e)
  | .opaqueDecl v e => .opaqueDecl (constantVal σ v) (expr σ e)
  | .basisDecl k => .basisDecl k
  | .indDecl block nP => .indDecl (block.map (constantInfo σ)) nP
  | .quotDecl k v => .quotDecl k (constantVal σ v)

/-- An evidence entry: a proof's theorem key and its proof term. -/
def evidence : Ix.Kernel.Evidence (Ix.Kernel.Key md × Ix.Kernel.Expr md) →
    Ix.Kernel.Evidence (Ix.Kernel.Key md' × Ix.Kernel.Expr md')
  | .defeq => .defeq
  | .proof (k, v) => .proof (σ k, expr σ v)

/-- The fold's evidence: roles are fixed, their entries renamed. -/
def evidences (ev : Ix.Kernel.Evidences md) : Ix.Kernel.Evidences md' :=
  ev.map fun (r, es) => (r, es.map (evidence σ))

def env (e : Env md) : Env md' := ⟨e.consts.map (constantInfo σ)⟩

end Rename

/-! The constant keys a term, constant or declaration contains: the input
keys of a run. -/

namespace Keys

def expr : Ix.Kernel.Expr md → List (Ix.Kernel.Key md)
  | .fvar _ t => expr t
  | .const n _ => [n]
  | .app f a => expr f ++ expr a
  | .lam t b _ => expr t ++ expr b
  | .forallE t b _ => expr t ++ expr b
  | .letE t v b _ => expr t ++ expr v ++ expr b
  | .proj n _ e => n :: expr e
  | _ => []

def constantVal (cv : Ix.Kernel.ConstantVal md) : List (Ix.Kernel.Key md) :=
  cv.name :: expr cv.type

def recRule (r : Ix.Kernel.RecRule md) : List (Ix.Kernel.Key md) :=
  r.ctor :: expr r.rhs ++ match r.fire with
    | .nested _ pins => pins.flatMap expr
    | _ => []

def constantInfo : Ix.Kernel.ConstantInfo md → List (Ix.Kernel.Key md)
  | .axiomInfo v => constantVal v
  | .defnInfo v e _ => constantVal v ++ expr e
  | .thmInfo v e => constantVal v ++ expr e
  | .indInfo v caps => constantVal v ++ caps.etaCtor.toList
  | .ctorInfo v _ _ => constantVal v
  | .recInfo v _ _ rules => constantVal v ++ rules.flatMap recRule
  | .projInfo tbl => tbl.structName :: tbl.ctor :: tbl.bodies.toList.flatMap expr

def declaration : Ix.Kernel.Declaration md → List (Ix.Kernel.Key md)
  | .axiomDecl v => constantVal v
  | .defnDecl v e _ => constantVal v ++ expr e
  | .thmDecl v e => constantVal v ++ expr e
  | .opaqueDecl v e => constantVal v ++ expr e
  | .basisDecl _ => []
  | .indDecl block _ => block.flatMap constantInfo
  | .quotDecl _ v => constantVal v

def evidences (ev : Ix.Kernel.Evidences md) : List (Ix.Kernel.Key md) :=
  ev.flatMap fun (_, es) => es.flatMap fun
    | .defeq => []
    | .proof (k, v) => k :: expr v

end Keys

/-- `n` is a key of the declarations `ds` or of the evidence `ev`. -/
def InputKey (ev : Ix.Kernel.Evidences md) (ds : Array (Ix.Kernel.Declaration md))
    (n : Ix.Kernel.Key md) : Prop :=
  (∃ d ∈ ds, n ∈ Keys.declaration d) ∨ n ∈ Keys.evidences ev

/-- The input ids a key names: its own, or its base's for a derived key. -/
def keyIds : Ix.Kernel.Key md → List md.Id
  | .id i => [i]
  | .role _ => []
  | .aux k _ => keyIds k

/-- `i` is an id a key of the declarations `ds` or of the evidence `ev` (the
role table's data) names. -/
def InputId (ev : Ix.Kernel.Evidences md) (ds : Array (Ix.Kernel.Declaration md))
    (i : md.Id) : Prop :=
  ∃ k, InputKey ev ds k ∧ i ∈ keyIds k

/-- **The renaming lemma's hypothesis** (IXC-PLAN §12): `f` is injective on
the input's ids. The renaming is `Key.map f`, so the role keys are fixed, a
derived key is renamed through its base and an input key stays an input key,
by construction: SP3 §9's other hypotheses (pinned keys fixed, no input key
renamed to a pinned one, derived keys commuting with the renaming, the front
door's shape tests unchanged) hold of every such renaming. -/
def RenamingHyp (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon)
    (ev : Ix.Kernel.Evidences .source) (ds : Array (Ix.Kernel.Declaration .source)) : Prop :=
  ∀ i j, InputId ev ds i → InputId ev ds j → f i = f j → i = j

/-- What a fold failure says without its message: `CheckError` carries
strings that spell names, so until structured errors (IXC-PLAN step 6) the
lemma compares the kind and the position only. -/
inductive ErrorKind where
  | notImplemented
  | invalid
  | internal
  deriving DecidableEq, Repr

def ErrorKind.of : Ix.Kernel.CheckError → ErrorKind
  | .notImplemented _ => .notImplemented
  | .invalid _ => .invalid
  | .internal _ => .internal

/-- A fold's verdict up to error messages. -/
def verdict : Except (Ix.Kernel.CheckError × Nat) (Env md) → Except (ErrorKind × Nat) (Env md)
  | .ok e => .ok e
  | .error (e, i) => .error (ErrorKind.of e, i)

/-- **The renaming lemma.** Stated, not proved: renaming a Source run's keys
to compiled ones by `Key.map f`, `f` injective on the run's ids, renames the
fold's verdict. -/
def RenamingLemma : Prop :=
  ∀ (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (ev : Ix.Kernel.Evidences .source)
    (ds : Array (Ix.Kernel.Declaration .source)), RenamingHyp f ev ds →
      verdict (Ix.Kernel.Cached.checkDecls .verified (Rename.evidences (Ix.Kernel.Key.map f) ev)
          (ds.map (Rename.declaration (Ix.Kernel.Key.map f)))) =
        (verdict (Ix.Kernel.Cached.checkDecls .verified ev ds)).map
          (Rename.env (Ix.Kernel.Key.map f))

end Ix.Cert
