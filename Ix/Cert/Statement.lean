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
  value model (`sourceValueSound`, `ixonValueSound`);
* `CompileCorrect`: if Source accepts a closure and the compiler compiled it,
  Ixon accepts the compiled closure, and every value model of the compiled
  environment, read through `reading`, is one of the source's (`Commutes`).
  Stated, not proved;
* `ClosureCorrect`: the computed closure is the closure. Stated, not proved;
* `RenamingLemma`: the fold commutes with a renaming of constant names that
  satisfies `RenamingHyp`. Stated, not proved.

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
    (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env) : Prop :=
  IsClosure env roots sub ∧ Ix.LeanIngress.checkSource sub (condense sub) = .ok envS

/-- The recursors of `env`, by the first member of the block they eliminate. -/
def recursorsByBlock (env : Ix.Environment) : Ix.Map Ix.Name (Array Ix.Name) :=
  env.consts.fold (init := {}) fun m n ci =>
    match ci with
    | .recInfo rv =>
      match rv.all[0]? with
      | some first => m.insert first ((m.getD first #[]).push n)
      | none => m
    | _ => m

/-- The names `DependsOn` relates a constant `ci` to. -/
def dependencies (recursors : Ix.Map Ix.Name (Array Ix.Name)) (ci : Ix.ConstantInfo) :
    Array Ix.Name :=
  (refsOf ci).toArray ++
    match ci with
    | .inductInfo v =>
      v.all ++ match v.all[0]? with
        | some first => recursors.getD first #[]
        | none => #[]
    | .recInfo rv => rv.all
    | _ => #[]

/-- The closure of `roots` in `env`, computed by a worklist. -/
def closure (env : Ix.Environment) (roots : List Ix.Name) : Ix.Environment := Id.run do
  let recursors := recursorsByBlock env
  let mut seen : Ix.Set Ix.Name := {}
  let mut todo : Array Ix.Name := roots.toArray
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    match env.consts.get? n with
    | none => continue
    | some ci =>
      seen := seen.insert n
      todo := todo ++ dependencies recursors ci
  return { consts := env.consts.filter fun n _ => seen.contains n }

/-- **The computed closure is the closure.** Stated, not proved. -/
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
    (envA : Env) : Prop :=
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

/-! ## Value models

The public `Ix.Kernel.Model` constrains types only: a definition may denote
any inhabitant of its type. A value model also makes every stored definition
denote its value. That is what the fold's soundness proof provides
(`Ix.Kernel.Cached.checkDecls_model_defn_values`). Not covered: theorem and
opaque values (the fold records none), the definitional equalities of
inductive types (recursor rules, structure eta) and of the quotient (its
computation rule), and level-parameter irrelevance. -/

/-- A model of `env` in which every stored definition denotes its value. -/
structure ValueModel (V : Type w) [SetTheory V] (env : Env) extends Model V env where
  defn_value : ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr)
      (hint : Ix.Kernel.ReducibilityHint), Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes cval env φ ρ value (cval cv.name φ)

/-! ## The reading τ -/

/-- The address the artifact publishes for the source name `n`: the entry of
`Ixon.Env.named` whose name the ingress spells `n`
(`Ix.LeanIngress.ingressName`). -/
def publishedAddress (ixe : Ixon.Env) (n : Ix.Kernel.Name) : Option Address :=
  (ixe.named.toList.find? fun (m, _) => Ix.LeanIngress.nameIs m n).map (·.2.addr)

/-- The reader's context of an Ixon run: the one `Ixon.Authenticated.checkBytes`
reads the decoded records against, under the admitted role table and its
prelude (`Ix.Kernel.Admission.checkBytes_reading`). -/
def admissionContext (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (order : List Address) : Option Ix.Kernel.Reader.Ctx := do
  let t ← (Ix.Kernel.Admission.admitBinding Address.blake3Pure binding).toOption
  let pre ← (Ix.Kernel.Reader.preludeFor t).toOption
  let constants ← (Ix.Kernel.Admission.decodeRecords limits (recordsOf ixe order)).toOption
  pure (Ix.Kernel.Admission.streamContext t pre constants (blobsOf ixe order) (hintsOf ixe))

/-- **The reading τ**: the compiled term the artifact reads the source
constant `c` as. That is the constant the reader keys `c`'s published
address by, applied to `c`'s own level parameters by position, so that
compiled parameter `i` is source parameter `i`. Today the key is the
reader's name: `ix.<hex>.i` (`Ix.Kernel.Reader.keyName`) through `resolve`,
a role key the table binds, or a recursor's name after its block. Under `Key m` (IXC-PLAN
step 5) the key is the published address itself, and this is the one
definition that changes.

Several source names can share an address (α-equal constants, one record).
They then read as the same constant, so a commuting source model gives them
one value (`Commutes.alias`). -/
def reading (ixe : Ixon.Env) (cx : Ix.Kernel.Reader.Ctx) (c : Ix.Kernel.ConstantInfo) :
    Option Ix.Kernel.Expr := do
  let a ← publishedAddress ixe c.name
  let r ← Ix.Kernel.Reader.resolve cx.store a
  pure (.const (cx.nameOf r) (c.toConstantVal.levelParams.map .param))

/-! ## Commutation -/

/-- **Commutation.** Every value model of the compiled environment `envA`,
read through `τ`, is a value model of the source environment `envS`: there
is a value model of `envS` in which every source constant denotes what its
reading denotes in the compiled model. So everything the source entails,
including the value of each definition, holds of its compiled reading. -/
def Commutes (τ : Ix.Kernel.ConstantInfo → Option Ix.Kernel.Expr) (envS envA : Env) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : ValueModel V envA), ∃ N : ValueModel V envS,
    ∀ c ∈ envS.consts, ∀ t, τ c = some t →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval envA φ ρ t (N.cval c.name φ)

/-- The compiler's hash is pure BLAKE3. The compiler addresses records with
the Rust BLAKE3 (`Address.blake3`), and the entry authenticates them with
pure BLAKE3. Like the admission hash's substitution
(`Address.admissionHash`), this is an assumption, checked on fixtures
(`Tests.Ix.Kernel.AddressPure`). -/
def HashAgreement : Prop :=
  ∀ bytes, Address.blake3 bytes = Address.blake3Pure bytes

/-- **Compiler correctness, forward, per root.** Suppose Source accepts the
closure `sub` of `roots` in `env`, grouped as the compiler groups it,
`compile env` returns `ixe`, and `ixe` publishes every constant of `sub`.
Then Ixon accepts the compiled closure under the default role table, within
some resource limits and in some order that respects its references, and the
compiled environment commutes with the source through the reading.

This is partial correctness. A closure that Source rejects or declines, a
compile that fails, and constants the compile leaves out are outside the
statement. -/
def CompileCorrect : Prop :=
  HashAgreement →
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env)
    (ixe : Ixon.Env),
    SourceAccepts blocksOf env roots sub envS → compile env = .ok ixe → Published ixe sub →
    ∃ binding, Ix.Kernel.Admission.defaultBinding = .ok binding ∧
    ∃ limits order envA cx, IxonAccepts binding limits ixe (Seed ixe sub) order envA ∧
      admissionContext binding limits ixe order = some cx ∧
        Commutes.{w} (reading ixe cx) envS envA

/-! ## The theorems that hold now -/

/-- **Source consistency, per root**: under every grouping function, nothing
Source accepts has `False`'s role key as its type. -/
def SourceConsistent : Prop :=
  ∀ (condense : Ix.Environment → Ix.CondensedBlocks) (V : Type w) [SetTheory V]
    (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env),
    SourceAccepts condense env roots sub envS →
      ∀ ci ∈ envS.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Ixon consistency**: under every role table, nothing Ixon accepts has
`False`'s role key as its type. -/
def IxonConsistent : Prop :=
  ∀ (V : Type w) [SetTheory V] (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env), IxonAccepts binding limits ixe S order envA →
      ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Authenticity**: every record Ixon accepts is stored under the pure
BLAKE3 hash of its bytes, and so is every blob and the role table's section. -/
def IxonAuthentic : Prop :=
  ∀ (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env),
    IxonAccepts binding limits ixe S order envA →
      (∀ a ∈ order, ∀ lc, ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
        (∀ b ∈ blobsOf ixe order, b.1 = Address.blake3Pure b.2) ∧
        Address.blake3Pure binding.bytes = binding.address

/-- **Source value soundness**: every environment Source accepts has a value
model. -/
def SourceValueSound : Prop :=
  ∀ (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment) (roots : List Ix.Name)
    (sub : Ix.Environment) (envS : Env), SourceAccepts condense env roots sub envS →
      ∀ (V : Type w) [SetTheory V], Nonempty (ValueModel V envS)

/-- **Ixon value soundness**: every environment Ixon accepts has a value
model, under every role table, so `Commutes` is not vacuous. -/
def IxonValueSound : Prop :=
  ∀ (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env),
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

/-- **Aliases collapse.** Source constants that read as the same compiled
term get one value in the commuting source model. -/
theorem Commutes.alias {τ : Ix.Kernel.ConstantInfo → Option Ix.Kernel.Expr} {envS envA : Env}
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

IXC-PLAN §12 and SP3-PARAMETRICITY §9, over today's `Name`-keyed fold: the
fold commutes with a renaming `σ` of constant names, up to error messages.
The bridge from Source to Ixon applies it after an alias-collapse step,
because the real map from source names to compiled keys is not injective. -/

namespace Rename

variable (σ : Ix.Kernel.Name → Ix.Kernel.Name)

def expr : Ix.Kernel.Expr → Ix.Kernel.Expr
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (expr t)
  | .sort u => .sort u
  | .const n us => .const (σ n) us
  | .app f a => .app (expr f) (expr a)
  | .lam t b m => .lam (expr t) (expr b) m
  | .forallE t b m => .forallE (expr t) (expr b) m
  | .letE t v b => .letE (expr t) (expr v) (expr b)
  | .lit l => .lit l
  | .proj n i e => .proj (σ n) i (expr e)

def constantVal (cv : Ix.Kernel.ConstantVal) : Ix.Kernel.ConstantVal :=
  { cv with name := σ cv.name, type := expr σ cv.type }

def recRule (r : Ix.Kernel.RecRule) : Ix.Kernel.RecRule :=
  { r with
    ctor := σ r.ctor
    rhs := expr σ r.rhs
    fire := match r.fire with
      | .nested lvls pins => .nested lvls (pins.map (expr σ))
      | f => f }

def constantInfo : Ix.Kernel.ConstantInfo → Ix.Kernel.ConstantInfo
  | .axiomInfo v => .axiomInfo (constantVal σ v)
  | .defnInfo v e h => .defnInfo (constantVal σ v) (expr σ e) h
  | .thmInfo v e => .thmInfo (constantVal σ v) (expr σ e)
  | .indInfo v caps => .indInfo (constantVal σ v) { caps with etaCtor := caps.etaCtor.map σ }
  | .ctorInfo v nP nF => .ctorInfo (constantVal σ v) nP nF
  | .recInfo v major pre rules => .recInfo (constantVal σ v) major pre (rules.map (recRule σ))
  | .projInfo tbl => .projInfo { tbl with
      structName := σ tbl.structName
      ctor := σ tbl.ctor
      bodies := tbl.bodies.map (expr σ) }

def declaration : Ix.Kernel.Declaration → Ix.Kernel.Declaration
  | .axiomDecl v => .axiomDecl (constantVal σ v)
  | .defnDecl v e h => .defnDecl (constantVal σ v) (expr σ e) h
  | .thmDecl v e => .thmDecl (constantVal σ v) (expr σ e)
  | .opaqueDecl v e => .opaqueDecl (constantVal σ v) (expr σ e)
  | .basisDecl k => .basisDecl k
  | .indDecl block nP => .indDecl (block.map (constantInfo σ)) nP
  | .quotDecl k v => .quotDecl k (constantVal σ v)

/-- An evidence entry: a proof's theorem key and its proof term. -/
def evidence : Ix.Kernel.Evidence (Ix.Kernel.Name × Ix.Kernel.Expr) →
    Ix.Kernel.Evidence (Ix.Kernel.Name × Ix.Kernel.Expr)
  | .defeq => .defeq
  | .proof (k, v) => .proof (σ k, expr σ v)

/-- The fold's evidence: roles are fixed, their entries renamed. -/
def evidences (ev : Ix.Kernel.Evidences) : Ix.Kernel.Evidences :=
  ev.map fun (r, es) => (r, es.map (evidence σ))

def env (e : Env) : Env := ⟨e.consts.map (constantInfo σ)⟩

end Rename

/-! The constant names a term, constant or declaration contains: the input
keys of a run. -/

namespace Keys

def expr : Ix.Kernel.Expr → List Ix.Kernel.Name
  | .fvar _ t => expr t
  | .const n _ => [n]
  | .app f a => expr f ++ expr a
  | .lam t b _ => expr t ++ expr b
  | .forallE t b _ => expr t ++ expr b
  | .letE t v b => expr t ++ expr v ++ expr b
  | .proj n _ e => n :: expr e
  | _ => []

def constantVal (cv : Ix.Kernel.ConstantVal) : List Ix.Kernel.Name :=
  cv.name :: expr cv.type

def recRule (r : Ix.Kernel.RecRule) : List Ix.Kernel.Name :=
  r.ctor :: expr r.rhs ++ match r.fire with
    | .nested _ pins => pins.flatMap expr
    | _ => []

def constantInfo : Ix.Kernel.ConstantInfo → List Ix.Kernel.Name
  | .axiomInfo v => constantVal v
  | .defnInfo v e _ => constantVal v ++ expr e
  | .thmInfo v e => constantVal v ++ expr e
  | .indInfo v caps => constantVal v ++ caps.etaCtor.toList
  | .ctorInfo v _ _ => constantVal v
  | .recInfo v _ _ rules => constantVal v ++ rules.flatMap recRule
  | .projInfo tbl => tbl.structName :: tbl.ctor :: tbl.bodies.toList.flatMap expr

def declaration : Ix.Kernel.Declaration → List Ix.Kernel.Name
  | .axiomDecl v => constantVal v
  | .defnDecl v e _ => constantVal v ++ expr e
  | .thmDecl v e => constantVal v ++ expr e
  | .opaqueDecl v e => constantVal v ++ expr e
  | .basisDecl _ => []
  | .indDecl block _ => block.flatMap constantInfo
  | .quotDecl _ v => constantVal v

def evidences (ev : Ix.Kernel.Evidences) : List Ix.Kernel.Name :=
  ev.flatMap fun (_, es) => es.flatMap fun
    | .defeq => []
    | .proof (k, v) => k :: expr v

end Keys

/-- `n` is a key of the declarations `ds` or of the evidence `ev`. -/
def InputKey (ev : Ix.Kernel.Evidences) (ds : Array Ix.Kernel.Declaration)
    (n : Ix.Kernel.Name) : Prop :=
  (∃ d ∈ ds, n ∈ Keys.declaration d) ∨ n ∈ Keys.evidences ev

/-- The checker's fixed names: the basis blocks' and the role keys (every
role's, bound or not: the specification set mentions them). -/
def Pinned (n : Ix.Kernel.Name) : Prop :=
  n ∈ Ix.Kernel.reservedBasisNames ∨ ∃ r : Ix.Kernel.Role, Ix.Kernel.roleKey r = n

/-- `n` is `k` followed by components, the first a string: the shape of
every name the checker derives from `k` (`k._model…`, `k.proj.i`,
`k.projTable.0`, `k._model._impl…`, `k.rec`). -/
inductive DerivedFrom (k : Ix.Kernel.Name) : Ix.Kernel.Name → Prop
  | str (s : String) : DerivedFrom k (.str k s)
  | extStr {n : Ix.Kernel.Name} (s : String) : DerivedFrom k n → DerivedFrom k (.str n s)
  | extNum {n : Ix.Kernel.Name} (i : Nat) : DerivedFrom k n → DerivedFrom k (.num n i)

/-- The names a run can look up or install: the input keys, the pinned
names, and the names derived from either. -/
def Built (ev : Ix.Kernel.Evidences) (ds : Array Ix.Kernel.Declaration)
    (n : Ix.Kernel.Name) : Prop :=
  ∃ k, (InputKey ev ds k ∨ Pinned k) ∧ (n = k ∨ DerivedFrom k n)

/-- **The renaming lemma's hypotheses** on today's names (SP3 §9, H1–H8).

The derived-name condition (`str`, `num`, `anonymous`) makes `σ` the
extension of its values on the input keys along name components, so `σ`
commutes with every derivation the checker makes. `recursor` and `shapes`
cover the sites that read the structure of input names (SP3 D1 and D5).
Under `Key m` (IXC-PLAN step 5) this reduces to `σ = Key.map f` with `f`
injective on the input ids: roles are fixed and derived keys commute by
construction, and recursors have keys of their own. -/
structure RenamingHyp (σ : Ix.Kernel.Name → Ix.Kernel.Name) (ev : Ix.Kernel.Evidences)
    (ds : Array Ix.Kernel.Declaration) : Prop where
  /-- the fixed names are fixed -/
  pinned : ∀ n, Pinned n → σ n = n
  /-- no other input key is renamed to a fixed name -/
  fresh : ∀ k, InputKey ev ds k → ¬ Pinned k → ¬ Pinned (σ k)
  /-- off the input keys, `σ` commutes with appending a component -/
  str : ∀ p s, ¬ InputKey ev ds (.str p s) → σ (.str p s) = .str (σ p) s
  num : ∀ p i, ¬ InputKey ev ds (.num p i) → σ (.num p i) = .num (σ p) i
  /-- the `etaCtor` sentinel (SP3 D10) -/
  anonymous : σ .anonymous = .anonymous
  /-- an input recursor `T.rec`, `T.rec_j` is renamed after `T`: the checker
  finds a block's recursor by that spelling (SP3 D1) -/
  recursor : ∀ p s, InputKey ev ds (.str p s) → (s = "rec" ∨ s.startsWith "rec_" = true) →
    σ (.str p s) = .str (σ p) s
  /-- the front door's shape tests give the same answers (SP3 D5) -/
  shapes : ∀ k, InputKey ev ds k →
    Ix.Kernel.Key.isProjFnShape (σ k) = Ix.Kernel.Key.isProjFnShape k ∧
      Ix.Kernel.Key.isModelSuffix (σ k) = Ix.Kernel.Key.isModelSuffix k
  /-- `σ` is injective on the names a run can build -/
  injective : ∀ a b, Built ev ds a → Built ev ds b → σ a = σ b → a = b

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
def verdict : Except (Ix.Kernel.CheckError × Nat) Env → Except (ErrorKind × Nat) Env
  | .ok e => .ok e
  | .error (e, i) => .error (ErrorKind.of e, i)

/-- **The renaming lemma.** Stated, not proved. -/
def RenamingLemma : Prop :=
  ∀ (σ : Ix.Kernel.Name → Ix.Kernel.Name) (ev : Ix.Kernel.Evidences)
    (ds : Array Ix.Kernel.Declaration), RenamingHyp σ ev ds →
      verdict (Ix.Kernel.Cached.checkDecls .verified (Rename.evidences σ ev)
          (ds.map (Rename.declaration σ))) =
        (verdict (Ix.Kernel.Cached.checkDecls .verified ev ds)).map (Rename.env σ)

end Ix.Cert
