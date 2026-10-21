import Ix.Cert.Compile
import Ix.LeanIngress.Theorems
import Ix.Ixon.Authenticated.Theorems
import IxC.Kernel.Ixon.Values
import Ix.Cert.SourceBundled
import Ix.CompileCert.Canon.Ref

/-! # The certification statements, in terms of IxC

One checker, two front ends:

* **Source mode.** `Ix.CanonM` turns a Lean environment into an
  `Ix.Environment`, the compiler's input. `Ix.LeanIngress.checkSourceBundled`
  hands its constants, under Lean's own names, to IxC's verified fold
  `Ix.Kernel.Cached.checkDecls`, under the fixed Source role table (each
  role bound to its Lean name) with the committed bundle's evidence
  (`Ix.RoleEvidence.bundleEvidence`, RoleData's `sourceEvidence`; owner,
  2026-10-20), whatever the input carries. IxC's model of the result
  is the source semantics.
* **Ixon mode.** The compiled artifact's records, as the bytes their
  addresses are computed over, go through the certified entry at BLAKE3,
  `Ixon.Authenticated.checkBytes`, with a role table's binding section (the
  default table, `Ix.Kernel.Admission.defaultBinding`, where a statement fixes
  one).

`compile` (`Ix.Cert.Compile`) relates them. Every statement is per root:
the Source check is all or nothing, and every real environment has `partial` or
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

/-- Whether a term has a `String` literal. -/
def hasStrLit : Ix.Expr → Bool
  | .lit (.strVal _) _ => true
  | .app f a _ => hasStrLit f || hasStrLit a
  | .lam _ t b _ _ | .forallE _ t b _ _ => hasStrLit t || hasStrLit b
  | .letE _ t v b _ _ => hasStrLit t || hasStrLit v || hasStrLit b
  | .mdata _ e _ | .proj _ _ e _ => hasStrLit e
  | _ => false

/-- Whether a term has a `Nat` literal. -/
def hasNatLit : Ix.Expr → Bool
  | .lit (.natVal _) _ => true
  | .app f a _ => hasNatLit f || hasNatLit a
  | .lam _ t b _ _ | .forallE _ t b _ _ => hasNatLit t || hasNatLit b
  | .letE _ t v b _ _ => hasNatLit t || hasNatLit v || hasNatLit b
  | .mdata _ e _ | .proj _ _ e _ => hasNatLit e
  | _ => false

/-- A constant's terms: its type, its value, its recursor rules' right-hand sides. -/
def termsOf : Ix.ConstantInfo → List Ix.Expr
  | .defnInfo v => [v.cnst.type, v.value]
  | .thmInfo v => [v.cnst.type, v.value]
  | .opaqueInfo v => [v.cnst.type, v.value]
  | .recInfo v => v.cnst.type :: v.rules.toList.map (·.rhs)
  | ci => [ci.getCnst.type]

/-- The Lean names of IxC's literal support (`Ix.Kernel.Reader.strLitSupportNames`,
`natLitSupportNames`): the constants it checks a literal against. -/
def supportNames (keys : List (Ix.Kernel.Key .source)) : Array Ix.Name :=
  keys.toArray.map fun k => Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName k)

/-- **The constants a constant's literals depend on** (owner, 2026-10-20): a
`String` literal references no constant, but IxC checks it against `String`,
`String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat` and the `Nat`
basis (`Expr.constsResolve`), and a `Nat` literal against the `Nat` basis. -/
def literalSupport (ci : Ix.ConstantInfo) : Array Ix.Name :=
  if (termsOf ci).any hasStrLit then supportNames Ix.Kernel.Reader.strLitSupportNames
  else if (termsOf ci).any hasNatLit then supportNames Ix.Kernel.Reader.natLitSupportNames
  else #[]

/-- **The closure relation**: the constant `a` of `env` needs `b`. These are
the reference graph's edges, the constants its literals are checked against
(`literalSupport`), and the edges the ingress's grouping needs
(`Ix.LeanIngress.groupsOf`): an inductive needs its whole block and every
recursor whose block starts at the same first member, and a recursor needs
its block. -/
def DependsOn (env : Ix.Environment) (a b : Ix.Name) : Prop :=
  ∃ ci, env.consts.get? a = some ci ∧
    ((refsOf ci).contains b = true ∨ (literalSupport ci).contains b = true ∨
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
  IsClosure env roots sub ∧ Ix.LeanIngress.checkSourceBundled sub (condense sub) = .ok envS

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
  (refsOf ci).toArray ++ literalSupport ci ++
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

/-- A record stored as the compiler's output stores it (`compileEnvFold`'s
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
`compileUnchecked`'s environment and failures, and passes `checkReport`
against the driver's resolution map and aux map that `compileUnchecked`
returns with them. -/
theorem compileReport_ok {env : Ix.Environment} {out : Ixon.Env × Failures}
    (h : compileReport env = .ok out) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (out.1, out.2, cenv) ∧
      checkReport env cenv out = .ok () := by
  have e : compileReport env = Except.bind (compileUnchecked env)
      (fun o => Except.bind (checkReport env o.2.2 (o.1, o.2.1)) fun _ =>
        Except.ok (o.1, o.2.1)) :=
    rfl
  rw [e] at h
  revert h
  cases compileUnchecked env with
  | error err => intro h; cases h
  | ok o =>
    obtain ⟨ixe, failures, cenv⟩ := o
    intro h
    change Except.bind (checkReport env cenv (ixe, failures))
      (fun _ => Except.ok (ixe, failures)) = Except.ok out at h
    revert h
    cases hc : checkReport env cenv (ixe, failures) with
    | error err => intro h; cases h
    | ok u =>
      intro h
      cases u
      have ho : (ixe, failures) = out := Except.ok.inj h
      subst ho
      exact ⟨cenv, rfl, hc⟩

/-- `checkReport` passes exactly when nothing is uncovered, nothing is
unauthentic, no stored record is on a reference cycle, no two different
names share a name hash, every `Muts` entry agrees with its block, every
resolved name is published where it resolves, every published input
inductive's component is seen, every input name of the aux map is published
with an original-form record, every published input name is resolved or in the
aux map, no resolved name outside the aux map is a cross-SCC claim, every Pass 3
head is in the changed set, all in the driver's final environment `cenv`, and
every input constant carries the name it is stored under. -/
theorem checkReport_ok {env : Ix.Environment} {cenv : Ix.CompileM.CompileEnv} {out : Ixon.Env × Failures}
    (h : checkReport env cenv out = .ok ()) :
    uncovered env out.1 out.2 = [] ∧ unauthentic out.1 = [] ∧ referenceCycle out.1 = none ∧
      nameHashCollision env out.1 = none ∧ mutsMismatch out.1 = none ∧
      resolutionMismatch cenv.nameToAddr out.1 = none ∧ unseenInductive env out.1 = none ∧
      unoriginalAux env cenv.auxNameToAddr out.1 = none ∧
      unresolvedPublished env cenv.nameToAddr cenv.auxNameToAddr out.1 = none ∧
      crossClaimed env cenv.nameToAddr cenv.auxNameToAddr cenv.auxGenExtraNames = none ∧
      foreignHead env cenv.p3Heads out.1 = none ∧ misnamedInput env = none ∧
      strayConstructor env = none := by
  unfold checkReport at h
  -- walk the checks in order: every failing branch is an error, so the one
  -- branch that returns has each check's equation in context
  repeat' (first | (split at h) | (focus (cases h; done)))
  exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- The checks `compileReport`'s result passed that read only the result
(`checkReport_ok`'s first five). -/
theorem compileReport_checks {env : Ix.Environment} {out : Ixon.Env × Failures}
    (h : compileReport env = .ok out) :
    uncovered env out.1 out.2 = [] ∧ unauthentic out.1 = [] ∧ referenceCycle out.1 = none ∧
      nameHashCollision env out.1 = none ∧ mutsMismatch out.1 = none := by
  obtain ⟨_, -, hc⟩ := compileReport_ok h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, -, -, -, -, -, -, -, -⟩ := checkReport_ok hc
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

/-- **Coverage, proved** (CQ2.27): `compileReport` publishes an input
constant exactly when it does not report it as failed. -/
theorem compileCovers : CompileCovers := by
  intro env ixe failures h n ci hn
  have hcov : uncovered env ixe failures = [] := (compileReport_checks h).1
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
  have hu : unauthentic ixe = [] := (compileReport_checks h).2.1
  unfold unauthentic at hu
  obtain ⟨hr, hb⟩ := List.append_eq_nil_iff.mp hu
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hr hb
  refine ⟨fun a lc hlc => ?_, fun a bytes hblob => ?_⟩
  · have := hr (a, lc) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hlc)
    simpa [Address.admissionHash_eq] using this
  · have := hb (a, bytes) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hblob)
    simpa [Address.admissionHash_eq] using this

/-- `nameHashCollision`'s step, from a state with no collision found: the
map keeps every entry it had, and records each name of the list under its
hash, unless a collision is found. -/
theorem nameHash_fold : ∀ (l : List Ix.Name) (acc : Std.HashMap Address Ix.Name × Option (Ix.Name × Ix.Name)),
    (l.foldl (fun acc n =>
      match acc.2 with
      | some _ => acc
      | none =>
        match acc.1.get? n.getHash with
        | some m => if Ix.nameCompareExact m n == .eq then acc else (acc.1, some (m, n))
        | none => (acc.1.insert n.getHash n, none)) acc).2 = none →
      acc.2 = none ∧
        (∀ (k : Address) (v : Ix.Name), acc.1[k]? = some v → (l.foldl (fun acc n =>
          match acc.2 with
          | some _ => acc
          | none =>
            match acc.1.get? n.getHash with
            | some m => if Ix.nameCompareExact m n == .eq then acc else (acc.1, some (m, n))
            | none => (acc.1.insert n.getHash n, none)) acc).1[k]? = some v) ∧
        ∀ x ∈ l, (l.foldl (fun acc n =>
          match acc.2 with
          | some _ => acc
          | none =>
            match acc.1.get? n.getHash with
            | some m => if Ix.nameCompareExact m n == .eq then acc else (acc.1, some (m, n))
            | none => (acc.1.insert n.getHash n, none)) acc).1[x.getHash]? = some x := by
  intro l
  induction l with
  | nil => intro acc h; exact ⟨h, fun _ _ hk => hk, fun _ hx => by cases hx⟩
  | cons y l ih =>
    intro acc h
    rw [List.foldl_cons] at h ⊢
    obtain ⟨none', keeps, recorded⟩ := ih _ h
    -- the step at `y` found no collision
    cases found : acc.2 with
    | some p =>
      simp only [found] at none'
      cases none'
    | none =>
      simp only [found] at none' keeps recorded ⊢
      cases seen : acc.1.get? y.getHash with
      | some m =>
        simp only [seen] at none' keeps recorded ⊢
        cases same : (Ix.nameCompareExact m y == .eq) with
        | false => simp only [same, Bool.false_eq_true, ↓reduceIte] at none'; cases none'
        | true =>
          simp only [same, ↓reduceIte] at keeps recorded ⊢
          have hm : m = y := Ix.CompileCert.Canon.nameCompareExact_eq_iff.mp (beq_iff_eq.mp same)
          subst hm
          refine ⟨trivial, keeps, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact keeps _ _ (by rw [← Std.HashMap.get?_eq_getElem?]; exact seen)
          · exact recorded x hx
      | none =>
        simp only [seen] at none' keeps recorded ⊢
        refine ⟨trivial, fun k v hk => keeps k v ?_, fun x hx => ?_⟩
        · rw [Std.HashMap.getElem?_insert]
          split
          · rename_i same
            have := beq_iff_eq.mp same
            subst this
            rw [← Std.HashMap.get?_eq_getElem?, seen] at hk
            cases hk
          · exact hk
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact keeps _ _ (by rw [Std.HashMap.getElem?_insert_self])
          · exact recorded x hx

/-- **Distinct name hashes**: where `nameHashCollision` finds nothing, two of
the input's constants' and the published names with one name hash are one
name. -/
theorem nameHashCollision_none {env : Ix.Environment} {ixe : Ixon.Env}
    (h : nameHashCollision env ixe = none) :
    ∀ a ∈ env.consts.keys ++ ixe.named.keys, ∀ b ∈ env.consts.keys ++ ixe.named.keys,
      a.getHash = b.getHash → a = b := by
  unfold nameHashCollision at h
  obtain ⟨-, -, recorded⟩ := nameHash_fold _ _ h
  intro a ha b hb same
  have ra := recorded a ha
  have rb := recorded b hb
  rw [same, rb] at ra
  exact (Option.some.inj ra).symm

/-- **The compile's names have distinct hashes**: `compileReport` checks it
(`checkReport`'s fourth check). -/
theorem nameHashes_distinct {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∀ a ∈ env.consts.keys ++ ixe.named.keys, ∀ b ∈ env.consts.keys ++ ixe.named.keys,
      a.getHash = b.getHash → a = b :=
  nameHashCollision_none (compileReport_checks h).2.2.2.1

/-- What `mutsMismatch = none` says: each name hash a `Muts` entry lists in
class `i` is published at member `i`'s projection of the entry's block. -/
theorem mutsMismatch_none {ixe : Ixon.Env} (h : mutsMismatch ixe = none) :
    ∀ entry named all layout, (entry, named) ∈ ixe.named.toList →
      named.constMeta.info = .muts all layout → ∀ i cls, all[i]? = some cls → ∀ x ∈ cls,
        publishedAtMember ixe (ixe.named.fold (init := {}) fun m n _ => m.insert n.getHash n)
          named.addr i x = true := by
  intro entry named all layout hn info i cls hcls x hx
  unfold mutsMismatch at h
  dsimp only at h
  rw [List.findSome?_eq_none_iff] at h
  have outer := h (entry, named) hn
  dsimp only at outer
  rw [info] at outer
  dsimp only at outer
  rw [List.findSome?_eq_none_iff] at outer
  have inner := outer (cls, i) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hcls))
  dsimp only at inner
  rw [Option.map_eq_none_iff, List.find?_eq_none] at inner
  have := inner x (Array.mem_toList_iff.mpr hx)
  simpa using this

/-- **The compile's `Muts` entries agree with its blocks**: `compileReport`
checks it (`checkReport`'s fifth check). -/
theorem mutsAgree {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∀ entry named all layout, (entry, named) ∈ ixe.named.toList →
      named.constMeta.info = .muts all layout → ∀ i cls, all[i]? = some cls → ∀ x ∈ cls,
        publishedAtMember ixe (ixe.named.fold (init := {}) fun m n _ => m.insert n.getHash n)
          named.addr i x = true :=
  mutsMismatch_none (compileReport_checks h).2.2.2.2

/-- What `resolutionMismatch = none` says: every name of `resolved` is
published at the address it resolves to. -/
theorem resolutionMismatch_none {resolved : Std.HashMap Ix.Compile.ExactKey.ExactName Address}
    {ixe : Ixon.Env} (h : resolutionMismatch resolved ixe = none) :
    ∀ n a, resolved.get? n = some a → (ixe.named.get? n).map (·.addr) = some a := by
  intro n a hn
  unfold resolutionMismatch at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : (n, a) ∈ resolved.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hn
  have := h (n, a) hmem
  dsimp only at this
  split at this
  · assumption
  · cases this

/-- **Resolved names are published where they resolve**: `compileReport`'s
result comes with the driver's resolution map at the end of the fold
(`CompileEnv.nameToAddr` of the driver's final environment, which
`compileUnchecked` returns), and every
name it holds is published at the address it resolves to (`checkReport`'s
sixth check). So a `Named` entry the aux tail registered after code no
proof follows cannot leave a resolved name published elsewhere. -/
theorem resolvedPublished {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ n a, cenv.nameToAddr.get? n = some a → (ixe.named.get? n).map (·.addr) = some a := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  exact ⟨cenv, hu, resolutionMismatch_none (checkReport_ok hc).2.2.2.2.2.1⟩

/-- An address of `mutsAddrs` is one at which a `Muts` entry is published. -/
theorem mutsAddrs_contains {ixe : Ixon.Env} {a : Address} (h : (mutsAddrs ixe).contains a = true) :
    ∃ entry e all layout, (entry, e) ∈ ixe.named.toList ∧ e.addr = a ∧
      e.constMeta.info = .muts all layout := by
  unfold mutsAddrs at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  suffices key : ∀ (l : List (Ix.Name × Ixon.Named)) (s : Std.HashSet Address),
      (l.foldl (fun s x => match x.2.constMeta.info with
        | .muts .. => s.insert x.2.addr
        | _ => s) s).contains a = true →
      s.contains a = true ∨ ∃ entry e all layout, (entry, e) ∈ l ∧ e.addr = a ∧
        e.constMeta.info = .muts all layout by
    rcases key _ _ h with h | h
    · simp at h
    · exact h
  intro l
  induction l with
  | nil => intro s h; exact .inl h
  | cons x l ih =>
    intro s h
    rcases ih _ h with h | ⟨entry, e, all, layout, hm, ha, hi⟩
    · obtain ⟨xn, xe⟩ := x
      dsimp only at h
      split at h
      · rename_i all layout hinfo
        rw [Std.HashSet.contains_insert] at h
        rcases Bool.or_eq_true_iff.mp h with heq | hs
        · exact .inr ⟨xn, xe, all, layout, List.mem_cons_self, beq_iff_eq.mp heq, hinfo⟩
        · exact .inl hs
      · exact .inl h
    · exact .inr ⟨entry, e, all, layout, List.mem_cons_of_mem _ hm, ha, hi⟩

/-- What `unseenInductive = none` says: every published input inductive is
published at an inductive projection whose block has a `Muts` entry
published at its address. -/
theorem unseenInductive_none {env : Ix.Environment} {ixe : Ixon.Env}
    (h : unseenInductive env ixe = none) :
    ∀ n v named, (n, Ix.ConstantInfo.inductInfo v) ∈ env.consts.toList →
      ixe.named.get? n = some named →
      ∃ p, (storedRecord ixe named.addr).map (·.info) = some (Ixon.ConstantInfo.iPrj p) ∧
        ∃ entry e all layout, (entry, e) ∈ ixe.named.toList ∧ e.addr = p.block ∧
          e.constMeta.info = .muts all layout := by
  intro n v named hn hnamed
  unfold unseenInductive at h
  dsimp only at h
  rw [List.findSome?_eq_none_iff] at h
  have hn := h (n, .inductInfo v) hn
  dsimp only at hn
  rw [hnamed] at hn
  dsimp only at hn
  split at hn
  · rename_i p hp
    refine ⟨p, hp, ?_⟩
    split at hn
    · rename_i hc
      exact mutsAddrs_contains hc
    · cases hn
  · cases hn

/-- **Every inductive component is seen** ((c3)): on `compileReport`'s
result, every published input inductive is published at an inductive
projection of a block with a `Muts` entry at its address (`checkReport`'s
seventh check), so the changed set's classifier, which reads an inductive
component only through its `Muts` entry, evaluates every published input
inductive's component. -/
theorem inductivesSeen {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∀ n v named, (n, Ix.ConstantInfo.inductInfo v) ∈ env.consts.toList →
      ixe.named.get? n = some named →
      ∃ p, (storedRecord ixe named.addr).map (·.info) = some (Ixon.ConstantInfo.iPrj p) ∧
        ∃ entry e all layout, (entry, e) ∈ ixe.named.toList ∧ e.addr = p.block ∧
          e.constMeta.info = .muts all layout := by
  obtain ⟨_, -, hc⟩ := compileReport_ok h
  exact unseenInductive_none (checkReport_ok hc).2.2.2.2.2.2.1

/-- What `unoriginalAux = none` says: every input name of `aux` is published
with an original-form record. -/
theorem unoriginalAux_none {env : Ix.Environment}
    {aux : Std.HashMap Ix.Compile.ExactKey.ExactName Address} {ixe : Ixon.Env}
    (h : unoriginalAux env aux ixe = none) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), aux.get? n = some a →
      env.consts.contains n = true →
        ∃ named, ixe.named.get? n = some named ∧ named.original.isSome = true := by
  intro n a hn hin
  unfold unoriginalAux at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : (n, a) ∈ aux.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hn
  have hfind := h (n, a) hmem
  dsimp only at hfind
  cases hg : ixe.named.get? n with
  | none => simp [hin, hg] at hfind
  | some named =>
    refine ⟨named, rfl, ?_⟩
    cases ho : named.original.isSome
    · simp [hin, hg, ho] at hfind
    · rfl

/-- **Input names the aux map resolves have original-form records**:
`compileReport`'s result comes with the driver's final aux map
(`CompileEnv.auxNameToAddr` of the driver's final environment), and every
input name it holds is published with `Named.original` (`checkReport`'s eighth
check). So an input name the driver resolved through the aux map is one the
classifier's regenerated rule reads (B9d); every other resolved name is a
primary claim of its own block's compile (`Ix.Cert.Resolution`). -/
theorem auxOriginal {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), cenv.auxNameToAddr.get? n = some a →
        env.consts.contains n = true →
          ∃ named, ixe.named.get? n = some named ∧ named.original.isSome = true := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  exact ⟨cenv, hu, unoriginalAux_none (checkReport_ok hc).2.2.2.2.2.2.2.1⟩

/-- What `unresolvedPublished = none` says: every published input name is in
`resolved` or in `aux`. -/
theorem unresolvedPublished_none {env : Ix.Environment}
    {resolved aux : Std.HashMap Ix.Compile.ExactKey.ExactName Address} {ixe : Ixon.Env}
    (h : unresolvedPublished env resolved aux ixe = none) :
    ∀ (n : Ix.Name) (named : Ixon.Named), (n, named) ∈ ixe.named.toList → env.consts.contains n = true →
      resolved.contains n = true ∨ aux.contains n = true := by
  intro n named hmem hin
  unfold unresolvedPublished at h
  rw [List.findSome?_eq_none_iff] at h
  have hfind := h (n, named) hmem
  dsimp only at hfind
  cases hr : resolved.contains n
  · cases ha : aux.contains n
    · simp [hin, hr, ha] at hfind
    · exact .inr rfl
  · exact .inl rfl

/-- **Published input names are resolved**: `compileReport`'s result comes
with the driver's final environment, whose resolution and aux maps
(`nameToAddr`, `auxNameToAddr`) hold every published input name
(`checkReport`'s ninth check). So a published input name is a primary claim of
a block compiled during the fold (`Ix.Cert.Resolution.compileReport_claim`),
or resolves through the aux map with an original-form record (`auxOriginal`). -/
theorem publishedResolved {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ (n : Ix.Name) (named : Ixon.Named), (n, named) ∈ ixe.named.toList → env.consts.contains n = true →
        cenv.nameToAddr.contains n = true ∨ cenv.auxNameToAddr.contains n = true := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  exact ⟨cenv, hu, unresolvedPublished_none (checkReport_ok hc).2.2.2.2.2.2.2.2.1⟩

/-- What `crossClaimed = none` says: no name of `resolved` outside `aux` is
among `extras`, or among the constructors of the input inductives among them. -/
theorem crossClaimed_none {env : Ix.Environment}
    {resolved aux : Std.HashMap Ix.Compile.ExactKey.ExactName Address}
    {extras : Std.HashSet Ix.Name} (h : crossClaimed env resolved aux extras = none) :
    ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), resolved.get? n = some a →
      aux.contains n = false → extras.contains n = false ∧ (extraCtors env extras).contains n = false := by
  intro n a hn haux
  unfold crossClaimed at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : (n, a) ∈ resolved.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hn
  have hfind := h (n, a) hmem
  dsimp only at hfind
  cases he : extras.contains n <;> cases hc : (extraCtors env extras).contains n
  · exact ⟨rfl, rfl⟩
  all_goals simp [haux, he, hc] at hfind

theorem set_foldl_insert_mono {l : List Ix.Name} {s : Std.HashSet Ix.Name} {n : Ix.Name}
    (h : s.contains n = true) : (l.foldl (fun s c => s.insert c) s).contains n = true := by
  induction l generalizing s with
  | nil => exact h
  | cons x l ih => exact ih (by rw [Std.HashSet.contains_insert, h, Bool.or_true])

theorem set_foldl_insert_mem {l : List Ix.Name} {s : Std.HashSet Ix.Name} {c n : Ix.Name}
    (hc : c ∈ l) (hcn : (c == n) = true) : (l.foldl (fun s c => s.insert c) s).contains n = true := by
  induction l generalizing s with
  | nil => cases hc
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact set_foldl_insert_mono (by rw [Std.HashSet.contains_insert, hcn, Bool.true_or])
    · exact ih hc

/-- A fold over a list whose steps keep `n` in the set, and whose step at
`e` puts it there, ends with `n` in the set when `e` is in the list. -/
theorem foldl_contains_of {f : Std.HashSet Ix.Name → Ix.Name → Std.HashSet Ix.Name} {n e : Ix.Name}
    (mono : ∀ s x, s.contains n = true → (f s x).contains n = true)
    (hit : ∀ s, (f s e).contains n = true) :
    ∀ (l : List Ix.Name) (s : Std.HashSet Ix.Name), e ∈ l → (l.foldl f s).contains n = true := by
  have keep : ∀ (l : List Ix.Name) (s : Std.HashSet Ix.Name), s.contains n = true →
      (l.foldl f s).contains n = true := by
    intro l
    induction l with
    | nil => intro s h; exact h
    | cons x l ih => intro s h; exact ih _ (mono s x h)
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x l ih =>
    intro s h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact keep _ _ (hit s)
    · exact ih _ h

/-- **The constructors of an inductive among the extra names are in
`extraCtors`**: for an extra name `e` stored in the input as an inductive, a
name that hashes like one of its constructors is in `extraCtors env extras`. -/
theorem extraCtors_contains {env : Ix.Environment} {extras : Std.HashSet Ix.Name} {e c n : Ix.Name}
    {iv : Ix.InductiveVal} (he : extras.contains e = true) (hi : env.consts.get? e = some (.inductInfo iv))
    (hc : c ∈ iv.ctors) (hcn : (c == n) = true) : (extraCtors env extras).contains n = true := by
  unfold extraCtors
  rw [Std.HashSet.fold_eq_foldl_toList]
  obtain ⟨e', he', ee'⟩ := List.contains_iff_exists_mem_beq.mp
    ((Std.HashSet.contains_toList (m := extras)).trans he)
  have hi' : env.consts.get? e' = some (.inductInfo iv) := by
    rw [← hi, Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?]
    exact (Std.HashMap.getElem?_congr ee').symm
  refine foldl_contains_of (fun s x h => ?_) (fun s => ?_) _ _ he'
  · split
    · rw [← Array.foldl_toList]; exact set_foldl_insert_mono h
    · exact h
  · rw [hi']
    dsimp only
    rw [← Array.foldl_toList]
    exact set_foldl_insert_mem (Array.mem_toList_iff.mpr hc) hcn

/-- **No cross-SCC claims**: in the driver's final environment, which
`compileUnchecked` returns, no resolved name outside the aux map is among the
extra names, where a cross-SCC subset's merge puts its members, or among the
constructors of the input inductives among them (`checkReport`'s tenth
check). -/
theorem noCrossClaims {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ cenv : Ix.CompileM.CompileEnv, compileUnchecked env = .ok (ixe, failures, cenv) ∧
      ∀ (n : Ix.Compile.ExactKey.ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false → cenv.auxGenExtraNames.contains n = false ∧
          (extraCtors env cenv.auxGenExtraNames).contains n = false := by
  obtain ⟨cenv, hu, hc⟩ := compileReport_ok h
  exact ⟨cenv, hu, crossClaimed_none (checkReport_ok hc).2.2.2.2.2.2.2.2.2.1⟩

/-- What `misnamedInput = none` says: every input constant's own name hashes
like the name it is stored under. -/
theorem misnamedInput_none {env : Ix.Environment} (h : misnamedInput env = none) :
    ∀ (n : Ix.Name) (ci : Ix.ConstantInfo), (n, ci) ∈ env.consts.toList → (ci.getCnst.name == n) = true := by
  intro n ci hmem
  unfold misnamedInput at h
  rw [List.findSome?_eq_none_iff] at h
  have hfind := h (n, ci) hmem
  dsimp only at hfind
  cases hb : (ci.getCnst.name == n)
  · simp [hb] at hfind
  · rfl

/-- **Input constants carry their names**: when `compileReport` returns,
every input constant's own name hashes like the name it is stored under
(`checkReport`'s twelfth check). -/
theorem inputsNamed {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∀ (n : Ix.Name) (ci : Ix.ConstantInfo), (n, ci) ∈ env.consts.toList → (ci.getCnst.name == n) = true := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact misnamedInput_none (checkReport_ok hc).2.2.2.2.2.2.2.2.2.2.2.1

/-- What `strayConstructor = none` says: every constructor name of an input
inductive is stored as a constructor whose inductive hashes like the name the
inductive is looked up by. -/
theorem strayConstructor_none {env : Ix.Environment} (h : strayConstructor env = none) :
    ∀ (n : Ix.Name) (iv : Ix.InductiveVal), env.consts.get? n = some (.inductInfo iv) →
      ∀ c ∈ iv.ctors, ∃ cv, env.consts.get? c = some (.ctorInfo cv) ∧ (cv.induct == n) = true := by
  intro n iv hn c hc
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hn
  obtain ⟨k, nk, hmem⟩ := hn
  unfold strayConstructor at h
  rw [List.findSome?_eq_none_iff] at h
  have hfind := h (k, .inductInfo iv) hmem
  dsimp only at hfind
  rw [List.find?_eq_none] at hfind
  have hc' := hfind c (Array.mem_toList_iff.mpr hc)
  revert hc'
  split
  · rename_i cv hcv
    intro hb
    refine ⟨cv, hcv, ?_⟩
    have hk : (cv.induct == k) = true := by simpa using hb
    exact BEq.trans hk (BEq.symm nk)
  · intro hb; simp at hb

/-- **Input constructors belong to their inductive**: when `compileReport`
returns, every constructor name of an input inductive is stored as a
constructor of it (`checkReport`'s thirteenth check). -/
theorem ctorsBelong {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∀ (n : Ix.Name) (iv : Ix.InductiveVal), env.consts.get? n = some (.inductInfo iv) →
      ∀ c ∈ iv.ctors, ∃ cv, env.consts.get? c = some (.ctorInfo cv) ∧ (cv.induct == n) = true := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact strayConstructor_none (checkReport_ok hc).2.2.2.2.2.2.2.2.2.2.2.2

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
  exact Ix.LeanIngress.checkSourceBundled_no_proof_of_False V h.2

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
  obtain ⟨_, _, _, _, hc⟩ := Ix.LeanIngress.checkSourceBundled_reading h.2
  obtain ⟨M, hM⟩ := Ix.Kernel.Cached.checkDecls_model_defn_values V _ _ envS hc
  exact ⟨{ M with defn_value := hM }⟩

theorem ixonValueSound : IxonValueSound.{w} := by
  intro _ _ _ _ _ _ h V _
  obtain ⟨M, hM⟩ := Ix.Kernel.Admission.checkBytes_has_model_values (hash := Address.blake3Pure) V h.2
  exact ⟨{ M with defn_value := hM }⟩

/-! ## The reference level (Route A, B10)

The bridge for unchanged blocks (`ROUTE-A.md` §3.1) reaches Ixon acceptance at
the reference level: the pure fold at some fuel (`Ix.Kernel.Cached.AcceptsRef`),
where neither the caches nor a fixed fuel appear. Consistency and value
soundness hold there as well, from the pure soundness tower
(`AcceptsRef.no_proof_of_False`, `AcceptsRef.model_values`), and every executed
accept is a reference accept of the same environment (`ixonAccepts_ref`). The
composition from per-block reference acceptance to the closure (locality) waits
for step 7.3's corollaries. -/

/-- **Ixon acceptance at the reference level** of the compiled closure of `S`:
the certified entry's preparation at BLAKE3 (the batch limits, key uniqueness,
authentication, the role table `binding`'s admission, canonical decoding and
reading behind the committed prelude read under the admitted table) gives
evidence and declarations that the pure fold accepts at some fuel, installing
`envA`. `limits` are resource bounds only. -/
def IxonAcceptsRef (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon) : Prop :=
  ClosureOrder ixe S order ∧
    ∃ t pre ev ds, Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (recordsOf ixe order)
        (blobsOf ixe order) (hintsOf ixe) = .ok (ev, ds) ∧
      Ix.Kernel.Cached.AcceptsRef .verified ev ds.toList envA

/-- **Ixon consistency at the reference level**: under every role table,
nothing Ixon accepts at the reference level has `False`'s role key as its
type. -/
def IxonConsistentRef : Prop :=
  ∀ (V : Type w) [SetTheory V] (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon), IxonAcceptsRef binding limits ixe S order envA →
      ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Ixon value soundness at the reference level**: every environment Ixon
accepts at the reference level has a value model, under every role table. -/
def IxonValueSoundRef : Prop :=
  ∀ (binding : Binding) (limits : Limits) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) (envA : Env .anon),
    IxonAcceptsRef binding limits ixe S order envA → ∀ (V : Type w) [SetTheory V], Nonempty (ValueModel V envA)

theorem ixonConsistentRef : IxonConsistentRef.{w} := by
  intro V _ _ _ _ _ _ _ h
  obtain ⟨_, _, _, _, _, _, _, _, ref⟩ := h
  exact ref.no_proof_of_False V

theorem ixonValueSoundRef : IxonValueSoundRef.{w} := by
  intro _ _ _ _ _ _ h V _
  obtain ⟨_, _, _, _, _, _, _, _, ref⟩ := h
  obtain ⟨M, hM⟩ := ref.model_values V
  exact ⟨{ M with defn_value := hM.1 }⟩

/-- **Every Ixon accept is a reference accept** of the same environment
(`Ix.Kernel.Cached.checkDecls_refines_ref`; the set theory is a hypothesis of
that walk, not of the statement's meaning), so `IxonConsistent` and
`IxonValueSound` follow from their reference-level twins. -/
theorem ixonAccepts_ref (V : Type w) [SetTheory V] {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxonAccepts binding limits ixe S order envA) : IxonAcceptsRef binding limits ixe S order envA := by
  obtain ⟨closure, accepted⟩ := h
  obtain ⟨t, pre, admitted, prelude, run⟩ := Ix.Kernel.Admission.checkBytes_with accepted
  obtain ⟨ev, ds, prepared, checked⟩ := Ix.Kernel.Admission.checkBytesWith_checkDecls run
  exact ⟨closure, t, pre, ev, ds, admitted, prelude, prepared,
    Ix.Kernel.Cached.checkDecls_refines_ref V rfl checked⟩

/-! ## Quotient Source and S4 (`ALPHA-COLLAPSE.md` §8; owner, 2026-10-20)

The certified theory is Lean with α-collapse made explicit: Source runs on the
artifact's alias fibers, every fiber renamed onto one representative and its
duplicates dropped, a fiber holding a role-bound address represented by that
role (the table rule, `Ix.LeanIngress.fiberAliasAt` at the role table's inverse),
at the artifact's per-fiber hints, at the pinned bundle evidence renamed onto the
representatives (`Ix.LeanIngress.evidenceSubst`). The prepared stream is checked
to be a renaming onto the artifact's keys (`Ix.LeanIngress.prepareSourceCollapsedAt`:
every key a representative, the bundle disjoint from the artifact, every evidence
key a representative or a bundle-only name). `SourceAcceptsQ` is that acceptance at
the reference level; the executed check gives it (`sourceAcceptsQ_of_check`).
Nominal acceptance implies it only through S4 (`NominalQuotientAgree`), a named
assumption that no theorem uses silently. -/

/-- **Quotient Source acceptance, per root, at a role table**: the closure `sub` of
`roots` in `env`, grouped by `condense sub`, ingressed at the artifact `ixe`'s
per-fiber hints, collapsed onto its alias fibers' representatives with the role read
off the table `t`, and checked to be a renaming onto the artifact's keys
(`Ix.LeanIngress.prepareSourceCollapsedAt`), behind the committed prelude, is accepted
by the pure fold at some fuel at the pinned bundle evidence renamed onto the
representatives (`Ix.LeanIngress.evidenceSubst` at `fiberAliasAt ixe (roleAtMap t)`),
installing `envS`. -/
def SourceAcceptsQ (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment)
    (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (envS : Env .source) : Prop :=
  IsClosure env roots sub ∧
    ∃ pre ds, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      Ix.LeanIngress.prepareSourceCollapsedAt ixe t
        ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub (condense sub) = .ok ds ∧
      Ix.Kernel.Cached.AcceptsRef .verified
        (Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
          (Ix.RoleEvidence.bundleEvidence ())) ds.toList envS

/-- **The executed quotient check gives `SourceAcceptsQ`**
(`Ix.LeanIngress.checkSourceCollapsedBundledAt_ref`, from
`Ix.Kernel.Cached.checkDecls_refines_ref`; the set theory is a hypothesis of
that walk, not of the statement's meaning). -/
theorem sourceAcceptsQ_of_check (V : Type w) [SetTheory V] {condense : Ix.Environment → Ix.CondensedBlocks}
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {envS : Env .source} (closure : IsClosure env roots sub)
    (h : Ix.LeanIngress.checkSourceCollapsedBundledAt ixe t sub (condense sub) = .ok envS) :
    SourceAcceptsQ condense env roots sub ixe t envS :=
  ⟨closure, Ix.LeanIngress.checkSourceCollapsedBundledAt_ref V h⟩

/-- **S4: nominal Source acceptance implies quotient Source acceptance** at the
compiled artifact's alias fibers, the role read off the default table
(`ALPHA-COLLAPSE.md` §5, §8.1). An assumption, not an axiom: unproved here, it is
the documented follow-up (the non-injective renaming lemma: algorithmic 4–8k plus
IxC changes, or semantic 10–25k). Its measured gap on Init+Std is 0: quotient
Source's rows are nominal Source's. A corollary that uses it takes it as a
hypothesis; no theorem depends on it silently. -/
def NominalQuotientAgree : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Env .source)
    (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable), SourceAccepts blocksOf env roots sub envS →
      compile env = .ok ixe → Ix.Kernel.Reader.defaultTable = .ok t →
        ∃ envQ, SourceAcceptsQ blocksOf env roots sub ixe t envQ

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
input keys, a failure's keys included (its message is structured: prose and
keys, `Ix.Kernel.Msg`, step 6). The bridge from Source to Ixon renames a
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

/-- A fold's result: an accepted environment renamed by `env`, a failure's
keys by `CheckError.mapKeys`, at the same position. -/
def result : Except (Ix.Kernel.CheckError md × Nat) (Env md) →
    Except (Ix.Kernel.CheckError md' × Nat) (Env md')
  | .ok e => .ok (env σ e)
  | .error (e, i) => .error (e.mapKeys σ, i)

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

/-- **The renaming lemma.** Stated, not proved: renaming a Source run's keys
to compiled ones by `Key.map f`, `f` injective on the run's ids, renames the
fold's result: the accepted environment, or the failure's keys at the same
position (`Rename.result`). The failure is compared whole: its verdict, its
position and its message, whose keys are renamed (structured errors,
IXC-PLAN step 6; before them the lemma compared the verdict kind and the
position only). -/
def RenamingLemma : Prop :=
  ∀ (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (ev : Ix.Kernel.Evidences .source)
    (ds : Array (Ix.Kernel.Declaration .source)), RenamingHyp f ev ds →
      Ix.Kernel.Cached.checkDecls .verified (Rename.evidences (Ix.Kernel.Key.map f) ev)
          (ds.map (Rename.declaration (Ix.Kernel.Key.map f))) =
        Rename.result (Ix.Kernel.Key.map f) (Ix.Kernel.Cached.checkDecls .verified ev ds)

end Ix.Cert
