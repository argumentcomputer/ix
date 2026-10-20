import Ix.Cert.Statement
import Ix.Cert.Closure
import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.ReadingAudit
import Ix.Cert.Canon
import Ix.Cert.Schedule
import Ix.Cert.Hybrid
import Ix.Cert.Stream
import Ix.Cert.Order
import Ix.Cert.Evidence
import Ix.Cert.Roles
import Ix.Cert.Admits
import Ix.Cert.BlockStart
import Ix.Cert.RoleClosure
import Ix.Cert.NoCtor
import Ix.Cert.Quotient

/-! # The certification statements, frozen

`#print` freezes every statement (`def … : Prop`) and every definition a
statement reads; `#check` freezes the proved theorems; `#print axioms`
freezes their axioms, which are the three standard ones. A change to any of
them fails the build.

The compiler's own axioms are frozen too: `Ix.Cert.compile`,
`Ix.Cert.blocksOf` and `Ix.Cert.CompileCorrect` reach only the three
standard ones. Every BLAKE3 digest they reach (`Address.blake3`, and the
`Ix.Name`, `Ix.Level`, `Ix.Expr` and `Ix.Tc` hashing constructors) is
finalized by `Address.ofHasher`, which passes the package's length bound
explicitly instead of proving it `by native_decide`; `blocksOf`'s
condensation is total (`Ix.CompileCert.Canon.condensation_isSome`, frozen
with it) and reads no `Inhabited Ix.Name` default. The proved Source theorems
quantify over every grouping function, which is stronger than naming
`blocksOf`; their instances at `blocksOf` (`sourceConsistent_blocksOf`,
`sourceValueSound_blocksOf`) are frozen at the three standard axioms too.

`#print axioms` does not show what executes in place of the logic.
`Ix.Cert.RuntimeAudit` freezes the runtime closure of `compile`: the
project-level foreign primitives, `unsafe` implementations and `partial`
definitions its compiled code reaches, which a proof about `compile` meets as
opaque constants.

Step 5b (the kernel's types indexed by a `Mode`) re-froze the statements
with the modes made explicit and nothing else changed: Source mode installs
an `Env .source`, Ixon mode an `Env .anon`, and the reading takes a source
constant to a compiled term (`ConstantInfo .source → Option (Expr .anon)`).
Value models, the renaming and the key sets it reads are generic in the
mode (`{md : Mode}`), and `RenamingLemma` quantifies over it. With Ixon
addresses as `.anon` keys, the reading and the admission context were
re-frozen: a source constant reads as the reader's key of its published
address (`Ix.Kernel.Reader.Ctx.keyAt`), and the context carries the hash that
keys a block member whose projection record the artifact omits. -/

/-- info: def Ix.Cert.refsOf : Ix.ConstantInfo → Ix.Set Ix.Name :=
fun ci => (Ix.GraphM.run { consts := ∅ } Ix.GraphState.init (Ix.graphConst ci)).fst -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.refsOf

/-- info: def Ix.Cert.DependsOn : Ix.Environment → Ix.Name → Ix.Name → Prop :=
fun env a b =>
  ∃ ci,
    env.consts.get? a = some ci ∧
      (Std.HashSet.contains (Ix.Cert.refsOf ci) b = true ∨
        (Ix.Cert.literalSupport ci).contains b = true ∨
          match ci with
          | Ix.ConstantInfo.inductInfo v =>
            v.all.contains b = true ∨
              ∃ first rv,
                v.all[0]? = some first ∧ env.consts.get? b = some (Ix.ConstantInfo.recInfo rv) ∧ rv.all[0]? = some first
          | Ix.ConstantInfo.recInfo rv => rv.all.contains b = true
          | x => False) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.DependsOn

-- The literal support (owner, 2026-10-20): a constant's literals depend on the constants IxC
-- checks them against.
/-- info: def Ix.Cert.literalSupport : Ix.ConstantInfo → Array Ix.Name :=
fun ci =>
  if (Ix.Cert.termsOf ci).any Ix.Cert.hasStrLit = true then Ix.Cert.supportNames Ix.Kernel.Reader.strLitSupportNames
  else
    if (Ix.Cert.termsOf ci).any Ix.Cert.hasNatLit = true then Ix.Cert.supportNames Ix.Kernel.Reader.natLitSupportNames
    else #[] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.literalSupport

/-- info: inductive Ix.Cert.Reaches : Ix.Environment → List Ix.Name → Ix.Name → Prop
number of parameters: 2
constructors:
Ix.Cert.Reaches.root : ∀ {env : Ix.Environment} {roots : List Ix.Name} {n : Ix.Name},
  roots.contains n = true → Ix.Cert.Reaches env roots n
Ix.Cert.Reaches.step : ∀ {env : Ix.Environment} {roots : List Ix.Name} {a b : Ix.Name},
  Ix.Cert.Reaches env roots a → Ix.Cert.DependsOn env a b → Ix.Cert.Reaches env roots b -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Reaches

/-- info: def Ix.Cert.IsClosure : Ix.Environment → List Ix.Name → Ix.Environment → Prop :=
fun env roots sub =>
  ∀ (n : Ix.Name),
    (Ix.Cert.Reaches env roots n → sub.consts.get? n = env.consts.get? n) ∧
      (¬Ix.Cert.Reaches env roots n → sub.consts.get? n = none) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IsClosure

/-- info: def Ix.Cert.SourceAccepts : (Ix.Environment → Ix.CondensedBlocks) →
  Ix.Environment → List Ix.Name → Ix.Environment → Ix.Kernel.Env Ix.Kernel.Mode.source → Prop :=
fun condense env roots sub envS =>
  Ix.Cert.IsClosure env roots sub ∧ Ix.LeanIngress.checkSourceBundled sub (condense sub) = Except.ok envS -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceAccepts

-- CQP.3: the worklist finds an inductive's recursors by the block's first
-- member compared structurally (`nameEq`), as `DependsOn` compares it. It
-- compared the hash fields only (`Ix.Name`'s `==`), so with two names of one
-- hash field it kept a recursor the roots do not reach, and `ClosureCorrect`
-- was false. It is now a `repeatM` loop over a stack (`closureStep`,
-- `closureLoop`), which unfolds one step at a time, and `ClosureCorrect` is
-- proved (`Ix.Cert.closureCorrect`, `Ix.Cert.Closure`).
/-- info: Ix.Cert.nameEq.eq_def : ∀ (x x_1 : Ix.Name),
  Ix.Cert.nameEq x x_1 =
    match x, x_1 with
    | Ix.Name.anonymous h, Ix.Name.anonymous h' => h == h'
    | p.str s h, p'.str s' h' => h == h' && s == s' && Ix.Cert.nameEq p p'
    | p.num i h, p'.num i' h' => h == h' && i == i' && Ix.Cert.nameEq p p'
    | x, x_2 => false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.nameEq.eq_def

/-- info: def Ix.Cert.recursorsByBlock : Ix.Environment → Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)) :=
fun env =>
  Std.HashMap.fold
    (fun m n ci =>
      match ci with
      | Ix.ConstantInfo.recInfo rv =>
        match rv.all[0]? with
        | some first => Std.HashMap.insert m first ((Std.HashMap.getD m first #[]).push (first, n))
        | none => m
      | x => m)
    ∅ env.consts -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recursorsByBlock

/-- info: def Ix.Cert.dependencies : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)) → Ix.ConstantInfo → Array Ix.Name :=
fun recursors ci =>
  Std.HashSet.toArray (Ix.Cert.refsOf ci) ++ Ix.Cert.literalSupport ci ++
    match ci with
    | Ix.ConstantInfo.inductInfo v =>
      v.all ++
        match v.all[0]? with
        | some first =>
          Array.map (fun x => x.snd)
            (Array.filter (fun x => Ix.Cert.nameEq x.fst first) (Std.HashMap.getD recursors first #[]))
        | none => #[]
    | Ix.ConstantInfo.recInfo rv => rv.all
    | x => #[] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.dependencies

/-- info: def Ix.Cert.closureStep : Ix.Environment →
  Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)) →
    Ix.Set Ix.Name × List Ix.Name → Ix.Set Ix.Name × List Ix.Name ⊕ Ix.Set Ix.Name :=
fun env recursors x =>
  match x with
  | (seen, []) => Sum.inr seen
  | (seen, n :: todo) =>
    if Std.HashSet.contains seen n = true then Sum.inl (seen, todo)
    else
      match env.consts.get? n with
      | none => Sum.inl (seen, todo)
      | some ci => Sum.inl (Std.HashSet.insert seen n, (Ix.Cert.dependencies recursors ci).toList ++ todo) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.closureStep

/-- info: def Ix.Cert.closureLoop : Ix.Environment → Ix.Set Ix.Name × List Ix.Name → Ix.Set Ix.Name :=
fun env s => (repeatM (fun s => pure (Ix.Cert.closureStep env (Ix.Cert.recursorsByBlock env) s)) s).run -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.closureLoop

/-- info: def Ix.Cert.closure : Ix.Environment → List Ix.Name → Ix.Environment :=
fun env roots =>
  have seen := Ix.Cert.closureLoop env (∅, roots);
  { consts := Std.HashMap.filter (fun n x => Std.HashSet.contains seen n) env.consts } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.closure

/-- info: def Ix.Cert.ClosureCorrect : Prop :=
∀ (env : Ix.Environment) (roots : List Ix.Name), Ix.Cert.IsClosure env roots (Ix.Cert.closure env roots) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ClosureCorrect

/-- info: def Ix.Cert.recordAt : Ixon.Env → Address → Option Ixon.Constant :=
fun ixe a => (ixe.consts.get? a).bind fun x => x.get? -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recordAt

/-- info: def Ix.Cert.ownerOf : Address → Ixon.Constant → Address :=
fun a c =>
  match c.info with
  | Ixon.ConstantInfo.dPrj p => p.block
  | Ixon.ConstantInfo.iPrj p => p.block
  | Ixon.ConstantInfo.rPrj p => p.block
  | Ixon.ConstantInfo.cPrj p => p.block
  | x => a -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ownerOf

/-- info: def Ix.Cert.RecordEdge : Ixon.Env → Address → Address → Prop :=
fun ixe a b =>
  ∃ c,
    Ix.Cert.recordAt ixe a = some c ∧
      (Ix.Cert.ownerOf a c = b ∧ b ≠ a ∨ c.refs.contains b = true ∧ ixe.consts.contains b = true) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RecordEdge

/-- info: inductive Ix.Cert.CompiledReach : Ixon.Env → (Address → Prop) → Address → Prop
number of parameters: 2
constructors:
Ix.Cert.CompiledReach.seed : ∀ {ixe : Ixon.Env} {S : Address → Prop} {a : Address},
  S a → ixe.consts.contains a = true → Ix.Cert.CompiledReach ixe S a
Ix.Cert.CompiledReach.step : ∀ {ixe : Ixon.Env} {S : Address → Prop} {a b : Address},
  Ix.Cert.CompiledReach ixe S a → Ix.Cert.RecordEdge ixe a b → Ix.Cert.CompiledReach ixe S b -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.CompiledReach

/-- info: def Ix.Cert.RecordRef : Ixon.Env → Address → Address → Prop :=
fun ixe a b =>
  ∃ c,
    Ix.Cert.recordAt ixe a = some c ∧
      ∃ r, r ∈ c.refs ∧ ∃ cr, Ix.Cert.recordAt ixe r = some cr ∧ Ix.Cert.ownerOf r cr = b ∧ b ≠ a -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RecordRef

/-- info: structure Ix.Cert.ClosureOrder (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) : Prop
number of parameters: 3
fields:
  Ix.Cert.ClosureOrder.nodup : order.Nodup
  Ix.Cert.ClosureOrder.complete : ∀ (a : Address), a ∈ order ↔ Ix.Cert.CompiledReach ixe S a
  Ix.Cert.ClosureOrder.ordered : List.Pairwise (fun a b => ¬Ix.Cert.RecordRef ixe a b) order
constructor:
  Ix.Cert.ClosureOrder.mk {ixe : Ixon.Env} {S : Address → Prop} {order : List Address} (nodup : order.Nodup)
    (complete : ∀ (a : Address), a ∈ order ↔ Ix.Cert.CompiledReach ixe S a)
    (ordered : List.Pairwise (fun a b => ¬Ix.Cert.RecordRef ixe a b) order) : Ix.Cert.ClosureOrder ixe S order -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ClosureOrder

/-- info: def Ix.Cert.recordsOf : Ixon.Env → List Address → Ix.Kernel.Admission.Records :=
fun ixe order => List.filterMap (fun a => Option.map (fun lc => (a, lc.rawBytes)) (ixe.consts.get? a)) order -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recordsOf

/-- info: def Ix.Cert.blobsOf : Ixon.Env → List Address → Ix.Kernel.Ingress.Blobs :=
fun ixe order =>
  have used :=
    List.foldl
      (fun s a =>
        match Ix.Cert.recordAt ixe a with
        | some c => Array.foldl (fun x1 x2 => x1.insert x2) s c.refs
        | none => s)
      ∅ order;
  List.filter (fun b => used.contains b.fst) ixe.blobs.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.blobsOf

/-- info: def Ix.Cert.hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint :=
fun x =>
  match x with
  | Lean.ReducibilityHints.opaque => Ix.Kernel.ReducibilityHint.opaque
  | Lean.ReducibilityHints.abbrev => Ix.Kernel.ReducibilityHint.abbrev
  | Lean.ReducibilityHints.regular h => Ix.Kernel.ReducibilityHint.regular h.toNat -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.hintOf

/-- info: def Ix.Cert.hintsOf : Ixon.Env → Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint :=
fun ixe =>
  have projAt :=
    Std.HashMap.fold
      (fun m a lc =>
        match lc.get? with
        | some c =>
          match c.info with
          | Ixon.ConstantInfo.dPrj p => m.insert (Ix.Kernel.ConstRef.member p.block p.idx.toNat) a
          | x => m
        | none => m)
      ∅ ixe.consts;
  fun r => Ix.Cert.hintOf <$> ixe.anonHints.get? ((projAt.get? r).getD r.block) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.hintsOf

/-- info: def Ix.Cert.IxonAccepts : Ix.Kernel.Admission.Binding →
  Ix.Kernel.Admission.Limits → Ixon.Env → (Address → Prop) → List Address → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop :=
fun binding limits ixe S order envA =>
  Ix.Cert.ClosureOrder ixe S order ∧
    Ixon.Authenticated.checkBytes binding limits (Ix.Cert.recordsOf ixe order) (Ix.Cert.blobsOf ixe order)
        (Ix.Cert.hintsOf ixe) =
      Except.ok envA -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonAccepts

/-- info: def Ix.Cert.Seed : Ixon.Env → Ix.Environment → Address → Prop :=
fun ixe sub a => ∃ n ci named, sub.consts.get? n = some ci ∧ ixe.named.get? n = some named ∧ named.addr = a -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Seed

/-- info: def Ix.Cert.Published : Ixon.Env → Ix.Environment → Prop :=
fun ixe sub =>
  ∀ (n : Ix.Name) (ci : Ix.ConstantInfo), sub.consts.get? n = some ci → ∃ named, ixe.named.get? n = some named -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Published

/-- info: structure Ix.Cert.ValueModel.{w} {md : Ix.Kernel.Mode} (V : Type w) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env md) :
  Type w
number of parameters: 4
parents:
  Ix.Cert.ValueModel.toModel : Ix.Kernel.Model V env
fields:
  Ix.Kernel.Model.cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V
  Ix.Kernel.Model.mem : ∀ (c : Ix.Kernel.ConstantInfo md),
      c ∈ env.consts →
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
          ∃ T,
            Ix.Kernel.Denotes self.cval env φ ρ c.toConstantVal.type T ∧ Ix.Kernel.SetTheory.Mem (self.cval c.name φ) T
  Ix.Kernel.Model.false_empty : ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (F : V),
      Ix.Kernel.Denotes self.cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.falseName []) F →
        F = Ix.Kernel.SetTheory.empty
  Ix.Kernel.Model.eq_equality : ∀ (u : Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V)
      (E A a b : V),
      Ix.Kernel.Denotes self.cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.eqName [u]) E →
        Ix.Kernel.SetTheory.Mem A (Ix.Kernel.SetTheory.univ (Ix.Kernel.Level.eval φ u)) →
          Ix.Kernel.SetTheory.Mem a A →
            Ix.Kernel.SetTheory.Mem b A →
              Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app E A) a) b =
                Ix.Kernel.SetTheory.eqv a b
  Ix.Cert.ValueModel.defn_value : ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md)
      (hint : Ix.Kernel.ReducibilityHint),
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
          Ix.Kernel.Denotes self.cval env φ ρ value (self.cval cv.name φ)
constructor:
  Ix.Cert.ValueModel.mk.{w} {md : Ix.Kernel.Mode} {V : Type w} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env md}
    (toModel : Ix.Kernel.Model V env)
    (defn_value :
      ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes toModel.cval env φ ρ value (toModel.cval cv.name φ)) :
    Ix.Cert.ValueModel V env
field notation resolution order:
  Ix.Cert.ValueModel, Ix.Kernel.Model -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ValueModel

-- Step 5a (typed keys): a source constant's key is `Ix.Kernel.Key` (was the
-- name), matched against the published names by `Ix.LeanIngress.nameIs`.
/-- info: def Ix.Cert.publishedAddress : Ixon.Env → Ix.Kernel.Key Ix.Kernel.Mode.source → Option Address :=
fun ixe k =>
  Option.map (fun x => x.snd.addr)
    (List.find?
      (fun x =>
        match x with
        | (m, snd) => Ix.LeanIngress.nameIs m k)
      ixe.named.toList) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.publishedAddress

/-- info: def Ix.Cert.admissionContext : Ix.Kernel.Admission.Binding →
  Ix.Kernel.Admission.Limits → Ixon.Env → List Address → Option (Ix.Kernel.Reader.Ctx Ix.Kernel.Mode.anon) :=
fun binding limits ixe order => do
  let t ← (Ix.Kernel.Admission.admitBinding Address.blake3Pure binding).toOption
  let pre ← (Ix.Kernel.Reader.preludeFor t).toOption
  let constants ← (Ix.Kernel.Admission.decodeRecords limits (Ix.Cert.recordsOf ixe order)).toOption
  pure
      (Ix.Kernel.Admission.streamContext Address.blake3Pure t pre constants (Ix.Cert.blobsOf ixe order)
        (Ix.Cert.hintsOf ixe)) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.admissionContext

/-- info: def Ix.Cert.reading : Ixon.Env →
  Ix.Kernel.Reader.Ctx Ix.Kernel.Mode.anon →
    Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source → Option (Ix.Kernel.Expr Ix.Kernel.Mode.anon) :=
fun ixe cx c => do
  let a ← Ix.Cert.publishedAddress ixe c.name
  let k ← Except.toOption (cx.keyAt a)
  pure (Ix.Kernel.Expr.const k (List.map Ix.Kernel.Level.param c.toConstantVal.levelParams)) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.reading

/-- info: def Ix.Cert.Commutes.{w} : (Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source →
    Option (Ix.Kernel.Expr Ix.Kernel.Mode.anon)) →
  Ix.Kernel.Env Ix.Kernel.Mode.source → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop :=
fun τ envS envA =>
  ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V] (M : Ix.Cert.ValueModel V envA),
    ∃ N,
      ∀ (c : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
        c ∈ envS.consts →
          ∀ (t : Ix.Kernel.Expr Ix.Kernel.Mode.anon),
            τ c = some t →
              ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
                Ix.Kernel.Denotes M.cval envA φ ρ t (N.cval c.name φ) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Commutes

-- CQP.1: `HashAgreement` (`∀ bytes, Address.blake3 bytes = Address.blake3Pure
-- bytes`) is gone, as `CompileCorrect`'s hypothesis and as a definition: since
-- CQ2.2 every content address the compiler computes is `Address.admissionHash`,
-- pure BLAKE3 in the logic, so the statement no longer assumes that the Rust
-- and the pure BLAKE3 agree. That the compiler's records and blobs sit at pure
-- BLAKE3 of their bytes is a property of `compile`, `CompileAuthentic`.
/-- info: def Ix.Cert.CompileAuthentic : Prop :=
∀ (env : Ix.Environment) (ixe : Ixon.Env),
  Ix.Cert.compile env = Except.ok ixe →
    (∀ (a : Address) (lc : Ixon.LazyConstant), ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
      ∀ (a : Address) (bytes : ByteArray), ixe.blobs.get? a = some bytes → a = Address.blake3Pure bytes -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.CompileAuthentic

-- CQP.2: `CompileCorrect` is hypothesised on the compile's own report
-- (`compileReport`), decidably, instead of on the artifact: "no constant of the
-- closure failed" (`NoFailure`) replaces `Published ixe sub`, which it now
-- concludes; the rest of the conclusion is `IxonCommutes`, the former one
-- verbatim. `CompileCovers` (every input constant is published exactly when it
-- did not fail) is stated, and under it the new and the former statement imply
-- each other (`CompileCorrect.published`, `CompileCorrect.of_published`).
-- CQ2.27: `CompileCovers` and `CompileAuthentic` are proved
-- (`compileCovers`, `compileAuthentic`), from `compileReport`'s own checks;
-- their statements are unchanged.
/-- info: def Ix.Cert.Failures.failed : Ix.Cert.Failures → Ix.Name → Bool :=
fun failures n => failures.ungrounded.contains n || failures.blocks.contains n -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Failures.failed

/-- info: def Ix.Cert.NoFailure : Ix.Cert.Failures → Ix.Environment → Prop :=
fun failures sub => ∀ (n : Ix.Name) (ci : Ix.ConstantInfo), sub.consts.get? n = some ci → failures.failed n = false -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.NoFailure

/-- info: def Ix.Cert.CompileCovers : Prop :=
∀ (env : Ix.Environment) (ixe : Ixon.Env) (failures : Ix.Cert.Failures),
  Ix.Cert.compileReport env = Except.ok (ixe, failures) →
    ∀ (n : Ix.Name) (ci : Ix.ConstantInfo),
      env.consts.get? n = some ci → ((∃ named, ixe.named.get? n = some named) ↔ failures.failed n = false) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.CompileCovers

/-- info: def Ix.Cert.IxonCommutes.{w} : Ixon.Env → Ix.Environment → Ix.Kernel.Env Ix.Kernel.Mode.source → Prop :=
fun ixe sub envS =>
  ∃ binding,
    Ix.Kernel.Admission.defaultBinding = Except.ok binding ∧
      ∃ limits order envA cx,
        Ix.Cert.IxonAccepts binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
          Ix.Cert.admissionContext binding limits ixe order = some cx ∧
            Ix.Cert.Commutes (Ix.Cert.reading ixe cx) envS envA -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonCommutes

/-- info: def Ix.Cert.CompileCorrect.{w} : Prop :=
∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
  (ixe : Ixon.Env) (failures : Ix.Cert.Failures),
  Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
    Ix.Cert.compileReport env = Except.ok (ixe, failures) →
      Ix.Cert.NoFailure failures sub → Ix.Cert.Published ixe sub ∧ Ix.Cert.IxonCommutes ixe sub envS -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.CompileCorrect

/-- info: def Ix.Cert.SourceConsistent.{w} : Prop :=
∀ (condense : Ix.Environment → Ix.CondensedBlocks) (V : Type w) [Ix.Kernel.SetTheory V] (env : Ix.Environment)
  (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source),
  Ix.Cert.SourceAccepts condense env roots sub envS →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
      ci ∈ envS.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceConsistent

/-- info: def Ix.Cert.IxonConsistent.{w} : Prop :=
∀ (V : Type w) [Ix.Kernel.SetTheory V] (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits)
  (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) (envA : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ix.Cert.IxonAccepts binding limits ixe S order envA →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon),
      ci ∈ envA.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonConsistent

/-- info: def Ix.Cert.IxonAuthentic : Prop :=
∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env) (S : Address → Prop)
  (order : List Address) (envA : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ix.Cert.IxonAccepts binding limits ixe S order envA →
    (∀ (a : Address),
        a ∈ order → ∀ (lc : Ixon.LazyConstant), ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
      (∀ (b : Address × ByteArray), b ∈ Ix.Cert.blobsOf ixe order → b.fst = Address.blake3Pure b.snd) ∧
        Address.blake3Pure binding.bytes = binding.address -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonAuthentic

/-- info: def Ix.Cert.SourceValueSound.{w} : Prop :=
∀ (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment)
  (envS : Ix.Kernel.Env Ix.Kernel.Mode.source),
  Ix.Cert.SourceAccepts condense env roots sub envS →
    ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V], Nonempty (Ix.Cert.ValueModel V envS) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceValueSound

/-- info: def Ix.Cert.IxonValueSound.{w} : Prop :=
∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env) (S : Address → Prop)
  (order : List Address) (envA : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ix.Cert.IxonAccepts binding limits ixe S order envA →
    ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V], Nonempty (Ix.Cert.ValueModel V envA) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonValueSound

-- Route A, B10: the reference-level twins of Ixon acceptance, consistency and value soundness
-- (the pure fold at some fuel), and every executed accept is a reference accept.
/-- info: def Ix.Cert.IxonAcceptsRef : Ix.Kernel.Admission.Binding →
  Ix.Kernel.Admission.Limits → Ixon.Env → (Address → Prop) → List Address → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop :=
fun binding limits ixe S order envA =>
  Ix.Cert.ClosureOrder ixe S order ∧
    ∃ t pre ev ds,
      Ix.Kernel.Admission.admitBinding Address.admissionHash binding = Except.ok t ∧
        Ix.Kernel.Reader.preludeFor t = Except.ok pre ∧
          Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (Ix.Cert.recordsOf ixe order)
                (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) =
              Except.ok (ev, ds) ∧
            Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified ev ds.toList envA -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonAcceptsRef

/-- info: def Ix.Cert.IxonConsistentRef.{w} : Prop :=
∀ (V : Type w) [Ix.Kernel.SetTheory V] (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits)
  (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) (envA : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ix.Cert.IxonAcceptsRef binding limits ixe S order envA →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon),
      ci ∈ envA.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonConsistentRef

/-- info: def Ix.Cert.IxonValueSoundRef.{w} : Prop :=
∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env) (S : Address → Prop)
  (order : List Address) (envA : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ix.Cert.IxonAcceptsRef binding limits ixe S order envA →
    ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V], Nonempty (Ix.Cert.ValueModel V envA) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonValueSoundRef

/-- info: Ix.Cert.ixonAccepts_ref : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {ixe : Ixon.Env} {S : Address → Prop} {order : List Address}
  {envA : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Cert.IxonAccepts binding limits ixe S order envA → Ix.Cert.IxonAcceptsRef binding limits ixe S order envA -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.ixonAccepts_ref

-- Step 5a (typed keys) re-froze the renaming lemma's definitions over
-- `Ix.Kernel.Key`: `σ : Key → Key`, the key lists are `List Key`, `Pinned` is
-- the role keys (the basis blocks' reserved keys are role keys,
-- `Ix.Cert.reservedBasisNames_pinned`), `DerivedFrom` is one or more `aux`
-- layers, and `RenamingHyp` replaces `str`/`num` by `aux` (commuting with a
-- derived shape off the input keys) and drops `anonymous` (keys have no
-- `etaCtor` sentinel) and `recursor` (no key spells a recursor the checker
-- reads).
-- Step 5b: `letE` carries a fourth field, its `LetMeta`, which a renaming keeps.
-- The renaming now takes a mode to another (`σ : Key md → Key md'`), so a
-- recursor rule's firing mode, an inductive's capabilities and a projection
-- table are renamed field by field (`Rename.recRuleFire`, `Rename.indCaps`,
-- `Rename.projTable`), and the lemma is stated for `σ = Key.map f` from Source
-- keys to Ixon keys with `f` injective on the input's ids (`keyIds`,
-- `InputId`, `RenamingHyp`, IXC-PLAN §12). `Pinned`, `DerivedFrom`, `Built` and
-- `reservedBasisNames_pinned` went with the old hypotheses: `Key.map` fixes
-- the role keys and commutes with derived shapes by construction.
/-- info: @Ix.Cert.Rename.expr.eq_def : ∀ {md md' : Ix.Kernel.Mode} (σ : Ix.Kernel.Key md → Ix.Kernel.Key md')
  (x : Ix.Kernel.Expr md),
  Ix.Cert.Rename.expr σ x =
    match x with
    | Ix.Kernel.Expr.bvar i => Ix.Kernel.Expr.bvar i
    | Ix.Kernel.Expr.fvar i t => Ix.Kernel.Expr.fvar i (Ix.Cert.Rename.expr σ t)
    | Ix.Kernel.Expr.sort u => Ix.Kernel.Expr.sort u
    | Ix.Kernel.Expr.const n us => Ix.Kernel.Expr.const (σ n) us
    | f.app a => (Ix.Cert.Rename.expr σ f).app (Ix.Cert.Rename.expr σ a)
    | t.lam b m => (Ix.Cert.Rename.expr σ t).lam (Ix.Cert.Rename.expr σ b) m
    | t.forallE b m => (Ix.Cert.Rename.expr σ t).forallE (Ix.Cert.Rename.expr σ b) m
    | t.letE v b l => (Ix.Cert.Rename.expr σ t).letE (Ix.Cert.Rename.expr σ v) (Ix.Cert.Rename.expr σ b) l
    | Ix.Kernel.Expr.lit l => Ix.Kernel.Expr.lit l
    | Ix.Kernel.Expr.proj n i e => Ix.Kernel.Expr.proj (σ n) i (Ix.Cert.Rename.expr σ e) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Rename.expr.eq_def

/-- info: def Ix.Cert.Rename.constantVal : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.ConstantVal md → Ix.Kernel.ConstantVal md' :=
fun {md md'} σ cv => { name := σ cv.name, levelParams := cv.levelParams, type := Ix.Cert.Rename.expr σ cv.type } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.constantVal

/-- info: def Ix.Cert.Rename.recRuleFire : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.RecRuleFire md → Ix.Kernel.RecRuleFire md' :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.RecRuleFire.inert => Ix.Kernel.RecRuleFire.inert
  | Ix.Kernel.RecRuleFire.plain => Ix.Kernel.RecRuleFire.plain
  | Ix.Kernel.RecRuleFire.nested lvls pins => Ix.Kernel.RecRuleFire.nested lvls (List.map (Ix.Cert.Rename.expr σ) pins) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.recRuleFire

/-- info: def Ix.Cert.Rename.recRule : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.RecRule md → Ix.Kernel.RecRule md' :=
fun {md md'} σ r =>
  { ctor := σ r.ctor, nfields := r.nfields, ctorParams := r.ctorParams, fire := Ix.Cert.Rename.recRuleFire σ r.fire,
    rhs := Ix.Cert.Rename.expr σ r.rhs, k := r.k, eta := r.eta, paramsBlind := r.paramsBlind } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.recRule

/-- info: def Ix.Cert.Rename.indCaps : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.IndCaps md → Ix.Kernel.IndCaps md' :=
fun {md md'} σ c =>
  { eta := c.eta, etaCtor := Option.map σ c.etaCtor, etaParams := c.etaParams, etaFields := c.etaFields,
    unitlike := c.unitlike, unitParams := c.unitParams, ruleK := c.ruleK, sortZ := c.sortZ } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.indCaps

/-- info: def Ix.Cert.Rename.projTable : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.ProjTable md → Ix.Kernel.ProjTable md' :=
fun {md md'} σ t =>
  { structName := σ t.structName, levelParams := t.levelParams, numParams := t.numParams, ctor := σ t.ctor,
    numFields := t.numFields, structSort := t.structSort, bodies := Array.map (Ix.Cert.Rename.expr σ) t.bodies,
    guards := t.guards, off := t.off } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.projTable

/-- info: def Ix.Cert.Rename.constantInfo : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.ConstantInfo md → Ix.Kernel.ConstantInfo md' :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.ConstantInfo.axiomInfo v => Ix.Kernel.ConstantInfo.axiomInfo (Ix.Cert.Rename.constantVal σ v)
  | Ix.Kernel.ConstantInfo.defnInfo v e h =>
    Ix.Kernel.ConstantInfo.defnInfo (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e) h
  | Ix.Kernel.ConstantInfo.thmInfo v e =>
    Ix.Kernel.ConstantInfo.thmInfo (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e)
  | Ix.Kernel.ConstantInfo.indInfo v caps =>
    Ix.Kernel.ConstantInfo.indInfo (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.indCaps σ caps)
  | Ix.Kernel.ConstantInfo.ctorInfo v nP nF => Ix.Kernel.ConstantInfo.ctorInfo (Ix.Cert.Rename.constantVal σ v) nP nF
  | Ix.Kernel.ConstantInfo.recInfo v major pre rules =>
    Ix.Kernel.ConstantInfo.recInfo (Ix.Cert.Rename.constantVal σ v) major pre
      (List.map (Ix.Cert.Rename.recRule σ) rules)
  | Ix.Kernel.ConstantInfo.projInfo tbl => Ix.Kernel.ConstantInfo.projInfo (Ix.Cert.Rename.projTable σ tbl) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.constantInfo

/-- info: def Ix.Cert.Rename.declaration : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.Declaration md → Ix.Kernel.Declaration md' :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.Declaration.axiomDecl v => Ix.Kernel.Declaration.axiomDecl (Ix.Cert.Rename.constantVal σ v)
  | Ix.Kernel.Declaration.defnDecl v e h =>
    Ix.Kernel.Declaration.defnDecl (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e) h
  | Ix.Kernel.Declaration.thmDecl v e =>
    Ix.Kernel.Declaration.thmDecl (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e)
  | Ix.Kernel.Declaration.opaqueDecl v e =>
    Ix.Kernel.Declaration.opaqueDecl (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e)
  | Ix.Kernel.Declaration.basisDecl k => Ix.Kernel.Declaration.basisDecl k
  | Ix.Kernel.Declaration.indDecl block nP =>
    Ix.Kernel.Declaration.indDecl (List.map (Ix.Cert.Rename.constantInfo σ) block) nP
  | Ix.Kernel.Declaration.quotDecl k v => Ix.Kernel.Declaration.quotDecl k (Ix.Cert.Rename.constantVal σ v) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.declaration

/-- info: def Ix.Cert.Rename.evidences : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.Evidences md → Ix.Kernel.Evidences md' :=
fun {md md'} σ ev =>
  List.map
    (fun x =>
      match x with
      | (r, es) => (r, List.map (Ix.Cert.Rename.evidence σ) es))
    ev -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.evidences

/-- info: def Ix.Cert.Rename.evidence : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') →
    Ix.Kernel.Evidence (Ix.Kernel.Key md × Ix.Kernel.Expr md) →
      Ix.Kernel.Evidence (Ix.Kernel.Key md' × Ix.Kernel.Expr md') :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.Evidence.defeq => Ix.Kernel.Evidence.defeq
  | Ix.Kernel.Evidence.proof (k, v) => Ix.Kernel.Evidence.proof (σ k, Ix.Cert.Rename.expr σ v) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.evidence

/-- info: def Ix.Cert.Rename.env : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.Env md → Ix.Kernel.Env md' :=
fun {md md'} σ e => { consts := List.map (Ix.Cert.Rename.constantInfo σ) e.consts } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.env

/-- info: @Ix.Cert.Keys.expr.eq_def : ∀ {md : Ix.Kernel.Mode} (x : Ix.Kernel.Expr md),
  Ix.Cert.Keys.expr x =
    match x with
    | Ix.Kernel.Expr.fvar idx t => Ix.Cert.Keys.expr t
    | Ix.Kernel.Expr.const n us => [n]
    | f.app a => Ix.Cert.Keys.expr f ++ Ix.Cert.Keys.expr a
    | t.lam b m => Ix.Cert.Keys.expr t ++ Ix.Cert.Keys.expr b
    | t.forallE b m => Ix.Cert.Keys.expr t ++ Ix.Cert.Keys.expr b
    | t.letE v b l => Ix.Cert.Keys.expr t ++ Ix.Cert.Keys.expr v ++ Ix.Cert.Keys.expr b
    | Ix.Kernel.Expr.proj n idx e => n :: Ix.Cert.Keys.expr e
    | x => [] -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Keys.expr.eq_def

/-- info: def Ix.Cert.Keys.constantVal : {md : Ix.Kernel.Mode} → Ix.Kernel.ConstantVal md → List (Ix.Kernel.Key md) :=
fun {md} cv => cv.name :: Ix.Cert.Keys.expr cv.type -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.constantVal

/-- info: def Ix.Cert.Keys.recRule : {md : Ix.Kernel.Mode} → Ix.Kernel.RecRule md → List (Ix.Kernel.Key md) :=
fun {md} r =>
  r.ctor :: Ix.Cert.Keys.expr r.rhs ++
    match r.fire with
    | Ix.Kernel.RecRuleFire.nested lvls pins => List.flatMap Ix.Cert.Keys.expr pins
    | x => [] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.recRule

/-- info: def Ix.Cert.Keys.constantInfo : {md : Ix.Kernel.Mode} → Ix.Kernel.ConstantInfo md → List (Ix.Kernel.Key md) :=
fun {md} x =>
  match x with
  | Ix.Kernel.ConstantInfo.axiomInfo v => Ix.Cert.Keys.constantVal v
  | Ix.Kernel.ConstantInfo.defnInfo v e hint => Ix.Cert.Keys.constantVal v ++ Ix.Cert.Keys.expr e
  | Ix.Kernel.ConstantInfo.thmInfo v e => Ix.Cert.Keys.constantVal v ++ Ix.Cert.Keys.expr e
  | Ix.Kernel.ConstantInfo.indInfo v caps => Ix.Cert.Keys.constantVal v ++ caps.etaCtor.toList
  | Ix.Kernel.ConstantInfo.ctorInfo v numParams numFields => Ix.Cert.Keys.constantVal v
  | Ix.Kernel.ConstantInfo.recInfo v majorIdx rulePrefix rules =>
    Ix.Cert.Keys.constantVal v ++ List.flatMap Ix.Cert.Keys.recRule rules
  | Ix.Kernel.ConstantInfo.projInfo tbl =>
    tbl.structName :: tbl.ctor :: List.flatMap Ix.Cert.Keys.expr tbl.bodies.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.constantInfo

/-- info: def Ix.Cert.Keys.declaration : {md : Ix.Kernel.Mode} → Ix.Kernel.Declaration md → List (Ix.Kernel.Key md) :=
fun {md} x =>
  match x with
  | Ix.Kernel.Declaration.axiomDecl v => Ix.Cert.Keys.constantVal v
  | Ix.Kernel.Declaration.defnDecl v e hint => Ix.Cert.Keys.constantVal v ++ Ix.Cert.Keys.expr e
  | Ix.Kernel.Declaration.thmDecl v e => Ix.Cert.Keys.constantVal v ++ Ix.Cert.Keys.expr e
  | Ix.Kernel.Declaration.opaqueDecl v e => Ix.Cert.Keys.constantVal v ++ Ix.Cert.Keys.expr e
  | Ix.Kernel.Declaration.basisDecl kind => []
  | Ix.Kernel.Declaration.indDecl block numParams => List.flatMap Ix.Cert.Keys.constantInfo block
  | Ix.Kernel.Declaration.quotDecl kind v => Ix.Cert.Keys.constantVal v -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.declaration

/-- info: def Ix.Cert.Keys.evidences : {md : Ix.Kernel.Mode} → Ix.Kernel.Evidences md → List (Ix.Kernel.Key md) :=
fun {md} ev =>
  List.flatMap
    (fun x =>
      match x with
      | (fst, es) =>
        List.flatMap
          (fun x =>
            match x with
            | Ix.Kernel.Evidence.defeq => []
            | Ix.Kernel.Evidence.proof (k, v) => k :: Ix.Cert.Keys.expr v)
          es)
    ev -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.evidences

/-- info: def Ix.Cert.InputKey : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Evidences md → Array (Ix.Kernel.Declaration md) → Ix.Kernel.Key md → Prop :=
fun {md} ev ds n => (∃ d, d ∈ ds ∧ n ∈ Ix.Cert.Keys.declaration d) ∨ n ∈ Ix.Cert.Keys.evidences ev -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.InputKey

/-- info: def Ix.Cert.keyIds : {md : Ix.Kernel.Mode} → Ix.Kernel.Key md → List md.Id :=
fun {md} x => Ix.Kernel.Key.brecOn x Ix.Cert.keyIds._f -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.keyIds

/-- info: def Ix.Cert.InputId : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Evidences md → Array (Ix.Kernel.Declaration md) → md.Id → Prop :=
fun {md} ev ds i => ∃ k, Ix.Cert.InputKey ev ds k ∧ i ∈ Ix.Cert.keyIds k -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.InputId

/-- info: def Ix.Kernel.Key.map : {md md' : Ix.Kernel.Mode} → (md.Id → md'.Id) → Ix.Kernel.Key md → Ix.Kernel.Key md' :=
fun {md md'} f x => Ix.Kernel.Key.brecOn x (Ix.Kernel.Key.map._f f) -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.Key.map

/-- info: def Ix.Cert.RenamingHyp : (Ix.Kernel.Mode.source.Id → Ix.Kernel.Mode.anon.Id) →
  Ix.Kernel.Evidences Ix.Kernel.Mode.source → Array (Ix.Kernel.Declaration Ix.Kernel.Mode.source) → Prop :=
fun f ev ds => ∀ (i j : Ix.Kernel.Mode.source.Id), Ix.Cert.InputId ev ds i → Ix.Cert.InputId ev ds j → f i = f j → i = j -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RenamingHyp

-- Step 6: failures are structured (`Ix.Kernel.CheckError md`: a verdict and a
-- message of prose and keys), so the lemma maps a failure's keys
-- (`Rename.result`, `CheckError.mapKeys`) instead of comparing the verdict
-- kind and the position only; `ErrorKind` and `verdict` went.
-- Step 6b: a prose part carries the failure's display (`FailureDisplay`: the
-- terms and binders `.meta` and `.source` print), a subsingleton, so two
-- failures that differ only there are equal; a renaming drops it (the other
-- mode's display is the empty one, equal to any).
/-- info: def Ix.Kernel.MsgPart.mapKeys : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.MsgPart md → Ix.Kernel.MsgPart md' :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.MsgPart.text s display => Ix.Kernel.MsgPart.text s
  | Ix.Kernel.MsgPart.key k => Ix.Kernel.MsgPart.key (σ k)
  | Ix.Kernel.MsgPart.nat n => Ix.Kernel.MsgPart.nat n -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.MsgPart.mapKeys

/-- info: def Ix.Kernel.Msg.mapKeys : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.Msg md → Ix.Kernel.Msg md' :=
fun {md md'} σ m => List.map (Ix.Kernel.MsgPart.mapKeys σ) m -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.Msg.mapKeys

/-- info: def Ix.Kernel.CheckError.mapKeys : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') → Ix.Kernel.CheckError md → Ix.Kernel.CheckError md' :=
fun {md md'} σ x =>
  match x with
  | Ix.Kernel.CheckError.notImplemented m => Ix.Kernel.CheckError.notImplemented (Ix.Kernel.Msg.mapKeys σ m)
  | Ix.Kernel.CheckError.invalid m => Ix.Kernel.CheckError.invalid (Ix.Kernel.Msg.mapKeys σ m)
  | Ix.Kernel.CheckError.internal m => Ix.Kernel.CheckError.internal (Ix.Kernel.Msg.mapKeys σ m) -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.CheckError.mapKeys

/-- info: def Ix.Cert.Rename.result : {md md' : Ix.Kernel.Mode} →
  (Ix.Kernel.Key md → Ix.Kernel.Key md') →
    Except (Ix.Kernel.CheckError md × Nat) (Ix.Kernel.Env md) →
      Except (Ix.Kernel.CheckError md' × Nat) (Ix.Kernel.Env md') :=
fun {md md'} σ x =>
  match x with
  | Except.ok e => Except.ok (Ix.Cert.Rename.env σ e)
  | Except.error (e, i) => Except.error (Ix.Kernel.CheckError.mapKeys σ e, i) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.result

/-- info: def Ix.Cert.RenamingLemma : Prop :=
∀ (f : Ix.Kernel.Mode.source.Id → Ix.Kernel.Mode.anon.Id) (ev : Ix.Kernel.Evidences Ix.Kernel.Mode.source)
  (ds : Array (Ix.Kernel.Declaration Ix.Kernel.Mode.source)),
  Ix.Cert.RenamingHyp f ev ds →
    Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified (Ix.Cert.Rename.evidences (Ix.Kernel.Key.map f) ev)
        (Array.map (Ix.Cert.Rename.declaration (Ix.Kernel.Key.map f)) ds) =
      Ix.Cert.Rename.result (Ix.Kernel.Key.map f) (Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified ev ds) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RenamingLemma

/-- info: def Ix.Cert.groundSplit : Ix.Environment → Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.GroundError :=
fun env =>
  have outRefs := Ix.GraphM.envSerial env;
  have inRefs :=
    Std.HashMap.fold
      (fun m n refs =>
        Std.HashSet.fold
          (fun m r =>
            Std.HashMap.alter m r fun x =>
              match x with
              | some s => some (Std.HashSet.insert s n)
              | none => some (Std.HashSet.insert ∅ n))
          m refs)
      ∅ outRefs;
  have ungrounded := Ix.groundConsts env inRefs;
  if Std.HashMap.isEmpty ungrounded = true then (outRefs, ungrounded)
  else
    (Std.HashMap.fold
        (fun m n refs =>
          if Std.HashMap.contains ungrounded n = true then m
          else
            Std.HashMap.insert m n
              (Std.HashSet.fold
                (fun s r => if Std.HashMap.contains ungrounded r = true then s else Std.HashSet.insert s r) ∅ refs))
        ∅ outRefs,
      ungrounded) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.groundSplit

/-- info: def Ix.Cert.groundedRefs : Ix.Environment → Ix.Map Ix.Name (Ix.Set Ix.Name) :=
fun env => (Ix.Cert.groundSplit env).fst -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.groundedRefs

/-- info: def Ix.Cert.blocksOf : Ix.Environment → Ix.CondensedBlocks :=
fun env => Ix.CondenseM.run (Ix.Cert.groundedRefs env) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.blocksOf

/-- info: structure Ix.Cert.Failures : Type
number of parameters: 0
fields:
  Ix.Cert.Failures.ungrounded : Std.HashMap Ix.Name String :=
    ∅
  Ix.Cert.Failures.blocks : Std.HashMap Ix.Name String :=
    ∅
constructor:
  Ix.Cert.Failures.mk (ungrounded blocks : Std.HashMap Ix.Name String) : Ix.Cert.Failures -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Failures

-- CQ2.27 (owner, 2026-10-15): `compileReport` checks its own result and
-- fails, with no artifact, on any inconsistency. The former body of
-- `compileReport` is `compileUnchecked`, verbatim; `compileReport` runs it,
-- then `checkReport`: coverage (`uncovered`: every input constant published
-- or listed as failed, exactly one of the two) and authenticity
-- (`unauthentic`: every record and blob at `Address.admissionHash` of its
-- stored bytes). On a consistent run the result is `compileUnchecked`'s, so
-- the bytes do not change. `Failures.failed` moved here from
-- `Ix.Cert.Statement`, unchanged, because the check reads it.
--
-- CQ2.14: the driver is the pure wave fold `Ix.CompileM.compileEnvFold`, the
-- one driver of `compile` and of the IO pipeline (`compileDecoratedConsts`);
-- the queue drivers `compileEnvAux` (sequential, live state) and
-- `compileEnvParallelAux` (waves applied in completion order) go. Only the
-- driver's name changes in this body; its arguments are the same.
/-- info: def Ix.Cert.compileUnchecked : Ix.Environment → Except String (Ixon.Env × Ix.Cert.Failures) :=
fun env =>
  have env := { consts := env.consts };
  have split := Ix.Cert.groundSplit env;
  do
  let __x ← Ix.CompileM.compileEnvFold env (Ix.CondenseM.run split.fst)
  match __x with
    | (ixe, fst, cenv) =>
      have ungrounded :=
        Std.HashMap.fold (fun m n e => m.insert n (e.refusal (Std.HashMap.contains split.snd))) ∅ split.snd;
      pure (ixe, { ungrounded := ungrounded, blocks := cenv.ungrounded }) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.compileUnchecked

/-- info: def Ix.Cert.uncovered : Ix.Environment → Ixon.Env → Ix.Cert.Failures → List Ix.Name :=
fun env ixe failures => List.filter (fun n => ixe.named.contains n == failures.failed n) env.consts.keys -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.uncovered

/-- info: def Ix.Cert.unauthentic : Ixon.Env → List Address :=
fun ixe =>
  List.map (fun x => x.fst)
      (List.filter
        (fun x =>
          match x with
          | (a, lc) => a != Address.admissionHash lc.rawBytes)
        ixe.consts.toList) ++
    List.map (fun x => x.fst)
      (List.filter
        (fun x =>
          match x with
          | (a, bytes) => a != Address.admissionHash bytes)
        ixe.blobs.toList) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.unauthentic

-- Route A, B4 (coordinator decision, 2026-10-16): `checkReport` gained a
-- third check, acyclic references (`referenceCycle`: the stored records'
-- reference graph, `recordGraph`, through `Ix.Compile.Canon.condensation`;
-- a component of more than one record, or a record referencing itself, is
-- an error). Each record's `refs` table and projection block are read
-- without its expressions (`RecordRefs.getRefs`, proved to be
-- `Ixon.getConstant` with the rest forgotten: `Ix.Cert.RefsRead`), on tasks
-- over the record list (`parMap`), and the edges are resolved on tasks too.
-- Re-frozen here: `checkReport` and `checkReport_ok` (a third conjunct);
-- new: `storedRecord`, `refOwner`, `storedRefs`, `recordTasks`, `parMap`,
-- `recordRefs`, `recordGraph`, `referenceCycle`, `RecordRefs.lazyRefs`,
-- `RecordRefs.refsAt`, `RecordRefs.getRefs`. On a consistent run the
-- result is unchanged.
/-- info: def Ix.Cert.storedRecord : Ixon.Env → Address → Option Ixon.Constant :=
fun ixe a => (ixe.consts.get? a).bind fun x => x.get? -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.storedRecord

/-- info: def Ix.Cert.refOwner : Address → Ixon.Constant → Address :=
fun a c =>
  match c.info with
  | Ixon.ConstantInfo.dPrj p => p.block
  | Ixon.ConstantInfo.iPrj p => p.block
  | Ixon.ConstantInfo.rPrj p => p.block
  | Ixon.ConstantInfo.cPrj p => p.block
  | x => a -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.refOwner

/-- info: def Ix.Cert.storedRefs : Ixon.Env → Address → Option (Array Address × Address) :=
fun ixe a => (ixe.consts.get? a).bind (Ix.Cert.RecordRefs.lazyRefs a) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.storedRefs

/-- info: def Ix.Cert.RecordRefs.lazyRefs : Address → Ixon.LazyConstant → Option (Array Address × Address) :=
fun a lc =>
  match lc.cache with
  | some c => some (c.refs, Ix.Cert.refOwner a c)
  | none =>
    Option.map
      (fun x =>
        match x with
        | (refs, block) => (refs, block.getD a))
      (Ix.Cert.RecordRefs.refsAt lc.buf lc.off) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RecordRefs.lazyRefs

/-- info: def Ix.Cert.RecordRefs.refsAt : ByteArray → Nat → Option (Array Address × Option Address) :=
fun buf off =>
  match EStateM.run Ix.Cert.RecordRefs.getRefs { idx := off, bytes := buf } with
  | EStateM.Result.ok r a => some r
  | EStateM.Result.error a a_1 => none -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RecordRefs.refsAt

/-- info: def Ix.Cert.RecordRefs.getRefs : Ixon.GetM (Array Address × Option Address) :=
do
  let block ← Ix.Cert.RecordRefs.skipInfo
  let __do_lift ← Ixon.getTagN 0
  have numSharing : Nat := __do_lift.value.toNat
  Ix.Cert.RecordRefs.skipMany Ix.Cert.RecordRefs.skipExpr numSharing
  let __do_lift ← Ixon.getTagN 0
  have numRefs : Nat := __do_lift.value.toNat
  let refs ← Ixon.getArray Ixon.Serialize.get numRefs
  let __do_lift ← Ixon.getTagN 0
  have numUnivs : Nat := __do_lift.value.toNat
  Ix.Cert.RecordRefs.skipMany Ix.Cert.RecordRefs.skipUniv numUnivs
  pure (refs, block) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RecordRefs.getRefs

/-- info: def Ix.Cert.recordTasks : Nat :=
256 -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recordTasks

/-- info: def Ix.Cert.parMap : {α β : Type} → (α → β) → Array α → Array β :=
fun {α β} f xs =>
  have n := xs.size;
  have size := (n + Ix.Cert.recordTasks - 1) / Ix.Cert.recordTasks;
  have chunks := if (size == 0) = true then 0 else (n + size - 1) / size;
  (Array.map Task.get
      (Array.map (fun c => Task.spawn fun x => Array.map f (xs.extract (c * size) ((c + 1) * size)))
        (Array.range chunks))).flatten -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.parMap

/-- info: def Ix.Cert.recordRefs : Array (Address × Option Ixon.LazyConstant) → Array (Option (Array Address × Address)) :=
fun recs =>
  Ix.Cert.parMap
    (fun x =>
      match x with
      | (a, lc) => lc.bind (Ix.Cert.RecordRefs.lazyRefs a))
    recs -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recordRefs

/-- info: def Ix.Cert.recordGraph : Ixon.Env → Array Address × Array (Array Nat) :=
fun ixe =>
  have addrs := ixe.consts.keys.toArray;
  have index := Std.HashMap.ofList addrs.toList.zipIdx;
  have info := Ix.Cert.recordRefs (Array.map (fun a => (a, ixe.consts.get? a)) addrs);
  have ownerAt := fun r => do
    let j ← index.get? r
    let __x ← info[j]?.join
    match __x with
      | (fst, o) => pure o;
  have adj :=
    Ix.Cert.parMap
      (fun x =>
        match x with
        | none => #[]
        | some (refs, snd) => Array.filterMap (fun r => ownerAt r >>= index.get?) refs)
      info;
  (addrs, adj) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recordGraph

/-- info: def Ix.Cert.referenceCycle : Ixon.Env → Option (List Address) :=
fun ixe =>
  match Ix.Cert.recordGraph ixe with
  | (addrs, adj) =>
    have cyclic := fun c => c.size != 1 || c.any fun i => (adj[i]?.getD #[]).contains i;
    match Ix.Compile.Canon.condensation adj with
    | none => some []
    | some C => Option.map (fun c => List.filterMap (fun x => addrs[x]?) c.toList) (List.find? cyclic C.comps.toList) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.referenceCycle

/-- info: def Ix.Cert.checkReport : Ix.Environment → Ixon.Env × Ix.Cert.Failures → Except String Unit :=
fun env out =>
  match Ix.Cert.uncovered env out.fst out.snd, Ix.Cert.unauthentic out.fst with
  | [], [] =>
    match Ix.Cert.referenceCycle out.fst with
    | none => Except.ok ()
    | some cycle =>
      Except.error
        (toString "compileReport: reference check failed: " ++ toString cycle.length ++
            toString " stored record(s) on a reference cycle; first: " ++
          toString (List.take 5 cycle))
  | n :: rest, x =>
    Except.error
      (toString "compileReport: coverage check failed: " ++ toString (rest.length + 1) ++
                toString " input constant(s) are published and listed as failed, or neither; first: " ++
              toString n.pretty ++
            toString " (" ++
          toString (if out.snd.failed n = true then "published and failed" else "neither published nor failed") ++
        toString ")")
  | [], a :: rest =>
    Except.error
      (toString "compileReport: authenticity check failed: " ++ toString (rest.length + 1) ++
          toString " record(s) or blob(s) are not stored at the admission hash of their bytes; first: " ++
        toString a) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.checkReport

/-- info: def Ix.Cert.compileReport : Ix.Environment → Except String (Ixon.Env × Ix.Cert.Failures) :=
fun env => do
  let out ← Ix.Cert.compileUnchecked env
  Ix.Cert.checkReport env out
  pure out -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.compileReport

/-- info: def Ix.Cert.compile : Ix.Environment → Except String Ixon.Env :=
fun env => Prod.fst <$> Ix.Cert.compileReport env -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.compile

/-! ## The theorems -/

/-- info: Ix.Cert.sourceConsistent : Ix.Cert.SourceConsistent -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceConsistent

/-- info: Ix.Cert.ixonConsistent : Ix.Cert.IxonConsistent -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.ixonConsistent

/-- info: Ix.Cert.ixonAuthentic : Ix.Cert.IxonAuthentic -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.ixonAuthentic

/-- info: Ix.Cert.sourceValueSound : Ix.Cert.SourceValueSound -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceValueSound

/-- info: Ix.Cert.ixonValueSound : Ix.Cert.IxonValueSound -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.ixonValueSound

/-- info: @Ix.Cert.Commutes.alias : ∀
  {τ : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source → Option (Ix.Kernel.Expr Ix.Kernel.Mode.anon)}
  {envS : Ix.Kernel.Env Ix.Kernel.Mode.source} {envA : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Cert.Commutes τ envS envA →
    ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] (M : Ix.Cert.ValueModel V envA),
      ∃ N,
        (∀ (c : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
            c ∈ envS.consts →
              ∀ (t : Ix.Kernel.Expr Ix.Kernel.Mode.anon),
                τ c = some t →
                  ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
                    Ix.Kernel.Denotes M.cval envA φ ρ t (N.cval c.name φ)) ∧
          ∀ (c₁ : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
            c₁ ∈ envS.consts →
              ∀ (c₂ : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
                c₂ ∈ envS.consts →
                  ∀ (t : Ix.Kernel.Expr Ix.Kernel.Mode.anon),
                    τ c₁ = some t →
                      τ c₂ = some t → ∀ (φ : Ix.Kernel.LevelParam → Nat), N.cval c₁.name φ = N.cval c₂.name φ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Commutes.alias

-- CQP.3: the Source theorems at the compiler's grouping.
/-- info: Ix.Cert.sourceConsistent_blocksOf : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] (env : Ix.Environment)
  (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source),
  Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.source),
      ci ∈ envS.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceConsistent_blocksOf

/-- info: Ix.Cert.sourceValueSound_blocksOf : ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment)
  (envS : Ix.Kernel.Env Ix.Kernel.Mode.source),
  Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
    ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V], Nonempty (Ix.Cert.ValueModel V envS) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceValueSound_blocksOf

/-- info: Ix.Cert.closureCorrect : Ix.Cert.ClosureCorrect -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.closureCorrect

-- CQP.1: the definitional steps of `CompileAuthentic`.
/-- info: Ix.Cert.blockAddr_mk' (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta)
  (projections : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta)) :
  (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockAddr =
    Address.blake3Pure (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.blockAddr_mk'

/-- info: Ix.Cert.storedRecord_authentic (bytes : ByteArray) :
  Address.admissionHash bytes = Address.blake3Pure { buf := bytes, len := bytes.size }.rawBytes -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.storedRecord_authentic

-- CQP.2: the bridges between the two hypotheses, under `CompileCovers`.
/-- info: Ix.Cert.CompileCorrect.published : Ix.Cert.CompileCovers →
  Ix.Cert.CompileCorrect →
    ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
      (ixe : Ixon.Env),
      Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
        Ix.Cert.compile env = Except.ok ixe → Ix.Cert.Published ixe sub → Ix.Cert.IxonCommutes ixe sub envS -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.CompileCorrect.published

/-- info: Ix.Cert.CompileCorrect.of_published : Ix.Cert.CompileCovers →
  (∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
      (ixe : Ixon.Env),
      Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
        Ix.Cert.compile env = Except.ok ixe → Ix.Cert.Published ixe sub → Ix.Cert.IxonCommutes ixe sub envS) →
    Ix.Cert.CompileCorrect -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.CompileCorrect.of_published

/-- info: Ix.Cert.noFailure_iff : ∀ (failures : Ix.Cert.Failures) (sub : Ix.Environment),
  Ix.Cert.NoFailure failures sub ↔ (sub.consts.keys.all fun n => !failures.failed n) = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.noFailure_iff

-- CQ2.27: coverage and authenticity, by construction.
/-- info: @Ix.Cert.compileReport_ok : ∀ {env : Ix.Environment} {out : Ixon.Env × Ix.Cert.Failures},
  Ix.Cert.compileReport env = Except.ok out →
    Ix.Cert.compileUnchecked env = Except.ok out ∧ Ix.Cert.checkReport env out = Except.ok () -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.compileReport_ok

/-- info: @Ix.Cert.checkReport_ok : ∀ {env : Ix.Environment} {out : Ixon.Env × Ix.Cert.Failures},
  Ix.Cert.checkReport env out = Except.ok () →
    Ix.Cert.uncovered env out.fst out.snd = [] ∧
      Ix.Cert.unauthentic out.fst = [] ∧ Ix.Cert.referenceCycle out.fst = none -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.checkReport_ok

/-- info: Ix.Cert.compileCovers : Ix.Cert.CompileCovers -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.compileCovers

/-- info: Ix.Cert.compileAuthentic : Ix.Cert.CompileAuthentic -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.compileAuthentic

/-- info: Ix.Cert.compileCorrect_iff_published : Ix.Cert.CompileCorrect ↔
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
    (ixe : Ixon.Env),
    Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
      Ix.Cert.compile env = Except.ok ixe → Ix.Cert.Published ixe sub → Ix.Cert.IxonCommutes ixe sub envS -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.compileCorrect_iff_published

/-! ## Axioms -/

/-- info: 'Ix.Cert.sourceConsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceConsistent

/-- info: 'Ix.Cert.ixonConsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonConsistent

/-- info: 'Ix.Cert.ixonAuthentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonAuthentic

/-- info: 'Ix.Cert.sourceValueSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceValueSound

/-- info: 'Ix.Cert.ixonValueSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonValueSound

/-- info: 'Ix.Cert.ixonConsistentRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonConsistentRef

/-- info: 'Ix.Cert.ixonValueSoundRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonValueSoundRef

/-- info: 'Ix.Cert.ixonAccepts_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ixonAccepts_ref

/-- info: 'Ix.Cert.Commutes.alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Commutes.alias

/-- info: 'Ix.Cert.sourceConsistent_blocksOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceConsistent_blocksOf

/-- info: 'Ix.Cert.sourceValueSound_blocksOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceValueSound_blocksOf

/-- info: 'Ix.Cert.closureCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.closureCorrect

/-- info: 'Ix.Cert.blockAddr_mk'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.blockAddr_mk'

/-- info: 'Ix.Cert.storedRecord_authentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.storedRecord_authentic

/-- info: 'Ix.Cert.CompileAuthentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileAuthentic

/-- info: 'Ix.Cert.CompileCorrect.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileCorrect.published

/-- info: 'Ix.Cert.CompileCorrect.of_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileCorrect.of_published

/-- info: 'Ix.Cert.noFailure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.noFailure_iff

/-- info: 'Ix.Cert.CompileCovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileCovers

/-- info: 'Ix.Cert.compileReport_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compileReport_ok

/-- info: 'Ix.Cert.checkReport_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.checkReport_ok

/-- info: 'Ix.Cert.compileCovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compileCovers

/-- info: 'Ix.Cert.compileAuthentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compileAuthentic

/-- info: 'Ix.Cert.compileCorrect_iff_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compileCorrect_iff_published

/-- info: 'Ix.Cert.SourceAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.SourceAccepts

/-- info: 'Ix.Cert.IxonAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.IxonAccepts

/-- info: 'Ix.Cert.reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.reading

/-- info: 'Ix.Cert.Commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Commutes

/-- info: 'Ix.Cert.ClosureCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.ClosureCorrect

/-- info: 'Ix.Cert.RenamingLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.RenamingLemma

/-- info: 'Ix.Cert.blocksOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.blocksOf

/-- info: 'Ix.CompileCert.Canon.condensation_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.condensation_isSome

/-- info: 'Ix.Cert.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compile

/-- info: 'Ix.Cert.compileReport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compileReport

/-- info: 'Ix.Cert.CompileCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileCorrect

/-! ## Component theorems: universes

The compiler canonicalizes every universe it stores (`Ixon.canonUniv`, through
the block memo `Ix.CompileM.canonUnivCached`). Canonicalization preserves the
value of a universe under every valuation, with no premise; the memo returns
exactly the canonicalizer's output; and the certified reader's reading of a
canonical universe has the raw universe's value over positional level
parameters. Every lemma behind them is audited in
`Ix.CompileCert.UniverseAudit`. -/

/-- info: Ix.CompileCert.CanonUnivEmit.canonUniv_eval (ρ : UInt64 → Nat) (level : Ixon.Univ) :
  Ix.CompileCert.univEval ρ (Ixon.canonUniv level) = Ix.CompileCert.univEval ρ level -/
#guard_msgs (whitespace := lax) in
#check Ix.CompileCert.CanonUnivEmit.canonUniv_eval

/-- info: Ix.CompileCert.CanonUnivScope.convCanon_eval (param : Nat → Ix.Kernel.LevelParam) (φ : Ix.Kernel.LevelParam → Nat)
  (source : Ixon.Univ) :
  Ix.Kernel.Level.eval φ (Ix.Kernel.Reader.convUniv param (Ixon.canonUniv source)) =
    Ix.CompileCert.univEval (fun index => φ (param index.toNat)) source -/
#guard_msgs (whitespace := lax) in
#check Ix.CompileCert.CanonUnivScope.convCanon_eval

/-- info: 'Ix.CompileCert.CanonUnivEmit.canonUniv_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.CanonUnivEmit.canonUniv_eval

/-- info: 'Ix.CompileCert.CanonUnivScope.convCanon_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.CanonUnivScope.convCanon_eval

/-- info: 'Ix.CompileCert.CanonUnivCache.canonUnivCached_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.CanonUnivCache.canonUnivCached_correct

/-! ## The `CanonM` correspondence (`Ix.Cert.Canon`)

What ties the shared `Ix.Environment` to Lean's: the cache-free
specification of `Ix.CanonM` (`nameS`, `levelS`, `exprS`, `constS`), the
direct reading of Lean's terms (`leanName`, `leanLevel`, `leanExpr`,
`leanPos`), and the cache-free universe compiler (`compileUnivS`).
`CanonMCorrect` and `CanonChunkCorrect` (C1) are **proved** (`canonMCorrect`,
`canonChunkCorrect`), from every state: since CQ2.26 `Ix.CanonM` confirms
every memo hit (`withPtrEq`) against an entry that carries its proof, has no
hash-keyed cache, and has a total `canonSyntax`. So `ingressExpr_canonExpr`
holds without a hypothesis. CQ2.26 re-froze this section: `Reachable` is
gone (C1 holds from every state, which is stronger), `CanonMCorrect` is
stated over every state, and `ingressExpr_canonExpr` lost its two premises.
The universe bridge from Lean is proved (`universeBridge`, under the wire's
bound only). CQ2.25's ingress part re-froze this section: `Numbering.pos`
compares names structurally (`Ix.Name.beqRaw`), so `HashEqAgrees` is gone,
`numbering_nameS` and `UniverseBridge` lost that premise and
`lower_eq_compileUnivS` its `agree` premise, and `compileUnivS` finds a
parameter structurally (stronger, every one). The proved theorems are at the
three standard axioms or fewer. -/

/-- info: Ix.Cert.Canon.nameS.eq_def : ∀ (x : Lean.Name),
  Ix.Cert.Canon.nameS x =
    match x with
    | Lean.Name.anonymous => Ix.Name.mkAnon
    | p.str s => (Ix.Cert.Canon.nameS p).mkStr s
    | p.num n => (Ix.Cert.Canon.nameS p).mkNat n -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.nameS.eq_def

/-- info: Ix.Cert.Canon.levelS.eq_def : ∀ (x : Lean.Level),
  Ix.Cert.Canon.levelS x =
    match x with
    | Lean.Level.zero => Ix.Level.mkZero
    | u.succ => (Ix.Cert.Canon.levelS u).mkSucc
    | u.max v => (Ix.Cert.Canon.levelS u).mkMax (Ix.Cert.Canon.levelS v)
    | u.imax v => (Ix.Cert.Canon.levelS u).mkIMax (Ix.Cert.Canon.levelS v)
    | Lean.Level.param n => Ix.Level.mkParam (Ix.Cert.Canon.nameS n)
    | Lean.Level.mvar m => Ix.Level.mkMvar (Ix.Cert.Canon.nameS m.name) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.levelS.eq_def

/-- info: Ix.Cert.Canon.exprS.eq_def : ∀ (x : Lean.Expr),
  Ix.Cert.Canon.exprS x =
    match x with
    | Lean.Expr.bvar i => Ix.Expr.mkBVar i
    | Lean.Expr.fvar x => Ix.Expr.mkFVar (Ix.Cert.Canon.nameS x.name)
    | Lean.Expr.mvar x => Ix.Expr.mkMVar (Ix.Cert.Canon.nameS x.name)
    | Lean.Expr.sort u => Ix.Expr.mkSort (Ix.Cert.Canon.levelS u)
    | Lean.Expr.const n us => Ix.Expr.mkConst (Ix.Cert.Canon.nameS n) (List.map Ix.Cert.Canon.levelS us).toArray
    | f.app a => (Ix.Cert.Canon.exprS f).mkApp (Ix.Cert.Canon.exprS a)
    | Lean.Expr.lam n t b bi => Ix.Expr.mkLam (Ix.Cert.Canon.nameS n) (Ix.Cert.Canon.exprS t) (Ix.Cert.Canon.exprS b) bi
    | Lean.Expr.forallE n t b bi =>
      Ix.Expr.mkForallE (Ix.Cert.Canon.nameS n) (Ix.Cert.Canon.exprS t) (Ix.Cert.Canon.exprS b) bi
    | Lean.Expr.letE n t v b nd =>
      Ix.Expr.mkLetE (Ix.Cert.Canon.nameS n) (Ix.Cert.Canon.exprS t) (Ix.Cert.Canon.exprS v) (Ix.Cert.Canon.exprS b) nd
    | Lean.Expr.lit l => Ix.Expr.mkLit l
    | Lean.Expr.mdata d e => Ix.Expr.mkMData (Ix.Cert.Canon.mdataS d) (Ix.Cert.Canon.exprS e)
    | Lean.Expr.proj s i e => Ix.Expr.mkProj (Ix.Cert.Canon.nameS s) i (Ix.Cert.Canon.exprS e) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.exprS.eq_def

/-- info: def Ix.Cert.Canon.constS : Lean.ConstantInfo → Ix.ConstantInfo :=
fun x =>
  match x with
  | Lean.ConstantInfo.axiomInfo v =>
    Ix.ConstantInfo.axiomInfo { cnst := Ix.Cert.Canon.constValS v.toConstantVal, isUnsafe := v.isUnsafe }
  | Lean.ConstantInfo.defnInfo v =>
    Ix.ConstantInfo.defnInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, value := Ix.Cert.Canon.exprS v.value, hints := v.hints,
        safety := v.safety, all := (List.map Ix.Cert.Canon.nameS v.all).toArray }
  | Lean.ConstantInfo.thmInfo v =>
    Ix.ConstantInfo.thmInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, value := Ix.Cert.Canon.exprS v.value,
        all := (List.map Ix.Cert.Canon.nameS v.all).toArray }
  | Lean.ConstantInfo.opaqueInfo v =>
    Ix.ConstantInfo.opaqueInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, value := Ix.Cert.Canon.exprS v.value, isUnsafe := v.isUnsafe,
        all := (List.map Ix.Cert.Canon.nameS v.all).toArray }
  | Lean.ConstantInfo.quotInfo v =>
    Ix.ConstantInfo.quotInfo { cnst := Ix.Cert.Canon.constValS v.toConstantVal, kind := v.kind }
  | Lean.ConstantInfo.inductInfo v =>
    Ix.ConstantInfo.inductInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, numParams := v.numParams, numIndices := v.numIndices,
        all := (List.map Ix.Cert.Canon.nameS v.all).toArray, ctors := (List.map Ix.Cert.Canon.nameS v.ctors).toArray,
        numNested := v.numNested, isRec := v.isRec, isUnsafe := v.isUnsafe, isReflexive := v.isReflexive }
  | Lean.ConstantInfo.ctorInfo v =>
    Ix.ConstantInfo.ctorInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, induct := Ix.Cert.Canon.nameS v.induct, cidx := v.cidx,
        numParams := v.numParams, numFields := v.numFields, isUnsafe := v.isUnsafe }
  | Lean.ConstantInfo.recInfo v =>
    Ix.ConstantInfo.recInfo
      { cnst := Ix.Cert.Canon.constValS v.toConstantVal, all := (List.map Ix.Cert.Canon.nameS v.all).toArray,
        numParams := v.numParams, numIndices := v.numIndices, numMotives := v.numMotives, numMinors := v.numMinors,
        rules :=
          (List.map
              (fun r => { ctor := Ix.Cert.Canon.nameS r.ctor, nfields := r.nfields, rhs := Ix.Cert.Canon.exprS r.rhs })
              v.rules).toArray,
        k := v.k, isUnsafe := v.isUnsafe } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.constS

/-- info: def Ix.Cert.Canon.CanonMCorrect : Prop :=
∀ (s : Ix.CanonM.CanonState),
  (∀ (n : Lean.Name), (StateT.run (Ix.CanonM.canonName n) s).run.fst = Ix.Cert.Canon.nameS n) ∧
    (∀ (l : Lean.Level), (StateT.run (Ix.CanonM.canonLevel l) s).run.fst = Ix.Cert.Canon.levelS l) ∧
      (∀ (e : Lean.Expr), (StateT.run (Ix.CanonM.canonExpr e) s).run.fst = Ix.Cert.Canon.exprS e) ∧
        ∀ (c : Lean.ConstantInfo), (StateT.run (Ix.CanonM.canonConst c) s).run.fst = Ix.Cert.Canon.constS c -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.CanonMCorrect

/-- info: def Ix.Cert.Canon.CanonChunkCorrect : Prop :=
∀ (chunk : Array (Lean.Name × Lean.ConstantInfo)),
  Ix.CanonM.canonChunk chunk =
    Array.map
      (fun x =>
        match x with
        | (n, c) => (Ix.Cert.Canon.nameS n, Ix.Cert.Canon.constS c))
      chunk -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.CanonChunkCorrect

/-- info: Ix.Cert.Canon.leanName.eq_def : ∀ (x : Lean.Name),
  Ix.Cert.Canon.leanName x =
    match x with
    | Lean.Name.anonymous => Ix.Kernel.Name.anonymous
    | p.str s => (Ix.Cert.Canon.leanName p).str s
    | p.num n => (Ix.Cert.Canon.leanName p).num n -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.leanName.eq_def

/-- info: Ix.Cert.Canon.leanLevel.eq_def : ∀ (σ : Lean.Name → Ix.Kernel.LevelParam) (x : Lean.Level),
  Ix.Cert.Canon.leanLevel σ x =
    match x with
    | Lean.Level.zero => pure Ix.Kernel.Level.zero
    | u.succ => do
      let __do_lift ← Ix.Cert.Canon.leanLevel σ u
      pure (Ix.Kernel.Level.succ __do_lift)
    | u.max v => do
      let __do_lift ← Ix.Cert.Canon.leanLevel σ u
      let __do_lift_1 ← Ix.Cert.Canon.leanLevel σ v
      pure (Ix.Kernel.Level.max __do_lift __do_lift_1)
    | u.imax v => do
      let __do_lift ← Ix.Cert.Canon.leanLevel σ u
      let __do_lift_1 ← Ix.Cert.Canon.leanLevel σ v
      pure (Ix.Kernel.Level.imax __do_lift __do_lift_1)
    | Lean.Level.param n => pure (Ix.Kernel.Level.param (σ n))
    | Lean.Level.mvar m => throw (Ix.LeanIngress.ExprError.levelMVar (Ix.Cert.Canon.leanName m.name)) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.leanLevel.eq_def

/-- info: Ix.Cert.Canon.leanExpr.eq_def : ∀ (σ : Lean.Name → Ix.Kernel.LevelParam) (x : Lean.Expr),
  Ix.Cert.Canon.leanExpr σ x =
    match x with
    | Lean.Expr.bvar i => pure (Ix.Kernel.Expr.mkBvar i)
    | Lean.Expr.fvar x => throw (Ix.LeanIngress.ExprError.fvar (Ix.Cert.Canon.leanName x.name))
    | Lean.Expr.mvar x => throw (Ix.LeanIngress.ExprError.mvar (Ix.Cert.Canon.leanName x.name))
    | Lean.Expr.sort u => do
      let __do_lift ← Ix.Cert.Canon.leanLevel σ u
      pure (Ix.Kernel.Expr.sort __do_lift)
    | Lean.Expr.const n us => do
      let __do_lift ← List.mapM (Ix.Cert.Canon.leanLevel σ) us
      pure (Ix.Kernel.Expr.const (Ix.Cert.Canon.leanKey n) __do_lift)
    | f.app a => do
      let __do_lift ← Ix.Cert.Canon.leanExpr σ f
      let __do_lift_1 ← Ix.Cert.Canon.leanExpr σ a
      pure (Ix.Kernel.Expr.app __do_lift __do_lift_1)
    | Lean.Expr.lam binderName t b binderInfo => do
      let __do_lift ← Ix.Cert.Canon.leanExpr σ t
      let __do_lift_1 ← Ix.Cert.Canon.leanExpr σ b
      pure (Ix.Kernel.Expr.lam __do_lift __do_lift_1 { pw := Ix.Kernel.PropWhen.never })
    | Lean.Expr.forallE binderName t b binderInfo => do
      let __do_lift ← Ix.Cert.Canon.leanExpr σ t
      let __do_lift_1 ← Ix.Cert.Canon.leanExpr σ b
      pure (Ix.Kernel.Expr.forallE __do_lift __do_lift_1 { pw := Ix.Kernel.PropWhen.never })
    | Lean.Expr.letE declName t v b nd => do
      let __do_lift ← Ix.Cert.Canon.leanExpr σ t
      let __do_lift_1 ← Ix.Cert.Canon.leanExpr σ v
      let __do_lift_2 ← Ix.Cert.Canon.leanExpr σ b
      pure (Ix.Kernel.Expr.letE __do_lift __do_lift_1 __do_lift_2 { contract := Ixon.LetContract.lean nd })
    | Lean.Expr.lit (Lean.Literal.natVal n) => pure (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal n))
    | Lean.Expr.lit (Lean.Literal.strVal s) => pure (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.strVal s))
    | Lean.Expr.mdata d e => Ix.Cert.Canon.leanMData d e (Ix.Cert.Canon.leanExpr σ e)
    | Lean.Expr.proj s i e => do
      let __do_lift ← Ix.Cert.Canon.leanExpr σ e
      pure (Ix.Kernel.Expr.proj (Ix.Cert.Canon.leanKey s) i __do_lift) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.leanExpr.eq_def

/-- info: def Ix.Cert.Canon.leanPos : Array Lean.Name → Bool → Lean.Name → Ix.Kernel.LevelParam :=
fun names large n =>
  match Array.findIdx? (fun x => x == n) names with
  | none => names.size
  | some 0 => if large = true then names.size - 1 else 0
  | some i.succ => if large = true then i else i + 1 -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.leanPos

/-- info: Ix.Cert.Canon.compileUnivS.eq_def : ∀ (ctx : List Ix.Name) (x : Ix.Level),
  Ix.Cert.Canon.compileUnivS ctx x =
    match x with
    | Ix.Level.zero hash => some Ixon.Univ.zero
    | l.succ hash => Option.map Ixon.Univ.succ (Ix.Cert.Canon.compileUnivS ctx l)
    | l.max r hash => do
      let __do_lift ← Ix.Cert.Canon.compileUnivS ctx l
      let __do_lift_1 ← Ix.Cert.Canon.compileUnivS ctx r
      pure (__do_lift.max __do_lift_1)
    | l.imax r hash => do
      let __do_lift ← Ix.Cert.Canon.compileUnivS ctx l
      let __do_lift_1 ← Ix.Cert.Canon.compileUnivS ctx r
      pure (__do_lift.imax __do_lift_1)
    | Ix.Level.param n hash => Option.map (fun i => Ixon.Univ.var i.toUInt64) (List.findIdx? (fun x => x.beqRaw n) ctx)
    | Ix.Level.mvar n hash => none -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.compileUnivS.eq_def

/-- info: def Ix.Cert.Canon.UnivMeaningS : Prop :=
∀ (ctx : Array Ix.Name),
  ctx.size < UInt64.size →
    ∀ (l : Ix.Level) (u : Ixon.Univ) (k : Ix.LeanIngress.KLevel) (φ : Ix.Kernel.LevelParam → Nat),
      Ix.Cert.Canon.compileUnivS ctx.toList l = some u →
        Ix.LeanIngress.ingressLevel { names := ctx }.pos l = Except.ok k →
          Ix.CompileCert.univEval (fun i => φ i.toNat) u = Ix.Kernel.Level.eval φ k -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.UnivMeaningS

/-- info: def Ix.Cert.Canon.UniverseBridge : Prop :=
∀ (ps : Array Lean.Name),
  ps.size < UInt64.size →
      ∀ (l : Lean.Level) (u : Ixon.Univ) (k : Ix.LeanIngress.KLevel) (φ : Ix.Kernel.LevelParam → Nat),
        Ix.Cert.Canon.compileUnivS (Array.map Ix.Cert.Canon.nameS ps).toList (Ix.Cert.Canon.levelS l) = some u →
          Ix.Cert.Canon.leanLevel (Ix.Cert.Canon.leanPos ps false) l = Except.ok k →
            Ix.Kernel.Level.eval φ (Ix.Kernel.Reader.convUniv id (Ixon.canonUniv u)) = Ix.Kernel.Level.eval φ k -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.UniverseBridge

/-- info: Ix.Cert.Canon.ingressName_nameS (n : Lean.Name) :
  Ix.LeanIngress.ingressName (Ix.Cert.Canon.nameS n) = Ix.Cert.Canon.leanName n -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.ingressName_nameS

/-- info: Ix.Cert.Canon.ingressLevel_levelS (σ : Ix.Name → Ix.Kernel.LevelParam) (l : Lean.Level) :
  Ix.LeanIngress.ingressLevel σ (Ix.Cert.Canon.levelS l) = Ix.Cert.Canon.leanLevel (σ ∘ Ix.Cert.Canon.nameS) l -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.ingressLevel_levelS

/-- info: Ix.Cert.Canon.ingressExpr_exprS (σ : Ix.Name → Ix.Kernel.LevelParam) (e : Lean.Expr) :
  Ix.LeanIngress.ingressExpr σ (Ix.Cert.Canon.exprS e) = Ix.Cert.Canon.leanExpr (σ ∘ Ix.Cert.Canon.nameS) e -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.ingressExpr_exprS

/-- info: Ix.Cert.Canon.ingressExpr_canonExpr (s : Ix.CanonM.CanonState) (σ : Ix.Name → Ix.Kernel.LevelParam) (e : Lean.Expr) :
  Ix.LeanIngress.ingressExpr σ (StateT.run (Ix.CanonM.canonExpr e) s).run.fst =
    Ix.Cert.Canon.leanExpr (σ ∘ Ix.Cert.Canon.nameS) e -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.ingressExpr_canonExpr

-- CQ2.26: C1, proved.
/-- info: Ix.Cert.Canon.canonMCorrect : Ix.Cert.Canon.CanonMCorrect -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.canonMCorrect

/-- info: Ix.Cert.Canon.canonChunkCorrect : Ix.Cert.Canon.CanonChunkCorrect -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.canonChunkCorrect

/-- info: Ix.Cert.Canon.numbering_nameS (names : Array Lean.Name) (large : Bool) (n : Lean.Name) :
  { names := Array.map Ix.Cert.Canon.nameS names, large := large }.pos (Ix.Cert.Canon.nameS n) =
    Ix.Cert.Canon.leanPos names large n -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.numbering_nameS

/-- info: Ix.Cert.Canon.universe_bridge (hmean : Ix.Cert.Canon.UnivMeaningS) : Ix.Cert.Canon.UniverseBridge -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.universe_bridge

/-- info: Ix.Cert.Canon.univMeaningS : Ix.Cert.Canon.UnivMeaningS -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.univMeaningS

/-- info: Ix.Cert.Canon.universeBridge : Ix.Cert.Canon.UniverseBridge -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.universeBridge

/-- info: 'Ix.Cert.Canon.ingressName_nameS' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.ingressName_nameS

/-- info: 'Ix.Cert.Canon.ingressLevel_levelS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.ingressLevel_levelS

/-- info: 'Ix.Cert.Canon.ingressExpr_exprS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.ingressExpr_exprS

/-- info: 'Ix.Cert.Canon.ingressExpr_canonExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.ingressExpr_canonExpr

/-- info: 'Ix.Cert.Canon.canonMCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.canonMCorrect

/-- info: 'Ix.Cert.Canon.canonChunkCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.canonChunkCorrect

/-- info: 'Ix.Cert.Canon.numbering_nameS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.numbering_nameS

/-- info: 'Ix.Cert.Canon.universe_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.universe_bridge

/-- info: 'Ix.Cert.Canon.univMeaningS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.univMeaningS

/-- info: 'Ix.Cert.Canon.universeBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.universeBridge

/-- info: 'Ix.Cert.Canon.CanonMCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.CanonMCorrect

/-- info: 'Ix.Cert.Canon.UniverseBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.UniverseBridge

/-! ## Component theorems: the reading chain's tables

The certified reader's reading of an in-flight compiler expression survives
every step that retains the reader's leaves (`convExpr_preserves`); the table
interners keep their index invariant and every old slot, and return the
index of what they intern (`internRef_correct`, `internUniv_correct`); the
metadata serializers write only names and blobs, and keep every readable blob
(`NamesBlobs.compileKVMap`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: @Ix.CompileCert.ExpressionRead.convExpr_preserves : ∀ {md : Ix.Kernel.Mode} {before after : Ix.Kernel.Reader.ECx md},
  Ix.CompileCert.ExpressionRead.Extends before after →
    ∀ {table nextTable : Array (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CExpr md))},
      (∀ (index : Nat) (value : Ix.Kernel.Reader.CExpr md),
          table[index]? = some (Except.ok value) → nextTable[index]? = some (Except.ok value)) →
        ∀ (expr : Ixon.Expr),
          Ix.CompileCert.ExpressionRead.Preserves (Ix.Kernel.Reader.convExpr before table expr)
            (Ix.Kernel.Reader.convExpr after nextTable expr) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ExpressionRead.convExpr_preserves

/-- info: Ix.CompileCert.Interning.internRef_correct : ∀ (address : Address)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState),
  Ix.CompileCert.Interning.RefIndexSound state →
    have result := Ix.CompileCert.rawRun (Ix.CompileM.internRef address) context state;
    Ix.CompileCert.Interning.RefIndexSound result.snd ∧
      Ix.CompileCert.Interning.Retains state.refs result.snd.refs ∧
        ∀ (index : UInt64), result.fst = Except.ok index → result.snd.refs[index.toNat]? = some address -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Interning.internRef_correct

/-- info: Ix.CompileCert.Interning.internUniv_correct : ∀ (univ : Ixon.Univ)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState),
  Ix.CompileCert.Interning.UnivIndexSound state →
    have result := Ix.CompileCert.rawRun (Ix.CompileM.internUniv univ) context state;
    Ix.CompileCert.Interning.UnivIndexSound result.snd ∧
      Ix.CompileCert.Interning.Retains state.univs result.snd.univs ∧
        ∀ (index : UInt64), result.fst = Except.ok index → result.snd.univs[index.toNat]? = some univ -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Interning.internUniv_correct

/-- info: Ix.CompileCert.Serializers.NamesBlobs.compileKVMap : ∀ (values : Array (Ix.Name × Ix.DataValue)),
  Ix.CompileCert.Serializers.NamesBlobs (Ix.CompileM.compileKVMap values) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Serializers.NamesBlobs.compileKVMap

/-- info: 'Ix.CompileCert.ExpressionRead.convExpr_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ExpressionRead.convExpr_preserves

/-- info: 'Ix.CompileCert.Interning.internRef_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Interning.internRef_correct

/-- info: 'Ix.CompileCert.Interning.internUniv_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Interning.internUniv_correct

/-- info: 'Ix.CompileCert.Serializers.NamesBlobs.compileKVMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Serializers.NamesBlobs.compileKVMap

-- The interners keep the primary tables on the wire (the sharing builder's
-- table hypothesis, `Ix.Sharing.Verify.BlockWireTablesWF`).
/-- info: Ix.CompileCert.WireTables.internUniv_preserves : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
  (state : Ix.CompileM.BlockState) (univ : Ixon.Univ),
  Ix.Sharing.Verify.BlockWireTablesWF state →
    univ.wireWF →
      Ix.Sharing.Verify.BlockWireTablesWF (Ix.CompileCert.rawRun (Ix.CompileM.internUniv univ) context state).snd -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.WireTables.internUniv_preserves

/-- info: 'Ix.CompileCert.WireTables.internUniv_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.WireTables.internUniv_preserves

/-! ## Component theorems: the universe pipeline's tables

After the raw universe compile, `compileAndInternUnivCanon` canonicalizes
through the block memo and interns the canonical form
(`Ix.CompileCert.UniversePipeline.canonicalTail`). A successful run leaves
the memo exact and the tables sound, and the certified reader reads the
returned slot as the canonical form, whose value under every valuation is the
raw universe's (`canonicalTail_read`). -/

/-- info: @Ix.CompileCert.UniversePipeline.canonicalTail_read : ∀ {md : Ix.Kernel.Mode} (raw : Ixon.Univ)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) (before : Ix.CompileM.BlockState),
  Ix.CompileCert.CanonUnivCache.CanonCacheExact before →
    Ix.CompileCert.UniversePipeline.TablesSound before →
      ∀ {value : UInt64 × Option UInt64} {after : Ix.CompileM.BlockState},
        Ix.CompileCert.rawRun (Ix.CompileCert.UniversePipeline.canonicalTail raw) context before =
            (Except.ok value, after) →
          ∀ (reader : Ix.Kernel.Reader.Ctx md) (param : Nat → Ix.Kernel.LevelParam)
            (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md))),
            Ix.CompileCert.CanonUnivCache.CanonCacheExact after ∧
              Ix.CompileCert.UniversePipeline.TablesSound after ∧
                (Ix.CompileCert.ExpressionRead.blockReader reader param self after).ecx.level value.fst =
                    Except.ok (Ix.Kernel.Reader.convUniv param (Ixon.canonUniv raw)) ∧
                  ∀ (φ : Ix.Kernel.LevelParam → Nat),
                    Ix.Kernel.Level.eval φ (Ix.Kernel.Reader.convUniv param (Ixon.canonUniv raw)) =
                      Ix.CompileCert.univEval (fun index => φ (param index.toNat)) raw -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniversePipeline.canonicalTail_read

/-- info: 'Ix.CompileCert.UniversePipeline.canonicalTail_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.UniversePipeline.canonicalTail_read

/-! ## Component theorems: the raw universe compiler and the whole universe pipeline

Since CQ2.8 the raw universe compiler's memo is keyed by the exact level and
its parameter context. Every run keeps the memo exact, and a successful run
returns the exact positional lowering of the source level
(`Ix.CompileCert.UniverseMeaning.compileUniv_exact`), the specification
`lower`, whose value is the value Source mode reads
(`Ix.CompileCert.UniverseMeaning.lower_eval`, through
`Ix.LeanIngress.ingressLevel`). So the certified reader reads the slot
`compileAndInternUnivCanon` returns as a level that means the source level
(`Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_read`), and
scope, capacity and preseed coverage make the operation succeed
(`compileAndInternUnivCanon_total_read`). Every lemma behind them is audited
in `Ix.CompileCert.ReadingAudit`. -/

/-- info: Ix.CompileCert.UniverseMeaning.lower.eq_def : ∀ (params : List Ix.Name) (x : Ix.Level),
  Ix.CompileCert.UniverseMeaning.lower params x =
    match x with
    | Ix.Level.zero hash => some Ixon.Univ.zero
    | level.succ hash => do
      let __do_lift ← Ix.CompileCert.UniverseMeaning.lower params level
      pure __do_lift.succ
    | left.max right hash => do
      let __do_lift ← Ix.CompileCert.UniverseMeaning.lower params left
      let __do_lift_1 ← Ix.CompileCert.UniverseMeaning.lower params right
      pure (__do_lift.max __do_lift_1)
    | left.imax right hash => do
      let __do_lift ← Ix.CompileCert.UniverseMeaning.lower params left
      let __do_lift_1 ← Ix.CompileCert.UniverseMeaning.lower params right
      pure (__do_lift.imax __do_lift_1)
    | Ix.Level.param name hash => do
      let index ← Ix.Compile.ExactKey.nameIndex name params
      if index < UInt64.size then some (Ixon.Univ.var index.toUInt64) else none
    | Ix.Level.mvar n hash => none -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniverseMeaning.lower.eq_def

-- N2 (2026-10-20): `LevelMeaning` gained `exact` (the level is the reading of the
-- canonical form of the exact lowering), from which `CanonLevelReading` reads the
-- level syntactically; re-frozen.
/-- info: structure Ix.CompileCert.UniversePipeline.LevelMeaning (params : List Ix.Name) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (param : Nat → Ix.Kernel.LevelParam) (source : Ix.Level) (level : Ix.Kernel.Level) : Prop
number of parameters: 5
fields:
  Ix.CompileCert.UniversePipeline.LevelMeaning.value : ∃ target,
      Ix.LeanIngress.ingressLevel σ source = Except.ok target ∧
        ∀ (φ ψ : Ix.Kernel.LevelParam → Nat),
          (∀ (name : Ix.Name) (index : Nat),
              Ix.Compile.ExactKey.nameIndex name params = some index → φ (σ name) = ψ (param index)) →
            Ix.Kernel.Level.eval φ target = Ix.Kernel.Level.eval ψ level
  Ix.CompileCert.UniversePipeline.LevelMeaning.defined : ∀ (allowed : List Ix.Kernel.LevelParam),
      (∀ (index : Nat), index < params.length → param index ∈ allowed) →
        Ix.Kernel.Level.allParamsDefined allowed level = true
  Ix.CompileCert.UniversePipeline.LevelMeaning.exact : ∃ raw,
      Ix.CompileCert.UniverseMeaning.lower params source = some raw ∧
        level = Ix.Kernel.Reader.convUniv param (Ixon.canonUniv raw)
constructor:
  Ix.CompileCert.UniversePipeline.LevelMeaning.mk {params : List Ix.Name} {σ : Ix.Name → Ix.Kernel.LevelParam}
    {param : Nat → Ix.Kernel.LevelParam} {source : Ix.Level} {level : Ix.Kernel.Level}
    (value :
      ∃ target,
        Ix.LeanIngress.ingressLevel σ source = Except.ok target ∧
          ∀ (φ ψ : Ix.Kernel.LevelParam → Nat),
            (∀ (name : Ix.Name) (index : Nat),
                Ix.Compile.ExactKey.nameIndex name params = some index → φ (σ name) = ψ (param index)) →
              Ix.Kernel.Level.eval φ target = Ix.Kernel.Level.eval ψ level)
    (defined :
      ∀ (allowed : List Ix.Kernel.LevelParam),
        (∀ (index : Nat), index < params.length → param index ∈ allowed) →
          Ix.Kernel.Level.allParamsDefined allowed level = true)
    (exact :
      ∃ raw,
        Ix.CompileCert.UniverseMeaning.lower params source = some raw ∧
          level = Ix.Kernel.Reader.convUniv param (Ixon.canonUniv raw)) :
    Ix.CompileCert.UniversePipeline.LevelMeaning params σ param source level -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.UniversePipeline.LevelMeaning

/-- info: Ix.CompileCert.UniverseMeaning.compileUniv_exact : ∀ (source : Ix.Level)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  Ix.CompileCert.Keeps context Ix.CompileCert.UniverseMeaning.UnivCacheExact (Ix.CompileM.compileUniv source)
    fun value => Ix.CompileCert.UniverseMeaning.lower context.snd.univCtx source = some value -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniverseMeaning.compileUniv_exact

/-- info: Ix.CompileCert.UniverseMeaning.lower_eval : ∀ (params : List Ix.Name) (σ : Ix.Name → Ix.Kernel.LevelParam)
  {source : Ix.Level} {value : Ixon.Univ},
  Ix.CompileCert.UniverseMeaning.lower params source = some value →
    ∃ level,
      Ix.LeanIngress.ingressLevel σ source = Except.ok level ∧
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : UInt64 → Nat),
          (∀ (name : Ix.Name) (index : Nat),
              Ix.Compile.ExactKey.nameIndex name params = some index →
                index < UInt64.size → φ (σ name) = ρ index.toUInt64) →
            Ix.Kernel.Level.eval φ level = Ix.CompileCert.univEval ρ value -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniverseMeaning.lower_eval

/-- info: @Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_read : ∀ {md : Ix.Kernel.Mode} (source : Ix.Level)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) (before : Ix.CompileM.BlockState),
  Ix.CompileCert.UniversePipeline.Sound before →
    ∀ {value : UInt64 × Option UInt64} {after : Ix.CompileM.BlockState},
      Ix.CompileCert.rawRun (Ix.CompileM.compileAndInternUnivCanon source) context before = (Except.ok value, after) →
        ∀ (reader : Ix.Kernel.Reader.Ctx md) (param : Nat → Ix.Kernel.LevelParam)
          (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
          (σ : Ix.Name → Ix.Kernel.LevelParam),
          Ix.CompileCert.UniversePipeline.Sound after ∧
            ∃ level,
              (Ix.CompileCert.ExpressionRead.blockReader reader param self after).ecx.level value.fst =
                  Except.ok level ∧
                Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param source level -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_read

/-- info: @Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_total_read : ∀ {md : Ix.Kernel.Mode} (source : Ix.Level)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) (before : Ix.CompileM.BlockState),
  Ix.CompileCert.UniversePipeline.Sound before →
    context.snd.univCtx.length ≤ UInt64.size →
      Ix.CompileCert.UniverseMeaning.Scoped context.snd.univCtx source →
        before.univs.size + before.metaUnivs.size + 1 < UInt64.size →
          Ix.CompileCert.UniversePipeline.Preseeded context.snd.univCtx source before →
            ∀ (reader : Ix.Kernel.Reader.Ctx md) (param : Nat → Ix.Kernel.LevelParam)
              (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
              (σ : Ix.Name → Ix.Kernel.LevelParam),
              ∃ value after level,
                Ix.CompileCert.rawRun (Ix.CompileM.compileAndInternUnivCanon source) context before =
                    (Except.ok value, after) ∧
                  Ix.CompileCert.UniversePipeline.Sound after ∧
                    (Ix.CompileCert.ExpressionRead.blockReader reader param self after).ecx.level value.fst =
                        Except.ok level ∧
                      Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param source level -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_total_read

/-- info: 'Ix.CompileCert.UniverseMeaning.compileUniv_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.UniverseMeaning.compileUniv_exact

/-- info: 'Ix.CompileCert.UniverseMeaning.lower_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.UniverseMeaning.lower_eval

/-- info: 'Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_read

/-- info: 'Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_total_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.UniversePipeline.compileAndInternUnivCanon_total_read

-- The exact lowering is the Canon bridge's cache-free compile wherever the
-- context fits the wire.
/-- info: Ix.Cert.Canon.lower_eq_compileUnivS : ∀ (ctx : List Ix.Name),
  ctx.length ≤ UInt64.size →
      ∀ (l : Ix.Level), Ix.CompileCert.UniverseMeaning.lower ctx l = Ix.Cert.Canon.compileUnivS ctx l -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Canon.lower_eq_compileUnivS

/-- info: 'Ix.Cert.Canon.lower_eq_compileUnivS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Canon.lower_eq_compileUnivS

/-! ## Component theorems: the ordinary expression compiler reads back as its source

`Ix.CompileM.compileExprNoSurgery` (the memo, then one step per constructor,
by well-founded recursion on `sizeOf`) is proved by strong induction: from
every state satisfying the expression invariant (`ExpressionState.Good`:
the universe invariants, the reference index, the declaration prefix's
binding view and the memo's meaning at CQ2.8's exact keys), every run keeps
it and every earlier reading, and a successful run's value reads, through
the certified reader, as a term `Related` to the source. Without call-site
plans the production entry `compileExpr` is that compiler
(`compileExpr_read`). The relation is Source mode's own reading up to keys
and level values (`related_ingress_value`). Every lemma behind them is
audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: inductive Ix.CompileCert.ExpressionState.Related : {md : Ix.Kernel.Mode} →
  (Ix.Name → Ix.Kernel.Reader.CName md → Prop) →
    (Ix.Level → Ix.Kernel.Level → Prop) → Ix.Expr → Ix.Kernel.Reader.CExpr md → Prop
number of parameters: 3
constructors:
Ix.CompileCert.ExpressionState.Related.bvar : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (index : Nat)
  (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.bvar index hash) (Ix.Kernel.Expr.mkBvar index)
Ix.CompileCert.ExpressionState.Related.sort : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Level}
  {level : Ix.Kernel.Level} (hash : Address),
  levels source level →
    Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.sort source hash) (Ix.Kernel.Expr.sort level)
Ix.CompileCert.ExpressionState.Related.const : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {name : Ix.Name}
  {key : Ix.Kernel.Reader.CName md} (hash : Address) (sources : Array Ix.Level) (targets : List Ix.Kernel.Level),
  names name key →
    List.Forall₂ levels sources.toList targets →
      Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.const name sources hash)
        (Ix.Kernel.Expr.const key targets)
Ix.CompileCert.ExpressionState.Related.app : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {fn arg : Ix.Expr}
  {targetFn targetArg : Ix.Kernel.Reader.CExpr md} (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels fn targetFn →
    Ix.CompileCert.ExpressionState.Related names levels arg targetArg →
      Ix.CompileCert.ExpressionState.Related names levels (fn.app arg hash) (Ix.Kernel.Expr.app targetFn targetArg)
Ix.CompileCert.ExpressionState.Related.lam : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
  {type body : Ix.Expr} {targetType targetBody : Ix.Kernel.Reader.CExpr md} (name : Ix.Name) (info : Lean.BinderInfo)
  (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels type targetType →
    Ix.CompileCert.ExpressionState.Related names levels body targetBody →
      Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.lam name type body info hash)
        (Ix.Kernel.Expr.lam targetType targetBody { pw := Ix.Kernel.PropWhen.never })
Ix.CompileCert.ExpressionState.Related.all : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
  {type body : Ix.Expr} {targetType targetBody : Ix.Kernel.Reader.CExpr md} (name : Ix.Name) (info : Lean.BinderInfo)
  (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels type targetType →
    Ix.CompileCert.ExpressionState.Related names levels body targetBody →
      Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.forallE name type body info hash)
        (Ix.Kernel.Expr.forallE targetType targetBody { pw := Ix.Kernel.PropWhen.never })
Ix.CompileCert.ExpressionState.Related.letE : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
  {type value body : Ix.Expr} {targetType targetValue targetBody : Ix.Kernel.Reader.CExpr md} (name : Ix.Name)
  (nonDep : Bool) (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels type targetType →
    Ix.CompileCert.ExpressionState.Related names levels value targetValue →
      Ix.CompileCert.ExpressionState.Related names levels body targetBody →
        Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.letE name type value body nonDep hash)
          (Ix.Kernel.Expr.letE targetType targetValue targetBody { contract := Ixon.LetContract.lean nonDep })
Ix.CompileCert.ExpressionState.Related.nat : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (value : Nat)
  (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.lit (Lean.Literal.natVal value) hash)
    (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal value))
Ix.CompileCert.ExpressionState.Related.str : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} (value : String)
  (hash : Address),
  Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.lit (Lean.Literal.strVal value) hash)
    (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.strVal value))
Ix.CompileCert.ExpressionState.Related.proj : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {name : Ix.Name}
  {key : Ix.Kernel.Reader.CName md} {value : Ix.Expr} {targetValue : Ix.Kernel.Reader.CExpr md} (field : Nat)
  (hash : Address),
  names name key →
    Ix.CompileCert.ExpressionState.Related names levels value targetValue →
      Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.proj name field value hash)
        (Ix.Kernel.Expr.proj key field targetValue)
Ix.CompileCert.ExpressionState.Related.mdata : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
  {target : Ix.Kernel.Reader.CExpr md} (data : Array (Ix.Name × Ix.DataValue)) (hash : Address),
  Ix.SemanticContract.hasMetadata data = false →
    Ix.CompileCert.ExpressionState.Related names levels source target →
      Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.mdata data source hash) target
Ix.CompileCert.ExpressionState.Related.contract : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop} {source : Ix.Expr}
  {target result : Ix.Kernel.Reader.CExpr md} (data : Array (Ix.Name × Ix.DataValue)) (hash : Address)
  (c : Ix.SemanticContract.Contract),
  Ix.SemanticContract.hasMetadata data = true →
    Ix.SemanticContract.read data = Except.ok c →
      Ix.CompileCert.ExpressionState.Related names levels source target →
        Ix.CompileCert.ExpressionState.withContract c source target = some result →
          Ix.CompileCert.ExpressionState.Related names levels (Ix.Expr.mdata data source hash) result -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.ExpressionState.Related

/-- info: @Ix.CompileCert.ExpressionState.compileExpr_read : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        Ix.CompileCert.ExpressionState.SelfCorrect context.snd self names →
          ∀ (source : Ix.Expr) (before : Ix.CompileM.BlockState),
            Ix.CompileCert.ExpressionState.Good cx param self
                (Ix.CompileCert.ExpressionState.Related names
                  (Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param))
                bindings before →
              ∀ {value : Ixon.Expr × UInt64} {after : Ix.CompileM.BlockState},
                Ix.CompileCert.rawRun (Ix.CompileM.compileExpr source) context before = (Except.ok value, after) →
                  ∃ target,
                    Ix.CompileCert.ExpressionState.Related names
                        (Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param) source target ∧
                      (Ix.CompileCert.ExpressionRead.blockReader cx param self after).read value.fst = Except.ok target -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ExpressionState.compileExpr_read

/-- info: @Ix.CompileCert.ExpressionState.related_ingress_value : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {params : List Ix.Name} {σ : Ix.Name → Ix.Kernel.LevelParam}
  {param : Nat → Ix.Kernel.LevelParam} {source : Ix.Expr} {target : Ix.Kernel.Reader.CExpr md},
  Ix.CompileCert.ExpressionState.Related names (Ix.CompileCert.UniversePipeline.LevelMeaning params σ param) source
      target →
    ∃ converted,
      Ix.LeanIngress.ingressExpr σ source = Except.ok converted ∧
        Ix.CompileCert.ExpressionState.Matches
          (fun key key' => ∃ name, key = Ix.LeanIngress.ingressKey name ∧ names name key')
          (fun level level' =>
            ∀ (φ ψ : Ix.Kernel.LevelParam → Nat),
              (∀ (name : Ix.Name) (index : Nat),
                  Ix.Compile.ExactKey.nameIndex name params = some index → φ (σ name) = ψ (param index)) →
                Ix.Kernel.Level.eval φ level = Ix.Kernel.Level.eval ψ level')
          converted target -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ExpressionState.related_ingress_value

/-- info: 'Ix.CompileCert.ExpressionState.compileExprNoSurgery_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ExpressionState.compileExprNoSurgery_scoped

/-- info: 'Ix.CompileCert.ExpressionState.compileExpr_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ExpressionState.compileExpr_read

/-- info: 'Ix.CompileCert.ExpressionState.related_ingress_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ExpressionState.related_ingress_value

/-! ## Component theorems: the preseed

Every run of `preseedExprTables` keeps the expression invariant and extends
the in-flight reader (`PreseedState.preseed_good`), so the expression
compiler's correctness applies after it (`preseed_compileExpr_read`); a
successful run keeps the primary tables on the wire (`PreseedWire.preseed_wire`;
the reference interner refuses an address that is not 32 bytes) and leaves the universe
table final, after which universe compilation does not grow it
(`FinalUniverses.compile_no_growth`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: @Ix.CompileCert.PreseedState.preseed_good : ∀ {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
  {param : Nat → Ix.Kernel.LevelParam} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md))}
  {related : Ix.Expr → Ix.Kernel.Reader.CExpr md → Prop} {bindings : Ix.CompileCert.ExpressionState.Bindings}
  {compileEnv : Ix.CompileM.CompileEnv},
  (∀ (address : Address), cx.blob address = compileEnv.blobs.get? address) →
    ∀ (roots : Array (Ix.Expr × List Ix.Name)),
      Ix.CompileCert.PreseedState.GoodStep cx param self related bindings compileEnv
        (Ix.CompileM.preseedExprTables roots) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.PreseedState.preseed_good

/-- info: @Ix.CompileCert.PreseedState.preseed_compileExpr_read : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        Ix.CompileCert.ExpressionState.SelfCorrect context.snd self names →
          ∀ (roots : Array (Ix.Expr × List Ix.Name)) (source : Ix.Expr) {before middle after : Ix.CompileM.BlockState}
            {value : Ixon.Expr × UInt64},
            Ix.CompileCert.ExpressionState.Good cx param self
                (Ix.CompileCert.ExpressionState.Related names
                  (Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param))
                bindings before →
              Ix.CompileCert.rawRun (Ix.CompileM.preseedExprTables roots) context before = (Except.ok (), middle) →
                Ix.CompileCert.rawRun (Ix.CompileM.compileExpr source) context middle = (Except.ok value, after) →
                  ∃ target,
                    Ix.CompileCert.ExpressionState.Related names
                        (Ix.CompileCert.UniversePipeline.LevelMeaning context.snd.univCtx σ param) source target ∧
                      (Ix.CompileCert.ExpressionRead.blockReader cx param self after).read value.fst = Except.ok target -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.PreseedState.preseed_compileExpr_read

/-- info: Ix.CompileCert.PreseedWire.preseed_wire : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
  (roots : Array (Ix.Expr × List Ix.Name)) {before after : Ix.CompileM.BlockState},
  Ix.Sharing.Verify.BlockWireTablesWF before →
    Ix.CompileCert.rawRun (Ix.CompileM.preseedExprTables roots) context before = (Except.ok (), after) →
      Ix.Sharing.Verify.BlockWireTablesWF after -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.PreseedWire.preseed_wire

/-- info: Ix.CompileCert.FinalUniverses.compile_no_growth : ∀ (source : Ix.Level)
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) {before after : Ix.CompileM.BlockState},
  before.univsFinal = true →
    ∀ {output : UInt64 × Option UInt64},
      Ix.CompileCert.rawRun (Ix.CompileM.compileAndInternUnivCanon source) context before = (Except.ok output, after) →
        after.univs = before.univs ∧ after.univsFinal = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.FinalUniverses.compile_no_growth

/-- info: 'Ix.CompileCert.PreseedState.preseed_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.PreseedState.preseed_good

/-- info: 'Ix.CompileCert.PreseedState.preseed_compileExpr_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.PreseedState.preseed_compileExpr_read

/-- info: 'Ix.CompileCert.PreseedWire.preseed_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.PreseedWire.preseed_wire

/-- info: 'Ix.CompileCert.FinalUniverses.compile_no_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.FinalUniverses.compile_no_growth

-- After a successful preseed, every level occurrence of every root is
-- preseeded (the universe table is final and holds the canonical form of
-- the level's exact lowering), discharging `UniversePipeline.Preseeded`.
/-- info: Ix.CompileCert.PreseedInsertion.preseed_preseeded : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
  (roots : Array (Ix.Expr × List Ix.Name)) {before after : Ix.CompileM.BlockState},
  Ix.CompileCert.Interning.UnivIndexSound before →
    Ix.CompileCert.CanonUnivCache.CanonCacheExact before →
      Ix.CompileCert.rawRun (Ix.CompileM.preseedExprTables roots) context before = (Except.ok (), after) →
        after.univsFinal = true ∧
          ∀ (root : Ix.Expr × List Ix.Name),
            root ∈ roots →
              Ix.CompileCert.PreseedUniverses.LevelsSatisfy
                (fun level => Ix.CompileCert.UniversePipeline.Preseeded root.snd level after) root.fst -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.PreseedInsertion.preseed_preseeded

/-- info: 'Ix.CompileCert.PreseedInsertion.preseed_preseeded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.PreseedInsertion.preseed_preseeded

/-! ## Component theorems: successful compilation keeps the tables on the wire

A successful run of the production expression compiler, under an
environment without call-site plans, or of any payload emitter (definition,
axiom, quotient, recursor, constructor, inductive, mutual members and
classes) keeps the primary reference and universe tables representable by
the constant wire format, from a state whose tables are on the wire and
whose universe table is final (`EmissionWire.Valid`); a successful preseed establishes that state
(`EmissionWire.seeded_valid`). Success-only: a refused universe miss may
write before its guard fires. Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.EmissionWire.Valid : Ix.CompileM.BlockState → Prop :=
fun state => Ix.Sharing.Verify.BlockWireTablesWF state ∧ state.univsFinal = true -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.EmissionWire.Valid

/-- info: def Ix.CompileCert.EmissionWire.Safe : {α : Type} →
  Ix.CompileM.CompileM α → (optParam (α → Prop) fun x => True) → Prop :=
fun {α} action post =>
  ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
    context.fst.surgeryFree = true →
      ∀ (before : Ix.CompileM.BlockState) (value : α) (after : Ix.CompileM.BlockState),
        Ix.CompileCert.EmissionWire.Valid before →
          Ix.CompileCert.rawRun action context before = (Except.ok value, after) →
            Ix.CompileCert.EmissionWire.Valid after ∧ post value -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.EmissionWire.Safe

/-- info: Ix.CompileCert.EmissionWire.Safe.expression : ∀ (source : Ix.Expr),
  Ix.CompileCert.EmissionWire.Safe (Ix.CompileM.compileExpr source) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionWire.Safe.expression

/-- info: Ix.CompileCert.EmissionWire.Safe.mutConsts : ∀ (sources : List (List Ix.MutConst)),
  Ix.CompileCert.EmissionWire.Safe (Ix.CompileM.compileMutConsts sources) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionWire.Safe.mutConsts

/-- info: Ix.CompileCert.EmissionWire.seeded_valid : ∀ (roots : Array (Ix.Expr × List Ix.Name))
  (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv) {before after : Ix.CompileM.BlockState},
  Ix.Sharing.Verify.BlockWireTablesWF before →
    Ix.CompileCert.rawRun (Ix.CompileM.preseedExprTables roots) context before = (Except.ok (), after) →
      Ix.CompileCert.EmissionWire.Valid after -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionWire.seeded_valid

/-- info: 'Ix.CompileCert.EmissionWire.Safe.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionWire.Safe.expression

/-- info: 'Ix.CompileCert.EmissionWire.Safe.mutConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionWire.Safe.mutConsts

/-- info: 'Ix.CompileCert.EmissionWire.seeded_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionWire.seeded_valid

/-! ## Component theorems: canonical sharing preserves the reading of every root

One theorem for every payload kind (R07-01/02): a successful root
write-back replaces exactly the roots, in order, and keeps the rest of the
payload (`SharingRoots.withRoots_inv`, over `erase`, which replaces every
root by one placeholder); the sharing builder keeps the payload but its
roots and the tables, and the built constant's actual member reader reads
its roots as the compiler's in-flight reader read the payload's roots, so
every root-by-root relation transfers (`SharingRoots.build_read`,
`RootsRead`). No pointer- or hash-injectivity premise
(`canonicalSharingTiered_meaning`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.SharingRoots.erase : Ixon.ConstantInfo → Ixon.ConstantInfo :=
fun info => Ix.Sharing.Exact.mapRoots (fun x => Ixon.Expr.sort 0) info -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.SharingRoots.erase

/-- info: def Ix.CompileCert.SharingRoots.RootsRead : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Reader.MemberReader md →
    (Ix.Expr → Ix.Kernel.Reader.CExpr md → Prop) → List Ix.Expr → List Ixon.Expr → Prop :=
fun {md} reader related sources roots =>
  List.Forall₂ (fun source root => ∃ target, related source target ∧ reader.read root = Except.ok target) sources roots -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.SharingRoots.RootsRead

/-- info: @Ix.CompileCert.SharingRoots.withRoots_inv : ∀ {info info' : Ixon.ConstantInfo} {roots : Array Ixon.Expr},
  Ix.Sharing.Exact.withRoots info roots = Except.ok info' →
    Ix.Sharing.Exact.constantInfoRoots info' = roots ∧
      Ix.CompileCert.SharingRoots.erase info' = Ix.CompileCert.SharingRoots.erase info -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.SharingRoots.withRoots_inv

/-- info: @Ix.CompileCert.SharingRoots.build_roots : ∀ {md : Ix.Kernel.Mode} (limits : Ix.Sharing.Exact.Limits)
  (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ) (out : Ixon.Constant),
  Ix.CompileM.buildConstantWithSharing limits info refs univs = Except.ok out →
    Ix.CompileCert.SharingRoots.erase out.info = Ix.CompileCert.SharingRoots.erase info ∧
      out.refs = refs ∧
        out.univs = univs ∧
          ∀ (context : Ix.Kernel.Reader.Ctx md) (param : Nat → Ix.Kernel.LevelParam)
            (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md))),
            Array.map (Ix.Kernel.Reader.MemberReader.mk' context out param self).read
                (Ix.CompileM.constantInfoRootExprs out.info) =
              Array.map
                (Ix.Kernel.Reader.MemberReader.mk' context
                    { info := info, sharing := #[], refs := refs, univs := univs } param self).read
                (Ix.CompileM.constantInfoRootExprs info) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.SharingRoots.build_roots

/-- info: @Ix.CompileCert.SharingRoots.build_read : ∀ {md : Ix.Kernel.Mode} (context : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (state : Ix.CompileM.BlockState) (limits : Ix.Sharing.Exact.Limits) (info : Ixon.ConstantInfo) (out : Ixon.Constant),
  Ix.CompileM.buildConstantWithSharing limits info state.refs state.univs = Except.ok out →
    ∀ {related : Ix.Expr → Ix.Kernel.Reader.CExpr md → Prop} {sources : List Ix.Expr},
      Ix.CompileCert.SharingRoots.RootsRead (Ix.CompileCert.ExpressionRead.blockReader context param self state) related
          sources (Ix.CompileM.constantInfoRootExprs info).toList →
        Ix.CompileCert.SharingRoots.erase out.info = Ix.CompileCert.SharingRoots.erase info ∧
          Ix.CompileCert.SharingRoots.RootsRead
            (Ix.Kernel.Reader.MemberReader.mk' (Ix.CompileCert.ExpressionRead.withBlockBlobs context state) out param
              self)
            related sources (Ix.CompileM.constantInfoRootExprs out.info).toList -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.SharingRoots.build_read

/-- info: 'Ix.CompileCert.SharingRoots.withRoots_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SharingRoots.withRoots_inv

/-- info: 'Ix.CompileCert.SharingRoots.build_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SharingRoots.build_roots

/-- info: 'Ix.CompileCert.SharingRoots.build_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SharingRoots.build_read

/-! ## Component theorems: the payload emitters read back as their sources

Every declaration emitter (definition-like, axiom, quotient, constructor and
the constructor loop, inductive, recursor and the rule loop), from a state
satisfying the expression invariant for the declaration's own relation and
under an environment without call-site plans, returns on success the
payload its source describes, whose expression roots the in-flight reader
reads as terms `Related` to the source's, in order
(`SharingRoots.RootsRead`); it ends `Emission.Clean` (the invariant's state
part, with an empty memo) and extends the reader. The finishers are one
skeleton (`Emission.Tidy`, `Emission.Frame`); the header counts are the
source's by the production guards (`Emission.Yields`). Every lemma behind
them is audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.Emission.Clean : Ix.CompileCert.ExpressionState.Bindings → Ix.CompileM.BlockState → Prop :=
fun bindings state => Ix.CompileCert.ExpressionState.StateSound bindings state ∧ state.exprCache = ∅ -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.Emission.Clean

/-- info: @Ix.CompileCert.Emission.definition_correct : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.Def),
          Ix.CompileCert.ExpressionState.ConstsSatisfy (Ix.CompileCert.ExpressionState.SelfName context.snd self names)
              source.type →
            Ix.CompileCert.ExpressionState.ConstsSatisfy
                (Ix.CompileCert.ExpressionState.SelfName context.snd self names) source.value →
              ∀ {before after : Ix.CompileM.BlockState}
                {output : Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr},
                Ix.CompileCert.ExpressionState.Good cx param self
                    (Ix.CompileCert.Emission.related param names σ
                      (Ix.CompileCert.Emission.inner source.name source.levelParams.toList context))
                    bindings before →
                  Ix.CompileCert.rawRun (Ix.CompileM.compileDefinitionData source) context before =
                      (Except.ok output, after) →
                    Ix.CompileCert.Emission.Clean bindings after ∧
                      Ix.CompileCert.ExpressionRead.Extends
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self before).ecx
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx ∧
                        output.fst = Ix.CompileCert.Emission.definitionPayload source output.fst.typ output.fst.value ∧
                          output.snd.snd = (output.fst.typ, output.fst.value) ∧
                            Ix.CompileCert.SharingRoots.RootsRead
                              (Ix.CompileCert.ExpressionRead.blockReader cx param self after)
                              (Ix.CompileCert.Emission.related param names σ
                                (Ix.CompileCert.Emission.inner source.name source.levelParams.toList context))
                              [source.type, source.value] [output.fst.typ, output.fst.value] -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Emission.definition_correct

/-- info: @Ix.CompileCert.Emission.recursor_correct : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.RecursorVal),
          Ix.CompileCert.ExpressionState.ConstsSatisfy (Ix.CompileCert.ExpressionState.SelfName context.snd self names)
              source.cnst.type →
            (∀ (rule : Ix.RecursorRule),
                rule ∈ source.rules.toList →
                  Ix.CompileCert.ExpressionState.ConstsSatisfy
                    (Ix.CompileCert.ExpressionState.SelfName context.snd self names) rule.rhs) →
              ∀ {before after : Ix.CompileM.BlockState} {output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr},
                Ix.CompileCert.ExpressionState.Good cx param self
                    (Ix.CompileCert.Emission.related param names σ
                      (Ix.CompileCert.Emission.inner source.cnst.name source.cnst.levelParams.toList context))
                    bindings before →
                  Ix.CompileCert.rawRun (Ix.CompileM.compileRecursor source) context before =
                      (Except.ok output, after) →
                    Ix.CompileCert.Emission.Clean bindings after ∧
                      Ix.CompileCert.ExpressionRead.Extends
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self before).ecx
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx ∧
                        output.fst = Ix.CompileCert.Emission.recursorPayload source output.fst.typ output.fst.rules ∧
                          List.map (fun x => x.fields) output.fst.rules.toList =
                              List.map (fun rule => rule.nfields.toUInt64) source.rules.toList ∧
                            output.snd.snd = output.fst.typ ∧
                              Ix.CompileCert.SharingRoots.RootsRead
                                (Ix.CompileCert.ExpressionRead.blockReader cx param self after)
                                (Ix.CompileCert.Emission.related param names σ
                                  (Ix.CompileCert.Emission.inner source.cnst.name source.cnst.levelParams.toList
                                    context))
                                (source.cnst.type :: List.map (fun x => x.rhs) source.rules.toList)
                                (output.fst.typ :: List.map (fun x => x.rhs) output.fst.rules.toList) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Emission.recursor_correct

/-- info: 'Ix.CompileCert.Emission.definition_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Emission.definition_correct

/-- info: 'Ix.CompileCert.Emission.axiom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Emission.axiom_correct

/-- info: 'Ix.CompileCert.Emission.quotient_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Emission.quotient_correct

/-- info: 'Ix.CompileCert.Emission.inductiveData_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Emission.inductiveData_correct

/-- info: 'Ix.CompileCert.Emission.recursor_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Emission.recursor_correct

/-! ## Component theorems: the singleton blocks read back as their sources

The preseeded singleton block compilers (definition-like, axiom, quotient,
recursor, standalone inductive family), from a clean state and under an
environment without call-site plans, return on success a block whose
payload keeps the source's skeleton (`SharingRoots.erase`: every field but
the expression roots) and whose actual member reader (the block's blobs
overlaid on the context's) reads the roots as terms `Related` to the
source's, in order; and, from tables on the wire, a block that decodes
exactly
(`Ix.Sharing.Verify.BlockResultCodecWF`). Every lemma behind them is
audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.EmissionBlocks.definitionSkeleton : Ix.Def → Ixon.ConstantInfo :=
fun source =>
  Ixon.ConstantInfo.defn (Ix.CompileCert.Emission.definitionPayload source (Ixon.Expr.sort 0) (Ixon.Expr.sort 0)) -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.EmissionBlocks.definitionSkeleton

/-- info: @Ix.CompileCert.EmissionBlocks.definitionInfo_correct : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.Def),
          Ix.CompileCert.ExpressionState.ConstsSatisfy (Ix.CompileCert.ExpressionState.SelfName context.snd self names)
              source.type →
            Ix.CompileCert.ExpressionState.ConstsSatisfy
                (Ix.CompileCert.ExpressionState.SelfName context.snd self names) source.value →
              ∀ {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
                Ix.CompileCert.Emission.Clean bindings before →
                  Ix.CompileCert.rawRun (Ix.CompileM.compileDefinitionDataInfo source) context before =
                      (Except.ok output, after) →
                    Ix.CompileCert.Emission.Clean bindings after ∧
                      Ix.CompileCert.ExpressionRead.Extends
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self before).ecx
                          (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx ∧
                        (∃ blockMeta, output = Ix.CompileM.BlockResult.mk' output.block blockMeta) ∧
                          Ix.CompileCert.SharingRoots.erase output.block.info =
                              Ix.CompileCert.SharingRoots.erase
                                (Ix.CompileCert.EmissionBlocks.definitionSkeleton source) ∧
                            Ix.CompileCert.SharingRoots.RootsRead
                              (Ix.CompileCert.EmissionBlocks.recordReader cx param self after output.block)
                              (Ix.CompileCert.Emission.related param names σ
                                (Ix.CompileCert.Emission.inner source.name source.levelParams.toList context))
                              [source.type, source.value] (Ix.CompileM.constantInfoRootExprs output.block.info).toList -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionBlocks.definitionInfo_correct

/-- info: Ix.CompileCert.EmissionBlocks.definitionInfo_codec : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (source : Ix.Def) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        Ix.CompileCert.rawRun (Ix.CompileM.compileDefinitionDataInfo source) context before =
            (Except.ok output, after) →
          Ix.Sharing.Verify.BlockResultCodecWF output -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionBlocks.definitionInfo_codec

/-- info: 'Ix.CompileCert.EmissionBlocks.definitionInfo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.definitionInfo_correct

/-- info: 'Ix.CompileCert.EmissionBlocks.axiomInfo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.axiomInfo_correct

/-- info: 'Ix.CompileCert.EmissionBlocks.quotientInfo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.quotientInfo_correct

/-- info: 'Ix.CompileCert.EmissionBlocks.recursorInfo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.recursorInfo_correct

/-- info: 'Ix.CompileCert.EmissionBlocks.familyInfo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.familyInfo_correct

/-- info: 'Ix.CompileCert.EmissionBlocks.familyInfo_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionBlocks.familyInfo_codec

/-! ## Component theorems: every public dispatch kind decodes exactly

Without call-site plans the plan-head audits are no-ops, so public dispatch
(`Ix.CompileM.compileConstantInfo`) is the kind's preseeded block compiler
in the singleton mutual context (`EmissionDispatch.*_run`); for every kind,
and for a mutual block, a successful compile from tables on the wire returns a
block that decodes exactly. Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: Ix.CompileCert.EmissionDispatch.constant_codec : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (info : Ix.ConstantInfo) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        Ix.CompileCert.rawRun (Ix.CompileM.compileConstantInfo info) context before = (Except.ok output, after) →
          Ix.Sharing.Verify.BlockResultCodecWF output -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionDispatch.constant_codec

/-- info: Ix.CompileCert.EmissionDispatch.mutualBlock_codec : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (classes : List (List Ix.MutConst)) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        Ix.CompileCert.rawRun (Ix.CompileM.compileMutualBlock classes) context before = (Except.ok output, after) →
          Ix.Sharing.Verify.BlockResultCodecWF output -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionDispatch.mutualBlock_codec

/-- info: Ix.CompileCert.EmissionDispatch.definition_run : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (info : Ix.ConstantInfo) (source : Ix.Def),
      Ix.CompileCert.EmissionDispatch.sourceData info = some source →
        ∀ (state : Ix.CompileM.BlockState),
          Ix.CompileCert.rawRun (Ix.CompileM.compileConstantInfo info) context state =
            Ix.CompileCert.rawRun (Ix.CompileM.compileDefinitionDataInfo source)
              (Ix.CompileCert.EmissionDispatch.singletonContext source.name context) state -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.EmissionDispatch.definition_run

/-- info: 'Ix.CompileCert.EmissionDispatch.constant_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionDispatch.constant_codec

/-- info: 'Ix.CompileCert.EmissionDispatch.mutualBlock_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.EmissionDispatch.mutualBlock_codec

/-! ## Component theorems: compiled singleton records are read back as their sources

Public dispatch of a definition, theorem, opaque, axiom or quotient, under
an environment without call-site plans, from a clean state whose tables
are on the wire returns a block that decodes exactly and that the certified
reader's `readRecord` (over the block's blobs overlaid on the context's)
reads as exactly the declaration the source describes: under the record's
key, with the level parameters `0, …, n - 1`, and with a type (and a
value) `Related` to the source's; given that the key reads, that the self
references resolve to it (`DefinitionReading.SelfAliases`) or do not occur
(headers), and the reader's safety policy. A declined declaration is
declined. Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: @Ix.CompileCert.DefinitionReading.constant_reads : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (info : Ix.ConstantInfo) (source : Ix.Def),
          Ix.CompileCert.EmissionDispatch.sourceData info = some source →
            ∀ {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult}
              (state : Ix.Kernel.Reader.State md) {key : Ix.Kernel.Reader.CName md},
              cx.memberKey (Ix.Kernel.ConstRef.member output.blockAddr 0) = Except.ok key →
                Ix.CompileCert.DefinitionReading.SelfAliases source.name key names →
                  Ix.CompileCert.Emission.Clean bindings before →
                    Ix.Sharing.Verify.BlockWireTablesWF before →
                      Ix.Kernel.Reader.safetyDeclineOf source.kind source.safety = none →
                        Ix.CompileCert.rawRun (Ix.CompileM.compileConstantInfo info) context before =
                            (Except.ok output, after) →
                          Ix.Sharing.Verify.BlockResultCodecWF output ∧
                            (∃ blockMeta, output = Ix.CompileM.BlockResult.mk' output.block blockMeta) ∧
                              ∃ result declaration type value,
                                Ix.Kernel.Reader.readRecord (Ix.CompileCert.ExpressionRead.withBlockBlobs cx after)
                                      state output.blockAddr output.block =
                                    Except.ok result ∧
                                  result.decls = #[declaration] ∧
                                    Ix.CompileCert.DefinitionReading.related names σ source source.type type ∧
                                      Ix.CompileCert.DefinitionReading.related names σ source source.value value ∧
                                        Ix.Kernel.Reader.DefinitionDecl
                                          { name := key, levelParams := List.range source.levelParams.size,
                                            type := type }
                                          value
                                          (Ix.Kernel.Reader.projRewrite state
                                            { name := key, levelParams := List.range source.levelParams.size,
                                              type := type }
                                            value)
                                          source.kind declaration -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.DefinitionReading.constant_reads

/-- info: @Ix.CompileCert.HeaderReading.axiom_reads : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.AxiomVal) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult}
          (state : Ix.Kernel.Reader.State md) {key : Ix.Kernel.Reader.CName md},
          cx.memberKey (Ix.Kernel.ConstRef.member output.blockAddr 0) = Except.ok key →
            Ix.CompileCert.ExpressionState.ConstsSatisfy
                (Ix.CompileCert.ExpressionState.SelfName
                  (Ix.CompileCert.EmissionDispatch.singletonContext source.cnst.name context).snd (fun x => none) names)
                source.cnst.type →
              Ix.CompileCert.Emission.Clean bindings before →
                Ix.Sharing.Verify.BlockWireTablesWF before →
                  source.isUnsafe = false →
                    Ix.CompileCert.rawRun (Ix.CompileM.compileConstantInfo (Ix.ConstantInfo.axiomInfo source)) context
                          before =
                        (Except.ok output, after) →
                      Ix.Sharing.Verify.BlockResultCodecWF output ∧
                        (∃ blockMeta, output = Ix.CompileM.BlockResult.mk' output.block blockMeta) ∧
                          ∃ type,
                            Ix.CompileCert.ExpressionState.Related names
                                (Ix.CompileCert.UniversePipeline.LevelMeaning source.cnst.levelParams.toList σ id)
                                source.cnst.type type ∧
                              Ix.Kernel.Reader.readRecord (Ix.CompileCert.ExpressionRead.withBlockBlobs cx after) state
                                  output.blockAddr output.block =
                                Except.ok
                                  {
                                    decls :=
                                      #[Ix.Kernel.Declaration.axiomDecl
                                          { name := key, levelParams := List.range source.cnst.levelParams.size,
                                            type := type }] } -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.HeaderReading.axiom_reads

/-- info: 'Ix.CompileCert.DefinitionReading.constant_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.DefinitionReading.constant_reads

/-- info: 'Ix.CompileCert.DefinitionReading.constant_declines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.DefinitionReading.constant_declines

/-- info: 'Ix.CompileCert.HeaderReading.axiom_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.HeaderReading.axiom_reads

/-- info: 'Ix.CompileCert.HeaderReading.axiom_declines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.HeaderReading.axiom_declines

/-- info: 'Ix.CompileCert.HeaderReading.quotient_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.HeaderReading.quotient_reads

/-! ## Component theorems: the reader's syntactic walks

The certified reader indexes a recursor before converting it, by walking
its raw type (`stripAll`, `stripAllFull`, `appHead`, `headRef`). The
sharing builder keeps that analysis (`ReaderSpines.build_analyse`), and on
the unshared in-flight record the walks follow the source: a complete
source telescope gives the reader's telescope with every domain still
related (`ReaderSourceSpines.source_stripAllFull`), a source constant head
of a domain's last binder gives the reader's carrier reference, whose key
the source name is related to (`source_carrier`), and the compiled
recursor's result-variable walk is the source's
(`compiled_telescope_variable`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: Ix.CompileCert.ReaderSpines.build_analyse : ∀ (store : Ix.Kernel.Reader.Store) (owner : Address)
  (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Recursor) (refs : Array Address) (univs : Array Ixon.Univ)
  (output : Ixon.Constant),
  Ix.CompileM.buildConstantWithSharing limits (Ixon.ConstantInfo.recr source) refs univs = Except.ok output →
    Ix.CompileCert.ReaderSpines.AnalysisBounds
        { info := Ixon.ConstantInfo.recr source, sharing := #[], refs := refs, univs := univs } source →
      ∃ target,
        output.info = Ixon.ConstantInfo.recr target ∧
          Ix.Kernel.Reader.analyseRecursor store owner output target =
            Ix.Kernel.Reader.analyseRecursor store owner
              { info := Ixon.ConstantInfo.recr source, sharing := #[], refs := refs, univs := univs } source -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ReaderSpines.build_analyse

/-- info: @Ix.CompileCert.ReaderSourceSpines.source_carrier : ∀ {md : Ix.Kernel.Mode} (reader : Ix.Kernel.Reader.ECx md),
  reader.src.sharing = #[] →
    ∀ (owner : Address),
      Ix.CompileCert.ReaderSourceSpines.SelfAligned reader owner →
        ∀ {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {levels : Ix.Level → Ix.Kernel.Level → Prop}
          (source : Ix.Expr) (expression : Ixon.Expr),
          Ix.CompileCert.ReaderSourceSpines.SourceRead reader names levels source expression →
            ∀ (count : Nat),
              count < Ix.Kernel.Reader.spineFuel →
                ∀ (types : List Ix.Expr) (body : Ix.Expr),
                  Ix.CompileCert.ReaderSourceSpines.sourceStrip count source = some (types, body) →
                    Ix.CompileCert.ReaderSourceSpines.SourceNonForall body →
                      ∀ (domain : Ix.Expr),
                        types.getLast? = some domain →
                          Ix.CompileCert.ReaderSourceSpines.sourceAppDepth domain < Ix.Kernel.Reader.spineFuel →
                            ∀ (name : Ix.Name) (sourceLevels : Array Ix.Level) (hash : Address),
                              Ix.CompileCert.ReaderSourceSpines.sourceHead domain =
                                  Ix.Expr.const name sourceLevels hash →
                                ∃ ref key,
                                  Ix.CompileCert.ReaderSpines.carrier reader.cx.store owner reader.src expression =
                                      some ref ∧
                                    Ix.CompileCert.ReaderSourceSpines.HeadKey reader.cx ref key ∧ names name key -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ReaderSourceSpines.source_carrier

/-- info: @Ix.CompileCert.ReaderSourceSpines.compiled_telescope_variable : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (param : Nat → Ix.Kernel.LevelParam) (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName md)))
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.RecursorVal),
          Ix.CompileCert.ExpressionState.ConstsSatisfy (Ix.CompileCert.ExpressionState.SelfName context.snd self names)
              source.cnst.type →
            (∀ (rule : Ix.RecursorRule),
                rule ∈ source.rules.toList →
                  Ix.CompileCert.ExpressionState.ConstsSatisfy
                    (Ix.CompileCert.ExpressionState.SelfName context.snd self names) rule.rhs) →
              ∀ {before after : Ix.CompileM.BlockState} {output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr},
                Ix.CompileCert.ExpressionState.Good cx param self
                    (Ix.CompileCert.Emission.related param names σ
                      (Ix.CompileCert.Emission.inner source.cnst.name source.cnst.levelParams.toList context))
                    bindings before →
                  Ix.CompileCert.rawRun (Ix.CompileM.compileRecursor source) context before =
                      (Except.ok output, after) →
                    ∀ (types : List Ix.Expr) (body : Ix.Expr),
                      Ix.CompileCert.ReaderSourceSpines.sourceStrip
                            (Ix.CompileCert.ReaderSourceSpines.sourceDepth source) source.cnst.type =
                          some (types, body) →
                        Ix.CompileCert.ReaderSourceSpines.sourceAppDepth body < Ix.Kernel.Reader.spineFuel →
                          ∀ (index : Nat) (hash : Address),
                            Ix.CompileCert.ReaderSourceSpines.sourceHead body = Ix.Expr.bvar index hash →
                              ∃ rawTypes residual rawIndex,
                                Ix.Kernel.Reader.stripAll
                                      (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx.src
                                      (Ix.CompileCert.ReaderSpines.depth output.fst) output.fst.typ =
                                    some (rawTypes, residual) ∧
                                  List.Forall₂
                                      (Ix.CompileCert.ReaderSourceSpines.SourceRead
                                        (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx names
                                        (Ix.CompileCert.UniversePipeline.LevelMeaning source.cnst.levelParams.toList σ
                                          param))
                                      types rawTypes ∧
                                    Ix.Kernel.Reader.appHead
                                          (Ix.CompileCert.ExpressionRead.blockReader cx param self after).ecx.src
                                          Ix.Kernel.Reader.spineFuel residual =
                                        Ixon.Expr.var rawIndex ∧
                                      rawIndex.toNat = index -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ReaderSourceSpines.compiled_telescope_variable

/-- info: 'Ix.CompileCert.ReaderSpines.build_analyse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderSpines.build_analyse

/-- info: 'Ix.CompileCert.ReaderSourceSpines.source_stripAllFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderSourceSpines.source_stripAllFull

/-- info: 'Ix.CompileCert.ReaderSourceSpines.source_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderSourceSpines.source_carrier

/-- info: 'Ix.CompileCert.ReaderSourceSpines.compiled_telescope_variable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderSourceSpines.compiled_telescope_variable

/-! ## Component theorems: the mutual layout

A mutual block keeps one payload per class, the class's first member, with
that member's kind and constructor positions, and the sharing build's
write-back keeps both (`ProjectionLayout.mutual_block_shape`); the class
sort returns no empty class (`sort_nonempty`); the standalone inductive
family's block keeps the source's constructor positions, so its projection
records resolve under the certified reader to the block's member and
constructors (`inductive_projection_resolves`,
`constructor_projection_resolves`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: Ix.CompileCert.ProjectionLayout.mutual_block_shape : ∀ (sources : List (List Ix.MutConst)),
  Ix.CompileCert.Emission.Yields (Ix.CompileM.compileMutualBlock sources) fun output =>
    Ix.CompileCert.ProjectionLayout.blockShape output.block.info =
      some (List.map Ix.CompileCert.ProjectionLayout.sourceShape (List.filterMap List.head? sources)) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ProjectionLayout.mutual_block_shape

/-- info: Ix.CompileCert.ProjectionLayout.constructor_projection_resolves : ∀ (source : Ix.InductiveVal)
  (constructors : Array Ix.ConstructorVal) (output : Ix.CompileM.BlockResult),
  Ix.CompileCert.ProjectionLayout.InductiveLayout source constructors output →
    ∀ (store : Ix.Kernel.Reader.Store),
      store output.blockAddr = some output.block →
        ∀ (index : Nat) (inside : index < constructors.size),
          constructors[index].cidx = index →
            ∃ projection metadata,
              output.projections[index + 1]? = some (constructors[index].cnst.name, projection, metadata) ∧
                Ix.Kernel.Reader.resolveSource store (Address.admissionHash (Ixon.ser projection)) projection =
                  some (Ix.Kernel.ConstRef.ctor output.blockAddr 0 index) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ProjectionLayout.constructor_projection_resolves

/-- info: 'Ix.CompileCert.ProjectionLayout.payload_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.payload_count

/-- info: 'Ix.CompileCert.ProjectionLayout.sort_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.sort_nonempty

/-- info: 'Ix.CompileCert.ProjectionLayout.mutual_block_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.mutual_block_shape

/-- info: 'Ix.CompileCert.ProjectionLayout.dispatch_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.dispatch_layout

/-- info: 'Ix.CompileCert.ProjectionLayout.inductive_projection_resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.inductive_projection_resolves

/-- info: 'Ix.CompileCert.ProjectionLayout.constructor_projection_resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ProjectionLayout.constructor_projection_resolves

/-! ## Component theorems: a mutual block's projections

A compiled mutual block either keeps the mutual wrapper, whose rows are a
member projection per source member at its class index and a constructor
projection per constructor position, or collapses a lone definition or
recursor, every source name registered to the block itself
(`MutualArtifact.build_cases`). Under an environment without call-site
plans, a successful mutual block from a state whose tables are on the wire
decodes exactly, so do its projections, and in any store holding the block
its rows read under the certified reader as their source-indexed references
(`MutualArtifact.mutual_correct`), given non-empty classes whose members
agree in shape (`MutualProjections.ClassesAgree`, discharged from the class
sort in R9b, below) and source constructors declaring their positions. Every lemma
behind them is audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.MutualProjections.ClassesAgree : List (List Ix.MutConst) → Prop :=
fun sources =>
  ∀ (members : List Ix.MutConst),
    members ∈ sources →
      ∀ (left : Ix.MutConst),
        left ∈ members →
          ∀ (right : Ix.MutConst),
            right ∈ members →
              Ix.CompileCert.ProjectionLayout.sourceShape left = Ix.CompileCert.ProjectionLayout.sourceShape right -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.MutualProjections.ClassesAgree

/-- info: Ix.CompileCert.MutualArtifact.mutual_correct : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (sources : List (List Ix.MutConst)) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        (∀ (members : List Ix.MutConst), members ∈ sources → members ≠ []) →
          Ix.CompileCert.MutualProjections.ClassesAgree sources →
            (∀ (source : Ix.MutConst),
                source ∈ sources.flatten → Ix.CompileCert.MutualProjections.ConstructorPositions source) →
              Ix.CompileCert.rawRun (Ix.CompileM.compileMutualBlock sources) context before =
                  (Except.ok output, after) →
                Ix.Sharing.Verify.BlockResultCodecWF output ∧
                  Ix.CompileCert.MutualProjections.ProjectionWire output ∧
                    ∀ (store : Ix.Kernel.Reader.Store),
                      store output.blockAddr = some output.block →
                        Ix.CompileCert.MutualProjections.readRows store
                            (Ix.CompileCert.MutualProjections.logicalRows output.projections) =
                          Ix.CompileCert.MutualProjections.expectedReferences output.blockAddr sources -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.MutualArtifact.mutual_correct

/-- info: 'Ix.CompileCert.MutualProjections.build_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualProjections.build_rows

/-- info: 'Ix.CompileCert.MutualProjections.mutual_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualProjections.mutual_codec

/-- info: 'Ix.CompileCert.MutualProjections.build_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualProjections.build_resolves

/-- info: 'Ix.CompileCert.MutualArtifact.build_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualArtifact.build_resolves

/-- info: 'Ix.CompileCert.MutualArtifact.mutual_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualArtifact.mutual_correct

/-! ## Component theorems: Pass 1's classes (CS-01) and the compiler's classes agree (R9b)

`Ix.Compile.Canon.sortClasses` (the compiler's `sortConsts`) returns the
coarsest consistent partition of its members: its classes partition them,
any two distinct members of a class compare `eq` under the classes' own
context, and every consistent partition refines them
(`Canon.sortClasses_coarsest`); an `eq` answer relates the two members by
the comparator's identifications (`Canon.sortClasses_match`). The one
hypothesis: the members' and constructors' names are pairwise distinct
(`Canon.KeysDistinct`). Pass 1 compares names structurally throughout
(`compareRef` by `nameEq`, the class context by `nameCompareExact`, the
comparison cache by `ExactName` keys, the address map by `ExactName`), so no
hypothesis on stored hashes is needed. So the compiler's classes agree in
shape (`MutualProjections.sort_classes`), which discharges
`mutual_correct`'s class premises for the driver's two steps
(`MutualArtifact.mutual_sorted_correct`) and for its three, with the
recursor-family order between them (`MutualArtifact.mutual_ordered_correct`,
N-READS N5 a: `orderRecursorFamily` permutes the classes). Every lemma behind
them is audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.Canon.KeysDistinct : List Ix.MutConst → Prop :=
fun ms => (List.flatMap Ix.CompileCert.Canon.keysOf ms).Nodup -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.Canon.KeysDistinct

/-- info: def Ix.CompileCert.Canon.Consistent : (Ix.Name → Option Address) → List (List Ix.MutConst) → Prop :=
fun addr? P =>
  ∀ (C : List Ix.MutConst),
    C ∈ P →
      ∀ (a : Ix.MutConst),
        a ∈ C →
          ∀ (b : Ix.MutConst),
            b ∈ C → a ≠ b → Ix.CompileCert.Canon.constOrd addr? (Ix.MutConst.ctx P) a b = Except.ok Ordering.eq -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.Canon.Consistent

/-- info: Ix.CompileCert.Canon.sortClasses_coarsest : ∀ (rules : Ix.Compile.Canon.Rules) {addr? : Ix.Name → Option Address}
  {sources : List Ix.MutConst},
  Ix.CompileCert.Canon.KeysDistinct sources →
    ∀ {F : List (List Ix.MutConst)} {stats : Ix.Compile.Canon.SortStats},
      Ix.Compile.Canon.sortClasses rules addr? sources = Except.ok (F, stats) →
        Ix.CompileCert.Canon.Partition F sources ∧
          Ix.CompileCert.Canon.Consistent addr? F ∧ Ix.CompileCert.Canon.Coarsest addr? sources F -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Canon.sortClasses_coarsest

/-- info: Ix.CompileCert.Canon.sortClasses_match : ∀ (rules : Ix.Compile.Canon.Rules) {addr? : Ix.Name → Option Address}
  {sources : List Ix.MutConst},
  Ix.CompileCert.Canon.KeysDistinct sources →
    ∀ {F : List (List Ix.MutConst)} {stats : Ix.Compile.Canon.SortStats},
      Ix.Compile.Canon.sortClasses rules addr? sources = Except.ok (F, stats) →
        ∀ (C : List Ix.MutConst),
          C ∈ F →
            ∀ (a : Ix.MutConst),
              a ∈ C →
                ∀ (b : Ix.MutConst),
                  b ∈ C →
                    a ≠ b → Ix.CompileCert.Canon.ConstMatch (Ix.CompileCert.Canon.ctxOf addr? (Ix.MutConst.ctx F)) a b -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.Canon.sortClasses_match

/-- info: Ix.CompileCert.MutualProjections.sort_classes : ∀ (sources : List Ix.MutConst),
  Ix.CompileCert.Canon.KeysDistinct sources →
    Ix.CompileCert.Emission.Yields (Ix.CompileM.sortConsts sources) fun classes =>
      Ix.CompileCert.Canon.Partition classes sources ∧ Ix.CompileCert.MutualProjections.ClassesAgree classes -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.MutualProjections.sort_classes

/-- info: Ix.CompileCert.MutualArtifact.mutual_sorted_correct : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (members : List Ix.MutConst) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        Ix.CompileCert.Canon.KeysDistinct members →
          (∀ (member : Ix.MutConst), member ∈ members → Ix.CompileCert.MutualProjections.ConstructorPositions member) →
            Ix.CompileCert.rawRun (Ix.CompileM.sortConsts members >>= Ix.CompileM.compileMutualBlock) context before =
                (Except.ok output, after) →
              ∃ classes,
                Ix.CompileCert.Canon.Partition classes members ∧
                  Ix.Sharing.Verify.BlockResultCodecWF output ∧
                    Ix.CompileCert.MutualProjections.ProjectionWire output ∧
                      ∀ (store : Ix.Kernel.Reader.Store),
                        store output.blockAddr = some output.block →
                          Ix.CompileCert.MutualProjections.readRows store
                              (Ix.CompileCert.MutualProjections.logicalRows output.projections) =
                            Ix.CompileCert.MutualProjections.expectedReferences output.blockAddr classes -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.MutualArtifact.mutual_sorted_correct

/-- info: Ix.CompileCert.MutualArtifact.mutual_ordered_correct : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ (members : List Ix.MutConst) {before after : Ix.CompileM.BlockState} {output : Ix.CompileM.BlockResult},
      Ix.Sharing.Verify.BlockWireTablesWF before →
        Ix.CompileCert.Canon.KeysDistinct members →
          (∀ (member : Ix.MutConst), member ∈ members → Ix.CompileCert.MutualProjections.ConstructorPositions member) →
            Ix.CompileCert.rawRun
                  (do
                    let sorted ← Ix.CompileM.sortConsts members
                    Ix.CompileM.compileMutualBlock (Ix.CompileM.orderRecursorFamily sorted))
                  context before =
                (Except.ok output, after) →
              ∃ classes,
                Ix.CompileCert.Canon.Partition classes members ∧
                  Ix.Sharing.Verify.BlockResultCodecWF output ∧
                    Ix.CompileCert.MutualProjections.ProjectionWire output ∧
                      ∀ (store : Ix.Kernel.Reader.Store),
                        store output.blockAddr = some output.block →
                          Ix.CompileCert.MutualProjections.readRows store
                              (Ix.CompileCert.MutualProjections.logicalRows output.projections) =
                            Ix.CompileCert.MutualProjections.expectedReferences output.blockAddr classes -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.MutualArtifact.mutual_ordered_correct

/-- info: 'Ix.CompileCert.Canon.constOrd_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.constOrd_total

/-- info: 'Ix.CompileCert.Canon.sortClasses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.sortClasses_eq

/-- info: 'Ix.CompileCert.Canon.sortClasses_coarsest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.sortClasses_coarsest

/-- info: 'Ix.CompileCert.Canon.compareExpr_eq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.compareExpr_eq_sound

/-- info: 'Ix.CompileCert.Canon.sortClasses_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.Canon.sortClasses_match

/-- info: 'Ix.CompileCert.MutualProjections.sort_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualProjections.sort_classes

/-- info: 'Ix.CompileCert.MutualArtifact.mutual_sorted_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualArtifact.mutual_sorted_correct

/-- info: 'Ix.CompileCert.MutualArtifact.mutual_ordered_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.MutualArtifact.mutual_ordered_correct

/-! ## Component theorems: the reader's recursor index

The certified reader indexes recursors by their own records (SP3 D8)
before reading (`Ix.Kernel.Reader.buildIndex`). Every block shape's order
was validated against the block's record, so a compiled standalone family
is indexed at member 0 exactly (`ReaderIndex.buildIndex_singleton_order`);
every indexed recursor comes from a scanned record whose analysis gave its
entry, and every recursor of a block shape is indexed at that block
(`buildIndex_valid`); over records coherent with the store, the reader's
lookups for a shape's recursors succeed (`grouped_lookup`), every eligible
recursor's block and motive is covered (`ReaderIndexDiscovery.buildIndex_covers`),
and the index holds one recursor per block and motive
(`buildIndex_role_unique`). Every lemma behind them is audited in
`Ix.CompileCert.ReadingAudit`. -/

/-- info: Ix.CompileCert.ReaderIndex.buildIndex_singleton_order : ∀ (store : Ix.Kernel.Reader.Store)
  (records : Array (Address × Ixon.Constant)) (owner : Address) (constant : Ixon.Constant) (source : Ixon.Inductive)
  (shape : Ix.Kernel.Reader.BlockShape),
  store owner = some constant →
    constant.info = Ixon.ConstantInfo.muts #[Ixon.MutConst.indc source] →
      (Ix.Kernel.Reader.buildIndex store records).blocks[owner]? = some shape → shape.order = #[0] -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ReaderIndex.buildIndex_singleton_order

/-- info: Ix.CompileCert.ReaderIndexDiscovery.buildIndex_covers : ∀ (store : Ix.Kernel.Reader.Store)
  (records : Array (Address × Ixon.Constant)),
  Ix.CompileCert.ReaderIndex.Coherent store records →
    ∀ (ref : Ix.Kernel.ConstRef Address) (entry : Ix.Kernel.Reader.RecEntry),
      Ix.CompileCert.ReaderIndex.From store records ref entry →
        ∃ selected chosen shape,
          (Ix.Kernel.Reader.buildIndex store records).recs[selected]? = some chosen ∧
            chosen.block = entry.block ∧
              chosen.motive = entry.motive ∧
                (Ix.Kernel.Reader.buildIndex store records).blocks[entry.block]? = some shape ∧
                  selected ∈ shape.recs ∧ Ix.CompileCert.ReaderIndex.From store records selected chosen -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.ReaderIndexDiscovery.buildIndex_covers

/-- info: 'Ix.CompileCert.ReaderIndex.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndex.run_eq

/-- info: 'Ix.CompileCert.ReaderIndex.buildIndex_singleton_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndex.buildIndex_singleton_order

/-- info: 'Ix.CompileCert.ReaderIndex.compiled_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndex.compiled_order

/-- info: 'Ix.CompileCert.ReaderIndex.grouped_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndex.grouped_lookup

/-- info: 'Ix.CompileCert.ReaderIndexDiscovery.buildIndex_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndexDiscovery.buildIndex_covers

/-- info: 'Ix.CompileCert.ReaderIndexDiscovery.buildIndex_role_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.ReaderIndexDiscovery.buildIndex_role_unique

/-! ## Component theorems: compiled standalone inductives are read back as their sources

Public dispatch of an inductive, under an environment without call-site
plans, from a clean state whose tables are on the wire, returns a block
that decodes exactly and that the certified reader's `readRecord` (over the
block's blobs overlaid on the context's) reads as `lowerInductive` of the
`BlockRead` the source describes (`InductiveReading.sourceBlock`): the
inductive under its key with the level parameters `0, …, n - 1` and a type
`Related` to the source's, its constructors in source order under their
keys with related types, and the recursors the reader reads from their own
records (`readRecursors`, whose correspondence with the compiled recursors
is R10b); given the index shaping the block at member 0 (derived from the
reader's own index in `inductive_reads_indexed`), the keys reading, the
self references (the family's name related to its key, R13's half, and no
constructor of the family in its types, `NoCtorIn`, N-READS N4: proved from
Source acceptance by `Ix.Cert.NoCtor.inductive_reads_sourceAccepts`), and a
well-formed source. Without a recursor in the input the block declines.
Every lemma behind them is audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.InductiveReading.sourceBlock : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Reader.CName md →
    (Nat → Ix.Kernel.Reader.CName md) →
      Ix.Kernel.Reader.CExpr md →
        List (Ix.Kernel.Reader.CExpr md) →
          Ix.InductiveVal →
            Array Ix.ConstructorVal →
              Array (Ix.Kernel.Reader.CVal md × Ix.Kernel.Reader.RecCounts × List (Ix.Kernel.RecRule md)) →
                Ix.Kernel.Reader.BlockRead md :=
fun {md} key ctorKey type ctorTypes source constructors recs =>
  { numParams := source.numParams,
    types :=
      #[({ name := key, levelParams := List.range source.cnst.levelParams.size, type := type }, source.numParams,
          source.numIndices)],
    ctors := (Ix.CompileCert.InductiveReading.sourceCtorReads ctorKey 0 constructors.toList ctorTypes).toArray,
    ctorNames :=
      #[List.map (fun x => x.fst.name)
          (Ix.CompileCert.InductiveReading.sourceCtorReads ctorKey 0 constructors.toList ctorTypes)],
    recs := recs } -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.InductiveReading.sourceBlock

/-- info: def Ix.CompileCert.InductiveReading.NoCtorIn : Array Ix.ConstructorVal → Ix.Expr → Prop :=
fun constructors =>
  Ix.CompileCert.ExpressionState.ConstsSatisfy fun name =>
    ∀ (ctor : Ix.ConstructorVal), ctor ∈ constructors.toList → name ≠ ctor.cnst.name -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.InductiveReading.NoCtorIn

/-- info: @Ix.CompileCert.InductiveReading.inductive_reads : ∀ {md : Ix.Kernel.Mode} (cx : Ix.Kernel.Reader.Ctx md)
  (names : Ix.Name → Ix.Kernel.Reader.CName md → Prop) (σ : Ix.Name → Ix.Kernel.LevelParam)
  (bindings : Ix.CompileCert.ExpressionState.Bindings) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    (∀ (address : Address), cx.blob address = context.fst.blobs.get? address) →
      Ix.CompileCert.ExpressionState.BindingsCorrect context.fst bindings cx names →
        ∀ (source : Ix.InductiveVal) (constructors : Array Ix.ConstructorVal) {before after : Ix.CompileM.BlockState}
          {output : Ix.CompileM.BlockResult},
          (Ix.CompileCert.rawRun (Ix.CompileM.lookupInductiveConstructors source)
                  (Ix.CompileCert.EmissionDispatch.singletonContext source.cnst.name context) before).fst =
              Except.ok constructors →
            ∀ (state : Ix.Kernel.Reader.State md) {shape : Ix.Kernel.Reader.BlockShape},
              cx.index.blocks[output.blockAddr]? = some shape →
                shape.order = #[0] →
                  ∀ {key : Ix.Kernel.Reader.CName md},
                    cx.memberKey (Ix.Kernel.ConstRef.member output.blockAddr 0) = Except.ok key →
                      ∀ (ctorKey : Nat → Ix.Kernel.Reader.CName md),
                        (∀ (j : Nat),
                            j < constructors.size →
                              cx.memberKey (Ix.Kernel.ConstRef.ctor output.blockAddr 0 j) = Except.ok (ctorKey j)) →
                          names source.cnst.name key →
                            Ix.CompileCert.InductiveReading.NoCtorIn constructors source.cnst.type →
                              (∀ (ctor : Ix.ConstructorVal),
                                  ctor ∈ constructors.toList →
                                    Ix.CompileCert.InductiveReading.NoCtorIn constructors ctor.cnst.type) →
                                source.isUnsafe = false →
                                  (∀ (ctor : Ix.ConstructorVal), ctor ∈ constructors.toList → ctor.isUnsafe = false) →
                                    (∀ (j : Nat) (inside : j < constructors.size), constructors[j].cidx = j) →
                                      (∀ (ctor : Ix.ConstructorVal),
                                          ctor ∈ constructors.toList →
                                            ∃ types body,
                                              Ix.CompileCert.ReaderSourceSpines.sourceStrip
                                                    (source.numParams + ctor.numFields) ctor.cnst.type =
                                                  some (types, body) ∧
                                                Ix.CompileCert.ReaderSourceSpines.SourceNonForall body) →
                                        Ix.CompileCert.Emission.Clean bindings before →
                                          Ix.Sharing.Verify.BlockWireTablesWF before →
                                            Ix.CompileCert.rawRun
                                                  (Ix.CompileM.compileConstantInfo (Ix.ConstantInfo.inductInfo source))
                                                  context before =
                                                (Except.ok output, after) →
                                              Ix.Sharing.Verify.BlockResultCodecWF output ∧
                                                Ix.CompileCert.ProjectionLayout.InductiveLayout source constructors
                                                    output ∧
                                                  ∃ type ctorTypes,
                                                    Ix.CompileCert.InductiveReading.related names σ source
                                                        source.cnst.type type ∧
                                                      List.Forall₂
                                                          (Ix.CompileCert.InductiveReading.related names σ source)
                                                          (List.map (fun x => x.cnst.type) constructors.toList)
                                                          ctorTypes ∧
                                                        Ix.Kernel.Reader.readRecord
                                                            (Ix.CompileCert.ExpressionRead.withBlockBlobs cx after)
                                                            state output.blockAddr output.block =
                                                          do
                                                          let recs ←
                                                            Ix.CompileCert.InductiveReading.readRecursors
                                                                (Ix.CompileCert.ExpressionRead.withBlockBlobs cx after)
                                                                (List.range source.cnst.levelParams.size) shape.recs
                                                          Ix.Kernel.Reader.lowerInductive state
                                                              (Ix.CompileCert.InductiveReading.sourceBlock key ctorKey
                                                                type ctorTypes source constructors recs) -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.InductiveReading.inductive_reads

/-- info: 'Ix.CompileCert.InductiveReading.readInductive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.InductiveReading.readInductive_eq

/-- info: 'Ix.CompileCert.InductiveReading.readRecord_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.InductiveReading.readRecord_singleton

/-- info: 'Ix.CompileCert.InductiveReading.inductive_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.InductiveReading.inductive_reads

/-- info: 'Ix.CompileCert.InductiveReading.inductive_reads_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.InductiveReading.inductive_reads_indexed

/-- info: 'Ix.CompileCert.InductiveReading.inductive_declines_unindexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.InductiveReading.inductive_declines_unindexed

/-! ## Component theorems: what Source mode admits of an inductive block (R12)

Source mode's group and conversion of an inductive block
(`Ix.LeanIngress.inductiveGroup`, `convertInductive`) check every
constructor's position, every member's and constructor's safety, one
`numParams`, and every constructor's type as a telescope of the parameters
and its fields (`inductiveGroup_spec`, `convertInductive_spec`,
`strip_of_ingress`). The compiler resolves a family's constructors through
its environment (`collect_lookups`, `mkIndc_lookups`). So where the compile
environment resolves a Source-admitted block's constructor names as
Source's input does (`Ix.Cert.compile` compiles the environment Source mode
checks), `InductiveReading.inductive_reads`' safety, position and telescope
premises hold (`source_premises`, `inductive_reads_source`), and so do R9a's
`ConstructorPositions` for the compiler's mutual members
(`mkIndc_positions`). The self references stay premises (N-READS). Every
lemma behind them is audited in `Ix.CompileCert.ReadingAudit`. -/

/-- info: def Ix.CompileCert.SourceConstructorPositions.Admits : Ix.Environment → Ix.InductiveVal → Prop :=
fun env first =>
  ∃ cands converted, Ix.LeanIngress.convert (Ix.LeanIngress.inductiveGroup env first cands) = Except.ok converted -/
#guard_msgs (whitespace := lax) in
#print Ix.CompileCert.SourceConstructorPositions.Admits

/-- info: Ix.CompileCert.SourceConstructorPositions.source_premises : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv),
  context.fst.surgeryFree = true →
    ∀ {env : Ix.Environment} {first : Ix.InductiveVal},
      Ix.CompileCert.SourceConstructorPositions.Admits env first →
        ∀ {source : Ix.InductiveVal},
          source.cnst.name ∈ first.all.toList →
            env.consts.get? source.cnst.name = some (Ix.ConstantInfo.inductInfo source) →
              (∀ (n : Ix.Name), n ∈ source.ctors.toList → context.fst.env.get? n = env.consts.get? n) →
                ∀ {constructors : Array Ix.ConstructorVal} {before : Ix.CompileM.BlockState},
                  (Ix.CompileCert.rawRun (Ix.CompileM.lookupInductiveConstructors source)
                          (Ix.CompileCert.EmissionDispatch.singletonContext source.cnst.name context) before).fst =
                      Except.ok constructors →
                    source.isUnsafe = false ∧
                      (∀ (ctor : Ix.ConstructorVal), ctor ∈ constructors.toList → ctor.isUnsafe = false) ∧
                        (∀ (j : Nat) (inside : j < constructors.size), constructors[j].cidx = j) ∧
                          ∀ (ctor : Ix.ConstructorVal),
                            ctor ∈ constructors.toList →
                              ∃ types body,
                                Ix.CompileCert.ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields)
                                      ctor.cnst.type =
                                    some (types, body) ∧
                                  Ix.CompileCert.ReaderSourceSpines.SourceNonForall body -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.SourceConstructorPositions.source_premises

/-- info: Ix.CompileCert.SourceConstructorPositions.mkIndc_positions : ∀ (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
  {env : Ix.Environment} {first : Ix.InductiveVal},
  Ix.CompileCert.SourceConstructorPositions.Admits env first →
    ∀ {i : Ix.InductiveVal},
      i.cnst.name ∈ first.all.toList →
        env.consts.get? i.cnst.name = some (Ix.ConstantInfo.inductInfo i) →
          (∀ (n : Ix.Name), n ∈ i.ctors.toList → context.fst.env.get? n = env.consts.get? n) →
            ∀ {state : Ix.CompileM.BlockState} {m : Ix.MutConst},
              (Ix.CompileCert.rawRun (Ix.CompileM.MutConst.mkIndc i) context state).fst = Except.ok m →
                Ix.CompileCert.MutualProjections.ConstructorPositions m -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.SourceConstructorPositions.mkIndc_positions

/-- info: 'Ix.CompileCert.SourceConstructorPositions.inductiveGroup_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.inductiveGroup_spec

/-- info: 'Ix.CompileCert.SourceConstructorPositions.convertInductive_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.convertInductive_spec

/-- info: 'Ix.CompileCert.SourceConstructorPositions.strip_of_ingress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.strip_of_ingress

/-- info: 'Ix.CompileCert.SourceConstructorPositions.source_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.source_premises

/-- info: 'Ix.CompileCert.SourceConstructorPositions.mkIndc_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.mkIndc_positions

/-- info: 'Ix.CompileCert.SourceConstructorPositions.inductive_reads_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.CompileCert.SourceConstructorPositions.inductive_reads_source

/-! ## CQP.4 (a): the driver's schedule is a fold

`Ix.CompileM.compileEnvFold`, the driver of `Ix.Cert.compile` and of the IO
pipeline, is its sequential form (`Ix.Cert.Schedule.compileEnvFoldSeq`):
each wave's ready blocks, in block-key order, each block's outcome computed
against the wave's snapshot, applied one by one (`applySeq`). The tasks a
wave is split into are contiguous slices of the ready blocks and a spawned
task's value is its function's, so the split (`width`) and the trace
(`dbg`) change nothing (`compileEnvFold_width`); the IO pipeline's
`IO.lazyPure` is `pure` of the value (`lazyPure_eq`). Blocks of one wave
being independent (the reference schedule) stays a test
(`compile-schedule-identity`, `cert-compile-parity-init`). -/

/-- info: [cert-audit] schedule: 12 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] schedule: 4 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "schedule"
    (#[`slices_flatten, `ceil_mul_ge, `chunks_cover, `slices_map, `waveTasks_flatten, `applyTasks_eq,
      `foldWave_eq_with, `foldWave_eq, `foldWaves_eq, `compileEnvFold_eq_seq, `compileEnvFold_width,
      `lazyPure_eq].map (`Ix.Cert.Schedule ++ ·))
  checkRuntime (tag := "cert-audit") "schedule"
    #[``Ix.CompileM.waveTasks, ``Ix.CompileM.foldWave, ``Ix.CompileM.foldWaves, ``Ix.CompileM.compileEnvFold]

/-- info: def Ix.Cert.Schedule.applySeq : Ix.CompileM.CompileEnv →
  Array (Ix.Name × Ix.Name × Ix.Set Ix.Name) → Ix.CompileM.DriverAcc → Ix.CompileM.DriverAcc :=
fun snapshot ready acc =>
  Array.foldl
    (fun acc x =>
      match x with
      | (key, fst, all) =>
        (Ix.CompileM.applyAuxBlockOutcome acc key all (Ix.CompileM.auxBlockOutcome snapshot key all)).fst)
    acc ready -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Schedule.applySeq

/-- info: Ix.Cert.Schedule.compileEnvFold_eq_seq : ∀ (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (dbg : Bool)
  (unmaterialized : Nat) (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat),
  Ix.CompileM.compileEnvFold env blocks dbg unmaterialized sharingLimits width =
    Ix.Cert.Schedule.compileEnvFoldSeq env blocks unmaterialized sharingLimits -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Schedule.compileEnvFold_eq_seq

/-- info: Ix.Cert.Schedule.compileEnvFold_width : ∀ (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (dbg dbg' : Bool)
  (unmaterialized : Nat) (sharingLimits : Ix.Sharing.Exact.Limits) (width width' : Nat),
  Ix.CompileM.compileEnvFold env blocks dbg unmaterialized sharingLimits width =
    Ix.CompileM.compileEnvFold env blocks dbg' unmaterialized sharingLimits width' -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Schedule.compileEnvFold_width

/-- info: 'Ix.Cert.Schedule.applyTasks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Schedule.applyTasks_eq

/-- info: 'Ix.Cert.Schedule.foldWaves_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Schedule.foldWaves_eq

/-- info: 'Ix.Cert.Schedule.compileEnvFold_eq_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Schedule.compileEnvFold_eq_seq

/-- info: 'Ix.Cert.Schedule.compileEnvFold_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Schedule.compileEnvFold_width

/-! ## CQP.4 (b): the hybrid environment compiles as the materialized one

The driver and its validations read the environment through
`Ix.Environment.get?` only, apart from the order of the inductive groups
they check (`Ix.Cert.Hybrid.groupOrder`). So two environments with the same
lookups, the same group order and the same source count compile alike under
every schedule (`compileEnvFold_lookups`), and the IO pipeline's hybrid
environment (`hybridEnv`), whose fallback computes the canonicalization's
specification (`fallback_spec`, from C1), folds as `Ix.Cert.compile`'s
materialized environment does (`pipeline_fold`), given that the latter is
the input's canonicalization and the code constants are its own and hold
exactly its inductives; the validations' group order follows
(`groupOrder_eq`, `hybrid_heads`) and is no longer a premise. The
restatement's bound on the source-claim walk changes nothing
(`sourceClaimOwned_fuel`, `pipeline_walk`). The IO pipeline's own loops,
its front end (canonicalization, graph, ground filter, condensation) and
the blocks' independence within a wave stay tested. -/

-- groupOrder (2026-10-19): the runtime check lists the production edit's
-- `groupHeads` (which replaces `inductiveGroups`), `groupAll` and `orderedGroups`
-- (8 → 10 safe definitions).
/-- info: [cert-audit] hybrid: 23 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] hybrid: 10 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "hybrid"
    (#[`uniformSafety_eq, `mixedSafetyMessage_eq, `validateMutualSafety_eq, `validateInductiveFlags_eq,
      `compileEnvFold_lookups, `fallback_spec, `hybrid_lookups, `pipeline_fold, `filter_length_mono,
      `filter_length_lt, `measure_push, `idBind, `fuel_exit, `forIn_measure, `sourceClaimOwned_fuel,
      `sourceClaimOwned_lookups, `view_get, `hybrid_invariant, `hybrid_covers,
      `pipeline_walk, `mem_groupHeads, `groupOrder_eq, `hybrid_heads].map (`Ix.Cert.Hybrid ++ ·))
  checkRuntime (tag := "cert-audit") "hybrid"
    #[``Ix.CompileM.validateInductiveFlags, ``Ix.CompileM.validateMutualSafety, ``Ix.CompileM.uniformSafety,
      ``Ix.CompileM.mixedSafetyMessage, ``Ix.CompileM.groupHeads, ``Ix.CompileM.groupAll,
      ``Ix.CompileM.orderedGroups, ``Ix.AuxGen.sourceClaimOwned, ``Ix.Environment.get?,
      ``Ix.CanonM.canonChunk]

-- groupOrder (2026-10-19, flagged production edit in Ix/CompileDriver.lean): the
-- validations' group order is now `orderedGroups` (the first members as a
-- `Std.TreeSet` under `Ix.nameCompareExact`, each with its own `all`), and
-- `groupOrder` restates it; re-frozen.
/-- info: def Ix.Cert.Hybrid.groupOrder : Ix.Environment → Array (Ix.Name × Array Ix.Name) :=
fun env => Ix.CompileM.orderedGroups env -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Hybrid.groupOrder

/-- info: def Ix.Cert.Hybrid.hybridEnv : Std.HashMap Ix.Name Ix.ConstantInfo →
  Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo) → Ix.Environment :=
fun codeConsts leanByIx =>
  { consts := codeConsts,
    fallback? :=
      some fun n =>
        (leanByIx.get? n).bind fun x =>
          match x with
          | (ln, lci) => Option.map (fun x => x.snd) (Ix.CanonM.canonChunk #[(ln, lci)])[0]? } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Hybrid.hybridEnv

/-- info: @Ix.Cert.Hybrid.compileEnvFold_lookups : ∀ {e₁ e₂ : Ix.Environment},
  (∀ (n : Ix.Name), e₁.get? n = e₂.get? n) →
    Ix.Cert.Hybrid.groupOrder e₁ = Ix.Cert.Hybrid.groupOrder e₂ →
      ∀ {u₁ u₂ : Nat},
        e₁.consts.size + u₁ = e₂.consts.size + u₂ →
          ∀ (blocks : Ix.CondensedBlocks) (dbg dbg' : Bool) (sharingLimits : Ix.Sharing.Exact.Limits)
            (width width' : Nat),
            Ix.CompileM.compileEnvFold e₁ blocks dbg u₁ sharingLimits width =
              Ix.Cert.Hybrid.restore e₁ u₁ <$> Ix.CompileM.compileEnvFold e₂ blocks dbg' u₂ sharingLimits width' -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Hybrid.compileEnvFold_lookups

-- groupOrder (2026-10-19): `pipeline_fold`'s premise that the two environments'
-- groups agree in order is gone (proved: `groupOrder_eq`, `hybrid_heads`); in its
-- place the IO layer's `inductives` (the code constants hold exactly the input's
-- inductives), tested like `code`; re-frozen.
/-- info: Ix.Cert.Hybrid.pipeline_fold : ∀ (full : Ix.Environment) (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
  (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)),
  (∀ (n : Ix.Name), full.get? n = Option.map (fun p => Ix.Cert.Canon.constS p.snd) (leanByIx.get? n)) →
    (∀ (n : Ix.Name) (ci : Ix.ConstantInfo), codeConsts.get? n = some ci → full.get? n = some ci) →
      codeConsts.size ≤ leanByIx.size ∧ full.consts.size = leanByIx.size →
        (∀ (n : Ix.Name) (v : Ix.InductiveVal),
            (n, Ix.ConstantInfo.inductInfo v) ∈ codeConsts.toList ↔
              (n, Ix.ConstantInfo.inductInfo v) ∈ full.consts.toList) →
          ∀ (blocks : Ix.CondensedBlocks) (dbg : Bool) (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat),
            Ix.CompileM.compileEnvFold (Ix.Cert.Hybrid.hybridEnv codeConsts leanByIx) blocks dbg
                (leanByIx.size - codeConsts.size) sharingLimits width =
              Ix.Cert.Hybrid.restore (Ix.Cert.Hybrid.hybridEnv codeConsts leanByIx)
                  (leanByIx.size - codeConsts.size) <$>
                Ix.CompileM.compileEnvFold full blocks false 0 sharingLimits -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Hybrid.pipeline_fold

/-- info: Ix.Cert.Hybrid.pipeline_walk : ∀ (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
  (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)),
  (∀ (n : Ix.Name), codeConsts.contains n = true → leanByIx.contains n = true) →
    ∀ (owners : Std.HashSet Ix.Name) (name : Ix.Name) {k k' : Nat},
      leanByIx.size ≤ k →
        leanByIx.size ≤ k' →
          Ix.AuxGen.sourceClaimOwned
                { consts := ∅, fallback? := some (Ix.Cert.Hybrid.hybridEnv codeConsts leanByIx).get? } owners name k =
              Ix.AuxGen.sourceClaimOwned (Ix.Cert.Hybrid.hybridEnv codeConsts leanByIx) owners name k' ∧
            ∃ b, Ix.AuxGen.sourceClaimOwned (Ix.Cert.Hybrid.hybridEnv codeConsts leanByIx) owners name k' = Except.ok b -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Hybrid.pipeline_walk

/-- info: 'Ix.Cert.Hybrid.compileEnvFold_lookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Hybrid.compileEnvFold_lookups

/-- info: 'Ix.Cert.Hybrid.pipeline_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Hybrid.pipeline_fold

/-- info: 'Ix.Cert.Hybrid.sourceClaimOwned_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Hybrid.sourceClaimOwned_fuel

/-- info: 'Ix.Cert.Hybrid.pipeline_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Hybrid.pipeline_walk

/-! ## Route A, B3: the reader succeeds over the compiled closure's stream

The certified entry's preparation (`Ix.Kernel.Admission.prepareWith`)
succeeds on the compiled closure (`Ix.Cert.Stream.closure_prepares`): the
byte stage holds for the artifact `compile` returns (unique keys from an
order of distinct addresses and the blob map, authentication from
`compileAuthentic`, batch limits and canonical decoding within some limits,
given that every stored record decodes to a wire-valid constant whose
canonical encoding is its stored bytes, `StoredCanonical`), and the reader's
stream succeeds on every record-by-record reading (`readRecords_complete`,
the converse of IxC's `readRecords_spec`). With the fold's acceptance under
the committed prelude that is `IxonAccepts` (`closure_accepts`).
`StoredCanonical` (R13, from R7e's per-block codec) and the stream reading
(N-READS) stay obligations. -/

/-- info: [cert-audit] stream: 22 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] stream: 11 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "stream"
    (#[`streamRead_cons_inv, `forIn_complete, `readRecords_loop, `readRecords_complete, `readStream_complete,
      `recordsOf_cons, `decodedOf_cons, `recordsOf_keys, `decodedOf_keys, `mem_blobsOf, `blobsOf_keys,
      `closure_unique, `mem_recordsOf, `closure_authentic, `size_le_payload, `nodes_le, `closure_reads,
      `closure_decodes, `prepareWith_ok, `closure_prepares, `checkBytesUsing_ok,
      `closure_accepts].map (`Ix.Cert.Stream ++ ·))
  checkRuntime (tag := "cert-audit") "stream"
    #[``Ix.Kernel.Admission.preflight, ``Ix.Kernel.Admission.uniqueKeys, ``Ix.Kernel.Admission.authenticate,
      ``Ix.Kernel.Admission.decodeRecords, ``Ix.Kernel.Admission.prepareWith,
      ``Ix.Kernel.Admission.readStream, ``Ix.Kernel.Admission.checkBytesWith,
      ``Ix.Kernel.Admission.checkBytesUsing, ``Ix.Kernel.Admission.checkBytes,
      ``Ix.Kernel.Reader.readRecords, ``Ixon.Authenticated.checkBytes]

/-- info: def Ix.Cert.Stream.StoredCanonical : Ixon.Env → List Address → Prop :=
fun ixe order =>
  ∀ (a : Address),
    a ∈ order →
      ∀ (lc : Ixon.LazyConstant),
        ixe.consts.get? a = some lc → ∃ c, lc.get? = some c ∧ c.wireWF ∧ Ixon.serConstant c = lc.rawBytes -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Stream.StoredCanonical

/-- info: @Ix.Cert.Stream.readRecords_complete : ∀ {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
  {st st' : Ix.Kernel.Reader.State md} {records : List (Address × Ixon.Constant)}
  {out : Array (Ix.Kernel.Reader.CDecl md)},
  Ix.Kernel.Reader.StreamRead cx st records st' out →
    (List.map Prod.fst records).Nodup → Ix.Kernel.Reader.readRecords cx st records.toArray = Except.ok (st', out) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Stream.readRecords_complete

/-- info: @Ix.Cert.Stream.closure_prepares : ∀ {env : Ix.Environment} {ixe : Ixon.Env},
  Ix.Cert.compile env = Except.ok ixe →
    ∀ {order : List Address},
      order.Nodup →
        Ix.Cert.Stream.StoredCanonical ixe order →
          ∀ {binding : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable},
            Ix.Kernel.Admission.admitBinding Address.admissionHash binding = Except.ok t →
              ∀ (pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon) {st' : Ix.Kernel.Reader.State Ix.Kernel.Mode.anon}
                {decls : Array (Ix.Kernel.Reader.CDecl Ix.Kernel.Mode.anon)},
                Ix.Kernel.Reader.StreamRead
                    (Ix.Kernel.Admission.streamContext Address.admissionHash t pre (Ix.Cert.Stream.decodedOf ixe order)
                      (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe))
                    pre.state (Ix.Cert.Stream.decodedOf ixe order) st' decls →
                  ∃ limits,
                    Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits
                        (Ix.Cert.recordsOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) =
                      Except.ok
                        (Ix.Kernel.Reader.evidenceOf
                            (Ix.Kernel.Admission.streamContext Address.admissionHash t pre
                              (Ix.Cert.Stream.decodedOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe))
                            st' t,
                          Ix.Kernel.Frontend.preparePrelude pre.ix decls) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Stream.closure_prepares

/-- info: @Ix.Cert.Stream.closure_accepts : ∀ {env : Ix.Environment} {ixe : Ixon.Env},
  Ix.Cert.compile env = Except.ok ixe →
    ∀ {S : Address → Prop} {order : List Address},
      Ix.Cert.ClosureOrder ixe S order →
        Ix.Cert.Stream.StoredCanonical ixe order →
          ∀ {binding : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable},
            Ix.Kernel.Admission.admitBinding Address.admissionHash binding = Except.ok t →
              ∀ {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon},
                Ix.Kernel.Reader.preludeFor t = Except.ok pre →
                  ∀ {st' : Ix.Kernel.Reader.State Ix.Kernel.Mode.anon}
                    {decls : Array (Ix.Kernel.Reader.CDecl Ix.Kernel.Mode.anon)},
                    Ix.Kernel.Reader.StreamRead
                        (Ix.Kernel.Admission.streamContext Address.admissionHash t pre
                          (Ix.Cert.Stream.decodedOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe))
                        pre.state (Ix.Cert.Stream.decodedOf ixe order) st' decls →
                      ∀ {envA : Ix.Kernel.Env Ix.Kernel.Mode.anon},
                        Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified
                              (Ix.Kernel.Reader.evidenceOf
                                (Ix.Kernel.Admission.streamContext Address.admissionHash t pre
                                  (Ix.Cert.Stream.decodedOf ixe order) (Ix.Cert.blobsOf ixe order)
                                  (Ix.Cert.hintsOf ixe))
                                st' t)
                              (Ix.Kernel.Frontend.preparePrelude pre.ix decls) =
                            Except.ok envA →
                          ∃ limits, Ix.Cert.IxonAccepts binding limits ixe S order envA -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Stream.closure_accepts

/-- info: 'Ix.Cert.Stream.readRecords_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Stream.readRecords_complete

/-- info: 'Ix.Cert.Stream.closure_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Stream.closure_prepares

/-- info: 'Ix.Cert.Stream.closure_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Stream.closure_accepts

/-! ## Route A, B4: the compiled closure has an order

`compileReport` checks that no stored record is on a reference cycle
(`Ix.Cert.referenceCycle`, Pass 1's proved condensation over the stored
records' reference graph). A successful check orders the stored records
(`Ix.Cert.Order.recordsOrdered_of_acyclic`: sorted by component, since an
edge never goes to a later component and every component is one record), and
ordered records give every seed set's compiled closure a `ClosureOrder`
(`closureOrder_of_ordered`), so one exists for every artifact `compile`
returns (`closureOrder_exists`). The check reads each record's `refs` table and
projection block without its expressions (`Ix.Cert.RecordRefs.getRefs`);
`Ix.Cert.RefsRead` proves that reader is `Ixon.getConstant` with the rest
forgotten, as an equation of reader programs, so the graph is the decoded
records' (`storedRefs_eq`). -/

/-- info: [cert-audit] refs read: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "refs read"
    (#[`skipExpr_eq, `skipUniv_eq, `skipInfo_eq, `getRefs_eq, `refsAt_eq, `lazyRefs_eq,
      `storedRefs_eq].map (`Ix.Cert.RefsRead ++ ·))

/-- info: Ix.Cert.RefsRead.getRefs_eq : Ix.Cert.RecordRefs.getRefs =
  (fun c => (c.refs, Ix.Cert.RefsRead.infoBlock c.info)) <$> Ixon.getConstant -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.RefsRead.getRefs_eq

/-- info: Ix.Cert.RefsRead.storedRefs_eq : ∀ (ixe : Ixon.Env) (a : Address),
  Ix.Cert.storedRefs ixe a = Option.map (fun c => (c.refs, Ix.Cert.refOwner a c)) (Ix.Cert.storedRecord ixe a) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.RefsRead.storedRefs_eq

/-- info: [cert-audit] order: 15 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] order: 3 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "order"
    (#[`refOwner_eq, `storedRecord_eq, `mem_keys_of_stored, `index_mem, `parMap_eq, `recordRefs_eq,
      `recordGraph_size, `recordGraph_edge, `singletons, `recordsOrdered_of_acyclic, `exists_nodup_filter,
      `closureOrder_of_ordered, `acyclic_of_compile, `recordsOrdered,
      `closureOrder_exists].map (`Ix.Cert.Order ++ ·))
  checkRuntime (tag := "cert-audit") "order"
    #[``Ix.Cert.recordGraph, ``Ix.Cert.referenceCycle, ``Ix.Compile.Canon.condensation]

/-- info: def Ix.Cert.Order.RecordsOrdered : Ixon.Env → Prop :=
fun ixe =>
  ∃ L,
    L.Nodup ∧
      (∀ (a : Address), a ∈ L ↔ ixe.consts.contains a = true) ∧ List.Pairwise (fun a b => ¬Ix.Cert.RecordRef ixe a b) L -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Order.RecordsOrdered

/-- info: @Ix.Cert.Order.recordsOrdered_of_acyclic : ∀ {ixe : Ixon.Env},
  Ix.Cert.referenceCycle ixe = none → Ix.Cert.Order.RecordsOrdered ixe -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Order.recordsOrdered_of_acyclic

/-- info: @Ix.Cert.Order.closureOrder_of_ordered : ∀ {ixe : Ixon.Env},
  Ix.Cert.Order.RecordsOrdered ixe → ∀ (S : Address → Prop), ∃ order, Ix.Cert.ClosureOrder ixe S order -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Order.closureOrder_of_ordered

/-- info: @Ix.Cert.Order.recordsOrdered : ∀ {env : Ix.Environment} {ixe : Ixon.Env},
  Ix.Cert.compile env = Except.ok ixe → Ix.Cert.Order.RecordsOrdered ixe -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Order.recordsOrdered

/-- info: @Ix.Cert.Order.closureOrder_exists : ∀ {env : Ix.Environment} {ixe : Ixon.Env},
  Ix.Cert.compile env = Except.ok ixe → ∀ (S : Address → Prop), ∃ order, Ix.Cert.ClosureOrder ixe S order -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Order.closureOrder_exists

/-- info: 'Ix.Cert.Order.recordsOrdered_of_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Order.recordsOrdered_of_acyclic

/-- info: 'Ix.Cert.Order.closureOrder_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Order.closureOrder_exists

/-! ## Route A, B5a and B6a: roles in the artifact, and evidence only gates

Source mode and Ixon mode check under different evidence (the certificate
theorems of the checked environment against the role table's synthesized
records). IxC's checker reads evidence only at `checkDecl`'s two gates, so an
acceptance moves to any evidence that passes every gate the first passes, with
the same environment (`Ix.Cert.Evidence.acceptsRef_covers`). The roles agree
on `sub` when every role whose Lean name `sub` declares is published at the
role table's address for it (`Ix.Cert.Roles.RolesBound`, decided by
`rolesBound`); `cert-statement`, `cert-compile-parity-init` and
`cert-roles-initstd` run it on the fixtures, `Init` and Init+Std. -/

/-- info: [cert-audit] evidence: 5 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] roles: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "evidence"
    (#[`natNames_disjoint, `checkDecl_covers, `foldlM_covers, `checkDeclsPure_covers,
      `acceptsRef_covers].map (`Ix.Cert.Evidence ++ ·))
  checkRoots (tag := "cert-audit") "roles"
    #[``Ix.Cert.Roles.rolesBound_iff, ``Ix.Cert.Roles.RolesBound.of_closure]

/-- info: structure Ix.Cert.Evidence.Covers {md : Ix.Kernel.Mode} (ops : Ix.Kernel.CheckerOps md (Ix.Kernel.CheckM md))
  (ev ev' : Ix.Kernel.Evidences md) : Prop
number of parameters: 4
fields:
  Ix.Cert.Evidence.Covers.defeq : ∀ (c : Ix.Kernel.Key md),
      Ix.Kernel.evidenceDefeqOk ev c = true → Ix.Kernel.evidenceDefeqOk ev' c = true
  Ix.Cert.Evidence.Covers.divMod : ∀ (env env2 : Ix.Kernel.Env md) (c : Ix.Kernel.Key md),
      Ix.Kernel.checkDivModEvidence ops ev env env2 c = Except.ok () →
        Ix.Kernel.checkDivModEvidence ops ev' env env2 c = Except.ok ()
constructor:
  Ix.Cert.Evidence.Covers.mk {md : Ix.Kernel.Mode} {ops : Ix.Kernel.CheckerOps md (Ix.Kernel.CheckM md)}
    {ev ev' : Ix.Kernel.Evidences md}
    (defeq : ∀ (c : Ix.Kernel.Key md), Ix.Kernel.evidenceDefeqOk ev c = true → Ix.Kernel.evidenceDefeqOk ev' c = true)
    (divMod :
      ∀ (env env2 : Ix.Kernel.Env md) (c : Ix.Kernel.Key md),
        Ix.Kernel.checkDivModEvidence ops ev env env2 c = Except.ok () →
          Ix.Kernel.checkDivModEvidence ops ev' env env2 c = Except.ok ()) :
    Ix.Cert.Evidence.Covers ops ev ev' -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Evidence.Covers

/-- info: @Ix.Cert.Evidence.acceptsRef_covers : ∀ {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode}
  {ev ev' : Ix.Kernel.Evidences md},
  (∀ (F : Nat), Ix.Cert.Evidence.Covers (Ix.Kernel.fueledOps μ F) ev ev') →
    ∀ {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md},
      Ix.Kernel.Cached.AcceptsRef μ ev ds env → Ix.Kernel.Cached.AcceptsRef μ ev' ds env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Evidence.acceptsRef_covers

/-- info: def Ix.Cert.Roles.RolesBound : Ix.Kernel.RoleTable → Ixon.Env → Ix.Environment → Prop :=
fun t ixe sub =>
  ∀ (r : Ix.Kernel.Role),
    r ∈ Ix.Kernel.Role.all →
      sub.consts.contains (Ix.Cert.Roles.roleName r) = true →
        Option.map (fun x => x.addr) (ixe.named.get? (Ix.Cert.Roles.roleName r)) = t.addressOf? r -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Roles.RolesBound

/-! ## N-READS, N1: Source acceptance admits every inductive block

R12 reads `inductive_reads`' Source premises and R9a's `ConstructorPositions`
off `Admits` (the block's group converts). An accepted Source check admits
every inductive block stored under its first member: the block's group is one
of the ingress's groups, and every one of those converts
(`Ix.LeanIngress.checkSource_converts`, `checkSourceBundled_converts`). -/

/-- info: [cert-audit] admits: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "admits"
    (#[`mem_forIn_of_mem, `mem_forIn_of_step, `mem_groupsOf, `admits_of_checkSource,
      `admits_of_checkSourceBundled, `admits_of_sourceAccepts, `source_premises_of_sourceAccepts,
      `mkIndc_positions_of_sourceAccepts].map (`Ix.Cert.Admits ++ ·))

/-- info: @Ix.Cert.Admits.admits_of_sourceAccepts : ∀ {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment}
  {roots : List Ix.Name} {sub : Ix.Environment} {envS : Ix.Kernel.Env Ix.Kernel.Mode.source},
  Ix.Cert.SourceAccepts condense env roots sub envS →
    ∀ {n : Ix.Name} {first : Ix.InductiveVal},
      (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList →
        first.all[0]? = some n → Ix.CompileCert.SourceConstructorPositions.Admits sub first -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Admits.admits_of_sourceAccepts

/-! ## N-READS, N2: levels read syntactically

The reader's level is the Source level in the compiler's canonical form
(`Ix.LeanIngress.canonLevelIn`, what IxC's U lowers Source levels to), when the
reader's parameter map is the constant's level parameters; roots in
`Ix.CompileCert.ReadingAudit` ("levels canonically"). -/

/-- info: @Ix.CompileCert.CanonLevelReading.related_ingress_canon : ∀ {md : Ix.Kernel.Mode}
  {names : Ix.Name → Ix.Kernel.Reader.CName md → Prop} {params : List Ix.Name} {σ : Ix.Name → Ix.Kernel.LevelParam}
  {param : Nat → Ix.Kernel.LevelParam},
  (∀ (a : Ix.Name), a ∈ params → ∀ (b : Ix.Name), b ∈ params → σ a = σ b → a = b) →
    (∀ (i : Nat) (h : i < params.length), param i = σ params[i]) →
      ∀ {source : Ix.Expr} {target : Ix.Kernel.Reader.CExpr md},
        Ix.CompileCert.ExpressionState.Related names (Ix.CompileCert.UniversePipeline.LevelMeaning params σ param)
            source target →
          ∃ converted,
            Ix.LeanIngress.ingressExpr σ source = Except.ok converted ∧
              Ix.CompileCert.ExpressionState.Matches
                (fun key key' => ∃ name, key = Ix.LeanIngress.ingressKey name ∧ names name key')
                (fun level level' => Ix.LeanIngress.canonLevelIn (List.map σ params) level = level') converted target -/
#guard_msgs (whitespace := lax) in
#check @Ix.CompileCert.CanonLevelReading.related_ingress_canon

/-! ## N-READS, N3 (a): the state every block starts from

The driver compiles every block from the empty `BlockState`; it is clean and
its wire tables are well formed. -/

/-- info: [cert-audit] block start: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "block start"
    (#[`clean_empty, `wire_empty].map (`Ix.Cert.BlockStart ++ ·))

/-! ## Route A, B6b: the role table's certificates on their pinned closure

`kernel-pin-gen` pins the well-founded `Nat` operations' dependency closure in
RoleData. On it, under the default table and its committed prelude, every
operation is defined and the pure fold accepts
(`Ix.Cert.RoleClosure.RoleEvidenceChecks`): a closed proposition about the
verifier's pinned configuration, not yet a premise of any statement.
`cert-statement` checks it after every regeneration through the executed fold
(`roleEvidenceCheck`, `roleEvidenceChecks_of_check`). -/

/-- info: def Ix.Cert.RoleClosure.RoleEvidenceChecks : Prop :=
∃ ev ds env,
  Ix.Cert.RoleClosure.preparedDefault = Except.ok (ev, ds) ∧
    Ix.Cert.RoleClosure.DefinesAll ds ∧ Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified ev ds env -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RoleClosure.RoleEvidenceChecks

/-- info: [cert-audit] role closure: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "role closure"
    (#[`definesAll_iff, `checks_of_closureCheck, `roleEvidenceChecks_of_check].map
      (`Ix.Cert.RoleClosure ++ ·))

/-! ## N-READS, N4 (b): no constructor of a Source-accepted family in its types

IxC checks every accepted `.indDecl`'s declared shape before its route
(`Ix.Kernel.Semantics.checkDecl_noCtor`). The ingress carries the sources'
constants to their keys, so no constructor of a Source-accepted family occurs
in the family's types (`Ix.Cert.NoCtor.noCtor_of_checkSourceWith`), and
`inductive_reads` holds of a Source-accepted closure with only the family's
name related to its key (R13's half) left of its self references
(`inductive_reads_sourceAccepts`). -/

/-- info: Ix.Cert.NoCtor.noCtor_of_checkSourceWith : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.source} {ev : Ix.Kernel.Evidences Ix.Kernel.Mode.source}
  {sub : Ix.Environment} {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env Ix.Kernel.Mode.source},
  Ix.LeanIngress.checkSourceWith pre ev sub blocks = Except.ok kenv →
    ∀ {n : Ix.Name} {first : Ix.InductiveVal},
      (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList →
        first.all[0]? = some n →
          ∀ {source : Ix.InductiveVal},
            source.cnst.name ∈ first.all.toList →
              sub.consts.get? source.cnst.name = some (Ix.ConstantInfo.inductInfo source) →
                ∀ (constructors : Array Ix.ConstructorVal),
                  List.Forall₂ (fun n c => sub.consts.get? n = some (Ix.ConstantInfo.ctorInfo c)) source.ctors.toList
                      constructors.toList →
                    Ix.CompileCert.InductiveReading.NoCtorIn constructors source.cnst.type ∧
                      ∀ (ctor : Ix.ConstructorVal),
                        ctor ∈ constructors.toList →
                          Ix.CompileCert.InductiveReading.NoCtorIn constructors ctor.cnst.type -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.NoCtor.noCtor_of_checkSourceWith

/-- info: [cert-audit] no constructor: 20 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "no constructor"
    (#[`converts_left, `drop_left_items, `items_facts, `convertInductive_entries, `foldlM_step_ok,
      `acceptsRef_decl, `mentionsConst_mapLevels, `canonExprM_run, `canonInfo_ind, `canonInfo_ctor,
      `withContract_mentions, `ingressMData_mentions, `noCtorIn_of_ingress, `mem_blockOf_type,
      `mem_blockOf_ctor, `lowerInductive_decl, `forIn_kept, `lowerAll_mem, `noCtor_of_checkSourceWith,
      `inductive_reads_sourceAccepts].map (`Ix.Cert.NoCtor ++ ·))

/-! ## Source mode at the pinned bundle evidence (owner, 2026-10-20)

`SourceAccepts` runs `Ix.LeanIngress.checkSourceBundled`: the committed prelude
and the committed bundle's evidence (`Ix.RoleEvidence.bundleEvidence`), whatever
the input carries, so a closure with a well-founded `Nat` operation is not
declined for want of the certificate theorems. Its readings are the
explicit-evidence entry's (`checkSourceWith_reading`). -/

/-- info: [cert-audit] source at the bundle: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source at the bundle"
    (#[`checkSourceBundledUsing_with, `checkSourceBundled_with, `checkSourceBundled_reading,
      `checkSourceBundled_refines_ref, `checkSourceBundled_no_proof_of_False,
      `checkSourceBundled_converts].map (`Ix.LeanIngress ++ ·) ++
      #[``Ix.Cert.Admits.admits_of_checkSourceBundled])

/-! ## Quotient Source and S4 (`ALPHA-COLLAPSE.md` §8; owner, 2026-10-20)

`SourceAcceptsQ` is Source acceptance on the artifact's alias fibers, every fiber
renamed onto one representative and its duplicates dropped, at the pinned bundle
evidence renamed onto the representatives; the executed check gives it. S4,
`NominalQuotientAgree`, is a named assumption, not an axiom: no theorem uses it,
and a corollary that does will take it as a hypothesis. -/

/-- info: def Ix.Cert.SourceAcceptsQ : (Ix.Environment → Ix.CondensedBlocks) →
  Ix.Environment → List Ix.Name → Ix.Environment → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.source → Prop :=
fun condense env roots sub ixe envS =>
  Ix.Cert.IsClosure env roots sub ∧
    ∃ pre ds,
      Ix.Kernel.Reader.builtinPrelude = Except.ok pre ∧
        Ix.LeanIngress.prepareSourceCollapsed (Ix.LeanIngress.fiberAlias ixe)
              (fun x => (Ix.LeanIngress.fiberHintsMap ixe)[x]?) pre sub (condense sub) =
            Except.ok ds ∧
          Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified
            (Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAlias ixe) (Ix.RoleEvidence.bundleEvidence ())) ds.toList
            envS -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceAcceptsQ

/-- info: def Ix.Cert.NominalQuotientAgree : Prop :=
∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
  (ixe : Ixon.Env),
  Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
    Ix.Cert.compile env = Except.ok ixe → ∃ envQ, Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe envQ -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.NominalQuotientAgree

/-- info: Ix.Cert.sourceAcceptsQ_of_check : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
  {ixe : Ixon.Env} {envS : Ix.Kernel.Env Ix.Kernel.Mode.source},
  Ix.Cert.IsClosure env roots sub →
    Ix.LeanIngress.checkSourceCollapsedBundled ixe sub (condense sub) = Except.ok envS →
      Ix.Cert.SourceAcceptsQ condense env roots sub ixe envS -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceAcceptsQ_of_check

/-- info: 'Ix.Cert.sourceAcceptsQ_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceAcceptsQ_of_check

/-! ## Quotient Source at the artifact's addresses (step 7.3 (iv), statements' side)

IxC renames a quotient accept from fiber representatives to their published
addresses (`Ix.LeanIngress.acceptsRef_addrOf`, and its table-rule form). The table
rule's premise `TableBound` follows from an admitted role table and an artifact-wide
check that every published role name sits at its role's address
(`Ix.Cert.tableBound_of`). The same check gives B5a's agreement by ingress name: the
statements' published address of a role's constant is the table's
(`Ix.Cert.publishedAddress_role`). B5a's `RolesBound` looks the declared roles' names up
by their stored hashes, so it gives neither on an artifact whose names' hashes are not
their own. The statements' published address of an input name is the renamed one when
every published name agrees with the address map (`Ix.Cert.publishedAddress_id`,
`Ix.Cert.reading_id`). Both checks are decided and run on the fixtures, `Init` and
Init+Std, with a planted failure of each. Value models pull back along the renaming's
relation (`Ix.Cert.ValueModel.pullback`). -/

/-- info: def Ix.Cert.PublishedRolesBound : Ix.Kernel.RoleTable → Ixon.Env → Prop :=
fun t ixe =>
  ∀ (m : Ix.Name) (d : Ixon.Named),
    (m, d) ∈ ixe.named.toList →
      ∀ (r : Ix.Kernel.Role), Ix.LeanIngress.ingressName m = r.leanName → t.addressOf? r = some d.addr -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.PublishedRolesBound

/-- info: def Ix.Cert.PublishedAgree : Ixon.Env → Prop :=
fun ixe =>
  ∀ (m : Ix.Name) (d : Ixon.Named),
    (m, d) ∈ ixe.named.toList → (Ix.LeanIngress.sourceAddrs ixe)[Ix.LeanIngress.ingressName m]? = some d.addr -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.PublishedAgree

/-- info: @Ix.Cert.tableBound_of : ∀ {t : Ix.Kernel.RoleTable} {ixe : Ixon.Env},
  t.check = Except.ok () →
    Ix.Cert.PublishedRolesBound t ixe → Ix.LeanIngress.TableBound ixe (Ix.LeanIngress.roleAtMap t) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.tableBound_of

/-- info: @Ix.Cert.publishedAddress_role : ∀ {t : Ix.Kernel.RoleTable} {ixe : Ixon.Env},
  Ix.Cert.PublishedRolesBound t ixe →
    ∀ {r : Ix.Kernel.Role} {a : Address},
      Ix.Cert.publishedAddress ixe (Ix.Kernel.Key.role r) = some a → t.addressOf? r = some a -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.publishedAddress_role

/-- info: @Ix.Cert.publishedAddress_id : ∀ {ixe : Ixon.Env},
  Ix.Cert.PublishedAgree ixe →
    ∀ {n : Ix.Kernel.Name},
      Ix.LeanIngress.roleOf n = none →
        ∀ {a : Address},
          (Ix.LeanIngress.sourceAddrs ixe)[n]? = some a → Ix.Cert.publishedAddress ixe (Ix.Kernel.Key.id n) = some a -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.publishedAddress_id

/-- info: [cert-audit] quotient addresses: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "quotient addresses"
    (#[`ValueModel.pullback, `publishedRolesBound_iff, `byLeanName_foldl, `roleOf_leanName,
      `tableBound_of, `publishedAgree_iff, `nameIsName_iff, `publishedAddress_role, `publishedAddress_id,
      `reading_id].map (`Ix.Cert ++ ·))
