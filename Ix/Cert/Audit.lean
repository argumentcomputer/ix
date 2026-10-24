import Ix.Compile.OriginalData
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
import Ix.Cert.Admits
import Ix.Cert.BlockStart
import Ix.Cert.RoleClosure
import Ix.Cert.NoCtor
import Ix.Cert.Quotient
import Ix.Cert.LiteralOrder
import Ix.Cert.Unchanged
import Ix.Cert.ReaderUnits
import Ix.Cert.PassHooks
import Ix.Cert.Resolution
import Ix.Cert.OriginalBytes
import Ix.Cert.HookFree
import Ix.Cert.CtxAgree
import Ix.Cert.CtxAgreeHints
import Ix.Cert.SourcePrelude
import Ix.Cert.ReaderKeys
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.ReaderFallback
import Ix.Cert.CtxAgreeProj
import Ix.Cert.CtxAgreeOwners
import Ix.Cert.CtxAgreeProjFields
import Ix.Cert.SourceNames
import Ix.Cert.SourceRetained
import Ix.Cert.SourceReplay
import Ix.Cert.SourceCommit
import Ix.Cert.SourceTrace
import Ix.Cert.SourceOrigin
import Ix.Cert.SourceOriginRead
import Ix.Cert.ValueRows
import Ix.Cert.ConversionValues
import Ix.CompileCert.ImageOrigin
import Ix.CompileCert.ImageShape
import Ix.CompileCert.CliqueRowShape
import Ix.CompileCert.CliqueRowsCoverage
import Ix.CompileCert.O6RecRead
import Ix.Cert.AnnotatedBeta
import Ix.CompileCert.O6Annotation
import Ix.Cert.CheckedBetaSpine
import Ix.CompileCert.O6Values
import Ix.CompileCert.O6Opened
import Ix.CompileCert.O6LambdaValues
import Ix.Cert.ContextValues
import Ix.Cert.ApplicationFronts
import Ix.CompileCert.O6ApplicationValues
import Ix.CompileCert.O6Telescope
import Ix.CompileCert.O6TelescopeOpened
import Ix.CompileCert.O6TelescopeValues
import Ix.Cert.ReferenceFronts
import Ix.Cert.PrefixReadings
import Ix.Cert.PrefixCore
import Ix.Cert.PrefixDefinitions
import Ix.Cert.PrefixConstType
import Ix.Cert.PrefixCapabilities
import Ix.Cert.PrefixRecRules
import Ix.Cert.PrefixTowers
import Ix.Cert.PrefixNatOps
import Ix.Cert.RuleInputValues
import Ix.CompileCert.O6PrefixValues
import Ix.CompileCert.OptDispatchOrigin
import Ix.CompileCert.OptShapeOrigin
import Ix.CompileCert.ViewPublicationOrigin

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
--
-- D14 (owner; after Q2): re-frozen. Reserved input is refused before the fold
-- (`Ix.Cert.reservedRefusal`): a grounded input constant with a reserved
-- metadata key, then a grounded input name with a reserved component, each by
-- its least message, as the IO pipeline (`compileDecoratedConsts`) and the Rust
-- compiler (`compile_env`) refuse it. The condensation is named once (`blocks`)
-- and passed to the refusal and to the driver; the driver's arguments are the
-- same. `compile-reserved-mdata` checks all three compilers name the same input.
--
-- Route A, B9b, check 3a (coordinator decision, 2026-10-20): re-frozen.
-- `compileUnchecked` also returns the driver's resolution map at the end of the
-- fold (`cenv.nameToAddr`, which it used to drop), for `checkReport`'s sixth
-- check (section "Resolved names are published where they resolve" below). The
-- environment and failures it returns are the same.
/-- info: def Ix.Cert.compileUnchecked : Ix.Environment → Except String (Ixon.Env × Ix.Cert.Failures × Ix.CompileM.CompileEnv) :=
fun env =>
  have env := { consts := env.consts };
  have split := Ix.Cert.groundSplit env;
  have blocks := Ix.CondenseM.run split.fst;
  do
  Ix.Cert.reservedRefusal env split.snd blocks
  let __x ← Ix.CompileM.compileEnvFold env blocks
  match __x with
    | (ixe, fst, cenv) =>
      have ungrounded :=
        Std.HashMap.fold (fun m n e => m.insert n (e.refusal (Std.HashMap.contains split.snd))) ∅ split.snd;
      pure (ixe, { ungrounded := ungrounded, blocks := cenv.ungrounded }, cenv) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.compileUnchecked

/-- info: def Ix.Cert.reservedRefusal : Ix.Environment →
  Ix.Map Ix.Name Ix.GroundError → Ix.CondensedBlocks → Except String Unit :=
fun env ungrounded blocks =>
  have reservedMetadata :=
    Std.HashMap.fold
      (fun acc n ci =>
        if (!Std.HashMap.contains ungrounded n && Ix.Cert.constHasReservedMetadata ci) = true then acc.push n else acc)
      #[] env.consts;
  have __do_jp := fun __r =>
    match Ix.CompileM.reservedInputRefusal? blocks with
    | some msg => throw msg
    | x => pure ();
  match Ix.CompileM.reservedMetadataRefusal? reservedMetadata with
  | some msg => do
    let __r ← throw msg
    __do_jp __r
  | x => __do_jp () -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.reservedRefusal

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

/-- info: def Ix.Cert.checkReport : Ix.Environment → Ix.CompileM.CompileEnv → Ixon.Env × Ix.Cert.Failures → Except String Unit :=
fun env cenv out =>
  match Ix.Cert.uncovered env out.fst out.snd, Ix.Cert.unauthentic out.fst with
  | [], [] =>
    match Ix.Cert.referenceCycle out.fst with
    | none =>
      match Ix.Cert.nameHashCollision env out.fst with
      | none =>
        match Ix.Cert.mutsMismatch out.fst with
        | none =>
          match Ix.Cert.resolutionMismatch cenv.nameToAddr out.fst with
          | none =>
            match Ix.Cert.unseenInductive env out.fst with
            | none =>
              match Ix.Cert.unoriginalAux env cenv.auxNameToAddr out.fst with
              | none =>
                match Ix.Cert.unresolvedPublished env cenv.nameToAddr cenv.auxNameToAddr out.fst with
                | none =>
                  match Ix.Cert.crossClaimed env cenv.nameToAddr cenv.auxNameToAddr cenv.auxGenExtraNames with
                  | none =>
                    match Ix.Cert.foreignHead env cenv.auxReport.table cenv.p3Heads out.fst with
                    | none =>
                      match Ix.Cert.misnamedInput env with
                      | none =>
                        match Ix.Cert.strayConstructor env with
                        | none =>
                          match Ix.Cert.strayFailure env cenv.ungrounded with
                          | none =>
                            match Ix.Cert.identityMismatch cenv.auxReport.identity out.fst with
                            | none =>
                              match Ix.Cert.projectionCollision out.fst with
                              | none => Except.ok ()
                              | some (b, i) =>
                                Except.error
                                  (toString "compileReport: projection check failed: member " ++ toString i ++
                                        toString " of the block at " ++
                                      toString b ++
                                    toString " has more than one stored definition projection record")
                            | some (n, same, a) =>
                              Except.error
                                (toString "compileReport: identity check failed: the identity row of " ++
                                            toString n.pretty ++
                                          toString " (" ++
                                        toString (if same = true then "identical" else "not identical") ++
                                      toString " at " ++
                                    toString a ++
                                  toString
                                    ") disagrees with another row of that name, or the name is not published at that address")
                          | some f =>
                            Except.error
                              (toString "compileReport: failure check failed: the driver records the name " ++
                                  toString f.pretty ++
                                toString " as a failure, but no input constant is stored under it")
                        | some c =>
                          Except.error
                            (toString "compileReport: constructor check failed: the name " ++ toString c.pretty ++
                              toString ", a constructor of an input inductive, is not stored as a constructor of it")
                      | some n =>
                        Except.error
                          (toString "compileReport: name invariant failed: the input constant stored under " ++
                              toString n.pretty ++
                            toString " carries another name")
                    | some h =>
                      Except.error
                        (toString "compileReport: heads check failed: the Pass 3 head " ++ toString h.pretty ++
                          toString " is not a regenerated published input name, so not known to be in the changed set")
                  | some n =>
                    Except.error
                      (toString "compileReport: cross-SCC check failed: the name " ++ toString n.pretty ++
                        toString
                          " resolves outside the aux map and is among the extra names or is a constructor of an inductive among them, so a cross-SCC subset may have claimed it")
                | some n =>
                  Except.error
                    (toString "compileReport: publication check failed: the input name " ++ toString n.pretty ++
                      toString " is published but neither resolved nor in the aux map")
              | some n =>
                Except.error
                  (toString "compileReport: original-form check failed: the input name " ++ toString n.pretty ++
                    toString " resolves through the aux map but is not published with an original-form record")
            | some n =>
              Except.error
                (toString "compileReport: component check failed: the input inductive " ++ toString n.pretty ++
                  toString " is not published at an inductive projection of a block with a Muts entry")
          | some (n, a, published) =>
            have found :=
              match published with
              | some b => toString "published at " ++ toString b
              | none => "not published";
            Except.error
              (toString "compileReport: resolution check failed: " ++ toString n.pretty ++ toString " resolves to " ++
                    toString a ++
                  toString " but is " ++
                toString found)
        | some (entry, i, h) =>
          Except.error
            (toString "compileReport: Muts check failed: the entry " ++ toString entry.pretty ++
                      toString " lists the name hash " ++
                    toString h ++
                  toString " in class " ++
                toString i ++
              toString ", which is not published at that member's projection of its block")
      | some (a, b) =>
        Except.error
          (toString "compileReport: name check failed: " ++ toString a.pretty ++ toString " and " ++
              toString b.pretty ++
            toString " are different names with one name hash")
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
  let __x ← Ix.Cert.compileUnchecked env
  match __x with
    | (ixe, failures, cenv) => do
      Ix.Cert.checkReport env cenv (ixe, failures)
      pure (ixe, failures) -/
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
    ∃ cenv,
      Ix.Cert.compileUnchecked env = Except.ok (out.fst, out.snd, cenv) ∧
        Ix.Cert.checkReport env cenv out = Except.ok () -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.compileReport_ok

/-- info: @Ix.Cert.checkReport_ok : ∀ {env : Ix.Environment} {cenv : Ix.CompileM.CompileEnv} {out : Ixon.Env × Ix.Cert.Failures},
  Ix.Cert.checkReport env cenv out = Except.ok () →
    Ix.Cert.uncovered env out.fst out.snd = [] ∧
      Ix.Cert.unauthentic out.fst = [] ∧
        Ix.Cert.referenceCycle out.fst = none ∧
          Ix.Cert.nameHashCollision env out.fst = none ∧
            Ix.Cert.mutsMismatch out.fst = none ∧
              Ix.Cert.resolutionMismatch cenv.nameToAddr out.fst = none ∧
                Ix.Cert.unseenInductive env out.fst = none ∧
                  Ix.Cert.unoriginalAux env cenv.auxNameToAddr out.fst = none ∧
                    Ix.Cert.unresolvedPublished env cenv.nameToAddr cenv.auxNameToAddr out.fst = none ∧
                      Ix.Cert.crossClaimed env cenv.nameToAddr cenv.auxNameToAddr cenv.auxGenExtraNames = none ∧
                        Ix.Cert.foreignHead env cenv.auxReport.table cenv.p3Heads out.fst = none ∧
                          Ix.Cert.misnamedInput env = none ∧
                            Ix.Cert.strayConstructor env = none ∧
                              Ix.Cert.strayFailure env cenv.ungrounded = none ∧
                                Ix.Cert.identityMismatch cenv.auxReport.identity out.fst = none ∧
                                  Ix.Cert.projectionCollision out.fst = none -/
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
the certified reader, as a term `Related` to the source. Without Pass 3
records the production entry `compileExpr` is that compiler
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
environment without Pass 3 records, or of any payload emitter (definition,
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
under an environment without Pass 3 records, returns on success the
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
environment without Pass 3 records, return on success a block whose
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

Since the call-site surgery was deleted (CQ3.5), public dispatch
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
an environment without Pass 3 records, from a clean state whose tables
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
(`MutualArtifact.build_cases`). Under an environment without Pass 3
records, a successful mutual block from a state whose tables are on the wire
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

Public dispatch of an inductive, under an environment without Pass 3
records, from a clean state whose tables are on the wire, returns a block
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
the converse of IxC's `readRecords_spec`) whose final state keeps the
prelude's entries (`State.keepsPrelude`, required by `readStream_complete`).
With the fold's acceptance under
the committed prelude that is `IxonAccepts` (`closure_accepts`).
`StoredCanonical` (R13, from R7e's per-block codec), the stream reading
(N-READS), and final-state preservation (`keeps`) stay obligations. Preservation
at every earlier reader state needs its own compiled-output proof. -/

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
                  pre.state.keepsPrelude st' = true →
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
                      pre.state.keepsPrelude st' = true →
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
when every published name whose ingress name is a role's Lean name sits at the
role table's address for that role (`Ix.Cert.PublishedRolesBound`, decided by
`publishedRolesBound`; the reading of a role's constant is then at the table's
address, `Ix.Cert.publishedAddress_role`); `cert-statement`,
`cert-compile-parity-init` and `cert-roles-initstd` run it on the fixtures, `Init`
and Init+Std. Re-frozen (push 77's follow-up): B5a's `RolesBound` and
`RolesBound.of_closure` are removed; `RolesBound` trusts stored name hashes and is
superseded by `PublishedRolesBound` (push 77). -/

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
    #[``Ix.Cert.publishedRolesBound_iff, ``Ix.Cert.publishedAddress_role]

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

/-- info: def Ix.Cert.PublishedRolesBound : Ix.Kernel.RoleTable → Ixon.Env → Prop :=
fun t ixe =>
  ∀ (m : Ix.Name) (d : Ixon.Named),
    (m, d) ∈ ixe.named.toList →
      ∀ (r : Ix.Kernel.Role), Ix.LeanIngress.ingressName m = r.leanName → t.addressOf? r = some d.addr -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.PublishedRolesBound

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

/-! ## N-READS, N5 b (stage A): one inductive through the driver's mutual path

The driver compiles a block of one inductive as `compileMutualBlock [[m]]`
over the member `MutConst.mkIndc` builds, after its class sort and
recursor-family order (which keep the one class), not through
`compileConstantInfo`. Over that path the block reads back as its source, its
projections are the class's (`MutualArtifact.mutual_correct`), and its Source
premises come from Source acceptance as in N4 (b)
(`Ix.Cert.NoCtor.inductive_reads_driver_sourceAccepts`; the reading-chain half
is `Ix.CompileCert.MutualInductiveReading`, audited by the reading audit). -/

/-- info: [cert-audit] driver inductive: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "driver inductive" #[`Ix.Cert.NoCtor.inductive_reads_driver_sourceAccepts]

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
renamed onto one representative and its duplicates dropped, the role read off the
role table (the table rule), the prepared stream checked to be a renaming onto the
artifact's keys, at the pinned bundle evidence renamed onto the representatives; the
executed check gives it. S4, `NominalQuotientAgree`, is a named assumption, not an
axiom: no theorem uses it, and a corollary that does will take it as a hypothesis.
Re-frozen (the …At restatement): one restatement, the table rule, the QRep check and
the evidence checks (`Ix.LeanIngress.prepareSourceCollapsedAt`,
`checkSourceCollapsedBundledAt`); S4 strengthened, measured gap 0. -/

/-- info: def Ix.Cert.SourceAcceptsQ : (Ix.Environment → Ix.CondensedBlocks) →
  Ix.Environment →
    List Ix.Name → Ix.Environment → Ixon.Env → Ix.Kernel.RoleTable → Ix.Kernel.Env Ix.Kernel.Mode.source → Prop :=
fun condense env roots sub ixe t envS =>
  Ix.Cert.IsClosure env roots sub ∧
    ∃ pre ds,
      Ix.Kernel.Reader.builtinPrelude = Except.ok pre ∧
        Ix.LeanIngress.prepareSourceCollapsedAt ixe t (fun x => (Ix.LeanIngress.fiberHintsMap ixe)[x]?) pre sub
              (condense sub) =
            Except.ok ds ∧
          Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified
            (Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
              (Ix.RoleEvidence.bundleEvidence ()))
            ds.toList envS -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceAcceptsQ

/-- info: def Ix.Cert.NominalQuotientAgree : Prop :=
∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env Ix.Kernel.Mode.source)
  (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable),
  Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
    Ix.Cert.compile env = Except.ok ixe →
      Ix.Kernel.Reader.defaultTable = Except.ok t →
        ∃ envQ, Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.NominalQuotientAgree

/-- info: Ix.Cert.sourceAcceptsQ_of_check : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
  {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} {envS : Ix.Kernel.Env Ix.Kernel.Mode.source},
  Ix.Cert.IsClosure env roots sub →
    Ix.LeanIngress.checkSourceCollapsedBundledAt ixe t sub (condense sub) = Except.ok envS →
      Ix.Cert.SourceAcceptsQ condense env roots sub ixe t envS -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceAcceptsQ_of_check

/-- info: 'Ix.Cert.sourceAcceptsQ_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.sourceAcceptsQ_of_check

/-! ## Quotient Source at the artifact's addresses (step 7.3 (iv), statements' side)

IxC renames a checked quotient accept to the artifact's addresses by the joined map
(`Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt`, `evAddr`). The table rule's
premise `TableBound` follows from an admitted role table and an artifact-wide check
that every published role name sits at its role's address (`Ix.Cert.tableBound_of`),
so a quotient accept at such a table is a reference accept at the artifact's
addresses (`Ix.Cert.sourceAcceptsQ_addrAt`, without unfolding the committed bundle).
The statements' published address of an input name is the renamed one when every
published name agrees with the address map (`Ix.Cert.publishedAddress_id`,
`Ix.Cert.reading_id`). Both checks are decided and run on the fixtures, `Init` and
Init+Std, with a planted failure of each. Value models pull back along the renaming's
relation (`Ix.Cert.ValueModel.pullback`). Re-frozen (the …At restatement):
`sourceAcceptsQ_addrAt` added; `PublishedRolesBound`'s print moved to the roles
section. -/

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

/-- info: @Ix.Cert.sourceAcceptsQ_addrAt : ∀ {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment}
  {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
  {envS : Ix.Kernel.Env Ix.Kernel.Mode.source},
  Ix.Cert.SourceAcceptsQ condense env roots sub ixe t envS →
    t.check = Except.ok () →
      Ix.Cert.PublishedRolesBound t ixe →
        ∃ b,
          Ix.RoleEvidence.committedBundle () = Except.ok b ∧
            ∃ ds envA,
              Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified
                  (Ix.Kernel.Evidences.mapKeys (Ix.LeanIngress.evAddr ixe b)
                    (Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
                      (Ix.RoleEvidence.bundleEvidence ())))
                  (List.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b)) ds.toList) envA ∧
                Ix.Kernel.EnvRel
                  (fun n =>
                    Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap t) n ∨ Ix.LeanIngress.BundleOnly ixe b n)
                  (Ix.LeanIngress.evAddr ixe b) envS envA -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.sourceAcceptsQ_addrAt

/-- info: [cert-audit] quotient addresses: 11 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "quotient addresses"
    (#[`ValueModel.pullback, `publishedRolesBound_iff, `byLeanName_foldl, `roleOf_leanName,
      `tableBound_of, `publishedAgree_iff, `nameIsName_iff, `publishedAddress_role, `publishedAddress_id,
      `reading_id, `sourceAcceptsQ_addrAt].map (`Ix.Cert ++ ·))

/-! ## S1's certificate-side `Closed`: string literals after their support

S1's `Closed` (IxC, 2026-10-20) counts a literal's support roles as mentions. A
record's reference table does not show them, so B4's `ClosureOrder` does not order
them; the decided `Ix.Cert.LiteralOrder.stringSupportOrdered` does: every record of
the order with a string literal (in itself or its owner block) comes after the stream
records of the string roles (`stringRoles`, `Ix.Kernel.strLitSupported`'s). A `Nat`
literal's support is the prelude's, at the front. `cert-statement`,
`cert-compile-parity-init` and `cert-roles-initstd` decide it on the closure orders of
the fixtures, `Init` and Init+Std, with a planted failure each. -/

/-- info: def Ix.Cert.LiteralOrder.StringSupportOrdered : Ixon.Env → Ix.Kernel.RoleTable → List Address → Prop :=
fun ixe t order =>
  ∀ (pre : List Address) (a : Address) (post : List Address),
    order = pre ++ a :: post →
      Ix.Cert.LiteralOrder.strAt ixe a = true →
        ∀ (r : Ix.Kernel.Role),
          r ∈ Ix.Cert.LiteralOrder.stringRoles →
            ∃ b, Ix.Cert.LiteralOrder.supportOwner ixe t r = some b ∧ (b = a ∨ b ∈ pre) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.LiteralOrder.StringSupportOrdered

/-- info: def Ix.Cert.LiteralOrder.stringRoles : List Ix.Kernel.Role :=
[Ix.Kernel.Role.string, Ix.Kernel.Role.stringOfList, Ix.Kernel.Role.list, Ix.Kernel.Role.listNil,
  Ix.Kernel.Role.listCons, Ix.Kernel.Role.char, Ix.Kernel.Role.charOfNat] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.LiteralOrder.stringRoles

/-- info: Ix.Cert.LiteralOrder.stringSupportOrdered_iff : ∀ (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (order : List Address),
  Ix.Cert.LiteralOrder.stringSupportOrdered ixe t order = true ↔ Ix.Cert.LiteralOrder.StringSupportOrdered ixe t order -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.LiteralOrder.stringSupportOrdered_iff

/-- info: [cert-audit] string literal order: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "string literal order"
    (#[`recordOk_iff, `orderedFrom_iff, `stringSupportOrdered_iff].map (`Ix.Cert.LiteralOrder ++ ·))

/-! ## Route A, B9a: a constant outside the changed set

`Ix.Cert.Unchanged.avoids_unchanged`: a constant of a closure that avoids the
compile's changed set (`ChangedSet.Avoids`, H1's hypothesis) is in no class
of a changed component and no constructor of a member of a changed inductive
one, is no image head of a changed inductive component's Lean block, is in no
condensation block whose references hold one, is in no clique of the input's
clique table and in no condensation block whose references hold one of Lean's
encoding constants of a clique, and, published with an original-form compile,
is found identical by the compile's aux table. The proofs read `ofCompile`
through its stages, identified with it by `rfl` (`ofCompile_eq`).
`cert-unchanged` checks on the changed-set corpus, and
`cert-statement`/`cert-compile-parity-init` on the fixtures and `Init`, that
these facts single the set out.

Re-frozen (2026-10-20, after push 91): `ofCompile` takes each changed
inductive component's image heads from the component itself and counts every
component, not through a map keyed by first name (a flagged, report-only edit;
the set is identical on the corpus, the fixtures and Init+Std). The head and
caller facts hold without `FirstsAgree`, which is gone with its decider and the
first-loop map lemmas: 49 roots → 41.

**Re-frozen (2026-10-21, CQ5.2 (b), flagged statement change): the changed set
over the compile's condensation and aux table.** `ofCompile env condensed table
ixe` (the compiler lane's commit 4) adds the clique stage (`cliqueStage`:
`clique` entries for the clique table, `caller` entries for the members of a
condensation block that references a clique's encoding), enters the callers
of the heads by condensation block (`callerStage`, over `condensed.blockRefs`),
and reads `regenerated` off the aux table (`AuxTable.identical`). So
`Unchanged` takes `condensed` and `table`; `caller` is restated at block level;
`clique` and `cliqueCaller` are new; `original` now says the table finds the
record identical (a verdict on bytes; B9d reads it as bytes, with the 15th
check). The stages are restated (`cliqueStage_eq`, `callerStage_eq`,
`regenStage_eq`; the third loop's lemmas are replaced): 41 roots → 57, and
the runtime list gains the two stages, the clique tables and
`AuxTable.identical`. The statements read the set as
`ofCompile { consts := env.consts } (compileBlocks env) (compileTable env) ixe`. -/

/-- info: [cert-audit] unchanged: 57 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] unchanged: 9 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "unchanged"
    (#[`forIn_grow, `forIn_hit, `ofCompile_eq, `forIn_grow_array, `forIn_hit_array, `Grows.refl,
      `Grows.trans, `Grows.push, `memberStage_eq, `headStage_eq, `cliqueStage_eq, `callerStage_eq,
      `regenStage_eq, `kind_beq, `ctorLoop_grows, `ctorLoop_hit, `memberBody_step, `memberBody_lands,
      `classBody_step, `blockBody_step, `member_entry, `Grows₂.refl, `Grows₂.trans, `headStep_step,
      `headBody_step, `headStage_grows, `heads_inv, `head_entry, `cliqueNameBody_step, `encMembers_grows,
      `encRefBody_step, `encRefs_grows, `encBlockBody_step, `cliqueNames_grows, `encBlocks_grows,
      `cliqueStage_grows, `clique_entry, `encCaller_entry, `callerMemberBody_step, `callerBlockBody_step,
      `callerStage_grows, `headCaller_entry, `regenBody_step, `regenStage_grows, `regenerated_entry,
      `sortEntries_eq, `dedupStep_spec, `dedup_keeps, `sortEntries_keeps, `names_contains,
      `contains_of_entry, `leastName_none, `blocks_toList, `refs_getD, `toList_of_contains,
      `unchanged_of_not_contains, `avoids_unchanged].map (`Ix.Cert.Unchanged ++ ·))
  checkRuntime (tag := "cert-audit") "unchanged"
    #[``Ix.Compile.ChangedSet.ofCompile, ``Ix.Compile.ChangedSet.sortEntries, ``Ix.Compile.ChangedSet.leastName,
      ``Ix.Compile.ChangedSet.ChangedSet.contains, ``Ix.Compile.ChangedSet.Entry.beq,
      ``Ix.Compile.ChangedSet.cliqueStage, ``Ix.Compile.ChangedSet.callerStage,
      ``Ix.Compile.ChangedSet.cliqueTables, ``Ix.AuxGen.AuxTable.identical]

/-! ## Distinct name hashes (B9's name keys; owner-approved check, 2026-10-20)

`Ix.Name`'s `==` compares stored name hashes, and every map keyed by name (the
input's constants, the artifact's published names, the changed set's tables)
identifies two names with one hash. `compileReport` now refuses a result in
which two different names among the input's constants and the published names
share a hash (`checkReport`'s fourth check, `nameHashCollision`), so on its
result names may be read structurally (`nameHashes_distinct`). Re-frozen with
it: `checkReport`'s print (the fourth check) and `checkReport_ok` (a fourth
conjunct). On a consistent run the result is unchanged. -/

/-- info: [cert-audit] name hashes: 3 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] name hashes: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "name hashes"
    (#[`nameHash_fold, `nameHashCollision_none, `nameHashes_distinct].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "name hashes" #[``Ix.Cert.nameHashCollision]

/-- info: def Ix.Cert.nameHashCollision : Ix.Environment → Ixon.Env → Option (Ix.Name × Ix.Name) :=
fun env ixe =>
  (List.foldl
      (fun acc n =>
        match acc.snd with
        | some val => acc
        | none =>
          match acc.fst.get? n.getHash with
          | some m => if (Ix.nameCompareExact m n == Ordering.eq) = true then acc else (acc.fst, some (m, n))
          | none => (acc.fst.insert n.getHash n, none))
      (∅, none) (env.consts.keys ++ ixe.named.keys)).snd -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.nameHashCollision

/-! ## `Muts` entries agree with their blocks (B9c (c2); coordinator decision, 2026-10-20)

The changed set reads a compiled component's classes off its `Muts` entry,
which the aux tail registers before AuxGen's pipeline runs (`partial` code no
proof can follow). `compileReport` now refuses a result in which a `Muts` entry
lists, in class `i`, a name not published at member `i`'s projection of its
block (`checkReport`'s fifth check, `mutsMismatch`); the projections are
`buildMutualProjections`', proved code. So on its result the classes the
changed set reads are the block's own (`mutsAgree`). Re-frozen with it:
`checkReport`'s print (the fifth check) and `checkReport_ok` (a fifth
conjunct). On a consistent run the result is unchanged. -/

/-- info: [cert-audit] Muts entries: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] Muts entries: 3 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "Muts entries"
    (#[`mutsMismatch_none, `mutsAgree].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "Muts entries"
    #[``Ix.Cert.memberProjection, ``Ix.Cert.publishedAtMember, ``Ix.Cert.mutsMismatch]

/-- info: def Ix.Cert.mutsMismatch : Ixon.Env → Option (Ix.Name × Nat × Address) :=
fun ixe =>
  have byHash := Std.HashMap.fold (fun m n x => m.insert n.getHash n) ∅ ixe.named;
  List.findSome?
    (fun x =>
      match x with
      | (entry, named) =>
        match named.constMeta.info with
        | Ixon.ConstantMetaInfo.muts all auxLayout =>
          List.findSome?
            (fun x =>
              match x with
              | (cls, i) =>
                Option.map (fun h => (entry, i, h))
                  (List.find? (fun h => !Ix.Cert.publishedAtMember ixe byHash named.addr i h) cls.toList))
            all.toList.zipIdx
        | x => none)
    ixe.named.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.mutsMismatch

/-! ## Resolved names are published where they resolve (B9b, check 3a; coordinator decision, 2026-10-20)

A block's merge registers each of its names in the driver's resolution map
(`CompileEnv.nameToAddr`) and its `Named` table at one address, but the aux
tail's `Named` entries, registered after AuxGen's `partial` code, are merged
after them and override a name's entry, so no proof bounds which names a later
block's entries overwrite. `compileReport` now refuses a result in which a name
of the resolution map at the end of the fold is not published at the address it
resolves to (`checkReport`'s sixth check, `resolutionMismatch`); B9b's merge
invariant is about the resolution map, and with this check it speaks of the
published names (`resolvedPublished`). Re-frozen with it: `compileUnchecked`'s
print (it returns the resolution map), `checkReport`'s print (its `resolved`
argument and the sixth check), `compileReport`'s print (it passes the map),
`compileReport_ok` (the map it was checked against) and `checkReport_ok` (a
sixth conjunct). `compileReport_checks` gives the first five conjuncts for the
proofs that read only the result. On a consistent run the result is unchanged. -/

/-- info: [cert-audit] resolved names: 3 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] resolved names: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "resolved names"
    (#[`resolutionMismatch_none, `resolvedPublished, `compileReport_checks].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "resolved names" #[``Ix.Cert.resolutionMismatch]

/-- info: def Ix.Cert.resolutionMismatch : Std.HashMap Ix.Compile.ExactKey.ExactName Address →
  Ixon.Env → Option (Ix.Name × Address × Option Address) :=
fun resolved ixe =>
  List.findSome?
    (fun x =>
      match x with
      | (n, a) =>
        have published := Option.map (fun x => x.addr) (ixe.named.get? n);
        if published = some a then none else some (n, a, published))
    resolved.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.resolutionMismatch

/-! ## Every inductive component is seen (B9b's (c3); coordinator decision, 2026-10-20)

The changed set reads an inductive component only through its block's `Muts`
entry (`Ix.Compile.ChangedSet.mutsRecords`), which the aux tail registers
before AuxGen's `partial` code, and a later `Named` entry may override, so a
component could escape the classifier. `compileReport` now refuses a result in
which a published input inductive is not published at an inductive projection
of a block with a `Muts` entry at its address (`checkReport`'s seventh check,
`unseenInductive`). It reads the published input inductives' records, not every
stored record: finding the stored inductive blocks among the records would mean
decoding every mutual block record, and the changed set is about the input's
names. Re-frozen with it: `checkReport`'s print (the seventh check) and
`checkReport_ok` (a seventh conjunct). On a consistent run the result is
unchanged. -/

/-- info: [cert-audit] inductive components: 3 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] inductive components: 2 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "inductive components"
    (#[`mutsAddrs_contains, `unseenInductive_none, `inductivesSeen].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "inductive components"
    #[``Ix.Cert.mutsAddrs, ``Ix.Cert.unseenInductive]

/-- info: def Ix.Cert.mutsAddrs : Ixon.Env → Std.HashSet Address :=
fun ixe =>
  Std.HashMap.fold
    (fun s x named =>
      match named.constMeta.info with
      | Ixon.ConstantMetaInfo.muts all auxLayout => s.insert named.addr
      | x => s)
    ∅ ixe.named -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.mutsAddrs

/-- info: def Ix.Cert.unseenInductive : Ix.Environment → Ixon.Env → Option Ix.Name :=
fun env ixe =>
  have muts := Ix.Cert.mutsAddrs ixe;
  List.findSome?
    (fun x =>
      match x with
      | (n, ci) =>
        match ci with
        | Ix.ConstantInfo.inductInfo v =>
          match ixe.named.get? n with
          | none => none
          | some named =>
            match Option.map (fun x => x.info) (Ix.Cert.storedRecord ixe named.addr) with
            | some (Ixon.ConstantInfo.iPrj p) => if muts.contains p.block = true then none else some n
            | x => some n
        | x => none)
    env.consts.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.unseenInductive

/-! ## Aux-resolved input names have original-form records (B9b's gap 2; coordinator decision, 2026-10-21)

The driver resolves a name through its aux map (`CompileEnv.auxNameToAddr`)
when another block's aux tail compiled it, AuxGen's `partial` code, which no
proof follows. Its promotion grafts the original-form compile's record onto
the name's entry (`promoteAuxWrites`), but the remaining members of a promoted
block (`promoteRemainingWrites`) get none, so such an input name would be
neither a primary claim of its own block's compile (B9b) nor a name the
classifier's regenerated rule reads (B9d). `compileReport` now refuses a result
in which an input name of the driver's final aux map is not published with
`Named.original` (`checkReport`'s eighth check, `unoriginalAux`; on Init+Std,
3,428 aux names, all input, all with one; on Mathlib, 22,842 aux names, 22,513
input, all with one). `compileUnchecked` also returns the final aux map.
Re-frozen with it: `compileUnchecked`'s, `checkReport`'s and `compileReport`'s
prints, `compileReport_ok` (the aux map beside the resolution map) and
`checkReport_ok` (an eighth conjunct). On a consistent run the result is
unchanged. -/

/-- info: [cert-audit] original-form records: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] original-form records: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "original-form records"
    (#[`unoriginalAux_none, `auxOriginal].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "original-form records" #[``Ix.Cert.unoriginalAux]

/-- info: def Ix.Cert.unoriginalAux : Ix.Environment →
  Std.HashMap Ix.Compile.ExactKey.ExactName Address → Ixon.Env → Option Ix.Name :=
fun env aux ixe =>
  List.findSome?
    (fun x =>
      match x with
      | (n, snd) =>
        if (env.consts.contains n && !Option.any (fun x => x.original.isSome) (ixe.named.get? n)) = true then some n
        else none)
    aux.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.unoriginalAux

/-! ## Published input names are resolved (B9b, `HookFree`'s discharge, (v); coordinator decision, 2026-10-21)

A `Named` entry can come from a block's aux tail (`BlockState.auxNamed`,
written after AuxGen's `partial` code, which no proof follows), so a published
input name need not be one the driver resolved. `compileReport` now refuses a
result in which a published input name is neither in the driver's final
resolution map nor in its final aux map (`checkReport`'s ninth check,
`unresolvedPublished`; probe `ports/20261021T034341Z-hookprobe`: on Init+Std,
117,694 published input names, on Mathlib 783,115, all resolved or in the aux
map). So every published input name is a
primary claim of a block compiled during the fold
(`Ix.Cert.Resolution.compileReport_claim`) or resolves through the aux map
with an original-form record (`auxOriginal`). Re-frozen with it:
`checkReport`'s print and `checkReport_ok` (a ninth
conjunct). On a consistent run the result is unchanged. -/

/-- info: [cert-audit] publication: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] publication: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "publication"
    (#[`unresolvedPublished_none, `publishedResolved].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "publication" #[``Ix.Cert.unresolvedPublished]

/-- info: def Ix.Cert.unresolvedPublished : Ix.Environment →
  Std.HashMap Ix.Compile.ExactKey.ExactName Address →
    Std.HashMap Ix.Compile.ExactKey.ExactName Address → Ixon.Env → Option Ix.Name :=
fun env resolved aux ixe =>
  List.findSome?
    (fun x =>
      match x with
      | (n, snd) => if (env.consts.contains n && !resolved.contains n && !aux.contains n) = true then some n else none)
    ixe.named.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.unresolvedPublished

/-! ## No cross-SCC claims; `compileUnchecked` returns the driver's final environment (B9b, `HookFree`'s discharge, (iv); coordinator decision, 2026-10-21)

A promoted block's cross-SCC subset is compiled under its own key, which is
not one of the condensation's block keys, so Pass 3's hook 2 (`prepareBlock`)
does not find the block's references and walks its members' terms, a loop no
proof unfolds: hook 2 cannot be shown the identity there. The subset's merge
puts each of its names among the extra names (`CompileEnv.auxGenExtraNames`),
and only a withdrawal, which also erases the name's resolution, removes one.
`compileReport` now refuses a result in which a resolved name outside the aux
map is among the extra names (`checkReport`'s tenth check, `crossClaimed`;
probe `ports/20261021T034341Z-hookprobe`: 0 on Init+Std, 117,694 resolved
names, and on Mathlib, 783,082). With it, `compileUnchecked` returns the
driver's final environment instead of its resolution and aux maps, and
`checkReport` reads the maps it needs from it (`nameToAddr`, `auxNameToAddr`,
`auxGenExtraNames`; each check takes only its maps). Re-frozen with it:
`compileUnchecked`'s, `checkReport`'s and `compileReport`'s prints,
`compileReport_ok` (the environment instead of the two maps) and
`checkReport_ok` (the maps read from the environment, and a tenth conjunct).
On a consistent run the result is unchanged.

**Amended (coordinator decision, 2026-10-21 ~05:05): constructors.** The
subset's compile also claims the constructors of its inductives, and a
constructor resolved before the subset compiled is not one of its members, so
not among the extra names. The check also refuses a resolved name outside the
aux map that is a constructor (`InductiveVal.ctors`) of an input inductive
among the extra names (`extraCtors`, `extraCtors_contains`); it takes the input
environment. Re-frozen with it: `crossClaimed`'s, `checkReport`'s and
`checkReport_ok`'s prints, and this section (a third root, a second runtime
definition, the print of `extraCtors`). -/

/-- info: [cert-audit] cross-SCC claims: 3 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] cross-SCC claims: 2 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "cross-SCC claims"
    (#[`crossClaimed_none, `extraCtors_contains, `noCrossClaims].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "cross-SCC claims" #[``Ix.Cert.crossClaimed, ``Ix.Cert.extraCtors]

/-- info: def Ix.Cert.extraCtors : Ix.Environment → Std.HashSet Ix.Name → Std.HashSet Ix.Name :=
fun env extras =>
  Std.HashSet.fold
    (fun s e =>
      match env.consts.get? e with
      | some (Ix.ConstantInfo.inductInfo iv) => Array.foldl (fun s c => s.insert c) s iv.ctors
      | x => s)
    ∅ extras -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.extraCtors

/-- info: def Ix.Cert.crossClaimed : Ix.Environment →
  Std.HashMap Ix.Compile.ExactKey.ExactName Address →
    Std.HashMap Ix.Compile.ExactKey.ExactName Address → Std.HashSet Ix.Name → Option Ix.Name :=
fun env resolved aux extras =>
  have ctors := Ix.Cert.extraCtors env extras;
  List.findSome?
    (fun x =>
      match x with
      | (n, snd) => if (!aux.contains n && (extras.contains n || ctors.contains n)) = true then some n else none)
    resolved.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.crossClaimed

/-! ## Pass 3's heads are in the changed set (B9b, `HookFree`'s discharge, (i); coordinator decision, 2026-10-21)

A block's merge publishes Pass 3's heads (`CompileEnv.p3Heads`) from hook 1
(`editBlock`), whose inputs come from the aux tail (AuxGen's `partial` code,
which no proof follows), and hook 2 (`prepareBlock`) rewrites every block that
references a head. `compileReport` now refuses a result in which a head of the
driver's final environment is not in the compile's changed set
(`checkReport`'s eleventh check, `foreignHead`, which computes the changed set
only when there are heads; probe `ports/20261021T034341Z-hookprobe`: no heads
on Init+Std; on Mathlib 329 heads, all among the 752 names of the changed
set). With it, a block whose members and references avoid the changed set
meets no head at block time (with the fold's monotonicity: a head leaves the
heads only with its name among the failures). Re-frozen with it:
`checkReport`'s print and `checkReport_ok` (an eleventh conjunct). On a
consistent run the result is unchanged.

**Re-frozen (2026-10-21, coordinator decision): the check reads the
regenerated names.** Computing the changed set cost about 245 s on Mathlib,
about half of the compile phase (`ports/20261021T065228Z-hookprobe`, quiet
box). `foreignHead` now refuses a head that is not a regenerated published
input name (`regeneratedNames`: a `Named` entry whose original-form record is
at another address, of an input name), one pass over the published names.
Each such name has a `regenerated` entry in the changed set whatever its
changed components (`Unchanged.regenerated_entry`), so `foreignHead_none` and
`headsChanged` keep their statements; they moved to `Ix.Cert.Unchanged`,
which proves them through `regeneratedNames_spec`. Re-frozen with it:
`foreignHead`'s print and `checkReport`'s print (the heads check's message).
The check is stronger than the changed-set test it replaces; on valid input
every head is regenerated (probe `ports/20261021T145130Z-gates-fh`: on Init+Std no
heads; on Mathlib 329 heads, all 329 regenerated; no recorded failure on either). -/

/-- info: [cert-audit] heads: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] heads: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "heads"
    (#[`foreignHead_none, `headsChanged].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "heads" #[``Ix.Cert.foreignHead]

/-- info: def Ix.Cert.foreignHead : Ix.Environment →
  Ix.AuxGen.AuxTable → Std.HashMap Ix.Compile.ExactKey.ExactName Ix.Name → Ixon.Env → Option Ix.Name :=
fun env table heads ixe =>
  if heads.isEmpty = true then none
  else
    have regenerated := Ix.Cert.regeneratedNames env table ixe;
    List.findSome?
      (fun x =>
        match x with
        | (h, snd) => if regenerated.contains h = true then none else some h)
      heads.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.foreignHead

/-- info: def Ix.Cert.regeneratedNames : Ix.Environment →
  Ix.AuxGen.AuxTable → Ixon.Env → Std.HashSet Ix.Compile.ExactKey.ExactName :=
fun env table ixe =>
  Std.HashMap.fold
    (fun s n named =>
      if (named.original.isSome && (env.consts.get? n).isSome && !table.identical n) = true then s.insert n else s)
    ∅ ixe.named -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.regeneratedNames

/-! **Re-frozen (2026-10-21, CQ5.2 (b), flagged Cert path): the heads check follows
the changed set's `regenerated` rule.** The changed set now reads `regenerated`
off the compile's aux table (`Ix.AuxGen.AuxTable.identical`: a published input
name with an original-form record that the table does not find identical), so
`regeneratedNames` takes the table and reads that rule, and `checkReport` passes
the final compile environment's table (`cenv.auxReport.table`; the statements'
`compileTable env`, `compileTable_eq`). `foreignHead_none` and `headsChanged` are
restated over `ofCompile { consts := env.consts } (compileBlocks env)
(compileTable env) ixe`. Re-frozen with it: `foreignHead`'s and
`regeneratedNames`' prints, `checkReport`'s print and `checkReport_ok`. -/

/-! ## Input constants carry their names (B9b, `HookFree`'s discharge, membership; coordinator decision, 2026-10-21)

The block compile names its projections by its members' own names
(`ConstantVal.name`, through `MutConst`), while the condensation and the
driver group and look them up by the names they are stored under; no
statement relates the two. `compileReport` now refuses an input in which a
constant's own name does not hash like the name it is stored under
(`checkReport`'s twelfth check, `misnamedInput`; probe
`ports/20261021T034341Z-hookprobe`: 0 on the materialized constants of
Init+Std, 36,870, and Mathlib, 237,499). With it, every name a block's
compile claims is a member's or a member's constructor's. Re-frozen with it:
`checkReport`'s print and `checkReport_ok` (a twelfth conjunct; its proof now
walks the checks' branches instead of splitting every check's result). On a
consistent run the result is unchanged. -/

/-- info: [cert-audit] input names: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] input names: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "input names"
    (#[`misnamedInput_none, `inputsNamed].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "input names" #[``Ix.Cert.misnamedInput]

/-- info: def Ix.Cert.misnamedInput : Ix.Environment → Option Ix.Name :=
fun env =>
  List.findSome?
    (fun x =>
      match x with
      | (n, ci) => if (ci.getCnst.name == n) = true then none else some n)
    env.consts.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.misnamedInput

/-! ## Input constructors belong to their inductive (B9b, `HookFree`'s discharge, membership; coordinator decision, 2026-10-21 ~05:20)

A block's compile claims its inductives' constructors, looked up by the names
the inductive lists (`InductiveVal.ctors`); a claimed constructor is in the
inductive's component, and in every closure that holds it, only if it
references the inductive. `compileReport` now refuses an input in which a
constructor an input inductive lists is not stored as a constructor of it
(`ConstructorVal.induct` hashing like the name the inductive is stored under;
`checkReport`'s thirteenth check, `strayConstructor`). Re-frozen with it:
`checkReport`'s print and `checkReport_ok` (a thirteenth conjunct). On a
consistent run the result is unchanged. -/

/-- info: [cert-audit] input constructors: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] input constructors: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "input constructors"
    (#[`strayConstructor_none, `ctorsBelong].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "input constructors" #[``Ix.Cert.strayConstructor]

/-- info: def Ix.Cert.strayConstructor : Ix.Environment → Option Ix.Name :=
fun env =>
  List.findSome?
    (fun x =>
      match x with
      | (n, ci) =>
        match ci with
        | Ix.ConstantInfo.inductInfo iv =>
          List.find?
            (fun c =>
              match env.consts.get? c with
              | some (Ix.ConstantInfo.ctorInfo cv) => !cv.induct == n
              | x => true)
            iv.ctors.toList
        | x => none)
    env.consts.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.strayConstructor

/-! ## Recorded failures are input names (B9b, `HookFree`'s discharge, (i); coordinator decision, 2026-10-21 ~08:17)

A reference of the block holding a compile's key may name no input constant
(a ground edge can dangle: `Ix.groundExpr` is `partial`, so no proof shows
edges land in the input). If such a name was a Pass 3 head when the block
compiled and was withdrawn later, it is recorded as a failure, and `NoFailure`
(over the closure only) does not refute it. `compileReport` now refuses a
driver's final environment that records a failure under a name the input's
map does not hold (`checkReport`'s fourteenth check, `strayFailure`). The
proof route not taken: a fold invariant that every recorded failure is a
condensation member. Re-frozen with it: `checkReport`'s print and
`checkReport_ok` (a fourteenth conjunct). On a consistent run the result is
unchanged. -/

/-- info: [cert-audit] recorded failures: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] recorded failures: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "recorded failures"
    (#[`strayFailure_none, `failuresInput].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "recorded failures" #[``Ix.Cert.strayFailure]

/-- info: def Ix.Cert.strayFailure : Ix.Environment → Std.HashMap Ix.Name String → Option Ix.Name :=
fun env ungrounded =>
  List.findSome?
    (fun x =>
      match x with
      | (n, snd) => if (env.consts.get? n).isSome = true then none else some n)
    ungrounded.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.strayFailure

/-! ## One projection record per definition member (CtxAgree's hints premise; coordinator decision, 2026-10-21 ~18:20)

The reader takes a definition block member's hint at the projection record of it
it finds first (`Ix.Cert.hintsOf`), quotient Source at the address the member's
name is published at (`Ix.LeanIngress.fiberHintsMap`). They are one hint when the
member has one projection record (`Ix.Cert.CtxAgree.hintsOf_projection`'s
premise). `compileReport` now refuses an artifact with two stored definition
projection records of one member (`checkReport`'s sixteenth check,
`projectionCollision`). The proof route not taken: from the compiler's emission,
one projection per member (≈0.2–0.4k). Re-frozen with it: `checkReport`'s print
and `checkReport_ok` (its projection conjunct, now sixteenth). On a consistent run the result is
unchanged.

The first corpus probe (ports/20261021T203754Z-projection-probe-p121) found
zero collisions on Init+Std, but the two full-decoder passes cost 6.60–6.64 s
for 29 projections among 100,327 records. The header filter now skips all
other records, respecting cached values and uncached buffer/offset behavior
on arbitrary inputs (`ProjectionRead.fast_eq`); candidate projections are
decoded once. `ProjectionRead.collision_eq` proves the entire check returns
exactly the original first collision on every input. The collision theorem
keeps its original conclusion. Only
the collision reader's print and these audit roots are re-frozen. -/

/-- info: [cert-audit] projections: 4 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] projections: 3 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "projections"
    ((#[`projectionCollision_none, `projectionsOne].map (`Ix.Cert ++ ·)) ++
      #[``Ix.Cert.ProjectionRead.fast_eq, ``Ix.Cert.ProjectionRead.collision_eq])
  checkRuntime (tag := "cert-audit") "projections" #[``Ix.Cert.projectionCollision, ``Ix.Cert.definitionProjectionHeader,
    ``Ix.Cert.definitionProjectionFast]

/-- info: def Ix.Cert.projectionCollision : Ixon.Env → Option (Address × Nat) :=
fun ixe =>
  have entries := List.filterMap Ix.Cert.definitionProjectionFast ixe.consts.toList;
  have first :=
    List.foldl
      (fun m x =>
        match x with
        | (r, a) => if m.contains r = true then m else m.insert r a)
      ∅ entries;
  List.findSome?
    (fun x =>
      match x with
      | (r, a) => if decide (first[r]? = some a) = true then none else some r)
    entries -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.projectionCollision

/-! ## S1's units, (R1): each record's and each group's lowering

`Ix.Cert.ReaderUnits`: the stream the Ixon reader decodes is its records'
lowerings concatenated, one per record (`readRecords_units`), and the Source
ingress's is its scheduled groups' lowerings (`leanIngress_units`). Each
lowering is the modeller's records then one declaration, or only
declarations, and every declaration past the modeller's names only the
record's member keys (`MemberKeyOf`) or the group's ingress keys
(`GroupKeyOf`). Neither is ever derived, so each lowering is empty or ends in
a declaration that is not generated (`Lowering.closed`, `LoweringBy.closed`):
what IxC's units check needs of each side to read the units as the lowerings'
pieces. Nothing about `InModel.generate`'s output is used. -/

/-- info: [cert-audit] reader units: 25 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "reader units"
    (#[`stream_lowerings, `readRecords_lowerings, `readDefinition_key, `lowerInductive_decls,
      `readInductive_lowering, `readRecord_lowering, `readRecords_units, `bindingsOf_keyed,
      `contextWith_keyed, `memberKey_role_or_id, `MemberKeyOf.not_derived, `LoweringBy.closed,
      `Lowering.closed, `LoweringBy.map, `defOrder_lt, `convertInductive_keys, `convertDefinitions_keys,
      `convert_keys, `lower_lowering, `canonDecl_names, `lowerAll_lowerings, `scheduleOf_ok,
      `graph_converted_ok, `leanIngress_units, `GroupKeyOf.not_derived].map (`Ix.Cert.ReaderUnits ++ ·))

/-! ## Route A, B9b piece 1: Pass 3's hooks on a block outside the changed set

`Ix.Cert.PassHooks`: the clique step (`cliqueStep`) returns the compile
environment as it is and the empty block state on a block outside every
clique (`cliqueStep_inert`); hook 2 (`prepareBlock`) returns the compile
environment as it is when none of the block's condensation references is a
head (`prepareBlock_unreferenced`); `withMetaRefs` changes no record; so the
records `runBlockWithAux` returns are the block compile's, a lone constant's
`compileConstantInfo` or `sortConsts` then `compileMutualBlock`, run from the
empty block state (`runBlockWithAux_records`). Hook 1 and the aux tail run
after the `BlockResult` and return it as it is. -/

/-- info: [cert-audit] pass hooks: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "pass hooks"
    (#[`cliqueStep_inert, `prepareBlock_unreferenced, `withMetaRefs_records,
      `runBlockWithAux_unreferenced, `findConst_preserves, `mkIndc_preserves, `forIn_set_state,
      `compileBlockWithAux_result, `compileBlockWithAux_records, `runBlockWithAux_records].map (`Ix.Cert.PassHooks ++ ·))

/-! ## Route A, B9b piece 2: where a resolved name's record comes from

`Ix.Cert.Resolution`: every entry of the driver's final resolution map is an
aux name's or a primary claim of a block compiled during the fold, with the
claimed record's bytes stored at its address (`compileUnchecked_provenance`);
such a claim is one of `runBlock`'s on a subset of a condensation block's
members, under a key, against a reached state (`compiled_runBlock`, with
`auxBlockOutcome_cross`); the block references never change during the fold
(`reach_p3BlockRefs`); where Pass 3's hooks are identities (`HookFree`), the
claim is the block compile's (`hookFree_compiled`). `compileReport_claim` is
B9b with `HookFree` as its premise. -/

/-- info: [cert-audit] resolution: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "resolution"
    (#[`reach_provenance, `compileUnchecked_provenance, `auxBlockOutcome_cross, `compiled_runBlock,
      `reach_p3BlockRefs, `hookFree_compiled, `compileReport_claim].map (`Ix.Cert.Resolution ++ ·))

/-! ## Route A, B9b step 4: `HookFree` discharged

`Ix.Cert.HookFree`: for a closure that avoids the changed set and has no
failure, every resolved name of it outside the final aux map is a claim of a
whole condensation block of the closure, compiled under its key against a
reached state, with Pass 3's hooks identities there (`HookFree`), so the
block compile's (`compileReport_hookFree`). A cross-SCC subset's claim is
refuted by the tenth check (`cross_refuted`, `applyAuxBlockOutcome_cross_extras`);
a compiled block's claims are its members' (`Ix.Cert.Claims.runBlock_owned`,
image blocks included); no reference or member of a block of the closure is a
snapshot head (`hookFree_of_sub`, from the eleventh and fourteenth checks,
`final_of_report`). `Ix.Cert.Resolution`'s fold steps now also keep the input
environment (`reach_env`).

**Re-frozen (2026-10-21, CQ5.2 (b)): `HookFree`'s third conjunct, the clique
step.** `runBlockWithAux` runs the clique step (`cliqueStep`) first, so
`HookFree` also says it is the identity, and `hookFree_of_sub` proves it from
`cliqueInert`: no member is in the clique table and no reference of the block
holding its key is one of Lean's encoding constants of a clique
(`Unchanged.clique`, `Unchanged.cliqueCaller` from `Avoids`), against the
tables the fold keeps (`Resolution.reach_cliques`; `Step` keeps `p3Cliques`
and `p3CliqueRoots`, and the fold's initial tables are `scheduleCliques`',
`cliqueTables_eq`). A claim's ownership holds through the clique step too
(`Claims.cliqueStep_keeps`: its overlay holds input constants with other
values, `Claims.prepareCliques_overlay`). The heads check reads the compile's
aux table (`compileTable_eq`). 7 roots → 12. -/

/-- info: [cert-audit] hook-free: 12 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "hook-free"
    ((#[`compileReport_hookFree, `final_of_report, `hookFree_of_sub, `cross_refuted,
      `applyAuxBlockOutcome_cross_extras, `cliqueTables_eq].map (`Ix.Cert.HookFree ++ ·)) ++
      #[``Ix.Cert.Claims.runBlock_owned, ``Ix.Cert.Resolution.reach_env, ``Ix.Cert.Resolution.reach_cliques,
        ``Ix.Cert.Claims.cliqueStep_keeps, ``Ix.Cert.Claims.prepareCliques_overlay, ``Ix.Cert.compileTable_eq])

/-! ## S1's generated records: the statements half of `CtxAgree`

`Ix.Cert.CtxAgree`: a mutual or nested block's modeller records agree on the
two streams. At reader states that agree on the block's scope, the block and its
renaming lower to renamed records through IxC's parametricity
(`lowerInductive_mapKeys`, at `KeyScope.Pre`); the states agree at every key but
the derived ones by the per-key relation (`ReadsAgreeAt`, read off the two
prefixes, `nonAuxAgree_of_reads`), and at the derived ones because they are an
earlier block's generated records on both sides (the cone induction,
`Streams.units`). Both sides run one hint per published definition
(`hints_agree`, with `fiberHintsMap_named`, `hintsOf_projection`,
`hintsOf_block`). -/

/-- info: [cert-audit] ctx agreement: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "ctx agreement"
    (#[`Streams.units, `lowerInductive_mapKeys, `ctxAgree_genCtx, `blockRecOf_mapKeys,
      `occursConstFast_eq, `nonAuxAgree_of_reads, `hints_agree, `fiberHintsMap_named,
      `hintsOf_projection, `hintsOf_block].map (`Ix.Cert.CtxAgree ++ ·))


/-! ## Identity rows: the promotion's compared address survives publication (B9d, check 15)

`checkReport` refuses identity rows that disagree under one name key on their
verdict or compared address, and an identical row whose address is not the
name's final published address (`identityMismatch`). Agreeing duplicates
remain valid. `identityMismatch_none` and `identityRowsAgree` expose both
facts; the provenance and preservation of the bytes compared remain B9d.
The report's print and success theorem are re-frozen for this new branch and
conjunct. The existing projection refusal is now check 16. No final
compiler-correctness statement gains a premise. -/

/-- info: [cert-audit] identity rows: 2 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [cert-audit] identity rows: 1 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "cert-audit") "identity rows"
    (#[`identityMismatch_none, `identityRowsAgree].map (`Ix.Cert ++ ·))
  checkRuntime (tag := "cert-audit") "identity rows" #[``Ix.Cert.identityMismatch]

/-- info: def Ix.Cert.identityMismatch : Array (Ix.Name × Bool × Address) → Ixon.Env → Option (Ix.Name × Bool × Address) :=
fun identity ixe =>
  have first :=
    Array.foldl
      (fun m x =>
        match x with
        | (n, s, a) => if m.contains n = true then m else m.insert n (s, a))
      ∅ identity;
  List.find?
    (fun x =>
      match x with
      | (n, s, a) => first.get? n != some (s, a) || s && Option.map (fun x => x.addr) (ixe.named.get? n) != some a)
    identity.toList -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.identityMismatch

/-! ## B9d: final published bytes of an identical original form

A table's identical verdict comes from a true identity row. That row's
original-form compile is from a reached snapshot and condensation block;
its compared singleton bytes, or projection and original-block bytes,
survive every merge and withdrawal and are copied into the artifact.
Check15 ties the row to the final published address. `unchanged_original`
composes B9a's table verdict with this byte-level fact. No digest-injectivity
or new final compiler-correctness premise is assumed; this does not claim
semantic equivalence of changed code from target acceptance alone. -/

/-- info: [cert-audit] original bytes: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "original bytes"
    (#[`table_identical_origin, `originalIdentities_true, `Compared.mono,
      `apply_rows, `auxBlockOutcome_original, `reach_rows, `compileEnvFold_report,
      `compileEnvFold_identity, `compileReport_identical, `unchanged_original].map (`Ix.Cert.OriginalBytes ++ ·))

/-! ## Projection hints: uniqueness from the compiler guard

The hint table's projection entry and the guard's definitionProjection are
exactly the same decoded projection. Successful compilation supplies the
uniqueness used by hintsOf_projection. The published Source/Ixon hint wrapper
still takes the existing PublishedAgree condition; compileReport does not
check that separate address-map condition. -/

/-- info: [cert-audit] published projection hints: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "published projection hints"
    (#[`projEntry_definitionProjection, `hintsOf_projection_compileReport,
      `hints_agree_projection].map (`Ix.Cert.CtxAgree ++ ·))

/-! ## Projection rewriting: scoped lookup and definition transport

The actual projection rewrite and definition lowerer commute with scoped
renaming under ProjectionAgree and height agreement. Successful inductive
lowering exposes its exact owner array. Deriving that lookup relation from
the two streams remains an intermediate obligation; the following owner
section discharges the constructor's renaming. No final premise is added. -/

/-- info: [cert-audit] projection lookup transport: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "projection lookup transport"
    (#[`projRewrite_mapKeys, `lowerDefinition_mapKeys,
      `lowerInductive_owners].map (`Ix.Cert.CtxAgree ++ ·))

/-! ## Source prelude entries at every group boundary

`SourcePrelude.prepareSourceCollapsed_prefix` extracts the actual raw/kept
lowering trace from successful preparation and proves equality of all five
reader maps at prelude keys at every retained-read boundary. Successful
collapse claims names monotonically and keeps only fresh declarations;
the raw closing declaration also claims the unfiltered side arrays' keys.
Both modeller rungs emit no basis declarations, proved from their output
constructors. Thus the existing final-state prelude check gives every
boundary's equality, with no executed-checker acceptance or units premise.
Target-prefix coverage and raw/kept reading alignment remain separate
composition obligations. -/

/-- info: [cert-audit] source prelude prefixes: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source prelude prefixes"
    ((#[`collapseRead_facts, `lowerAllCollapsed_trace, `collapseGroup_sideFresh,
      `lower_noBasis, `group_frame, `lowerAllCollapsed_prefix,
      `prepareSourceCollapsed_prefix].map (`Ix.Cert.SourcePrelude ++ ·)) ++
      #[``Ix.Cert.SourcePrelude.Shape.generate_noBasis])

/-! ## Projection owners: construction commutes with scoped renaming

The structure-shape check and the direct recognizer's success flag are
preserved. Together with the native recognizer, recursion flags and indexed
candidate selection, they give ownersOf_mapKeys and the exact corresponding
lowerInductive owner lists. This closes a local construction obligation,
not whole-stream lookup provenance or prefix preservation. -/

/-- info: [cert-audit] projection owner construction: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "projection owner construction"
    (#[`structShape_mapKeys, `structPartsCore_isSome_mapKeys,
      `ownersOf_mapKeys, `lowerInductive_owners_mapKeys].map (`Ix.Cert.CtxAgree ++ ·))

/-! ## Projection fields: exact ordered writes and paired-read transport

Owners retain the producing block's scope. Projection-level recognition
commutes with arbitrary key renaming; exact commit/fold formulas retain the
update order. Entry-list transport assumes already-paired reads, not an
unproved actual stream correspondence. Raw/kept generated-index alignment
and dropped-generated level consistency remain separate obligations. -/

/-- info: [cert-audit] projection field entries: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "projection field entries"
    (#[`ownersOf_good, `lowerInductive_owners_good, `projLevelEntry_mapKeys,
      `noteGenerated_projLevels, `fold_projection_fields,
      `UnitAgree.projection_entries].map (`Ix.Cert.CtxAgree ++ ·))

/-! ## Source names: raw generated and production ordinary classification

The generator results are nonempty and all-derived. The actual raw Source
read classifies its generated prefix. Production fiberAliasAt preserves
ordinary keys through the quotient conversion; arbitrary FiberMap does not.
This does not establish retained indices, duplicate/drop replay or iota-level
consistency after collapse, and adds no final correctness premise. -/

/-- info: [cert-audit] source name classification: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source name classification"
    (#[`fiberAliasAt_not_aux, `generate_names, `lower_generated,
      `quotient_lower_ordinary].map (`Ix.Cert.SourceNames ++ ·))

/-! ## Source collapse: retained indices and generated-prefix classification

Actual successful collapse yields an ordered subsequence of original pairs,
with exactly its retained generated cutoff. Classification transfers to the
kept read and is instantiated for the production quotient conversion. No
name uniqueness, drop replay, owner coherence or semantic-map equality is
assumed or established by these endpoints. -/

/-- info: [cert-audit] source retained prefix: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source retained prefix"
    (#[`collapseRead_retained, `Retained.generated_le, `Retained.indices,
      `Retained.transfer, `quotient_collapse_classified].map (`Ix.Cert.SourceRetained ++ ·))

/-! ## Source collapse: exact owners and per-step replay fixed points

OwnerExact and kept basis-freedom hold on the actual reachable Source trace.
A successful drop is the exact kept declaration at an in-bounds owner index.
Replay is pointwise idempotent and preserves old unwritten heights. The
per-step endpoint retains explicit internal owner/basis/stability conditions;
read-loop/commit assembly and production Trace stability remain follow-ups. -/

/-- info: [cert-audit] source owner replay: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source owner replay"
    (#[`step_drop, `trace_ownerExact, `trace_keptNoBasis, `replay_idem,
      `StableOwned.fields, `step_replay].map (`Ix.Cert.SourceReplay ++ ·))

/-! ## Source reads: stable replay through actual collapse and commit

The actual loop preserves its explicit owner/basis/stability invariants and
relates raw and kept replay. Retained classification identifies the actual
commit folds, yielding all-five-lookup agreement while allowing counters to
differ. Production schedule extraction and Trace StableOwned discharge are
still separate; no final compiler-correctness premise is added. -/

/-- info: [cert-audit] source read commits: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "source read commits"
    (#[`commit_replay, `collapseRead_replay, `collapseRead_commit,
      `quotient_lower_classified].map (`Ix.Cert.SourceCommit ++ ·))

/-! ## Production Source trace: conversion provenance and stable replay

Both converted-array maps preserve actual group provenance; missing/default
and failed conversions cannot yield success. Trace induction supplies stable
replay, and actual lowering/preparation wrappers discharge membership and
stability premises. This closes these Source context facts, not acceptance,
Source/Ixon unit correspondence or the final compiler theorem. -/

/-- info: [cert-audit] production source trace: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "production source trace"
    (#[`graph_conversion, `trace_stable, `lowerAllCollapsed_stable,
      `prepareSourceCollapsed_stable].map (`Ix.Cert.SourceTrace ++ ·))

/-! ## Reader cache coverage and role keys

`ReaderKeys` proves lookup origins, first-address preservation and coverage
for the actual keysOf fold, and role origins/injectivity for bindingsOf.
Singleton fallback resolves directly. Scoped ReconCompatible isolates the
remaining reconstruction/cache-hit case and gives memberKey's role/input
classification. Its scope is the references that actually emit entries.
This is an internal predicate; compiler-specific reconstruction/fallback
compatibility and target-prefix preservation remain unproved here. No
production guard or final admission premise is added. -/

/-- info: [cert-audit] reader caches and roles: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "reader caches and roles"
    (#[`withAddress_keeps, `keysOf_address_origin, `keysOf_key_origin,
      `keysOf_covers, `bindings_role_origin, `bindings_role_inj,
      `singletonAt_resolves, `memberKey_role_iff].map (`Ix.Cert.ReaderKeys ++ ·))

/-! ## Selected closure rows and reader caches

ReaderClosureKeys connects resolving stored seeds and published Source
rows to the actual keysOf cache over Stream.decodedOf. Input rows shadow
fallback rows; selected recursors retain that exact origin split. A
coherent standalone recursor origin is cached. With an internal fallback
singleton-shape premise, every selected recursor is cached or has an
explicit input origin in a mutual block. The closed fallback data, all
emitting-reference coverage and paired-trace correspondence remain owed.
StoredCanonical/closure_decodes still connect decodedOf to raw admission;
no final assumption, guard or hash-injectivity premise is added. -/

/-- info: [cert-audit] selected closure caches: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "selected closure caches"
    (#[`context_input, `context_coherent_of_nodup, `selected_origin,
      `standalone_origin_cached, `selected_cached_or_input_mutual,
      `seeded_resolved_cached, `published_resolved_cached].map (`Ix.Cert.ReaderClosureKeys ++ ·))

/-! ## The checked committed fallback

preludeFor checks fallback recursor shape independently of declaration
role names; generic readPrelude and injected preludes remain flexible.
ReaderFallback derives singleton recursor origins from that check, and
coherence from kernel-checked fixed-address uniqueness and structural
decoder transport, without reducing evidence bodies. Its selected-recursor
result is scoped to actual preludeFor success and retains the mutual-input
case. All-emitting-reference coverage, paired traces and StoredCanonical
remain separate; no final premise or new axiom is introduced. -/

/-- info: [cert-audit] committed fallback: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "committed fallback"
    ((#[`fixed_addresses, `decoded_keys, `preludeFor_keys, `preludeFor_singletons,
      `context_coherent, `selected].map (`Ix.Cert.ReaderFallback ++ ·)) ++
      #[``Ix.Kernel.Reader.preludeFor_checks])

/-! ## Original-data finalization: exact bytes and old-field frame -/

/-- info: [cert-audit] original-data frame: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "original-data frame"
    (#[`insertBytes_existing, `insertBytes_self, `insertBytes_keeps,
      `finalizeOriginals_frame].map (`Ix.Compile.OriginalData ++ ·))

/-! ## Generated declaration names: input-block base origins

Successful Mutual and Nested generation root every emitted declaration name
at an input block name's base. The public wrappers discharge the internal
scope from the actual input. Distinctness, no-drop, accepted-stream alignment
and Source/Ixon unit correspondence remain separate obligations. -/

/-- info: [cert-audit] generated base origins: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "generated base origins"
    (#[`genMutual_bases, `genNested_bases, `generate_bases].map (`Ix.Cert.SourceOrigin ++ ·))

/-! ## Generated bases of actual inductive reads

The generator's roots are closing block names even when its type zip is
truncated. Generated entries inherit that origin; ordinary-key and mapped
forms give the baseS/baseA shapes. Actual quotient conversion discharges
ordinary keys. No accepted-stream, no-drop or pairing premise is hidden. -/

/-- info: [cert-audit] generated read bases: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "generated read bases"
    (#[`roots_blockRecOf, `lowerInductive_bases, `lowerInductive_bases_ordinary,
      `lowerInductive_bases_mapKeys, `quotient_lowerInductive_bases].map (`Ix.Cert.SourceOriginRead ++ ·))

/-! ## Strong value models and exact equation rows

Strong-model admission and its value-model projection preserve one
interpretation. Actual stored Eq rows equate endpoints within their declared
type/universe domains. These leaves do not establish source-copy faithfulness,
changed-code conversion, endpoint typing or the final compiler theorem. -/

/-- info: [cert-audit] strong models and equation rows: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "strong models and equation rows"
    (#[`ofStrong, `strongModel_of_acceptsRef, `commutes_strong, `equation_values,
      `stored_equation_values, `strong_equation_values, `equation_to_constant,
      `equation_to_stored_constant].map (`Ix.Cert.ValueRows ++ ·))

/-! ## Full-grade conversion at the actual checked subjects

The same strong model supplies both inferred readings and grades. Static
DefEq equates their public values; actual annotation/value-front and
definition-check traces retain the checked subjects' provenance. No raw
let/fvar denotation or compiler-wide conversion premise is introduced. -/

/-- info: [cert-audit] checked conversion values: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "checked conversion values"
    (#[`infer_reading, `reading_denotes, `defeq_values, `defeq_denotations_eq,
      `checked_defeq_values, `definition_front, `valueFront_defeq_values].map (`Ix.Cert.ConversionValues ++ ·))

/-! ## Actual image-generation prefix and production view provenance

The successful StateT run supplies one coherent prefix through telescope,
minor analysis and buildRecApp. The view retains its actual spec/canonical
build and exact back-renaming. No rule simulation or recognition is assumed. -/

/-- info: [cert-audit] image production origins: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "image production origins"
    (#[`imageOf_origin, `view_image_origin, `buildViewWith_spec,
      `buildView_origin].map (`Ix.CompileCert.ImageOrigin ++ ·))

/-! ## Actual image-shape recognition and bounded selectors

Successful loops recover the exact header and argument witnesses, preserving
raw cached hashes. Optional lookups discharge bounds for every selected
argument and retained minor term. Permutations and production provenance use
the same recognition success; image completeness/simulation stay separate. -/

/-- info: [cert-audit] image shape recognition: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "image shape recognition"
    (#[`position_shape, `readShape_result, `readShape_permutations,
      `readShape_reads, `production_origin].map (`Ix.CompileCert.ImageShape ++ ·))

/-! ## Exact equation rows from successful production construction

The row's source/value/universe, empty-state proof run and guard remain
linked to its actual returned theorem. Source-copy header/value identities
name only the producer operations; semantic faithfulness, required row
existence, publication, reading and Eq-domain discharge remain separate. -/

/-- info: [cert-audit] clique row producer shape: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "clique row producer shape"
    (#[`rowOfWith_shape, `rowOf_shape, `srcCopy_header, `srcCopy_value,
      `rowOfWith_header].map (`Ix.CompileCert.CliqueRowShape ++ ·))

/-! ## Actual row/copy workers: positional coverage and multiplicity

The real sorted arrays and task/mapM workers relate outputs positionally,
with exact occurrence counts and both directions of provenance. The non-WF
empty result is explicit; planner membership, publication/address coverage
and semantic copy faithfulness are not inferred. -/

/-- info: [cert-audit] clique row output coverage: 9 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "clique row output coverage"
    (#[`row_workers, `rowsOf_produced, `rowsOf_wf, `Produced.sizes,
      `Produced.copy_of_input, `Produced.row_of_member, `Produced.input_of_copy,
      `Produced.member_of_row, `Produced.copy_contents].map (`Ix.CompileCert.CliqueRowsCoverage ++ ·))

/-! ## Actual closed O6 recursor branch: raw reader reduction

The real successful pass, image/matcher provenance and both reader results
yield raw kernel Red through a derived positional selector/pick relation.
Universe arity and closed arguments remain explicit. Raw .never is not a
checked annotation, and no value/under-binder/fallback claim is made. -/

/-- info: [cert-audit] O6 raw reader reduction: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 raw reader reduction"
    (#[`related_unique, `Lambdas.beta, `o6_rec_output, `o5_subst_levels,
      `data_picks, `selects_read, `o6_rec_raw_reader_red].map (`Ix.CompileCert.O6RecRead ++ ·))

/-! ## Actual closed annotation/inference: certified beta and public values

The exact application run supplies argument io inference and domain DefEq,
including Prop. The annotation trace retains the real opener and marker.
Reduction soundness supplies the reduct's frame/read/grade at the same model;
annotation of the raw reduct or actual O6 output is not identified here. -/

/-- info: [cert-audit] annotated beta values: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "annotated beta values"
    (#[`inferred_beta_certificate, `annotate_lam_trace, `annotate_beta_trace,
      `inferred_beta_values, `annotated_beta_values].map (`Ix.Cert.AnnotatedBeta ++ ·))

/-! ## Actual O6 selector layout through annotation

The real typed openings preserve the exact terminal selector body. Actual
argument runs agree across fuels in one env/depth, yielding equality with
the actual checked output, including repeated/reordered arguments and extras.
No checked beta spine, value preservation or under-binder claim is inferred. -/

/-- info: [cert-audit] O6 annotation layout: 9 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 annotation layout"
    (#[`annotation_unique, `annotate_apps, `Flat.annotate, `open_close,
      `annotate_selector_tail, `ReadAnn.unique, `read_ann_apps,
      `selectors_annotated, `o6_rec_annotation_layout].map (`Ix.CompileCert.O6Annotation ++ ·))

/-! ## Checked lambda spines from original full inference

Actual head inference fixes every lambda/forall domain. The original
application trace supplies each certified beta, including Prop, without
intermediate-reduct inference. Bulk substitution and extra arguments are
derived exactly; the O6 public-value wrapper remains separate. -/

/-- info: [cert-audit] checked beta spines: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "checked beta spines"
    (#[`domains_abstract, `inferred_lam_domains, `infer_apps, `trace_beta,
      `checked_lambda_spine_red].map (`Ix.Cert.CheckedBetaSpine ++ ·))

/-! ## Actual closed O6 recursor rewrite: public equal values

The real pass/image/read/annotation trace and baseline full inference derive
checked Red/DefEq. Every strong model of that same prefix env gives a common
public value. No output/reduct inference, N-PERM, CQ5.4 or driver proof is assumed. -/

/-- info: [cert-audit] O6 checked values: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 checked values"
    #[`Ix.CompileCert.O6Values.o6_rec_values]

/-! ## Actual O6 body beneath one enclosing lambda

Whole annotation/inference runs derive the common opener, reopening,
Frame and inner inference. The real opened selector layout yields certified
body Red/DefEq at depth one. Outer marker agreement and whole-lambda values
remain separate; no final closed-occurrence restriction is introduced. -/

/-- info: [cert-audit] O6 actual opened bodies: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 actual opened bodies"
    (#[`annotation_reopen, `trace_beta_at, `checked_spine_at, `OpenAnn.unique,
      `selectors_open_annotated, `opened_layout,
      `o6_rec_under_lam_opened_red].map (`Ix.CompileCert.O6Opened ++ ·))

/-! ## Whole-lambda markers and actual O6 public values

Two real value fronts against one checked header force marker agreement
inside each supplied strong model, including empty binder domains. Actual
body conversion and both reopening identities then give whole-lambda
DefEq/public values. No model existence or context inhabitant is assumed. -/

/-- info: [cert-audit] O6 whole lambda values: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 whole lambda values"
    (#[`lam_mem_pi_bits, `infer_package, `lambda_markers_eq_of_fronts].map
      (`Ix.Cert.LambdaMarkers ++ ·) ++ #[`Ix.CompileCert.O6LambdaValues.o6_rec_under_lam_values])

/-! ## Internal context composition under valid valuations

Actual local checks transport the raw Frame/Ctx invariant and supply
witnessed readings/grades. Same-domain lambda congruence uses the body IH
and bit agreement only under Sat, without a context inhabitant or global
marker equality. Local check producers remain an explicit proof obligation. -/

/-- info: [cert-audit] checked context lambda congruence: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "checked context lambda congruence"
    (#[`annotate_context, `infer_package_at, `lambda_bits_at,
      `eqAt_of_readings, `checked_lambda_congr_at].map (`Ix.Cert.ContextValues ++ ·))

/-! ## Real local fronts from enclosing applications

Paired actual app checks with the same raw function derive both argument
fronts and one WHNF domain. Real function inference/WHNF supplies its
semantic frame/context/read/grade, without inventing a domain check. The
typed-header consumer and full O6 production composition remain separate. -/

/-- info: [cert-audit] actual application argument fronts: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual application argument fronts"
    (#[`function_domain, `paired_app_argument_fronts].map (`Ix.Cert.ApplicationFronts ++ ·))

/-! ## Consumers of the application producer's typed header

The factored marker/congruence proofs consume the proved domain package.
The direct lambda-argument connection derives every header fact and both
local fronts from actual paired app calls. Existing executable-header
interfaces remain wrappers; no domain check or runtime checker is invented. -/

/-- info: [cert-audit] produced typed header consumers: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "produced typed header consumers"
    #[`Ix.Cert.ContextValues.lambda_bits_of_header,
      `Ix.Cert.ContextValues.checked_lambda_congr_of_header,
      `Ix.Cert.ApplicationFronts.paired_app_lambda_arguments]

/-! ## Actual O6 composition through a lambda argument and application

Real enclosing checks and O6 producers derive the lambda shapes, local
fronts/header and body comparison. Application congruence is consumed by
the whole public-value endpoint; no unsupported body IH passes through. -/

/-- info: [cert-audit] O6 whole application values: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 whole application values"
    (#[`app_argument, `o6_lambda_argument_values].map (`Ix.CompileCert.O6ApplicationValues ++ ·))

/-! ## Actual shared dependent telescope producer

Whole annotations and baseline full inference produce common typed domains,
exact per-binder subcalls, bulk-opened leaf runs and frames. Every supplied
strong model then gets a real context-extension trace, without a Sat witness. -/

/-- info: [cert-audit] actual telescope producer: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual telescope producer"
    (#[`openers_append_one, `annotation_reopen_at, `annotation_frame_at,
      `DomainTraceFrom.length, `DomainTraceFrom.at, `ContextTrace.length,
      `paired_telescope_from, `DomainTrace.length, `DomainTrace.at,
      `paired_telescope].map (`Ix.CompileCert.O6Telescope ++ ·))

/-! ## Actual O6 reduction under a shared dependent telescope

Bulk opening preserves the derived selector body at its own binder cursor.
The produced leaf checks and frames supply certified beta; the endpoint
retains all original O6 pass, image and reader evidence. -/

/-- info: [cert-audit] O6 dependent telescope reduction: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 dependent telescope reduction"
    (#[`strip_open_list, `BulkAnn.unique, `bulk_ann_pairs, `bulk_ann_apps,
      `selectors_bulk_annotated, `bulk_opened_layout,
      `o6_rec_under_telescope_opened_red].map (`Ix.CompileCert.O6TelescopeOpened ++ ·))

/-! ## Closing actual paired lambda telescopes

Actual full-inference chains propagate the root compatibility derived
from real header/value fronts within each supplied strong model. -/

/-- info: [cert-audit] checked telescope closing: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "checked telescope closing"
    (#[`lamPw_abstract1, `markers_of_fronts, `close_telescope].map (`Ix.CompileCert.O6TelescopeValues ++ ·))

/-! ## Whole O6 values under an arbitrary shared dependent telescope

The frozen O6 leaf, real header and both whole value fronts derive every
opening, inner run and marker fact. Conversion remains inside each model. -/

/-- info: [cert-audit] O6 whole telescope values: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "O6 whole telescope values"
    #[`Ix.CompileCert.O6TelescopeValues.o6_rec_under_telescope_values]

/-! ## Indexed reference-stream definition fronts

One actual accepted fuel supplies the exact prefix, declaration and suffix.
Lookup persistence identifies the annotated body in the final environment. -/

/-- info: [cert-audit] indexed reference definition fronts: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "indexed reference definition fronts"
    (#[`reference_definition_front_at, `DefinitionFrontAt.unique,
      `DefinitionFrontAt.denotes].map (`Ix.Cert.ReferenceFronts ++ ·))

/-! ## Fronts of the exact prepared Ixon stream

One actual preparation/evidence witness supplies every indexed definition
front; no separately accepted environment or source-form check is chosen. -/

/-- info: [cert-audit] prepared Ixon definition fronts: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "prepared Ixon definition fronts"
    #[`Ix.Cert.ReferenceFronts.ixon_definition_fronts]

/-! ## Actual paired readings under a fixed interpretation

Positive lookup preservation transports the real inference run's literal
support and present projection slots; no prefix model is assumed. -/

/-- info: [cert-audit] fixed interpretation paired readings: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed interpretation paired readings"
    (#[`lookup_guard, `nat_support, `string_support, `projection_slot,
      `inferred_readings_preserved].map (`Ix.Cert.PrefixReadings ++ ·))

/-! ## Actual prefix fronts at the supplied final interpretation

The indexed run derives lookup growth and paired header/body readings.
Final stored-definition laws supply the target package at the same acval. -/

/-- info: [cert-audit] final interpretation prefix fronts: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "final interpretation prefix fronts"
    (#[`lookup_preserved, `readings_across, `final_semantic_front].map
      (`Ix.Cert.ReferenceFronts.DefinitionFrontAt ++ ·))

/-! ## The actual prefix core with the final model's literal valuation

Prefix acceptance yields only model-free Props; every interpreted field
comes from the supplied final model, with both valuation equalities by rfl. -/

/-- info: [cert-audit] fixed final interpretation prefix core: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed final interpretation prefix core"
    (#[`prefix_syntax, `coreAt_acval, `coreAt_cval,
      `core_of_front].map (`Ix.Cert.PrefixCore ++ ·))

/-! ## Actual final-interpretation prefix core and basic target package

Leaf validity, numeral heads and Eq use only the supplied final model;
the actual target package is transported through the same literal acval. -/

/-- info: [cert-audit] actual final interpretation prefix package: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual final interpretation prefix package"
    #[`Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_core]

/-! ## Every stored definition's actual creating reference step

All non-definition paths preserve the exact definition entries, including
native settled/retry, modeled, basis, quotient and projection branches. -/

/-- info: [cert-audit] universal stored definition origins: 17 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "universal stored definition origins"
    (#[`definition_mem, `fold_definitions, `basis_definitions, `member_definitions,
      `recs_definitions, `projection_definitions, `projection_step_definitions,
      `modeled_definitions, `constructors_definitions, `native_table_definitions,
      `native_pass_definitions, `native_tail_definitions, `native_definitions,
      `checkDecl_definitions, `step_definition_origin, `fold_definition_origin,
      `reference_stored_definition_origin].map (`Ix.Cert.PrefixDefinitions ++ ·))

/-! ## Universal prefix unfolding at the supplied final interpretation

Every stored definition uses its actual creating front/run and produced
lookup. Paired readings and the same final model pin its exact leaf. -/

/-- info: [cert-audit] universal fixed interpretation definition row: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "universal fixed interpretation definition row"
    (#[`prefix_definitions_read, `final_prefix_defn].map (`Ix.Cert.ReferenceFronts.DefinitionFrontAt ++ ·))

/-! ## Actual table origin and old-head projection slots

Every new table's former was fresh in the original checker prefix; real
growth then preserves all slots at already-stored heads, without an absence
premise or membership-to-hit shortcut. -/

/-- info: [cert-audit] actual old-head projection slots: 16 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual old-head projection slots"
    (#[`table_mem, `TableOrigin.of_tables, `fold_tables, `basis_tables, `member_tables,
      `recs_tables, `projection_tables, `modeled_tables, `constructors_tables,
      `native_table_origin, `native_pass_origin, `native_tail_origin, `native_origin,
      `step_table_origin, `checked_step_stored_slots,
      `checked_suffix_stored_slots].map (`Ix.Cert.PrefixConstType ++ ·))

/-! ## Every resolving header at the supplied final interpretation

Actual growth derives subject-specific literal queries and both projection
branches. The SAME final model supplies every constant type/level/depth row. -/

/-- info: [cert-audit] universal fixed interpretation constant types: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "universal fixed interpretation constant types"
    ((#[`query_eq, `nat_guard_eq, `string_queries_eq, `resolving_reading_eq].map
      (`Ix.Cert.PrefixConstType ++ ·)) ++
      #[`Ix.Cert.ReferenceFronts.DefinitionFrontAt.stored_head_slots,
        `Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_const_ty])

/-! ## Capability and successor rows at the same final interpretation

Positive family guards and resolving headers transport both capability
halves. The successor argument uses only the supplied core; the unit law
gains no eta-family premise and no prefix interpretation is chosen. -/

/-- info: [cert-audit] fixed interpretation capability and successor rows: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed interpretation capability and successor rows"
    ((#[`eta_family_preserved, `capabilities_preserved, `nat_succ_row].map
      (`Ix.Cert.PrefixCapabilities ++ ·)) ++
      #[`Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_caps_succ])

/-! ## Every stored recursor's exact header, RHS and open-pin readings

Actual prefix WF supplies resolution, including getD defaults and the
sort-zero reverse openers. Reading equations need no model or grading. -/

/-- info: [cert-audit] fixed interpretation stored recursor readings: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed interpretation stored recursor readings"
    (#[`openRev_resolves, `stored_rule_resolves, `stored_rule_readings].map
      (`Ix.Cert.PrefixRecRules ++ ·))

/-! ## Universal recursor rules at the supplied final interpretation

The full law retains RHS grading, outer guarded pin grading, contravariant
nested comparisons, both type readings and the fired equality/output grade. -/

/-- info: [cert-audit] universal fixed interpretation recursor rules: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "universal fixed interpretation recursor rules"
    #[`Ix.Cert.PrefixRecRules.rec_rules_preserved,
      `Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_rec_rules]

/-! ## Actual prefix tower heads and all body/header readings

Both positive head witnesses come from prefix projection discipline;
the table and three exact depth-zero readings transport at fixed acval. -/

/-- info: [cert-audit] fixed interpretation stored tower readings: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed interpretation stored tower readings"
    (#[`stored_tower_heads, `stored_tower_readings].map
      (`Ix.Cert.PrefixTowers ++ ·))

/-! ## Universal tower laws at the supplied final interpretation

Produced prefix hits identify the final law's witnesses. The exact typing,
iota, eta and Prop-guard clauses use the same readings and final acval. -/

/-- info: [cert-audit] universal fixed interpretation tower laws: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "universal fixed interpretation tower laws"
    #[`Ix.Cert.PrefixTowers.tower_ok_preserved,
      `Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_tower_ok]

/-! ## Actual Nat-operation guards and both fixed-acval readings

Each creating POST guard survives its actual suffix. Original raw/result
facts derive both readings, with no model or backwards support premise. -/

/-- info: [cert-audit] actual prefix Nat-operation readings: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual prefix Nat-operation readings"
    ((#[`guard_preserved, `reference_nat_op_guards, `binary_mem, `literal_resolves,
      `raw_literal_resolves, `result_resolves, `guarded_nat_op_readings].map
      (`Ix.Cert.PrefixNatOps ++ ·)) ++
      #[`Ix.Cert.ReferenceFronts.DefinitionFrontAt.prefix_nat_op_guards])

/-! ## All rule inputs at the supplied final interpretation

The original NatOpRow transfers through both actual readings. Nine proved
fields retain EqLaw, exact valuations and the unchanged target package. -/

/-- info: [cert-audit] actual fixed interpretation rule inputs: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual fixed interpretation rule inputs"
    #[`Ix.Cert.PrefixNatOps.nat_op_preserved,
      `Ix.Cert.ReferenceFronts.DefinitionFrontAt.final_prefix_rules_inputs]

/-! ## Actual checked values and root markers from rule inputs

The fixed carrier and nine proved rows supply inference/Denotes and checked
marker equality without a prefix StrongModel or an inner context witness. -/

/-- info: [cert-audit] fixed interpretation checked value adapters: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "fixed interpretation checked value adapters"
    (#[`frame_context, `infer_package, `reading_denotes, `defeq_readings,
      `lambda_markers_eq_of_fronts, `markers_of_fronts].map (`Ix.Cert.RuleInputValues ++ ·))

/-! ## Actual indexed O6 values in the supplied final model

The real target front and one same-prefix/header baseline front derive the
telescope conversion; both checked subjects denote the final constant. -/

/-- info: [cert-audit] indexed O6 final interpretation values: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "indexed O6 final interpretation values"
    #[`Ix.CompileCert.O6PrefixValues.o6_rec_under_telescope_final_values]

/-! ## The actual engine and passConfig branch origin

First-success misses, the literal recursive fuel and all reports survive;
the hook derives permission and its actual driver environment. -/

/-- info: [cert-audit] actual optimization dispatch origins: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual optimization dispatch origins"
    (#[`engineN_origin, `engineN_success_origin, `engine_origin, `passConfig_origin].map
      (`Ix.CompileCert.OptDispatchOrigin ++ ·))

/-! ## Actual outer-map/view and O6 call provenance

The real exact-key fold supplies its view. Recovered O6 dispatch retains
both rec/recOn and the actual guards, without inventing image or memo origin. -/

/-- info: [cert-audit] actual O6 driver call origins: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual O6 driver call origins"
    (#[`optBlocks_origin, `o6_lookup_origin, `driver_o6_origin, `passConfig_with_o6_origin].map
      (`Ix.CompileCert.OptDispatchOrigin ++ ·))

/-! ## Actual shape insertion origins under exact name keys

Every positive hit retains its real source/image/recognizer calls through
skipped attempts and overwrite, with exact query/name/level identification. -/

/-- info: [cert-audit] actual optimizer shape insertion origins: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual optimizer shape insertion origins"
    (#[`Origins.insert, `optBlockOf_origins, `optBlockOf_shape_origin].map
      (`Ix.CompileCert.OptShapeOrigin ++ ·))

/-! ## The actual hook's common O6 source/image/shape witnesses

The repaired shape producer enriches the SAME view/query/shape tuple;
all engine branches, reports and the rec/recOn distinction are retained. -/

/-- info: [cert-audit] actual O6 image call origins: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual O6 image call origins"
    (#[`o6_calls_images, `O6Images.calls, `passConfig_with_images].map
      (`Ix.CompileCert.OptShapeOrigin ++ ·))

/-! ## Actual view queries and fresh publication entries

The real empty-start loop supplies query/owner and exact cached-or-built
origins. The actual absence guard forces a current build for every new entry. -/

/-- info: [cert-audit] actual view query and publication origins: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual view query and publication origins"
    (#[`viewOf_origin, `Origins.mono, `Origins.insert, `viewsOf_origins, `viewsOf_origin,
      `newMemoViews_entries, `newMemoViews_built].map (`Ix.CompileCert.ViewPublicationOrigin ++ ·))

/-! ## Actual view publication and transition values

All three real producers supply their own build snapshots. Merges retain
exact values; post-failure queries retain actual head/owner witnesses. -/

/-- info: [cert-audit] actual view publication transitions: 11 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "cert-audit") "actual view publication transitions"
    (#[`memoMerge_keeps, `memoMerge_origin, `memoMerge_views_origin, `mergeCompiledBlock_views,
      `failAuxPromotion_views, `after_failure_query_origin, `PublicationOrigin.entry_built,
      `rewriteCliqueCanon_origin, `prepareBlock_origin, `compileImageBlock_origin,
      `merge_publication_origin].map (`Ix.CompileCert.ViewPublicationOrigin ++ ·))
