import Ix.Cert.Statement
import Ix.Cert.Closure
import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.ReadingAudit
import Ix.Cert.Canon

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
        match ci with
        | Ix.ConstantInfo.inductInfo v =>
          v.all.contains b = true ∨
            ∃ first rv,
              v.all[0]? = some first ∧ env.consts.get? b = some (Ix.ConstantInfo.recInfo rv) ∧ rv.all[0]? = some first
        | Ix.ConstantInfo.recInfo rv => rv.all.contains b = true
        | x => False) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.DependsOn

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
  Ix.Cert.IsClosure env roots sub ∧ Ix.LeanIngress.checkSource sub (condense sub) = Except.ok envS -/
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
  Std.HashSet.toArray (Ix.Cert.refsOf ci) ++
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

/-- info: inductive Ix.Cert.ErrorKind : Type
number of parameters: 0
constructors:
Ix.Cert.ErrorKind.notImplemented : Ix.Cert.ErrorKind
Ix.Cert.ErrorKind.invalid : Ix.Cert.ErrorKind
Ix.Cert.ErrorKind.internal : Ix.Cert.ErrorKind -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ErrorKind

/-- info: def Ix.Cert.ErrorKind.of : Ix.Kernel.CheckError → Ix.Cert.ErrorKind :=
fun x =>
  match x with
  | Ix.Kernel.CheckError.notImplemented what => Ix.Cert.ErrorKind.notImplemented
  | Ix.Kernel.CheckError.invalid msg => Ix.Cert.ErrorKind.invalid
  | Ix.Kernel.CheckError.internal msg => Ix.Cert.ErrorKind.internal -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.ErrorKind.of

/-- info: def Ix.Cert.verdict : {md : Ix.Kernel.Mode} →
  Except (Ix.Kernel.CheckError × Nat) (Ix.Kernel.Env md) → Except (Ix.Cert.ErrorKind × Nat) (Ix.Kernel.Env md) :=
fun {md} x =>
  match x with
  | Except.ok e => Except.ok e
  | Except.error (e, i) => Except.error (Ix.Cert.ErrorKind.of e, i) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.verdict

/-- info: def Ix.Cert.RenamingLemma : Prop :=
∀ (f : Ix.Kernel.Mode.source.Id → Ix.Kernel.Mode.anon.Id) (ev : Ix.Kernel.Evidences Ix.Kernel.Mode.source)
  (ds : Array (Ix.Kernel.Declaration Ix.Kernel.Mode.source)),
  Ix.Cert.RenamingHyp f ev ds →
    Ix.Cert.verdict
        (Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified (Ix.Cert.Rename.evidences (Ix.Kernel.Key.map f) ev)
          (Array.map (Ix.Cert.Rename.declaration (Ix.Kernel.Key.map f)) ds)) =
      Except.map (Ix.Cert.Rename.env (Ix.Kernel.Key.map f))
        (Ix.Cert.verdict (Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified ev ds)) -/
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

/-- info: def Ix.Cert.compileReport : Ix.Environment → Except String (Ixon.Env × Ix.Cert.Failures) :=
fun env =>
  have env := { consts := env.consts };
  have split := Ix.Cert.groundSplit env;
  do
  let __x ← Ix.CompileM.compileEnvAux env (Ix.CondenseM.run split.fst)
  match __x with
    | (ixe, fst, cenv) =>
      have ungrounded :=
        Std.HashMap.fold (fun m n e => m.insert n (e.refusal (Std.HashMap.contains split.snd))) ∅ split.snd;
      pure (ixe, { ungrounded := ungrounded, blocks := cenv.ungrounded }) -/
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
`CanonMCorrect` and `CanonChunkCorrect` (C1) are **stated, not proved**:
they are unprovable for today's `Ix.CanonM`, whose cache hits are not
confirmed and whose `canonSyntax` is `partial` (CQ2.26). The universe bridge
from Lean is proved (`universeBridge`, under `HashEqAgrees`). The proved
theorems are at the three standard axioms or fewer. -/

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

/-- info: inductive Ix.Cert.Canon.Reachable : Ix.CanonM.CanonState → Prop
number of parameters: 0
constructors:
Ix.Cert.Canon.Reachable.empty : Ix.Cert.Canon.Reachable { }
Ix.Cert.Canon.Reachable.name : ∀ {s : Ix.CanonM.CanonState} (n : Lean.Name),
  Ix.Cert.Canon.Reachable s → Ix.Cert.Canon.Reachable (StateT.run (Ix.CanonM.canonName n) s).run.snd
Ix.Cert.Canon.Reachable.level : ∀ {s : Ix.CanonM.CanonState} (l : Lean.Level),
  Ix.Cert.Canon.Reachable s → Ix.Cert.Canon.Reachable (StateT.run (Ix.CanonM.canonLevel l) s).run.snd
Ix.Cert.Canon.Reachable.expr : ∀ {s : Ix.CanonM.CanonState} (e : Lean.Expr),
  Ix.Cert.Canon.Reachable s → Ix.Cert.Canon.Reachable (StateT.run (Ix.CanonM.canonExpr e) s).run.snd
Ix.Cert.Canon.Reachable.const : ∀ {s : Ix.CanonM.CanonState} (c : Lean.ConstantInfo),
  Ix.Cert.Canon.Reachable s → Ix.Cert.Canon.Reachable (StateT.run (Ix.CanonM.canonConst c) s).run.snd -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.Reachable

/-- info: def Ix.Cert.Canon.CanonMCorrect : Prop :=
∀ (s : Ix.CanonM.CanonState),
  Ix.Cert.Canon.Reachable s →
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

/-- info: def Ix.Cert.Canon.HashEqAgrees : Array Lean.Name → Prop :=
fun names =>
  ∀ (m : Lean.Name), m ∈ names → ∀ (n : Lean.Name), (Ix.Cert.Canon.nameS m == Ix.Cert.Canon.nameS n) = (m == n) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Canon.HashEqAgrees

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
    | Ix.Level.param n hash => Option.map (fun i => Ixon.Univ.var i.toUInt64) (List.idxOf? n ctx)
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
    Ix.Cert.Canon.HashEqAgrees ps →
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

/-- info: Ix.Cert.Canon.ingressExpr_canonExpr (hc : Ix.Cert.Canon.CanonMCorrect) {s : Ix.CanonM.CanonState}
  (hs : Ix.Cert.Canon.Reachable s) (σ : Ix.Name → Ix.Kernel.LevelParam) (e : Lean.Expr) :
  Ix.LeanIngress.ingressExpr σ (StateT.run (Ix.CanonM.canonExpr e) s).run.fst =
    Ix.Cert.Canon.leanExpr (σ ∘ Ix.Cert.Canon.nameS) e -/
#guard_msgs (whitespace := lax) in
#check Ix.Cert.Canon.ingressExpr_canonExpr

/-- info: Ix.Cert.Canon.numbering_nameS (names : Array Lean.Name) (large : Bool) (h : Ix.Cert.Canon.HashEqAgrees names)
  (n : Lean.Name) :
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
