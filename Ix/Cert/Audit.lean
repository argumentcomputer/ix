import Ix.Cert.Statement

/-! # The certification statements, frozen

`#print` freezes every statement (`def … : Prop`) and every definition a
statement reads; `#check` freezes the proved theorems; `#print axioms`
freezes their axioms, which are the three standard ones. A change to any of
them fails the build.

The compiler's own axioms are frozen too. `Ix.Cert.compile` reaches one
`native_decide` axiom, the length bound of the Rust BLAKE3 wrapper's `hash`
(through `Address.blake3`). Every other hashing constructor it reaches
(`Ix.Name`, `Ix.Level`, `Ix.Expr`, `Ix.Tc`) finalizes through
`Address.ofHasher`, which passes that bound explicitly. `Ix.Cert.blocksOf`
reaches only the three standard ones: its condensation is total
(`Ix.CompileCert.Canon.condensation_isSome`, frozen with it) and reads no
`Inhabited Ix.Name` default. Every statement about `compile` inherits the
remaining axiom; the proved theorems still quantify over the grouping
function instead of naming `blocksOf`. -/

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
  Ix.Environment → List Ix.Name → Ix.Environment → Ix.Kernel.Env → Prop :=
fun condense env roots sub envS =>
  Ix.Cert.IsClosure env roots sub ∧ Ix.LeanIngress.checkSource sub (condense sub) = Except.ok envS -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceAccepts

/-- info: def Ix.Cert.recursorsByBlock : Ix.Environment → Ix.Map Ix.Name (Array Ix.Name) :=
fun env =>
  Std.HashMap.fold
    (fun m n ci =>
      match ci with
      | Ix.ConstantInfo.recInfo rv =>
        match rv.all[0]? with
        | some first => Std.HashMap.insert m first ((Std.HashMap.getD m first #[]).push n)
        | none => m
      | x => m)
    ∅ env.consts -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.recursorsByBlock

/-- info: def Ix.Cert.dependencies : Ix.Map Ix.Name (Array Ix.Name) → Ix.ConstantInfo → Array Ix.Name :=
fun recursors ci =>
  Std.HashSet.toArray (Ix.Cert.refsOf ci) ++
    match ci with
    | Ix.ConstantInfo.inductInfo v =>
      v.all ++
        match v.all[0]? with
        | some first => Std.HashMap.getD recursors first #[]
        | none => #[]
    | Ix.ConstantInfo.recInfo rv => rv.all
    | x => #[] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.dependencies

/-- info: def Ix.Cert.closure : Ix.Environment → List Ix.Name → Ix.Environment :=
fun env roots =>
  (have recursors := Ix.Cert.recursorsByBlock env;
    have seen := ∅;
    have todo := roots.toArray;
    do
    let __s ←
      forIn { } (seen, todo) fun x __s =>
          have seen := __s.fst;
          let todo := __s.snd;
          if h : todo.size > 0 then
            have n := todo[todo.size - 1];
            have todo := todo.pop;
            if Std.HashSet.contains seen n = true then pure (ForInStep.yield (seen, todo))
            else
              match env.consts.get? n with
              | none => pure (ForInStep.yield (seen, todo))
              | some ci =>
                have seen := Std.HashSet.insert seen n;
                have todo := todo ++ Ix.Cert.dependencies recursors ci;
                pure (ForInStep.yield (seen, todo))
          else pure (ForInStep.done (seen, todo))
    have seen : Ix.Set Ix.Name := __s.fst
    pure { consts := Std.HashMap.filter (fun n x => Std.HashSet.contains seen n) env.consts }).run -/
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
  Ix.Kernel.Admission.Limits → Ixon.Env → (Address → Prop) → List Address → Ix.Kernel.Env → Prop :=
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

/-- info: structure Ix.Cert.ValueModel.{w} (V : Type w) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env) : Type w
number of parameters: 3
parents:
  Ix.Cert.ValueModel.toModel : Ix.Kernel.Model V env
fields:
  Ix.Kernel.Model.cval : Ix.Kernel.Key → (Ix.Kernel.LevelParam → Nat) → V
  Ix.Kernel.Model.mem : ∀ (c : Ix.Kernel.ConstantInfo),
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
  Ix.Cert.ValueModel.defn_value : ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr)
      (hint : Ix.Kernel.ReducibilityHint),
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
          Ix.Kernel.Denotes self.cval env φ ρ value (self.cval cv.name φ)
constructor:
  Ix.Cert.ValueModel.mk.{w} {V : Type w} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env} (toModel : Ix.Kernel.Model V env)
    (defn_value :
      ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr) (hint : Ix.Kernel.ReducibilityHint),
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
/-- info: def Ix.Cert.publishedAddress : Ixon.Env → Ix.Kernel.Key → Option Address :=
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
  Ix.Kernel.Admission.Limits → Ixon.Env → List Address → Option Ix.Kernel.Reader.Ctx :=
fun binding limits ixe order => do
  let t ← (Ix.Kernel.Admission.admitBinding Address.blake3Pure binding).toOption
  let pre ← (Ix.Kernel.Reader.preludeFor t).toOption
  let constants ← (Ix.Kernel.Admission.decodeRecords limits (Ix.Cert.recordsOf ixe order)).toOption
  pure (Ix.Kernel.Admission.streamContext t pre constants (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe)) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.admissionContext

/-- info: def Ix.Cert.reading : Ixon.Env → Ix.Kernel.Reader.Ctx → Ix.Kernel.ConstantInfo → Option Ix.Kernel.Expr :=
fun ixe cx c => do
  let a ← Ix.Cert.publishedAddress ixe c.name
  let r ← Ix.Kernel.Reader.resolve cx.store a
  pure (Ix.Kernel.Expr.const (cx.nameOf r) (List.map Ix.Kernel.Level.param c.toConstantVal.levelParams)) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.reading

/-- info: def Ix.Cert.Commutes.{w} : (Ix.Kernel.ConstantInfo → Option Ix.Kernel.Expr) → Ix.Kernel.Env → Ix.Kernel.Env → Prop :=
fun τ envS envA =>
  ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V] (M : Ix.Cert.ValueModel V envA),
    ∃ N,
      ∀ (c : Ix.Kernel.ConstantInfo),
        c ∈ envS.consts →
          ∀ (t : Ix.Kernel.Expr),
            τ c = some t →
              ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
                Ix.Kernel.Denotes M.cval envA φ ρ t (N.cval c.name φ) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Commutes

/-- info: def Ix.Cert.HashAgreement : Prop :=
∀ (bytes : ByteArray), Address.blake3 bytes = Address.blake3Pure bytes -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.HashAgreement

/-- info: def Ix.Cert.CompileCorrect.{w} : Prop :=
Ix.Cert.HashAgreement →
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env) (ixe : Ixon.Env),
    Ix.Cert.SourceAccepts Ix.Cert.blocksOf env roots sub envS →
      Ix.Cert.compile env = Except.ok ixe →
        Ix.Cert.Published ixe sub →
          ∃ binding,
            Ix.Kernel.Admission.defaultBinding = Except.ok binding ∧
              ∃ limits order envA cx,
                Ix.Cert.IxonAccepts binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
                  Ix.Cert.admissionContext binding limits ixe order = some cx ∧
                    Ix.Cert.Commutes (Ix.Cert.reading ixe cx) envS envA -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.CompileCorrect

/-- info: def Ix.Cert.SourceConsistent.{w} : Prop :=
∀ (condense : Ix.Environment → Ix.CondensedBlocks) (V : Type w) [Ix.Kernel.SetTheory V] (env : Ix.Environment)
  (roots : List Ix.Name) (sub : Ix.Environment) (envS : Ix.Kernel.Env),
  Ix.Cert.SourceAccepts condense env roots sub envS →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ envS.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceConsistent

/-- info: def Ix.Cert.IxonConsistent.{w} : Prop :=
∀ (V : Type w) [Ix.Kernel.SetTheory V] (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits)
  (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) (envA : Ix.Kernel.Env),
  Ix.Cert.IxonAccepts binding limits ixe S order envA →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ envA.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonConsistent

/-- info: def Ix.Cert.IxonAuthentic : Prop :=
∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env) (S : Address → Prop)
  (order : List Address) (envA : Ix.Kernel.Env),
  Ix.Cert.IxonAccepts binding limits ixe S order envA →
    (∀ (a : Address),
        a ∈ order → ∀ (lc : Ixon.LazyConstant), ixe.consts.get? a = some lc → a = Address.blake3Pure lc.rawBytes) ∧
      (∀ (b : Address × ByteArray), b ∈ Ix.Cert.blobsOf ixe order → b.fst = Address.blake3Pure b.snd) ∧
        Address.blake3Pure binding.bytes = binding.address -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.IxonAuthentic

/-- info: def Ix.Cert.SourceValueSound.{w} : Prop :=
∀ (condense : Ix.Environment → Ix.CondensedBlocks) (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment)
  (envS : Ix.Kernel.Env),
  Ix.Cert.SourceAccepts condense env roots sub envS →
    ∀ (V : Type w) [inst : Ix.Kernel.SetTheory V], Nonempty (Ix.Cert.ValueModel V envS) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.SourceValueSound

/-- info: def Ix.Cert.IxonValueSound.{w} : Prop :=
∀ (binding : Ix.Kernel.Admission.Binding) (limits : Ix.Kernel.Admission.Limits) (ixe : Ixon.Env) (S : Address → Prop)
  (order : List Address) (envA : Ix.Kernel.Env),
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
/-- info: Ix.Cert.Rename.expr.eq_def : ∀ (σ : Ix.Kernel.Key → Ix.Kernel.Key) (x : Ix.Kernel.Expr),
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

/-- info: def Ix.Cert.Rename.constantVal : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.ConstantVal → Ix.Kernel.ConstantVal :=
fun σ cv => { name := σ cv.name, levelParams := cv.levelParams, type := Ix.Cert.Rename.expr σ cv.type } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.constantVal

/-- info: def Ix.Cert.Rename.recRule : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.RecRule → Ix.Kernel.RecRule :=
fun σ r =>
  { ctor := σ r.ctor, nfields := r.nfields, ctorParams := r.ctorParams,
    fire :=
      match r.fire with
      | Ix.Kernel.RecRuleFire.nested lvls pins =>
        Ix.Kernel.RecRuleFire.nested lvls (List.map (Ix.Cert.Rename.expr σ) pins)
      | f => f,
    rhs := Ix.Cert.Rename.expr σ r.rhs, k := r.k, eta := r.eta, paramsBlind := r.paramsBlind } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.recRule

/-- info: def Ix.Cert.Rename.constantInfo : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.ConstantInfo → Ix.Kernel.ConstantInfo :=
fun σ x =>
  match x with
  | Ix.Kernel.ConstantInfo.axiomInfo v => Ix.Kernel.ConstantInfo.axiomInfo (Ix.Cert.Rename.constantVal σ v)
  | Ix.Kernel.ConstantInfo.defnInfo v e h =>
    Ix.Kernel.ConstantInfo.defnInfo (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e) h
  | Ix.Kernel.ConstantInfo.thmInfo v e =>
    Ix.Kernel.ConstantInfo.thmInfo (Ix.Cert.Rename.constantVal σ v) (Ix.Cert.Rename.expr σ e)
  | Ix.Kernel.ConstantInfo.indInfo v caps =>
    Ix.Kernel.ConstantInfo.indInfo (Ix.Cert.Rename.constantVal σ v)
      { eta := caps.eta, etaCtor := Option.map σ caps.etaCtor, etaParams := caps.etaParams, etaFields := caps.etaFields,
        unitlike := caps.unitlike, unitParams := caps.unitParams, ruleK := caps.ruleK, sortZ := caps.sortZ }
  | Ix.Kernel.ConstantInfo.ctorInfo v nP nF => Ix.Kernel.ConstantInfo.ctorInfo (Ix.Cert.Rename.constantVal σ v) nP nF
  | Ix.Kernel.ConstantInfo.recInfo v major pre rules =>
    Ix.Kernel.ConstantInfo.recInfo (Ix.Cert.Rename.constantVal σ v) major pre
      (List.map (Ix.Cert.Rename.recRule σ) rules)
  | Ix.Kernel.ConstantInfo.projInfo tbl =>
    Ix.Kernel.ConstantInfo.projInfo
      { structName := σ tbl.structName, levelParams := tbl.levelParams, numParams := tbl.numParams, ctor := σ tbl.ctor,
        numFields := tbl.numFields, structSort := tbl.structSort,
        bodies := Array.map (Ix.Cert.Rename.expr σ) tbl.bodies, guards := tbl.guards, off := tbl.off } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.constantInfo

/-- info: def Ix.Cert.Rename.declaration : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.Declaration → Ix.Kernel.Declaration :=
fun σ x =>
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

/-- info: def Ix.Cert.Rename.evidences : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.Evidences → Ix.Kernel.Evidences :=
fun σ ev =>
  List.map
    (fun x =>
      match x with
      | (r, es) => (r, List.map (Ix.Cert.Rename.evidence σ) es))
    ev -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.evidences

/-- info: def Ix.Cert.Rename.evidence : (Ix.Kernel.Key → Ix.Kernel.Key) →
  Ix.Kernel.Evidence (Ix.Kernel.Key × Ix.Kernel.Expr) → Ix.Kernel.Evidence (Ix.Kernel.Key × Ix.Kernel.Expr) :=
fun σ x =>
  match x with
  | Ix.Kernel.Evidence.defeq => Ix.Kernel.Evidence.defeq
  | Ix.Kernel.Evidence.proof (k, v) => Ix.Kernel.Evidence.proof (σ k, Ix.Cert.Rename.expr σ v) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.evidence

/-- info: def Ix.Cert.Rename.env : (Ix.Kernel.Key → Ix.Kernel.Key) → Ix.Kernel.Env → Ix.Kernel.Env :=
fun σ e => { consts := List.map (Ix.Cert.Rename.constantInfo σ) e.consts } -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Rename.env

/-- info: Ix.Cert.Keys.expr.eq_def : ∀ (x : Ix.Kernel.Expr),
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

/-- info: def Ix.Cert.Keys.constantVal : Ix.Kernel.ConstantVal → List Ix.Kernel.Key :=
fun cv => cv.name :: Ix.Cert.Keys.expr cv.type -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.constantVal

/-- info: def Ix.Cert.Keys.recRule : Ix.Kernel.RecRule → List Ix.Kernel.Key :=
fun r =>
  r.ctor :: Ix.Cert.Keys.expr r.rhs ++
    match r.fire with
    | Ix.Kernel.RecRuleFire.nested lvls pins => List.flatMap Ix.Cert.Keys.expr pins
    | x => [] -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Keys.recRule

/-- info: def Ix.Cert.Keys.constantInfo : Ix.Kernel.ConstantInfo → List Ix.Kernel.Key :=
fun x =>
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

/-- info: def Ix.Cert.Keys.declaration : Ix.Kernel.Declaration → List Ix.Kernel.Key :=
fun x =>
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

/-- info: def Ix.Cert.Keys.evidences : Ix.Kernel.Evidences → List Ix.Kernel.Key :=
fun ev =>
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

/-- info: def Ix.Cert.InputKey : Ix.Kernel.Evidences → Array Ix.Kernel.Declaration → Ix.Kernel.Key → Prop :=
fun ev ds n => (∃ d, d ∈ ds ∧ n ∈ Ix.Cert.Keys.declaration d) ∨ n ∈ Ix.Cert.Keys.evidences ev -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.InputKey

/-- info: def Ix.Cert.Pinned : Ix.Kernel.Key → Prop :=
fun n => ∃ r, Ix.Kernel.roleKey r = n -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Pinned

/-- info: inductive Ix.Cert.DerivedFrom : Ix.Kernel.Key → Ix.Kernel.Key → Prop
number of parameters: 1
constructors:
Ix.Cert.DerivedFrom.aux : ∀ {k : Ix.Kernel.Key} (d : Ix.Kernel.Derived), Ix.Cert.DerivedFrom k (k.aux d)
Ix.Cert.DerivedFrom.ext : ∀ {k n : Ix.Kernel.Key} (d : Ix.Kernel.Derived),
  Ix.Cert.DerivedFrom k n → Ix.Cert.DerivedFrom k (n.aux d) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.DerivedFrom

/-- info: def Ix.Cert.Built : Ix.Kernel.Evidences → Array Ix.Kernel.Declaration → Ix.Kernel.Key → Prop :=
fun ev ds n => ∃ k, (Ix.Cert.InputKey ev ds k ∨ Ix.Cert.Pinned k) ∧ (n = k ∨ Ix.Cert.DerivedFrom k n) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.Built

/-- info: structure Ix.Cert.RenamingHyp (σ : Ix.Kernel.Key → Ix.Kernel.Key) (ev : Ix.Kernel.Evidences)
  (ds : Array Ix.Kernel.Declaration) : Prop
number of parameters: 3
fields:
  Ix.Cert.RenamingHyp.pinned : ∀ (n : Ix.Kernel.Key), Ix.Cert.Pinned n → σ n = n
  Ix.Cert.RenamingHyp.fresh : ∀ (k : Ix.Kernel.Key),
      Ix.Cert.InputKey ev ds k → ¬Ix.Cert.Pinned k → ¬Ix.Cert.Pinned (σ k)
  Ix.Cert.RenamingHyp.aux : ∀ (k : Ix.Kernel.Key) (d : Ix.Kernel.Derived),
      ¬Ix.Cert.InputKey ev ds (k.aux d) → σ (k.aux d) = (σ k).aux d
  Ix.Cert.RenamingHyp.shapes : ∀ (k : Ix.Kernel.Key),
      Ix.Cert.InputKey ev ds k → (σ k).isProjFnShape = k.isProjFnShape ∧ (σ k).isModelSuffix = k.isModelSuffix
  Ix.Cert.RenamingHyp.injective : ∀ (a b : Ix.Kernel.Key),
      Ix.Cert.Built ev ds a → Ix.Cert.Built ev ds b → σ a = σ b → a = b
constructor:
  Ix.Cert.RenamingHyp.mk {σ : Ix.Kernel.Key → Ix.Kernel.Key} {ev : Ix.Kernel.Evidences}
    {ds : Array Ix.Kernel.Declaration} (pinned : ∀ (n : Ix.Kernel.Key), Ix.Cert.Pinned n → σ n = n)
    (fresh : ∀ (k : Ix.Kernel.Key), Ix.Cert.InputKey ev ds k → ¬Ix.Cert.Pinned k → ¬Ix.Cert.Pinned (σ k))
    (aux : ∀ (k : Ix.Kernel.Key) (d : Ix.Kernel.Derived), ¬Ix.Cert.InputKey ev ds (k.aux d) → σ (k.aux d) = (σ k).aux d)
    (shapes :
      ∀ (k : Ix.Kernel.Key),
        Ix.Cert.InputKey ev ds k → (σ k).isProjFnShape = k.isProjFnShape ∧ (σ k).isModelSuffix = k.isModelSuffix)
    (injective : ∀ (a b : Ix.Kernel.Key), Ix.Cert.Built ev ds a → Ix.Cert.Built ev ds b → σ a = σ b → a = b) :
    Ix.Cert.RenamingHyp σ ev ds -/
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

/-- info: def Ix.Cert.verdict : Except (Ix.Kernel.CheckError × Nat) Ix.Kernel.Env →
  Except (Ix.Cert.ErrorKind × Nat) Ix.Kernel.Env :=
fun x =>
  match x with
  | Except.ok e => Except.ok e
  | Except.error (e, i) => Except.error (Ix.Cert.ErrorKind.of e, i) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.verdict

/-- info: def Ix.Cert.RenamingLemma : Prop :=
∀ (σ : Ix.Kernel.Key → Ix.Kernel.Key) (ev : Ix.Kernel.Evidences) (ds : Array Ix.Kernel.Declaration),
  Ix.Cert.RenamingHyp σ ev ds →
    Ix.Cert.verdict
        (Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified (Ix.Cert.Rename.evidences σ ev)
          (Array.map (Ix.Cert.Rename.declaration σ) ds)) =
      Except.map (Ix.Cert.Rename.env σ)
        (Ix.Cert.verdict (Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified ev ds)) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.RenamingLemma

/-- info: def Ix.Cert.groundedRefs : Ix.Environment → Ix.Map Ix.Name (Ix.Set Ix.Name) :=
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
  if Std.HashMap.isEmpty ungrounded = true then outRefs
  else
    Std.HashMap.fold
      (fun m n refs =>
        if Std.HashMap.contains ungrounded n = true then m
        else
          Std.HashMap.insert m n
            (Std.HashSet.fold
              (fun s r => if Std.HashMap.contains ungrounded r = true then s else Std.HashSet.insert s r) ∅ refs))
      ∅ outRefs -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.groundedRefs

/-- info: def Ix.Cert.blocksOf : Ix.Environment → Ix.CondensedBlocks :=
fun env => Ix.CondenseM.run (Ix.Cert.groundedRefs env) -/
#guard_msgs (whitespace := lax) in
#print Ix.Cert.blocksOf

/-- info: def Ix.Cert.compile : Ix.Environment → Except String Ixon.Env :=
fun env =>
  have env := { consts := env.consts };
  do
  let __x ← Ix.CompileM.compileEnvAux env (Ix.Cert.blocksOf env)
  match __x with
    | (ixe, fst, snd) => pure ixe -/
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

/-- info: @Ix.Cert.Commutes.alias : ∀ {τ : Ix.Kernel.ConstantInfo → Option Ix.Kernel.Expr} {envS envA : Ix.Kernel.Env},
  Ix.Cert.Commutes τ envS envA →
    ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] (M : Ix.Cert.ValueModel V envA),
      ∃ N,
        (∀ (c : Ix.Kernel.ConstantInfo),
            c ∈ envS.consts →
              ∀ (t : Ix.Kernel.Expr),
                τ c = some t →
                  ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
                    Ix.Kernel.Denotes M.cval envA φ ρ t (N.cval c.name φ)) ∧
          ∀ (c₁ : Ix.Kernel.ConstantInfo),
            c₁ ∈ envS.consts →
              ∀ (c₂ : Ix.Kernel.ConstantInfo),
                c₂ ∈ envS.consts →
                  ∀ (t : Ix.Kernel.Expr),
                    τ c₁ = some t →
                      τ c₂ = some t → ∀ (φ : Ix.Kernel.LevelParam → Nat), N.cval c₁.name φ = N.cval c₂.name φ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Commutes.alias

/-- info: Ix.Cert.reservedBasisNames_pinned : ∀ (n : Ix.Kernel.Key), n ∈ Ix.Kernel.reservedBasisNames → Ix.Cert.Pinned n -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.reservedBasisNames_pinned

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

/-- info: 'Ix.Cert.reservedBasisNames_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.reservedBasisNames_pinned

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

/-- info: 'Ix.Cert.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.compile

/-- info: 'Ix.Cert.CompileCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.CompileCorrect
