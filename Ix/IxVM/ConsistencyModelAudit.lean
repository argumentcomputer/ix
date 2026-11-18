import IxC.Kernel.Denotes
import IxC.Kernel.Audit.Axioms

/-! # The model interface of the consistency statement, frozen

The composed consistency statement (`IxVM.Consistency.CircuitComposed`, frozen in
`Ix.IxVM.ConsistencyAudit`) concludes that an environment has a model in every set theory:
`∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W env)`. What that says is
fixed by the class `Ix.Kernel.SetTheory`, the structure `Ix.Kernel.Model` and what the two
read. `#print` freezes them here: `SetTheory` with its axioms, `Model` with its fields, and
every definition of `IxC.Kernel.Denotes` and `IxC.Kernel.SetTheory.Core` that the statement
reads through them: the denotation relation `Denotes`, and the model's laws `IotaLaw` (with
`IotaRule`), `UnitLikeLaw`, `ProjLaw`, `ProjTypeLaw`, `EtaFnLaw`, `NatLitLaw`, `NatAddLaw` and
`GradedLaw`, with their auxiliaries. The four structurally recursive functions among them are
frozen by their unfolding equations (`#check`). `#guard_kernel_axioms` freezes the axioms the
two reach: none for `SetTheory`; `propext`, `Classical.choice` and `Quot.sound` for `Model`. A
change to any of them fails the build, so what a model is cannot drift silently. The module
is outside any namespace, so every name prints in full.

The module imports the kernel's denotation module and the axiom check only: it builds whether
or not the consistency proof, or the statement, does.

What this module does not freeze. A definition read from another module appears here by name
only: the set-theoretic operators derived from the axioms (`Ix.Kernel.SetTheory.empty`, `app`,
`univ`, `sfst`, `ssnd`, `pt`, `eqv`; `Ix.Kernel.SetModel.piR`, `lamR`), the kernel's terms and
environments (`Ix.Kernel.Expr`, `Env`, `ConstantInfo`, `Level.eval`, `Level.substFn`,
`Expr.instantiateLevelParams`, `Expr.stripPis`, `Env.findProj?`), `PropWhen.holds`, the
literal constructors (`natLitToConstructor`, `strLitToConstructor`) and the basis names
(`falseName`, `eqName`, `punitName`, `natAddName` and the others). -/

/-! ## The set theory and the model -/

/--
info: class Ix.Kernel.SetTheory.{u} (V : Type u) : Type u
number of parameters: 1
fields:
  Ix.Kernel.SetTheory.Mem : V → V → Prop
  Ix.Kernel.SetTheory.ext : ∀ {x y : V}, (∀ (z : V), Ix.Kernel.SetTheory.Mem z x ↔ Ix.Kernel.SetTheory.Mem z y) → x = y
  Ix.Kernel.SetTheory.upair : V → V → V
  Ix.Kernel.SetTheory.mem_upair : ∀ {z a b : V},
      Ix.Kernel.SetTheory.Mem z (Ix.Kernel.SetTheory.upair a b) ↔ z = a ∨ z = b
  Ix.Kernel.SetTheory.sUnion : V → V
  Ix.Kernel.SetTheory.mem_sUnion : ∀ {z x : V},
      Ix.Kernel.SetTheory.Mem z (Ix.Kernel.SetTheory.sUnion x) ↔
        ∃ y, Ix.Kernel.SetTheory.Mem y x ∧ Ix.Kernel.SetTheory.Mem z y
  Ix.Kernel.SetTheory.power : V → V
  Ix.Kernel.SetTheory.mem_power : ∀ {z x : V},
      Ix.Kernel.SetTheory.Mem z (Ix.Kernel.SetTheory.power x) ↔
        ∀ (w : V), Ix.Kernel.SetTheory.Mem w z → Ix.Kernel.SetTheory.Mem w x
  Ix.Kernel.SetTheory.regularity : ∀ (x : V),
      (∃ y, Ix.Kernel.SetTheory.Mem y x) →
        ∃ y, Ix.Kernel.SetTheory.Mem y x ∧ ¬∃ z, Ix.Kernel.SetTheory.Mem z y ∧ Ix.Kernel.SetTheory.Mem z x
  Ix.Kernel.SetTheory.image : (V → V) → V → V
  Ix.Kernel.SetTheory.mem_image : ∀ {f : V → V} {a z : V},
      Ix.Kernel.SetTheory.Mem z (Ix.Kernel.SetTheory.image f a) ↔ ∃ w, Ix.Kernel.SetTheory.Mem w a ∧ z = f w
  Ix.Kernel.SetTheory.univChain : Nat → V
  Ix.Kernel.SetTheory.univChain_mem : ∀ (n : Nat),
      Ix.Kernel.SetTheory.Mem (Ix.Kernel.SetTheory.univChain n) (Ix.Kernel.SetTheory.univChain (n + 1))
  Ix.Kernel.SetTheory.univChain_tg : ∀ (n : Nat),
      Ix.Kernel.IsTGUniverse Ix.Kernel.SetTheory.Mem (Ix.Kernel.SetTheory.univChain n)
constructor:
  Ix.Kernel.SetTheory.mk.{u} {V : Type u} (Mem : V → V → Prop)
    (ext : ∀ {x y : V}, (∀ (z : V), Mem z x ↔ Mem z y) → x = y) (upair : V → V → V)
    (mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b) (sUnion : V → V)
    (mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y) (power : V → V)
    (mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ (w : V), Mem w z → Mem w x)
    (regularity : ∀ (x : V), (∃ y, Mem y x) → ∃ y, Mem y x ∧ ¬∃ z, Mem z y ∧ Mem z x) (image : (V → V) → V → V)
    (mem_image : ∀ {f : V → V} {a z : V}, Mem z (image f a) ↔ ∃ w, Mem w a ∧ z = f w) (univChain : Nat → V)
    (univChain_mem : ∀ (n : Nat), Mem (univChain n) (univChain (n + 1)))
    (univChain_tg : ∀ (n : Nat), Ix.Kernel.IsTGUniverse Mem (univChain n)) : Ix.Kernel.SetTheory V
-/
#guard_msgs in
#print Ix.Kernel.SetTheory

/--
info: structure Ix.Kernel.Model.{w} {md : Ix.Kernel.Mode} (V : Type w) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env md) :
  Type w
number of parameters: 4
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
  Ix.Kernel.Model.punit_unit : ∀ (us vs : List Ix.Kernel.Level) (φ ψ : Ix.Kernel.LevelParam → Nat)
      (ρ ρ' : Ix.Kernel.BVarIdx → V) (P Q x y : V),
      Ix.Kernel.Denotes self.cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.punitName us) P →
        Ix.Kernel.Denotes self.cval env ψ ρ' (Ix.Kernel.Expr.const Ix.Kernel.punitName vs) Q →
          Ix.Kernel.SetTheory.Mem x P → Ix.Kernel.SetTheory.Mem y Q → x = y
  Ix.Kernel.Model.defn_value : ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md)
      (hint : Ix.Kernel.ReducibilityHint),
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
          Ix.Kernel.Denotes self.cval env φ ρ value (self.cval cv.name φ)
  Ix.Kernel.Model.iota_rule : Ix.Kernel.IotaLaw self.cval env
  Ix.Kernel.Model.unit_like : Ix.Kernel.UnitLikeLaw self.cval env
  Ix.Kernel.Model.proj_law : Ix.Kernel.ProjLaw self.cval env
  Ix.Kernel.Model.proj_type : Ix.Kernel.ProjTypeLaw self.cval env
  Ix.Kernel.Model.eta_fn : Ix.Kernel.EtaFnLaw self.cval env
  Ix.Kernel.Model.lit_ops : Ix.Kernel.NatLitLaw self.cval env
  Ix.Kernel.Model.nat_add : Ix.Kernel.NatAddLaw self.cval env
  Ix.Kernel.Model.graded : Ix.Kernel.GradedLaw self.cval env
  Ix.Kernel.Model.cval_params : ∀ (n : Ix.Kernel.Key md) (ci : Ix.Kernel.ConstantInfo md),
      env.find? n = some ci →
        ∀ (φ₁ φ₂ : Ix.Kernel.LevelParam → Nat),
          (∀ (p : Ix.Kernel.LevelParam), p ∈ ci.toConstantVal.levelParams → φ₁ p = φ₂ p) →
            self.cval n φ₁ = self.cval n φ₂
constructor:
  Ix.Kernel.Model.mk.{w} {md : Ix.Kernel.Mode} {V : Type w} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env md}
    (cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V)
    (mem :
      ∀ (c : Ix.Kernel.ConstantInfo md),
        c ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            ∃ T, Ix.Kernel.Denotes cval env φ ρ c.toConstantVal.type T ∧ Ix.Kernel.SetTheory.Mem (cval c.name φ) T)
    (false_empty :
      ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (F : V),
        Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.falseName []) F → F = Ix.Kernel.SetTheory.empty)
    (eq_equality :
      ∀ (u : Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (E A a b : V),
        Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.eqName [u]) E →
          Ix.Kernel.SetTheory.Mem A (Ix.Kernel.SetTheory.univ (Ix.Kernel.Level.eval φ u)) →
            Ix.Kernel.SetTheory.Mem a A →
              Ix.Kernel.SetTheory.Mem b A →
                Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app E A) a) b =
                  Ix.Kernel.SetTheory.eqv a b)
    (punit_unit :
      ∀ (us vs : List Ix.Kernel.Level) (φ ψ : Ix.Kernel.LevelParam → Nat) (ρ ρ' : Ix.Kernel.BVarIdx → V) (P Q x y : V),
        Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.punitName us) P →
          Ix.Kernel.Denotes cval env ψ ρ' (Ix.Kernel.Expr.const Ix.Kernel.punitName vs) Q →
            Ix.Kernel.SetTheory.Mem x P → Ix.Kernel.SetTheory.Mem y Q → x = y)
    (defn_value :
      ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes cval env φ ρ value (cval cv.name φ))
    (iota_rule : Ix.Kernel.IotaLaw cval env) (unit_like : Ix.Kernel.UnitLikeLaw cval env)
    (proj_law : Ix.Kernel.ProjLaw cval env) (proj_type : Ix.Kernel.ProjTypeLaw cval env)
    (eta_fn : Ix.Kernel.EtaFnLaw cval env) (lit_ops : Ix.Kernel.NatLitLaw cval env)
    (nat_add : Ix.Kernel.NatAddLaw cval env) (graded : Ix.Kernel.GradedLaw cval env)
    (cval_params :
      ∀ (n : Ix.Kernel.Key md) (ci : Ix.Kernel.ConstantInfo md),
        env.find? n = some ci →
          ∀ (φ₁ φ₂ : Ix.Kernel.LevelParam → Nat),
            (∀ (p : Ix.Kernel.LevelParam), p ∈ ci.toConstantVal.levelParams → φ₁ p = φ₂ p) → cval n φ₁ = cval n φ₂) :
    Ix.Kernel.Model V env
-/
#guard_msgs in
#print Ix.Kernel.Model

/-! ## What they read from `IxC.Kernel.Denotes` -/

/--
info: @[reducible] def Ix.Kernel.BVarIdx : Type :=
Nat
-/
#guard_msgs in
#print Ix.Kernel.BVarIdx

/--
info: def Ix.Kernel.push.{w} : {V : Type w} → V → (Ix.Kernel.BVarIdx → V) → Ix.Kernel.BVarIdx → V :=
fun {V} x ρ x_1 =>
  match x_1 with
  | 0 => x
  | Nat.succ i => ρ i
-/
#guard_msgs in
#print Ix.Kernel.push

/--
info: def Ix.Kernel.regime : (Ix.Kernel.LevelParam → Nat) → Ix.Kernel.PropWhen → Nat :=
fun φ pw => if Ix.Kernel.PropWhen.holds φ pw = true then 0 else 1
-/
#guard_msgs in
#print Ix.Kernel.regime

/--
info: @Ix.Kernel.field.eq_def : ∀ {V : Type u_1} [inst : Ix.Kernel.SetTheory V] (x : Nat) (x_1 : V),
  Ix.Kernel.field x x_1 =
    match x, x_1 with
    | 0, p => Ix.Kernel.SetTheory.sfst p
    | i.succ, p => Ix.Kernel.field i (Ix.Kernel.SetTheory.ssnd p)
-/
#guard_msgs in
#check @Ix.Kernel.field.eq_def

/--
info: inductive Ix.Kernel.Denotes.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} →
      (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) →
        Ix.Kernel.Env md → (Ix.Kernel.LevelParam → Nat) → (Ix.Kernel.BVarIdx → V) → Ix.Kernel.Expr md → V → Prop
number of parameters: 6
constructors:
Ix.Kernel.Denotes.bvar : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {i : Ix.Kernel.BVarIdx}, Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.bvar i) (ρ i)
Ix.Kernel.Denotes.sort : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {u : Ix.Kernel.Level},
  Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.sort u) (Ix.Kernel.SetTheory.univ (Ix.Kernel.Level.eval φ u))
Ix.Kernel.Denotes.const : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {n : Ix.Kernel.Key md} {us : List Ix.Kernel.Level} {ci : Ix.Kernel.ConstantInfo md},
  env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const n us)
        (cval n (Ix.Kernel.Level.substFn φ ci.toConstantVal.levelParams us))
Ix.Kernel.Denotes.app : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {f a : Ix.Kernel.Expr md} {F X : V},
  Ix.Kernel.Denotes cval env φ ρ f F →
    Ix.Kernel.Denotes cval env φ ρ a X → Ix.Kernel.Denotes cval env φ ρ (f.app a) (Ix.Kernel.SetTheory.app F X)
Ix.Kernel.Denotes.lam : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {ty body : Ix.Kernel.Expr md} {m : Ix.Kernel.BinderMeta} {A : V} {F : V → V},
  Ix.Kernel.Denotes cval env φ ρ ty A →
    (∀ (x : V), Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.Denotes cval env φ (Ix.Kernel.push x ρ) body (F x)) →
      (Ix.Kernel.regime φ m.pw = 0 → ∀ (x : V), Ix.Kernel.SetTheory.Mem x A → F x = Ix.Kernel.SetTheory.pt) →
        Ix.Kernel.Denotes cval env φ ρ (ty.lam body m) (Ix.Kernel.SetModel.lamR (Ix.Kernel.regime φ m.pw) A F)
Ix.Kernel.Denotes.pi : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {ty body : Ix.Kernel.Expr md} {m : Ix.Kernel.BinderMeta} {A : V} {B : V → V},
  Ix.Kernel.Denotes cval env φ ρ ty A →
    (∀ (x : V), Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.Denotes cval env φ (Ix.Kernel.push x ρ) body (B x)) →
      (Ix.Kernel.regime φ m.pw = 0 →
          ∀ (x : V), Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.SetTheory.Mem (B x) (Ix.Kernel.SetTheory.univ 0)) →
        Ix.Kernel.Denotes cval env φ ρ (ty.forallE body m) (Ix.Kernel.SetModel.piR (Ix.Kernel.regime φ m.pw) A B)
Ix.Kernel.Denotes.proj_table : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {T : Ix.Kernel.Key md} {i : Nat} {e : Ix.Kernel.Expr md} {entry : Ix.Kernel.ProjEntry md}
  {P : V},
  env.findProj? T i = some entry →
    Ix.Kernel.Denotes cval env φ ρ e P →
      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.proj T i e) (Ix.Kernel.field (i + entry.off) P)
Ix.Kernel.Denotes.proj_fst : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {T : Ix.Kernel.Key md} {e : Ix.Kernel.Expr md} {P : V},
  env.findProj? T 0 = none →
    Ix.Kernel.Denotes cval env φ ρ e P →
      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.proj T 0 e) (Ix.Kernel.SetTheory.sfst P)
Ix.Kernel.Denotes.proj_snd : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {T : Ix.Kernel.Key md} {e : Ix.Kernel.Expr md} {P : V},
  env.findProj? T 1 = none →
    Ix.Kernel.Denotes cval env φ ρ e P →
      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.proj T 1 e) (Ix.Kernel.SetTheory.ssnd P)
Ix.Kernel.Denotes.natLit : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {n : Nat} {X : V},
  Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.natLitToConstructor n) X →
    Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal n)) X
Ix.Kernel.Denotes.strLit : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {s : String} {X : V},
  Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.strLitToConstructor s) X →
    Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.strVal s)) X
-/
#guard_msgs in
#print Ix.Kernel.Denotes

/--
info: inductive Ix.Kernel.DenotesList.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} →
      (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) →
        Ix.Kernel.Env md →
          (Ix.Kernel.LevelParam → Nat) → (Ix.Kernel.BVarIdx → V) → List (Ix.Kernel.Expr md) → List V → Prop
number of parameters: 7
constructors:
Ix.Kernel.DenotesList.nil : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V}, Ix.Kernel.DenotesList cval env φ ρ [] []
Ix.Kernel.DenotesList.cons : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {e : Ix.Kernel.Expr md} {es : List (Ix.Kernel.Expr md)} {v : V} {vs : List V},
  Ix.Kernel.Denotes cval env φ ρ e v →
    Ix.Kernel.DenotesList cval env φ ρ es vs → Ix.Kernel.DenotesList cval env φ ρ (e :: es) (v :: vs)
-/
#guard_msgs in
#print Ix.Kernel.DenotesList

/--
info: inductive Ix.Kernel.Fits.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} →
      (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) →
        Ix.Kernel.Env md →
          (Ix.Kernel.LevelParam → Nat) →
            (Ix.Kernel.BVarIdx → V) → Ix.Kernel.Expr md → List V → (Ix.Kernel.BVarIdx → V) → Ix.Kernel.Expr md → Prop
number of parameters: 6
constructors:
Ix.Kernel.Fits.nil : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ : Ix.Kernel.BVarIdx → V} {T : Ix.Kernel.Expr md}, Ix.Kernel.Fits cval env φ ρ T [] ρ T
Ix.Kernel.Fits.cons : ∀ {V : Type w} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  {cval : Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V} {env : Ix.Kernel.Env md} {φ : Ix.Kernel.LevelParam → Nat}
  {ρ ρ' : Ix.Kernel.BVarIdx → V} {A B R : Ix.Kernel.Expr md} {m : Ix.Kernel.BinderMeta} {X x : V} {xs : List V},
  Ix.Kernel.Denotes cval env φ ρ A X →
    Ix.Kernel.SetTheory.Mem x X →
      Ix.Kernel.Fits cval env φ (Ix.Kernel.push x ρ) B xs ρ' R →
        Ix.Kernel.Fits cval env φ ρ (A.forallE B m) (x :: xs) ρ' R
-/
#guard_msgs in
#print Ix.Kernel.Fits

/--
info: @Ix.Kernel.GradedBy.eq_def : ∀ {V : Type u_1} [inst : Ix.Kernel.SetTheory V] {md : Ix.Kernel.Mode}
  (D : (Ix.Kernel.BVarIdx → V) → Ix.Kernel.Expr md → V → Prop) (x : Ix.Kernel.BVarIdx → V) (x_1 : Ix.Kernel.Expr md),
  Ix.Kernel.GradedBy D x x_1 =
    match x, x_1 with
    | ρ, f.app a =>
      Ix.Kernel.GradedBy D ρ f ∧
        Ix.Kernel.GradedBy D ρ a ∧
          ∃ r A F X B,
            D ρ f F ∧
              D ρ a X ∧
                Ix.Kernel.SetTheory.Mem F (Ix.Kernel.SetModel.piR r A B) ∧
                  Ix.Kernel.SetTheory.Mem X A ∧
                    (r = 0 →
                      ∀ (x : V),
                        Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.SetTheory.Mem (B x) (Ix.Kernel.SetTheory.univ 0))
    | ρ, ty.lam b m =>
      Ix.Kernel.GradedBy D ρ ty ∧
        ∀ (A : V), D ρ ty A → ∀ (x : V), Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.GradedBy D (Ix.Kernel.push x ρ) b
    | ρ, ty.forallE b m =>
      Ix.Kernel.GradedBy D ρ ty ∧
        ∀ (A : V), D ρ ty A → ∀ (x : V), Ix.Kernel.SetTheory.Mem x A → Ix.Kernel.GradedBy D (Ix.Kernel.push x ρ) b
    | ρ, Ix.Kernel.Expr.proj structName idx e => Ix.Kernel.GradedBy D ρ e
    | x, x_2 => True
-/
#guard_msgs in
#check @Ix.Kernel.GradedBy.eq_def

/--
info: @Ix.Kernel.SpineOk.eq_def : ∀ {V : Type u_1} [inst : Ix.Kernel.SetTheory V] (x : V) (x_1 : List V),
  Ix.Kernel.SpineOk x x_1 =
    match x, x_1 with
    | x, [] => True
    | F, x :: xs =>
      (∃ r A B, Ix.Kernel.SetTheory.Mem F (Ix.Kernel.SetModel.piR r A B) ∧ Ix.Kernel.SetTheory.Mem x A) ∧
        Ix.Kernel.SpineOk (Ix.Kernel.SetTheory.app F x) xs
-/
#guard_msgs in
#check @Ix.Kernel.SpineOk.eq_def

/--
info: def Ix.Kernel.IotaRule.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} →
      (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) →
        Ix.Kernel.Env md → Ix.Kernel.Key md → Ix.Kernel.ConstantVal md → Nat → Nat → Ix.Kernel.RecRule md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env r cv mI rP rl =>
  ∀ (cvC : Ix.Kernel.ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (Ix.Kernel.ConstantInfo.ctorInfo cvC nP nF) →
      ∀ (us : List Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ σ σC : Ix.Kernel.BVarIdx → V) (xs ys : List V)
        (dom body RC : Ix.Kernel.Expr md) (m : Ix.Kernel.BinderMeta) (D : Ix.Kernel.Key md) (ls : List Ix.Kernel.Level)
        (R K X : V),
        us.length = cv.levelParams.length →
          xs.length = mI →
            ys.length = nP + nF →
              Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const r us) R →
                Ix.Kernel.Fits cval env φ ρ (Ix.Kernel.Expr.instantiateLevelParams cv.levelParams us cv.type) xs σ
                    (dom.forallE body m) →
                  dom.getAppFn = Ix.Kernel.Expr.const D ls →
                    Ix.Kernel.Denotes cval env φ σ dom X →
                      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const rl.ctor ls) K →
                        Ix.Kernel.Fits cval env φ ρ (Ix.Kernel.Expr.instantiateLevelParams cvC.levelParams ls cvC.type)
                            ys σC RC →
                          Ix.Kernel.SetTheory.Mem (List.foldl Ix.Kernel.SetTheory.app K ys) X →
                            (rl.compareParams = true →
                                Ix.Kernel.DenotesList cval env φ σ (List.take nP dom.getAppArgs) (List.take nP ys)) →
                              (mI ≠ rP →
                                  Ix.Kernel.DenotesList cval env φ σC (List.drop nP RC.getAppArgs) (List.drop rP xs)) →
                                ∃ H,
                                  Ix.Kernel.Denotes cval env φ ρ
                                      (Ix.Kernel.Expr.instantiateLevelParams cv.levelParams us rl.rhs) H ∧
                                    Ix.Kernel.GradedBy (Ix.Kernel.Denotes cval env φ) ρ
                                        (Ix.Kernel.Expr.instantiateLevelParams cv.levelParams us rl.rhs) ∧
                                      Ix.Kernel.SpineOk H (List.take rP xs ++ List.drop nP ys) ∧
                                        List.foldl Ix.Kernel.SetTheory.app R
                                            (xs ++ [List.foldl Ix.Kernel.SetTheory.app K ys]) =
                                          List.foldl Ix.Kernel.SetTheory.app H (List.take rP xs ++ List.drop nP ys)
-/
#guard_msgs in
#print Ix.Kernel.IotaRule

/--
info: def Ix.Kernel.IotaLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (r : Ix.Kernel.Key md) (cv : Ix.Kernel.ConstantVal md) (mI rP : Nat) (rules : List (Ix.Kernel.RecRule md))
    (rl : Ix.Kernel.RecRule md),
    env.find? r = some (Ix.Kernel.ConstantInfo.recInfo cv mI rP rules) →
      rl ∈ rules → Ix.Kernel.IotaRule cval env r cv mI rP rl
-/
#guard_msgs in
#print Ix.Kernel.IotaLaw

/--
info: def Ix.Kernel.UnitLikeLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (T : Ix.Kernel.Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md),
    env.find? T = some (Ix.Kernel.ConstantInfo.indInfo cvT caps) →
      caps.unitlike = true →
        ∀ (us : List Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ σ : Ix.Kernel.BVarIdx → V) (ts : List V)
          (R : Ix.Kernel.Expr md) (F x y : V),
          us.length = cvT.levelParams.length →
            ts.length = caps.unitParams →
              Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const T us) F →
                Ix.Kernel.Fits cval env φ ρ (Ix.Kernel.Expr.instantiateLevelParams cvT.levelParams us cvT.type) ts σ R →
                  Ix.Kernel.SetTheory.Mem x (List.foldl Ix.Kernel.SetTheory.app F ts) →
                    Ix.Kernel.SetTheory.Mem y (List.foldl Ix.Kernel.SetTheory.app F ts) → x = y
-/
#guard_msgs in
#print Ix.Kernel.UnitLikeLaw

/--
info: def Ix.Kernel.ProjLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (T : Ix.Kernel.Key md) (i : Nat) (entry : Ix.Kernel.ProjEntry md) (cvT : Ix.Kernel.ConstantVal md)
    (capsT : Ix.Kernel.IndCaps md),
    env.findProj? T i = some entry →
      env.find? T = some (Ix.Kernel.ConstantInfo.indInfo cvT capsT) →
        cvT.levelParams = entry.levelParams ∧
          ∃ cvC,
            env.find? entry.ctor = some (Ix.Kernel.ConstantInfo.ctorInfo cvC entry.numParams entry.numFields) ∧
              cvC.levelParams = entry.levelParams ∧
                (∃ bs,
                    Ix.Kernel.Expr.stripPis (entry.numParams + entry.numFields) cvC.type =
                      some
                        (bs,
                          (Ix.Kernel.Expr.const T (List.map Ix.Kernel.Level.param entry.levelParams)).mkAppN
                            (List.map (fun k => Ix.Kernel.Expr.bvar (entry.numFields + entry.numParams - 1 - k))
                              (List.range entry.numParams)))) ∧
                  ∀ (us : List Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (F K : V),
                    us.length = entry.levelParams.length →
                      Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const T us) F →
                        Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const entry.ctor us) K →
                          ((Ix.Kernel.Level.eval (Ix.Kernel.Level.substFn φ entry.levelParams us) entry.structSort = 0 →
                                Ix.Kernel.Level.eval (Ix.Kernel.Level.substFn φ entry.levelParams us) entry.fieldSort =
                                  0) →
                              ∀ (σ : Ix.Kernel.BVarIdx → V) (R : Ix.Kernel.Expr md) (ys : List V),
                                ys.length = entry.numParams + entry.numFields →
                                  Ix.Kernel.Fits cval env φ ρ
                                      (Ix.Kernel.Expr.instantiateLevelParams cvC.levelParams us cvC.type) ys σ R →
                                    Ix.Kernel.field (i + entry.off) (List.foldl Ix.Kernel.SetTheory.app K ys) =
                                      ys.getD (entry.numParams + i) Ix.Kernel.SetTheory.empty) ∧
                            ∀ (σ : Ix.Kernel.BVarIdx → V) (R : Ix.Kernel.Expr md) (ts : List V) (x : V),
                              ts.length = entry.numParams →
                                Ix.Kernel.Fits cval env φ ρ
                                    (Ix.Kernel.Expr.instantiateLevelParams cvT.levelParams us cvT.type) ts σ R →
                                  Ix.Kernel.SetTheory.Mem x (List.foldl Ix.Kernel.SetTheory.app F ts) →
                                    x =
                                      List.foldl Ix.Kernel.SetTheory.app K
                                        (ts ++
                                          List.map (fun j => Ix.Kernel.field (j + entry.off) x)
                                            (List.range entry.numFields))
-/
#guard_msgs in
#print Ix.Kernel.ProjLaw

/--
info: def Ix.Kernel.natArithOps : {md : Ix.Kernel.Mode} → List (Ix.Kernel.Key md × (Nat → Nat → Nat)) :=
fun {md} =>
  [(Ix.Kernel.natAddName, Nat.add), (Ix.Kernel.natSubName, Nat.sub), (Ix.Kernel.natMulName, Nat.mul),
    (Ix.Kernel.natPowName, Nat.pow), (Ix.Kernel.natDivName, Nat.div), (Ix.Kernel.natModName, Nat.mod),
    (Ix.Kernel.natGcdName, Nat.gcd), (Ix.Kernel.natLandName, Nat.land), (Ix.Kernel.natLorName, Nat.lor),
    (Ix.Kernel.natXorName, Nat.xor), (Ix.Kernel.natShiftLeftName, Nat.shiftLeft),
    (Ix.Kernel.natShiftRightName, Nat.shiftRight)]
-/
#guard_msgs in
#print Ix.Kernel.natArithOps

/--
info: def Ix.Kernel.natCmpOps : {md : Ix.Kernel.Mode} → List (Ix.Kernel.Key md × (Nat → Nat → Bool)) :=
fun {md} => [(Ix.Kernel.natBeqName, Nat.beq), (Ix.Kernel.natBleName, Nat.ble)]
-/
#guard_msgs in
#print Ix.Kernel.natCmpOps

/--
info: def Ix.Kernel.NatLitLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  (∀ (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
      env.find? Ix.Kernel.natPredName = some (Ix.Kernel.ConstantInfo.defnInfo cv v hint) →
        ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (a : Nat) (X : V),
          Ix.Kernel.Denotes cval env φ ρ
              ((Ix.Kernel.Expr.const Ix.Kernel.natPredName []).app (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal a)))
              X →
            Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal (a - 1))) X) ∧
    (∀ (c : Ix.Kernel.Key md) (f : Nat → Nat → Nat),
        (c, f) ∈ Ix.Kernel.natArithOps →
          ∀ (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
            env.find? c = some (Ix.Kernel.ConstantInfo.defnInfo cv v hint) →
              ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (a b : Nat) (X : V),
                Ix.Kernel.Denotes cval env φ ρ
                    (((Ix.Kernel.Expr.const c []).app (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal a))).app
                      (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal b)))
                    X →
                  Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal (f a b))) X) ∧
      ∀ (c : Ix.Kernel.Key md) (f : Nat → Nat → Bool),
        (c, f) ∈ Ix.Kernel.natCmpOps →
          ∀ (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
            env.find? c = some (Ix.Kernel.ConstantInfo.defnInfo cv v hint) →
              ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (a b : Nat) (X : V),
                Ix.Kernel.Denotes cval env φ ρ
                    (((Ix.Kernel.Expr.const c []).app (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal a))).app
                      (Ix.Kernel.Expr.lit (Ix.Kernel.Literal.natVal b)))
                    X →
                  Ix.Kernel.Denotes cval env φ ρ
                    (Ix.Kernel.Expr.const (if f a b = true then Ix.Kernel.boolTrueName else Ix.Kernel.boolFalseName) [])
                    X
-/
#guard_msgs in
#print Ix.Kernel.NatLitLaw

/--
info: def Ix.Kernel.NatAddLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
    env.find? Ix.Kernel.natAddName = some (Ix.Kernel.ConstantInfo.defnInfo cv v hint) →
      ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (N Z S A : V),
        Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.natName []) N →
          Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.natZeroName []) Z →
            Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.natSuccName []) S →
              Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const Ix.Kernel.natAddName []) A →
                ∀ (x y : V),
                  Ix.Kernel.SetTheory.Mem x N →
                    Ix.Kernel.SetTheory.Mem y N →
                      Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app A x) Z = x ∧
                        Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app A x) (Ix.Kernel.SetTheory.app S y) =
                          Ix.Kernel.SetTheory.app S (Ix.Kernel.SetTheory.app (Ix.Kernel.SetTheory.app A x) y)
-/
#guard_msgs in
#print Ix.Kernel.NatAddLaw

/--
info: def Ix.Kernel.GradedLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (c : Ix.Kernel.ConstantInfo md),
    c ∈ env.consts →
      ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
        Ix.Kernel.GradedBy (Ix.Kernel.Denotes cval env φ) ρ c.toConstantVal.type ∧
          ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint),
            c = Ix.Kernel.ConstantInfo.defnInfo cv value hint →
              Ix.Kernel.GradedBy (Ix.Kernel.Denotes cval env φ) ρ value
-/
#guard_msgs in
#print Ix.Kernel.GradedLaw

/--
info: @Ix.Kernel.pushVals.eq_def : ∀ {V : Type u_1} (ρ : Ix.Kernel.BVarIdx → V) (x : List V),
  Ix.Kernel.pushVals ρ x =
    match (motive := List V → Ix.Kernel.BVarIdx → V) x with
    | [] => ρ
    | x :: xs => Ix.Kernel.pushVals (Ix.Kernel.push x ρ) xs
-/
#guard_msgs in
#check @Ix.Kernel.pushVals.eq_def

/--
info: def Ix.Kernel.ProjTypeLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (T : Ix.Kernel.Key md) (i : Nat) (entry : Ix.Kernel.ProjEntry md),
    env.findProj? T i = some entry →
      ∀ (us : List Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V) (F : V) (ts : List V)
        (x : V),
        us.length = entry.levelParams.length →
          Ix.Kernel.Denotes cval env φ ρ (Ix.Kernel.Expr.const T us) F →
            (Ix.Kernel.Level.eval (Ix.Kernel.Level.substFn φ entry.levelParams us) entry.structSort = 0 →
                Ix.Kernel.Level.eval (Ix.Kernel.Level.substFn φ entry.levelParams us) entry.fieldSort = 0) →
              ts.length = entry.numParams →
                Ix.Kernel.SpineOk F ts →
                  Ix.Kernel.SetTheory.Mem x (List.foldl Ix.Kernel.SetTheory.app F ts) →
                    ∃ B,
                      Ix.Kernel.Denotes cval env φ (Ix.Kernel.push x (Ix.Kernel.pushVals ρ ts))
                          (Ix.Kernel.Expr.instantiateLevelParams entry.levelParams us entry.body) B ∧
                        Ix.Kernel.GradedBy (Ix.Kernel.Denotes cval env φ) (Ix.Kernel.push x (Ix.Kernel.pushVals ρ ts))
                            (Ix.Kernel.Expr.instantiateLevelParams entry.levelParams us entry.body) ∧
                          Ix.Kernel.SetTheory.Mem (Ix.Kernel.field (i + entry.off) x) B
-/
#guard_msgs in
#print Ix.Kernel.ProjTypeLaw

/--
info: def Ix.Kernel.EtaFnLaw.{w} : {V : Type w} →
  [Ix.Kernel.SetTheory V] →
    {md : Ix.Kernel.Mode} → (Ix.Kernel.Key md → (Ix.Kernel.LevelParam → Nat) → V) → Ix.Kernel.Env md → Prop :=
fun {V} [Ix.Kernel.SetTheory V] {md} cval env =>
  ∀ (T : Ix.Kernel.Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md) (C : Ix.Kernel.Key md),
    env.find? T = some (Ix.Kernel.ConstantInfo.indInfo cvT caps) →
      caps.eta = true →
        Ix.Kernel.reservedBasisNames.contains T = false →
          caps.etaCtor = some C →
            Ix.Kernel.reservedBasisNames.contains C = false →
              (∃ cvC nP nF, env.find? C = some (Ix.Kernel.ConstantInfo.ctorInfo cvC nP nF)) →
                (∀ (j : Nat),
                    j < caps.etaFields →
                      ∃ cv mI rP rules,
                        env.find? (Ix.Kernel.projFnName T j) = some (Ix.Kernel.ConstantInfo.recInfo cv mI rP rules)) →
                  ∀ (us : List Ix.Kernel.Level) (φ : Ix.Kernel.LevelParam → Nat) (ρ σ : Ix.Kernel.BVarIdx → V)
                    (R : Ix.Kernel.Expr md) (ts : List V) (x : V),
                    us.length = cvT.levelParams.length →
                      ts.length = caps.etaParams →
                        Ix.Kernel.Fits cval env φ ρ (Ix.Kernel.Expr.instantiateLevelParams cvT.levelParams us cvT.type)
                            ts σ R →
                          Ix.Kernel.SetTheory.Mem x
                              (List.foldl Ix.Kernel.SetTheory.app
                                (cval T (Ix.Kernel.Level.substFn φ cvT.levelParams us)) ts) →
                            x =
                              List.foldl Ix.Kernel.SetTheory.app (cval C (Ix.Kernel.Level.substFn φ cvT.levelParams us))
                                (ts ++
                                  List.map
                                    (fun j =>
                                      List.foldl Ix.Kernel.SetTheory.app
                                        (cval (Ix.Kernel.projFnName T j) (Ix.Kernel.Level.substFn φ cvT.levelParams us))
                                        (ts ++ [x]))
                                    (List.range caps.etaFields))
-/
#guard_msgs in
#print Ix.Kernel.EtaFnLaw

/-! ## What they read from `IxC.Kernel.SetTheory.Core` -/

/--
info: def Ix.Kernel.Equinumerous.{u} : {V : Type u} → (V → V → Prop) → V → V → Prop :=
fun {V} mem y u =>
  ∃ f,
    (∀ (z : V), mem z y → mem (f z) u) ∧
      (∀ (z z' : V), mem z y → mem z' y → f z = f z' → z = z') ∧ ∀ (w : V), mem w u → ∃ z, mem z y ∧ f z = w
-/
#guard_msgs in
#print Ix.Kernel.Equinumerous

/--
info: def Ix.Kernel.IsTGUniverse.{u} : {V : Type u} → (V → V → Prop) → V → Prop :=
fun {V} mem u =>
  (∀ (y z : V), mem y u → mem z y → mem z u) ∧
    (∀ (y z : V), mem y u → (∀ (w : V), mem w z → mem w y) → mem z u) ∧
      (∀ (y : V), mem y u → ∃ p, mem p u ∧ ∀ (z : V), (∀ (w : V), mem w z → mem w y) → mem z p) ∧
        ∀ (y : V), (∀ (w : V), mem w y → mem w u) → Ix.Kernel.Equinumerous mem y u ∨ mem y u
-/
#guard_msgs in
#print Ix.Kernel.IsTGUniverse

/-! ## Axioms

The class of set theories reaches no axiom. The structure of models reaches the three
standard axioms and no other. -/

#guard_kernel_axioms Ix.Kernel.SetTheory []
#guard_kernel_axioms Ix.Kernel.Model [propext, Classical.choice, Quot.sound]
