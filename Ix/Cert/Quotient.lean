import Ix.Cert.Statement
import Ix.Cert.SourceLaws
import Ix.LeanIngress.Rename
import IxC.Kernel.Verify.Rename.Model
import IxC.Kernel.Ixon.ReaderSpec

/-! # Quotient Source at the artifact's addresses: the statements' side (step 7.3 (iv))

IxC renames a checked quotient Source accept to the artifact's addresses
(`Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt`, by the joined map `evAddr`: a
published name to its address, a bundle-only name to its bundle address), with the
two environments related key by key (`Ix.Kernel.EnvRel`). This module supplies what
the statements need around it:

* `ValueModel.pullback`: a value model of the renamed environment is one of the
  quotient environment (IxC's `Model.pullback` and `defn_value_pullback`);
* `PublishedRolesBound`, decided: every published name whose ingress name is a role's
  Lean name sits at the table's address for that role. It is B5a's role binding, by
  ingress name over every published name, so no stored name hash is trusted. It gives
  the table rule's premise `Ix.LeanIngress.TableBound` (`tableBound_of`) and the
  agreement of Source's by-name and Ixon's by-table role binding
  (`publishedAddress_role`);
* `publishedAddress_id`, `reading_id`: the address the statements read a source name
  at (`publishedAddress`) is the one IxC renames it to (`addrOf`), when every
  published name agrees with the artifact's address map (`PublishedAgree`, decided);
  and its reading is the role key the table binds there or the address itself
  (`Ix.Kernel.Reader.Ctx.keyAt_ok`);
* `sourceAcceptsQ_addrAt`: `SourceAcceptsQ` at an admitted table the artifact's role
  names sit at is a reference accept at the artifact's addresses. Its evidence is the
  bundle's renamed by `evAddr` (a bundle-only name goes to the bundle's address for it, the
  content address its records cite), not the Ixon run's; only injectivity is used,
  and moving acceptance between evidences is `Ix.Cert.Evidence.acceptsRef_covers`'s;
* `EnvSubstRel`, `EnvSubstModelPullback`, `EnvSubstPullback`: conditional model-theoretic
  pullbacks from the quotient Source environment `envQ` to a nominal Source environment
  `envS` along the fiber-alias substitution `Key.subst ρ`. Quotient Source (`CompileCorrect`
  together with `Ix.LeanIngress.prepareSourceCollapsedAt_trace`) is the primary
  unconditional security guarantee: quotient collapse only merges declarations that are
  structurally identical (`Declaration.beqF`, hence `=`) under `Key.subst ρ`, and
  `CompileCorrect` transports both `ValueModel` and `LawModel` unconditionally between
  `envQ` and `envA`. Pulling models of `envQ` back to a nominal `envS` is conditioned on
  `EnvSubstRel` (for `ValueModel`) and `LawModel.Rel` (for `LawModel`); deriving
  `LawModel.Rel` from `EnvSubstRel` and discharging `EnvSubstRel` from
  `Ix.LeanIngress.FiberAliasSafe` on closures whose alias fibers do not mix reducibility
  hints is left for future work. -/

namespace Ix.Cert

open Ix.Kernel (Env SetTheory LevelParam BVarIdx)
open Ix.LeanIngress (ingressName roleOf sourceAddrs addrOf)

universe w

/-! ## Value models pull back along a renaming -/

/-- **A value model pulls back along a renaming**: under `EnvRel P f env env'`, a value
model of `env'` gives one of `env` (`Ix.Kernel.Model.pullback`, with the definitions'
values through `Ix.Kernel.defn_value_pullback`). -/
def ValueModel.pullback {md md' : Ix.Kernel.Mode} {V : Type w} [SetTheory V]
    {P : md.Id → Prop} {f : md.Id → md'.Id} {env : Env md} {env' : Env md'}
    (h : Ix.Kernel.EnvRel P f env env') (N : ValueModel V env') : ValueModel V env :=
  { Ix.Kernel.Model.pullback h N.toModel with
    defn_value := Ix.Kernel.defn_value_pullback h N.defn_value }

/-! ## Every published role name sits at its role's address -/

/-- **Every published role name sits at its role's address**: a published name whose
ingress name is a role's Lean name is published at the address the table binds that
role to. Over every published name and by ingress name, so no stored name hash is
trusted. -/
def PublishedRolesBound (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) : Prop :=
  ∀ m d, (m, d) ∈ ixe.named.toList → ∀ r : Ix.Kernel.Role, ingressName m = r.leanName →
    t.addressOf? r = some d.addr

/-- `PublishedRolesBound`, decided (each published name's ingress name built once). -/
def publishedRolesBound (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) : Bool :=
  ixe.named.toList.all fun p =>
    let n := ingressName p.1
    Ix.Kernel.Role.all.all fun r => if n = r.leanName then t.addressOf? r == some p.2.addr else true

theorem publishedRolesBound_iff (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) :
    publishedRolesBound t ixe = true ↔ PublishedRolesBound t ixe := by
  unfold publishedRolesBound PublishedRolesBound
  rw [List.all_eq_true]
  constructor
  · intro h m d hm r hr
    have h1 := List.all_eq_true.mp (h (m, d) hm) r (Ix.Kernel.Role.mem_all r)
    simp only [hr, ↓reduceIte, beq_iff_eq] at h1
    exact h1
  · intro h p hp
    refine List.all_eq_true.mpr fun r _ => ?_
    by_cases hr : ingressName p.1 = r.leanName
    · simp only [hr, ↓reduceIte, beq_iff_eq]
      exact h p.1 p.2 hp r hr
    · simp only [hr, ↓reduceIte]

theorem byLeanName_foldl : ∀ (l : List Ix.Kernel.Role) (init : Std.HashMap Ix.Kernel.Name Ix.Kernel.Role)
    {x : Ix.Kernel.Name} {r : Ix.Kernel.Role},
    (l.foldl (fun m s => m.insert s.leanName s) init)[x]? = some r → init[x]? = some r ∨ r.leanName = x
  | [], _, _, _, h => .inl h
  | s :: l, init, x, r, h => by
    rw [List.foldl_cons] at h
    rcases byLeanName_foldl l _ h with h | h
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        exact .inr (beq_iff_eq.mp he)
      · exact .inl h
    · exact .inr h

/-- **A role name is its role's Lean name** (`roleOf` reads `Role.byLeanName`). -/
theorem roleOf_leanName {x : Ix.Kernel.Name} {r : Ix.Kernel.Role} (h : roleOf x = some r) :
    x = r.leanName := by
  have hk := Ix.LeanIngress.roleOf_eq_some h
  unfold Ix.Kernel.Key.ofName at hk
  cases hb : Ix.Kernel.Role.byLeanName[x]? with
  | none => rw [hb] at hk; cases hk
  | some s =>
    rw [hb] at hk
    cases hk
    unfold Ix.Kernel.Role.byLeanName at hb
    rcases byLeanName_foldl _ _ hb with h0 | h0
    · simp at h0
    · exact h0.symm

/-- **The table rule's premise**: when the table is admitted and every published role
name sits at its role's address, every published role name's address is bound to its
role in the table's inverse (`Ix.LeanIngress.roleAtMap_spec`). -/
theorem tableBound_of {t : Ix.Kernel.RoleTable} {ixe : Ixon.Env} (checked : t.check = .ok ())
    (bound : PublishedRolesBound t ixe) :
    Ix.LeanIngress.TableBound ixe (Ix.LeanIngress.roleAtMap t) := by
  intro x r a hx hr
  obtain ⟨m, d, hm, hn, ha⟩ := Ix.LeanIngress.sourceAddrs_spec hx
  have e := bound m d hm r (by rw [hn]; exact roleOf_leanName hr)
  rw [ha] at e
  exact (Ix.LeanIngress.roleAtMap_spec checked).mpr e


/-! ## The published address is the renamed one -/

/-- **Every published name agrees with the artifact's address map**: the address map
(`sourceAddrs`, keyed by ingress names) holds each published name at its own address,
so two published names with one ingress name have one address. -/
def PublishedAgree (ixe : Ixon.Env) : Prop :=
  ∀ m d, (m, d) ∈ ixe.named.toList → (sourceAddrs ixe)[ingressName m]? = some d.addr

/-- `PublishedAgree`, decided (the address map built once, not per entry). -/
def publishedAgree (ixe : Ixon.Env) : Bool :=
  let addrs := sourceAddrs ixe
  ixe.named.toList.all fun (m, d) => addrs[ingressName m]? == some d.addr

theorem publishedAgree_iff (ixe : Ixon.Env) : publishedAgree ixe = true ↔ PublishedAgree ixe := by
  unfold publishedAgree PublishedAgree
  dsimp only
  rw [List.all_eq_true]
  constructor
  · intro h m d hm
    exact beq_iff_eq.mp (h (m, d) hm)
  · intro h p hp
    exact beq_iff_eq.mpr (h p.1 p.2 hp)

theorem nameIsName_iff : ∀ (n : Ix.Name) (m : Ix.Kernel.Name),
    Ix.LeanIngress.nameIsName n m = true ↔ ingressName n = m
  | .anonymous _, .anonymous => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .anonymous _, .str _ _ => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .anonymous _, .num _ _ => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .str p s _, .anonymous => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .str p s _, .num _ _ => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .num p i _, .anonymous => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .num p i _, .str _ _ => by simp [Ix.LeanIngress.nameIsName, ingressName]
  | .str p s _, .str q t => by
    simp only [Ix.LeanIngress.nameIsName, ingressName, Bool.and_eq_true, beq_iff_eq, nameIsName_iff p q,
      Ix.Kernel.Name.str.injEq]
    exact and_comm
  | .num p i _, .num q j => by
    simp only [Ix.LeanIngress.nameIsName, ingressName, Bool.and_eq_true, beq_iff_eq, nameIsName_iff p q,
      Ix.Kernel.Name.num.injEq]
    exact and_comm

/-- **The published address of a role is the table's** (B5a's agreement, by ingress
name): the address the statements read a role's constant at (`publishedAddress` at
`.role r`) is the one the table binds `r` to, when every published role name sits at
its role's address. -/
theorem publishedAddress_role {t : Ix.Kernel.RoleTable} {ixe : Ixon.Env}
    (bound : PublishedRolesBound t ixe) {r : Ix.Kernel.Role} {a : Address}
    (h : publishedAddress ixe (.role r) = some a) : t.addressOf? r = some a := by
  unfold publishedAddress at h
  revert h
  cases hf : ixe.named.toList.find? (fun (p : Ix.Name × Ixon.Named) => Ix.LeanIngress.nameIs p.1 (.role r)) with
  | none => intro h; cases h
  | some p =>
    obtain ⟨m, d⟩ := p
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    have found := List.find?_some hf
    have inside := List.mem_of_find?_eq_some hf
    simp only [Ix.LeanIngress.nameIs] at found
    rw [← h]
    exact bound m d inside r ((nameIsName_iff m r.leanName).mp found)

/-- **The published address of an input name is the renamed one**: when every
published name agrees with the address map, the statements' published address for an
input key (`publishedAddress`) is its address in the map, which IxC renames it to
(`addrOf`). -/
theorem publishedAddress_id {ixe : Ixon.Env} (agree : PublishedAgree ixe) {n : Ix.Kernel.Name}
    (noRole : roleOf n = none) {a : Address} (published : (sourceAddrs ixe)[n]? = some a) :
    publishedAddress ixe (.id n) = some a := by
  obtain ⟨m, d, hm, hn, _⟩ := Ix.LeanIngress.sourceAddrs_spec published
  have notRole : Ix.Kernel.Role.byLeanName.contains n = false := by
    unfold roleOf Ix.Kernel.Key.ofName at noRole
    cases hb : Ix.Kernel.Role.byLeanName[n]? with
    | none => rw [Std.HashMap.contains_eq_isSome_getElem?, hb]; rfl
    | some r => rw [hb] at noRole; cases noRole
  unfold publishedAddress
  cases hf : ixe.named.toList.find? (fun (p : Ix.Name × Ixon.Named) => Ix.LeanIngress.nameIs p.1 (.id n)) with
  | none =>
    have := List.find?_eq_none.mp hf (m, d) hm
    simp [Ix.LeanIngress.nameIs, (nameIsName_iff m n).mpr hn, notRole] at this
  | some p =>
    obtain ⟨m', d'⟩ := p
    have found := List.find?_some hf
    have inside := List.mem_of_find?_eq_some hf
    simp only [Ix.LeanIngress.nameIs, Bool.and_eq_true] at found
    have hn' := (nameIsName_iff m' n).mp found.1
    have := agree m' d' inside
    rw [hn', published] at this
    simp only [Option.map_some, Option.some.injEq]
    exact (Option.some.inj this).symm

/-- **The reading of an input name**: its published address is the renamed one, and the
reader keys it either by the role key the table binds at that address or by the
address itself (`Ix.Kernel.Reader.Ctx.keyAt_ok`). -/
theorem reading_id {ixe : Ixon.Env} (agree : PublishedAgree ixe) (cx : Ix.Kernel.Reader.Ctx .anon)
    {c : Ix.Kernel.ConstantInfo .source} {n : Ix.Kernel.Name} (named : c.name = .id n)
    (noRole : roleOf n = none) {a : Address} (published : (sourceAddrs ixe)[n]? = some a)
    {e : Ix.Kernel.Expr .anon} (read : reading ixe cx c = some e) :
    a = addrOf ixe n ∧ ∃ r k, Ix.Kernel.Reader.resolve cx.store a = some r ∧
      e = .const k (c.toConstantVal.levelParams.map .param) ∧
      (cx.roles.names[r]? = some k ∨ (cx.roles.names[r]? = none ∧ k = .id a)) := by
  refine ⟨(Ix.LeanIngress.addrOf_eq published).symm, ?_⟩
  unfold reading at read
  rw [named, publishedAddress_id agree noRole published] at read
  cases hk : cx.keyAt a with
  | error err => simp [hk, Except.toOption] at read
  | ok k =>
    simp only [hk, Except.toOption, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at read
    obtain ⟨r, hr, hkey⟩ := Ix.Kernel.Reader.Ctx.keyAt_ok hk
    refine ⟨r, k, hr, read.symm, ?_⟩
    rcases hkey with bound | ⟨free, i, hi, rfl⟩
    · exact .inl bound
    · simp only [Ix.Kernel.Mode.addressId?, Option.some.injEq] at hi
      exact .inr ⟨free, by rw [hi]⟩

/-! ## Quotient Source at the artifact's addresses -/

/-- **Quotient Source acceptance at the artifact's addresses**: a quotient accept at an
admitted table that every published role name sits at, renamed by the joined map
(`Ix.LeanIngress.evAddr`: a published name to its address, a bundle-only name to its
bundle address), is a reference accept at the same fuel, at the renamed bundle
evidence, of the renamed declarations, installing an environment related key by key to
the quotient one (`Ix.Kernel.EnvRel`); every value model of it pulls back
(`ValueModel.pullback`). From IxC's `acceptsRef_prepareSourceCollapsedAt`; the
committed bundle is not unfolded. -/
theorem sourceAcceptsQ_addrAt {condense : Ix.Environment → Ix.CondensedBlocks} {env : Ix.Environment}
    {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {envS : Env .source} (accepted : SourceAcceptsQ condense env roots sub ixe t envS)
    (checked : t.check = .ok ()) (bound : PublishedRolesBound t ixe) :
    ∃ b, Ix.RoleEvidence.quotientBundle () = .ok b ∧
      ∃ (ds : Array (Ix.Kernel.Declaration .source)) (envA : Env .anon),
        Ix.Kernel.Cached.AcceptsRef .verified
          ((Ix.LeanIngress.evidenceSubst (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
            (Ix.RoleEvidence.quotientEvidence ())).mapKeys (Ix.LeanIngress.evAddr ixe b))
          (ds.toList.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))) envA ∧
        Ix.Kernel.EnvRel
          (fun n => Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap t) n ∨ Ix.LeanIngress.BundleOnly ixe b n)
          (Ix.LeanIngress.evAddr ixe b) envS envA := by
  obtain ⟨_, _, ds, _, prepared, run⟩ := accepted
  obtain ⟨b, hb, envA, runA, rel⟩ :=
    Ix.LeanIngress.acceptsRef_prepareSourceCollapsedAt .verified (tableBound_of checked bound) prepared run
  exact ⟨b, hb, ds, envA, runA, rel⟩

/-! ## Semantic model pullback and composition along non-injective `Key.subst ρ` -/

/-- **Law-model pullback along a key map `σ`**: every law model of `env₂`
pulls back to a law model of `env₁` whose constant values agree with `env₂`'s
along `σ`. -/
def LawModel.Rel {md₁ md₂ : Ix.Kernel.Mode}
    (σ : Ix.Kernel.Key md₁ → Ix.Kernel.Key md₂)
    (env₁ : Env md₁) (env₂ : Env md₂) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : LawModel V env₂),
    ∃ N : LawModel V env₁, ∀ k φ, N.cval k φ = M.cval (σ k) φ

/-- **Composition of `ValueModel.Rel`**: pulling back along `f` and `g` pulls back
along `g ∘ f`. -/
theorem ValueModel.comp {md₁ md₂ md₃ : Ix.Kernel.Mode}
    {f : Ix.Kernel.Key md₁ → Ix.Kernel.Key md₂}
    {g : Ix.Kernel.Key md₂ → Ix.Kernel.Key md₃}
    {env₁ : Env md₁} {env₂ : Env md₂} {env₃ : Env md₃}
    (hf : ValueModel.Rel.{w} f env₁ env₂)
    (hg : ValueModel.Rel.{w} g env₂ env₃) :
    ValueModel.Rel.{w} (g ∘ f) env₁ env₃ := by
  intro V _ M₃
  obtain ⟨M₂, hM₂⟩ := hg V M₃
  obtain ⟨M₁, hM₁⟩ := hf V M₂
  exact ⟨M₁, fun k φ => (hM₁ k φ).trans (hM₂ (f k) φ)⟩

/-- **Composition of `LawModel.Rel`**: pulling back along `f` and `g` pulls back
along `g ∘ f`. -/
theorem LawModel.comp {md₁ md₂ md₃ : Ix.Kernel.Mode}
    {f : Ix.Kernel.Key md₁ → Ix.Kernel.Key md₂}
    {g : Ix.Kernel.Key md₂ → Ix.Kernel.Key md₃}
    {env₁ : Env md₁} {env₂ : Env md₂} {env₃ : Env md₃}
    (hf : LawModel.Rel.{w} f env₁ env₂)
    (hg : LawModel.Rel.{w} g env₂ env₃) :
    LawModel.Rel.{w} (g ∘ f) env₁ env₃ := by
  intro V _ M₃
  obtain ⟨M₂, hM₂⟩ := hg V M₃
  obtain ⟨M₁, hM₁⟩ := hf V M₂
  exact ⟨M₁, fun k φ => (hM₁ k φ).trans (hM₂ (f k) φ)⟩

/-- `ValueModel.pullback` packaged as a `ValueModel.Rel` along `Key.map f`. -/
theorem ValueModel.pullback_rel {md md' : Ix.Kernel.Mode}
    {P : md.Id → Prop} {f : md.Id → md'.Id} {env : Env md} {env' : Env md'}
    (h : Ix.Kernel.EnvRel P f env env') :
    ValueModel.Rel.{w} (Ix.Kernel.Key.map f) env env' :=
  fun _ _ N => ⟨ValueModel.pullback h N, fun _ _ => rfl⟩

/-- **The pulled-back constant values along `Key.subst ρ`**: `k` denotes what
`Key.subst ρ k` does. -/
def substCval {V : Type w} (ρ : Ix.LeanIngress.FiberMap)
    (cval' : Ix.Kernel.Key .source → (LevelParam → Nat) → V) :
    Ix.Kernel.Key .source → (LevelParam → Nat) → V :=
  fun k φ => cval' (Ix.LeanIngress.Key.subst ρ k) φ

/-- Rename a projection-table entry's keys by `Key.subst ρ`. -/
def ProjEntry.substKeys (ρ : Ix.LeanIngress.FiberMap)
    (e : Ix.Kernel.ProjEntry .source) : Ix.Kernel.ProjEntry .source :=
  { structName := Ix.LeanIngress.Key.subst ρ e.structName,
    idx := e.idx,
    levelParams := e.levelParams,
    numParams := e.numParams,
    ctor := Ix.LeanIngress.Key.subst ρ e.ctor,
    numFields := e.numFields,
    body := Ix.LeanIngress.Expr.substKeys ρ e.body,
    fieldSort := e.fieldSort,
    structSort := e.structSort,
    off := e.off }

theorem ProjTable.substKeys_entry (ρ : Ix.LeanIngress.FiberMap)
    (t : Ix.Kernel.ProjTable .source) (i : Nat) :
    (Ix.LeanIngress.ProjTable.substKeys ρ t).entry i =
      ProjEntry.substKeys ρ (t.entry i) := by
  simp only [Ix.Kernel.ProjTable.entry, Ix.LeanIngress.ProjTable.substKeys,
    ProjEntry.substKeys, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t.bodies[i]? <;> rfl

@[simp] theorem natLitToConstructor_substKeys (ρ : Ix.LeanIngress.FiberMap) (n : Nat) :
    Ix.LeanIngress.Expr.substKeys ρ (Ix.Kernel.natLitToConstructor n) =
      Ix.Kernel.natLitToConstructor n := by
  cases n <;> rfl

@[simp] theorem strLitToConstructor_substKeys (ρ : Ix.LeanIngress.FiberMap) (s : String) :
    Ix.LeanIngress.Expr.substKeys ρ (Ix.Kernel.strLitToConstructor s) =
      Ix.Kernel.strLitToConstructor s := by
  unfold Ix.Kernel.strLitToConstructor
  simp only [Ix.LeanIngress.Expr.substKeys, Ix.LeanIngress.Key.subst]
  congr 1
  generalize s.toList = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldr_cons, Ix.LeanIngress.Expr.substKeys, Ix.LeanIngress.Key.subst, ih]

/-- **Environment relation along a non-injective fiber map `Key.subst ρ`**:
`envS`'s constants are in scope `P`, every constant of `envS` maps into `envQ`
under `ConstantInfo.substKeys ρ`, and every lookup at a good key of `envS`
is answered in `envQ` at its substituted key by the substituted constant. -/
structure EnvSubstRel (P : Ix.Kernel.Mode.Id .source → Prop)
    (ρ : Ix.LeanIngress.FiberMap) (envS envQ : Env .source) : Prop where
  all : envS.Good (Ix.Kernel.KeyScope.ofId P)
  find : ∀ k : Ix.Kernel.Key .source, k.Good (Ix.Kernel.KeyScope.ofId P) →
    envQ.find? (Ix.LeanIngress.Key.subst ρ k) =
      (envS.find? k).map (Ix.LeanIngress.ConstantInfo.substKeys ρ)
  mem : ∀ {c : Ix.Kernel.ConstantInfo .source},
    c ∈ envS.consts → Ix.LeanIngress.ConstantInfo.substKeys ρ c ∈ envQ.consts

theorem EnvSubstRel.find_some {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρ envS envQ) {k : Ix.Kernel.Key .source}
    {c : Ix.Kernel.ConstantInfo .source} (hc : envS.find? k = some c) :
    envQ.find? (Ix.LeanIngress.Key.subst ρ k) =
      some (Ix.LeanIngress.ConstantInfo.substKeys ρ c) := by
  have hk : k.Good (Ix.Kernel.KeyScope.ofId P) := by
    obtain ⟨cs⟩ := envS
    simp only [Ix.Kernel.Env.find?] at hc
    have hname := List.find?_some hc
    have hmem := List.mem_of_find?_eq_some hc
    rw [beq_iff_eq] at hname
    rw [← hname]
    exact (h.all c hmem).name
  rw [h.find k hk, hc]
  rfl

theorem EnvSubstRel.findProj? {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρ envS envQ)
    {T : Ix.Kernel.Key .source} (hT : T.Good (Ix.Kernel.KeyScope.ofId P)) (i : Nat) :
    envQ.findProj? (Ix.LeanIngress.Key.subst ρ T) i =
      (envS.findProj? T i).map (ProjEntry.substKeys ρ) := by
  unfold Ix.Kernel.Env.findProj?
  have hk := h.find (Ix.Kernel.projTableName T) hT
  simp only [Ix.Kernel.projTableName, Ix.Kernel.auxKey, Ix.LeanIngress.Key.subst] at hk ⊢
  rw [hk]
  cases envS.find? (.aux T .projTable) with
  | none => rfl
  | some c =>
    cases c with
    | projInfo tbl =>
      simp only [Option.map_some, Ix.LeanIngress.ConstantInfo.substKeys]
      have hn : (Ix.LeanIngress.ProjTable.substKeys ρ tbl).numFields = tbl.numFields := rfl
      rw [hn]
      split
      · simp [ProjTable.substKeys_entry]
      · rfl
    | _ => rfl

/-- **A good term denotes, in `envS`, what its `substKeys ρf` image denotes in a
related `envQ`**, at the pulled-back constant values `substCval ρf cval'`. -/
theorem Denotes.substPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρf envS envQ)
    {V : Type w} [SetTheory V]
    {cval' : Ix.Kernel.Key .source → (LevelParam → Nat) → V}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {e' : Ix.Kernel.Expr .source} {v : V}
    (hd : Ix.Kernel.Denotes cval' envQ φ ρ e' v) :
    ∀ {e : Ix.Kernel.Expr .source},
      e' = Ix.LeanIngress.Expr.substKeys ρf e →
      e.Good (Ix.Kernel.KeyScope.ofId P) →
      Ix.Kernel.Denotes (substCval ρf cval') envS φ ρ e v := by
  induction hd with
  | bvar =>
    intro e he _
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    subst he
    exact .bvar
  | sort =>
    intro e he _
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    subst he
    exact .sort
  | @const ρv n us ci hf hlen =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    rename_i m us'
    obtain ⟨rfl, rfl⟩ := he
    have hm : m.Good (Ix.Kernel.KeyScope.ofId P) := hg
    rw [h.find m hm] at hf
    obtain ⟨ci₀, hci₀, rfl⟩ := Option.map_eq_some_iff.mp hf
    have hlps : (Ix.LeanIngress.ConstantInfo.substKeys ρf ci₀).toConstantVal.levelParams =
        ci₀.toConstantVal.levelParams := by
      simp [Ix.LeanIngress.ConstantInfo.substKeys_toConstantVal]
    rw [hlps] at hlen ⊢
    exact .const hci₀ hlen
  | app _ _ ihf iha =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .app (ihf rfl hg.1) (iha rfl hg.2)
  | lam _ _ hP ihA ihF =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .lam (ihA rfl hg.1) (fun x hx => ihF x hx rfl hg.2) hP
  | pi _ _ hP ihA ihB =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .pi (ihA rfl hg.1) (fun x hx => ihB x hx rfl hg.2) hP
  | @proj_table ρv T i e₀ entry P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    obtain ⟨entry₀, hentry₀, rfl⟩ := Option.map_eq_some_iff.mp ht
    have hoff : (ProjEntry.substKeys ρf entry₀).off = entry₀.off := rfl
    rw [hoff]
    exact .proj_table hentry₀ (ihe rfl hg.2)
  | @proj_fst ρv T e₀ P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    exact .proj_fst (Option.map_eq_none_iff.mp ht) (ihe rfl hg.2)
  | @proj_snd ρv T e₀ P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    exact .proj_snd (Option.map_eq_none_iff.mp ht) (ihe rfl hg.2)
  | @natLit ρv n X _ ih =>
    intro e he _
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    subst he
    exact .natLit (ih (natLitToConstructor_substKeys ρf n).symm
      (Ix.Kernel.natLitToConstructor_good (Ix.Kernel.KeyScope.ofId_pre P) n))
  | @strLit ρv s X _ ih =>
    intro e he _
    cases e <;> simp [Ix.LeanIngress.Expr.substKeys] at he
    subst he
    exact .strLit (ih (strLitToConstructor_substKeys ρf s).symm
      (Ix.Kernel.strLitToConstructor_good (Ix.Kernel.KeyScope.ofId_pre P)
        (Ix.Kernel.KeyScope.ofId_str P) s))

/-- A constant's denotation at the pulled-back values is its substituted key's. -/
theorem Denotes.subst_const_push {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρf envS envQ)
    {V : Type w} [SetTheory V]
    {cval' : Ix.Kernel.Key .source → (LevelParam → Nat) → V}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {k : Ix.Kernel.Key .source} {us : List Ix.Kernel.Level} {v : V}
    (hd : Ix.Kernel.Denotes (substCval ρf cval') envS φ ρ (.const k us) v) :
    Ix.Kernel.Denotes cval' envQ φ ρ (.const (Ix.LeanIngress.Key.subst ρf k) us) v := by
  cases hd with
  | const hf hlen =>
    rename_i ci
    have hf' := h.find_some hf
    have hlps : (Ix.LeanIngress.ConstantInfo.substKeys ρf ci).toConstantVal.levelParams =
        ci.toConstantVal.levelParams := by
      simp [Ix.LeanIngress.ConstantInfo.substKeys_toConstantVal]
    have hd' := Ix.Kernel.Denotes.const (cval := cval') (φ := φ) (ρ := ρ) (us := us) hf'
      (by rw [hlps]; exact hlen)
    rw [hlps] at hd'
    exact hd'

/-- **A model of the quotient environment pulls back to the nominal environment**
along `Key.subst ρf`. -/
def Model.substPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρf envS envQ)
    {V : Type w} [SetTheory V] (M : Ix.Kernel.Model V envQ) :
    Ix.Kernel.Model V envS where
  cval := substCval ρf M.cval
  mem c hc φ ρ := by
    obtain ⟨T, hT, hmem⟩ := M.mem _ (h.mem hc) φ ρ
    have hty : (Ix.LeanIngress.ConstantInfo.substKeys ρf c).toConstantVal.type =
        Ix.LeanIngress.Expr.substKeys ρf c.toConstantVal.type := by
      simp [Ix.LeanIngress.ConstantInfo.substKeys_toConstantVal, Ix.LeanIngress.ConstantVal.substKeys_type]
    rw [hty] at hT
    refine ⟨T, Denotes.substPullback h hT rfl (h.all c hc).toConstantVal.2, ?_⟩
    have hn : (Ix.LeanIngress.ConstantInfo.substKeys ρf c).name =
        Ix.LeanIngress.Key.subst ρf c.name := Ix.LeanIngress.ConstantInfo.substKeys_name ρf c
    rw [hn] at hmem
    exact hmem
  false_empty φ ρ F hF := M.false_empty φ ρ F (Denotes.subst_const_push h hF)
  eq_equality u φ ρ E A a b hE := M.eq_equality u φ ρ E A a b (Denotes.subst_const_push h hE)

/-- **The definition-value clause pulls back along `Key.subst ρf`**. -/
theorem defn_value_substPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρf envS envQ)
    {V : Type w} [SetTheory V]
    {cval' : Ix.Kernel.Key .source → (LevelParam → Nat) → V}
    (hv : ∀ (cv : Ix.Kernel.ConstantVal .source) (value : Ix.Kernel.Expr .source)
      (hint : Ix.Kernel.ReducibilityHint),
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ envQ.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Ix.Kernel.Denotes cval' envQ φ ρ value (cval' cv.name φ)) :
    ∀ (cv : Ix.Kernel.ConstantVal .source) (value : Ix.Kernel.Expr .source)
      (hint : Ix.Kernel.ReducibilityHint),
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ envS.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Ix.Kernel.Denotes (substCval ρf cval') envS φ ρ value
          (substCval ρf cval' cv.name φ) := by
  intro cv value hint hc φ ρ
  have hc' := h.mem hc
  have hg := h.all _ hc
  exact Denotes.substPullback h (hv _ _ hint hc' φ ρ) rfl hg.2

/-- **A value model of `envQ` pulls back along `Key.subst ρf` to `envS`**. -/
def ValueModel.substPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    {V : Type w} [SetTheory V]
    (h : EnvSubstRel P ρf envS envQ) (N : ValueModel V envQ) : ValueModel V envS :=
  { Model.substPullback h N.toModel with
    defn_value := defn_value_substPullback h N.defn_value }

theorem ValueModel.substPullback_rel {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρf : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρf envS envQ) :
    ValueModel.Rel.{w} (Ix.LeanIngress.Key.subst ρf) envS envQ :=
  fun _ _ N => ⟨ValueModel.substPullback h N, fun _ _ => rfl⟩

/-- **Nominal-to-quotient value-model pullback along `Key.subst ρ`**: every
constant and lookup of `envS` maps into `envQ` under `ConstantInfo.substKeys ρ`,
and `ValueModel` (`Model` and `defn_value`) pulls back from `envQ` to `envS`
along `Key.subst ρ` without requiring `LawModel.Rel`. -/
structure EnvSubstModelPullback (ρ : Ix.LeanIngress.FiberMap) (envS envQ : Env .source) : Prop where
  mem : ∀ {c : Ix.Kernel.ConstantInfo .source},
    c ∈ envS.consts → Ix.LeanIngress.ConstantInfo.substKeys ρ c ∈ envQ.consts
  find_some : ∀ {k : Ix.Kernel.Key .source} {c : Ix.Kernel.ConstantInfo .source},
    envS.find? k = some c →
      envQ.find? (Ix.LeanIngress.Key.subst ρ k) =
        some (Ix.LeanIngress.ConstantInfo.substKeys ρ c)
  valueModel : ValueModel.Rel.{w} (Ix.LeanIngress.Key.subst ρ) envS envQ

/-- Construct `EnvSubstModelPullback` unconditionally from `EnvSubstRel`
(without `LawModel.Rel`). -/
theorem EnvSubstRel.toModelPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρ envS envQ) :
    EnvSubstModelPullback.{w} ρ envS envQ :=
  ⟨h.mem, h.find_some, ValueModel.substPullback_rel h⟩

/-- **Composing `EnvSubstModelPullback` with `EnvRel` gives a direct `ValueModel.Rel`
from `envS` to `envA` along `(Key.map f) ∘ (Key.subst ρ)`** without requiring
`LawModel.Rel`. -/
theorem EnvSubstModelPullback.comp_envRel_valueModel
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    {P : Ix.Kernel.Mode.Id .source → Prop}
    {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {envA : Env .anon}
    (hsub : EnvSubstModelPullback.{w} ρ envS envQ)
    (hrel : Ix.Kernel.EnvRel P f envQ envA) :
    ValueModel.Rel.{w}
      ((Ix.Kernel.Key.map f) ∘ (Ix.LeanIngress.Key.subst ρ)) envS envA :=
  ValueModel.comp hsub.valueModel (ValueModel.pullback_rel hrel)

/-- **Nominal-to-quotient semantic pullback along `Key.subst ρ`**: every constant
and lookup of `envS` maps into `envQ` under `ConstantInfo.substKeys ρ`, and both
`ValueModel` and `LawModel` pull back from `envQ` to `envS` along `Key.subst ρ`.

Note: Quotient Source (`CompileCorrect` + `Ix.LeanIngress.prepareSourceCollapsedAt_trace`)
is the primary unconditional security guarantee, transporting `ValueModel` and
`LawModel` unconditionally between `envQ` and `envA` while ensuring quotient
collapse only merges declarations that are structurally identical (`Declaration.beqF`,
hence `=`) under `Key.subst ρ`. `EnvSubstPullback` packages the hypotheses for
conditional model-theoretic corollaries that pull models of `envQ` back to a
nominal environment `envS` satisfying `EnvSubstRel` and `LawModel.Rel`. Deriving
`LawModel.Rel` from `EnvSubstRel` and discharging `EnvSubstRel` from
`Ix.LeanIngress.FiberAliasSafe` on closures whose alias fibers do not mix
reducibility hints is left for future work. -/
structure EnvSubstPullback (ρ : Ix.LeanIngress.FiberMap) (envS envQ : Env .source) : Prop
    extends EnvSubstModelPullback.{w} ρ envS envQ where
  lawModel : LawModel.Rel.{w} (Ix.LeanIngress.Key.subst ρ) envS envQ

/-- Upgrade `EnvSubstModelPullback` to `EnvSubstPullback` given `LawModel.Rel`. -/
theorem EnvSubstModelPullback.toPullback {ρ : Ix.LeanIngress.FiberMap}
    {envS envQ : Env .source}
    (h : EnvSubstModelPullback.{w} ρ envS envQ)
    (hlaw : LawModel.Rel.{w} (Ix.LeanIngress.Key.subst ρ) envS envQ) :
    EnvSubstPullback.{w} ρ envS envQ :=
  ⟨h, hlaw⟩

/-- Construct `EnvSubstPullback` from `EnvSubstRel` and `LawModel.Rel`. -/
theorem EnvSubstRel.toPullback {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρ envS envQ)
    (hlaw : LawModel.Rel.{w} (Ix.LeanIngress.Key.subst ρ) envS envQ) :
    EnvSubstPullback.{w} ρ envS envQ :=
  h.toModelPullback.toPullback hlaw

/-- Construct `EnvSubstPullback` from `EnvSubstRel` when `RecRuleLaws` and
`CapabilityLaws` hold on the pulled-back valuation `substCval ρ N.cval` for every
quotient `LawModel` `N`. -/
theorem EnvSubstRel.toPullback_of_laws {P : Ix.Kernel.Mode.Id .source → Prop}
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    (h : EnvSubstRel P ρ envS envQ)
    (hlaws : ∀ (V : Type w) [SetTheory V] (N : LawModel V envQ),
      RecRuleLaws (substCval ρ N.cval) envS ∧
        CapabilityLaws (substCval ρ N.cval) envS) :
    EnvSubstPullback.{w} ρ envS envQ :=
  h.toPullback fun V _ N =>
    ⟨{ ValueModel.substPullback h N.toValueModel with
       rec_rule := (hlaws V N).1
       caps := (hlaws V N).2 },
     fun _ _ => rfl⟩

/-- **Composing `EnvSubstPullback` with `EnvRel` gives a direct `ValueModel.Rel`
from `envS` to `envA` along `(Key.map f) ∘ (Key.subst ρ)`**. -/
theorem EnvSubstPullback.comp_envRel_valueModel
    {ρ : Ix.LeanIngress.FiberMap} {envS envQ : Env .source}
    {P : Ix.Kernel.Mode.Id .source → Prop}
    {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {envA : Env .anon}
    (hsub : EnvSubstPullback.{w} ρ envS envQ)
    (hrel : Ix.Kernel.EnvRel P f envQ envA) :
    ValueModel.Rel.{w}
      ((Ix.Kernel.Key.map f) ∘ (Ix.LeanIngress.Key.subst ρ)) envS envA :=
  hsub.toEnvSubstModelPullback.comp_envRel_valueModel hrel

/-- **Composite key map on a published Source name**: under a well-formed role table
`t` with `PublishedRolesBound t ixe`, for every Source name `i` published at
address `a` (`(sourceAddrs ixe)[i]? = some a`), the composite map
`(Key.map (evAddr ixe b)) ∘ (Key.subst (fiberAliasAt ixe (roleAtMap t)))` sends
`Key.ofName i` to `.role r` when `(roleAtMap t)[a]? = some r` (equivalently
`t.addressOf? r = some a`), and to `.id a` when `(roleAtMap t)[a]? = none`. -/
theorem evAddr_subst_key {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    (checked : t.check = .ok ()) (bound : PublishedRolesBound t ixe)
    (b : Ix.RoleEvidence.Bundle) {i : Ix.Kernel.Name} {a : Address}
    (hi : (sourceAddrs ixe)[i]? = some a) :
    (∃ r, (Ix.LeanIngress.roleAtMap t)[a]? = some r ∧ t.addressOf? r = some a ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.Kernel.Key.ofName i)).map (Ix.LeanIngress.evAddr ixe b) = .role r) ∨
    ((Ix.LeanIngress.roleAtMap t)[a]? = none ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.Kernel.Key.ofName i)).map (Ix.LeanIngress.evAddr ixe b) = .id a) := by
  have htb : Ix.LeanIngress.TableBound ixe (Ix.LeanIngress.roleAtMap t) :=
    tableBound_of checked bound
  have hne : (Ix.LeanIngress.fiberMembers (sourceAddrs ixe)).getD a [] ≠ [] := by
    intro h
    have := Ix.LeanIngress.mem_fiberMembers.mpr hi
    rw [h] at this
    cases this
  obtain ⟨rep, hrep⟩ :=
    Ix.LeanIngress.repAt_isSome (bound := (Ix.LeanIngress.roleAtMap t)[a]?) hne
      fun x hx r hxr => htb x r a (Ix.LeanIngress.mem_fiberMembers.mp hx) hxr
  have hsub := Ix.LeanIngress.fiberAliasAt_subst hi hrep
  rw [hsub]
  cases hr : (Ix.LeanIngress.roleAtMap t)[a]? with
  | some r =>
    left
    rw [hr] at hrep
    simp only [Ix.LeanIngress.repAt] at hrep
    split at hrep
    · cases hrep
      exact ⟨r, rfl, (Ix.LeanIngress.roleAtMap_spec checked).mp hr, rfl⟩
    · cases hrep
  | none =>
    right
    refine ⟨rfl, ?_⟩
    rw [hr] at hrep
    simp only [Ix.LeanIngress.repAt] at hrep
    obtain ⟨k, hk, hkr⟩ := Ix.LeanIngress.fiberRep_mem hrep
    have hka : (sourceAddrs ixe)[k]? = some a := Ix.LeanIngress.mem_fiberMembers.mp hk
    cases hrole : roleOf k with
    | some r =>
      have := htb k r a hka hrole
      rw [hr] at this
      cases this
    | none =>
      rw [Ix.LeanIngress.roleOf_eq_none hrole] at hkr
      subst hkr
      simp [Ix.LeanIngress.evAddr, hka]

/-- **Composite key map on a compiled user constant `n : Ix.Name`**: when
`(sourceAddrs ixe)[ingressName n]? = some a`, the composite map
`(Key.map (evAddr ixe b)) ∘ (Key.subst (fiberAliasAt ixe (roleAtMap t)))` sends
`ingressKey n` to `.role r` when `(roleAtMap t)[a]? = some r` (`t.addressOf? r = some a`)
and to `.id a` when `(roleAtMap t)[a]? = none`. -/
theorem evAddr_subst_ingressKey {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    (checked : t.check = .ok ()) (bound : PublishedRolesBound t ixe)
    (b : Ix.RoleEvidence.Bundle) {n : Ix.Name} {a : Address}
    (hn : (sourceAddrs ixe)[ingressName n]? = some a) :
    (∃ r, (Ix.LeanIngress.roleAtMap t)[a]? = some r ∧ t.addressOf? r = some a ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.LeanIngress.ingressKey n)).map (Ix.LeanIngress.evAddr ixe b) = .role r) ∨
    ((Ix.LeanIngress.roleAtMap t)[a]? = none ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.LeanIngress.ingressKey n)).map (Ix.LeanIngress.evAddr ixe b) = .id a) :=
  evAddr_subst_key checked bound b hn

/-- **Composite key map on a published entry `(n, d) ∈ ixe.named.toList`**: under
`PublishedAgree ixe`, the composite map sends `ingressKey n` to `.role r` when
`(roleAtMap t)[d.addr]? = some r` and to `.id d.addr` when
`(roleAtMap t)[d.addr]? = none`. -/
theorem evAddr_subst_named {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    (checked : t.check = .ok ()) (bound : PublishedRolesBound t ixe)
    (agree : PublishedAgree ixe) (b : Ix.RoleEvidence.Bundle)
    {n : Ix.Name} {d : Ixon.Named} (hmem : (n, d) ∈ ixe.named.toList) :
    (∃ r, (Ix.LeanIngress.roleAtMap t)[d.addr]? = some r ∧ t.addressOf? r = some d.addr ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.LeanIngress.ingressKey n)).map (Ix.LeanIngress.evAddr ixe b) = .role r) ∨
    ((Ix.LeanIngress.roleAtMap t)[d.addr]? = none ∧
      (Ix.LeanIngress.Key.subst
        (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.LeanIngress.ingressKey n)).map (Ix.LeanIngress.evAddr ixe b) = .id d.addr) :=
  evAddr_subst_ingressKey checked bound b (agree n d hmem)

end Ix.Cert
