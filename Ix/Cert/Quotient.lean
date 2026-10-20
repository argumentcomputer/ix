import Ix.Cert.Statement
import Ix.LeanIngress.Rename
import IxC.Kernel.Verify.Rename.Model
import IxC.Kernel.Ixon.ReaderSpec

/-! # Quotient Source at the artifact's addresses: the statements' side (step 7.3 (iv))

IxC renames a quotient Source accept to the artifact's addresses
(`Ix.LeanIngress.acceptsRef_addrOf`, and its table-rule form at `fiberAliasAt`), with the
two environments related key by key (`Ix.Kernel.EnvRel`). This module supplies what
the statements need around it:

* `ValueModel.pullback`: a value model of the renamed environment is one of the
  quotient environment (IxC's `Model.pullback` and `defn_value_pullback`);
* `tableBound_of`: the table rule's premise `Ix.LeanIngress.TableBound` at the admitted
  table's inverse (`roleAtMap`), from a decidable check of the artifact,
  `PublishedRolesBound` (every published name whose ingress name is a role's Lean name
  sits at the table's address for that role). B5a's `RolesBound` does not give it: it
  looks names up by their stored hashes (`Ix.Name`'s `==`) and covers the roles the
  input declares, while a fiber is made of every published name, compared by ingress
  name;
* `publishedAddress_id`, `reading_id`: the address the statements read a source name
  at (`publishedAddress`) is the one IxC renames it to (`addrOf`), when every
  published name agrees with the artifact's address map (`PublishedAgree`, decided);
  and its reading is the role key the table binds there or the address itself
  (`Ix.Kernel.Reader.Ctx.keyAt_ok`). -/

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
trusted (B5a's `RolesBound` looks the declared roles' names up by their hashes). -/
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

end Ix.Cert
