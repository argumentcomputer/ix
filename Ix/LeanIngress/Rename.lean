import Ix.LeanIngress
import IxC.Kernel.Verify.Rename.Fold
import IxC.Kernel.Verify.Frontend.Prepare
import IxC.Kernel.Ixon.RoleTableInj

/-! # Quotient Source under the artifact's addresses (step 7.3, chunk (iv))

Quotient Source runs on representatives: every input key is renamed onto its
alias fiber's representative (`Key.subst (fiberAlias ixe)`). Renaming a
representative to its address (`addrOf ixe`) is injective
(`addrOf_injOn`): two representatives at one address are one key
(`fiberAlias_addr_inj`), provided no fiber holds two roles' names
(`FibersRoleFree`). So reference acceptance of a quotient run carries over to
the run at addresses (`acceptsRef_addrOf`, from `Ix.Kernel.Cached.AcceptsRef.rename`).

The input side: a key whose ids are published names, none a role's Lean
name (`QIn`), renames onto representatives (`QRep`), and so does every term,
constant, declaration and evidence entry built from such keys
(`Declaration.substKeys_good`, `evidenceSubst_good`). -/

namespace Ix.LeanIngress

open Ix.Kernel

universe w

variable {ixe : Ixon.Env}

/-! ## Representatives and their addresses -/

/-- **The address of a published name** (the default address for an
unpublished one). -/
def addrOf (ixe : Ixon.Env) : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon :=
  fun n => ((sourceAddrs ixe)[n]?).getD default

/-- **No fiber holds two roles' names** (the hypothesis of
`fiberAlias_addr_inj`, at every address). -/
def FibersRoleFree (ixe : Ixon.Env) : Prop :=
  ∀ a x y r₁ r₂, (sourceAddrs ixe)[x]? = some a → (sourceAddrs ixe)[y]? = some a →
    roleOf x = some r₁ → roleOf y = some r₂ → r₁ = r₂

/-- **An input name**: published, and no role's Lean name. -/
def QIn (ixe : Ixon.Env) (n : Ix.Kernel.Mode.Id .source) : Prop :=
  roleOf n = none ∧ ((sourceAddrs ixe)[n]?).isSome

/-- **A representative**: an input name its fiber map fixes. -/
def QRep (ixe : Ixon.Env) (n : Ix.Kernel.Mode.Id .source) : Prop :=
  QIn ixe n ∧ Key.subst (fiberAlias ixe) (.id n) = .id n


/-! ## Addresses and the published names -/

theorem sourceAddrs_foldl :
    ∀ (l : List (Ix.Name × Ixon.Named)) (init : Std.HashMap Ix.Kernel.Name Address)
      {n : Ix.Kernel.Name} {a : Address},
      (l.foldl (fun m p => m.insert (ingressName p.1) p.2.addr) init)[n]? = some a →
        init[n]? = some a ∨ ∃ p ∈ l, ingressName p.1 = n ∧ p.2.addr = a
  | [], _, _, _, h => Or.inl h
  | p :: l, init, n, a, h => by
    rw [List.foldl_cons] at h
    rcases sourceAddrs_foldl l _ h with h | ⟨q, hq, h1, h2⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        exact Or.inr ⟨p, List.mem_cons_self, beq_iff_eq.mp he, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- **A Source name's address is a published name's**: the entry of
`ixe.named` the ingress names `n`. -/
theorem sourceAddrs_spec {n : Ix.Kernel.Name} {a : Address} (h : (sourceAddrs ixe)[n]? = some a) :
    ∃ m d, (m, d) ∈ ixe.named.toList ∧ ingressName m = n ∧ d.addr = a := by
  unfold sourceAddrs at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  rcases sourceAddrs_foldl _ _ h with h | ⟨⟨m, d⟩, hm, h1, h2⟩
  · simp at h
  · exact ⟨m, d, hm, h1, h2⟩

/-- `addrOf` at a published name is its address. -/
theorem addrOf_eq {n : Ix.Kernel.Name} {a : Address} (h : (sourceAddrs ixe)[n]? = some a) :
    addrOf ixe n = a := by
  simp [addrOf, h]
/-- **Renaming representatives to their addresses is injective.** -/
theorem addrOf_injOn (hroles : FibersRoleFree ixe) :
    Ix.Kernel.InjOn (md := .source) (md' := .anon) (addrOf ixe) (QRep ixe) := by
  intro i j hi hj hij
  obtain ⟨⟨hri, hai⟩, hfi⟩ := hi
  obtain ⟨⟨hrj, haj⟩, hfj⟩ := hj
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hai
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp haj
  have hab : a = b := by simpa [addrOf, ha, hb] using hij
  subst hab
  have h := fiberAlias_addr_inj ha hb (fun x y r₁ r₂ hx hy => hroles a x y r₁ r₂ hx hy)
  rw [roleOf_eq_none hri, roleOf_eq_none hrj, hfi, hfj] at h
  cases h
  rfl

/-- **Reference acceptance at the artifact's addresses**: a quotient run whose
keys are representatives, renamed to their addresses, is accepted at the same
fuel, installing an environment that answers every lookup at a renamed key
with the renamed constant. -/
theorem acceptsRef_addrOf (μ : Ix.Kernel.CheckMode) (hroles : FibersRoleFree ixe)
    {ev : Ix.Kernel.Evidences .source} (hev : ev.Good (KeyScope.ofId (QRep ixe))) {ds : List (Ix.Kernel.Declaration .source)}
    (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId (QRep ixe))) {envS : Ix.Kernel.Env .source}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds envS) :
    ∃ envA, Ix.Kernel.Cached.AcceptsRef μ (ev.mapKeys (addrOf ixe))
        (ds.map (Ix.Kernel.Declaration.mapKeys (addrOf ixe))) envA ∧
      Ix.Kernel.EnvRel (QRep ixe) (addrOf ixe) envS envA :=
  Ix.Kernel.Cached.AcceptsRef.rename μ (addrOf_injOn hroles) hev hds h

/-! ## The input side -/

/-- **An input key renames onto representatives.** -/
theorem Key.subst_good (hroles : FibersRoleFree ixe) :
    ∀ {k : Ix.Kernel.Key .source}, k.Good (KeyScope.ofId (QIn ixe)) → (Key.subst (fiberAlias ixe) k).Good (KeyScope.ofId (QRep ixe))
  | .id n, hk => by
    obtain ⟨hrn, han⟩ := hk
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp han
    cases hfa : (fiberAlias ixe)[n]? with
    | none =>
      have hfix : Key.subst (fiberAlias ixe) (.id n) = .id n := by
        simp only [Key.subst, hfa, Option.getD_none]
      rw [hfix]
      exact ⟨⟨hrn, han⟩, hfix⟩
    | some rep =>
      have hsub : Key.subst (fiberAlias ixe) (.id n) = rep := by
        simp only [Key.subst, hfa, Option.getD_some]
      rw [hsub]
      obtain ⟨m, hm, hmrep⟩ := fiberAlias_rep_addr ha hfa
      cases hrm : roleOf m with
      | some r =>
        rw [roleOf_eq_some hrm] at hmrep
        subst hmrep
        trivial
      | none =>
        rw [roleOf_eq_none hrm] at hmrep
        subst hmrep
        have h := fiberAlias_addr_inj hm ha (fun x y r₁ r₂ hx hy => hroles a x y r₁ r₂ hx hy)
        rw [roleOf_eq_none hrm, roleOf_eq_none hrn, hsub] at h
        exact ⟨⟨hrm, by rw [hm]; rfl⟩, h⟩
  | .role _, _ => trivial
  | .aux k _, hk => Key.subst_good hroles (k := k) hk

section Structural

variable {ρ : FiberMap} {P Q : Ix.Kernel.Mode.Id .source → Prop}
  (hK : ∀ k : Ix.Kernel.Key .source, k.Good (KeyScope.ofId P) → (Key.subst ρ k).Good (KeyScope.ofId Q))
include hK

theorem Expr.substKeys_good : ∀ {e : Ix.Kernel.Expr .source}, e.Good (KeyScope.ofId P) → (Expr.substKeys ρ e).Good (KeyScope.ofId Q)
  | .bvar _, _ => trivial
  | .fvar _ t, h => Expr.substKeys_good (e := t) h
  | .sort _, _ => trivial
  | .const n _, h => hK n h
  | .app a b, h => ⟨Expr.substKeys_good (e := a) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .lam t b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .forallE t b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .letE t v b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := v) h.2.1,
      Expr.substKeys_good (e := b) h.2.2⟩
  | .lit (.natVal _), _ => trivial
  | .lit (.strVal _), _ => fun _ _ => trivial
  | .proj s _ e, h => ⟨hK s h.1, Expr.substKeys_good (e := e) h.2⟩

theorem Expr.GoodList.substKeys {es : List (Ix.Kernel.Expr .source)} (h : Expr.GoodList (KeyScope.ofId P) es) :
    Expr.GoodList (KeyScope.ofId Q) (es.map (Expr.substKeys ρ)) := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨e₀, h₀, rfl⟩ := he
  exact Expr.substKeys_good hK (h e₀ h₀)

theorem ConstantVal.substKeys_good {cv : Ix.Kernel.ConstantVal .source} (h : cv.Good (KeyScope.ofId P)) :
    (ConstantVal.substKeys ρ cv).Good (KeyScope.ofId Q) :=
  ⟨hK _ h.1, Expr.substKeys_good hK h.2⟩

theorem RecRule.substKeys_good {r : Ix.Kernel.RecRule .source} (h : r.Good (KeyScope.ofId P)) :
    (RecRule.substKeys ρ r).Good (KeyScope.ofId Q) := by
  refine ⟨hK _ h.1, ?_, Expr.substKeys_good hK h.2.2⟩
  have h2 := h.2.1
  unfold RecRule.substKeys RecRuleFire.substKeys
  cases hf : r.fire with
  | inert => trivial
  | plain => trivial
  | nested lvls pins =>
    rw [hf] at h2
    exact Expr.GoodList.substKeys hK h2

theorem ConstantInfo.substKeys_good {c : Ix.Kernel.ConstantInfo .source} (h : c.Good (KeyScope.ofId P)) :
    (ConstantInfo.substKeys ρ c).Good (KeyScope.ofId Q) := by
  cases c with
  | axiomInfo v => exact ConstantVal.substKeys_good hK h
  | defnInfo v e _ => exact ⟨ConstantVal.substKeys_good hK h.1, Expr.substKeys_good hK h.2⟩
  | thmInfo v e => exact ⟨ConstantVal.substKeys_good hK h.1, Expr.substKeys_good hK h.2⟩
  | indInfo v caps =>
    refine ⟨ConstantVal.substKeys_good hK h.1, ?_⟩
    intro k hk
    simp only [IndCaps.substKeys, Option.mem_def, Option.map_eq_some_iff]
      at hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    exact hK _ (h.2 k₀ hk₀)
  | ctorInfo v _ _ => exact ConstantVal.substKeys_good hK h
  | recInfo v _ _ rules =>
    refine ⟨ConstantVal.substKeys_good hK h.1, ?_⟩
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact RecRule.substKeys_good hK (h.2 r₀ hr₀)
  | projInfo t =>
    refine ⟨hK _ h.1, hK _ h.2.1, ?_⟩
    intro b hb
    simp only [ProjTable.substKeys, Array.mem_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact Expr.substKeys_good hK (h.2.2 b₀ hb₀)

theorem Declaration.substKeys_good {d : Ix.Kernel.Declaration .source} (h : d.Good (KeyScope.ofId P)) :
    (Declaration.substKeys ρ d).Good (KeyScope.ofId Q) := by
  cases d with
  | axiomDecl v => exact ConstantVal.substKeys_good hK h
  | defnDecl v e _ => exact ⟨ConstantVal.substKeys_good hK h.1, Expr.substKeys_good hK h.2⟩
  | thmDecl v e => exact ⟨ConstantVal.substKeys_good hK h.1, Expr.substKeys_good hK h.2⟩
  | opaqueDecl v e => exact ⟨ConstantVal.substKeys_good hK h.1, Expr.substKeys_good hK h.2⟩
  | basisDecl _ => trivial
  | indDecl block _ =>
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact ConstantInfo.substKeys_good hK (h c₀ hc₀)
  | quotDecl _ v => exact ConstantVal.substKeys_good hK h

theorem evidenceSubst_good {ev : Ix.Kernel.Evidences .source} (h : ev.Good (KeyScope.ofId P)) :
    (evidenceSubst ρ ev).Good (KeyScope.ofId Q) := by
  intro p hp e he
  simp only [evidenceSubst, List.mem_map] at hp
  obtain ⟨⟨r, es⟩, hp₀, rfl⟩ := hp
  simp only [List.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  have h₀ := h _ hp₀ e₀ he₀
  cases e₀ with
  | defeq => trivial
  | proof kv =>
    obtain ⟨k, v⟩ := kv
    exact ⟨hK _ h₀.1, Expr.substKeys_good hK h₀.2⟩

end Structural


/-! ## The collapse -/

/-- An invariant of a `for` loop in `Except`: preserved by every step whose
element satisfies `Q`, it holds of the loop's result. -/
theorem forIn_except_inv {α σ ε : Type} (I : σ → Prop) (Q : α → Prop)
    (f : α → σ → Except ε (ForInStep σ))
    (hf : ∀ a s r, Q a → I s → f a s = .ok r →
      I (match r with | .done b => b | .yield b => b)) :
    ∀ (l : List α) (init : σ), (∀ a ∈ l, Q a) → I init → ∀ s, forIn l init f = .ok s → I s
  | [], init, _, hi, s, h => by
    simp only [List.forIn_nil] at h
    cases h
    exact hi
  | a :: l, init, hl, hi, s, h => by
    rw [List.forIn_cons] at h
    cases hfa : f a init with
    | error e =>
      rw [hfa] at h
      cases h
    | ok r =>
      rw [hfa] at h
      have hr := hf a init r (hl a List.mem_cons_self) hi hfa
      cases r with
      | done b =>
        cases h
        exact hr
      | yield b =>
        exact forIn_except_inv I Q f hf l b (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hr s h

/-- **The collapse keeps renamed inputs**: every kept declaration is an
input declaration with its keys renamed. -/
theorem collapseDecls_kept {ρ : FiberMap} {ds : Array (Ix.Kernel.Declaration .source)}
    {c : Collapsed} (h : collapseDecls ρ ds = .ok c) :
    ∀ d' ∈ c.decls, ∃ d ∈ ds, d' = Declaration.substKeys ρ d := by
  unfold collapseDecls at h
  dsimp only at h
  generalize hloop : forIn (m := Except CollapseError) ds _ _ = r at h
  cases r with
  | error e => cases h
  | ok s =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [← Array.forIn_toList] at hloop
    refine forIn_except_inv
      (fun s : CollapseState × Array (Ix.Kernel.Key .source × Ix.Kernel.Key .source) =>
        ∀ x ∈ s.1.kept, ∃ d ∈ ds, x = Declaration.substKeys ρ d)
      (fun d => d ∈ ds) _ ?_ ds.toList _ (fun d hd => Array.mem_toList_iff.mp hd)
      (by intro x hx; simp at hx) s hloop
    intro a st r ha hst hr
    obtain ⟨cs, dropped⟩ := st
    dsimp only at hr hst
    generalize hs : cs.step (a.names.head?.getD (.id .anonymous)) (Declaration.substKeys ρ a) = p at hr
    obtain ⟨cs', res⟩ := p
    cases res with
    | error e => simp [bind, Except.bind] at hr
    | ok b =>
      have hinv : ∀ x ∈ cs'.kept, ∃ d ∈ ds, x = Declaration.substKeys ρ d := by
        intro x hx
        rw [CollapseState.step_kept hs] at hx
        split at hx
        · rcases Array.mem_push.mp hx with hx | rfl
          · exact hst x hx
          · exact ⟨a, ha, rfl⟩
        · exact hst x hx
      cases b <;> simp [bind, Except.bind, pure, Except.pure] at hr <;> subst hr <;> exact hinv

/-- **The collapse at the artifact's fibers renames input keys onto
representatives**: declarations whose keys name input names (`QIn`) collapse
to declarations whose keys are representatives (`QRep`). -/
theorem collapseDecls_good (hroles : FibersRoleFree ixe) {ds : Array (Ix.Kernel.Declaration .source)}
    {c : Collapsed} (h : collapseDecls (fiberAlias ixe) ds = .ok c)
    (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId (QIn ixe))) : ∀ d ∈ c.decls, d.Good (KeyScope.ofId (QRep ixe)) := by
  intro d' hd'
  obtain ⟨d, hd, rfl⟩ := collapseDecls_kept h d' hd'
  exact Declaration.substKeys_good (fun _ hk => Key.subst_good hroles hk) (hds d hd)

/-! ## The table rule (`fiberAliasAt`)

The same results with the role read off the table (`fiberAliasAt ixe roles`,
`roles` the table's inverse `roleAtMap t`): injectivity needs only that every
published role name sits at its role's bound address (`TableBound`), which a
well-formed table gives together with the statements' decided
`PublishedRolesBound` (`Ix.Cert.tableBound_of`, through `roleAtMap_spec`). -/

section TableRule

variable {roles : Std.HashMap Address Ix.Kernel.Role}

/-- **A representative under the table rule**: an input name its fiber map
fixes. -/
def QRepAt (ixe : Ixon.Env) (roles : Std.HashMap Address Ix.Kernel.Role)
    (n : Ix.Kernel.Mode.Id .source) : Prop :=
  QIn ixe n ∧ Key.subst (fiberAliasAt ixe roles) (.id n) = .id n

/-- **Renaming representatives to their addresses is injective** under the
table rule. -/
theorem addrOf_injOnAt (hb : TableBound ixe roles) :
    Ix.Kernel.InjOn (md := .source) (md' := .anon) (addrOf ixe) (QRepAt ixe roles) := by
  intro i j hi hj hij
  obtain ⟨⟨hri, hai⟩, hfi⟩ := hi
  obtain ⟨⟨hrj, haj⟩, hfj⟩ := hj
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hai
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp haj
  have hab : a = b := by simpa [addrOf, ha, hb'] using hij
  subst hab
  have h := fiberAliasAt_addr_inj hb ha hb'
  rw [roleOf_eq_none hri, roleOf_eq_none hrj, hfi, hfj] at h
  cases h
  rfl

/-- **Reference acceptance at the artifact's addresses**, under the table rule. -/
theorem acceptsRef_addrOfAt (μ : Ix.Kernel.CheckMode) (hb : TableBound ixe roles)
    {ev : Ix.Kernel.Evidences .source} (hev : ev.Good (KeyScope.ofId (QRepAt ixe roles)))
    {ds : List (Ix.Kernel.Declaration .source)} (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe roles)))
    {envS : Ix.Kernel.Env .source} (h : Ix.Kernel.Cached.AcceptsRef μ ev ds envS) :
    ∃ envA, Ix.Kernel.Cached.AcceptsRef μ (ev.mapKeys (addrOf ixe))
        (ds.map (Ix.Kernel.Declaration.mapKeys (addrOf ixe))) envA ∧
      Ix.Kernel.EnvRel (QRepAt ixe roles) (addrOf ixe) envS envA :=
  Ix.Kernel.Cached.AcceptsRef.rename μ (addrOf_injOnAt hb) hev hds h

/-- **An input key renames onto representatives** under the table rule. -/
theorem Key.subst_goodAt (hb : TableBound ixe roles) :
    ∀ {k : Ix.Kernel.Key .source}, k.Good (KeyScope.ofId (QIn ixe)) →
      (Key.subst (fiberAliasAt ixe roles) k).Good (KeyScope.ofId (QRepAt ixe roles))
  | .id n, hk => by
    obtain ⟨hrn, han⟩ := hk
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp han
    cases hfa : (fiberAliasAt ixe roles)[n]? with
    | none =>
      have hfix : Key.subst (fiberAliasAt ixe roles) (.id n) = .id n := by
        simp only [Key.subst, hfa, Option.getD_none]
      rw [hfix]
      exact ⟨⟨hrn, han⟩, hfix⟩
    | some rep =>
      have hsub : Key.subst (fiberAliasAt ixe roles) (.id n) = rep := by
        simp only [Key.subst, hfa, Option.getD_some]
      rw [hsub]
      rcases fiberAliasAt_rep_addr ha hfa with ⟨m, hm, hmrep⟩ | ⟨r, rfl⟩
      · cases hrm : roleOf m with
        | some r =>
          rw [roleOf_eq_some hrm] at hmrep
          subst hmrep
          trivial
        | none =>
          rw [roleOf_eq_none hrm] at hmrep
          subst hmrep
          have h := fiberAliasAt_addr_inj hb hm ha
          rw [roleOf_eq_none hrm, roleOf_eq_none hrn, hsub] at h
          exact ⟨⟨hrm, by rw [hm]; rfl⟩, h⟩
      · trivial
  | .role _, _ => trivial
  | .aux k _, hk => Key.subst_goodAt hb (k := k) hk

/-- The collapse at the table rule's fibers renames input keys onto
representatives. -/
theorem collapseDecls_goodAt (hb : TableBound ixe roles)
    {ds : Array (Ix.Kernel.Declaration .source)} {c : Collapsed}
    (h : collapseDecls (fiberAliasAt ixe roles) ds = .ok c)
    (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId (QIn ixe))) : ∀ d ∈ c.decls, d.Good (KeyScope.ofId (QRepAt ixe roles)) := by
  intro d' hd'
  obtain ⟨d, hd, rfl⟩ := collapseDecls_kept h d' hd'
  exact Declaration.substKeys_good (fun _ hk => Key.subst_goodAt hb hk) (hds d hd)

end TableRule

/-! ### The table's inverse -/

theorem foldl_insert_snd_of_mem :
    ∀ (l : List (Ix.Kernel.Role × Address)) (m : Std.HashMap Address Ix.Kernel.Role) {a : Address}
      {r : Ix.Kernel.Role},
      (l.foldl (fun m p => m.insert p.2 p.1) m)[a]? = some r → (r, a) ∈ l ∨ m[a]? = some r
  | [], _, _, _, h => Or.inr h
  | p :: l, m, a, r, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insert_snd_of_mem l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        obtain ⟨p1, p2⟩ := p
        simp only [beq_iff_eq] at he
        subst he
        exact Or.inl List.mem_cons_self
      · exact Or.inr h

theorem foldl_insert_snd_not_mem :
    ∀ (l : List (Ix.Kernel.Role × Address)) (m : Std.HashMap Address Ix.Kernel.Role) {a : Address},
      a ∉ l.map (·.2) → (l.foldl (fun m p => m.insert p.2 p.1) m)[a]? = m[a]?
  | [], _, _, _ => rfl
  | p :: l, m, a, h => by
    rw [List.foldl_cons, foldl_insert_snd_not_mem l _ (fun hm => h (List.mem_cons_of_mem _ hm)),
      Std.HashMap.getElem?_insert]
    have hne : (p.2 == a) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      exact h (he ▸ List.mem_cons_self)
    simp [hne]

theorem foldl_insert_snd_of_mem' :
    ∀ (l : List (Ix.Kernel.Role × Address)) (m : Std.HashMap Address Ix.Kernel.Role) {a : Address}
      {r : Ix.Kernel.Role}, (l.map (·.2)).Nodup → (r, a) ∈ l →
      (l.foldl (fun m p => m.insert p.2 p.1) m)[a]? = some r
  | [], _, _, _, _, h => nomatch h
  | p :: l, m, a, r, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rw [foldl_insert_snd_not_mem l _ hn.1, Std.HashMap.getElem?_insert_self]
    · exact foldl_insert_snd_of_mem' l _ hn.2 h

/-- **The table's inverse is its binding**: under a well-formed table, the role
`roleAtMap t` gives an address is the role the table binds there. -/
theorem roleAtMap_spec {t : Ix.Kernel.RoleTable} (h : t.check = .ok ()) {a : Address}
    {r : Ix.Kernel.Role} : (roleAtMap t)[a]? = some r ↔ t.addressOf? r = some a := by
  obtain ⟨hroles, haddrs⟩ := Ix.Kernel.RoleTable.check_nodup h
  have hmem : (roleAtMap t)[a]? = some r ↔ (r, a) ∈ t.bound.toList := by
    unfold roleAtMap
    rw [← Array.foldl_toList]
    constructor
    · intro hr
      rcases foldl_insert_snd_of_mem _ _ hr with hr | hr
      · exact hr
      · simp at hr
    · exact foldl_insert_snd_of_mem' _ _ haddrs
  rw [hmem]
  unfold Ix.Kernel.RoleTable.addressOf?
  constructor
  · intro hm
    cases hf : t.bound.find? (·.1 == r) with
    | none =>
      have := Array.find?_eq_none.mp hf (r, a) (Array.mem_toList_iff.mp hm)
      simp at this
    | some q =>
      have hq1 : q.1 = r := by simpa using Array.find?_some hf
      have hqm := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hf)
      have heq : q = (r, a) := by
        have := Ix.Kernel.RoleTable.eq_of_nodup_map_snd (l := t.bound.toList.map fun p => (p.2, p.1))
          (p := (q.2, q.1)) (q := (a, r)) (by simpa [List.map_map, Function.comp_def] using hroles)
          (List.mem_map.mpr ⟨q, hqm, rfl⟩) (List.mem_map.mpr ⟨(r, a), hm, rfl⟩) hq1
        obtain ⟨q1, q2⟩ := q
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2]
      simp [heq]
  · intro hf
    obtain ⟨q, hq, hqa⟩ := Option.map_eq_some_iff.mp hf
    have hq1 : q.1 = r := by simpa using Array.find?_some hq
    have hqm := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hq)
    obtain ⟨q1, q2⟩ := q
    simp only at hq1 hqa
    subst hq1 hqa
    exact hqm

/-! ## The bundle's evidence at the artifact's addresses -/

section Bundle

variable {b : Ix.RoleEvidence.Bundle}

theorem bundleAddrs_foldl :
    ∀ (l : List (Address × Lean.Name)) (init : Std.HashMap Ix.Kernel.Name Address)
      {n : Ix.Kernel.Name} {a : Address},
      (l.foldl (fun m p => m.insert (Ix.Kernel.Name.ofLeanName p.2) p.1) init)[n]? = some a →
        init[n]? = some a ∨ ∃ p ∈ l, Ix.Kernel.Name.ofLeanName p.2 = n ∧ p.1 = a
  | [], _, _, _, h => Or.inl h
  | p :: l, init, n, a, h => by
    rw [List.foldl_cons] at h
    rcases bundleAddrs_foldl l _ h with h | ⟨q, hq, h1, h2⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        exact Or.inr ⟨p, List.mem_cons_self, beq_iff_eq.mp he, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- **A bundle address is a bundle name's**. -/
theorem bundleAddrs_spec {n : Ix.Kernel.Name} {a : Address} (h : (bundleAddrs b)[n]? = some a) :
    ∃ m, b.names[a]? = some m ∧ Ix.Kernel.Name.ofLeanName m = n := by
  unfold bundleAddrs at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  rcases bundleAddrs_foldl _ _ h with h | ⟨⟨a', m⟩, hm, h1, h2⟩
  · simp at h
  · simp only at h1 h2
    subst h2
    exact ⟨m, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm, h1⟩

/-- **Two bundle names at one bundle address are one name**: the names table maps each
address to one name (no collision resistance assumed). -/
theorem bundleAddrs_inj {i j : Ix.Kernel.Name} {a : Address} (hi : (bundleAddrs b)[i]? = some a)
    (hj : (bundleAddrs b)[j]? = some a) : i = j := by
  obtain ⟨m, hm, rfl⟩ := bundleAddrs_spec hi
  obtain ⟨m', hm', rfl⟩ := bundleAddrs_spec hj
  rw [hm] at hm'
  cases hm'
  rfl

theorem publishedAddrs_foldl :
    ∀ (l : List (Ix.Kernel.Name × Address)) (init : Std.HashSet Address) {a : Address},
      (l.foldl (fun s p => s.insert p.2) init).contains a = true →
        init.contains a = true ∨ ∃ p ∈ l, p.2 = a
  | [], _, _, h => Or.inl h
  | p :: l, init, a, h => by
    rw [List.foldl_cons] at h
    rcases publishedAddrs_foldl l _ h with h | ⟨q, hq, h1⟩
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inr ⟨p, List.mem_cons_self, beq_iff_eq.mp h⟩
      · exact Or.inl h
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h1⟩

/-- An address the artifact publishes is a published name's. -/
theorem publishedAddrs_spec {a : Address} (h : (publishedAddrs ixe).contains a = true) :
    ∃ m : Ix.Kernel.Name, (sourceAddrs ixe)[m]? = some a := by
  unfold publishedAddrs at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  rcases publishedAddrs_foldl _ _ h with h | ⟨⟨m, a'⟩, hm, h1⟩
  · simp at h
  · simp only at h1
    subst h1
    exact ⟨m, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm⟩

theorem publishedAddrs_foldl_of :
    ∀ (l : List (Ix.Kernel.Name × Address)) (init : Std.HashSet Address) {a : Address}
      {m : Ix.Kernel.Name}, (init.contains a = true ∨ (m, a) ∈ l) →
        (l.foldl (fun s p => s.insert p.2) init).contains a = true
  | [], _, _, _, h => by
    rcases h with h | h
    · exact h
    · cases h
  | p :: l, init, a, m, h => by
    rw [List.foldl_cons]
    apply publishedAddrs_foldl_of l _ (m := m)
    rcases h with h | h
    · left
      rw [Std.HashSet.contains_insert]
      simp [h]
    · rcases List.mem_cons.mp h with h | h
      · left
        rw [Std.HashSet.contains_insert, ← h]
        simp
      · exact Or.inr h

theorem publishedAddrs_of {m : Ix.Kernel.Name} {a : Address} (h : (sourceAddrs ixe)[m]? = some a) :
    (publishedAddrs ixe).contains a = true := by
  unfold publishedAddrs
  rw [Std.HashMap.fold_eq_foldl_toList]
  exact publishedAddrs_foldl_of _ _ (m := m)
    (Or.inr (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h))

/-- **A bundle-only name**: no role's, unpublished, and in the bundle. -/
def BundleOnly (ixe : Ixon.Env) (b : Ix.RoleEvidence.Bundle) (n : Ix.Kernel.Mode.Id .source) : Prop :=
  roleOf n = none ∧ (sourceAddrs ixe)[n]? = none ∧ ((bundleAddrs b)[n]?).isSome

/-- **The joined renaming**: a published name to its address, a bundle name
the artifact does not publish to its bundle address. -/
def evAddr (ixe : Ixon.Env) (b : Ix.RoleEvidence.Bundle) :
    Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon :=
  fun n => match (sourceAddrs ixe)[n]? with
    | some a => a
    | none => ((bundleAddrs b)[n]?).getD default

/-- `bundleDisjointB`, read: a bundle-only name's address is no published name's. -/
theorem bundleDisjointB_spec (h : bundleDisjointB ixe b = true) {n : Ix.Kernel.Name} {a : Address}
    (hn : (sourceAddrs ixe)[n]? = none) (ha : (bundleAddrs b)[n]? = some a) :
    ∀ m : Ix.Kernel.Name, (sourceAddrs ixe)[m]? ≠ some a := by
  intro m hm
  unfold bundleDisjointB at h
  have hmem : (n, a) ∈ (bundleAddrs b).toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ha
  have := List.all_eq_true.mp h _ hmem
  simp only [Std.HashMap.contains_eq_isSome_getElem?, hn, Option.isSome_none, Bool.false_or,
    Bool.not_eq_true'] at this
  rw [publishedAddrs_of hm] at this
  cases this

/-- **The joined renaming is injective** on representatives and bundle-only
names, when every published role name sits at its role's bound address and the
bundle is disjoint from the artifact. -/
theorem evAddr_injOn {roles : Std.HashMap Address Ix.Kernel.Role} (hb : TableBound ixe roles)
    (hd : bundleDisjointB ixe b = true) :
    Ix.Kernel.InjOn (md := .source) (md' := .anon) (evAddr ixe b)
      (fun n => QRepAt ixe roles n ∨ BundleOnly ixe b n) := by
  intro i j hi hj hij
  have hq : ∀ {n}, QRepAt ixe roles n → ∃ a, (sourceAddrs ixe)[n]? = some a ∧ evAddr ixe b n = a :=
    fun {n} hn => by
      obtain ⟨⟨_, han⟩, _⟩ := hn
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp han
      exact ⟨a, ha, by simp [evAddr, ha]⟩
  have hbo : ∀ {n}, BundleOnly ixe b n →
      ∃ a, (sourceAddrs ixe)[n]? = none ∧ (bundleAddrs b)[n]? = some a ∧ evAddr ixe b n = a :=
    fun {n} hn => by
      obtain ⟨_, hns, hnb⟩ := hn
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hnb
      exact ⟨a, hns, ha, by simp [evAddr, hns, ha]⟩
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact addrOf_injOnAt hb hi hj (by
      obtain ⟨a, ha, hia⟩ := hq hi
      obtain ⟨a', ha', hja⟩ := hq hj
      rw [addrOf_eq ha, addrOf_eq ha']
      rw [hia, hja] at hij
      exact hij)
  · obtain ⟨a, ha, hia⟩ := hq hi
    obtain ⟨a', hns, hb', hja⟩ := hbo hj
    rw [hia, hja] at hij
    subst hij
    exact absurd ha (bundleDisjointB_spec hd hns hb' i)
  · obtain ⟨a, hns, hb', hia⟩ := hbo hi
    obtain ⟨a', ha', hja⟩ := hq hj
    rw [hia, hja] at hij
    subst hij
    exact absurd ha' (bundleDisjointB_spec hd hns hb' j)
  · obtain ⟨a, _, hia', hia⟩ := hbo hi
    obtain ⟨a', _, hja', hja⟩ := hbo hj
    rw [hia, hja] at hij
    subst hij
    exact bundleAddrs_inj hia' hja'

/-- **Reference acceptance at the joined renaming**, the evidence explicit:
a quotient run whose declarations name representatives and whose evidence names
representatives or bundle-only names, renamed by `evAddr`, is accepted at the
same fuel, with a related environment. -/
theorem acceptsRef_evAddr (μ : Ix.Kernel.CheckMode) {roles : Std.HashMap Address Ix.Kernel.Role}
    (hb : TableBound ixe roles) (hd : bundleDisjointB ixe b = true)
    {ev : Ix.Kernel.Evidences .source}
    (hev : ev.Good (KeyScope.ofId (fun n => QRepAt ixe roles n ∨ BundleOnly ixe b n)))
    {ds : List (Ix.Kernel.Declaration .source)}
    (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId (fun n => QRepAt ixe roles n ∨ BundleOnly ixe b n)))
    {envS : Ix.Kernel.Env .source} (h : Ix.Kernel.Cached.AcceptsRef μ ev ds envS) :
    ∃ envA, Ix.Kernel.Cached.AcceptsRef μ (ev.mapKeys (evAddr ixe b))
        (ds.map (Ix.Kernel.Declaration.mapKeys (evAddr ixe b))) envA ∧
      Ix.Kernel.EnvRel (fun n => QRepAt ixe roles n ∨ BundleOnly ixe b n) (evAddr ixe b) envS envA :=
  Ix.Kernel.Cached.AcceptsRef.rename μ (evAddr_injOn hb hd) hev hds h

end Bundle

/-! ## The decided goodness of a stream -/

section Decided

variable {q : Ix.Kernel.Name → Bool}

theorem Key.goodB_spec : ∀ {k : Ix.Kernel.Key .source}, Key.goodB q k = true →
    k.Good (KeyScope.ofId (fun n => q n = true))
  | .id _, h => h
  | .role _, _ => trivial
  | .aux k _, h => Key.goodB_spec (k := k) h

/-- The memo's invariant: every recorded subterm is good. -/
def GoodSeen (Q : Ix.Kernel.Name → Prop) (seen : Std.HashSet (Ix.Kernel.Expr .source)) : Prop :=
  ∀ e, seen.contains e = true → e.Good (KeyScope.ofId Q)

theorem GoodSeen.empty {Q : Ix.Kernel.Name → Prop} : GoodSeen Q {} := by
  intro e h
  simp at h

theorem GoodSeen.insert {Q : Ix.Kernel.Name → Prop} {seen : Std.HashSet (Ix.Kernel.Expr .source)}
    (h : GoodSeen Q seen) {e : Ix.Kernel.Expr .source} (he : e.Good (KeyScope.ofId Q)) : GoodSeen Q (seen.insert e) := by
  intro x hx
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · rw [← eq_of_beq hx]
    exact he
  · exact h x hx

theorem goodBGo_finish {Q : Ix.Kernel.Name → Prop} {seen : Std.HashSet (Ix.Kernel.Expr .source)}
    {e : Ix.Kernel.Expr .source} {ok : Bool} (hs : GoodSeen Q seen) (he : ok = true → e.Good (KeyScope.ofId Q)) :
    GoodSeen Q (if ok = true then (true, seen.insert e) else (false, seen)).2 ∧
      ((if ok = true then (true, seen.insert e) else (false, seen)).1 = true → e.Good (KeyScope.ofId Q)) := by
  cases ok with
  | false => exact ⟨hs, by simp⟩
  | true => exact ⟨hs.insert (he rfl), fun _ => he rfl⟩

/-- **The memoised walk decides goodness.** -/
theorem Expr.goodBGo_spec : ∀ (e : Ix.Kernel.Expr .source) {seen : Std.HashSet (Ix.Kernel.Expr .source)},
    GoodSeen (fun n => q n = true) seen →
      GoodSeen (fun n => q n = true) (Expr.goodBGo q seen e).2 ∧
        ((Expr.goodBGo q seen e).1 = true → e.Good (KeyScope.ofId (fun n => q n = true))) := by
  intro e
  induction e with
  | bvar => intro seen hs; exact ⟨hs, fun _ => trivial⟩
  | sort => intro seen hs; exact ⟨hs, fun _ => trivial⟩
  | lit l => intro seen hs; cases l <;> exact ⟨hs, fun _ => by first | trivial | exact fun _ _ => trivial⟩
  | const n us => intro seen hs; exact ⟨hs, fun h => Key.goodB_spec h⟩
  | fvar i ty ih =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      obtain ⟨h1, h2⟩ := ih hs
      exact goodBGo_finish h1 h2
  | app a b iha ihb =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      obtain ⟨h1, h2⟩ := iha hs
      by_cases ha : (Expr.goodBGo q seen a).1 = true
      · simp only [ha, ↓reduceIte]
        obtain ⟨h3, h4⟩ := ihb h1
        exact goodBGo_finish h3 (fun h => ⟨h2 ha, h4 h⟩)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h1, False.elim⟩
  | lam ty body m iht ihb =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      obtain ⟨h1, h2⟩ := iht hs
      by_cases ha : (Expr.goodBGo q seen ty).1 = true
      · simp only [ha, ↓reduceIte]
        obtain ⟨h3, h4⟩ := ihb h1
        exact goodBGo_finish h3 (fun h => ⟨h2 ha, h4 h⟩)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h1, False.elim⟩
  | forallE ty body m iht ihb =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      obtain ⟨h1, h2⟩ := iht hs
      by_cases ha : (Expr.goodBGo q seen ty).1 = true
      · simp only [ha, ↓reduceIte]
        obtain ⟨h3, h4⟩ := ihb h1
        exact goodBGo_finish h3 (fun h => ⟨h2 ha, h4 h⟩)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h1, False.elim⟩
  | letE ty v body l iht ihv ihb =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      obtain ⟨h1, h2⟩ := iht hs
      by_cases ha : (Expr.goodBGo q seen ty).1 = true
      · simp only [ha, ↓reduceIte]
        obtain ⟨h3, h4⟩ := ihv h1
        by_cases hv : (Expr.goodBGo q (Expr.goodBGo q seen ty).2 v).1 = true
        · simp only [hv, ↓reduceIte]
          obtain ⟨h5, h6⟩ := ihb h3
          exact goodBGo_finish h5 (fun h => ⟨h2 ha, h4 hv, h6 h⟩)
        · simp only [hv, Bool.false_eq_true, ↓reduceIte]
          exact ⟨h3, False.elim⟩
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h1, False.elim⟩
  | proj s i sub ih =>
    intro seen hs
    rw [Expr.goodBGo]
    split
    · rename_i hc
      exact ⟨hs, fun _ => hs _ hc⟩
    · dsimp only
      by_cases hk : Key.goodB q s = true
      · simp only [hk, ↓reduceIte]
        obtain ⟨h1, h2⟩ := ih hs
        exact goodBGo_finish h1 (fun h => ⟨Key.goodB_spec hk, h2 h⟩)
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hs, False.elim⟩


theorem exprsGoodB_spec : ∀ (es : List (Ix.Kernel.Expr .source))
    {seen : Std.HashSet (Ix.Kernel.Expr .source)}, GoodSeen (fun n => q n = true) seen →
      GoodSeen (fun n => q n = true) (exprsGoodB q seen es).2 ∧
        ((exprsGoodB q seen es).1 = true → ∀ e ∈ es, e.Good (KeyScope.ofId (fun n => q n = true)))
  | [], _, hs => ⟨hs, fun _ _ he => nomatch he⟩
  | e :: es, seen, hs => by
    obtain ⟨h1, h2⟩ := Expr.goodBGo_spec e hs
    rcases hb : Expr.goodBGo q seen e with ⟨b, s⟩
    rw [hb] at h1 h2
    cases b with
    | false =>
      simp only [exprsGoodB, hb]
      exact ⟨h1, fun h => by cases h⟩
    | true =>
      simp only [exprsGoodB, hb]
      obtain ⟨h3, h4⟩ := exprsGoodB_spec es h1
      refine ⟨h3, fun h x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h2 rfl
      · exact h4 h x hx

/-- A constant whose parts are good is good. -/
theorem ConstantInfo.good_of_parts {P : Ix.Kernel.Name → Prop} {c : Ix.Kernel.ConstantInfo .source}
    (hk : ∀ k ∈ (ConstantInfo.parts c).1, k.Good (KeyScope.ofId P)) (he : ∀ e ∈ (ConstantInfo.parts c).2, e.Good (KeyScope.ofId P)) :
    c.Good (KeyScope.ofId P) := by
  cases c with
  | axiomInfo v => exact ⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩
  | defnInfo v e _ =>
    exact ⟨⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩,
      he _ (by simp [ConstantInfo.parts])⟩
  | thmInfo v e =>
    exact ⟨⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩,
      he _ (by simp [ConstantInfo.parts])⟩
  | indInfo v caps =>
    refine ⟨⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩, ?_⟩
    intro k hk'
    exact hk k (by simp [ConstantInfo.parts, Option.mem_toList.mpr hk'])
  | ctorInfo v _ _ => exact ⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩
  | recInfo v _ _ rules =>
    refine ⟨⟨hk _ (by simp [ConstantInfo.parts]), he _ (by simp [ConstantInfo.parts])⟩, ?_⟩
    intro r hr
    refine ⟨hk _ (by simp only [ConstantInfo.parts, List.mem_cons, List.mem_map]; exact Or.inr ⟨r, hr, rfl⟩),
      ?_, he _ (by
        simp only [ConstantInfo.parts, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨r, hr, Or.inl rfl⟩)⟩
    cases hf : r.fire with
    | inert => trivial
    | plain => trivial
    | nested _ ps =>
      intro x hx
      exact he _ (by
        simp only [ConstantInfo.parts, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨r, hr, Or.inr (by rw [hf]; exact hx)⟩)
  | projInfo t =>
    refine ⟨hk _ (by simp [ConstantInfo.parts]), hk _ (by simp [ConstantInfo.parts]), ?_⟩
    intro x hx
    exact he _ (by simpa [ConstantInfo.parts] using hx)

/-- A declaration whose parts are good is good. -/
theorem Declaration.good_of_parts {P : Ix.Kernel.Name → Prop} {d : Ix.Kernel.Declaration .source}
    (hk : ∀ k ∈ (Declaration.parts d).1, k.Good (KeyScope.ofId P)) (he : ∀ e ∈ (Declaration.parts d).2, e.Good (KeyScope.ofId P)) :
    d.Good (KeyScope.ofId P) := by
  cases d with
  | axiomDecl v => exact ⟨hk _ (by simp [Declaration.parts]), he _ (by simp [Declaration.parts])⟩
  | defnDecl v e _ =>
    exact ⟨⟨hk _ (by simp [Declaration.parts]), he _ (by simp [Declaration.parts])⟩,
      he _ (by simp [Declaration.parts])⟩
  | thmDecl v e =>
    exact ⟨⟨hk _ (by simp [Declaration.parts]), he _ (by simp [Declaration.parts])⟩,
      he _ (by simp [Declaration.parts])⟩
  | opaqueDecl v e =>
    exact ⟨⟨hk _ (by simp [Declaration.parts]), he _ (by simp [Declaration.parts])⟩,
      he _ (by simp [Declaration.parts])⟩
  | basisDecl _ => trivial
  | indDecl block _ =>
    intro c hc
    exact ConstantInfo.good_of_parts
      (fun k hk' => hk k (by simp only [Declaration.parts, List.mem_flatMap]; exact ⟨c, hc, hk'⟩))
      (fun e he' => he e (by simp only [Declaration.parts, List.mem_flatMap]; exact ⟨c, hc, he'⟩))
  | quotDecl _ v => exact ⟨hk _ (by simp [Declaration.parts]), he _ (by simp [Declaration.parts])⟩

/-- **The decided goodness of a stream**: every declaration's parts pass `q`. -/
theorem declsGoodB_spec {ds : Array (Ix.Kernel.Declaration .source)} (h : declsGoodB q ds = true) :
    ∀ d ∈ ds, (∀ k ∈ (Declaration.parts d).1, k.Good (KeyScope.ofId (fun n => q n = true))) ∧
      (∀ e ∈ (Declaration.parts d).2, e.Good (KeyScope.ofId (fun n => q n = true))) := by
  unfold declsGoodB at h
  rw [← Array.foldl_toList] at h
  intro d hd
  have hd' := Array.mem_toList_iff.mpr hd
  generalize ds.toList = l at h hd'
  suffices ∀ (l : List (Ix.Kernel.Declaration .source)) (acc : Bool × Std.HashSet (Ix.Kernel.Expr .source)),
      GoodSeen (fun n => q n = true) acc.2 →
      (l.foldl (fun (acc : Bool × Std.HashSet (Ix.Kernel.Expr .source)) d =>
        if acc.1 then
          if (Declaration.parts d).1.all (Key.goodB q) then exprsGoodB q acc.2 (Declaration.parts d).2
          else (false, acc.2)
        else acc) acc).1 = true →
      acc.1 = true ∧ ∀ d ∈ l, (∀ k ∈ (Declaration.parts d).1, k.Good (KeyScope.ofId (fun n => q n = true))) ∧
        (∀ e ∈ (Declaration.parts d).2, e.Good (KeyScope.ofId (fun n => q n = true))) from
    (this l (true, {}) GoodSeen.empty h).2 d hd'
  intro l
  induction l with
  | nil => intro acc _ h; exact ⟨h, fun _ hd => nomatch hd⟩
  | cons x xs ih =>
    intro acc hs h
    rw [List.foldl_cons] at h
    by_cases ha : acc.1 = true
    · simp only [ha, ↓reduceIte] at h
      by_cases hk : (Declaration.parts x).1.all (Key.goodB q) = true
      · simp only [hk, ↓reduceIte] at h
        obtain ⟨h1, h2⟩ := exprsGoodB_spec (Declaration.parts x).2 hs
        obtain ⟨h3, h4⟩ := ih _ h1 h
        refine ⟨ha, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨fun k hk' => Key.goodB_spec (List.all_eq_true.mp hk k hk'), h2 h3⟩
        · exact h4 d hd
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
        have := (ih (false, acc.2) hs h).1
        cases this
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd (ih acc hs h).1 ha

/-- The decided goodness of a stream, read: every declaration is good. -/
theorem declsGoodB_good {ds : Array (Ix.Kernel.Declaration .source)} (h : declsGoodB q ds = true) :
    ∀ d ∈ ds, d.Good (KeyScope.ofId (fun n => q n = true)) := fun d hd =>
  Declaration.good_of_parts (declsGoodB_spec h d hd).1 (declsGoodB_spec h d hd).2

/-- **The decided goodness of an evidence table.** -/
theorem evidenceGoodB_good {ev : Ix.Kernel.Evidences .source} (h : evidenceGoodB q ev = true) :
    ev.Good (KeyScope.ofId (fun n => q n = true)) := by
  unfold evidenceGoodB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hk, he⟩ := h
  have he' := (exprsGoodB_spec (evidenceParts ev).2 GoodSeen.empty).2 he
  intro p hp e hpe
  cases e with
  | defeq => trivial
  | proof kv =>
    obtain ⟨k, v⟩ := kv
    refine ⟨Key.goodB_spec (List.all_eq_true.mp hk k ?_), he' v ?_⟩
    · simp only [evidenceParts, List.mem_flatMap]
      exact ⟨p, hp, .proof (k, v), hpe, List.mem_singleton_self _⟩
    · simp only [evidenceParts, List.mem_flatMap]
      exact ⟨p, hp, .proof (k, v), hpe, List.mem_singleton_self _⟩
end Decided

/-! ## Quotient Source at a compiled artifact (`prepareSourceCollapsedAt`) -/

section At

variable {t : Ix.Kernel.RoleTable}

/-- `qRepAtB`, read: a representative of the artifact under the table rule. -/
theorem qRepAtB_spec {roles : Std.HashMap Address Ix.Kernel.Role} {n : Ix.Kernel.Name}
    (h : qRepAtB (sourceAddrs ixe) (fiberAliasAt ixe roles) n = true) : QRepAt ixe roles n := by
  simp only [qRepAtB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hr, hc⟩, hf⟩ := h
  refine ⟨⟨hr, ?_⟩, hf⟩
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  exact hc

/-- `qEvB`, read: a representative or a bundle-only name. -/
theorem qEvB_spec {roles : Std.HashMap Address Ix.Kernel.Role} {b : Ix.RoleEvidence.Bundle}
    {n : Ix.Kernel.Name}
    (h : qEvB (sourceAddrs ixe) (fiberAliasAt ixe roles) (bundleAddrs b) n = true) :
    QRepAt ixe roles n ∨ BundleOnly ixe b n := by
  simp only [qEvB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (qRepAtB_spec h)
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hr, hs⟩, hb⟩ := h
    refine Or.inr ⟨hr, ?_, ?_⟩
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at hs
      cases h' : (sourceAddrs ixe)[n]? with
      | none => rfl
      | some _ => rw [h'] at hs; cases hs
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at hb
      exact hb

/-- **What the checks give**, at a bundle `b` and evidence `ev`. -/
theorem collapsedChecksWith_spec {b : Ix.RoleEvidence.Bundle} {ev : Ix.Kernel.Evidences .source}
    {ds : Array (Ix.Kernel.Declaration .source)} (h : collapsedChecksWith ixe t b ev ds = none) :
    (∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t)))) ∧
      (∀ d ∈ ds, d.Good (KeyScope.ofId (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n))) ∧
      bundleDisjointB ixe b = true ∧
      (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev).Good
        (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) := by
  unfold collapsedChecksWith at h
  dsimp only at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3
  refine ⟨fun d hd => ?_, fun d hd => ?_, h2, ?_⟩
  · have hp := declsGoodB_spec h1 d hd
    exact Declaration.good_of_parts
      (fun k hk => Ix.Kernel.Key.Good.mono (fun _ hn => qRepAtB_spec hn) (fun _ _ => trivial) (hp.1 k hk))
      (fun e he => Ix.Kernel.Expr.Good.mono (fun _ hn => qRepAtB_spec hn) (fun _ _ => trivial) (hp.2 e he))
  · have hp := declsGoodB_spec h1 d hd
    exact Declaration.good_of_parts
      (fun k hk => Ix.Kernel.Key.Good.mono (fun _ hn => Or.inl (qRepAtB_spec hn)) (fun _ _ => trivial) (hp.1 k hk))
      (fun e he => Ix.Kernel.Expr.Good.mono (fun _ hn => Or.inl (qRepAtB_spec hn)) (fun _ _ => trivial) (hp.2 e he))
  · intro p hp e he
    have := evidenceGoodB_good h3 p hp e he
    cases e with
    | defeq => trivial
    | proof kv =>
      obtain ⟨k, v⟩ := kv
      exact ⟨Ix.Kernel.Key.Good.mono (fun _ hn => qEvB_spec hn) (fun _ _ => trivial) this.1,
        Ix.Kernel.Expr.Good.mono (fun _ hn => qEvB_spec hn) (fun _ _ => trivial) this.2⟩

theorem collapsedChecksUsing_spec {bundle : Except String Ix.RoleEvidence.Bundle}
    {ev : Ix.Kernel.Evidences .source} {ds : Array (Ix.Kernel.Declaration .source)}
    (h : collapsedChecksUsing bundle ev ixe t ds = .ok ()) :
    ∃ b, bundle = .ok b ∧ collapsedChecksWith ixe t b ev ds = none := by
  unfold collapsedChecksUsing at h
  cases bundle with
  | error e => cases h
  | ok b =>
    refine ⟨b, rfl, ?_⟩
    dsimp only at h
    cases hc : collapsedChecksWith ixe t b ev ds with
    | none => rfl
    | some e => rw [hc] at h; cases h

/-- **Quotient Source's prepared stream at an artifact is checked**, over any
bundle source and evidence. -/
theorem prepareSourceCollapsedAtUsing_good {bundle : Except String Ix.RoleEvidence.Bundle}
    {ev : Ix.Kernel.Evidences .source}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)}
    (h : prepareSourceCollapsedAtUsing bundle ev ixe t hints pre env blocks = .ok ds) :
    prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks = .ok ds ∧
      ∃ b, bundle = .ok b ∧
        (∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t)))) ∧
        (∀ d ∈ ds, d.Good (KeyScope.ofId (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n))) ∧
        bundleDisjointB ixe b = true ∧
        (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev).Good
          (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) := by
  unfold prepareSourceCollapsedAtUsing at h
  cases hp : prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks with
  | error e => rw [hp] at h; cases h
  | ok ds' =>
    rw [hp] at h
    dsimp only at h
    cases hc : collapsedChecksUsing bundle ev ixe t ds' with
    | error e => rw [hc] at h; cases h
    | ok u =>
      rw [hc] at h
      cases h
      obtain ⟨b, hb, hw⟩ := collapsedChecksUsing_spec hc
      exact ⟨rfl, b, hb, collapsedChecksWith_spec hw⟩

/-- **Quotient Source's prepared stream at a compiled artifact is checked**:
whenever `prepareSourceCollapsedAt` succeeds, its declarations name
representatives, the committed bundle is disjoint from the artifact, and the
renamed bundle evidence names representatives or bundle-only names.
Unconditional: the statements' `CollapsedGood`. -/
theorem prepareSourceCollapsedAt_good
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)}
    (h : prepareSourceCollapsedAt ixe t hints pre env blocks = .ok ds) :
    prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks = .ok ds ∧
      ∃ b, Ix.RoleEvidence.quotientBundle () = .ok b ∧
        (∀ d ∈ ds, d.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t)))) ∧
        (∀ d ∈ ds, d.Good (KeyScope.ofId (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n))) ∧
        bundleDisjointB ixe b = true ∧
        (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) (Ix.RoleEvidence.quotientEvidence ())).Good
          (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) :=
  prepareSourceCollapsedAtUsing_good h

/-- **Reference acceptance of checked quotient Source at the artifact's
addresses**, over any bundle source and evidence: a reference accept of the
checked stream at the renamed evidence, renamed by the joined map (`evAddr`),
is accepted at the same fuel, with a related environment. -/
theorem acceptsRef_prepareSourceCollapsedAtUsing (μ : Ix.Kernel.CheckMode)
    (hb : TableBound ixe (roleAtMap t)) {bundle : Except String Ix.RoleEvidence.Bundle}
    {ev : Ix.Kernel.Evidences .source}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)}
    (h : prepareSourceCollapsedAtUsing bundle ev ixe t hints pre env blocks = .ok ds)
    {envS : Ix.Kernel.Env .source}
    (hacc : Ix.Kernel.Cached.AcceptsRef μ (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev)
      ds.toList envS) :
    ∃ b, bundle = .ok b ∧ ∃ envA,
      Ix.Kernel.Cached.AcceptsRef μ
        ((evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev).mapKeys (evAddr ixe b))
        (ds.toList.map (Ix.Kernel.Declaration.mapKeys (evAddr ixe b))) envA ∧
      Ix.Kernel.EnvRel (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) (evAddr ixe b)
        envS envA := by
  obtain ⟨_, b, hbun, _, hds, hd, hev⟩ := prepareSourceCollapsedAtUsing_good h
  exact ⟨b, hbun, acceptsRef_evAddr μ hb hd hev (fun d hd' => hds d (Array.mem_toList_iff.mp hd')) hacc⟩

/-- `acceptsRef_prepareSourceCollapsedAtUsing` at the committed bundle and
evidence (`prepareSourceCollapsedAt`). -/
theorem acceptsRef_prepareSourceCollapsedAt (μ : Ix.Kernel.CheckMode)
    (hb : TableBound ixe (roleAtMap t))
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)}
    (h : prepareSourceCollapsedAt ixe t hints pre env blocks = .ok ds)
    {envS : Ix.Kernel.Env .source}
    (hacc : Ix.Kernel.Cached.AcceptsRef μ
      (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) (Ix.RoleEvidence.quotientEvidence ()))
      ds.toList envS) :
    ∃ b, Ix.RoleEvidence.quotientBundle () = .ok b ∧ ∃ envA,
      Ix.Kernel.Cached.AcceptsRef μ
        ((evidenceSubst (fiberAliasAt ixe (roleAtMap t)) (Ix.RoleEvidence.quotientEvidence ())).mapKeys
          (evAddr ixe b))
        (ds.toList.map (Ix.Kernel.Declaration.mapKeys (evAddr ixe b))) envA ∧
      Ix.Kernel.EnvRel (fun n => QRepAt ixe (roleAtMap t) n ∨ BundleOnly ixe b n) (evAddr ixe b)
        envS envA :=
  acceptsRef_prepareSourceCollapsedAtUsing μ hb h hacc

/-- **The executed check gives the reference accept** (the shape of the
statements' `sourceAcceptsQ_of_check`), over explicit sources. -/
theorem checkSourceCollapsedBundledAtUsing_ref (V : Type w) [SetTheory V]
    {prelude : Except String (Ix.Kernel.Reader.Prelude .source)}
    {bundle : Except String Ix.RoleEvidence.Bundle} {ev : Ix.Kernel.Evidences .source}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {envS : Ix.Kernel.Env .source}
    (h : checkSourceCollapsedBundledAtUsing prelude bundle ev ixe t env blocks = .ok envS) :
    ∃ pre ds, prelude = .ok pre ∧
      prepareSourceCollapsedAtUsing bundle ev ixe t ((fiberHintsMap ixe)[·]?) pre env blocks = .ok ds ∧
      Ix.Kernel.Cached.AcceptsRef .verified (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev)
        ds.toList envS := by
  unfold checkSourceCollapsedBundledAtUsing at h
  cases prelude with
  | error e => cases h
  | ok pre =>
    dsimp only at h
    cases hp : prepareSourceCollapsedAtUsing bundle ev ixe t ((fiberHintsMap ixe)[·]?) pre env blocks with
    | error e => rw [hp] at h; cases h
    | ok ds =>
      rw [hp] at h
      dsimp only at h
      cases hc : Ix.Kernel.Cached.checkDecls .verified
          (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev) ds with
      | error e => rw [hc] at h; cases h
      | ok kenv =>
        rw [hc] at h
        cases h
        exact ⟨pre, ds, rfl, hp, Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc⟩

/-- `checkSourceCollapsedBundledAtUsing_ref` at the committed sources
(`checkSourceCollapsedBundledAt`). -/
theorem checkSourceCollapsedBundledAt_ref (V : Type w) [SetTheory V]
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {envS : Ix.Kernel.Env .source}
    (h : checkSourceCollapsedBundledAt ixe t env blocks = .ok envS) :
    ∃ pre ds, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      prepareSourceCollapsedAt ixe t ((fiberHintsMap ixe)[·]?) pre env blocks = .ok ds ∧
      Ix.Kernel.Cached.AcceptsRef .verified
        (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) (Ix.RoleEvidence.quotientEvidence ()))
        ds.toList envS :=
  checkSourceCollapsedBundledAtUsing_ref V h
end At
end Ix.LeanIngress
