import Ix.LeanIngress
import IxC.Kernel.Verify.Rename.Fold
import IxC.Kernel.Verify.Frontend.Prepare

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
    {ev : Ix.Kernel.Evidences .source} (hev : ev.Good (QRep ixe)) {ds : List (Ix.Kernel.Declaration .source)}
    (hds : ∀ d ∈ ds, d.Good (QRep ixe)) {envS : Ix.Kernel.Env .source}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds envS) :
    ∃ envA, Ix.Kernel.Cached.AcceptsRef μ (ev.mapKeys (addrOf ixe))
        (ds.map (Ix.Kernel.Declaration.mapKeys (addrOf ixe))) envA ∧
      Ix.Kernel.EnvRel (QRep ixe) (addrOf ixe) envS envA :=
  Ix.Kernel.Cached.AcceptsRef.rename μ (addrOf_injOn hroles) hev hds h

/-! ## The input side -/

/-- **An input key renames onto representatives.** -/
theorem Key.subst_good (hroles : FibersRoleFree ixe) :
    ∀ {k : Ix.Kernel.Key .source}, k.Good (QIn ixe) → (Key.subst (fiberAlias ixe) k).Good (QRep ixe)
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
  (hK : ∀ k : Ix.Kernel.Key .source, k.Good P → (Key.subst ρ k).Good Q)
include hK

theorem Expr.substKeys_good : ∀ {e : Ix.Kernel.Expr .source}, e.Good P → (Expr.substKeys ρ e).Good Q
  | .bvar _, _ => trivial
  | .fvar _ t, h => Expr.substKeys_good (e := t) h
  | .sort _, _ => trivial
  | .const n _, h => hK n h
  | .app a b, h => ⟨Expr.substKeys_good (e := a) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .lam t b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .forallE t b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := b) h.2⟩
  | .letE t v b _, h => ⟨Expr.substKeys_good (e := t) h.1, Expr.substKeys_good (e := v) h.2.1,
      Expr.substKeys_good (e := b) h.2.2⟩
  | .lit _, _ => trivial
  | .proj s _ e, h => ⟨hK s h.1, Expr.substKeys_good (e := e) h.2⟩

theorem Expr.GoodList.substKeys {es : List (Ix.Kernel.Expr .source)} (h : Expr.GoodList P es) :
    Expr.GoodList Q (es.map (Expr.substKeys ρ)) := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨e₀, h₀, rfl⟩ := he
  exact Expr.substKeys_good hK (h e₀ h₀)

theorem ConstantVal.substKeys_good {cv : Ix.Kernel.ConstantVal .source} (h : cv.Good P) :
    (ConstantVal.substKeys ρ cv).Good Q :=
  ⟨hK _ h.1, Expr.substKeys_good hK h.2⟩

theorem RecRule.substKeys_good {r : Ix.Kernel.RecRule .source} (h : r.Good P) :
    (RecRule.substKeys ρ r).Good Q := by
  refine ⟨hK _ h.1, ?_, Expr.substKeys_good hK h.2.2⟩
  have h2 := h.2.1
  unfold RecRule.substKeys RecRuleFire.substKeys
  cases hf : r.fire with
  | inert => trivial
  | plain => trivial
  | nested lvls pins =>
    rw [hf] at h2
    exact Expr.GoodList.substKeys hK h2

theorem ConstantInfo.substKeys_good {c : Ix.Kernel.ConstantInfo .source} (h : c.Good P) :
    (ConstantInfo.substKeys ρ c).Good Q := by
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

theorem Declaration.substKeys_good {d : Ix.Kernel.Declaration .source} (h : d.Good P) :
    (Declaration.substKeys ρ d).Good Q := by
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

theorem evidenceSubst_good {ev : Ix.Kernel.Evidences .source} (h : ev.Good P) :
    (evidenceSubst ρ ev).Good Q := by
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
      (fun s : Array (Ix.Kernel.Declaration .source) × Std.HashMap (Ix.Kernel.Key .source) Nat ×
        Array (Ix.Kernel.Key .source × Ix.Kernel.Key .source) =>
        ∀ x ∈ s.1, ∃ d ∈ ds, x = Declaration.substKeys ρ d)
      (fun d => d ∈ ds) _ ?_ ds.toList _ (fun d hd => Array.mem_toList_iff.mp hd)
      (by intro x hx; simp at hx) s hloop
    intro a st r ha hst hr
    obtain ⟨kept, owner, dropped⟩ := st
    dsimp only at hr hst
    split at hr
    · cases hin : forIn (m := Except CollapseError) (Declaration.substKeys ρ a).names owner _ with
      | error e =>
        rw [hin] at hr
        cases hr
      | ok o =>
        rw [hin] at hr
        cases hr
        intro x hx
        rcases Array.mem_push.mp hx with hx | rfl
        · exact hst x hx
        · exact ⟨a, ha, rfl⟩
    · split at hr
      · cases hr
        exact hst
      · cases hr

/-- **The collapse at the artifact's fibers renames input keys onto
representatives**: declarations whose keys name input names (`QIn`) collapse
to declarations whose keys are representatives (`QRep`). -/
theorem collapseDecls_good (hroles : FibersRoleFree ixe) {ds : Array (Ix.Kernel.Declaration .source)}
    {c : Collapsed} (h : collapseDecls (fiberAlias ixe) ds = .ok c)
    (hds : ∀ d ∈ ds, d.Good (QIn ixe)) : ∀ d ∈ c.decls, d.Good (QRep ixe) := by
  intro d' hd'
  obtain ⟨d, hd, rfl⟩ := collapseDecls_kept h d' hd'
  exact Declaration.substKeys_good (fun _ hk => Key.subst_good hroles hk) (hds d hd)

/-- **Quotient Source's prepared declarations are representatives'**: the
ingress's declarations naming input names, and the prelude's naming
representatives (role keys, in Source mode), the prepared stream's do. -/
theorem prepareSourceCollapsed_good (hroles : FibersRoleFree ixe)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Ix.Kernel.Declaration .source)}
    (h : prepareSourceCollapsed (fiberAlias ixe) hints pre env blocks = .ok ds)
    (hin : ∀ decls, leanIngressHinted hints env blocks pre.state = .ok decls →
      ∀ d ∈ decls, d.Good (QIn ixe))
    (hpre : ∀ d ∈ pre.ix.decls, d.Good (QRep ixe)) : ∀ d ∈ ds, d.Good (QRep ixe) := by
  unfold prepareSourceCollapsed at h
  cases hi : leanIngressHinted hints env blocks pre.state with
  | error e => simp [hi, bind, Except.bind, Except.mapError] at h
  | ok decls =>
    cases hc : collapseDecls (fiberAlias ixe) decls with
    | error e => simp [hi, hc, bind, Except.bind, Except.mapError] at h
    | ok c =>
      simp only [hi, hc, bind, Except.bind, Except.mapError, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      intro d hd
      obtain ⟨extra, hextra, hperm⟩ := Ix.Kernel.Frontend.preparePrelude_perm pre.ix c.decls
      have hd' := hperm.mem_iff.mp (Array.mem_toList_iff.mpr hd)
      rcases List.mem_append.mp hd' with hd' | hd'
      · exact collapseDecls_good hroles hc (hin decls hi) d (Array.mem_toList_iff.mp hd')
      · exact hpre d (Array.mem_toList_iff.mp (hextra d hd'))
end Ix.LeanIngress
