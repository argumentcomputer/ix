import IxVMRefinement.Binding.Defs

/-! # Changing the group limit of the prefix invariant

`Decl.PrefixInv E t lim env` reads the limit `lim` in three places only: the role fields of
`CoreCompanions` (through the roles in force) and `roleRes` (every fabricated role in force
resolves). Every other field is the same statement at every limit; the firing of the stored
projection tables names no limit.

* `scopedLoadFacts_withLim`, `prefixInv_withLim`: the invariant at another limit, given the
  companions and `roleRes` there.
* `prefixInv_lower`: to a limit with fewer roles in force.
* `prefixInv_raise`: to a limit with more roles in force, given for each role newly in force
  that its companion fact holds (`RaiseOk`: an operation with its companion facts, `String` with
  the whole literal support, or a role no companion field reads) and, for a fabricated role,
  that its key is stored.
* The raises the fold makes between groups: one group below the well-founded block
  (`prefixInv_raise_succ`), the well-founded block at once (`prefixInv_raise_wf`, 33 to 41),
  the literal block at once (`prefixInv_raise_literal`, 41 to 46: `String` needs all seven
  support constants, `strLitSupported_of_shapes`), and the equation groups at once
  (`prefixInv_raise_tail`, 46 to any limit).
* `topLim n`: the largest carried limit at which every role in force is of the first `n`
  groups; `bfacts_inv_of_top`: the prefix invariant at it gives it at every carried limit
  within the first `n` groups.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

/-! ## The load contract at another limit -/

/-- **The load contract at another limit**: every field but `roleRes` is the same statement. -/
theorem scopedLoadFacts_withLim {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t : Ix.Kernel.RoleTable} {lim lim' : Option Nat}
    (h : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env, t, lim⟩))
    (hres : RoleResAt (Core.Ctx.stored ⟨E, env, t, lim'⟩)) :
    Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env, t, lim'⟩) where
  getCI := fun addr ptr h₀ h₁ cs a ev hal hne hg ha =>
    h.getCI addr ptr h₀ h₁ cs a ev hal hne ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ ha
  getCprj := fun bp ptr i j h₀ h₁ cs b ev hal hfam hg hb =>
    h.getCprj bp ptr i j h₀ h₁ cs b ev hal hfam ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ hb
  getIprj := fun bp ptr i h₀ h₁ cs b ev hal hfam hg hb =>
    h.getIprj bp ptr i h₀ h₁ cs b ev hal hfam ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ hb
  indRecord := h.indRecord
  inductRecord := h.inductRecord
  projTables := h.projTables
  projTablesAt := h.projTablesAt
  unitLike := h.unitLike
  unitLikeRaw := fun ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps ev hal hne hg ha ld hb hfind
      hfew hz hnr =>
    h.unitLikeRaw ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps ev hal hne hg ha ld hb hfind hfew
      ⟨hz.bp, hz.ptr, hz.before, hz.after, hz.calls, hz.observed, hz.allowed, hz.good,
        hz.blockRep, hz.zeroFields⟩
      ⟨hnr.ap, hnr.before, hnr.after, hnr.calls, hnr.observed, hnr.allowed, hnr.good,
        hnr.parentRep⟩
  eta := h.eta
  etaIota := h.etaIota
  recordShape := h.recordShape
  inductBlock := h.inductBlock
  projCtorTele := h.projCtorTele
  projFire := h.projFire
  canonical := h.canonical
  storedRes := h.storedRes
  findRes := h.findRes
  ctorIndRes := h.ctorIndRes
  ctorIndPerm := h.ctorIndPerm
  roleRes := hres

/-! ## The companions at another limit -/

section Companions

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
  {lim lim' : Option Nat}

/-- **The companions at a limit with fewer roles in force.** -/
theorem coreCompanions_lower (h : Decl.CoreCompanions ⟨E, env, t, lim⟩)
    (hsub : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → Core.Ctx.inForce ⟨E, env, t, lim⟩ r) :
    Decl.CoreCompanions ⟨E, env, t, lim'⟩ where
  natLit := fun h1 h2 h3 => h.natLit (hsub _ h1) (hsub _ h2) (hsub _ h3)
  strLit := fun h1 => h.strLit (hsub _ h1)
  natOps := fun r hr hm => h.natOps r (hsub r hr) hm
  natAdd := fun h1 => h.natAdd (hsub _ h1)
  eqStored := fun h1 => h.eqStored (hsub _ h1)
  quotBasis := fun h1 => h.quotBasis (hsub _ h1)
  recMajorRecord := h.recMajorRecord
  recRulesNodupAndProj := h.recRulesNodupAndProj
  recPlain := h.recPlain
  ruleCtorHead := h.ruleCtorHead

end Companions

/-- The roles a companion field reads. -/
def companionRoles : List Ix.Kernel.Role :=
  [.nat, .natZero, .natSucc, .natAdd, .string, .eq, .quot]

/-- The companion roles that are no operation and not `String`: they must be in force already. -/
def basicRoles : List Ix.Kernel.Role := [.nat, .natZero, .natSucc, .eq, .quot]

/-- **A role newly in force has its companion fact**: an operation stored with its companion
facts, `String` with the whole literal support, or a role no companion field reads. -/
def RaiseOk (env : Ix.Kernel.Env .anon) (r : Ix.Kernel.Role) : Prop :=
  RoleOps.OpCompanion env r ∨ (r = .string ∧ Ix.Kernel.strLitSupported env = true) ∨
    (r ∉ companionRoles ∧ (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames)

theorem mem_opRoles_of_opCompanion {env : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role}
    (hc : RoleOps.OpCompanion env r) : r ∈ RoleOps.opRoles := by
  have h1 := hc.1
  rw [RoleOps.opNames_eq_map] at h1
  obtain ⟨r₀, hr₀, heq⟩ := List.mem_map.mp h1
  have heq' : (Ix.Kernel.Key.role r₀ : Core.KKey) = Ix.Kernel.Key.role r := heq
  have hr : r₀ = r := Ix.Kernel.Key.role.inj heq'
  rw [← hr]
  exact hr₀

/-- An operation stored as pinned has its companion facts (`Nat.add` aside). -/
theorem opCompanion_of_storedOk {env : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role}
    (hr : r ∈ RoleOps.opRoles) (hok : Ix.Kernel.natOpStoredOk env (.role r) = true)
    (hadd : r ≠ .natAdd) : RoleOps.OpCompanion env r := by
  refine ⟨?_, RoleOps.natOpStored_of_storedOk hok, fun h => absurd h hadd⟩
  rw [RoleOps.opNames_eq_map]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

private theorem basic_not_op : ∀ r ∈ basicRoles, r ∉ RoleOps.opRoles := by decide

private theorem basic_ne_string : ∀ r ∈ basicRoles, r ≠ .string := by decide

private theorem basic_companion : ∀ r ∈ basicRoles, r ∈ companionRoles := by decide

section Raise

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
  {lim lim' : Option Nat}

/-- A basic companion role in force at the higher limit is in force at the lower one. -/
theorem old_of_basic
    (hnew : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → ¬ Core.Ctx.inForce ⟨E, env, t, lim⟩ r →
      RaiseOk env r)
    {r : Ix.Kernel.Role} (hr : r ∈ basicRoles) (hf : Core.Ctx.inForce ⟨E, env, t, lim'⟩ r) :
    Core.Ctx.inForce ⟨E, env, t, lim⟩ r := by
  by_contra hn
  rcases hnew r hf hn with hc | ⟨he, -⟩ | ⟨hm, -⟩
  · exact basic_not_op r hr (mem_opRoles_of_opCompanion hc)
  · exact basic_ne_string r hr he
  · exact hm (basic_companion r hr)

/-- **The companions at a limit with more roles in force**, each new role with its companion
fact. -/
theorem coreCompanions_raise (h : Decl.CoreCompanions ⟨E, env, t, lim⟩)
    (hnew : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → ¬ Core.Ctx.inForce ⟨E, env, t, lim⟩ r →
      RaiseOk env r) :
    Decl.CoreCompanions ⟨E, env, t, lim'⟩ where
  natLit := fun h1 h2 h3 => h.natLit (old_of_basic hnew (by decide) h1)
    (old_of_basic hnew (by decide) h2) (old_of_basic hnew (by decide) h3)
  strLit := fun h1 => by
    by_cases hold : Core.Ctx.inForce ⟨E, env, t, lim⟩ .string
    · exact h.strLit hold
    · rcases hnew _ h1 hold with hc | ⟨-, hs⟩ | ⟨hm, -⟩
      · exact absurd (mem_opRoles_of_opCompanion hc) (by decide)
      · exact hs
      · exact absurd (by decide : Ix.Kernel.Role.string ∈ companionRoles) hm
  natOps := fun r hr hm => by
    by_cases hold : Core.Ctx.inForce ⟨E, env, t, lim⟩ r
    · exact h.natOps r hold hm
    · rcases hnew r hr hold with hc | ⟨he, -⟩ | ⟨-, hnb⟩
      · exact hc.2.1
      · subst he
        exact absurd hm (by decide)
      · exact absurd hm hnb
  natAdd := fun h1 => by
    by_cases hold : Core.Ctx.inForce ⟨E, env, t, lim⟩ .natAdd
    · exact h.natAdd hold
    · rcases hnew _ h1 hold with hc | ⟨he, -⟩ | ⟨hm, -⟩
      · exact hc.2.2 rfl
      · exact absurd he (by decide)
      · exact absurd (by decide : Ix.Kernel.Role.natAdd ∈ companionRoles) hm
  eqStored := fun h1 => h.eqStored (old_of_basic hnew (by decide) h1)
  quotBasis := fun h1 => h.quotBasis (old_of_basic hnew (by decide) h1)
  recMajorRecord := h.recMajorRecord
  recRulesNodupAndProj := h.recRulesNodupAndProj
  recPlain := h.recPlain
  ruleCtorHead := h.ruleCtorHead

/-! ## `roleRes` at another limit -/

/-- **`roleRes` at a limit with fewer roles in force.** -/
theorem roleResAt_lower (h : RoleResAt (Core.Ctx.stored ⟨E, env, t, lim⟩))
    (hsub : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → Core.Ctx.inForce ⟨E, env, t, lim⟩ r) :
    RoleResAt (Core.Ctx.stored ⟨E, env, t, lim'⟩) :=
  fun r a hf hfab ha => h r a (hsub r hf) hfab ha

/-- **`roleRes` at a limit with more roles in force**: every fabricated role newly in force has
its key stored. -/
theorem roleResAt_raise (h : RoleResAt (Core.Ctx.stored ⟨E, env, t, lim⟩))
    (hnew : ∀ r a, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → ¬ Core.Ctx.inForce ⟨E, env, t, lim⟩ r →
      Core.fabricatedRole r = true → t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci) :
    RoleResAt (Core.Ctx.stored ⟨E, env, t, lim'⟩) := by
  intro r a hf hfab ha
  by_cases hold : Core.Ctx.inForce ⟨E, env, t, lim⟩ r
  · exact h r a hold hfab ha
  · obtain ⟨ci, hci⟩ := hnew r a hf hold hfab ha
    rw [Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim'⟩) hci]
    exact Core.Resolved.ne

/-! ## The prefix invariant at another limit -/

/-- **The prefix invariant at another limit**, given the companions and `roleRes` there. -/
theorem prefixInv_withLim (h : Decl.PrefixInv.{u} E t lim env)
    (hc : Decl.CoreCompanions ⟨E, env, t, lim'⟩)
    (hr : RoleResAt (Core.Ctx.stored ⟨E, env, t, lim'⟩)) :
    Decl.PrefixInv.{u} E t lim' env where
  decl := h.decl
  store := h.store
  unresolved := h.unresolved
  tableWf := h.tableWf
  companions := hc
  loads := scopedLoadFacts_withLim h.loads hr
  etaStable := h.etaStable

/-- **Lowering the limit** to one with fewer roles in force. -/
theorem prefixInv_lower (h : Decl.PrefixInv.{u} E t lim env)
    (hsub : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → Core.Ctx.inForce ⟨E, env, t, lim⟩ r) :
    Decl.PrefixInv.{u} E t lim' env :=
  prefixInv_withLim h (coreCompanions_lower h.companions hsub)
    (roleResAt_lower (roleResAt_of_loads h.loads) hsub)

/-- **Raising the limit**: every role newly in force has its companion fact and, if fabricated,
its key stored. -/
theorem prefixInv_raise (h : Decl.PrefixInv.{u} E t lim env)
    (hnew : ∀ r, Core.Ctx.inForce ⟨E, env, t, lim'⟩ r → ¬ Core.Ctx.inForce ⟨E, env, t, lim⟩ r →
      RaiseOk env r ∧ (Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
        ∃ ci, env.find? (Core.keyOf t a) = some ci)) :
    Decl.PrefixInv.{u} E t lim' env :=
  prefixInv_withLim h (coreCompanions_raise h.companions fun r hf hn => (hnew r hf hn).1)
    (roleResAt_raise (roleResAt_of_loads h.loads)
      fun r a hf hn hfab ha => (hnew r hf hn).2 hfab a ha)

/-- A role in force at `m` and not at `n` is of a group in `[n, m)`. -/
theorem inForce_new_some {m n : Nat} {r : Ix.Kernel.Role}
    (hf : Core.Ctx.inForce ⟨E, env, t, some m⟩ r) (hn : ¬ Core.Ctx.inForce ⟨E, env, t, some n⟩ r) :
    n ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r < m := by
  refine ⟨?_, hf.2 m rfl⟩
  by_contra hlt
  exact hn ⟨hf.1, fun k (hk : some n = some k) => by obtain rfl := Option.some.inj hk; omega⟩

/-- A role in force at any limit and not at `n` is of a group at or past `n`. -/
theorem inForce_new_ge {n : Nat} {r : Ix.Kernel.Role}
    (hf : Core.Ctx.inForce ⟨E, env, t, lim'⟩ r) (hn : ¬ Core.Ctx.inForce ⟨E, env, t, some n⟩ r) :
    n ≤ Ix.SpecDigest.groupOf r := by
  by_contra hlt
  exact hn ⟨hf.1, fun k (hk : some n = some k) => by obtain rfl := Option.some.inj hk; omega⟩

end Raise

/-! ## The groups at the block boundaries (decided) -/

/-- The eight well-founded operations. -/
def wfOpRoles : List Ix.Kernel.Role :=
  [.natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight]

/-- The seven roles of the literal support's five groups. -/
def literalRoles : List Ix.Kernel.Role :=
  [.char, .string, .list, .listNil, .listCons, .charOfNat, .stringOfList]

set_option maxRecDepth 100000 in
private theorem wf_block_all : Ix.Kernel.Role.all.all (fun r =>
    decide (33 ≤ Ix.SpecDigest.groupOf r → Ix.SpecDigest.groupOf r < 41 → r ∈ wfOpRoles)) =
    true := by
  decide +kernel

/-- **The groups 33 to 40 hold the eight well-founded operations and nothing else.** -/
theorem wf_block {r : Ix.Kernel.Role} (h1 : 33 ≤ Ix.SpecDigest.groupOf r)
    (h2 : Ix.SpecDigest.groupOf r < 41) : r ∈ wfOpRoles :=
  of_decide_eq_true (List.all_eq_true.mp wf_block_all r (Ix.Kernel.Role.mem_all r)) h1 h2

set_option maxRecDepth 100000 in
private theorem literal_block_all : Ix.Kernel.Role.all.all (fun r =>
    decide (41 ≤ Ix.SpecDigest.groupOf r → Ix.SpecDigest.groupOf r < 46 → r ∈ literalRoles)) =
    true := by
  decide +kernel

/-- **The groups 41 to 45 hold the seven literal-support roles and nothing else.** -/
theorem literal_block {r : Ix.Kernel.Role} (h1 : 41 ≤ Ix.SpecDigest.groupOf r)
    (h2 : Ix.SpecDigest.groupOf r < 46) : r ∈ literalRoles :=
  of_decide_eq_true (List.all_eq_true.mp literal_block_all r (Ix.Kernel.Role.mem_all r)) h1 h2

set_option maxRecDepth 100000 in
private theorem tail_free_all : Ix.Kernel.Role.all.all (fun r =>
    decide (46 ≤ Ix.SpecDigest.groupOf r → r ∉ companionRoles ∧
      (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames ∧
      Core.fabricatedRole r = false)) = true := by
  decide +kernel

/-- **The roles of the groups from 46 on are read by no companion field and are not
fabricated.** -/
theorem tail_free {r : Ix.Kernel.Role} (h : 46 ≤ Ix.SpecDigest.groupOf r) :
    r ∉ companionRoles ∧ (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames ∧
      Core.fabricatedRole r = false :=
  of_decide_eq_true (List.all_eq_true.mp tail_free_all r (Ix.Kernel.Role.mem_all r)) h

private theorem wf_sub_op : ∀ r ∈ wfOpRoles, r ∈ RoleOps.opRoles := by decide

private theorem wf_ne_add : ∀ r ∈ wfOpRoles, r ≠ .natAdd := by decide

private theorem literal_free : ∀ r ∈ literalRoles, r ≠ .string →
    r ∉ companionRoles ∧ (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames := by
  decide

/-! ## The raises between groups -/

section Raises

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}

/-- **Past one group**: every role of group `g` has its companion fact and, if fabricated, its
key stored. -/
theorem prefixInv_raise_succ {g : Nat} (h : Decl.PrefixInv.{u} E t (some g) env)
    (hnew : ∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true →
      RaiseOk env r ∧ (Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
        ∃ ci, env.find? (Core.keyOf t a) = some ci)) :
    Decl.PrefixInv.{u} E t (some (g + 1)) env := by
  refine prefixInv_raise h (fun r hf hn => ?_)
  obtain ⟨hlo, hhi⟩ := inForce_new_some hf hn
  have hgr : Ix.SpecDigest.groupOf r = g := by omega
  have hmem : r ∈ roleGroup g := hgr ▸ role_mem_roleGroup r
  exact hnew r hmem hf.1

/-- **Past the well-founded block at once** (33 to 41): its groups hold the eight well-founded
operations alone, each stored as pinned. -/
theorem prefixInv_raise_wf (h : Decl.PrefixInv.{u} E t (some 33) env)
    (hops : ∀ r ∈ wfOpRoles, (t.addressOf? r).isSome = true →
      Ix.Kernel.natOpStoredOk env (.role r) = true) :
    Decl.PrefixInv.{u} E t (some 41) env := by
  refine prefixInv_raise h (fun r hf hn => ?_)
  obtain ⟨hlo, hhi⟩ := inForce_new_some hf hn
  have hr := wf_block hlo hhi
  have hok := hops r hr hf.1
  refine ⟨Or.inl (opCompanion_of_storedOk (wf_sub_op r hr) hok (wf_ne_add r hr)),
    fun _ a ha => ?_⟩
  obtain ⟨cv, v, hint, hfind, -, -⟩ := RoleOps.natOpStoredOk_inv hok
  have hk : Core.keyOf t a = .role r := Core.keyOf_of_addressOf h.tableWf ha
  rw [hk]
  exact ⟨_, hfind⟩

/-- **The literal support, from the stored shapes**: with `Nat` literals supported, the seven
types the shapes record give `strLitSupported`. -/
theorem strLitSupported_of_shapes {G : Nat → Prop} (hnat : Ix.Kernel.natLitSupported env = true)
    (hs : Shapes G env) (hG : ∀ r ∈ literalRoles, G (Ix.SpecDigest.groupOf r)) :
    Ix.Kernel.strLitSupported env = true := by
  have hc := hs.char (hG .char (by decide))
  have hstr := hs.string (hG .string (by decide))
  obtain ⟨hl, hln, hlc⟩ := hs.list (hG .list (by decide))
  have hcn := hs.charOfNat (hG .charOfNat (by decide))
  have hsl := hs.stringOfList (hG .stringOfList (by decide))
  unfold Ix.Kernel.strLitSupported
  rw [hnat, hc, hstr, hl, hln, hlc, hcn, hsl]
  rfl

/-- **Past the literal block at once** (41 to 46): its groups hold the seven literal-support
roles alone; `String` needs the whole support (`strLitSupported`), and the six fabricated ones
need their keys stored. -/
theorem prefixInv_raise_literal (h : Decl.PrefixInv.{u} E t (some 41) env)
    (hstr : Ix.Kernel.strLitSupported env = true)
    (hst : ∀ r ∈ literalRoles, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci) :
    Decl.PrefixInv.{u} E t (some 46) env := by
  refine prefixInv_raise h (fun r hf hn => ?_)
  obtain ⟨hlo, hhi⟩ := inForce_new_some hf hn
  have hr := literal_block hlo hhi
  refine ⟨?_, hst r hr⟩
  by_cases hs : r = .string
  · exact Or.inr (Or.inl ⟨hs, hstr⟩)
  · exact Or.inr (Or.inr (literal_free r hr hs))

/-- **Past the equation groups at once** (46 to any limit): their roles are read by no
companion field and are not fabricated. -/
theorem prefixInv_raise_tail (h : Decl.PrefixInv.{u} E t (some 46) env) (lim' : Option Nat) :
    Decl.PrefixInv.{u} E t lim' env := by
  refine prefixInv_raise h (fun r hf hn => ?_)
  obtain ⟨hc, hb, hfab⟩ := tail_free (inForce_new_ge hf hn)
  exact ⟨Or.inr (Or.inr ⟨hc, hb⟩),
    fun hf' => (Bool.false_ne_true (hfab.symm.trans hf')).elim⟩

end Raises

/-! ## The top carried limit within the first `n` groups -/

/-- **The largest carried limit at which every role in force is of the first `n` groups** (for
a table binding every role): `n` up to the well-founded block, then the block's limit 33, the
literal block's 41, the equation groups' 46, and no limit once every group is in. -/
def topLim (n : Nat) : Option Nat :=
  if n ≤ 33 then some n else if n ≤ 40 then some 33 else if n ≤ 45 then some 41
  else if n ≤ 76 then some 46 else none

/-- At a group, the top carried limit is the group's validation limit. -/
theorem topLim_valLimit {g : Nat} (hg : g < 77) : topLim g = some (valLimit g) := by
  show topLim g = some (RoleVal.groupValLimit g)
  unfold topLim RoleVal.groupValLimit
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A group's validation limit is at most 33, or 41, or 46. -/
theorem valLimit_cases (h : Nat) :
    RoleVal.groupValLimit h ≤ 33 ∨ RoleVal.groupValLimit h = 41 ∨ RoleVal.groupValLimit h = 46 := by
  unfold RoleVal.groupValLimit
  split_ifs <;> omega

theorem topLim_some {n m : Nat} (hn : n < 77) (hle : m ≤ n) (hm : m ≤ 33 ∨ m = 41 ∨ m = 46) :
    ∃ v, topLim n = some v ∧ m ≤ v := by
  unfold topLim
  split_ifs <;> first | exact ⟨_, rfl, by omega⟩ | omega

theorem topLim_none {n : Nat} (hn : 77 ≤ n) : topLim n = none := by
  unfold topLim
  split_ifs <;> first | rfl | omega

set_option maxRecDepth 100000 in
private theorem groupOrder_groups : (List.range 77).all (fun k =>
    Ix.SpecDigest.groupOf (Ix.SpecDigest.groupOrder.getD k .nat) == k) = true := by
  decide +kernel

/-- Every group below 77 holds a role. -/
theorem group_inhabited {k : Nat} (hk : k < 77) : ∃ r, Ix.SpecDigest.groupOf r = k :=
  ⟨_, beq_iff_eq.mp (List.all_eq_true.mp groupOrder_groups k (List.mem_range.mpr hk))⟩

section Top

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}

/-- **A role in force at a carried limit within the first `n` groups is in force at the top
limit**, for a table binding every role. -/
theorem inForce_top (hall : AllBound t) {n : Nat} {lim : Option Nat} (hc : Carried lim)
    (hw : LimWithin (· < n) t lim) {r : Ix.Kernel.Role}
    (hf : Core.Ctx.inForce ⟨E, env, t, lim⟩ r) : Core.Ctx.inForce ⟨E, env, t, topLim n⟩ r := by
  by_cases hn : n < 77
  · obtain ⟨r₀, hr₀⟩ := group_inhabited hn
    rcases hc with rfl | rfl | ⟨h, rfl⟩
    · have h1 : Ix.SpecDigest.groupOf r₀ < n :=
        hw r₀ (hall r₀) (fun k (hk : none = some k) => nomatch hk)
      omega
    · have h1 : Ix.SpecDigest.groupOf r₀ < n :=
        hw r₀ (hall r₀) (fun k (hk : some 77 = some k) => by
          obtain rfl := Option.some.inj hk
          omega)
      omega
    · have hle : RoleVal.groupValLimit h ≤ n := by
        by_contra hlt
        have h1 : Ix.SpecDigest.groupOf r₀ < n :=
          hw r₀ (hall r₀) (fun k (hk : some (RoleVal.groupValLimit h) = some k) => by
            obtain rfl := Option.some.inj hk
            omega)
        omega
      obtain ⟨v, hv, hlev⟩ := topLim_some hn hle (valLimit_cases h)
      rw [hv]
      exact ⟨hf.1, fun k (hk : some v = some k) => by
        obtain rfl := Option.some.inj hk
        exact Nat.lt_of_lt_of_le (hf.2 _ rfl) hlev⟩
  · rw [topLim_none (by omega)]
    exact ⟨hf.1, fun k (hk : none = some k) => nomatch hk⟩

end Top

/-- **The prefix invariant at every carried limit within the first `n` groups**, from the
invariant at the top limit. -/
theorem bfacts_inv_of_top {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hall : AllBound t) {n : Nat}
    (htop : ∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t (topLim n) env) :
    ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin (· < n) t lim →
      Decl.PrefixInv.{u} E t lim env :=
  fun E hE lim hc hw =>
    prefixInv_lower (htop E hE) (fun r hf => inForce_top hall hc hw hf)

end IxVM.Refinement.Binding
