import IxVMRefinement.FamilyAlias.CallRename
import IxVMRefinement.Binding.TermCells

/-! # The check's renamed terms at the keying of a prefix

`KernelModeled::check_family` types and compares terms it has renamed with
`KernelModeled::rename` (a recursor's type, a rule's right-hand side, a constructor's type, the
pins). The registry's judgements (`k_infer`, `k_is_def_eq`, `k_ensure_sort`) are stated at the
keying of the step's prefix (`Core.Ctx.stored`), which resolves exactly the stored keys; the
family's own members are fresh there, so the term as loaded is not represented at that keying,
and `Decl.rename_exact` (which asks the renaming's agreement at every address) does not apply.

This module states the renamed term's representation at the prefix's keying from its own cells:
a cell of the renamed term is the renaming of a cell of the term (`rename_cells`), so the renamed
term is represented at the prefix's keying as soon as the renaming of each cell of the term is
stored (`rename_stored`, `rename_stored_consts`). A cell that is a member is renamed to its
model, which the prefix stores; any other cell stays, and has to be stored itself
(`rename_stored_of_members`).

* `rename_cells`: the `Const` and `Proj` cells of the renamed term are renamings of the term's;
* `tmExact_stored_of_cells`: a term exact at the table's keying whose cells are stored is exact
  at the keying of the prefix;
* `aliasMap_zip_cases`, `aliasMap_zip_mem`, `aliasMap_zip_stored`: the renaming of a key is the
  key or one of the models, and a member's renaming is a model;
* `rename_stored`, `rename_stored_consts`, `rename_stored_of_members`: the renamed term at the
  keying of a prefix. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)
open IxVM.Refinement.Decl.FamilyAlias (aliasMap)

local macro "rename_lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append]; omega)

private theorem snoc_cell (h : Heap F) (v : SourceValue F) : (h ++ [v])[h.length]? = some v := by
  simp

/-! ## The cells of a renamed term -/

/-- **The cells of a renamed term are the renamed cells of the term**: each address of a `Const`
or `Proj` cell of `KernelModeled::rename`'s result keys, under the second keying, as the renaming
of the key of an address of a cell of the term under the first. -/
theorem rename_cells {κ₁ κ₂ : _root_.Address → KKey} [∀ a, Resolved (κ₂ a)] {f : KKey → KKey}
    {Γ : Nat → KExpr} :
    ∀ {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr},
      ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs →
      Decl.TmExact κ₁ 0 Γ h k E e → Decl.RenameMap κ₁ κ₂ f h src dst →
      ∀ x, AddrIn h' r x → ∃ a, AddrIn h e a ∧ κ₂ (ixAddr x) = f (κ₁ (ixAddr a)) := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelModeled::rename" →
      ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
        args = [e, src, dst] →
        Decl.TmExact κ₁ 0 Γ h k E e → Decl.RenameMap κ₁ κ₂ f h src dst →
        ∀ x, AddrIn h' r x → ∃ a, AddrIn h e a ∧ κ₂ (ixAddr x) = f (κ₁ (ixAddr a)) :=
    ObsFn.strong_induction (world := W)
      (fun fname args h r h' cs => fname = "KernelModeled::rename" →
        ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
          args = [e, src, dst] →
          Decl.TmExact κ₁ 0 Γ h k E e → Decl.RenameMap κ₁ κ₂ f h src dst →
          ∀ x, AddrIn h' r x → ∃ a, AddrIn h e a ∧ κ₂ (ixAddr x) = f (κ₁ (ixAddr a)))
      (fun fname args h r h' cs ev ih hfn e src dst k E hargs hE rm => by
        subst hfn hargs
        match Obs.«KernelModeled::rename».obs ev with
        | .Const (ld12 := ld) (he34 := hr) (hm33 := hm) (ev51 := e1) .. =>
          subst hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨a, ls, -, ra, -⟩ := hE.const_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := Decl.rename_addr_spec e1 ra rm
          intro x hx
          have hx' := Binding.addrIn_const_inv (snoc_cell _ _) hx
          have e' : a' = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible
            (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) ra') hx'
          subst e'
          exact ⟨a, .const cell ra, hka⟩
        | .App (ld12 := ld) (he105 := hr) (hm104 := hm) (ev122 := e1) (ev158 := e2)
            (hc183 := hc) .. =>
          subst hc hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨Ef, Ea, -, hf, ha⟩ := hE.app_of_load ld
          have x1 := e1.heap_extends
          have x2 := e2.heap_extends
          have sf := Decl.rename_exact (Γ₂ := Γ) e1 hf rm
          have sa := Decl.rename_exact (Γ₂ := Γ) e2 (ha.mono x1) (rm.mono x1)
          intro x hx
          rcases Binding.addrIn_app_inv (snoc_cell _ _) hx with hx | hx
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e1 rfl _ src dst k Ef rfl hf rm
              x (Binding.TmExact.addrIn_back sf (x2.trans (Heap.Extends.snoc _ _)) x hx)
            exact ⟨a, .appFn cell ha', hk⟩
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e2 rfl _ src dst k Ea rfl
              (ha.mono x1) (rm.mono x1) x
              (Binding.TmExact.addrIn_back sa (Heap.Extends.snoc _ _) x hx)
            exact ⟨a, .appArg cell (Binding.TmExact.addrIn_back ha x1 a ha'), hk⟩
        | .Lam (ld12 := ld) (he210 := hr) (hm209 := hm) (ev228 := e1) (ev264 := e2)
            (hc296 := hc) .. =>
          subst hc hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨T, B, ℓ, -, ht, hb, -⟩ := hE.lam_of_load ld
          have x1 := e1.heap_extends
          have x2 := e2.heap_extends
          have st := Decl.rename_exact (Γ₂ := Γ) e1 ht rm
          have sb := Decl.rename_exact (Γ₂ := Γ) e2 (hb.mono x1) (rm.mono x1)
          intro x hx
          rcases Binding.addrIn_lam_inv (snoc_cell _ _) hx with hx | hx
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e1 rfl _ src dst k T rfl ht rm
              x (Binding.TmExact.addrIn_back st (x2.trans (Heap.Extends.snoc _ _)) x hx)
            exact ⟨a, .lamTy cell ha', hk⟩
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e2 rfl _ src dst (k + 1) B rfl
              (hb.mono x1) (rm.mono x1) x
              (Binding.TmExact.addrIn_back sb (Heap.Extends.snoc _ _) x hx)
            exact ⟨a, .lamBody cell (Binding.TmExact.addrIn_back hb x1 a ha'), hk⟩
        | .Forall (ld12 := ld) (he323 := hr) (hm322 := hm) (ev341 := e1) (ev377 := e2)
            (hc409 := hc) .. =>
          subst hc hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨T, B, ℓ, -, ht, hb, -⟩ := hE.forallE_of_load ld
          have x1 := e1.heap_extends
          have x2 := e2.heap_extends
          have st := Decl.rename_exact (Γ₂ := Γ) e1 ht rm
          have sb := Decl.rename_exact (Γ₂ := Γ) e2 (hb.mono x1) (rm.mono x1)
          intro x hx
          rcases Binding.addrIn_forall_inv (snoc_cell _ _) hx with hx | hx
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e1 rfl _ src dst k T rfl ht rm
              x (Binding.TmExact.addrIn_back st (x2.trans (Heap.Extends.snoc _ _)) x hx)
            exact ⟨a, .forallTy cell ha', hk⟩
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e2 rfl _ src dst (k + 1) B rfl
              (hb.mono x1) (rm.mono x1) x
              (Binding.TmExact.addrIn_back sb (Heap.Extends.snoc _ _) x hx)
            exact ⟨a, .forallBody cell (Binding.TmExact.addrIn_back hb x1 a ha'), hk⟩
        | .Let (ld12 := ld) (he436 := hr) (hm435 := hm) (ev454 := e1) (ev490 := e2)
            (ev526 := e3) (hc551 := hc) .. =>
          subst hc hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨T, V, B, -, ht, hv, hb⟩ := hE.letE_of_load ld
          have x1 := e1.heap_extends
          have x2 := e2.heap_extends
          have x3 := e3.heap_extends
          have st := Decl.rename_exact (Γ₂ := Γ) e1 ht rm
          have sv := Decl.rename_exact (Γ₂ := Γ) e2 (hv.mono x1) (rm.mono x1)
          have sb := Decl.rename_exact (Γ₂ := Γ) e3 (hb.mono (x1.trans x2))
            (rm.mono (x1.trans x2))
          intro x hx
          rcases Binding.addrIn_let_inv (snoc_cell _ _) hx with hx | hx | hx
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e1 rfl _ src dst k T rfl ht rm
              x (Binding.TmExact.addrIn_back st (x2.trans (x3.trans (Heap.Extends.snoc _ _))) x
                hx)
            exact ⟨a, .letTy cell ha', hk⟩
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e2 rfl _ src dst k V rfl
              (hv.mono x1) (rm.mono x1) x
              (Binding.TmExact.addrIn_back sv (x3.trans (Heap.Extends.snoc _ _)) x hx)
            exact ⟨a, .letVal cell (Binding.TmExact.addrIn_back hv x1 a ha'), hk⟩
          · obtain ⟨a, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e3 rfl _ src dst (k + 1) B rfl
              (hb.mono (x1.trans x2)) (rm.mono (x1.trans x2)) x
              (Binding.TmExact.addrIn_back sb (Heap.Extends.snoc _ _) x hx)
            exact ⟨a, .letBody cell (Binding.TmExact.addrIn_back hb (x1.trans x2) a ha'), hk⟩
        | .Proj (ld12 := ld) (he578 := hr) (hm577 := hm) (ev596 := e1) (ev639 := e2)
            (hc664 := hc) .. =>
          subst hc hr hm
          obtain ⟨addr, rfl, cell⟩ := Binding.TmExact.cell_of_load hE ld
          obtain ⟨a, i, Es, rfl, -, ra, hes⟩ := hE.proj_of_load ld
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := Decl.rename_addr_spec e1 ra rm
          have x2 := e2.heap_extends
          have ses := Decl.rename_exact (Γ₂ := Γ) e2 hes rm
          intro x hx
          rcases Binding.addrIn_proj_inv (snoc_cell _ _) hx with hx | hx
          · have e' : a' = x := Bytes.repAddressRef_inj U32.Goldilocks.compatible
              (Bytes.repAddressRef_heapMono₂ addrTy (x2.trans (Heap.Extends.snoc _ _)) ra') hx
            subst e'
            exact ⟨a, .projHead cell ra, hka⟩
          · obtain ⟨a₀, ha', hk⟩ := ih _ _ _ _ _ _ rename_lt_calls e2 rfl _ src dst k Es rfl hes
              rm x (Binding.TmExact.addrIn_back ses (Heap.Extends.snoc _ _) x hx)
            exact ⟨a₀, .projArg cell ha', hk⟩
        | .other (ld12 := ld) (hne84 := n1) (hne184 := n2) (hne297 := n3) (hne410 := n4)
            (hne552 := n5) (hne665 := n6) (he670 := hr) (he671 := hh) .. =>
          subst hr hh
          intro x hx
          exfalso
          cases hE with
          | bvarLocal cell => exact Binding.addrIn_none cell (by decide) hx
          | bvarFree cell => exact Binding.addrIn_none cell (by decide) hx
          | sort cell => exact Binding.addrIn_none cell (by decide) hx
          | litNat cell => exact Binding.addrIn_none cell (by decide) hx
          | litStr cell => exact Binding.addrIn_none cell (by decide) hx
          | const cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n1 _ rfl)
          | app cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n2 _ rfl)
          | lam cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n3 _ rfl)
          | forallE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n4 _ rfl)
          | letE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n5 _ rfl)
          | proj cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n6 _ rfl))
  intro e src dst r h h' cs k E ev hE rm
  exact hmain _ _ _ _ _ _ ev rfl e src dst k E rfl hE rm

/-! ## A term whose cells are stored, at the keying of the prefix -/

/-- **A term exact at the table's keying is exact at the keying of a prefix that stores the key
of each of its cells**: the prefix's keying is the table's at a stored key
(`Core.Ctx.stored_key_of_find`), and permits a projection there
(`Core.Ctx.stored_projPermitted_of_find`). -/
theorem tmExact_stored_of_cells {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Decl.TmExact (Core.keyOf t) d Γ h k E p) :
    (∀ a, AddrIn h p a → ∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) →
    Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact fun _ => .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact fun _ => .bvarFree cell hs hk hd
  | sort cell rl => exact fun _ => .sort cell rl
  | @const k addr ap lsp a ls res cell ra rls =>
    intro hc
    obtain ⟨ci, hci⟩ := hc a (.const cell ra)
    have e : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
      Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    have : Resolved ((Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a)) :=
      ⟨by rw [e]; exact res.ne⟩
    rw [← e]
    exact .const cell ra rls
  | app cell _ _ ihf iha =>
    exact fun hc => .app cell (ihf fun a m => hc a (.appFn cell m))
      (iha fun a m => hc a (.appArg cell m))
  | lam cell _ _ rl iht ihb =>
    exact fun hc => .lam cell (iht fun a m => hc a (.lamTy cell m))
      (ihb fun a m => hc a (.lamBody cell m)) rl
  | forallE cell _ _ rl iht ihb =>
    exact fun hc => .forallE cell (iht fun a m => hc a (.forallTy cell m))
      (ihb fun a m => hc a (.forallBody cell m)) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact fun hc => .letE cell (iht fun a m => hc a (.letTy cell m))
      (ihv fun a m => hc a (.letVal cell m)) (ihb fun a m => hc a (.letBody cell m))
  | litNat cell rl hc => exact fun _ => .litNat cell rl hc
  | litStr cell rb hs => exact fun _ => .litStr cell rb hs
  | @proj k addr ap ep a i E res pm cell ra _ ih =>
    intro hc
    obtain ⟨ci, hci⟩ := hc a (.projHead cell ra)
    have e : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
      Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    have : Resolved ((Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a)) :=
      ⟨by rw [e]; exact res.ne⟩
    have : ProjPermitted (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a) :=
      Core.Ctx.stored_projPermitted_of_find (c := ⟨E₀, env, t, lim⟩) hci
    rw [← e]
    exact .proj cell ra (ih fun a m => hc a (.projArg cell m))

/-! ## The renaming of a key -/

/-- **The renaming of a key is the key, or one of the models.** -/
theorem aliasMap_zip_cases (k : KKey) :
    ∀ (ks ds : List KKey), aliasMap (ks.zip ds) k = k ∨ aliasMap (ks.zip ds) k ∈ ds
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inl rfl
  | s :: ss, d :: ds => by
    simp only [List.zip_cons_cons, aliasMap]
    split
    · exact Or.inr (List.mem_cons_self ..)
    · rcases aliasMap_zip_cases k ss ds with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **A member's renaming is one of the models.** -/
theorem aliasMap_zip_mem (k : KKey) :
    ∀ (ks ds : List KKey), ks.length = ds.length → k ∈ ks → aliasMap (ks.zip ds) k ∈ ds
  | [], _, _, hk => nomatch hk
  | _ :: _, [], hl, _ => nomatch hl
  | s :: ss, d :: ds, hl, hk => by
    simp only [List.zip_cons_cons, aliasMap]
    split
    · exact List.mem_cons_self ..
    · rename_i hne
      rcases List.mem_cons.mp hk with e | hk'
      · exact absurd e hne
      · exact List.mem_cons_of_mem _ (aliasMap_zip_mem k ss ds (Nat.succ.inj hl) hk')

/-- **The renaming of a stored key or of a member is stored**, where every model is. -/
theorem aliasMap_zip_stored {env : Ix.Kernel.Env .anon} {ks ds : List KKey}
    (hlen : ks.length = ds.length) (hds : ∀ d ∈ ds, ∃ ci, env.find? d = some ci) {k : KKey}
    (hk : (∃ ci, env.find? k = some ci) ∨ k ∈ ks) :
    ∃ ci, env.find? (aliasMap (ks.zip ds) k) = some ci := by
  rcases hk with hk | hk
  · rcases aliasMap_zip_cases k ks ds with h | h
    · rw [h]
      exact hk
    · exact hds _ h
  · exact hds _ (aliasMap_zip_mem k ks ds hlen hk)

/-! ## The renamed term at the keying of a prefix -/

/-- **A term the check renames, after the renaming, at the keying of a prefix**: represented
exactly at the table's keying before, it is represented exactly at the keying of the prefix `env`
after, as its `renameAll` by the `aliasMap` of the lists, where the renaming of the key of each of
its cells is stored. -/
theorem rename_stored {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : Decl.TmExact (Core.keyOf t) 0 Γ₁ h k E e)
    (hcells : ∀ a, AddrIn h e a →
      ∃ ci, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (ixAddr a))) = some ci) :
    Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h' k
      (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b)))) E) r := by
  refine tmExact_stored_of_cells (rename_aliasMap hwf ev hlen hsrc hdst he) (fun x hx => ?_)
  obtain ⟨a, ha, hk⟩ :=
    rename_cells (Γ := Γ₁) ev he (renameMap_aliasMap hwf hlen hsrc hdst) x hx
  rw [hk]
  exact hcells a ha

/-- **The same, as `renameConsts`**, where no projection of the term names a member. -/
theorem rename_stored_consts {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : Decl.TmExact (Core.keyOf t) 0 Γ₁ h k E e)
    (hcells : ∀ a, AddrIn h e a →
      ∃ ci, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (ixAddr a))) = some ci)
    (hnp : Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) E = true) :
    Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h' k
      (E.renameConsts (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))) r := by
  have hout : ∀ k', (srcAs.map fun b => Core.keyOf t (ixAddr b)).contains k' = false →
      aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) k' = k' := by
    intro k' hk
    rw [← renameKeyList_eq_aliasMap]
    exact Decl.renameKeyList_out k' _ _ hk
  rw [← Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp]
  exact rename_stored hwf ev hlen hsrc hdst he hcells

/-- **The renamed term at the keying of a prefix that stores every model**, where each cell of
the term is stored or is a member. -/
theorem rename_stored_of_members {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : Decl.TmExact (Core.keyOf t) 0 Γ₁ h k E e)
    (hmodels : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci)
    (hcells : ∀ a, AddrIn h e a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ a ∈ srcAs) :
    Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h' k
      (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b)))) E) r := by
  refine rename_stored hwf ev hlen hsrc hdst he (fun a ha => ?_)
  refine aliasMap_zip_stored (by simp [hlen]) (fun d hd => ?_) ?_
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    exact hmodels b hb
  · rcases hcells a ha with hs | hm
    · exact Or.inl hs
    · exact Or.inr (List.mem_map.mpr ⟨a, hm, rfl⟩)

end IxVM.Refinement.Typing.FamilyAlias
