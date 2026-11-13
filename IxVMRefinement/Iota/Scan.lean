import IxVMRefinement.Iota.Basic

/-! # Step lemmas of `KernelWhnf`'s structure-η shape scans

The mention scan of a heap term (`se_mentions`), the constructor scan of a block member
(`struct_scan_ctors`), the member scan (`struct_scan_members`), the block's member addresses
(`struct_block_member_addrs`), the block-level `is_rec` (`struct_is_rec`) and the telescope peel
(`se_peel_tol`). The scans' claims are heap syntax (`HeapClean`, `ForallChain`, `ChainEnd`,
`FieldsClean`, `MembersClean`); the first section proves that heap extension preserves them, and
that a mention-free reading of a represented term at a later heap is one at the heap the term is
represented in. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core.Specs.Whnf
  (HeapClean ForallChain NotForallNode ChainEnd FieldsClean MembersClean)

set_option linter.unusedVariables false

/-! ## Helpers -/

theorem se_addrRep_mono {h₁ h₂ : Heap F} {a : Bytes.Address} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepAddr h₁ a p) : RepAddr h₂ a p :=
  Bytes.repAddressRef_heapMono₂ addrTy ext r

theorem se_addrs_mono {h₁ h₂ : Heap F} {ms : List Bytes.Address} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepList addrListEnum RepAddr h₁ ms p) :
    RepList addrListEnum RepAddr h₂ ms p :=
  r.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext

theorem se_val_natCast_le (x : Nat) : ZMod.val (x : F) ≤ x := by
  rw [ZMod.val_natCast]
  exact Nat.mod_le _ _

theorem se_mem_of_mem_drop {α : Type} {l : List α} {n : Nat} {x : α} (hx : x ∈ l.drop n) :
    x ∈ l := by
  induction l generalizing n with
  | nil => cases n <;> exact hx
  | cons a l ih =>
    cases n with
    | zero => exact hx
    | succ n => exact List.mem_cons_of_mem a (ih (n := n) hx)

theorem se_mem_drop_of_le {α : Type} {l : List α} {n m : Nat} {x : α} (hle : n ≤ m)
    (hx : x ∈ l.drop m) : x ∈ l.drop n := by
  induction l generalizing n m with
  | nil => cases m <;> cases n <;> exact hx
  | cons a l ih =>
    cases m with
    | zero =>
      obtain rfl : n = 0 := by omega
      exact hx
    | succ m =>
      cases n with
      | zero => exact List.mem_cons_of_mem a (se_mem_of_mem_drop (l := l) (n := m) hx)
      | succ n => exact ih (n := n) (m := m) (by omega) hx

theorem se_mem_drop_append {α : Type} {l₁ l₂ : List α} {n : Nat} {x : α}
    (hn : l₁.length ≤ n) (hx : x ∈ (l₁ ++ l₂).drop n) : x ∈ l₂ := by
  induction l₁ generalizing n with
  | nil => exact se_mem_of_mem_drop (l := [] ++ l₂) hx
  | cons a l ih =>
    cases n with
    | zero => rw [List.length_cons] at hn; omega
    | succ n => exact ih (n := n) (by rw [List.length_cons] at hn; omega) hx

/-- The type of a loaded constructor is a closed term. -/
theorem ci_ctor_ty {κ : _root_.Address → KKey} {h : Heap F} {w nl ty : SourceValue F}
    {rest : List (SourceValue F)} {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h w ci)
    (hw : w = .construct kciEnum "Ctor" (nl :: ty :: rest)) : ∃ T, TmC κ h T ty := by
  cases r with
  | ctor hv _ _ _ _ =>
    injection hw with _ _ hxs
    injection hxs with _ hrest
    injection hrest with hty
    subst hty
    exact ⟨_, hv.2.2.2⟩
  | axio _ | opaq _ | defn _ _ | thm _ _ | quot _ _ | induct _ _ _
  | recr _ _ _ _ _ _ _ _ _ _ _ =>
    injection hw with _ hc _
    exact absurd hc (by decide)

/-- The block of a loaded inductive is an address. -/
theorem ci_induct_blk {κ : _root_.Address → KKey} {h : Heap F}
    {w nl ty np ni nc u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h w ci) (hw : w = .construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) :
    ∃ b : Bytes.Address, RepAddr h b blk := by
  cases r with
  | induct _ _ hkey =>
    injection hw with _ _ hxs
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hxs
    obtain ⟨b, i, hb, -, -⟩ := hkey
    exact ⟨b, hb⟩
  | axio _ | opaq _ | defn _ _ | thm _ _ | quot _ _ | ctor _ _ _ _ _
  | recr _ _ _ _ _ _ _ _ _ _ _ =>
    injection hw with _ hc _
    exact absurd hc (by decide)

/-! ## Heap syntax: monotonicity -/

theorem heapClean_mono {P : Bytes.Address → Prop} {h₁ h₂ : Heap F} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hc : HeapClean P h₁ p) : HeapClean P h₂ p := by
  induction hc with
  | bvar hl => exact .bvar (ext.loadValue_eq hl)
  | srt hl => exact .srt (ext.loadValue_eq hl)
  | lit hl => exact .lit (ext.loadValue_eq hl)
  | const hl ha hP => exact .const (ext.loadValue_eq hl) (se_addrRep_mono ext ha) hP
  | app hl _ _ ihx ihy => exact .app (ext.loadValue_eq hl) ihx ihy
  | lam hl _ _ ihx ihy => exact .lam (ext.loadValue_eq hl) ihx ihy
  | forallE hl _ _ ihx ihy => exact .forallE (ext.loadValue_eq hl) ihx ihy
  | letE hl _ _ _ ihx ihy ihz => exact .letE (ext.loadValue_eq hl) ihx ihy ihz
  | proj hl _ ihe => exact .proj (ext.loadValue_eq hl) ihe

theorem forallChain_mono {h₁ h₂ : Heap F} {p q : SourceValue F} {ds : List (SourceValue F)}
    (ext : Heap.Extends h₁ h₂) (fc : ForallChain h₁ p ds q) : ForallChain h₂ p ds q := by
  induction fc with
  | nil => exact .nil
  | cons hl _ ih => exact .cons (ext.loadValue_eq hl) ih

theorem notForallNode_mono {h₁ h₂ : Heap F} {q : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (n : NotForallNode h₁ q) : NotForallNode h₂ q := by
  obtain ⟨ctor, xs, hl, hne⟩ := n
  exact ⟨ctor, xs, ext.loadValue_eq hl, hne⟩

theorem chainEnd_mono {h₁ h₂ : Heap F} {q : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (n : ChainEnd h₁ q) : ChainEnd h₂ q := by
  obtain ⟨ctor, xs, hl, hne1, hne2⟩ := n
  exact ⟨ctor, xs, ext.loadValue_eq hl, hne1, hne2⟩

theorem fieldsClean_mono {h₁ h₂ : Heap F} {p : Nat} {ms : List Bytes.Address}
    {ty : SourceValue F} (ext : Heap.Extends h₁ h₂) (fc : FieldsClean h₁ p ms ty) :
    FieldsClean h₂ p ms ty := by
  obtain ⟨ds, q, hch, hq, hcl⟩ := fc
  exact ⟨ds, q, forallChain_mono ext hch, chainEnd_mono ext hq,
    fun dp hdp => heapClean_mono ext (hcl dp hdp)⟩

theorem membersClean_mono {c : Ctx} {h₁ h₂ : Heap F} {ms membs : List Bytes.Address}
    (ext : Heap.Extends h₁ h₂) (mc : MembersClean c h₁ ms membs) : MembersClean c h₂ ms membs := by
  intro m hm cm cb p xs ind h1 h2 h3 h4 h5 t ht
  obtain ⟨cicon, w, nl, ty, rest, hf, hci, hw, hfc⟩ := mc m hm cm cb p xs ind h1 h2 h3 h4 h5 t ht
  exact ⟨cicon, w, nl, ty, rest, hf, CIRep.mono ext hci, hw, fieldsClean_mono ext hfc⟩

/-- Skipping more binders keeps the fields clean. -/
theorem fieldsClean_le {h : Heap F} {p p' : Nat} {ms : List Bytes.Address} {ty : SourceValue F}
    (hle : p ≤ p') (fc : FieldsClean h p ms ty) : FieldsClean h p' ms ty := by
  obtain ⟨ds, q, hch, hq, hcl⟩ := fc
  exact ⟨ds, q, hch, hq, fun dp hdp => hcl dp (se_mem_drop_of_le hle hdp)⟩

theorem forallChain_append {h : Heap F} {p q s : SourceValue F} {ds es : List (SourceValue F)}
    (f1 : ForallChain h p ds q) (f2 : ForallChain h q es s) : ForallChain h p (ds ++ es) s := by
  revert f2
  induction f1 with
  | nil => exact fun f2 => f2
  | cons hl _ ih => exact fun f2 => by rw [List.cons_append]; exact .cons hl (ih f2)

/-- The end of a `∀` chain of a represented term is represented, under the chain's binders. -/
theorem tm_forallChain {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {p q : SourceValue F} {ds : List (SourceValue F)} (fc : ForallChain h p ds q) :
    ∀ {k : Nat} {E : KExpr}, Tm κ d Γ h k E p → ∃ E', Tm κ d Γ h (k + ds.length) E' q := by
  induction fc with
  | nil => intro k E hE; exact ⟨E, by simpa using hE⟩
  | @cons p' dom cod lvl q' ds' hl _ ih =>
    intro k E hE
    obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE.forallE_of_load hl
    obtain ⟨E', hE'⟩ := ih hB
    refine ⟨E', ?_⟩
    rw [List.length_cons, show k + (ds'.length + 1) = k + 1 + ds'.length by omega]
    exact hE'

/-- **A mention-free reading at a later heap is one at the heap of the representation**: every
node of a represented term is a cell of `h`, which loads the same at `m`, and a constant's address
is the same address there (`addr_det`). -/
theorem heapClean_of_extends {P : Bytes.Address → Prop} {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h m : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h m) (rep : Tm κ d Γ h k E p) (hc : HeapClean P m p) :
    HeapClean P h p := by
  revert hc
  induction rep with
  | bvarLocal cell _ _ => exact fun _ => .bvar (loadValue_enum_cell cell)
  | bvarFree cell _ _ _ => exact fun _ => .bvar (loadValue_enum_cell cell)
  | sort cell _ _ => exact fun _ => .srt (loadValue_enum_cell cell)
  | litNat cell _ _ => exact fun _ => .lit (loadValue_enum_cell cell)
  | litStr cell _ _ => exact fun _ => .lit (loadValue_enum_cell cell)
  | const cell ra _ _ =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | const hl ha hP =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with e1 _
      subst e1
      refine .const (loadValue_enum_cell cell) ra ?_
      rwa [addr_det (se_addrRep_mono ext ra) ha]
    | bvar hl | srt hl | lit hl | app hl _ _ | lam hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell' hl (by decide)).elim
  | app cell _ _ ihf iha =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | app hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with e1 hrest
      injection hrest with e2
      subst e1 e2
      exact .app (loadValue_enum_cell cell) (ihf hx) (iha hy)
    | bvar hl | srt hl | lit hl | const hl _ _ | lam hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell' hl (by decide)).elim
  | lam cell _ _ _ iht ihb =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | lam hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with e1 hrest
      injection hrest with e2 _
      subst e1 e2
      exact .lam (loadValue_enum_cell cell) (iht hx) (ihb hy)
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell' hl (by decide)).elim
  | forallE cell _ _ _ iht ihb =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | forallE hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with e1 hrest
      injection hrest with e2 _
      subst e1 e2
      exact .forallE (loadValue_enum_cell cell) (iht hx) (ihb hy)
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell' hl (by decide)).elim
  | letE cell _ _ _ iht ihv ihb =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | letE hl hx hy hz =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with e1 hrest
      injection hrest with e2 hrest'
      injection hrest' with e3
      subst e1 e2 e3
      exact .letE (loadValue_enum_cell cell) (iht hx) (ihv hy) (ihb hz)
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | forallE hl _ _
    | proj hl _ => exact (load_cell_ne cell' hl (by decide)).elim
  | proj cell _ _ ihe =>
    intro hc
    have cell' := ext.getElem?_eq cell
    cases hc with
    | proj hl he =>
      obtain ⟨-, hxs⟩ := load_cell cell' hl
      injection hxs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with e3
      subst e3
      exact .proj (loadValue_enum_cell cell) (ihe he)
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | forallE hl _ _
    | letE hl _ _ _ => exact (load_cell_ne cell' hl (by decide)).elim

/-! ## `se_mentions` -/

/-- `KernelWhnf::se_mentions` walks the heap term, asking `se_addr_in` at each constant. -/
theorem se_mentions_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::se_mentions" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.se_mentions c args h r h' calls := by
  intro e xs hargs good ms hms hE hr
  subst hargs
  obtain ⟨d, Γ, k, E, hE⟩ := hE
  rcases Obs.«KernelWhnf::se_mentions».obs ev with
    ⟨x_a, w20, cs34, ld12, ev36, hc53⟩ |
    ⟨x_f, x_x, m72, cs83, ld12, ev85, he106, he107, hc108⟩ |
    ⟨x_f, x_x, v71, m72, cs83, cs116, ld12, ev85, hne109, ev118, hc135⟩ |
    ⟨x_t, x_b, w143, m160, cs171, ld12, ev173, he194, he195, hc196⟩ |
    ⟨x_t, x_b, w143, v159, m160, cs171, cs204, ld12, ev173, hne197, ev206, hc223⟩ |
    ⟨x_t, x_b, w231, m248, cs259, ld12, ev261, he282, he283, hc284⟩ |
    ⟨x_t, x_b, w231, v247, m248, cs259, cs292, ld12, ev261, hne285, ev294, hc311⟩ |
    ⟨x_t, x_v, x_b, m335, cs346, ld12, ev348, he369, he370, hc371⟩ |
    ⟨x_t, x_v, x_b, v334, m335, cs346, m377, cs388, ld12, ev348, hne372, ev390, he411, he412,
      hc413⟩ |
    ⟨x_t, x_v, x_b, v334, m335, cs346, v376, m377, cs388, cs421, ld12, ev348, hne372, ev390,
      hne414, ev423, hc440⟩ |
    ⟨w448, w449, x_inner, cs468, ld12, ev470, hc487⟩ |
    ⟨v1, ld12, hne54, hne136, hne224, hne312, hne441, hne488, he492, he493, hc494⟩
  · -- `Const`: the answer of `se_addr_in`
    obtain ⟨a, us, rfl, ha, -⟩ := hE.const_of_load ld12
    subst hc53
    obtain ⟨hr', -⟩ := ih.get (.whnf .se_addr_in) (by lt_calls) ev36 x_a xs rfl
      (good.sub fun z hz => by simp [hz]) a ms ha hms
    refine .const ld12 ha ?_
    intro hm
    have hm' : a ∈ ms := hm
    apply hr
    rw [hr']
    simp [hm']
  · exact absurd he106 hr
  · obtain ⟨Ef, Ea, rfl, hf, hx⟩ := hE.app_of_load ld12
    subst hc135
    have ext := ObsFn.heap_extends ev85
    have c1 := ih.get (.whnf .se_mentions) (by lt_calls) ev85 x_f xs rfl
      (good.sub fun z hz => by simp [hz]) ms hms ⟨d, Γ, k, Ef, hf⟩ hne109
    have c2 := ih.get (.whnf .se_mentions) (by lt_calls) ev118 x_x xs rfl
      (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono ext hms)
      ⟨d, Γ, k, Ea, Tm.mono ext hx⟩ hr
    exact .app ld12 c1 (heapClean_of_extends ext hx c2)
  · exact absurd he194 hr
  · obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := hE.lam_of_load ld12
    subst hc223
    have ext := ObsFn.heap_extends ev173
    have c1 := ih.get (.whnf .se_mentions) (by lt_calls) ev173 x_t xs rfl
      (good.sub fun z hz => by simp [hz]) ms hms ⟨d, Γ, k, T, ht⟩ hne197
    have c2 := ih.get (.whnf .se_mentions) (by lt_calls) ev206 x_b xs rfl
      (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono ext hms)
      ⟨d, Γ, k + 1, B, Tm.mono ext hb⟩ hr
    exact .lam ld12 c1 (heapClean_of_extends ext hb c2)
  · exact absurd he282 hr
  · obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := hE.forallE_of_load ld12
    subst hc311
    have ext := ObsFn.heap_extends ev261
    have c1 := ih.get (.whnf .se_mentions) (by lt_calls) ev261 x_t xs rfl
      (good.sub fun z hz => by simp [hz]) ms hms ⟨d, Γ, k, T, ht⟩ hne285
    have c2 := ih.get (.whnf .se_mentions) (by lt_calls) ev294 x_b xs rfl
      (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono ext hms)
      ⟨d, Γ, k + 1, B, Tm.mono ext hb⟩ hr
    exact .forallE ld12 c1 (heapClean_of_extends ext hb c2)
  · exact absurd he369 hr
  · exact absurd he411 hr
  · obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld12
    subst hc440
    have ext1 := ObsFn.heap_extends ev348
    have ext2 := ObsFn.heap_extends ev390
    have c1 := ih.get (.whnf .se_mentions) (by lt_calls) ev348 x_t xs rfl
      (good.sub fun z hz => by simp [hz]) ms hms ⟨d, Γ, k, T, ht⟩ hne372
    have c2 := ih.get (.whnf .se_mentions) (by lt_calls) ev390 x_v xs rfl
      (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono ext1 hms)
      ⟨d, Γ, k, V, Tm.mono ext1 hv⟩ hne414
    have c3 := ih.get (.whnf .se_mentions) (by lt_calls) ev423 x_b xs rfl
      (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono (ext1.trans ext2) hms)
      ⟨d, Γ, k + 1, B, Tm.mono (ext1.trans ext2) hb⟩ hr
    exact .letE ld12 c1 (heapClean_of_extends ext1 hv c2)
      (heapClean_of_extends (ext1.trans ext2) hb c3)
  · obtain ⟨a, i, Es, -, rfl, -, hes⟩ := hE.proj_of_load ld12
    subst hc487
    have c1 := ih.get (.whnf .se_mentions) (by lt_calls) ev470 x_inner xs rfl
      (good.sub fun z hz => by simp [hz]) ms hms ⟨d, Γ, k, Es, hes⟩ hr
    exact .proj ld12 c1
  · -- any other node: a variable, a sort or a literal
    cases hE with
    | bvarLocal cell _ _ => exact .bvar (loadValue_enum_cell cell)
    | bvarFree cell _ _ _ => exact .bvar (loadValue_enum_cell cell)
    | sort cell _ _ => exact .srt (loadValue_enum_cell cell)
    | litNat cell _ _ => exact .lit (loadValue_enum_cell cell)
    | litStr cell _ _ => exact .lit (loadValue_enum_cell cell)
    | const cell _ _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne54 _ (by rfl) hv.symm).elim
    | app cell _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne136 _ (by rfl) hv.symm).elim
    | lam cell _ _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne224 _ (by rfl) hv.symm).elim
    | forallE cell _ _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne312 _ (by rfl) hv.symm).elim
    | letE cell _ _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne441 _ (by rfl) hv.symm).elim
    | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld12
      injection ld12 with hv
      exact (hne488 _ (by rfl) hv.symm).elim

/-! ## `struct_scan_ctors` -/

/-- `KernelWhnf::struct_scan_ctors` loads constructor `c` (`Ingress::get_ci_cprj`), peels the
member's parameters (`se_peel_tol`) and scans the remaining fields (`se_scan_fields`), then
moves to `c + 1`. The chain before the parameters and the chain the field scan reads are one
chain; the parameters cover at least the first. -/
theorem struct_scan_ctors_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::struct_scan_ctors" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.struct_scan_ctors c args h r h' calls := by
  intro blk idx nc np xs ci hargs good b i n p j ms hb hi hn hp hms hj hr
  subst hargs hi hn hp hj
  rcases Obs.«KernelWhnf::struct_scan_ctors».obs ev with
    ⟨op17, he24, he25, hc26⟩ |
    ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, m166,
      cs177, op17, hne27, ev47, ld41, ev148, ev179, he200, he201, hc202⟩ |
    ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, v165,
      m166, cs177, cs210, v218, op17, hne27, ev47, ld41, ev148, ev179, hne203, op267, ev212,
      hc269⟩ |
    ⟨v1, v31, m32, p39, cs45, op17, hne27, ev47, ld41, hne270, he274, he275, hc276⟩
  · have h0 : n - j = 0 := (NatAux.field_inj (NatAux.sub_ok op17)).symm
    intro t ht
    rw [h0, ZMod.val_zero] at ht
    exact absurd ht (Nat.not_lt_zero _)
  · exact absurd he200 hr
  · have hv := NatAux.sub_ok op17
    subst hv
    have hnj : n - j ≠ 0 := fun e => hne27 (by rw [e])
    have hv2 := NatAux.add_ok op267
    subst hv2 hc269
    have e1 := ObsFn.heap_extends ev47
    have e2 := ObsFn.heap_extends ev179
    have e3 := ObsFn.heap_extends ev212
    obtain ⟨ci0, hfind, v, hv, hci⟩ := ih.get (.callees .get_ci_cprj) (by lt_calls) ev47 blk i j b
      rfl (good.sub fun z hz => by simp [hz]) hb
    rw [ld41] at hv
    injection hv with hv
    subst hv
    obtain ⟨T, hT⟩ := ci_ctor_ty hci rfl
    obtain ⟨rfl, ds1, hch1, hle1, -⟩ := ih.get (.whnf .se_peel_tol) (by lt_calls) ev148 x_cty
      (.field p) rfl (good.sub fun z hz => by simp [hz]) p rfl ⟨0, fun _ => T, 0, T, hT 0 (fun _ => T)⟩
    obtain ⟨E1, hE1⟩ := tm_forallChain hch1 (hT 0 (fun _ => T))
    obtain ⟨ds2, q, hch2, hq, hcl⟩ := ih.get (.whnf .se_scan_fields) (by lt_calls) ev179 v135 xs
      rfl (good.sub fun z hz => by simp [hz]) ms (se_addrs_mono e1 hms)
      ⟨0, fun _ => T, 0 + ds1.length, E1, hE1⟩ hne203
    have hrec := ih.get (.whnf .struct_scan_ctors) (by lt_calls) ev212 blk (.field i) (.field n)
      (.field p) xs (.field (j + 1)) rfl (good.sub fun z hz => by simp [hz]) b i n p (j + 1) ms
      (se_addrRep_mono (e1.trans e2) hb) rfl rfl rfl (se_addrs_mono (e1.trans e2) hms) rfl hr
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · refine ⟨ci0, _, w88, x_cty, [w89, w90, w91, w92, w93, w94], ?_,
        CIRep.mono (e2.trans e3) hci, rfl, ?_⟩
      · simpa using hfind
      · refine ⟨ds1 ++ ds2, q, forallChain_mono (e2.trans e3) (forallChain_append hch1 hch2),
          chainEnd_mono (e2.trans e3) hq, ?_⟩
        intro dp hdp
        exact heapClean_mono (e2.trans e3) (hcl dp (se_mem_drop_append hle1 hdp))
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hlt : t' < ZMod.val (n - (j + 1)) := by
        have := Lib.val_sub_one hnj
        rw [show n - (j + 1) = n - j - 1 by ring]
        omega
      obtain ⟨cicon, w, nl', ty', rest, hf, hci', hw, hfc⟩ := hrec t' hlt
      refine ⟨cicon, w, nl', ty', rest, ?_, hci', hw, hfc⟩
      have e : j + ((t' + 1 : Nat) : F) = j + 1 + (t' : F) := by push_cast; ring
      rw [e]
      exact hf
  · exact absurd he274 hr

/-! ## `struct_scan_members` -/

/-- `KernelWhnf::struct_scan_members` loads each address (`Ingress::get_ci`) and scans the
constructors of an inductive (`struct_scan_ctors`); `LoadFacts.indRecord` ties the loaded
inductive's counts, block and index to the records, and its bounds read the field elements back
as the records' numbers. -/
theorem struct_scan_members_step (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::struct_scan_members" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.struct_scan_members c args h r h' calls := by
  intro msp xs hargs good ms membs hms hmembs hr
  subst hargs
  rcases Obs.«KernelWhnf::struct_scan_members».obs ev with
    ⟨ld12, he20, he21, hc22⟩ |
    ⟨x_m, x_rest, m41, p49, cs55, w72, w73, x_n_params, w74, x_num_ctors, w75, x_block, x_idx,
      m117, cs128, ld12, ev57, ld51, ev130, he182, he183, hc184⟩ |
    ⟨x_m, x_rest, m41, p49, cs55, w72, w73, x_n_params, w74, x_num_ctors, w75, x_block, x_idx,
      v116, m117, cs128, cs192, ld12, ev57, ld51, ev130, hne185, ev194, hc211⟩ |
    ⟨x_m, x_rest, v40, m41, p49, cs55, cs219, ld12, ev57, ld51, hne212, ev221, hc238⟩
  · obtain rfl := RepList.nil_of_load hms ld12
    intro m hm
    simp at hm
  · exact absurd he182 hr
  · obtain ⟨a, ms', rfl, ha, hms'⟩ := RepList.cons_of_load hms ld12
    subst hc211
    have e1 := ObsFn.heap_extends ev57
    have e2 := ObsFn.heap_extends ev130
    have e3 := ObsFn.heap_extends ev194
    have hrest := ih.get (.whnf .struct_scan_members) (by lt_calls) ev194 x_rest xs rfl
      (good.sub fun z hz => by simp [hz]) ms' membs (se_addrs_mono (e1.trans e2) hms')
      (se_addrs_mono (e1.trans e2) hmembs) hr
    intro m hm cm cb pp ys ind h1 h2 h3 h4 h5
    rcases List.mem_cons.mp hm with rfl | hm'
    · obtain ⟨nl, ty, u, blk, b, hl, hb, hbb, hidx, hsize⟩ := hc.loads.indRecord x_m p49 h m41
        cs55 m cm cb pp ys ind ev57 (good.sub fun z hz => by simp [hz]) ha h1 h2 h3 h4 h5
      have hidx' : pp.idx.toNat < 18446744069414584321 := lt_trans hidx (by norm_num)
      have hsize' : ind.ctors.size < 18446744069414584321 := lt_trans hsize (by norm_num)
      rw [ld51] at hl
      injection hl with hl
      injection hl with _ _ hl
      simp only [List.cons.injEq, and_true] at hl
      obtain ⟨-, -, rfl, -, rfl, -, rfl, rfl⟩ := hl
      have hsc := ih.get (.whnf .struct_scan_ctors) (by lt_calls) ev130 x_block
        (.field (pp.idx.toNat : F)) (.field (ind.ctors.size : F)) (.field (ind.params.toNat : F))
        xs (.field 0) rfl (good.sub fun z hz => by simp [hz]) b (pp.idx.toNat : F)
        (ind.ctors.size : F) (ind.params.toNat : F) 0 membs hb rfl rfl rfl
        (se_addrs_mono e1 hmembs) rfl hne185
      intro t ht
      have ht' : t < ZMod.val ((ind.ctors.size : F) - 0) := by
        rw [sub_zero, NatAux.val_natCast hsize']
        exact ht
      obtain ⟨cicon, w, nl', ty', rest, hf, hci, hw, hfc⟩ := hsc t ht'
      refine ⟨cicon, w, nl', ty', rest, ?_, CIRep.mono e3 hci, hw,
        fieldsClean_le (se_val_natCast_le _) (fieldsClean_mono e3 hfc)⟩
      rw [zero_add, NatAux.val_natCast (n := t) (by omega), NatAux.val_natCast hidx', hbb] at hf
      exact hf
    · exact hrest m hm' cm cb pp ys ind h1 h2 h3 h4 h5
  · obtain ⟨a, ms', rfl, ha, hms'⟩ := RepList.cons_of_load hms ld12
    subst hc238
    have e1 := ObsFn.heap_extends ev57
    have hrest := ih.get (.whnf .struct_scan_members) (by lt_calls) ev221 x_rest xs rfl
      (good.sub fun z hz => by simp [hz]) ms' membs (se_addrs_mono e1 hms')
      (se_addrs_mono e1 hmembs) hr
    intro m hm cm cb pp ys ind h1 h2 h3 h4 h5
    rcases List.mem_cons.mp hm with rfl | hm'
    · obtain ⟨nl, ty, u, blk, b, hl, -, -, -, -⟩ := hc.loads.indRecord x_m p49 h m41 cs55 m cm cb
        pp ys ind ev57 (good.sub fun z hz => by simp [hz]) ha h1 h2 h3 h4 h5
      rw [ld51] at hl
      injection hl with hl
      exact (hne212 _ (by rfl) hl).elim
    · exact hrest m hm' cm cb pp ys ind h1 h2 h3 h4 h5

/-! ## `struct_block_member_addrs` -/

/-- A decoded record whose info is a `Muts` node is a block, with its members. -/
theorem infoShape_muts {h : Heap F} {info : Ixon.ConstantInfo} {x : SourceValue F}
    (hs : Specs.Callees.InfoShape h info (.construct Specs.Callees.ixInfoEnum "Muts" [x])) :
    ∃ ms, info = .muts ms ∧ Specs.Callees.MembersRep h ms.toList x := by
  cases info with
  | muts ms =>
    obtain ⟨lp, hv, hm⟩ := hs
    injection hv with _ _ hv
    injection hv with hv
    subst hv
    exact ⟨ms, rfl, hm⟩
  | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
    obtain ⟨y, hv⟩ := hs
    injection hv with _ hc _
    revert hc
    simp +decide [Specs.Callees.infoCtor]

/-- `KernelWhnf::struct_block_member_addrs` loads the record at the block
(`Ingress::load_verified_constant`): at a block it builds the members' projection-record
addresses (`Ingress::build_recur_addrs`), otherwise the one-element list of the parent. -/
theorem struct_block_member_addrs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::struct_block_member_addrs" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.struct_block_member_addrs c args h r h' calls := by
  intro par blk hargs good p b hp hb cb hcb
  subst hargs
  rcases Obs.«KernelWhnf::struct_block_member_addrs».obs ev with
    ⟨m2, cs12, w39, w40, w41, w42, x_members, cs92, ev14, ev94, hc111⟩ |
    ⟨m2, cs12, x_info, w39, w40, w41, w42, m134, ev14, hne112, he120, hm119, hm142, hc146⟩
  · subst hc111
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨-, hshape⟩ := ih.get (.callees .load_verified_constant) (by lt_calls) ev14 blk b rfl
      (good.sub fun z hz => by simp [hz]) hb
    obtain ⟨info, sh, rf, un, hv, hinfo⟩ := hshape cb hcb
    injection hv with _ _ hv
    injection hv with hi _
    subst hi
    obtain ⟨ms, hms, hmr⟩ := infoShape_muts hinfo
    obtain ⟨as, has, hmap⟩ := ih.get (.callees .build_recur_addrs) (by lt_calls) ev94 x_members
      blk ms.toList b rfl (good.sub fun z hz => by simp [hz]) hmr (se_addrRep_mono e1 hb)
    refine ⟨as, has, ?_, fun hn => absurd hms (hn ms)⟩
    intro ms' hms' i ind hi
    rw [hms] at hms'
    injection hms' with e
    subst e
    have h1 : ms.toList[i]? = some (.indc ind) := by simpa using hi
    have h2 : (as.map ixAddr)[i]? = some (iprjAddr (ixAddr b) i) := by
      rw [hmap, List.getElem?_mapIdx, h1]
      try rfl
    rw [List.getElem?_map] at h2
    cases ha : as[i]? with
    | none =>
      rw [ha] at h2
      simp at h2
    | some a =>
      rw [ha] at h2
      exact ⟨a, List.mem_of_getElem? ha, Option.some.inj h2⟩
  · subst hc146 hm142 hm119 he120
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨-, hshape⟩ := ih.get (.callees .load_verified_constant) (by lt_calls) ev14 blk b rfl
      (good.sub fun z hz => by simp [hz]) hb
    obtain ⟨info, sh, rf, un, hv, hinfo⟩ := hshape cb hcb
    injection hv with _ _ hv
    injection hv with hi _
    subst hi
    refine ⟨[p], Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
      (se_addrRep_mono (e1.trans (Heap.Extends.snoc _ _)) hp) (Lib.rep_store_nil m2), ?_,
      fun _ => rfl⟩
    intro ms hms i ind hi
    rw [hms] at hinfo
    obtain ⟨lp, hv', -⟩ := hinfo
    exact (hne112 _ (by rfl) hv').elim

/-! ## `struct_is_rec` -/

/-- `KernelWhnf::struct_is_rec` loads the parent (`Ingress::get_ci`), and at a single-inductive
block scans the block's member list against itself. The block IxVM loaded is the parent's block
in the records (`LoadFacts.indRecord`, `addr_det`); with no record at the block the member list
is taken empty. -/
theorem struct_is_rec_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::struct_is_rec" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.struct_is_rec c args h r h' calls := by
  intro par hargs good p hp hr
  subst hargs
  rcases Obs.«KernelWhnf::struct_is_rec».obs ev with
    ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, m90, cs101, v116, m117, cs127,
      cs149, ev17, ld11, ev103, ev129, ev151, hc168⟩ |
    ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, v89, m90, cs101, ev17, ld11, ev103,
      hne169, he173, he174, hc175⟩ |
    ⟨v1, m2, p9, cs15, ev17, ld11, hne176, he180, he181, hc182⟩
  · subst hc168
    have e1 := ObsFn.heap_extends ev17
    have e2 := ObsFn.heap_extends ev103
    obtain ⟨ci, -, v, hv, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev17 par p rfl
      (good.sub fun z hz => by simp [hz]) hp
    rw [ld11] at hv
    injection hv with hv
    subst hv
    obtain ⟨b, hb⟩ := ci_induct_blk hci rfl
    have hmem := ih.get (.whnf .struct_block_member_addrs) (by lt_calls) ev129 par
      x_block rfl (good.sub fun z hz => by simp [hz]) p b (se_addrRep_mono (e1.trans e2) hp)
      (se_addrRep_mono e2 hb)
    have hpar : ∀ (cm cb : Ixon.Constant) (pp : Ixon.InductiveProj) (ys : Array Ixon.MutConst)
        (ind : Ixon.Inductive),
        Ix.Cert.recordAt c.E (ixAddr p) = some cm → cm.info = .iPrj pp →
        Ix.Cert.recordAt c.E pp.block = some cb → cb.info = .muts ys →
        ys[pp.idx.toNat]? = some (.indc ind) → ixAddr b = pp.block := by
      intro cm cb pp ys ind h1 h2 h3 h4 h5
      obtain ⟨nl, ty, u, blk, b', hl, hb', hbb, -, -⟩ := hc.loads.indRecord par p9 h m2 cs15 p cm
        cb pp ys ind ev17 (good.sub fun z hz => by simp [hz]) hp h1 h2 h3 h4 h5
      rw [ld11] at hl
      injection hl with hl
      injection hl with _ _ hl
      simp only [List.cons.injEq, and_true] at hl
      obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hl
      rw [addr_det hb hb', hbb]
    cases hrec : Ix.Cert.recordAt c.E (ixAddr b) with
    | none =>
      refine ⟨b, [], ?_, hpar, fun cb hcb => ?_⟩
      · intro m hm
        simp at hm
      · rw [hrec] at hcb
        cases hcb
    | some cb0 =>
      obtain ⟨ms, hms, hall, hnot⟩ := hmem cb0 hrec
      have hmc := ih.get (.whnf .struct_scan_members) (by lt_calls) ev151 v116 v116 rfl
        (good.sub fun z hz => by simp [hz]) ms ms hms hms hr
      refine ⟨b, ms, hmc, hpar, fun cb hcb => ?_⟩
      rw [hrec] at hcb
      injection hcb with hcb
      subst hcb
      exact ⟨hall, hnot⟩
  · exact absurd he173 hr
  · exact absurd he180 hr

/-! ## `se_peel_tol` -/

theorem se_peel_tol_aux (c : Ctx) (N : Nat) :
    ∀ {ty n : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)},
      calls.length < N → ObsFn W "KernelWhnf::se_peel_tol" [ty, n] h r h' calls →
      ∀ m : F, n = .field m → ∀ d Γ k T, c.tmk d Γ k h T ty →
        h' = h ∧ ∃ ds, ForallChain h ty ds r ∧ ds.length ≤ ZMod.val m ∧
          (ds.length < ZMod.val m → NotForallNode h r) := by
  induction N with
  | zero => intro _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro ty n h h' r calls hlt ev m hn d Γ k T hT
    subst hn
    rcases Obs.«KernelWhnf::se_peel_tol».obs ev with
      ⟨hv14, he16, he17, hc18⟩ |
      ⟨w42, x_body, w43, cs62, v66, hne19, ld34, op87, ev64, hc89⟩ |
      ⟨v23, hne19, ld34, hne90, he95, he96, hc97⟩
    · injection hv14 with hm
      subst hm he16 he17
      exact ⟨rfl, [], .nil, by simp, fun h0 => by simp at h0⟩
    · have hm0 : m ≠ 0 := fun e => hne19 (by rw [e])
      have hv := NatAux.sub_ok op87
      subst hv hc89
      obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld34
      obtain ⟨rfl, ds, hch, hle, hnf⟩ := ihN (by simp only [List.length_cons] at hlt; omega) ev64
        (m - 1) rfl d Γ (k + 1) B hB
      have hs := Lib.val_sub_one hm0
      refine ⟨rfl, w42 :: ds, .cons ld34 hch, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro hlt'
        rw [List.length_cons] at hlt'
        exact hnf (by omega)
    · subst he95 he96
      refine ⟨rfl, [], .nil, Nat.zero_le _, fun _ => ?_⟩
      cases hT with
      | forallE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld34
        injection ld34 with hv
        exact (hne90 _ (by rfl) hv.symm).elim
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
      | proj cell _ _ => exact ⟨_, _, loadValue_enum_cell cell, by decide⟩

/-- `KernelWhnf::se_peel_tol` walks up to `n` `∀` nodes of the represented type; at a node other
than a `∀` node the walk stops, and that node is a term node. -/
theorem se_peel_tol_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::se_peel_tol" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.se_peel_tol c args h r h' calls := by
  rintro ty n rfl good m hn ⟨d, Γ, k, T, hT⟩
  exact se_peel_tol_aux c (calls.length + 1) (Nat.lt_succ_self _) ev m hn d Γ k T hT

end IxVM.Refinement.Core
