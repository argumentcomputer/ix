import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Binding.ReadsLocal

/-! # The flattened family's derivation reads only the block and its nested containers' blocks

`derivedFlatAt` reads a store through a `FlatView`: the members of the block `B`, the inductive
types at the addresses it meets (each read off its projection record and that record's block),
the constructor types of the entries' blocks, and the addresses that keys name. Every address it
reads is reached from `B` by a block's member, a projection's block, or a key in a constructor
type it reads, or in an occurrence's parameters taken from such a type. So it reads nothing
outside a set of addresses closed under those steps (`FlatView.ClosedOn`), and a view that
answers as the first on such a set derives the same entries (`derivedFlatAt_leOn`).

Over stores:

* `blockDerivedFlat_of_closed_sub`: a sub-store of `E₀` closed under used references and owners
  (`UsedClosed`) that holds the block and `E₀`'s blobs derives the same entries: the addresses
  the store holds are such a set, since a constructor type's keys are the keys of references its
  block uses or of the block's own members (`read_keys`), and the role table's keys name their
  addresses (`keyAddr_keyOf`);
* `blockDerivedFlat_grow`: a store that holds the records and blobs of the first derives the same
  entries (`ofStore_le`);
* `RecordFlat.of_blobs`: the record's entries read the same over a store holding the first's
  blobs (the reading is over the record's own tables and the blobs);
* `familyOfBlock_of_closed`: the family of a block over a store closed under block members that
  holds the block and its family record (the readers read the two records only). -/

namespace IxVM.Refinement.Binding.FamilyFlat

open IxVM.Consistency
open IxVM.Refinement.ReaderReads (exprReader_mono)

set_option linter.unusedVariables false

/-! ## Keys of the terms the derivation builds -/

section Keys

variable {k : Ix.Kernel.Key .anon}

/-- A key of a lowered term is a key of the term. -/
theorem keyIn_lowerBVars (a : Nat) : ∀ (e : Ix.Kernel.Expr .anon) (c : Nat),
    KeyIn k (Ix.Kernel.Expr.lowerBVars a c e) → KeyIn k e := by
  intro e
  induction e with
  | bvar i =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    split at h <;> cases h
  | fvar i ty _ =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    exact h
  | sort u =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    exact h
  | const n us =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    exact h
  | app f x ihf ihx =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    cases h with
    | appFn h => exact .appFn (ihf c h)
    | appArg h => exact .appArg (ihx c h)
  | lam t b m iht ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    cases h with
    | lamTy h => exact .lamTy (iht c h)
    | lamBody h => exact .lamBody (ihb (c + 1) h)
  | forallE t b m iht ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    cases h with
    | allTy h => exact .allTy (iht c h)
    | allBody h => exact .allBody (ihb (c + 1) h)
  | letE t v b l iht ihv ihb =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    cases h with
    | letTy h => exact .letTy (iht c h)
    | letVal h => exact .letVal (ihv c h)
    | letBody h => exact .letBody (ihb (c + 1) h)
  | lit l =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    exact h
  | proj s i x ih =>
    intro c h
    simp only [Ix.Kernel.Expr.lowerBVars] at h
    cases h with
    | proj => exact .proj _ _
    | projBody h => exact .projBody (ih c h)

/-- A key of a term with a bound variable replaced is a key of the term or of the replacement. -/
theorem keyIn_instantiate1 (v : Ix.Kernel.Expr .anon) : ∀ (e : Ix.Kernel.Expr .anon) (d : Nat),
    KeyIn k (Ix.Kernel.Expr.instantiate1 e v d) → KeyIn k e ∨ KeyIn k v := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    split at h
    · exact Or.inr h
    · split at h <;> cases h
  | fvar i ty _ =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    exact Or.inl h
  | sort u =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    exact Or.inl h
  | const n us =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    exact Or.inl h
  | app f x ihf ihx =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    cases h with
    | appFn h => exact (ihf d h).imp_left .appFn
    | appArg h => exact (ihx d h).imp_left .appArg
  | lam t b m iht ihb =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    cases h with
    | lamTy h => exact (iht d h).imp_left .lamTy
    | lamBody h => exact (ihb (d + 1) h).imp_left .lamBody
  | forallE t b m iht ihb =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    cases h with
    | allTy h => exact (iht d h).imp_left .allTy
    | allBody h => exact (ihb (d + 1) h).imp_left .allBody
  | letE t x b l iht ihx ihb =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    cases h with
    | letTy h => exact (iht d h).imp_left .letTy
    | letVal h => exact (ihx d h).imp_left .letVal
    | letBody h => exact (ihb (d + 1) h).imp_left .letBody
  | lit l =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    exact Or.inl h
  | proj s i x ih =>
    intro d h
    simp only [Ix.Kernel.Expr.instantiate1] at h
    cases h with
    | proj => exact Or.inl (.proj _ _)
    | projBody h => exact (ih d h).imp_left .projBody

/-- A key of a term with its level parameters instantiated is a key of the term. -/
theorem keyIn_instantiateLevelParams {ks : List Ix.Kernel.LevelParam} {us : List Ix.Kernel.Level} :
    ∀ (e : Ix.Kernel.Expr .anon), KeyIn k (e.instantiateLevelParams ks us) → KeyIn k e := by
  intro e
  induction e with
  | bvar i =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h
  | fvar i ty ih =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | fvarTy h => exact .fvarTy (ih h)
  | sort u =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h
  | const n vs =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | const => exact .const _
  | app f x ihf ihx =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | appFn h => exact .appFn (ihf h)
    | appArg h => exact .appArg (ihx h)
  | lam t b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | lamTy h => exact .lamTy (iht h)
    | lamBody h => exact .lamBody (ihb h)
  | forallE t b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | allTy h => exact .allTy (iht h)
    | allBody h => exact .allBody (ihb h)
  | letE t v b l iht ihv ihb =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | letTy h => exact .letTy (iht h)
    | letVal h => exact .letVal (ihv h)
    | letBody h => exact .letBody (ihb h)
  | lit l =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h
  | proj s i x ih =>
    intro h
    simp only [Ix.Kernel.Expr.instantiateLevelParams] at h
    cases h with
    | proj => exact .proj _ _
    | projBody h => exact .projBody (ih h)

/-- A key of an argument of a spine is a key of the spine. -/
theorem keyIn_of_mem_getAppArgs {x : Ix.Kernel.Expr .anon} :
    ∀ (e : Ix.Kernel.Expr .anon), x ∈ Ix.Kernel.Expr.getAppArgs e → KeyIn k x → KeyIn k e := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hx hk
    simp only [Ix.Kernel.Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact .appFn (ihf hx hk)
    · subst hx
      exact .appArg hk
  | _ =>
    intro hx _
    simp [Ix.Kernel.Expr.getAppArgs] at hx

/-- A key of the body past leading binders is a key of the term. -/
theorem keyIn_of_peelForalls : ∀ (n : Nat) {e b : Ix.Kernel.Expr .anon},
    peelForalls n e = some b → KeyIn k b → KeyIn k e
  | 0, e, b, h, hk => by
    simp only [peelForalls, Option.some.injEq] at h
    subst h
    exact hk
  | n + 1, e, b, h, hk => by
    cases e with
    | forallE t body m =>
      simp only [peelForalls] at h
      exact .allBody (keyIn_of_peelForalls n h hk)
    | _ => simp [peelForalls] at h

/-- A key of a constructor type with parameters instantiated is a key of the type or of a
parameter. -/
theorem keyIn_of_instCtorParams : ∀ (sp : List (Ix.Kernel.Expr .anon)) {ty b : Ix.Kernel.Expr .anon},
    instCtorParams ty sp = some b → KeyIn k b → KeyIn k ty ∨ ∃ s ∈ sp, KeyIn k s
  | [], ty, b, h, hk => by
    simp only [instCtorParams, Option.some.injEq] at h
    subst h
    exact Or.inl hk
  | v :: vs, ty, b, h, hk => by
    cases ty with
    | forallE d body m =>
      simp only [instCtorParams] at h
      rcases keyIn_of_instCtorParams vs h hk with h1 | ⟨s, hs, h2⟩
      · rcases keyIn_instantiate1 v body 0 h1 with h3 | h3
        · exact Or.inl (.allBody h3)
        · exact Or.inr ⟨v, List.mem_cons_self, h3⟩
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, h2⟩
    | _ => simp [instCtorParams] at h

theorem keyIn_of_ctorBody {aux : Bool} {np : Nat} {sp : List (Ix.Kernel.Expr .anon)}
    {ty b : Ix.Kernel.Expr .anon} (h : ctorBody aux np sp ty = some b) (hk : KeyIn k b) :
    KeyIn k ty ∨ ∃ s ∈ sp, KeyIn k s := by
  cases aux with
  | true =>
    simp only [ctorBody] at h
    exact keyIn_of_instCtorParams sp h hk
  | false =>
    simp only [ctorBody] at h
    exact Or.inl (keyIn_of_peelForalls np h hk)

/-- A key of a lowered parameter is a key of an occurrence's parameter. -/
theorem keyIn_of_occParamsLower : ∀ (xs : List (Ix.Kernel.Expr .anon)) (d : Nat)
    {ys : List (Ix.Kernel.Expr .anon)}, occParamsLower xs d = some ys →
    ∀ y ∈ ys, KeyIn k y → ∃ x ∈ xs, KeyIn k x
  | [], d, ys, h, y, hy, hk => by
    simp only [occParamsLower, Option.some.injEq] at h
    subst h
    cases hy
  | x :: xs, d, ys, h, y, hy, hk => by
    simp only [occParamsLower] at h
    split at h
    · cases h
    · cases hr : occParamsLower xs d with
      | none => simp [hr] at h
      | some zs =>
        simp only [hr, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with hy | hy
        · subst hy
          exact ⟨x, List.mem_cons_self, keyIn_lowerBVars d x 0 hk⟩
        · obtain ⟨x', hx', hk'⟩ := keyIn_of_occParamsLower xs d hr y hy hk
          exact ⟨x', List.mem_cons_of_mem _ hx', hk'⟩

end Keys

/-! ## A view that answers as the first on a closed set of addresses -/

/-- **Every key of the term names, through the view, an address of `S`.** -/
abbrev KeysAt (V : FlatView) (S : _root_.Address → Prop) (e : Ix.Kernel.Expr .anon) : Prop :=
  ∀ k, KeyIn k e → ∀ a, V.addr k = some a → S a

/-- **An entry at an address of `S`, whose parameters' keys name addresses of `S`.** -/
structure EntryAt (V : FlatView) (S : _root_.Address → Prop) (e : FlatEntry) : Prop where
  addr : S e.addr
  params : ∀ p ∈ e.params, KeysAt V S p

/-- **`V'` answers as `V` at the addresses of `S`** (and names the same addresses by keys). -/
structure FlatView.LeOn (S : _root_.Address → Prop) (V V' : FlatView) : Prop where
  ci : ∀ a x, S a → V.ci a = some x → V'.ci a = some x
  ctorType : ∀ b i c x, S b → V.ctorType b i c = some x → V'.ctorType b i c = some x
  members : ∀ b x, S b → V.members b = some x → V'.members b = some x
  addr : ∀ k x, V.addr k = some x → V'.addr k = some x

/-- **What `V` answers at the addresses of `S` stays in `S`**: an inductive type's block, a
block's members, and the addresses the keys of a constructor type name. -/
structure FlatView.ClosedOn (S : _root_.Address → Prop) (V : FlatView) : Prop where
  ciBlk : ∀ a i, S a → V.ci a = some (some i) → S i.blk
  members : ∀ b ms, S b → V.members b = some ms → ∀ a ∈ ms, S a
  ctorType : ∀ b i c ty, S b → V.ctorType b i c = some ty → KeysAt V S ty

section LeOn

variable {S : _root_.Address → Prop} {V V' : FlatView}

theorem peer_leOn (hV : V.LeOn S V') (B : _root_.Address) {k : Ix.Kernel.Key .anon}
    (hk : ∀ a, V.addr k = some a → S a) {r : Bool} (h : peer V B k = some r) :
    peer V' B k = some r := by
  unfold peer at h ⊢
  cases ha : V.addr k with
  | none => simp [ha] at h
  | some a =>
    simp only [ha, hV.addr k a ha] at h ⊢
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      simp only [hc, hV.ci a x (hk a ha) hc] at h ⊢
      exact h

theorem mentions_leOn (hV : V.LeOn S V') (B : _root_.Address) :
    ∀ (e : Ix.Kernel.Expr .anon) (r : Bool), KeysAt V S e → mentions V B e = some r →
      mentions V' B e = some r := by
  intro e
  induction e with
  | bvar _ => intro r _ h; simp only [mentions] at h ⊢; exact h
  | fvar _ _ _ => intro r _ h; simp only [mentions] at h ⊢; exact h
  | sort _ => intro r _ h; simp only [mentions] at h ⊢; exact h
  | const k _ =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact peer_leOn hV B (hK k (.const _)) h
  | app f a ihf iha =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact orB_le (fun r' => ihf r' (fun k hk => hK k (.appFn hk)))
      (fun r' => iha r' (fun k hk => hK k (.appArg hk))) h
  | lam t b _ iht ihb =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact orB_le (fun r' => iht r' (fun k hk => hK k (.lamTy hk)))
      (fun r' => ihb r' (fun k hk => hK k (.lamBody hk))) h
  | forallE t b _ iht ihb =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact orB_le (fun r' => iht r' (fun k hk => hK k (.allTy hk)))
      (fun r' => ihb r' (fun k hk => hK k (.allBody hk))) h
  | letE t v b _ iht ihv ihb =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact orB_le (fun r' => iht r' (fun k hk => hK k (.letTy hk)))
      (fun r' h' => orB_le (fun r'' => ihv r'' (fun k hk => hK k (.letVal hk)))
        (fun r'' => ihb r'' (fun k hk => hK k (.letBody hk))) h') h
  | lit _ => intro r _ h; simp only [mentions] at h ⊢; exact h
  | proj _ _ e ih =>
    intro r hK h
    simp only [mentions] at h ⊢
    exact ih r (fun k hk => hK k (.projBody hk)) h

theorem mentionsList_leOn (hV : V.LeOn S V') (B : _root_.Address) :
    ∀ (es : List (Ix.Kernel.Expr .anon)) (r : Bool), (∀ e ∈ es, KeysAt V S e) →
      mentionsList V B es = some r → mentionsList V' B es = some r := by
  intro es
  induction es with
  | nil => intro r _ h; exact h
  | cons e es ih =>
    intro r hK h
    simp only [mentionsList] at h ⊢
    exact orB_le (fun r' => mentions_leOn hV B e r' (hK e List.mem_cons_self))
      (fun r' => ih r' (fun x hx => hK x (List.mem_cons_of_mem _ hx))) h

theorem nestedAt_leOn (hV : V.LeOn S V') (B : _root_.Address) (i : IndInfo)
    (args : List (Ix.Kernel.Expr .anon)) (hargs : ∀ x ∈ args, KeysAt V S x) {r : Bool}
    (h : nestedAt V B i args = some r) : nestedAt V' B i args = some r := by
  unfold nestedAt at h ⊢
  cases hb : (i.blk == B || decide (args.length < i.np)) with
  | true =>
    simp only [hb] at h ⊢
    exact h
  | false =>
    simp only [hb] at h ⊢
    exact mentionsList_leOn hV B _ r (fun x hx => hargs x (List.mem_of_mem_take hx)) h

theorem scanList_leOn
    {rec rec' : Ix.Kernel.Expr .anon → List FlatEntry → Option (List FlatEntry)}
    {G : Ix.Kernel.Expr .anon → Prop} {I : List FlatEntry → Prop}
    (hr : ∀ x acc r, G x → I acc → rec x acc = some r → rec' x acc = some r ∧ I r) :
    ∀ (l : List (Ix.Kernel.Expr .anon)) (acc r : List FlatEntry), (∀ x ∈ l, G x) → I acc →
      scanList rec l acc = some r → scanList rec' l acc = some r ∧ I r := by
  intro l
  induction l with
  | nil =>
    intro acc r _ hI h
    simp only [scanList, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hI⟩
  | cons x xs ih =>
    intro acc r hG hI h
    simp only [scanList] at h ⊢
    cases hx : rec x acc with
    | none => simp [hx] at h
    | some a =>
      obtain ⟨hx', hIa⟩ := hr x acc a (hG x List.mem_cons_self) hI hx
      simp only [hx, hx'] at h ⊢
      exact ih a r (fun y hy => hG y (List.mem_cons_of_mem _ hy)) hIa h

theorem eq_of_constOf {hd : Ix.Kernel.Expr .anon} {c : Ix.Kernel.Key .anon}
    {us : List Ix.Kernel.Level} (h : constOf hd = some (c, us)) : hd = .const c us := by
  cases hd with
  | const c' us' =>
    simp only [constOf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | _ => simp [constOf] at h

theorem addBlockMembers_entryAt {sp : List (Ix.Kernel.Expr .anon)} {us : List Ix.Kernel.Level}
    (hsp : ∀ p ∈ sp, KeysAt V S p) :
    ∀ (ms : List _root_.Address) (acc : List FlatEntry), (∀ m ∈ ms, S m) →
      (∀ x ∈ acc, EntryAt V S x) → ∀ x ∈ addBlockMembers ms sp us acc, EntryAt V S x := by
  intro ms
  induction ms with
  | nil =>
    intro acc _ hacc
    simp only [addBlockMembers]
    exact hacc
  | cons m ms ih =>
    intro acc hms hacc
    simp only [addBlockMembers]
    apply ih _ (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))
    by_cases hin : auxEntryIn acc m sp us = true
    · rw [ite_eq_left hin]
      exact hacc
    · rw [ite_eq_right hin]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hacc x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hms m List.mem_cons_self, hsp⟩

theorem appCase_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (B : _root_.Address)
    {rec rec' : Ix.Kernel.Expr .anon → Nat → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ e d acc r, KeysAt V S e → (∀ x ∈ acc, EntryAt V S x) → rec e d acc = some r →
      rec' e d acc = some r ∧ ∀ x ∈ r, EntryAt V S x)
    {hd : Ix.Kernel.Expr .anon} {args : List (Ix.Kernel.Expr .anon)} {d : Nat}
    {acc r : List FlatEntry} (hhd : KeysAt V S hd) (hargs : ∀ x ∈ args, KeysAt V S x)
    (hacc : ∀ x ∈ acc, EntryAt V S x) (h : appCase rec V B hd args d acc = some r) :
    appCase rec' V' B hd args d acc = some r ∧ ∀ x ∈ r, EntryAt V S x := by
  have hs : ∀ acc r, (∀ x ∈ acc, EntryAt V S x) →
      scanList (fun x acc => rec x d acc) args acc = some r →
      scanList (fun x acc => rec' x d acc) args acc = some r ∧ ∀ x ∈ r, EntryAt V S x :=
    fun acc r hI hsc => scanList_leOn (rec := fun x acc => rec x d acc)
      (rec' := fun x acc => rec' x d acc) (G := KeysAt V S)
      (I := fun acc => ∀ x ∈ acc, EntryAt V S x)
      (fun x acc r hG hI h => hr x d acc r hG hI h) args acc r hargs hI hsc
  unfold appCase at h ⊢
  cases hk : constOf hd with
  | none =>
    simp only [hk] at h ⊢
    cases h1 : rec hd d acc with
    | none => simp [h1] at h
    | some a =>
      obtain ⟨h1', hIa⟩ := hr hd d acc a hhd hacc h1
      simp only [h1, h1'] at h ⊢
      exact hs a r hIa h
  | some p =>
    obtain ⟨c, us⟩ := p
    have hdc : hd = .const c us := eq_of_constOf hk
    simp only [hk] at h ⊢
    cases ha : V.addr c with
    | none => simp [ha] at h
    | some ca =>
      have hSca : S ca := hhd c (by rw [hdc]; exact .const us) ca ha
      simp only [ha, hV.addr c ca ha] at h ⊢
      cases hc : V.ci ca with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none =>
          simp only [hc, hV.ci ca none hSca hc] at h ⊢
          exact hs acc r hacc h
        | some i =>
          simp only [hc, hV.ci ca (some i) hSca hc] at h ⊢
          cases hn : nestedAt V B i args with
          | none => simp [hn] at h
          | some b =>
            have hn' := nestedAt_leOn hV B i args hargs hn
            cases b with
            | false =>
              simp only [hn, hn'] at h ⊢
              exact hs acc r hacc h
            | true =>
              simp only [hn, hn'] at h ⊢
              have hSblk : S i.blk := hC.ciBlk ca i hSca hc
              cases hm : V.members i.blk with
              | none => simp [hm] at h
              | some ms =>
                simp only [hm, hV.members i.blk ms hSblk hm] at h ⊢
                cases ho : occParamsLower (args.take i.np) d with
                | none => simp [ho] at h
                | some sp =>
                  simp only [ho, Option.some.injEq] at h ⊢
                  subst h
                  refine ⟨rfl, ?_⟩
                  have hsp : ∀ p ∈ sp, KeysAt V S p := by
                    intro p hp k hk a hka
                    obtain ⟨x, hx, hkx⟩ := keyIn_of_occParamsLower _ d ho p hp hk
                    exact hargs x (List.mem_of_mem_take hx) k hkx a hka
                  exact addBlockMembers_entryAt hsp ms acc (hC.members i.blk ms hSblk hm) hacc

theorem occScanF_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (B : _root_.Address) :
    ∀ (n : Nat) (e : Ix.Kernel.Expr .anon) (d : Nat) (acc r : List FlatEntry),
      KeysAt V S e → (∀ x ∈ acc, EntryAt V S x) → occScanF V B n e d acc = some r →
      occScanF V' B n e d acc = some r ∧ ∀ x ∈ r, EntryAt V S x := by
  intro n
  induction n with
  | zero => intro e d acc r _ _ h; simp [occScanF] at h
  | succ n ih =>
    intro e d acc r hK hacc h
    simp only [occScanF] at h ⊢
    cases hm : mentions V B e with
    | none => simp [hm] at h
    | some b =>
      have hm' := mentions_leOn hV B e b hK hm
      cases b with
      | false =>
        simp only [hm, hm', Option.some.injEq] at h ⊢
        subst h
        exact ⟨rfl, hacc⟩
      | true =>
        simp only [hm, hm'] at h ⊢
        cases e with
        | app f a =>
          simp only at h ⊢
          exact appCase_leOn (rec := occScanF V B n) (rec' := occScanF V' B n) hV hC B ih
            (fun k hk => hK k (keyIn_getAppFn hk))
            (fun x hx k hk => hK k (keyIn_of_mem_getAppArgs _ hx hk)) hacc h
        | lam t b m =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            obtain ⟨h1', hI1⟩ := ih t d acc a1 (fun k hk => hK k (.lamTy hk)) hacc h1
            simp only [h1, h1'] at h ⊢
            exact ih b (d + 1) a1 r (fun k hk => hK k (.lamBody hk)) hI1 h
        | forallE t b m =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            obtain ⟨h1', hI1⟩ := ih t d acc a1 (fun k hk => hK k (.allTy hk)) hacc h1
            simp only [h1, h1'] at h ⊢
            exact ih b (d + 1) a1 r (fun k hk => hK k (.allBody hk)) hI1 h
        | letE t v b l =>
          simp only at h ⊢
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            obtain ⟨h1', hI1⟩ := ih t d acc a1 (fun k hk => hK k (.letTy hk)) hacc h1
            simp only [h1, h1'] at h ⊢
            cases h2 : occScanF V B n v d a1 with
            | none => simp [h2] at h
            | some a2 =>
              obtain ⟨h2', hI2⟩ := ih v d a1 a2 (fun k hk => hK k (.letVal hk)) hI1 h2
              simp only [h2, h2'] at h ⊢
              exact ih b (d + 1) a2 r (fun k hk => hK k (.letBody hk)) hI2 h
        | proj s i x =>
          simp only at h ⊢
          exact ih x d acc r (fun k hk => hK k (.projBody hk)) hacc h
        | bvar _ =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, hacc⟩
        | fvar _ _ =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, hacc⟩
        | sort _ =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, hacc⟩
        | const _ _ =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, hacc⟩
        | lit _ =>
          simp only [Option.some.injEq] at h ⊢
          subst h
          exact ⟨rfl, hacc⟩

theorem ctorScan_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (B : _root_.Address)
    (i : IndInfo) (aux : Bool) (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level)
    (hblk : S i.blk) (hsp : ∀ p ∈ sp, KeysAt V S p) {acc r : List FlatEntry} {c : Nat}
    (hacc : ∀ x ∈ acc, EntryAt V S x) (h : ctorScan V B i aux sp us acc c = some r) :
    ctorScan V' B i aux sp us acc c = some r ∧ ∀ x ∈ r, EntryAt V S x := by
  unfold ctorScan at h ⊢
  cases hc : V.ctorType i.blk i.idx c with
  | none => simp [hc] at h
  | some cty =>
    simp only [hc, hV.ctorType i.blk i.idx c cty hblk hc] at h ⊢
    cases hb : ctorBody aux i.np sp (cty.instantiateLevelParams (List.range us.length) us) with
    | none => simp [hb] at h
    | some body =>
      simp only [hb] at h ⊢
      have hKb : KeysAt V S body := by
        intro k hk a ha
        rcases keyIn_of_ctorBody hb hk with h1 | ⟨s, hs, h2⟩
        · exact hC.ctorType i.blk i.idx c cty hblk hc k (keyIn_instantiateLevelParams _ h1) a ha
        · exact hsp s hs k h2 a ha
      exact occScanF_leOn hV hC B _ body 0 acc r hKb hacc h

theorem ctorsLoop_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (B : _root_.Address)
    (i : IndInfo) (aux : Bool) (sp : List (Ix.Kernel.Expr .anon)) (us : List Ix.Kernel.Level)
    (hblk : S i.blk) (hsp : ∀ p ∈ sp, KeysAt V S p) :
    ∀ (cs : List Nat) (acc r : List FlatEntry), (∀ x ∈ acc, EntryAt V S x) →
      ctorsLoop V B i aux sp us cs acc = some r →
      ctorsLoop V' B i aux sp us cs acc = some r ∧ ∀ x ∈ r, EntryAt V S x := by
  intro cs
  induction cs with
  | nil =>
    intro acc r hacc h
    simp only [ctorsLoop, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hacc⟩
  | cons c cs ih =>
    intro acc r hacc h
    simp only [ctorsLoop] at h ⊢
    cases h1 : ctorScan V B i aux sp us acc c with
    | none => simp [h1] at h
    | some a =>
      obtain ⟨h1', hIa⟩ := ctorScan_leOn hV hC B i aux sp us hblk hsp hacc h1
      simp only [h1, h1'] at h ⊢
      exact ih a r hIa h

theorem nestedWalk_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) (B : _root_.Address) :
    ∀ (n i : Nat) (acc r : List FlatEntry), (∀ x ∈ acc, EntryAt V S x) →
      nestedWalk V B n i acc = some r → nestedWalk V' B n i acc = some r := by
  intro n
  induction n with
  | zero => intro i acc r _ h; simp [nestedWalk] at h
  | succ n ih =>
    intro i acc r hacc h
    simp only [nestedWalk] at h ⊢
    cases hi : acc[i]? with
    | none =>
      simp only [hi] at h ⊢
      exact h
    | some e =>
      simp only [hi] at h ⊢
      have he : EntryAt V S e := hacc e (List.mem_of_getElem? hi)
      cases hc : V.ci e.addr with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none => simp [hc] at h
        | some info =>
          simp only [hc, hV.ci e.addr (some info) he.addr hc] at h ⊢
          cases hs : ctorsScan V B info e.aux e.params e.levels acc with
          | none => simp [hs] at h
          | some a =>
            have hl := ctorsLoop_leOn hV hC B info e.aux e.params e.levels
              (hC.ciBlk e.addr info he.addr hc) he.params (List.range info.nctors) acc a hacc hs
            have hs' : ctorsScan V' B info e.aux e.params e.levels acc = some a := hl.1
            simp only [hs, hs'] at h ⊢
            exact ih (i + 1) a r hl.2 h

theorem originals_leOn (hV : V.LeOn S V') (off : Nat) :
    ∀ (as : List _root_.Address) (es : List FlatEntry), (∀ a ∈ as, S a) →
      originals V off as = some es → originals V' off as = some es ∧ ∀ x ∈ es, EntryAt V S x := by
  intro as
  induction as with
  | nil =>
    intro es _ h
    simp only [originals, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun x hx => by simp at hx⟩
  | cons a as ih =>
    intro es hS h
    simp only [originals] at h ⊢
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none => simp [hc] at h
      | some i =>
        simp only [hc, hV.ci a (some i) (hS a List.mem_cons_self) hc] at h ⊢
        cases ho : originals V off as with
        | none => simp [ho] at h
        | some os =>
          obtain ⟨ho', hI⟩ := ih os (fun b hb => hS b (List.mem_cons_of_mem _ hb)) ho
          simp only [ho, ho', Option.some.injEq] at h ⊢
          subst h
          refine ⟨rfl, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst hx
            exact ⟨hS a List.mem_cons_self, fun p hp => by simp at hp⟩
          · exact hI x hx

/-- **A view that answers as the first on a closed set holding the block derives the same
entries.** -/
theorem derivedFlatAt_leOn (hV : V.LeOn S V') (hC : V.ClosedOn S) {B : _root_.Address}
    (hB : S B) {off n : Nat} {es : List FlatEntry} (h : derivedFlatAt V B off n = some es) :
    derivedFlatAt V' B off n = some es := by
  unfold derivedFlatAt at h ⊢
  cases hm : V.members B with
  | none => simp [hm] at h
  | some ms =>
    simp only [hm, hV.members B ms hB hm] at h ⊢
    cases ho : originals V off ms with
    | none => simp [ho] at h
    | some os =>
      obtain ⟨ho', hI⟩ := originals_leOn hV off ms os (hC.members B ms hB hm) ho
      simp only [ho, ho'] at h ⊢
      exact nestedWalk_leOn hV hC B n 0 os es hI h

end LeOn

/-! ## The readings of a store -/

section Store

theorem except_toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x with
  | error e => simp [Except.toOption]
  | ok b =>
    constructor
    · intro h
      have hb : some b = some a := h
      exact congrArg Except.ok (Option.some.inj hb)
    · intro h
      cases h
      rfl

theorem indInfoAt_inv {E : Ixon.Env} {a : _root_.Address} {i : IndInfo}
    (h : indInfoAt E a = some (some i)) :
    ∃ c p cb ms ind, recordOf E a = some c ∧ c.info = .iPrj p ∧ recordOf E p.block = some cb ∧
      cb.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      i = ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, p.block, p.idx.toNat⟩ := by
  unfold indInfoAt at h
  obtain ⟨c, hc⟩ : ∃ c, recordOf E a = some c := by
    cases hc : recordOf E a with
    | none => simp [hc] at h
    | some c => exact ⟨c, rfl⟩
  simp only [hc] at h
  obtain ⟨p, hci⟩ : ∃ p, c.info = .iPrj p := by
    cases hci : c.info with
    | iPrj p => exact ⟨p, rfl⟩
    | _ => simp [hci] at h
  simp only [hci] at h
  obtain ⟨cb, hcb⟩ : ∃ cb, recordOf E p.block = some cb := by
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb => exact ⟨cb, rfl⟩
  simp only [hcb] at h
  obtain ⟨ms, hcbi⟩ : ∃ ms, cb.info = .muts ms := by
    cases hcbi : cb.info with
    | muts ms => exact ⟨ms, rfl⟩
    | _ => simp [hcbi] at h
  simp only [hcbi] at h
  obtain ⟨ind, hm⟩ : ∃ ind, ms[p.idx.toNat]? = some (.indc ind) := by
    cases hm : ms[p.idx.toNat]? with
    | none => simp [hm] at h
    | some m =>
      cases m with
      | indc ind => exact ⟨ind, rfl⟩
      | defn _ => simp [hm] at h
      | recr _ => simp [hm] at h
  simp only [hm, Option.some.injEq] at h
  exact ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, h.symm⟩

theorem indInfoAt_none_inv {E : Ixon.Env} {a : _root_.Address}
    (h : indInfoAt E a = some none) : ∃ c, recordOf E a = some c ∧ ∀ p, c.info ≠ .iPrj p := by
  unfold indInfoAt at h
  obtain ⟨c, hc⟩ : ∃ c, recordOf E a = some c := by
    cases hc : recordOf E a with
    | none => simp [hc] at h
    | some c => exact ⟨c, rfl⟩
  refine ⟨c, hc, fun p hp => ?_⟩
  simp only [hc, hp] at h
  obtain ⟨cb, hcb⟩ : ∃ cb, recordOf E p.block = some cb := by
    cases hcb : recordOf E p.block with
    | none => simp [hcb] at h
    | some cb => exact ⟨cb, rfl⟩
  simp only [hcb] at h
  obtain ⟨ms, hcbi⟩ : ∃ ms, cb.info = .muts ms := by
    cases hcbi : cb.info with
    | muts ms => exact ⟨ms, rfl⟩
    | _ => simp [hcbi] at h
  simp only [hcbi] at h
  cases hm : ms[p.idx.toNat]? with
  | none => simp [hm] at h
  | some m =>
    cases m with
    | indc ind => simp [hm] at h
    | defn _ => simp [hm] at h
    | recr _ => simp [hm] at h

theorem indInfoAt_of_iPrj {E : Ixon.Env} {a : _root_.Address} {c cb : Ixon.Constant}
    {p : Ixon.InductiveProj} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hc : recordOf E a = some c) (hci : c.info = .iPrj p) (hcb : recordOf E p.block = some cb)
    (hcbi : cb.info = .muts ms) (hm : ms[p.idx.toNat]? = some (.indc ind)) :
    indInfoAt E a =
      some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, p.block, p.idx.toNat⟩) := by
  unfold indInfoAt
  simp only [hc, hci, hcb, hcbi, hm]

theorem indInfoAt_of_not_iPrj {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E a = some c) (hn : ∀ p, c.info ≠ .iPrj p) : indInfoAt E a = some none := by
  cases hci : c.info with
  | iPrj p => exact absurd hci (hn p)
  | _ => simp only [indInfoAt, hc, hci]

theorem ctorTypeAt_inv {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    {i c : Nat} {x : Ix.Kernel.Expr .anon} (h : ctorTypeAt t E b i c = some x) :
    ∃ cb ms ind ctor, recordOf E b = some cb ∧ cb.info = .muts ms ∧
      ms[i]? = some (.indc ind) ∧ ind.ctors[c]? = some ctor ∧
      (exprReader t (fun y => E.blobs.get? y) cb id (blockSelf t b ms)).read ctor.typ = .ok x := by
  unfold ctorTypeAt at h
  obtain ⟨cb, hcb⟩ : ∃ cb, recordOf E b = some cb := by
    cases hcb : recordOf E b with
    | none => simp [hcb] at h
    | some cb => exact ⟨cb, rfl⟩
  simp only [hcb] at h
  obtain ⟨ms, hci⟩ : ∃ ms, cb.info = .muts ms := by
    cases hci : cb.info with
    | muts ms => exact ⟨ms, rfl⟩
    | _ => simp [hci] at h
  simp only [hci] at h
  obtain ⟨ind, hm⟩ : ∃ ind, ms[i]? = some (.indc ind) := by
    cases hm : ms[i]? with
    | none => simp [hm] at h
    | some m =>
      cases m with
      | indc ind => exact ⟨ind, rfl⟩
      | defn _ => simp [hm] at h
      | recr _ => simp [hm] at h
  simp only [hm] at h
  obtain ⟨ctor, hct⟩ : ∃ ctor, ind.ctors[c]? = some ctor := by
    cases hct : ind.ctors[c]? with
    | none => simp [hct] at h
    | some ctor => exact ⟨ctor, rfl⟩
  simp only [hct] at h
  exact ⟨cb, ms, ind, ctor, hcb, hci, hm, hct, except_toOption_eq_some.mp h⟩

theorem ctorTypeAt_of {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    {i c : Nat} {x : Ix.Kernel.Expr .anon} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {ctor : Ixon.Constructor} (hcb : recordOf E b = some cb)
    (hci : cb.info = .muts ms) (hm : ms[i]? = some (.indc ind)) (hct : ind.ctors[c]? = some ctor)
    (hr : (exprReader t (fun y => E.blobs.get? y) cb id (blockSelf t b ms)).read ctor.typ =
      .ok x) :
    ctorTypeAt t E b i c = some x := by
  unfold ctorTypeAt
  simp only [hcb, hci, hm, hct]
  exact except_toOption_eq_some.mpr hr

theorem membersAt_inv {E : Ixon.Env} {b : _root_.Address} {ms : List _root_.Address}
    (h : membersAt E b = some ms) :
    ∃ cb arr, recordOf E b = some cb ∧ cb.info = .muts arr ∧ ms = indcAddrs b 0 arr.toList := by
  unfold membersAt at h
  obtain ⟨cb, hcb⟩ : ∃ cb, recordOf E b = some cb := by
    cases hcb : recordOf E b with
    | none => simp [hcb] at h
    | some cb => exact ⟨cb, rfl⟩
  simp only [hcb] at h
  obtain ⟨arr, hci⟩ : ∃ arr, cb.info = .muts arr := by
    cases hci : cb.info with
    | muts arr => exact ⟨arr, rfl⟩
    | _ => simp [hci] at h
  simp only [hci, Option.some.injEq] at h
  exact ⟨cb, arr, hcb, hci, h.symm⟩

theorem membersAt_of {E : Ixon.Env} {b : _root_.Address} {cb : Ixon.Constant}
    {arr : Array Ixon.MutConst} (hcb : recordOf E b = some cb) (hci : cb.info = .muts arr) :
    membersAt E b = some (indcAddrs b 0 arr.toList) := by
  unfold membersAt
  simp only [hcb, hci]

/-- An address `indcAddrs` lists is the constant address of a member. -/
theorem mem_indcAddrs {b a : _root_.Address} :
    ∀ (l : List Ixon.MutConst) (j : Nat), a ∈ indcAddrs b j l →
      ∃ i m, l[i]? = some m ∧ a = memberAddr b (j + i) m
  | [], _, h => by simp [indcAddrs] at h
  | m :: ms, j, h => by
    cases m with
    | indc ind =>
      simp only [indcAddrs, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨0, .indc ind, rfl, by rw [h, Nat.add_zero]⟩
      · obtain ⟨i, m', hm, ha⟩ := mem_indcAddrs ms (j + 1) h
        refine ⟨i + 1, m', by simpa using hm, ?_⟩
        rw [ha, show j + 1 + i = j + (i + 1) by omega]
    | defn d =>
      simp only [indcAddrs] at h
      obtain ⟨i, m', hm, ha⟩ := mem_indcAddrs ms (j + 1) h
      refine ⟨i + 1, m', by simpa using hm, ?_⟩
      rw [ha, show j + 1 + i = j + (i + 1) by omega]
    | recr r =>
      simp only [indcAddrs] at h
      obtain ⟨i, m', hm, ha⟩ := mem_indcAddrs ms (j + 1) h
      refine ⟨i + 1, m', by simpa using hm, ?_⟩
      rw [ha, show j + 1 + i = j + (i + 1) by omega]

/-- **The role table's keys name their addresses.** -/
theorem keyAddr_keyOf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) (y : _root_.Address) :
    keyAddr t (keyOf t y) = some y := by
  rcases keyOf_cases t y with ⟨h, -⟩ | ⟨r, -, h⟩
  · simp only [h, keyAddr]
  · simp only [h, keyAddr]
    exact IxVM.Refinement.Core.addressOf_of_keyOf (a := y) (r := r) hwf h

/-- The addresses at which the store holds a record. -/
abbrev Held (R : Ixon.Env) (a : _root_.Address) : Prop := (recordOf R a).isSome = true

theorem recordOf_eq_of_held {R E₀ : Ixon.Env}
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) {y : _root_.Address}
    (hy : Held R y) : recordOf R y = recordOf E₀ y := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hy
  rw [hc, hsub y c hc]

/-- **A store that holds the records and blobs of `E` answers whatever `E` answers.** -/
theorem ofStore_le {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b) :
    (FlatView.ofStore t E).Le (FlatView.ofStore t E') where
  ci a x h := by
    show indInfoAt E' a = some x
    have h' : indInfoAt E a = some x := h
    cases x with
    | none =>
      obtain ⟨c, hc, hn⟩ := indInfoAt_none_inv h'
      exact indInfoAt_of_not_iPrj (hle a c hc) hn
    | some i =>
      obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, rfl⟩ := indInfoAt_inv h'
      exact indInfoAt_of_iPrj (hle a c hc) hci (hle _ cb hcb) hcbi hm
  ctorType b i c x h := by
    show ctorTypeAt t E' b i c = some x
    obtain ⟨cb, ms, ind, ctor, hcb, hci, hm, hct, hr⟩ :=
      ctorTypeAt_inv (h : ctorTypeAt t E b i c = some x)
    exact ctorTypeAt_of (hle b cb hcb) hci hm hct (exprReader_mono hblob hr)
  members b x h := by
    show membersAt E' b = some x
    obtain ⟨cb, arr, hcb, hci, rfl⟩ := membersAt_inv (h : membersAt E b = some x)
    exact membersAt_of (hle b cb hcb) hci
  addr k x h := h

/-- **A sub-store of `E₀` closed under used references and owners, holding `E₀`'s blobs, answers
as `E₀` at the addresses it holds.** -/
theorem ofStore_leOn_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b) :
    (FlatView.ofStore t E₀).LeOn (Held R) (FlatView.ofStore t R) where
  ci a x ha h := by
    show indInfoAt R a = some x
    have h' : indInfoAt E₀ a = some x := h
    cases x with
    | none =>
      obtain ⟨c, hc, hn⟩ := indInfoAt_none_inv h'
      exact indInfoAt_of_not_iPrj ((recordOf_eq_of_held hsub ha).trans hc) hn
    | some i =>
      obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, rfl⟩ := indInfoAt_inv h'
      have hcR : recordOf R a = some c := (recordOf_eq_of_held hsub ha).trans hc
      have hown : Ix.Cert.ownerOf a c = p.block := by simp only [Ix.Cert.ownerOf, hci]
      have hheld : Held R p.block := by
        have h1 := (hcl.1 a c hcR).1
        rw [hown] at h1
        exact h1
      exact indInfoAt_of_iPrj hcR hci ((recordOf_eq_of_held hsub hheld).trans hcb) hcbi hm
  ctorType b i c x hb h := by
    show ctorTypeAt t R b i c = some x
    obtain ⟨cb, ms, ind, ctor, hcb, hci, hm, hct, hr⟩ :=
      ctorTypeAt_inv (h : ctorTypeAt t E₀ b i c = some x)
    exact ctorTypeAt_of ((recordOf_eq_of_held hsub hb).trans hcb) hci hm hct
      (exprReader_mono hblob hr)
  members b x hb h := by
    show membersAt R b = some x
    obtain ⟨cb, arr, hcb, hci, rfl⟩ := membersAt_inv (h : membersAt E₀ b = some x)
    exact membersAt_of ((recordOf_eq_of_held hsub hb).trans hcb) hci
  addr k x h := h

/-- **What `E₀` answers at the addresses a used-closed sub-store holds stays among them**: an
inductive projection's block is its owner, a block's members are held with it, and a
constructor type's keys are those of references its block uses or of the block's members
(`read_keys`), each naming its address (`keyAddr_keyOf`). -/
theorem ofStore_closedOn_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R) :
    (FlatView.ofStore t E₀).ClosedOn (Held R) where
  ciBlk a i ha h := by
    obtain ⟨c, p, cb, ms, ind, hc, hci, hcb, hcbi, hm, rfl⟩ :=
      indInfoAt_inv (h : indInfoAt E₀ a = some (some i))
    have hcR : recordOf R a = some c := (recordOf_eq_of_held hsub ha).trans hc
    have hown : Ix.Cert.ownerOf a c = p.block := by simp only [Ix.Cert.ownerOf, hci]
    have h1 := (hcl.1 a c hcR).1
    rw [hown] at h1
    exact h1
  members b ms hb h := by
    obtain ⟨cb, arr, hcb, hci, rfl⟩ := membersAt_inv (h : membersAt E₀ b = some ms)
    have hcbR : recordOf R b = some cb := (recordOf_eq_of_held hsub hb).trans hcb
    intro a ha
    obtain ⟨i, m, hm, rfl⟩ := mem_indcAddrs arr.toList 0 ha
    have hm' : arr[i]? = some m := by simpa only [Array.getElem?_toList] using hm
    rw [Nat.zero_add]
    exact Option.isSome_iff_exists.mpr ⟨_, (hcl.2 b cb arr hcbR hci i m hm').1⟩
  ctorType b i c ty hb h := by
    obtain ⟨cb, ms, ind, ctor, hcb, hci, hm, hct, hr⟩ :=
      ctorTypeAt_inv (h : ctorTypeAt t E₀ b i c = some ty)
    have hcbR : recordOf R b = some cb := (recordOf_eq_of_held hsub hb).trans hcb
    have hself : ∀ (j : Nat) (k : Ix.Kernel.Key .anon),
        blockSelf t b ms j = some (Except.ok k) → ∃ z, Held R z ∧ k = keyOf t z := by
      intro j k hs
      unfold blockSelf at hs
      cases hmj : ms[j]? with
      | none =>
        rw [hmj] at hs
        cases hs
      | some mj =>
        rw [hmj] at hs
        cases Except.ok.inj (Option.some.inj hs)
        exact ⟨_, Option.isSome_iff_exists.mpr ⟨_, (hcl.2 b cb ms hcbR hci j mj hmj).1⟩, rfl⟩
    have he : ∀ j ∈ exprRefIdxs ctor.typ, j ∈ usedRefIdxs cb := by
      intro j hj
      have hmem : Ixon.MutConst.indc ind ∈ ms.toList :=
        List.mem_of_getElem? (show ms.toList[i]? = some (.indc ind) by
          rw [Array.getElem?_toList]; exact hm)
      have hcmem : ctor ∈ ind.ctors.toList :=
        List.mem_of_getElem? (show ind.ctors.toList[c]? = some ctor by
          rw [Array.getElem?_toList]; exact hct)
      have hmut : j ∈ mutRefIdxs (.indc ind) := by
        show j ∈ exprRefIdxs ind.typ ++ ind.ctors.toList.flatMap (fun c => exprRefIdxs c.typ)
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ctor, hcmem, hj⟩)
      simp only [usedRefIdxs, hci]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind, hmem, hmut⟩)
    intro k hk a ha
    obtain ⟨z, hz, rfl⟩ := read_keys checked (P := fun k => ∃ z, Held R z ∧ k = keyOf t z)
      (fun j hj y hy => ⟨y, (hcl.1 b cb hcbR).2 j hj y hy, rfl⟩) hself he hr k hk
    have e : a = z := Option.some.inj (ha.symm.trans (keyAddr_keyOf hwf z))
    rw [e]
    exact hz

/-- **The flattened family derived over a used-closed sub-store of `E₀` that holds the block and
`E₀`'s blobs is the one derived over `E₀`.** -/
theorem blockDerivedFlat_of_closed_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    {B : _root_.Address} (hB : (recordOf R B).isSome = true) {off : Nat} {es : List FlatEntry}
    (h : BlockDerivedFlat t E₀ B off es) : BlockDerivedFlat t R B off es := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, derivedFlatAt_leOn (ofStore_leOn_sub hsub hcl hblob)
    (ofStore_closedOn_sub checked hwf hsub hcl) hB hn⟩

/-- **The flattened family derived over a store is the one derived over a store that holds its
records and blobs.** -/
theorem blockDerivedFlat_grow {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {B : _root_.Address} {off : Nat} {es : List FlatEntry}
    (h : BlockDerivedFlat t E B off es) : BlockDerivedFlat t E' B off es := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, derivedFlatAt_le (ofStore_le hle hblob) hn⟩

/-- **The record's entries read the same over a store that holds the first's blobs**: the reading
is over the record's own tables and the blobs. -/
theorem RecordFlat.of_blobs {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} (h : RecordFlat t E rb crb rs es) : RecordFlat t E' rb crb rs es := by
  intro k r e hr he
  obtain ⟨ty, d, h1, h2, h3, h4⟩ := h k r e hr he
  exact ⟨ty, d, exprReader_mono hblob h1, h2, h3, h4⟩

end Store

end IxVM.Refinement.Binding.FamilyFlat

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)

/-- **The family of a block over a store closed under block members that holds the block and its
family record**: the readers read the two records only. -/
theorem familyOfBlock_of_closed {E S : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst} {flat : List _root_.Address}
    (hS : UsedClosed S) (hB : recordOf S B = some cb) (hrb : recordOf S rb = some crb)
    (h : FamilyOfBlock E B cb ms rb crb rs flat) : FamilyOfBlock S B cb ms rb crb rs flat where
  block := {
    record := hB
    muts := h.block.muts
    indcs := h.block.indcs
    logic := h.block.logic
    members := fun i m hm => (hS.2 B cb ms hB h.block.muts i m hm).1
    ctors := fun i ind j hm hj => (hS.2 B cb ms hB h.block.muts i _ hm).2 ind rfl j hj }
  record := {
    record := hrb
    muts := h.record.muts
    recrs := h.record.recrs
    logic := h.record.logic
    members := fun i m hm => (hS.2 rb crb rs hrb h.record.muts i m hm).1 }
  covers := h.covers
  originals := h.originals
  motives := h.motives
  carriers := h.carriers
  major := h.major

end IxVM.Refinement.Binding
