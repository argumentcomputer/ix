import IxCC.Lam.Erase.Proof.Select

/-! # `casesOn` after its arguments

The three `casesOn` forms (empty, subsingleton, ordinary) against SrcEval's
F5, once the arguments are bound: SrcEval charges ι, chooses a rule (for an
ordinary eliminator by forcing the major), forces the minor and applies it
to the fields; Lam ticks, then `trap`s, applies the only minor to the index
fields, or cases on the major and applies the chosen alternative's minor. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

section Refs

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- References stay related when Lam binders are pushed on top. -/
theorem RefSlot.extend {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {ref : Ref} {s : Src.Slot}
    (h : RefSlot I G ls ρ ρ'' ref s) (xs : List Slot) : RefSlot I G ls ρ (xs ++ ρ'') ref s := by
  cases h with
  | box hs => exact .box hs
  | name => exact .name
  | lvl hl hg hv =>
    refine .lvl (by simp; omega) ?_ hv
    rename_i l _ _
    have e : (xs ++ ρ'').length - 1 - l = xs.length + (ρ''.length - 1 - l) := by simp; omega
    rw [e, List.getElem?_append_right (by omega)]
    simpa using hg

/-- No `r⋆` minor lives at or above the depth. -/
theorem MinorsLt.lookup_none {cx : Cx} (h : MinorsLt cx) {l : Nat} (hl : cx.depth ≤ l)
    (sig : List Mode) : cx.minors.lookup l ≠ some sig := fun e => by
  have := h _ (lookup_mem e)
  simp at this
  omega

end Refs

namespace Setting

variable (S : Setting)

/-- SrcEval's `casesOn` firing, once its entry and kind are known. -/
theorem fire_cases_of {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile} {ls' : Levels} {kind : Src.RecKind}
    (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some kind) (hag : Agree ls' q) (args : List Src.Slot) (j : Nat) :
    Src.fire S.p j (.cases c) ls' args = later j fun j =>
      (Src.recChosen S.p j ls' kind ind np (np + 1 + ni) (args.drop (np + 1)) args).bind
        fun (jr, fields) =>
          (Src.force S.p j (args.getD (np + 1 + ni + 1 + jr) default)).bind fun minor =>
            Src.applyAll S.p j minor fields := by
  rw [Src.fire_cases]
  simp only [Input.kindAt, input_recKind, Option.map_eq_some_iff] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  have hres' : S.p.table.resolveOf c = some (.case r) := hres
  have hd' : S.p.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) := hd
  simp only [hres', hd', hk₀, Option.map_some, hag.recKind]

theorem formArgs_getD {h : Head} {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {refs : List Ref}
    {ss : List Src.Slot} (hfa : FormArgs S.I S.G h ls ρ ρ'' refs ss) {i : Nat} (hi : i < ss.length)
    (hr : headReads S.I h i = true) :
    RefSlot S.I S.G ls ρ ρ'' (refs.getD i .box) (ss.getD i default) := by
  have hi' : i < refs.length := hfa.length ▸ hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hfa.at_ i _ _ (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hi) hr

theorem headReads_cases {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty)) {i : Nat}
    (hi : np + 1 ≤ i) : headReads S.I (.cases c) i = true := by
  simp [headReads, hres, hd, hi]

section

variable {S} (wf : ProgWF S.I) {m : Nat} (hlt : ∀ m' < m, S.Level m')
include wf hlt

/-- An ordinary `casesOn`: ι, the major's constructor, its minor on the
fields. -/
theorem cases_ord_form {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile}
    (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some .ordinary) (hu : S.I.unbox? ind q = none)
    {cx : Cx} {ρ : Src.Env} {ρ'' : Env} {ls ls' : Levels} (he : EnvR S.I S.G cx ρ ρ'')
    (hag : Agree ls cx.prof) (hag' : Agree ls' q) {refs : List Ref} {ss : List Src.Slot}
    (hfa : FormArgs S.I S.G (.cases c) ls ρ ρ'' refs ss) (hlen : ss.length = np + 1 + ni + 1 + nmin)
    {l : Nat} (hl : refs.getD (np + 1 + ni) .box = .lvl l) {alts : List Alt}
    (halts : AltsR S.I S.G cx r q ind refs (np + 1 + ni + 1) 0 rules alts) :
    SimUpTo (VR S.I S.G) m (fun j => Src.fire S.p j (.cases c) ls' ss)
      (fun j => Lam.eval S.L j ρ'' (.tick (.case (cx.lvl l) alts none))) := by
  have hmaj := S.formArgs_getD hfa (i := np + 1 + ni) (by omega)
    (S.headReads_cases hres hd (by omega))
  rw [hl] at hmaj
  generalize hsm : ss.getD (np + 1 + ni) default = sm at hmaj
  cases hmaj with
  | lvl _hl hg hvm =>
    rename_i mj mj'
    have hlam : ∀ j, Lam.eval S.L j ρ'' (cx.lvl l) = .ok mj' := fun j => by
      rw [Cx.lvl_eq, he.depth, Lam.eval_var_of S.L j ρ'' hg, Lam.force_val]
    obtain ⟨hcount, hrn⟩ := wf.recRules hd
    refine (SimUpTo.later (n := m)
      (c₁ := fun j => match S.p.selectRule ind np mj with
        | some (jr, flds) =>
          (Src.force S.p j (ss.getD (np + 1 + ni + 1 + jr) default)).bind fun mv =>
            Src.applyAll S.p j mv flds
        | none => .stuck)
      (c₂ := fun j => match mj'.asCtor S.L.known with
        | some (key, vals) => Lam.evalAlts S.L j ρ'' key vals alts none
        | none => .stuck)
      fun m' hm' => ?_).congr (fun j => ?_) (fun j => ?_)
    · have hlt' : ∀ m'' < m', S.Level m'' := fun m'' h => hlt m'' (by omega)
      have hap' : S.ApplySim m' := (hlt m' (by omega)).apply
      cases hsel : S.p.selectRule ind np mj with
      | none => exact SimUpTo.stuck _
      | some jf =>
        obtain ⟨jr, flds⟩ := jf
        obtain ⟨rule, key, n, fields, body, vals, hrule, hbody, hasc, hn, hev, hfs, hge⟩ :=
          select_alt wf (AltsR.altsFor halts) hcount
            (by rw [← Input.unbox?_prof S.I ind q]; exact hu) hvm hsel ρ'' he.depth
        have hjr : jr < nmin := by have := lt_of_getElem?_eq_some hrule; omega
        have hmin := S.formArgs_getD hfa (i := np + 1 + ni + 1 + jr) (by omega)
          (S.headReads_cases hres hd (by omega))
        have he' : EnvR S.I S.G (cx.extra n) ρ (vals.reverse.map .val ++ ρ'') := by
          have := he.extra (vals.reverse.map .val)
          simpa [hn] using this
        refine (minor_sim hlt' hap' hbody he' hag (hmin.extend _) hfs fun l' hl' sig => ?_).congr
          (fun j => rfl) (fun j => by simp only [hasc]; exact hev j none)
        exact he.minorsLt.lookup_none (hge l' hl') sig
    · rw [S.fire_cases_of hres hd hk hag' ss j]
      cases j with
      | zero => rfl
      | succ j =>
        simp only [later_succ, Src.recChosen, hsm, Src.force_val, Sem.Result.bind_ok]
        cases S.p.selectRule ind np mj with
        | none => rfl
        | some jf => simp [Result.ofOption]
    · rw [Lam.eval_tick]
      cases j with
      | zero => rfl
      | succ j =>
        show Lam.eval S.L j ρ'' _ = _
        rw [Lam.eval_case, hlam, Sem.Result.bind_ok]; rfl

omit hlt in
/-- For an unboxed inductive, the single constructor is at index 0 and its
field count is `unboxFields`. -/
theorem unboxFields_eq {ind c : CId} {q : Profile} {u : Nat} {sf : Bool}
    {lv cidx np nf : Nat} {ty : Src.Term} (hu : S.I.unbox? ind q = some u)
    (hd : S.I.decl? c = some (.ctor sf lv ind cidx np nf ty)) :
    unboxFields S.I ind = nf ∧ cidx = 0 := by
  obtain ⟨k, hk, _, _⟩ := unbox?_spec hu
  have hci := wf.ctorIn hd
  rw [hk] at hci
  cases cidx with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hci
    subst hci
    simp [unboxFields, hk, hd]
  | succ _ => simp at hci

/-- An unboxed ordinary `casesOn`: ι, the major forced (already the single
kept field), its only minor applied to that field at `u` and `irr` elsewhere. -/
theorem cases_unbox_form {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile} {u : Nat}
    (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some .ordinary) (hu : S.I.unbox? ind q = some u)
    {cx : Cx} {ρ : Src.Env} {ρ'' : Env} {ls ls' : Levels} (he : EnvR S.I S.G cx ρ ρ'')
    (hag : Agree ls cx.prof) (hag' : Agree ls' q) {refs : List Ref} {ss : List Src.Slot}
    (hfa : FormArgs S.I S.G (.cases c) ls ρ ρ'' refs ss) (hlen : ss.length = np + 1 + ni + 1 + nmin)
    {l : Nat} (hl : refs.getD (np + 1 + ni) .box = .lvl l)
    (hfresh : ∀ sig, cx.minors.lookup l ≠ some sig) {body : Term}
    (hbody : MinorR S.I S.G cx (refs.getD (np + 1 + ni + 1 + 0) .box)
      ((List.range (unboxFields S.I ind)).map fun i => if i == u then some l else none) body) :
    SimUpTo (VR S.I S.G) m (fun j => Src.fire S.p j (.cases c) ls' ss)
      (fun j => Lam.eval S.L j ρ'' (.tick body)) := by
  have hmaj := S.formArgs_getD hfa (i := np + 1 + ni) (by omega)
    (S.headReads_cases hres hd (by omega))
  rw [hl] at hmaj
  generalize hsm : ss.getD (np + 1 + ni) default = sm at hmaj
  cases hmaj with
  | lvl hlt_l hg hvm =>
    rename_i mj mj'
    obtain ⟨k_ind, hk_ind, _, _⟩ := unbox?_spec hu
    obtain ⟨hcount, hrn⟩ := wf.recRules hd
    have hmin : 0 < nmin := by rw [hk_ind, List.length_singleton] at hcount; omega
    refine (SimUpTo.later (n := m)
      (c₁ := fun j => match S.p.selectRule ind np mj with
        | some (jr, flds) =>
          (Src.force S.p j (ss.getD (np + 1 + ni + 1 + jr) default)).bind fun mv =>
            Src.applyAll S.p j mv flds
        | none => .stuck)
      (c₂ := fun j => Lam.eval S.L j ρ'' body)
      fun m' hm' => ?_).congr (fun j => ?_) (fun j => ?_)
    · have hlt' : ∀ m'' < m', S.Level m'' := fun m'' h => hlt m'' (by omega)
      have hap' : S.ApplySim m' := (hlt m' (by omega)).apply
      cases hsel : S.p.selectRule ind np mj with
      | none => exact SimUpTo.stuck _
      | some jf =>
        obtain ⟨jr, flds⟩ := jf
        cases mj with
        | lit n =>
          simp only [Src.Program.selectRule] at hsel
          split at hsel
          · next hnat =>
            have hN : S.I.known.nat = some ind := by simp at hnat; exact hnat.symm
            obtain ⟨_, Sc, _, _, _, ⟨sfs, lvs, tys, hdS⟩⟩ := wf.natPins hN
            have h1 := wf.ctorIn hdS
            rw [hk_ind] at h1
            simp at h1
          · cases hsel
        | con c_v ls_v ps_v fs_v =>
          simp only [Src.Program.selectRule] at hsel
          split at hsel
          · next sf' lv' ind' cidx np' nf ty' hd_c =>
            split at hsel
            · next hcond =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨rfl, _⟩ := hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hsel
              obtain ⟨rfl, rfl⟩ := hsel
              have hd_c' : S.I.decl? c_v = some (.ctor sf' lv' ind' cidx np' nf ty') := hd_c
              obtain ⟨hunf, hcidx0⟩ := S.unboxFields_eq wf hu hd_c'
              subst hcidx0
              obtain ⟨hlenf, hvr⟩ := hvm.con_inv hd_c'
              have hu0 : S.I.unbox? ind' [] = some u := by
                rw [← Input.unbox?_prof S.I ind' q]; exact hu
              rcases hvr with ⟨u', a, hu0', hfu, hva, hirr⟩ | ⟨hu0', _⟩
              · rw [hu0] at hu0'
                cases hu0'
                have hfs : Forall2 (FieldSlot S.I S.G ρ'')
                    ((List.range (unboxFields S.I ind')).map fun i =>
                      if i == u then some l else none)
                    (fs_v.map .val) := by
                  refine Forall2.of_getElem (by simp [hunf, hlenf]) fun i x y hx hy => ?_
                  simp only [List.getElem?_map, Option.map_eq_some_iff] at hx hy
                  obtain ⟨i', hi', rfl⟩ := hx
                  obtain ⟨f, hf, rfl⟩ := hy
                  have hi : i' = i := (range_getElem?_eq_some hi').1.symm
                  subst hi
                  by_cases hiu : i' = u
                  · subst hiu
                    simp only [beq_self_eq_true, ↓reduceIte]
                    rw [hfu] at hf
                    cases hf
                    exact .lvl hlt_l hg hva
                  · have hne : (i' == u) = false := beq_false_of_ne hiu
                    simp only [hne, Bool.false_eq_true, ↓reduceIte]
                    have hirr' := hirr i' f hf hiu
                    cases f with
                    | irr t ρ₀ ls₀ => exact .box ⟨_, _, _, rfl⟩
                    | _ => simp [Src.Value.isIrr] at hirr'
                have hminor := S.formArgs_getD hfa (i := np + 1 + ni + 1 + 0) (by omega)
                  (S.headReads_cases hres hd (by omega))
                refine minor_sim hlt' hap' hbody he hag hminor hfs fun l' hl' sig => ?_
                simp only [List.mem_map] at hl'
                obtain ⟨i, _, hs⟩ := hl'
                split at hs
                · cases hs; exact hfresh sig
                · cases hs
              · rw [hu0] at hu0'; cases hu0'
            · cases hsel
          · cases hsel
        | _ => simp [Src.Program.selectRule] at hsel
    · rw [S.fire_cases_of hres hd hk hag' ss j]
      cases j with
      | zero => rfl
      | succ j =>
        simp only [later_succ, Src.recChosen, hsm, Src.force_val, Sem.Result.bind_ok]
        cases S.p.selectRule ind np mj with
        | none => rfl
        | some jf => simp [Result.ofOption]
    · rw [Lam.eval_tick]; cases j <;> rfl

omit wf hlt in
/-- An empty `casesOn`: ι, then `trap`. -/
theorem cases_empty_form {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile}
    (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some .empty) {ρ'' : Env} {ls' : Levels} (hag' : Agree ls' q)
    (ss : List Src.Slot) :
    SimUpTo (VR S.I S.G) m (fun j => Src.fire S.p j (.cases c) ls' ss)
      (fun j => Lam.eval S.L j ρ'' (.tick .trap)) := by
  refine (SimUpTo.later (n := m) (c₁ := fun _ => .trap) (c₂ := fun _ => .trap)
    fun _ _ => SimUpTo.trap).congr (fun j => ?_) (fun j => ?_)
  · rw [S.fire_cases_of hres hd hk hag' ss j]
    cases j <;> rfl
  · rw [Lam.eval_tick]
    cases j with
    | zero => rfl
    | succ j => exact Lam.eval_trap' S.L j ρ''

/-- A subsingleton `casesOn`: ι, then its only minor on the index fields
(`irr` for the others), the major never forced. -/
theorem cases_sub_form {c r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile} {w : Src.PropWhen}
    {srcs : List Src.FieldSrc}
    (hres : S.I.resolve.get? c = some (.case r))
    (hd : S.I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some (.subsingleton w srcs))
    {cx : Cx} {ρ : Src.Env} {ρ'' : Env} {ls ls' : Levels} (he : EnvR S.I S.G cx ρ ρ'')
    (hag : Agree ls cx.prof) (hag' : Agree ls' q) {refs : List Ref} {ss : List Src.Slot}
    (hfa : FormArgs S.I S.G (.cases c) ls ρ ρ'' refs ss) (hlen : ss.length = np + 1 + ni + 1 + nmin)
    (hnn : ∀ i, i < np + 1 + ni + 1 → ∀ a, refs.getD i .box ≠ .name a)
    (hfresh : ∀ i l, refs.getD i .box = .lvl l → ∀ sig, cx.minors.lookup l ≠ some sig)
    (hmin : 0 < nmin) {body : Term}
    (hbody : MinorR S.I S.G cx (refs.getD (np + 1 + ni + 1 + 0) .box)
      (srcs.map fun
        | .index i => (refs.getD (np + 1 + i) .box).level?
        | .proof => none) body) :
    SimUpTo (VR S.I S.G) m (fun j => Src.fire S.p j (.cases c) ls' ss)
      (fun j => Lam.eval S.L j ρ'' (.tick body)) := by
  obtain ⟨k₀, hk₀, hkk⟩ : ∃ k₀, S.I.recKind.get? r = some k₀ ∧ k₀.atProfile q =
      .subsingleton w srcs := by
    simpa [Input.kindAt] using hk
  have hk₀' : S.I.recKind.get? r = some (.subsingleton w srcs) := by
    cases k₀ with
    | subsingleton w' srcs' =>
      simp only [Src.RecKind.atProfile] at hkk
      split at hkk
      · cases hkk; exact hk₀
      · cases hkk
    | _ => simp [Src.RecKind.atProfile] at hkk
  have hidx := wf.recKindIdx hd hk₀'
  -- The index fields as SrcEval builds them, against their references.
  have hfs : Forall2 (FieldSlot S.I S.G ρ'')
      (srcs.map fun
        | .index i => (refs.getD (np + 1 + i) .box).level?
        | .proof => none)
      (srcs.map fun
        | .index i => (ss.drop (np + 1)).getD i (Src.Slot.irrNone ls')
        | .proof => Src.Slot.irrNone ls') := by
    refine Forall2.of_getElem (by simp) fun i x y hx hy => ?_
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx hy
    obtain ⟨s₁, hs₁, rfl⟩ := hx
    obtain ⟨s₂, hs₂, rfl⟩ := hy
    rw [hs₁] at hs₂
    cases hs₂
    cases s₁ with
    | proof => exact .box ⟨_, _, _, rfl⟩
    | index i' =>
      have hi' : i' < ni := hidx i' (List.mem_of_getElem? hs₁)
      have hslot := S.formArgs_getD hfa (i := np + 1 + i') (by omega)
        (S.headReads_cases hres hd (by omega))
      have hdrop : (ss.drop (np + 1)).getD i' (Src.Slot.irrNone ls') =
          ss.getD (np + 1 + i') default := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [List.getElem?_eq_getElem (by omega)]
        rfl
      dsimp only
      rw [hdrop]
      generalize hr : refs.getD (np + 1 + i') .box = ref at hslot ⊢
      generalize hsl : ss.getD (np + 1 + i') default = sl at hslot ⊢
      cases hslot with
      | box hs => exact .box hs
      | lvl hl hg hv => exact .lvl hl hg hv
      | name => exact absurd hr (hnn _ (by omega) _)
  have hminor := S.formArgs_getD hfa (i := np + 1 + ni + 1 + 0) (by omega)
    (S.headReads_cases hres hd (by omega))
  refine (SimUpTo.later (n := m) fun m' hm' =>
    minor_sim (fun m'' h => hlt m'' (by omega)) (hlt m' (by omega)).apply hbody he hag hminor hfs
      fun l hl sig => ?_).congr (fun j => ?_) (fun j => ?_)
  · simp only [List.mem_map] at hl
    obtain ⟨s, _, hs⟩ := hl
    cases s with
    | proof => cases hs
    | index i' =>
      simp only [Ref.level?] at hs
      split at hs
      · next l' hl' => cases hs; exact hfresh _ _ hl' sig
      · cases hs
  · rw [S.fire_cases_of hres hd hk hag' ss j]
    cases j with
    | zero => rfl
    | succ j => simp only [later_succ, Src.recChosen, Sem.Result.bind_ok]; rfl
  · rw [Lam.eval_tick]; rfl

end

end Setting

end IxCC.Lam.Erase.Proof
