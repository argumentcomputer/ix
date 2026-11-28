import IxCK.Resource.Proof.F4Check
import IxCK.Resource.Proof.F4Default

/-!
# Operational Simulation Bridges for Checked Bodies (`F4OpsBridge`)

Provides the 9 non-recursive operational simulation bridges connecting `IxCK.Resource.Check`'s
abstract operations (`Runs`, `APrimArgs`, `ACaps`, `initBody`, `caseAltArgs`, `altRetVal`)
to `IxCK.Resource.Eval`'s concrete operations (`live`/`conform`, `projTail`, `construct`, `prim`,
`bindParamsM`, `bindAt`, `ret`, `select`, `formClosure`), with zero `evalS` recursion:

1. `var_bridge`
2. `proj_bridge`
3. `ctor_sat_bridge`
4. `prim_sat_bridge`
5. `bindParamsM_checked_sound`
6. `bindInner_bridge`
7. `retCheck_bridge`
8. `select_caseAltArgs_bridge` (+ `caseField_fromCell_clear`)
9. `acaps_formClosure_bridge` (+ `clo_call_sim_of_captures`)
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon

/-! ## 0. Shared Micro-Helpers -/

theorem SpentOnceSafe.liveRef {h : Heap} {v : Val} (hs : SpentOnceSafe h v) : LiveRef h v := by
  rcases hs with rfl | ⟨_, _, _, o, _, _, rfl, ho, hcap, _⟩
  · trivial
  · exact ⟨o, ho, hcap⟩

theorem NoOnceCell_of_nonOnce_cell {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {loc cap : Nat} {t : List Nat} {o : Obj}
    (ho : st.heap.objs[loc]? = some o)
    (hcf : CtorFieldsOk P ext B st (.ref loc cap t))
    (hcell : (∃ r fs, o.cell = .ctor r fs) ∨ (∃ n, o.cell = .num n)) :
    NoOnceCell st.heap (.ref loc cap t) := by
  intro l o' hr ho' tgt sp hc'
  cases hr with
  | here =>
    rw [ho] at ho'; cases ho'
    rcases hcell with ⟨_, _, hc⟩ | ⟨_, hc⟩ <;> (rw [hc] at hc'; cases hc')
  | step ho1 hm1 hr2 =>
    rw [ho] at ho1; cases ho1
    rcases hcell with ⟨r, fs, hc⟩ | ⟨n, hc⟩
    · rw [hc] at hm1
      exact (hcf loc o r fs _ .here ho hc hm1).1 l o' hr2 ho' tgt sp hc'
    · rw [hc] at hm1; cases hm1

theorem VSim_imm_irr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp} {av : AVal}
    (hregs : ∀ r ∈ av.regs, r < σ.nextRegion)
    (hdeps : ∀ d ∈ av.deps, d < σ.st.size)
    (hsrc : ∀ x, av.src = some x → x < σ.st.size ∧ x ∈ av.deps) :
    VSim P ext B st Frame NoKill NoSpend σ I (fun _ => False) av (.imm .irr) := by
  refine ⟨hregs, hdeps, hsrc, fun _ _ => SpentOnceSafe.irr _, fun _ => ?_⟩
  have hnv : NonValSafe st.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
  refine ⟨ValBaseOk_imm st .irr, DeepOpenUnder_imm _ _ _ _, CtorFieldsOk_imm P ext B st .irr,
    fun _ _ => hnv,
    fun _ => ⟨NoOnceCell_imm _ _, fun _ h => h, FunOkAt_imm_irr P ext B st av.skel⟩,
    fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
      (fun _ _ _ _ _ _ h => by cases h),
      FunOkAt_weaken_onceOnly (FunOkAt_imm_irr P ext B st av.skel)⟩,
    fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
      FunOkAt_weaken_onceOnly (FunOkAt_imm_irr P ext B st av.skel)⟩,
    fun _ => ⟨hnv.ownTreeFull.1, fun _ hr => False.elim (hnv.ownTreeFull.2 _ hr)⟩⟩

theorem ValEnvDisj_imm_irr {P : Prog} {st : St} {NoKill Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {envFoot : Nat → Nat → Prop} {av : AVal}
    (hsrcNone : av.src = none) :
    ValEnvDisj P st NoKill Scope env aenv σ envFoot (fun _ => False) av (.imm .irr) := by
  intro _ _ _ _ _ _ _
  refine ⟨(fun _ _ _ _ _ hor => by cases hor),
    (fun _ _ _ _ _ _ hr => by cases hr),
    fun _ _ _ _ _ h => False.elim h,
    (fun _ _ _ _ _ _ hr => by cases hr),
    (fun _ _ hs => by rw [hsrcNone] at hs; cases hs),
    (fun hs => by rw [hsrcNone] at hs; cases hs),
    (fun _ hs => by rw [hsrcNone] at hs; cases hs)⟩

theorem NoReachForbid_imm_irr (st : St) (Forbid BadReg BadDep : Nat → Prop) (av : AVal) :
    NoReachForbid st Forbid BadReg BadDep av (.imm .irr) :=
  fun _ _ _ hr => by cases hr

theorem VSim_nonValSafe {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp} {av : AVal} {v : Val}
    (hregs : ∀ r ∈ av.regs, r < σ.nextRegion)
    (hdeps : ∀ d ∈ av.deps, d < σ.st.size)
    (hsrcNone : av.src = none)
    (hbase : ValBaseOk st v)
    (hnv : NonValSafe st.heap v) :
    VSim P ext B st Frame NoKill NoSpend σ I (fun _ => False) av v := by
  have hnotOnce : ¬ IsOnceSrc σ av := by rintro ⟨_, hs, _⟩; rw [hsrcNone] at hs; cases hs
  refine ⟨hregs, hdeps, (fun _ hs => by rw [hsrcNone] at hs; cases hs),
    fun _ his => absurd his hnotOnce, fun _ => ?_⟩
  refine ⟨hbase, hnv.deepOpenUnder_nil, hnv.ctorFieldsOk P ext B st,
    fun _ _ => hnv,
    fun _ => ⟨hnv.noOnceCell, fun _ h => h, hnv.funOkAt P ext B st av.skel⟩,
    fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
      fun _ _ _ _ _ _ _ _ _ _ h => False.elim h,
      FunOkAt_weaken_onceOnly (hnv.funOkAt P ext B st av.skel)⟩,
    fun his => absurd his hnotOnce,
    fun _ => ⟨hnv.ownTreeFull.1, fun _ hr => False.elim (hnv.ownTreeFull.2 _ hr)⟩⟩

theorem ValEnvDisj_nonValSafe {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {av : AVal} {v : Val}
    (hsrcNone : av.src = none)
    (hnv : NonValSafe st.heap v)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    ValEnvDisj P st NoKill Scope env aenv σ envFoot (fun _ => False) av v := by
  intro i b ab hsc hbi habi hne
  refine ⟨fun _ _ _ _ _ hor => False.elim (hnv.ownTreeFull.2 _ hor),
    fun _ _ _ _ l hor hr => OwnReach_not_numLoc hor (hnv.reach_numLoc hr),
    fun _ _ _ _ _ h => False.elim h,
    fun haB hfB _ _ l hft hr => ?_,
    (fun _ _ hs => by rw [hsrcNone] at hs; cases hs),
    (fun hs => by rw [hsrcNone] at hs; cases hs),
    (fun _ hs => by rw [hsrcNone] at hs; cases hs)⟩
  have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.2.2.2.2 haB
  have hnum := hnv.reach_numLoc hr
  rcases hfB with hoO | ⟨hisB, _⟩
  · exact (hvB.2.2.2.2.2.1 hoO).1 l hft |>.2.2 hnum
  · exact (hvB.2.2.2.2.2.2.1 hisB).1 l hft |>.2.2 hnum

theorem NoReachForbid_nonValSafe {st : St} {Forbid BadReg BadDep : Nat → Prop} {av : AVal} {v : Val}
    (hnv : NonValSafe st.heap v) :
    NoReachForbid st Forbid BadReg BadDep av v :=
  fun _ _ _ hr _ hnotNum => absurd (hnv.reach_numLoc hr) hnotNum

theorem Cls_beq_false_of_ne {a b : Cls} (h : a ≠ b) : (a == b) = false := by
  cases a <;> cases b <;> first | exact absurd rfl h | rfl

theorem BinderMode_beq_false_of_ne {a b : BinderMode} (h : a ≠ b) : (a == b) = false := by
  cases a <;> cases b <;> first | exact absurd rfl h | rfl

theorem PreservesLocs_old_num {st₁ st₂ : St}
    (hp : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap) :
    ∀ (l : Nat) (o : Obj) (n : Nat),
      st₁.heap.objs[l]? = some o → o.cell = Cell.num n → st₂.heap.objs[l]? = some o := by
  intro l o _ ho _
  have hlt : l < st₁.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
  rw [hp l hlt, ho]

theorem StaticStrLoc_lt_size {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    (hst : StOk P ext B st) {l : Nat} (hss : StaticStrLoc st l) : l < st.heap.objs.size := by
  rcases hss with ⟨sr, sv, hm, hr⟩ | ⟨ss, sv, hm, hr⟩
  · obtain ⟨_, _, _, _, hbv, _⟩ := hst.2.2.1 sr sv hm
    exact hbv.1.reach_lt_size hr
  · obtain ⟨loc, cap, o, rfl, ho, _, hcell⟩ := hst.2.2.2 ss sv hm
    cases hr with
    | here => exact (Array.getElem?_eq_some_iff.mp ho).1
    | step ho' hm' _ => rw [ho] at ho'; cases ho'; rw [hcell] at hm'; cases hm'

theorem StaticStrLoc_unchanged_of_preserves {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    (hst : StOk P ext B st)
    (hstat : st'.statics = st.statics) (hstr : st'.strs = st.strs)
    (hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap)
    {l : Nat} (hss' : StaticStrLoc st' l) : StaticStrLoc st l ∧ l < st.heap.objs.size := by
  rcases hss' with ⟨sr, sv, hm, hr'⟩ | ⟨ss, sv, hm, hr'⟩
  · rw [hstat] at hm
    obtain ⟨_, _, _, _, hbv, _⟩ := hst.2.2.1 sr sv hm
    have hpV : PreservesLocs (Reach st.heap sv) st.heap st'.heap := hpSS.mono fun x hx => Or.inl ⟨sr, sv, hm, hx⟩
    have hr0 := (Reach_congr hpV l).mp hr'
    exact ⟨Or.inl ⟨sr, sv, hm, hr0⟩, hbv.1.reach_lt_size hr0⟩
  · rw [hstr] at hm
    obtain ⟨loc, cap, o, rfl, ho, _, hcell⟩ := hst.2.2.2 ss sv hm
    have hlt : loc < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
    have hssLoc : StaticStrLoc st loc := Or.inr ⟨ss, .ref loc cap [], hm, .here⟩
    have ho' : st'.heap.objs[loc]? = some o := by rw [hpSS loc hssLoc, ho]
    cases hr' with
    | here => exact ⟨Or.inr ⟨ss, .ref l cap [], hm, .here⟩, hlt⟩
    | step ho2 hm2 _ => rw [ho'] at ho2; cases ho2; rw [hcell] at hm2; cases hm2

theorem StaticStrLoc_unchanged {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    (hst : StOk P ext B st)
    (hstat : st'.statics = st.statics) (hstr : st'.strs = st.strs)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap)
    {l : Nat} (hss' : StaticStrLoc st' l) : StaticStrLoc st l ∧ l < st.heap.objs.size :=
  StaticStrLoc_unchanged_of_preserves hst hstat hstr (hp.mono fun _ h => StaticStrLoc_lt_size hst h) hss'

theorem OwnTreeFull_of_sameLoc {P : Prog} {h : Heap} {v₁ v₂ : Val}
    (hloc : SameLoc v₁ v₂) (ht : OwnTreeFull P h v₁) : OwnTreeFull P h v₂ := by
  cases v₁ with
  | imm _ =>
    cases v₂ with
    | imm _ =>
      constructor
      · intro _ _ _ _ _ _ _ _ _ _ _ hp; cases hp
      · intro _ _ _ _ _ _ _ hp; cases hp
    | ref _ _ _ => cases hloc
  | ref l₁ c₁ t₁ =>
    cases v₂ with
    | imm _ => cases hloc
    | ref l₂ c₂ t₂ =>
      dsimp only [SameLoc] at hloc; subst hloc
      constructor
      · intro p₁ p₂ i₁ i₂ l ca cb o₁ o₂ ta tb hp₁ hp₂
        exact ht.1 p₁ p₂ i₁ i₂ l ca cb o₁ o₂ ta tb
          (OwnReach_ref_taint.mp hp₁) (OwnReach_ref_taint.mp hp₂)
      · intro p l i o r fs w hp ho hcell hi hs hl
        exact ht.2 p l i o r fs w (OwnReach_ref_taint.mp hp) ho hcell hi hs
          (OwnReach_ref_taint.mp hl)

/-! ## 1. Bridge 1 (`var_bridge`) & Bridge 2 (`proj_bridge`) -/

/-- **Bridge 1 (`var_bridge`)**: simulates `ATerm.var` (`readVar` + class cast `c`) against
`live b.val >>= fun _ => conform c b.val`, handling both active and spent `@once` bindings. -/
theorem var_bridge {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {i : Nat} {c : Cls} {v : AVal}
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hsc : Scope i)
    (hread : Runs (readVar aenv i) σ v σ₁) :
    let m : M Val := do
      let some b := env[i]? | stuckM
      if b.mode == .erased then violate .erasedRead
      live b.val
      conform c b.val
    let Foot' : Nat → Prop := if c == .val then envFoot i else fun _ => False
    let av' : AVal := { v with cls := c }
    σ₁ = σ ∧
    (∃ b ab, env[i]? = some b ∧ aenv[i]? = some ab ∧ b.mode = ab.mode ∧ ab.mode ≠ .erased ∧ v = effVal ab) ∧
    (m.run st = .error .stuck ∨
     ∃ rv st', m.run st = .ok (rv, st') ∧
       st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
       st'.statics = st.statics ∧ st'.strs = st.strs ∧
       st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
       PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
       PreservesLocs Frame st.heap st'.heap ∧
       PreservesOnceShell st.heap st'.heap ∧
       StaticStrFresh st st' ∧
       StOk P ext B st' ∧
       Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ₁ I envFoot ∧
       EnvNoReachForbid st' Scope env aenv σ₁ Forbid BadReg BadDep ∧
       VSim P ext B st' Frame NoKill NoSpend σ₁ I Foot' av' rv ∧
       ValEnvDisj P st' NoKill Scope env aenv σ₁ envFoot Foot' av' rv ∧
       (ActiveVal σ₁ av' → NoReachForbid st' Forbid BadReg BadDep av' rv) ∧
       (ValidDeps σ₁ av'.deps → av'.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
       (∀ l, Reach st'.heap rv l →
         st.heap.objs.size ≤ l ∨ ∃ b, env[i]? = some b ∧ Reach st.heap b.val l)) := by
  intro m Foot' av'
  obtain ⟨ab, habi, hneAb, rfl, hvd, hσEq⟩ := Runs_readVar hread
  subst σ₁
  have hiA : i < aenv.length := (List.getElem?_eq_some_iff.mp habi).1
  have hiE : i < env.length := by rw [hsim.1]; exact hiA
  let b := env[i]
  have hbi : env[i]? = some b := List.getElem?_eq_getElem hiE
  obtain ⟨hmode, hneBody⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
  obtain ⟨honceAb, hvB⟩ := hneBody hneAb
  have hneB : b.mode ≠ .erased := by rw [hmode]; exact hneAb
  have hneBB : (b.mode == .erased) = false := beq_false_of_ne hneB
  have hmUnfold : m.run st = (do live b.val; conform c b.val).run st := by
    dsimp only [m]
    simp only [hbi, hneBB, Bool.false_eq_true, ↓reduceIte]
  refine ⟨rfl, ⟨b, ab, hbi, habi, hmode, hneAb, rfl⟩, ?_⟩
  rw [hmUnfold, M_bind_run]
  by_cases hact : ActiveVal σ (effVal ab)
  · obtain ⟨hbase, hopen, hcf, hnvB, hplain, honceOnly, honceSrc, htrans⟩ := hvB.2.2.2.2 hact
    rw [live_ok hbase.1.self.1]; dsimp only
    have hconfCases :
        (conform c b.val).run st = .error .stuck ∨
        ∃ rv st', (conform c b.val).run st = .ok (rv, st') ∧
          st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
          st'.statics = st.statics ∧ st'.strs = st.strs ∧
          st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
          PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
          PreservesOnceShell st.heap st'.heap ∧
          StaticStrFresh st st' ∧
          StOk P ext B st' ∧
          ValBaseOk st' rv ∧
          ClsSafe st'.heap c rv ∧
          CtorFieldsOk P ext B st' rv ∧
          (∀ rs A, DeepOpenUnder st.heap rs A b.val → DeepOpenUnder st'.heap rs A rv) ∧
          (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap b.val l) ∧
          (∀ l, OwnReach P st'.heap rv l → OwnReach P st.heap b.val l) ∧
          (OwnTreeFull P st.heap b.val → OwnTreeFull P st'.heap rv) ∧
          (c = .val → rv = b.val ∧ st' = st) ∧
          (c ≠ .val → NoOnceCell st'.heap rv ∧ FunOkAt P ext B st' (effVal ab).skel false (fun _ => False) rv) := by
      by_cases his : IsOnceSrc σ (effVal ab)
      · rcases conform_sound (onceOnly := true) (Foot := envFoot i) hst hbase hcf
            (fun h => by cases h) (honceSrc his).2.2 with hSt |
          ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst', hbase',
            hcls', hcf', hdou', hreach', hown', htree', _, hvalEq, hneVal, _⟩
        · exact Or.inl hSt
        · exact Or.inr ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
            hbase', hcls', hcf', hdou', hreach', hown', htree', hvalEq, hneVal⟩
      · by_cases hoO : (effVal ab).onceOnly = true
        · rcases conform_sound (onceOnly := true) (Foot := envFoot i) hst hbase hcf
              (fun h => by cases h) (honceOnly hoO).2.2.2 with hSt |
            ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst', hbase',
              hcls', hcf', hdou', hreach', hown', htree', _, hvalEq, hneVal, _⟩
          · exact Or.inl hSt
          · exact Or.inr ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
              hbase', hcls', hcf', hdou', hreach', hown', htree', hvalEq, hneVal⟩
        · have hoF : (effVal ab).onceOnly = false := Bool.eq_false_iff.mpr hoO
          obtain ⟨hno, _, hfun⟩ := hplain ⟨his, hoF⟩
          rcases conform_sound (onceOnly := false) (Foot := fun _ => False) hst hbase hcf
              (fun _ => hno) hfun with hSt |
            ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst', hbase',
              hcls', hcf', hdou', hreach', hown', htree', _, hvalEq, hneVal, _⟩
          · exact Or.inl hSt
          · exact Or.inr ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
              hbase', hcls', hcf', hdou', hreach', hown', htree', hvalEq, hneVal⟩
    rcases hconfCases with hSt |
      ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst', hbase',
        hcls', hcf', hdou', hreach', _, _, hvalEq, _⟩
    · exact Or.inl hSt
    · right
      have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
      have hIok' : InterpOk σ st' I := ⟨fun r hr' c' hc' => hnr ▸ hsim.2.2.1.1 r hr' c' hc',
        fun c' hc' => hsim.2.2.1.2 c' (hr ▸ hc')⟩
      have hpEnv : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
        Sim_preserves_of_old (AStateLe.refl σ) hpres hsim
      have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
        hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss
      have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok' hrf honceSh hssf
        (fun _ _ _ h => h) hpEnv hsim
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim)
        hsim.2.2.2.1 (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hpEnv henvNRF
      refine ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres,
        hpres.mono fun _ hf => hFrameLt _ hf, honceSh, hssf, hst', hsim', henvNRF', ?_, ?_, ?_, ?_, ?_⟩
      · -- VSim
        by_cases hcV : c = .val
        · subst hcV
          obtain ⟨rfl, rfl⟩ := hvalEq rfl
          have hftEq : Foot' = envFoot i := rfl
          rw [hftEq]
          refine ⟨hvB.1, hvB.2.1, hvB.2.2.1, hvB.2.2.2.1, fun _ => ?_⟩
          refine ⟨hbase, hopen, hcf, fun _ hne => absurd rfl hne, hplain, honceOnly, honceSrc, fun htr => ?_⟩
          by_cases habCls : (effVal ab).cls = .val
          · exact htrans ⟨habCls, htr.2.1, htr.2.2.1, htr.2.2.2.1, htr.2.2.2.2⟩
          · have hnv := hnvB htr.2.2.2.1 habCls
            exact ⟨hnv.ownTreeFull.1, fun _ hor => False.elim (hnv.ownTreeFull.2 _ hor)⟩
        · have hftEq : Foot' = fun _ => False := by dsimp only [Foot']; rw [Cls_beq_false_of_ne hcV]; rfl
          rw [hftEq]
          have hnv' : NonValSafe st'.heap rv := ClsSafe.to_nonValSafe hcV hcls' hbase'.1.self.1
          refine ⟨hvB.1, hvB.2.1, hvB.2.2.1, fun hvd' his' => ?_, fun _ => ?_⟩
          · have hsp : SpentOnceSafe st.heap b.val := hvB.2.2.2.1 hvd' his'
            rcases conform_spentOnceSafe (c := c) hsp with hSt | ⟨rv0, hrun0, hcases0⟩
            · rw [hSt] at hrun; cases hrun
            · rw [hrun0] at hrun; cases hrun
              rcases hcases0 with ⟨_, hcEq⟩ | ⟨rfl, _⟩
              · exact absurd hcEq hcV
              · exact SpentOnceSafe.irr _
          · exact ⟨hbase', hnv'.deepOpenUnder_nil, hnv'.ctorFieldsOk P ext B st',
              fun _ _ => hnv',
              fun _ => ⟨hnv'.noOnceCell, fun _ h => h, hnv'.funOkAt P ext B st' av'.skel⟩,
              fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
                fun _ _ _ _ _ _ _ _ _ _ h => False.elim h,
                FunOkAt_weaken_onceOnly (hnv'.funOkAt P ext B st' av'.skel)⟩,
              fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
                FunOkAt_weaken_onceOnly (hnv'.funOkAt P ext B st' av'.skel)⟩,
              fun htr => absurd htr.1 hcV⟩
      · -- ValEnvDisj
        by_cases hcV : c = .val
        · subst hcV
          obtain ⟨rfl, rfl⟩ := hvalEq rfl
          have hftEq : Foot' = envFoot i := rfl
          rw [hftEq]
          intro j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
          by_cases hij : i = j
          · subst hij
            rw [hbi] at hbi₂; cases hbi₂
            rw [habi] at habi₂; cases habi₂
            refine ⟨fun _ _ _ hdd => False.elim (hdd ab.id (List.mem_cons_self ..) (List.mem_cons_self ..)),
              fun _ _ _ hdd => False.elim (hdd ab.id (List.mem_cons_self ..) (List.mem_cons_self ..)),
              fun _ _ _ hne => absurd rfl hne,
              fun _ _ _ hne => absurd rfl hne,
              fun _ _ _ _ h => h,
              fun _ ho => ho,
              fun _ _ => Or.inl (SameLoc.refl _)⟩
          · have hidNe : ab.id ≠ ab₂.id := fun h => hij (hsim.2.2.2.2.1 i j ab ab₂ habi habi₂ h)
            have hsrcNe : av'.src ≠ some ab₂.id := fun h => hidNe (Option.some.inj h)
            obtain ⟨hdU1, hdF1⟩ := hsim.2.2.2.2.2.2 i j b b₂ ab ab₂ hij hsc hsc₂ hbi habi hbi₂ habi₂ hneAb hne₂
            obtain ⟨hdU2, hdF2⟩ := hsim.2.2.2.2.2.2 j i b₂ b ab₂ ab (Ne.symm hij) hsc₂ hsc hbi₂ habi₂ hbi habi hne₂ hneAb
            refine ⟨fun haV htrV haB hdd l hor hrB => ?_,
              fun haB htrB haV hdd => hdU2 haB htrB haV hdd,
              fun haV hfV haB _ => hdF1 haV hfV haB,
              fun haB hfB haV _ => hdF2 haB hfB haV,
              fun _ _ hs => absurd hs hsrcNe,
              fun hs => absurd hs hsrcNe,
              fun _ hs => absurd hs hsrcNe⟩
            by_cases habCls : (effVal ab).cls = .val
            · exact hdU1 haV ⟨habCls, htrV.2.1, htrV.2.2.1, htrV.2.2.2.1, htrV.2.2.2.2⟩ haB hdd l hor hrB
            · exact False.elim ((hnvB htrV.2.2.2.1 habCls).ownTreeFull.2 l hor)
        · have hftEq : Foot' = fun _ => False := by dsimp only [Foot']; rw [Cls_beq_false_of_ne hcV]; rfl
          rw [hftEq]
          have hnv' : NonValSafe st'.heap rv := ClsSafe.to_nonValSafe hcV hcls' hbase'.1.self.1
          intro j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
          refine ⟨fun _ htr => absurd htr.1 hcV,
            fun _ _ _ _ l hor hr => OwnReach_not_numLoc hor (hnv'.reach_numLoc hr),
            fun _ _ _ _ _ h => False.elim h,
            fun haB hfB _ _ l hft hr => ?_,
            fun _ _ _ _ h => False.elim h,
            fun hs ho => ?_,
            fun _ _ => Or.inr fun _ hr => hnv'.reach_numLoc hr⟩
          · have hvB₂ := ((hsim'.2.2.2.2.2.1 j b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2.2.2.2.2 haB
            have hnum := hnv'.reach_numLoc hr
            rcases hfB with hoO | ⟨hisB, _⟩
            · exact (hvB₂.2.2.2.2.2.1 hoO).1 l hft |>.2.2 hnum
            · exact (hvB₂.2.2.2.2.2.2.1 hisB).1 l hft |>.2.2 hnum
          · have hidEq : ab.id = ab₂.id := Option.some.inj hs
            have hij : i = j := hsim.2.2.2.2.1 i j ab ab₂ habi habi₂ hidEq
            subst hij; rw [habi] at habi₂; cases habi₂; exact ho
      · -- NoReachForbid
        intro ha' hregs hdeps l hr₂ hnotSS₂ hnotNum₂ hF
        rcases hreach' l hr₂ with hge | hr₁
        · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
        · have hnotSS₁ : ¬ StaticStrLoc st l := fun hss₁ =>
            hnotSS₂ (StaticStrLoc_mono (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hss₁)
          have hpB : PreservesLocs (Reach st.heap b.val) st.heap st'.heap :=
            hpres.mono fun _ hr => hbase.1.reach_lt_size hr
          have hnotNum₁ : ¬ NumLoc st.heap l := fun hnum₁ => hnotNum₂ ((NumLoc_congr hpB hr₁).mp hnum₁)
          exact henvNRF i b ab hsc hbi habi hneAb hact hregs hdeps l hr₁ hnotSS₁ hnotNum₁ hF
      · -- ValidDeps → av'.cls ≠ .val → ValBaseOk ∧ NonValSafe
        intro _ hneC
        exact ⟨hbase', ClsSafe.to_nonValSafe hneC hcls' hbase'.1.self.1⟩
      · -- Reach bound
        intro l hr
        rcases hreach' l hr with hge | hr₁
        · exact Or.inl hge
        · exact Or.inr ⟨b, hbi, hr₁⟩
  · -- Spent `@once` binding (`¬ ActiveVal σ (effVal ab)` with `ValidDeps σ (effVal ab).deps`)
    have his : IsOnceSrc σ (effVal ab) :=
      Classical.byContradiction fun hnot => hact ⟨hvd, fun h => absurd h hnot⟩
    have hsp : SpentOnceSafe st.heap b.val := hvB.2.2.2.1 hvd his
    rw [live_ok hsp.liveRef]; dsimp only
    rcases conform_spentOnceSafe (c := c) hsp with hSt | ⟨rv, hrun, hcases⟩
    · exact Or.inl hSt
    · right
      refine ⟨rv, st, hrun, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
        PreservesLocs.refl _ _, PreservesLocs.refl _ _, PreservesOnceShell.refl _,
        StaticStrFresh.refl _, hst, hsim, henvNRF, ?_, ?_, ?_, ?_, ?_⟩
      · -- VSim (ActiveVal σ av' is false!)
        have hnotAct' : ¬ ActiveVal σ av' := hact
        refine ⟨hvB.1, hvB.2.1, hvB.2.2.1, fun _ _ => ?_, fun ha => absurd ha hnotAct'⟩
        rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hsp
        · exact SpentOnceSafe.irr _
      · -- ValEnvDisj
        have hnotAct' : ¬ ActiveVal σ av' := hact
        intro j b₂ ab₂ _ _ habi₂ _
        refine ⟨fun ha => absurd ha hnotAct',
          fun _ _ ha => absurd ha hnotAct',
          fun ha => absurd ha hnotAct',
          fun _ _ ha => absurd ha hnotAct',
          fun ha => absurd ha hnotAct',
          fun hs ho => ?_,
          fun ha => absurd ha hnotAct'⟩
        have hij : i = j := hsim.2.2.2.2.1 i j ab ab₂ habi habi₂ (Option.some.inj hs)
        subst hij; rw [habi] at habi₂; cases habi₂; exact ho
      · -- NoReachForbid
        intro ha; exact absurd ha hact
      · -- ValidDeps → av'.cls ≠ .val → ValBaseOk ∧ NonValSafe
        intro _ hneC
        rcases hcases with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact absurd rfl hneC
        · exact ⟨ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
      · -- Reach bound
        intro l hr
        rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inr ⟨b, hbi, hr⟩
        · cases hr

/-- **Bridge 2 (`proj_bridge`)**: simulates `ATerm.proj` (`valid` + `anProj`, post Bug #12) against
`projTail P s i xv c`. -/
theorem proj_bridge {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {s : Ref} {i : Nat} {v res : AVal} {c : Cls} {xv : Val}
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hvd : ValidDeps σ v.deps)
    (hproj : Runs (anProj P s i v c) σ res σ')
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot v xv)
    (hdisj : ValEnvDisj P st NoKill Scope env aenv σ envFoot Foot v xv)
    (hnrf : ActiveVal σ v → NoReachForbid st Forbid BadReg BadDep v xv) :
    σ' = σ ∧
    ((projTail P s i xv c).run st = .error .stuck ∨
     ∃ rv st', (projTail P s i xv c).run st = .ok (rv, st') ∧
       st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
       st'.statics = st.statics ∧ st'.strs = st.strs ∧
       st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
       PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
       PreservesLocs Frame st.heap st'.heap ∧
       PreservesOnceShell st.heap st'.heap ∧
       StaticStrFresh st st' ∧
       StOk P ext B st' ∧
       Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
       EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
       VSim P ext B st' Frame NoKill NoSpend σ' I (fun _ => False) res rv ∧
       ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv ∧
       (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
       (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
       (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap xv l)) := by
  obtain ⟨hσEq, hprojInfo⟩ := Runs_anProj hproj
  subst σ'
  refine ⟨rfl, ?_⟩
  have hliveX : LiveRef st.heap xv := by
    by_cases hact : ActiveVal σ v
    · exact (hv.2.2.2.2 hact).1.1.self.1
    · have his : IsOnceSrc σ v :=
        Classical.byContradiction fun hnot => hact ⟨hvd, fun h => absurd h hnot⟩
      exact (hv.2.2.2.1 hvd his).liveRef
  cases hcs0 : (P.ctorsOf s)[0]? with
  | none =>
    left; unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only; rw [hcs0]; rfl
  | some ctor =>
    cases hco : P.ctorOf? ctor with
    | none =>
      left; unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only; rw [hcs0]; dsimp only; rw [hco]; rfl
    | some q =>
      rcases q with ⟨ind, ci, nP, fields⟩
      cases hf : fields[i]? with
      | none =>
        left; unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only
        rw [hcs0]; dsimp only; rw [hco]; dsimp only; rw [hf]; rfl
      | some f =>
        obtain ⟨hneEr, hResIrr, hResIL, hResNV, hResVal⟩ := hprojInfo ctor ind ci nP fields f hcs0 hco hf
        have hnotErAll : ∀ ctor' ind' ci' nP' fs' f',
            (P.ctorsOf s)[0]? = some ctor' → P.ctorOf? ctor' = some (ind', ci', nP', fs') →
            fs'[i]? = some f' → f'.mode ≠ .erased := by
          intro ctor' ind' ci' nP' fs' f' h1 h2 h3
          rw [hcs0] at h1; cases h1; rw [hco] at h2; cases h2; rw [hf] at h3; cases h3; exact hneEr
        have hneErB : (f.mode == .erased) = false := beq_false_of_ne hneEr
        -- Helper to finish when `(projTail P s i xv c).run st = .ok (.imm .irr, st)`
        have hFinishIrr : (projTail P s i xv c).run st = .ok (.imm .irr, st) →
            (res.src = none ∧ (∀ r ∈ res.regs, r < σ.nextRegion) ∧ (∀ d ∈ res.deps, d < σ.st.size)) →
            ∃ rv st', (projTail P s i xv c).run st = .ok (rv, st') ∧
              st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
              st'.statics = st.statics ∧ st'.strs = st.strs ∧
              st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
              PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
              PreservesLocs Frame st.heap st'.heap ∧
              PreservesOnceShell st.heap st'.heap ∧
              StaticStrFresh st st' ∧
              StOk P ext B st' ∧
              Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot ∧
              EnvNoReachForbid st' Scope env aenv σ Forbid BadReg BadDep ∧
              VSim P ext B st' Frame NoKill NoSpend σ I (fun _ => False) res rv ∧
              ValEnvDisj P st' NoKill Scope env aenv σ envFoot (fun _ => False) res rv ∧
              (ActiveVal σ res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
              (ValidDeps σ res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
              (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap xv l) := by
          intro hrun ⟨hsrcN, hregsB, hdepsB⟩
          exact ⟨.imm .irr, st, hrun, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
            PreservesLocs.refl _ _, PreservesLocs.refl _ _, PreservesOnceShell.refl _,
            StaticStrFresh.refl _, hst, hsim, henvNRF,
            VSim_imm_irr hregsB hdepsB (fun _ hs => by rw [hsrcN] at hs; cases hs),
            ValEnvDisj_imm_irr hsrcN,
            fun _ => NoReachForbid_imm_irr st Forbid BadReg BadDep res,
            fun _ _ => ⟨ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩,
            fun _ hr => by cases hr⟩
        have hResMeta : res.src = none ∧ (∀ r ∈ res.regs, r < σ.nextRegion) ∧ (∀ d ∈ res.deps, d < σ.st.size) := by
          by_cases hfi : f.cls = .irr
          · rw [hResIrr (Or.inl hfi)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
          · cases hc : c with
            | irr => rw [hResIrr (Or.inr hc)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
            | imm => rw [hResIL hfi (Or.inl hc)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
            | leaf => rw [hResIL hfi (Or.inr hc)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
            | val =>
              by_cases hvc : v.cls = .val
              · rw [hResVal hfi hc hvc]; exact ⟨rfl, hv.1, hv.2.1⟩
              · rw [hResNV hfi hc hvc]; exact ⟨rfl, hv.1, hv.2.1⟩
        by_cases hfi : f.cls = .irr
        · right
          have hrun : (projTail P s i xv c).run st = .ok (.imm .irr, st) := by
            unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only
            rw [hcs0]; dsimp only; rw [hco]; dsimp only; rw [hf]; dsimp only
            simp only [hneErB, Bool.false_eq_true, ↓reduceIte, hfi]; rfl
          exact hFinishIrr hrun hResMeta
        · have hfiB : (f.cls == .irr) = false := Cls_beq_false_of_ne hfi
          have hTailImm : ∀ im, xv = .imm im → (projTail P s i xv c).run st =
              if P.wrapperField? s == some i then (conform c xv).run st else .error .stuck := by
            intro im hEq; subst hEq
            unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only
            simp only [hcs0, hco, hf, hneErB, hfiB, Bool.false_eq_true, ↓reduceIte]
            split <;> rfl
          have hTailNum : ∀ loc cap tv o n, xv = .ref loc cap tv → st.heap.objs[loc]? = some o →
              o.cell = .num n → (projTail P s i xv c).run st =
              if P.wrapperField? s == some i then (conform c xv).run st else .error .stuck := by
            intro loc cap tv o n hEq ho hnum; subst hEq
            unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only
            simp only [hcs0, hco, hf, hneErB, hfiB, Bool.false_eq_true, ↓reduceIte]
            rw [M_bind_run]
            have hobj : (obj loc).run st = .ok (o, st) := by
              change (match st.heap.objs[loc]? with | some o => pure o | none => stuckM : M Obj).run st = .ok (o, st)
              rw [ho]; rfl
            rw [hobj]; dsimp only; rw [hnum]; dsimp only; split <;> rfl
          have hTailOther : ∀ loc cap tv o, xv = .ref loc cap tv → st.heap.objs[loc]? = some o →
              (∀ r' fs, o.cell ≠ .ctor r' fs) → (∀ n, o.cell ≠ .num n) →
              (projTail P s i xv c).run st = .error .stuck := by
            intro loc cap tv o hEq ho hnc hnn; subst hEq
            unfold projTail; rw [M_bind_run, live_ok hliveX]; dsimp only
            simp only [hcs0, hco, hf, hneErB, hfiB, Bool.false_eq_true, ↓reduceIte]
            rw [M_bind_run]
            have hobj : (obj loc).run st = .ok (o, st) := by
              change (match st.heap.objs[loc]? with | some o => pure o | none => stuckM : M Obj).run st = .ok (o, st)
              rw [ho]; rfl
            rw [hobj]; dsimp only
            cases hcO : o.cell with
            | ctor r' fs => exact absurd hcO (hnc r' fs)
            | num n => exact absurd hcO (hnn n)
            | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => rfl
          by_cases his : IsOnceSrc σ v
          · have hsp : SpentOnceSafe st.heap xv := hv.2.2.2.1 hvd his
            rcases hsp with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, _, hcell⟩
            · cases hwf : (P.wrapperField? s == some i) with
              | false =>
                left; rw [hTailImm .irr rfl]; simp only [hwf, Bool.false_eq_true, ↓reduceIte]
              | true =>
                rcases conform_spentOnceSafe (c := c) (SpentOnceSafe.irr st.heap) with hSt | ⟨rv, hrun, hcases⟩
                · left; rw [hTailImm .irr rfl]; simp only [hwf, ↓reduceIte]; exact hSt
                · have hrv : rv = .imm .irr := by rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
                  subst hrv
                  have hrunP : (projTail P s i (.imm .irr) c).run st = .ok (.imm .irr, st) := by
                    rw [hTailImm .irr rfl]; simp only [hwf, ↓reduceIte]; exact hrun
                  exact Or.inr (hFinishIrr hrunP hResMeta)
            · left; exact hTailOther loc cap t o rfl ho (fun _ _ h => by rw [hcell] at h; cases h)
                (fun _ h => by rw [hcell] at h; cases h)
          · have hact : ActiveVal σ v := ⟨hvd, fun h => absurd h his⟩
            obtain ⟨hbase, hopen, hcf, hnvB, _, _, _, _⟩ := hv.2.2.2.2 hact
            by_cases hvCls : v.cls = .val
            · -- Main case: `v.cls = .val`, `¬ IsOnceSrc σ v`, `f.cls ≠ .irr`
              have hNoOnceOrStuck :
                  (projTail P s i xv c).run st = .error .stuck ∨
                  (NoOnceCell st.heap xv ∧
                    (xv = .imm .irr ∨ (∃ im, xv = .imm im) ∨
                      (∃ loc cap o n, xv = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n) ∨
                      (∃ loc cap tv o r' fs, xv = .ref loc cap tv ∧ st.heap.objs[loc]? = some o ∧ o.cell = .ctor r' fs))) := by
                cases hxv : xv with
                | imm im => exact Or.inr ⟨NoOnceCell_imm _ _, Or.inr (Or.inl ⟨im, rfl⟩)⟩
                | ref loc cap tv =>
                  have hbaseR : ValBaseOk st (.ref loc cap tv) := hxv ▸ hbase
                  obtain ⟨o, ho, hcap⟩ := hbaseR.1.self.1
                  cases hcO : o.cell with
                  | ctor r' fs =>
                    exact Or.inr ⟨NoOnceCell_of_nonOnce_cell ho (hxv ▸ hcf) (Or.inl ⟨r', fs, hcO⟩),
                      Or.inr (Or.inr (Or.inr ⟨loc, cap, tv, o, r', fs, rfl, ho, hcO⟩))⟩
                  | num n =>
                    have htNil : tv = [] := hbaseR.2.2.1 (.ref loc cap tv) (HeldBy.refl _ _) o n ho hcO
                    subst htNil
                    exact Or.inr ⟨NoOnceCell_of_nonOnce_cell ho (hxv ▸ hcf) (Or.inr ⟨n, hcO⟩),
                      Or.inr (Or.inr (Or.inl ⟨loc, cap, o, n, rfl, ho, hcO⟩))⟩
                  | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
                    left; rw [← hxv]; exact hTailOther loc cap tv o hxv ho
                      (fun _ _ h => by rw [hcO] at h; cases h) (fun _ h => by rw [hcO] at h; cases h)
              rcases hNoOnceOrStuck with hSt | ⟨hnoX, hshapeX⟩
              · exact Or.inl hSt
              · have hskNonCtor :
                    (xv = .imm .irr ∨ (∃ im, xv = .imm im) ∨
                      ∃ loc cap o n, xv = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n) →
                    FunOkAt P ext B st .unknown false (fun _ => False) xv := by
                  intro hnc
                  have hnv : NonValSafe st.heap xv := by
                    rcases hnc with rfl | ⟨im, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, hnum⟩
                    · exact Or.inl ⟨.irr, rfl⟩
                    · exact Or.inl ⟨im, rfl⟩
                    · obtain ⟨o', ho', hcap⟩ := hbase.1.self.1
                      rw [ho] at ho'; cases ho'
                      exact Or.inr ⟨loc, cap, o, n, rfl, ho, hcap, hnum⟩
                  exact hnv.funOkAt P ext B st .unknown
                rcases proj_sound (sk := .unknown) (A := I.regsOf v.regs) hst hbase hnoX hcf hopen
                    hnotErAll hskNonCtor (Or.inl rfl) with hSt |
                  ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, _, honceSh, hssf, hst',
                    hbase', hcls', hno', hcf', hfun', hdou', hreach'⟩
                · exact Or.inl hSt
                · right
                  have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
                  have hIok' : InterpOk σ st' I := ⟨fun r hr' c' hc' => hnr ▸ hsim.2.2.1.1 r hr' c' hc',
                    fun c' hc' => hsim.2.2.1.2 c' (hr ▸ hc')⟩
                  have hpEnv : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
                    Sim_preserves_of_old (AStateLe.refl σ) hpres hsim
                  have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
                    hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss
                  have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok' hrf honceSh hssf
                    (fun _ _ _ h => h) hpEnv hsim
                  have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim)
                    hsim.2.2.2.1 (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hpEnv henvNRF
                  refine ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres,
                    hpres.mono fun _ hf' => hFrameLt _ hf', honceSh, hssf, hst', hsim', henvNRF',
                    ?_, ?_, ?_, ?_, hreach'⟩
                  · -- VSim
                    cases hc : c with
                    | val =>
                      rw [hResVal hfi hc hvCls]
                      have hnotOnceR : ¬ IsOnceSrc σ { cls := .val, deps := v.deps, regs := v.regs, skel := .unknown } := by
                        rintro ⟨_, hs, _⟩; cases hs
                      refine ⟨hv.1, hv.2.1, (fun _ hs => by cases hs), fun _ h => absurd h hnotOnceR, fun _ => ?_⟩
                      exact ⟨hbase', (by rw [hc] at hdou'; exact hdou'), hcf',
                        fun _ hne => absurd hc hne,
                        fun _ => ⟨hno', fun _ h => h, hfun'⟩,
                        (fun h => by cases h),
                        fun h => absurd h hnotOnceR,
                        (fun htr => by cases htr.2.1)⟩
                    | irr =>
                      rw [hResIrr (Or.inr hc)]
                      exact VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl
                        hbase' (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                    | imm =>
                      rw [hResIL hfi (Or.inl hc)]
                      exact VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl
                        hbase' (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                    | leaf =>
                      rw [hResIL hfi (Or.inr hc)]
                      exact VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl
                        hbase' (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                  · -- ValEnvDisj
                    cases hc : c with
                    | val =>
                      rw [hResVal hfi hc hvCls]
                      intro j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
                      obtain ⟨_, hd2, _, hd4, _, _, hd7⟩ := hdisj j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
                      have hvB₂ := ((hsim.2.2.2.2.2.1 j b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
                      refine ⟨(fun _ htr => by cases htr.2.1),
                        fun haB htrB _ hdd l hor hrR => ?_,
                        fun _ _ _ _ _ h => False.elim h,
                        fun haB hfB _ _ l hft hrR => ?_,
                        (fun _ _ hs => by cases hs),
                        (fun hs => by cases hs),
                        (fun _ hs => by cases hs)⟩
                      · have hpB := hpEnv j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ haB
                        have hor1 : OwnReach P st.heap b₂.val l := (OwnReach_congr hpB l).mp hor
                        rcases hreach' l hrR with hge | hr1
                        · exact Nat.not_lt_of_ge hge ((hvB₂.2.2.2.2 haB).1.1.reach_lt_size (OwnReach_toReach hor1))
                        · exact hd2 haB htrB hact hdd l hor1 hr1
                      · have hftNotNum : ¬ NumLoc st.heap l := by
                          rcases hfB with hoO | ⟨hisB, _⟩
                          · exact ((hvB₂.2.2.2.2 haB).2.2.2.2.2.1 hoO).1 l hft |>.2.2
                          · exact ((hvB₂.2.2.2.2 haB).2.2.2.2.2.2.1 hisB).1 l hft |>.2.2
                        have hftReach : Reach st.heap b₂.val l := by
                          rcases hfB with hoO | ⟨hisB, _⟩
                          · exact ((hvB₂.2.2.2.2 haB).2.2.2.2.2.1 hoO).1 l hft |>.1
                          · exact ((hvB₂.2.2.2.2 haB).2.2.2.2.2.2.1 hisB).1 l hft |>.1
                        rcases hreach' l hrR with hge | hr1
                        · exact Nat.not_lt_of_ge hge ((hvB₂.2.2.2.2 haB).1.1.reach_lt_size hftReach)
                        · by_cases hsrcEq : v.src = some ab₂.id
                          · rcases hd7 hact hsrcEq with hsame | hnumAll
                            · rcases hshapeX with rfl | ⟨im, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, hnum⟩ |
                                ⟨loc, cap, tv, o, r', fs, rfl, ho, hctor⟩
                              · cases hr1
                              · cases hr1
                              · exact hftNotNum ((NonValSafe.reach_numLoc (Or.inr ⟨loc, cap, o, n, rfl, ho,
                                  (by obtain ⟨o', ho', hcap⟩ := hbase.1.self.1; rw [ho] at ho'; cases ho'; exact hcap),
                                  hnum⟩)) hr1)
                              · cases hb2 : b₂.val with
                                | imm _ => rw [hb2] at hsame; cases hsame
                                | ref l₂ c₂ t₂ =>
                                  rw [hb2] at hsame; simp only [SameLoc] at hsame; subst hsame
                                  rcases hfB with hoO | ⟨hisB, _⟩
                                  · exact ((hvB₂.2.2.2.2 haB).2.2.2.2.2.1 hoO).2.2.1 l₂ c₂ t₂ o r' fs hb2 ho hctor l hft
                                  · have hsp₂ := hvB₂.2.2.2.1 haB.1 hisB
                                    rcases hsp₂ with h | ⟨_, _, _, o₂, _, _, hEq, ho₂, _, hc₂⟩
                                    · rw [h] at hb2; cases hb2
                                    · rw [hEq] at hb2; cases hb2; rw [ho] at ho₂; cases ho₂; rw [hctor] at hc₂; cases hc₂
                            · exact hftNotNum (hnumAll l hr1)
                          · exact hd4 haB hfB hact hsrcEq l hft hr1
                    | irr =>
                      rw [hResIrr (Or.inr hc)]
                      exact ValEnvDisj_nonValSafe rfl (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1) hsim'
                    | imm =>
                      rw [hResIL hfi (Or.inl hc)]
                      exact ValEnvDisj_nonValSafe rfl (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1) hsim'
                    | leaf =>
                      rw [hResIL hfi (Or.inr hc)]
                      exact ValEnvDisj_nonValSafe rfl (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1) hsim'
                  · -- NoReachForbid
                    intro _
                    cases hc : c with
                    | val =>
                      rw [hResVal hfi hc hvCls]
                      intro hregs hdeps l hr₂ hnotSS₂ hnotNum₂ hF
                      rcases hreach' l hr₂ with hge | hr₁
                      · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
                      · have hnotSS₁ : ¬ StaticStrLoc st l := fun hss₁ =>
                          hnotSS₂ (StaticStrLoc_mono (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hss₁)
                        have hpX : PreservesLocs (Reach st.heap xv) st.heap st'.heap :=
                          hpres.mono fun _ hr => hbase.1.reach_lt_size hr
                        have hnotNum₁ : ¬ NumLoc st.heap l := fun hnum₁ => hnotNum₂ ((NumLoc_congr hpX hr₁).mp hnum₁)
                        exact hnrf hact hregs hdeps l hr₁ hnotSS₁ hnotNum₁ hF
                    | irr =>
                      rw [hResIrr (Or.inr hc)]
                      exact NoReachForbid_nonValSafe (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                    | imm =>
                      rw [hResIL hfi (Or.inl hc)]
                      exact NoReachForbid_nonValSafe (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                    | leaf =>
                      rw [hResIL hfi (Or.inr hc)]
                      exact NoReachForbid_nonValSafe (ClsSafe.to_nonValSafe (by decide) (hc ▸ hcls') hbase'.1.self.1)
                  · -- ValidDeps → res.cls ≠ .val → ValBaseOk ∧ NonValSafe
                    intro _ hneR
                    have hneC : c ≠ .val := by
                      intro hc; subst hc
                      rw [hResVal hfi rfl hvCls] at hneR; exact hneR rfl
                    exact ⟨hbase', ClsSafe.to_nonValSafe hneC hcls' hbase'.1.self.1⟩
            · -- `v.cls ≠ .val`, `¬ IsOnceSrc σ v`, `f.cls ≠ .irr`: `xv` is `NonValSafe`, so `projTail` hits `asWrapper`
              have hnvX : NonValSafe st.heap xv := hnvB his hvCls
              have hAsWrap : (projTail P s i xv c).run st =
                  if P.wrapperField? s == some i then (conform c xv).run st else .error .stuck := by
                rcases hnvX with ⟨im, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
                · exact hTailImm im rfl
                · exact hTailNum loc cap [] o n rfl ho hnum
              rw [hAsWrap]
              split
              · rcases conform_sound (onceOnly := false) (Foot := fun _ => False) (sk := v.skel)
                    hst hbase (hnvX.ctorFieldsOk P ext B st) (fun _ => hnvX.noOnceCell)
                    (hnvX.funOkAt P ext B st v.skel) with hSt |
                  ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
                    hbase', hcls', _, _, hreach', _, _, _, hvalEq, _, _⟩
                · exact Or.inl hSt
                · right
                  have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
                  have hIok' : InterpOk σ st' I := ⟨fun r hr' c' hc' => hnr ▸ hsim.2.2.1.1 r hr' c' hc',
                    fun c' hc' => hsim.2.2.1.2 c' (hr ▸ hc')⟩
                  have hpEnv : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
                    Sim_preserves_of_old (AStateLe.refl σ) hpres hsim
                  have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
                    hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss
                  have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok' hrf honceSh hssf
                    (fun _ _ _ h => h) hpEnv hsim
                  have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim)
                    hsim.2.2.2.1 (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hpEnv henvNRF
                  have hnv' : NonValSafe st'.heap rv := by
                    by_cases hcV : c = .val
                    · obtain ⟨rfl, rfl⟩ := hvalEq hcV; exact hnvX
                    · exact ClsSafe.to_nonValSafe hcV hcls' hbase'.1.self.1
                  exact ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres,
                    hpres.mono fun _ hf' => hFrameLt _ hf', honceSh, hssf, hst', hsim', henvNRF',
                    VSim_nonValSafe hResMeta.2.1 hResMeta.2.2 hResMeta.1 hbase' hnv',
                    ValEnvDisj_nonValSafe hResMeta.1 hnv' hsim',
                    fun _ => NoReachForbid_nonValSafe hnv',
                    fun _ _ => ⟨hbase', hnv'⟩, hreach'⟩
              · exact Or.inl rfl

/-! ## 2. Bridge 4 (`prim_sat_bridge`) -/

/-- Structural unpacking of `APrimArgs`: state monotonicity, no killings, and per-arg validity. -/
theorem APrimArgs_info {avs : List (Option AVal)} {σ σ' : AState}
    {deps₀ regs₀ deps regs : List Nat}
    (hok : AStateOk σ) (h : APrimArgs avs σ deps₀ regs₀ deps regs σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    (∀ i, i < σ.st.size → σ'.st[i]? = some .dead → σ.st[i]? = some .dead) ∧
    (∀ a, some a ∈ avs → ValidDeps σ a.deps ∧ (a.cls = .val → ¬ IsOnceSrc σ a)) := by
  induction h with
  | nil =>
    exact ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ h => by cases h⟩
  | consNone _ ih =>
    obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hnd, hall⟩ := ih hok
    refine ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hnd, fun a ha => ?_⟩
    simp only [List.mem_cons, reduceCtorEq, false_or] at ha
    exact hall a ha
  | @consNonVal a rest σ0 σ1 deps0 regs0 deps1 regs1 σ2 hne hval _ ih =>
    obtain ⟨hvd, rfl⟩ := Runs_valid hval
    obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hnd, hall⟩ := ih hok
    refine ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hnd, fun a' ha' => ?_⟩
    rcases List.mem_cons.mp ha' with hEq | hmem
    · cases hEq; exact ⟨hvd, fun h => absurd h hne⟩
    · exact hall a' hmem
  | @consVal a rest σ0 σ1 deps0 regs0 deps1 regs1 σ2 hcls hflow _ ih =>
    obtain ⟨hok1, hle1, hszSt1, honce1, hszSp1, hreg1, hnr1, hvd, _, hnotShare, _, _, hst1, _, _⟩ :=
      Runs_flowTo hok hflow
    obtain ⟨_, _, hnotOnce⟩ := hnotShare (by intro h; cases h)
    obtain ⟨hok2, hle2, hszSt2, honce2, hszSp2, hreg2, hnr2, hnd2, hall2⟩ := ih hok1
    have hnd1 : ∀ i, i < σ0.st.size → σ1.st[i]? = some .dead → σ0.st[i]? = some .dead := by
      intro i hi hdead
      rw [hst1 rfl i hi] at hdead
      by_cases hcond : a.cls = .val ∧ i ∈ a.deps ∧ σ0.st[i]? = some .live
      · simp only [hcond, and_self, ↓reduceIte] at hdead; cases hdead
      · simp only [hcond, ↓reduceIte] at hdead; exact hdead
    refine ⟨hok2, hle1.trans hle2, hszSt2.trans hszSt1, honce2.trans honce1, hszSp2.trans hszSp1,
      hreg2.trans hreg1, hnr2.trans hnr1,
      fun i hi hdead => hnd1 i hi (hnd2 i (hszSt1 ▸ hi) hdead),
      fun a' ha' => ?_⟩
    rcases List.mem_cons.mp ha' with hEq | hmem
    · cases hEq; exact ⟨hvd, fun _ => hnotOnce⟩
    · obtain ⟨hvd1, hno1⟩ := hall2 a' hmem
      refine ⟨ValidDeps.of_AStateLe hle1 (fun d hd => hszSt1 ▸ (hvd1 d hd).1) hvd1, fun hc his0 => ?_⟩
      apply hno1 hc
      obtain ⟨id, hsrc, ho0⟩ := his0
      exact ⟨id, hsrc, by rw [honce1]; exact ho0⟩

/-- **Bridge 4 (`prim_sat_bridge`)**: simulates a saturated primitive call (`APrimArgs` + `prim` +
`conform c`). -/
theorem prim_sat_bridge {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {p : Prim} {c : Cls} {vs : List Val}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {deps regs : List Nat}
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args)
    (hvsLen : vs.length = args.length)
    (hvsMatch : ∀ (i : Nat) v av ft, args[i]? = some (some (v, av, ft)) → vs[i]? = some v)
    (hNoneLive : ∀ (i : Nat) v, args[i]? = some none → vs[i]? = some v → LiveRef st.heap v)
    (hprimA : APrimArgs (args.map (Option.map fun x => x.2.1)) σ [] [] deps regs σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    (NoKillOk NoKill σ → NoKillOk NoKill σ') ∧
    ((do conform c (← prim p vs)).run st = .error .stuck ∨
     ∃ rv st', (do conform c (← prim p vs)).run st = .ok (rv, st') ∧
       st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
       st'.statics = st.statics ∧ st'.strs = st.strs ∧
       st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
       PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
       PreservesLocs Frame st.heap st'.heap ∧
       PreservesOnceShell st.heap st'.heap ∧
       StaticStrFresh st st' ∧
       StOk P ext B st' ∧
       Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
       EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
       VSim P ext B st' Frame NoKill NoSpend σ' I (fun _ => False) { cls := c } rv ∧
       ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) { cls := c } rv ∧
       (ActiveVal σ' { cls := c } → NoReachForbid st' Forbid BadReg BadDep { cls := c } rv) ∧
       (ValidDeps σ' ({ cls := c } : AVal).deps → ({ cls := c } : AVal).cls ≠ .val →
         ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
       (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l)) := by
  obtain ⟨hok', hle', hszSt', _, _, hreg', hnr', hnd', hallA⟩ := APrimArgs_info hsim.2.1 hprimA
  have hnk' : NoKillOk NoKill σ → NoKillOk NoKill σ' := by
    intro hnk d hnd hdead
    have hlt : d < σ.st.size := by
      have := (Array.getElem?_eq_some_iff.mp hdead).1; omega
    exact hnk d hnd (hnd' d hlt hdead)
  have hliveVs : ∀ v ∈ vs, LiveRef st.heap v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hiA : i < args.length := hvsLen ▸ hi
    cases harg : args[i]? with
    | none => exact absurd (List.getElem?_eq_none_iff.mp harg) (Nat.not_le_of_lt hiA)
    | some opt =>
      cases opt with
      | none => exact hNoneLive i vs[i] harg (List.getElem?_eq_getElem hi)
      | some triple =>
        rcases triple with ⟨v', av, ft⟩
        have hvEq : vs[i]? = some v' := hvsMatch i v' av ft harg
        rw [List.getElem?_eq_getElem hi] at hvEq; cases hvEq
        have hmemAv : some av ∈ args.map (Option.map fun x => x.2.1) := by
          refine List.mem_map.mpr ⟨some (vs[i], av, ft), List.mem_of_getElem? harg, rfl⟩
        obtain ⟨hvd, hnoVal⟩ := hallA av hmemAv
        obtain ⟨hvSim, _, _, hnv⟩ := hargs.1 i vs[i] av ft harg
        by_cases hcV : av.cls = .val
        · exact (hvSim.2.2.2.2 ⟨hvd, fun his => absurd his (hnoVal hcV)⟩).1.1.self.1
        · exact (hnv hvd hcV).1.1.self.1
  refine ⟨hok', hle', hnk', ?_⟩
  rcases prim_sound (P := P) (ext := ext) (B := B) (p := p) (vs := vs) (c := c) hst hliveVs with
    hSt | ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
      hbase', hcls', hdou', hcf', hno', hfun', htree', hreach'⟩
  · exact Or.inl hSt
  · right
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    have hIok' : InterpOk σ' st' I :=
      ⟨fun r hr' c' hc' => hnr ▸ hsim.2.2.1.1 r (hnr' ▸ hr') c' hc',
       fun c' hc' => hreg'.symm ▸ hsim.2.2.1.2 c' (hr ▸ hc')⟩
    have hpEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap :=
      Sim_preserves_of_old hle' hpres hsim
    have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
      hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss
    have hsim' := Sim_step (Nat.le_refl B) hle' hok' hIok' hrf honceSh hssf
      (fun _ _ _ h => h) hpEnv hsim
    have henvNRF' := EnvNoReachForbid_step hsim.2.1 hle' (Sim_deps_lt hsim)
      hsim.2.2.2.1 (hstat ▸ ArrayExtends.refl _) (hstr ▸ ArrayExtends.refl _) hpSS hpEnv henvNRF
    have hnotOnce : ¬ IsOnceSrc σ' { cls := c } := by rintro ⟨_, hs, _⟩; cases hs
    refine ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres,
      hpres.mono fun _ hf => hFrameLt _ hf, honceSh, hssf, hst', hsim', henvNRF', ?_, ?_, ?_, ?_, hreach'⟩
    · refine ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ hs => by cases hs),
        fun _ his => absurd his hnotOnce, fun _ => ?_⟩
      exact ⟨hbase', hdou', hcf',
        fun _ hne => ClsSafe.to_nonValSafe hne hcls' hbase'.1.self.1,
        fun _ => ⟨hno', fun _ h => h, hfun'⟩,
        (fun h => by cases h),
        fun his => absurd his hnotOnce,
        (fun htr => by cases htr.2.1)⟩
    · intro j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
      have hvB₂ := ((hsim.2.2.2.2.2.1 j b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
      have hsrcB : ∀ x, (effVal ab₂).src = some x → x < σ.st.size := fun x hx => (hvB₂.2.2.1 x hx).1
      refine ⟨(fun _ htr => by cases htr.2.1),
        fun haB _ _ _ l hor hrR => ?_,
        fun _ _ _ _ _ h => False.elim h,
        fun haB hfB _ _ l hft hrR => ?_,
        (fun _ _ hs => by cases hs),
        (fun hs => by cases hs),
        (fun _ hs => by cases hs)⟩
      · have haB1 := ActiveVal.of_AStateLe hsim.2.1 hle' hvB₂.2.1 hsrcB haB
        have hpB := hpEnv j b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ haB
        have hor1 := (OwnReach_congr hpB l).mp hor
        exact Nat.not_lt_of_ge (hreach' l hrR) ((hvB₂.2.2.2.2 haB1).1.1.reach_lt_size (OwnReach_toReach hor1))
      · have haB1 := ActiveVal.of_AStateLe hsim.2.1 hle' hvB₂.2.1 hsrcB haB
        have hfB1 := FootActive.of_AStateLe hsim.2.1 hle' hvB₂.2.1 hsrcB hfB
        have hftR : Reach st.heap b₂.val l := by
          rcases hfB1 with hoO | ⟨hisB, _⟩
          · exact ((hvB₂.2.2.2.2 haB1).2.2.2.2.2.1 hoO).1 l hft |>.1
          · exact ((hvB₂.2.2.2.2 haB1).2.2.2.2.2.2.1 hisB).1 l hft |>.1
        exact Nat.not_lt_of_ge (hreach' l hrR) ((hvB₂.2.2.2.2 haB1).1.1.reach_lt_size hftR)
    · intro _ _ _ l hr _ _ hF
      exact Nat.not_lt_of_ge (hreach' l hr) (hForbidLt l hF)
    · intro _ hneC
      exact ⟨hbase', ClsSafe.to_nonValSafe hneC hcls' hbase'.1.self.1⟩

/-! ## 3. Bridge 5 (`bindParamsM_checked_sound`) & Bridge 6 (`bindInner_bridge`) -/

/-- Strengthened `.once` footprint helper for `bindAt`: exposes `¬ NumLoc st'.heap l` on `resFoot`
and `¬ NumLoc` / non-`Forbid` for `c ≠ .val` as well. -/
theorem bindAt_once_foot {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {fuel s : Nat} {m : BinderMode} {c : Cls} {sk : Skel}
    {onceOnly : Bool} {Foot : Nat → Prop} {v : Val}
    (hst : StOk P ext B st)
    (hu : m.usage = .once)
    (hbase : ValBaseOk st v)
    (hfun : FunOkAt P ext B st sk onceOnly Foot v)
    (hFootFalse : onceOnly = false → ∀ l, ¬ Foot l)
    (hFootOk : ∀ l, Foot l → Reach st.heap v l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l)
    {bnd : Bnd} {st' : St}
    (hrun : (bindAt P fuel s m c v).run st = .ok (bnd, st')) :
    SpentOnceSafe st'.heap bnd.val ∧
    (c ≠ .val → ∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ NumLoc st'.heap l) ∧
    ∃ loc resFoot, st.heap.objs.size ≤ loc ∧
      (∀ l, resFoot l → l = loc ∨ Foot l) ∧
      (∀ l, resFoot l → Reach st'.heap bnd.val l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
      FunOkAt P ext B st' sk true resFoot bnd.val := by
  have her : m ≠ .erased := by intro h; subst h; cases hu
  have hnotU : m.isUnique = false := by cases m <;> simp [BinderMode.usage, BinderMode.isUnique] at hu ⊢
  rcases bindAt_spec (P := P) (fuel := fuel) (s := s) (m := m) (c := c) (v := v) hst.1
      (fun _ => hbase.1) (fun _ => hbase.2.1) (fun h => by rw [hnotU] at h; cases h)
      (fun h => by rw [hnotU] at h; cases h) with hSt | hOOF |
    ⟨bnd1, st1, hrun1, _, hr, hnr, hstat, hstr, hsz, _, _, hoss, hpres,
      _, _, _, _, _, honce', _, _, _, _, _⟩
  · rw [hSt] at hrun; cases hrun
  · rw [hOOF] at hrun; cases hrun
  · have hEq := Except.ok.inj (hrun1.symm.trans hrun)
    cases congrArg Prod.fst hEq; cases congrArg Prod.snd hEq
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres.mono fun l hlt => ⟨hlt, fun h => by rw [hnotU] at h; cases h⟩
    have hssBack : ∀ l, StaticStrLoc st' l → StaticStrLoc st l :=
      StaticStrLoc_of_preserves_outside hstat hstr
        (hpresOld.mono fun _ hss => StOk_staticStrLoc_lt hst hss)
    obtain ⟨base, loc, cap, hbv, _, hge, ho, hdlBase, hclsBase, _, _⟩ := honce' hu
    have hlocNotSS : ¬ StaticStrLoc st' loc := fun hss =>
      Nat.not_lt_of_ge hge (StOk_staticStrLoc_lt hst (hssBack loc hss))
    have hlocNotNum : ¬ NumLoc st'.heap loc := by
      rintro ⟨o', n', ho', hn'⟩; rw [ho] at ho'; cases ho'; cases hn'
    have hneValReach : c ≠ .val → ∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ NumLoc st'.heap l := by
      intro hcv l hrB
      rw [hbv] at hrB
      cases hrB with
      | here => exact Or.inl hge
      | step ho1 hm1 hr2 =>
        rw [ho] at ho1; cases ho1
        simp only [Cell.vals, List.mem_singleton] at hm1; cases hm1
        have hnv : NonValSafe st'.heap base :=
          ClsSafe.to_nonValSafe hcv (ClsSafe.of_clsOk hclsBase) hdlBase.self.1
        exact Or.inr (hnv.reach_numLoc hr2)
    refine ⟨by rw [hbv]; exact SpentOnceSafe.of_once ho rfl rfl, hneValReach, ?_⟩
    by_cases hcv : c = .val
    · subst hcv
      obtain ⟨base0, st0, hrun0, hloc0, _, _, hst0⟩ :=
        bindAt_once_val_sameLoc (P := P) (fuel := fuel) (s := s) hu hbase.1
      have hEq0 := Except.ok.inj (hrun0.symm.trans hrun)
      have hbvEq : bnd.val = .ref st.heap.objs.size st.heap.nextCap base0.taint :=
        congrArg Bnd.val (congrArg Prod.fst hEq0).symm
      have hstEq : st' = { st with heap := { objs := st.heap.objs.push ⟨.once base0 false, st.heap.nextCap⟩,
                                             nextCap := st.heap.nextCap + 1 } } :=
        (congrArg Prod.snd hEq0).symm.trans hst0
      have hoN : st'.heap.objs[st.heap.objs.size]? = some ⟨.once base0 false, st.heap.nextCap⟩ := by
        rw [hstEq]; simp
      have hlocEq : loc = st.heap.objs.size := by
        rw [hbvEq] at hbv
        exact (congrArg (fun | .ref l _ _ => l | _ => 0) hbv).symm
      refine ⟨st.heap.objs.size, fun l => l = st.heap.objs.size ∨ Foot l, Nat.le_refl _,
        fun _ h => h, ?_, ?_⟩
      · intro l hl
        rcases hl with rfl | hft
        · exact ⟨by rw [hbvEq]; exact .here, hlocEq ▸ hlocNotSS, hlocEq ▸ hlocNotNum⟩
        · obtain ⟨hrV, hnotSS, hnotNum⟩ := hFootOk l hft
          have hrB0 : Reach st.heap base0 l := Reach_of_sameShapeOn (SameShapeOn.refl _ _) hloc0 hrV
          have hrB : Reach st'.heap base0 l :=
            Reach_of_sameShapeOn (hoss.to_sameShapeOn _) (SameLoc.refl _) hrB0
          have hmem0 : base0 ∈ (Obj.mk (.once base0 false) st.heap.nextCap).cell.vals :=
            List.mem_singleton_self _
          have hpV : PreservesLocs (Reach st.heap v) st.heap st'.heap :=
            hpresOld.mono fun _ h => hbase.1.reach_lt_size h
          exact ⟨by rw [hbvEq]; exact .step hoN hmem0 hrB,
            fun hss => hnotSS (hssBack l hss),
            fun hnum => hnotNum ((NumLoc_congr hpV hrV).mpr hnum)⟩
      · have hfBase : FunOkAt P ext B st' sk true Foot base0 := by
          cases onceOnly with
          | true => exact FunOkAt_preserve_sameShape hloc0 (hoss.to_sameShapeOn _) hrf hfun
          | false =>
            have hfF : FunOkAt P ext B st sk false (fun _ => False) v :=
              FunOkAt_weaken_foot (fun l hl => False.elim (hFootFalse rfl l hl)) hfun
            exact FunOkAt_weaken_foot (fun _ h => False.elim h)
              (FunOkAt_weaken_onceOnly (FunOkAt_preserve_sameShape hloc0 (hoss.to_sameShapeOn _) hrf hfF))
        rw [hbvEq]
        exact FunOkAt_once_wrap hoN rfl hfBase
    · refine ⟨loc, fun l => l = loc, hge, fun _ h => Or.inl h, ?_, ?_⟩
      · intro l hl; subst hl
        exact ⟨by rw [hbv]; exact .here, hlocNotSS, hlocNotNum⟩
      · rw [hbv]
        have hfBase : FunOkAt P ext B st' sk false (fun _ => False) base :=
          ClsSafe_funOkAt P ext B st' sk hcv (ClsSafe.of_clsOk hclsBase)
        exact FunOkAt_once_wrap_plain ho rfl hfBase

/-- Push a `.once`-usage binding `(b, bv)` onto `env`/`aenv` in `Sim` without requiring `NoOnceCell`
on the newly allocated `.once` cell `b.val`. -/
theorem Sim_push_once_bnd {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {bFoot : Nat → Prop}
    {b : Bnd} {bv : AVal}
    (hu : b.mode.usage = .once)
    (hregs : ∀ r ∈ bv.regs, r < σ.nextRegion)
    (hdeps : ∀ d ∈ bv.deps, d < σ.st.size)
    (hsp : SpentOnceSafe st.heap b.val)
    (hbase : ValBaseOk st b.val)
    (hdou : DeepOpenUnder st.heap st.regions (I.regsOf bv.regs) b.val)
    (hcf : CtorFieldsOk P ext B st b.val)
    (hfoot : ∀ l, bFoot l → Reach st.heap b.val l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l)
    (hfun : FunOkAt P ext B st bv.skel true bFoot b.val)
    (hfootEnv : ∀ i b₂ ab₂, Scope i → env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
      ActiveVal σ (effVal ab₂) → ∀ l, bFoot l → ¬ Reach st.heap b₂.val l)
    (henvDisj : ∀ i b₁ ab₁, Scope i → env[i]? = some b₁ → aenv[i]? = some ab₁ → ab₁.mode ≠ .erased →
      (ActiveVal σ (effVal ab₁) → Transferable σ NoKill (effVal ab₁) → ValidDeps σ bv.deps →
        (∀ d, d ∈ (effVal ab₁).deps → ¬ (d ∈ bv.deps)) →
        ∀ l, OwnReach P st.heap b₁.val l → ¬ Reach st.heap b.val l) ∧
      (ActiveVal σ (effVal ab₁) → FootActive σ (effVal ab₁) → ValidDeps σ bv.deps →
        ∀ l, envFoot i l → ¬ Reach st.heap b.val l))
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    let res := σ.pushBnd bv true
    let ab : ABnd := { id := res.1, mode := b.mode, val := bv }
    let Scope' : Nat → Prop := fun i => match i with | 0 => True | k + 1 => Scope k
    let envFoot' : Nat → Nat → Prop := fun i => match i with | 0 => bFoot | k + 1 => envFoot k
    Sim P ext B st Frame NoKill NoSpend Scope' (b :: env) (ab :: aenv) res.2 I envFoot' := by
  intro res ab Scope' envFoot'
  have hok₁ := hsim.2.1
  have hle : AStateLe σ res.2 := (hok₁.pushBnd bv true).2
  have hok₂ : AStateOk res.2 := (hok₁.pushBnd bv true).1
  have hIok₂ : InterpOk res.2 st I := hsim.2.2.1
  have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂ (RegsFuture.refl st)
    (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
    (PreservesActiveEnv.refl _ _ _ _ _) hsim
  have honceNew : res.2.once[ab.id]? = some true := by
    dsimp [res, ab, AState.pushBnd]; rw [hok₁.1, Array.getElem?_push_size]
  have hisNew : IsOnceSrc res.2 (effVal ab) := ⟨ab.id, rfl, honceNew⟩
  have hmemDeps : ∀ d, d ∈ (effVal ab).deps ↔ d = ab.id ∨ (d ∈ bv.deps ∧ d ≠ ab.id) := fun d => by
    simp only [effVal, List.mem_cons, List.mem_filter, bne_iff_ne]; rfl
  have hValidOld : ValidDeps res.2 (effVal ab).deps → ValidDeps σ bv.deps := fun hv2 d hd =>
    ValidDeps.of_AStateLe hle hdeps
      (fun x hx => hv2 x ((hmemDeps x).mpr (Or.inr ⟨hx, Nat.ne_of_lt (hdeps x hx)⟩))) d hd
  have hnotCtor : ∀ loc cap t o r fs, b.val = .ref loc cap t → st.heap.objs[loc]? = some o →
      o.cell = .ctor r fs → ∀ l, ¬ bFoot l := by
    intro loc cap t o r fs hbEq ho hc _ _
    rcases hsp with h | ⟨_, _, _, o', _, _, hEq, ho', _, hc'⟩
    · rw [h] at hbEq; cases hbEq
    · rw [hEq] at hbEq; cases hbEq; rw [ho] at ho'; cases ho'; rw [hc] at hc'; cases hc'
  have hVSimNew : VSim P ext B st Frame NoKill NoSpend res.2 I bFoot (effVal ab) b.val := by
    refine ⟨hregs, ?_, ?_, fun _ _ => hsp, fun _ => ?_⟩
    · intro d hd
      rcases (hmemDeps d).mp hd with rfl | ⟨hd1, _⟩
      · dsimp [res, ab, AState.pushBnd]; simp
      · exact Nat.lt_of_lt_of_le (hdeps d hd1) hle.1
    · intro x hx; dsimp [effVal] at hx; cases hx
      exact ⟨by dsimp [res, ab, AState.pushBnd]; simp, List.mem_cons_self ..⟩
    · exact ⟨hbase, hdou, hcf,
        fun hno => absurd hisNew hno,
        fun ⟨hno, _⟩ => absurd hisNew hno,
        fun _ => ⟨fun l hl => ⟨(hfoot l hl).1, (hfoot l hl).2.2.1, (hfoot l hl).2.2.2⟩,
          fun _ l hl => (hfoot l hl).2.1, hnotCtor, hfun⟩,
        fun _ => ⟨fun l hl => ⟨(hfoot l hl).1, (hfoot l hl).2.2.1, (hfoot l hl).2.2.2⟩,
          fun _ l hl => (hfoot l hl).2.1, hfun⟩,
        fun htr => absurd hisNew htr.2.2.2.1⟩
  obtain ⟨hlen, _, _, hids, huniqId, hbnds, hdisj⟩ := hsim₂
  refine ⟨by simp [hlen], hok₂, hIok₂, ?_, ?_, ?_, ?_⟩
  · intro i ab' hab'
    cases i with
    | zero => simp at hab'; subst hab'; dsimp [res, ab, AState.pushBnd]; simp
    | succ k => exact hids k ab' (by simpa using hab')
  · intro i j ab₁ ab₂ hab₁ hab₂ heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ k =>
        simp at hab₁ hab₂; subst hab₁
        have hlt := hsim.2.2.2.1 k ab₂ hab₂
        dsimp [ab, res, AState.pushBnd] at heq; omega
    | succ k =>
      cases j with
      | zero =>
        simp at hab₁ hab₂; subst hab₂
        have hlt := hsim.2.2.2.1 k ab₁ hab₁
        dsimp [ab, res, AState.pushBnd] at heq; omega
      | succ m =>
        exact congrArg Nat.succ (huniqId k m ab₁ ab₂ (by simpa using hab₁) (by simpa using hab₂) heq)
  · intro i b' ab' hsc hbi habi
    cases i with
    | zero =>
      simp at hbi habi; subst hbi; subst habi
      refine ⟨rfl, fun _ => ⟨?_, hVSimNew⟩⟩
      have hbu : (b.mode.usage == .once) = true := by simp [hu]
      rw [hbu]; exact honceNew
    | succ k => exact hbnds k b' ab' hsc (by simpa using hbi) (by simpa using habi)
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ m =>
        simp at hb₁ hab₁; subst hb₁; subst hab₁
        have hb₂' : env[m]? = some b₂ := by simpa using hb₂
        have hab₂' : aenv[m]? = some ab₂ := by simpa using hab₂
        have hv₂ := ((hsim.2.2.2.2.2.1 m b₂ ab₂ hsj hb₂' hab₂').2 hne₂).2
        have hsrc₂ : ∀ x, (effVal ab₂).src = some x → x < σ.st.size := fun x hx => (hv₂.2.2.1 x hx).1
        refine ⟨fun _ htr => absurd hisNew htr.2.2.2.1, fun _ _ ha₂₂ l hft hr₂ => ?_⟩
        exact hfootEnv m b₂ ab₂ hsj hb₂' hab₂' hne₂
          (ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc₂ ha₂₂) l hft hr₂
    | succ k =>
      cases j with
      | zero =>
        simp at hb₂ hab₂; subst hb₂; subst hab₂
        have hb₁' : env[k]? = some b₁ := by simpa using hb₁
        have hab₁' : aenv[k]? = some ab₁ := by simpa using hab₁
        have hv₁ := ((hsim.2.2.2.2.2.1 k b₁ ab₁ hsi hb₁' hab₁').2 hne₁).2
        have hsrc₁ : ∀ x, (effVal ab₁).src = some x → x < σ.st.size := fun x hx => (hv₁.2.2.1 x hx).1
        obtain ⟨hd1, hd2⟩ := henvDisj k b₁ ab₁ hsi hb₁' hab₁' hne₁
        refine ⟨fun ha₁₂ htr₁₂ ha₂₂ hdd l hor hr₂ => ?_, fun ha₁₂ hf₁₂ ha₂₂ l hft hr₂ => ?_⟩
        · have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ ha₁₂
          have htr₁₁ := Transferable.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ (fun _ h => h) htr₁₂
          have hdd' : ∀ d, d ∈ (effVal ab₁).deps → ¬ (d ∈ bv.deps) := fun d hd1 hd2 =>
            hdd d hd1 ((hmemDeps d).mpr (Or.inr ⟨hd2, Nat.ne_of_lt (hdeps d hd2)⟩))
          exact hd1 ha₁₁ htr₁₁ (hValidOld ha₂₂.1) hdd' l hor hr₂
        · have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ ha₁₂
          have hf₁₁ := FootActive.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ hf₁₂
          exact hd2 ha₁₁ hf₁₁ (hValidOld ha₂₂.1) l hft hr₂
      | succ m =>
        exact hdisj k m b₁ b₂ ab₁ ab₂ (fun h => hij (congrArg Nat.succ h)) hsi hsj
          (by simpa using hb₁) (by simpa using hab₁) (by simpa using hb₂) (by simpa using hab₂) hne₁ hne₂

/-- Helper: one step of `initBody`'s fold over parameters. -/
private def initBodyStep (acc : List ABnd × AState) (p : Param) : List ABnd × AState :=
  let v := paramVal p 2
  let (id, σ') := acc.2.pushBnd v (p.mode.usage == .once)
  ({ id, mode := p.mode, val := v } :: acc.1, σ')

/-- Generalized induction for `bindParamsM_checked_sound` over a list of parameter-value items. -/
private theorem bindParamsM_loop_checked_sound {P : Prog} {ext : ExternOracle} {B fuel s : Nat}
    {Frame Forbid : Nat → Prop} {argRegs : List Nat}
    (items : List (Param × Val × Bool × (Nat → Prop))) :
    ∀ (env : List Bnd) (aenv : List ABnd) (σ : AState) (envFoot : Nat → Nat → Prop) (st : St),
      let I : Interp := ⟨fun r => if r == 2 then [s] else argRegs.filter (· < s)⟩
      StOk P ext B st →
      s < st.nextRegion →
      st.regions.head? = some s →
      (σ.regions = [2, 1] ∧ σ.nextRegion = 3) →
      (∀ l, Frame l → l < st.heap.objs.size) →
      (∀ l, Forbid l → l < st.heap.objs.size) →
      (∀ (i : Nat) ab, aenv[i]? = some ab → ab.val.onceOnly = false) →
      (∀ (i : Nat) ab, aenv[i]? = some ab → ab.mode ≠ .erased → ActiveVal σ (effVal ab)) →
      (∀ (i : Nat) b ab, env[i]? = some b → aenv[i]? = some ab → ab.mode = .erased → b.val = .imm .irr) →
      Sim P ext B st Frame (fun _ => False) (fun _ => False) (fun _ => True) env aenv σ I envFoot →
      EnvNoReachForbid st (fun _ => True) env aenv σ Forbid (· = 2) (fun _ => False) →
      (∀ it ∈ items,
        let (p, v, aOnce, aFoot) := it
        p.mode ≠ .erased →
          ValBaseOk st v ∧
          DeepOpenUnder st.heap st.regions (argRegs.filter (· < s)) v ∧
          CtorFieldsOk P ext B st v ∧
          (p.mode.usage = .once →
            FunOkAt P ext B st p.skel aOnce aFoot v ∧
            (aOnce = false → ∀ l, ¬ aFoot l) ∧
            (∀ l, aFoot l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l) ∧
            (∀ (i : Nat) b ab, env[i]? = some b → aenv[i]? = some ab → ab.mode ≠ .erased →
              ∀ l, aFoot l → ¬ Reach st.heap b.val l)) ∧
          (p.mode.usage ≠ .once →
            NoOnceCell st.heap v ∧ FunOkAt P ext B st p.skel false (fun _ => False) v) ∧
          (p.mode.isUnique = true →
            OwnTreeFull P st.heap v ∧
            (∀ l, OwnReach P st.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st l) ∧
            (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v) ∧
            (∀ (i : Nat) b ab, env[i]? = some b → aenv[i]? = some ab → ab.mode ≠ .erased →
              ∀ l, OwnReach P st.heap v l → ¬ Reach st.heap b.val l)) ∧
          (∀ (i : Nat) b ab, env[i]? = some b → aenv[i]? = some ab → ab.mode ≠ .erased →
            (ab.val.own = .uniq → ab.val.cls = .val → ab.mode.usage ≠ .once →
              ∀ l, OwnReach P st.heap b.val l → ¬ Reach st.heap v l) ∧
            (ab.mode.usage = .once → ∀ l, envFoot i l → ¬ Reach st.heap v l)) ∧
          (p.mode.isBorrowed = false → ∀ l, Reach st.heap v l → ¬ StaticStrLoc st l → ¬ NumLoc st.heap l → ¬ Forbid l)) →
      (∀ (i j : Nat) (it₁ it₂ : Param × Val × Bool × (Nat → Prop)), i ≠ j →
        items[i]? = some it₁ → items[j]? = some it₂ →
        it₁.1.mode ≠ .erased → it₂.1.mode ≠ .erased →
        (it₁.1.mode.isUnique = true → ∀ l, OwnReach P st.heap it₁.2.1 l → ¬ Reach st.heap it₂.2.1 l) ∧
        (it₁.1.mode.usage = .once → ∀ l, it₁.2.2.2 l → ¬ Reach st.heap it₂.2.1 l)) →
      let pvs := items.map fun it => (it.1, it.2.1)
      let resA := (items.map (·.1)).foldl initBodyStep (aenv, σ)
      (bindParamsM P fuel s pvs env).run st = .error .stuck ∨
      (bindParamsM P fuel s pvs env).run st = .error .outOfFuel ∨
      ∃ env' st', (bindParamsM P fuel s pvs env).run st = .ok (env', st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesLocs (StaticStrLoc st) st.heap st'.heap ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        StOk P ext B st' ∧
        (∃ envFoot',
          Sim P ext B st' Frame (fun _ => False) (fun _ => False) (fun _ => True) env' resA.1 resA.2 I envFoot') ∧
        EnvNoReachForbid st' (fun _ => True) env' resA.1 resA.2 Forbid (· = 2) (fun _ => False) ∧
        (∀ b ∈ env', ∀ l, Reach st'.heap b.val l →
          st.heap.objs.size ≤ l ∨ (∃ b0 ∈ env, Reach st.heap b0.val l) ∨
          ∃ it ∈ items, it.1.mode ≠ .erased ∧ Reach st.heap it.2.1 l) := by
  induction items with
  | nil =>
    intro env aenv σ envFoot st I hst _ _ _ _ _ _ _ _ hsim henvNRF _ _
    right; right
    refine ⟨env, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, PreservesLocs.refl _ _, PreservesOnceShell.refl _,
      StaticStrFresh.refl _, hst, ⟨envFoot, hsim⟩, henvNRF,
      fun b hb l hr => Or.inr (Or.inl ⟨b, hb, hr⟩)⟩
  | cons hd rest ih =>
    rcases hd with ⟨p, v, aOnce, aFoot⟩
    intro env aenv σ envFoot st I hst hs hregsSt hσReg hFrameLt hForbidLt hnoOO hAllAct hErIrr hsim henvNRF hitems hpair
    have hhd := hitems (p, v, aOnce, aFoot) List.mem_cons_self
    dsimp only at hhd
    have hUnfold : (bindParamsM P fuel s ((p, v) :: rest.map fun it => (it.1, it.2.1)) env).run st =
        (match (bindAt P fuel s p.mode p.cls v).run st with
         | .error e => .error e
         | .ok (b, st₁) => (bindParamsM P fuel s (rest.map fun it => (it.1, it.2.1)) (b :: env)).run st₁) := by
      conv => lhs; unfold bindParamsM
      rw [M_bind_run]
      cases (bindAt P fuel s p.mode p.cls v).run st with
      | error _ => rfl
      | ok q => rcases q with ⟨_, _⟩; rfl
    dsimp only [List.map]
    rw [hUnfold]
    have hbindOnce : p.mode.usage ≠ .once → (if p.mode.usage == .once then aOnce else false) = false := by
      intro h; simp [h]
    have hbindFootFalse : (if p.mode.usage == .once then aOnce else false) = false →
        ∀ l, ¬ (if p.mode.usage == .once then aFoot l else False) := by
      intro h l hl
      by_cases hu : p.mode.usage = .once
      · simp only [hu, beq_self_eq_true, ↓reduceIte] at h hl
        exact (hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.1 hu |>.2.1 h l hl
      · simp [hu] at hl
    rcases bindAt_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s)
        (m := p.mode) (c := p.cls) (sk := p.skel)
        (onceOnly := if p.mode.usage == .once then aOnce else false)
        (Foot := fun l => if p.mode.usage == .once then aFoot l else False)
        (v := v) hst hs
        (fun hne => (hhd hne).1)
        (fun hne => (hhd hne).2.2.1)
        (fun hne hnu => ((hhd hne).2.2.2.2.1 hnu).1)
        (fun hne => by
          by_cases hu : p.mode.usage = .once
          · simp only [hu, beq_self_eq_true, ↓reduceIte]; exact ((hhd hne).2.2.2.1 hu).1
          · have hb : (p.mode.usage == .once) = false := by
              cases hm : p.mode <;> simp [hm, BinderMode.usage] at hu ⊢
            simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact ((hhd hne).2.2.2.2.1 hu).2)
        hbindOnce hbindFootFalse
        (fun hu l hl => by
          simp only [hu, beq_self_eq_true, ↓reduceIte] at hl
          have h := ((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.1 hu).2.2.1 l hl
          exact ⟨h.1, h.2.2.1⟩)
        (fun hu => ((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).1)
        (fun hu l hl => (((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).2.1 l hl).2)
        (fun hu hnb => by
          have hdou := ((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).2.2.1 hnb
          exact hdou v (HeldBy.refl _ _)) with hSt | hOOF |
      ⟨bnd, st₁, hrun₁, hmode₁, hr₁, hnr₁, hstat₁, hstr₁, hsz₁, hcap₁, _, hpres₁, honceSh₁, hssf₁,
        hst₁, hbase₁, hcf₁, her₁, hplain₁, _, htree₁, _, hdou₁, hreach₁, hown₁⟩
    · exact Or.inl (by rw [hSt])
    · exact Or.inr (Or.inl (by rw [hOOF]))
    · rw [hrun₁]; dsimp only
      have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions (hnr₁ ▸ Nat.le_refl _) hr₁
      have hIok₁ : InterpOk σ st₁ I :=
        ⟨fun r hr' c' hc' => hnr₁ ▸ hsim.2.2.1.1 r hr' c' hc',
         fun c' hc' => hsim.2.2.1.2 c' (hr₁ ▸ hc')⟩
      have hpFrame₁ : PreservesLocs Frame st.heap st₁.heap :=
        hpres₁.mono fun l hl => ⟨hFrameLt l hl, fun hu hor =>
          (((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).2.1 l hor).1 hl⟩
      have hpSS₁ : PreservesLocs (StaticStrLoc st) st.heap st₁.heap :=
        hpres₁.mono fun l hss => ⟨StOk_staticStrLoc_lt hst hss, fun hu hor =>
          (((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).2.1 l hor).2 hss⟩
      have hpEnv₁ : PreservesActiveEnv (fun _ => True) env aenv σ st.heap st₁.heap := by
        intro i b₀ ab₀ _ hbi₀ habi₀ hne₀ ha₀
        have hv₀ := ((hsim.2.2.2.2.2.1 i b₀ ab₀ trivial hbi₀ habi₀).2 hne₀).2
        refine hpres₁.mono fun l hrl => ⟨(hv₀.2.2.2.2 ha₀).1.1.reach_lt_size hrl, fun hu hor => ?_⟩
        exact ((hhd (by intro he; rw [he] at hu; cases hu)).2.2.2.2.2.1 hu).2.2.2 i b₀ ab₀ hbi₀ habi₀ hne₀ l hor hrl
      have hsim₁ := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok₁ hrf₁ honceSh₁ hssf₁
        (fun _ _ _ h => h) hpEnv₁ hsim
      have henvNRF₁ := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim)
        hsim.2.2.2.1 (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _) hpSS₁ hpEnv₁ henvNRF
      let acc₁ := initBodyStep (aenv, σ) p
      have hσReg₁ : acc₁.2.regions = [2, 1] ∧ acc₁.2.nextRegion = 3 := hσReg
      have hnoOO₁ : ∀ (i : Nat) ab, acc₁.1[i]? = some ab → ab.val.onceOnly = false := by
        intro i ab hab
        cases i with
        | zero =>
          dsimp only [acc₁, initBodyStep] at hab; simp at hab; subst hab
          dsimp only [paramVal]; cases p.mode <;> rfl
        | succ k => exact hnoOO k ab (by simpa [acc₁, initBodyStep] using hab)
      have hAllAct₁ : ∀ (i : Nat) ab, acc₁.1[i]? = some ab → ab.mode ≠ .erased → ActiveVal acc₁.2 (effVal ab) := by
        intro i ab hab hneAb
        cases i with
        | zero =>
          dsimp only [acc₁, initBodyStep, AState.pushBnd] at hab; simp at hab; subst hab
          have hdepsNil : (paramVal p 2).deps = [] := by dsimp only [paramVal]; cases p.mode <;> rfl
          have heffDeps : (effVal { id := σ.st.size, mode := p.mode, val := paramVal p 2 }).deps = [σ.st.size] := by
            simp [effVal, hdepsNil]
          refine ⟨fun d hd => ?_, fun _ d hd _ => ?_⟩
          · rw [heffDeps, List.mem_singleton] at hd; subst hd
            dsimp only [acc₁, initBodyStep, AState.pushBnd]
            refine ⟨by simp, ?_⟩
            rw [Array.getElem?_push_size]
            cases (paramVal p 2).own <;> decide
          · rw [heffDeps, List.mem_singleton] at hd; subst hd
            dsimp only [acc₁, initBodyStep, AState.pushBnd]
            rw [hsim.2.1.2.1, Array.getElem?_push_size]
        | succ k =>
          have habK : aenv[k]? = some ab := by simpa [acc₁, initBodyStep] using hab
          have ha0 := hAllAct k ab habK hneAb
          refine ⟨fun d hd => ?_, fun his1 d hd ho1 => ?_⟩
          · have ⟨hlt, hnd⟩ := ha0.1 d hd
            dsimp only [acc₁, initBodyStep, AState.pushBnd]
            rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
            exact ⟨(by simp; omega), hnd⟩
          · have ⟨hlt, _⟩ := ha0.1 d hd
            have hltO : d < σ.once.size := by rw [← hsim.2.1.1]; exact hlt
            have hltS : d < σ.spent.size := by rw [← hsim.2.1.2.1]; exact hlt
            dsimp only [acc₁, initBodyStep, AState.pushBnd] at ho1 ⊢
            rw [Array.getElem?_push_lt hltO, ← Array.getElem?_eq_getElem hltO] at ho1
            rw [Array.getElem?_push_lt hltS, ← Array.getElem?_eq_getElem hltS]
            have his0 : IsOnceSrc σ (effVal ab) := by
              obtain ⟨id, hsrc, ho'⟩ := his1
              dsimp only [effVal] at hsrc; cases hsrc
              have hidLt : ab.id < σ.once.size := by rw [← hsim.2.1.1]; exact hsim.2.2.2.1 k ab habK
              dsimp only [acc₁, initBodyStep, AState.pushBnd] at ho'
              rw [Array.getElem?_push_lt hidLt, ← Array.getElem?_eq_getElem hidLt] at ho'
              exact ⟨ab.id, rfl, ho'⟩
            exact ha0.2 his0 d hd ho1
      have hPush :
          (∃ envFoot₁,
            Sim P ext B st₁ Frame (fun _ => False) (fun _ => False) (fun _ => True) (bnd :: env) acc₁.1 acc₁.2 I envFoot₁ ∧
            (∀ k l, envFoot₁ (k + 1) l ↔ envFoot k l) ∧
            (p.mode.usage = .once → ∀ l, envFoot₁ 0 l → st.heap.objs.size ≤ l ∨ aFoot l)) ∧
          EnvNoReachForbid st₁ (fun _ => True) (bnd :: env) acc₁.1 acc₁.2 Forbid (· = 2) (fun _ => False) := by
        by_cases hpEr : p.mode = .erased
        · obtain ⟨hbEq, hstEq⟩ := her₁ hpEr
          have habEq : acc₁ = ({ id := σ.st.size, mode := .erased, val := { cls := .irr } } :: aenv,
              (σ.pushBnd { cls := .irr } false).2) := by
            dsimp only [acc₁, initBodyStep, paramVal]; rw [hpEr]; rfl
          have hsimP := Sim_push_erased hsim₁
          have hsimP' : Sim P ext B st₁ Frame (fun _ => False) (fun _ => False) (fun _ => True)
              (bnd :: env) acc₁.1 acc₁.2 I (fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k) := by
            rw [hbEq, habEq]
            exact Sim_weaken_scope (fun i _ => by cases i <;> trivial) hsimP
          refine ⟨⟨_, hsimP', fun _ _ => Iff.rfl, fun hu => by rw [hpEr] at hu; cases hu⟩, ?_⟩
          intro i b' ab' _ hbi' habi' hne' ha'
          cases i with
          | zero => rw [habEq] at habi'; simp at habi'; subst habi'; exact absurd rfl hne'
          | succ k =>
            rw [habEq] at habi'
            have hbiK : env[k]? = some b' := by simpa using hbi'
            have habiK : aenv[k]? = some ab' := by simpa using habi'
            have hleP : AStateLe σ (σ.pushBnd { cls := .irr } false).2 := (hsim.2.1.pushBnd _ false).2
            have hvK := ((hsim₁.2.2.2.2.2.1 k b' ab' trivial hbiK habiK).2 hne').2
            have hsrcK : ∀ x, (effVal ab').src = some x → x < σ.st.size := fun x hx => (hvK.2.2.1 x hx).1
            exact henvNRF₁ k b' ab' trivial hbiK habiK hne'
              (ActiveVal.of_AStateLe hsim.2.1 hleP hvK.2.1 hsrcK (by simpa [habEq] using ha'))
        · have hhdP := hhd hpEr
          let bv : AVal := paramVal p 2
          have hbvSrc : bv.src = none := by dsimp only [bv, paramVal]; cases p.mode <;> rfl
          have hbvOnceOnly : bv.onceOnly = false := by dsimp only [bv, paramVal]; cases p.mode <;> rfl
          have hbvDeps : bv.deps = [] := by dsimp only [bv, paramVal]; cases p.mode <;> rfl
          have hbvRegsLt : ∀ r ∈ bv.regs, r < σ.nextRegion := by
            intro r hr; rw [hσReg.2]
            dsimp only [bv, paramVal] at hr
            by_cases hc : (p.cls == .val) = true
            · simp only [hc, ↓reduceIte] at hr
              cases hm : p.mode <;> rw [hm] at hr <;>
                (simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                 first | done | (rcases hr with rfl | rfl <;> omega) | (subst hr; omega))
            · simp only [hc] at hr
              cases hm : p.mode <;> rw [hm] at hr <;> cases hr
          have hbvSkel : bv.skel = p.skel := by
            dsimp only [bv, paramVal]; cases hpM : p.mode with
            | erased => exact absurd hpM hpEr
            | unique | uniqueBorrowed | borrowed | onceBorrowed | many | once => rfl
          have hbvCls : bv.cls = p.cls := by
            dsimp only [bv, paramVal]; cases hpM : p.mode with
            | erased => exact absurd hpM hpEr
            | unique | uniqueBorrowed | borrowed | onceBorrowed | many | once => rfl
          have hbvOwn : bv.own = .uniq → p.mode.isUnique = true := by
            dsimp only [bv, paramVal]; cases hpM : p.mode with
            | erased => exact absurd hpM hpEr
            | unique | uniqueBorrowed => intro _; rfl
            | borrowed | onceBorrowed | many | once => intro h; cases h
          have hdouBnd : DeepOpenUnder st₁.heap st₁.regions (I.regsOf bv.regs) bnd.val := by
            by_cases hcV : p.cls = .val
            · cases hpM : p.mode with
              | erased => exact absurd hpM hpEr
              | unique =>
                have hregsEq : bv.regs = [] := by dsimp only [bv, paramVal]; rw [hpM]
                rw [hregsEq, Interp.regsOf_nil]
                have h0 := hdou₁ st₁.regions [] (fun _ =>
                  hr₁ ▸ (hhdP.2.2.2.2.2.1 (by rw [hpM]; rfl)).2.2.1 (by rw [hpM]; rfl))
                simpa [hpM, BinderMode.isBorrowed] using h0
              | uniqueBorrowed | borrowed | onceBorrowed =>
                have hregsEq : bv.regs = [2, 1] := by dsimp only [bv, paramVal]; rw [hpM, hcV]; rfl
                have hIregs : I.regsOf bv.regs = s :: argRegs.filter (· < s) := by
                  rw [hregsEq]; simp [Interp.regsOf, I]
                rw [hIregs]
                have h0 := hdou₁ st₁.regions (argRegs.filter (· < s)) (fun _ => hr₁ ▸ hhdP.2.1)
                simpa [hpM, BinderMode.isBorrowed] using h0
              | many | once =>
                have hregsEq : bv.regs = [1] := by dsimp only [bv, paramVal]; rw [hpM, hcV]; rfl
                have hIregs : I.regsOf bv.regs = argRegs.filter (· < s) := by
                  rw [hregsEq]; simp [Interp.regsOf, I]
                rw [hIregs]
                have h0 := hdou₁ st₁.regions (argRegs.filter (· < s)) (fun _ => hr₁ ▸ hhdP.2.1)
                simpa [hpM, BinderMode.isBorrowed] using h0
            · by_cases hu : p.mode.usage = .once
              · have hOnceSpec : ∃ base loc cap, bnd.val = .ref loc cap base.taint ∧
                    st₁.heap.objs[loc]? = some ⟨.once base false, cap⟩ ∧
                    DeepLive st₁.heap base ∧ ClsOk st₁.heap p.cls base := by
                  rcases bindAt_spec (P := P) (fuel := fuel) (s := s) (m := p.mode) (c := p.cls) (v := v)
                      hst.1 (fun _ => hhdP.1.1) (fun _ => hhdP.1.2.1)
                      (fun h => (hhdP.2.2.2.2.2.1 h).1)
                      (fun h hnb => (hhdP.2.2.2.2.2.1 h).2.2.1 hnb v (HeldBy.refl _ _)) with hS | hO |
                    ⟨b0, s0, hr0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho0, _, _, _, _, _⟩
                  · rw [hS] at hrun₁; cases hrun₁
                  · rw [hO] at hrun₁; cases hrun₁
                  · have hEq := Except.ok.inj (hr0.symm.trans hrun₁)
                    cases congrArg Prod.fst hEq; cases congrArg Prod.snd hEq
                    obtain ⟨base, loc, cap, hbvEq, _, _, ho, hdlB, hclsB, _, _⟩ := ho0 hu
                    exact ⟨base, loc, cap, hbvEq, ho, hdlB, hclsB⟩
                obtain ⟨base, loc, cap, hbvEq, ho, hdlB, hclsB⟩ := hOnceSpec
                have hnvB : NonValSafe st₁.heap base :=
                  ClsSafe.to_nonValSafe hcV (ClsSafe.of_clsOk hclsB) hdlB.self.1
                have hbtNil : base.taint = [] := by
                  rcases hnvB with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, _, _, _⟩ <;> rfl
                intro w hw r hrW _
                rw [hbvEq] at hw
                rcases hw with rfl | ⟨l0, o0, hr0, ho0, hm0⟩
                · rw [hbtNil] at hrW; cases hrW
                · cases hr0 with
                  | here =>
                    rw [ho] at ho0; cases ho0
                    simp only [Cell.vals, List.mem_singleton] at hm0; subst hm0
                    rw [hbtNil] at hrW; cases hrW
                  | step ho2 hm2 hr2 =>
                    rw [ho] at ho2; cases ho2
                    simp only [Cell.vals, List.mem_singleton] at hm2; subst hm2
                    rcases hnvB with ⟨_, rfl⟩ | ⟨_, _, o', _, rfl, ho', _, hn'⟩
                    · cases hr2
                    · cases hr2 with
                      | here => rw [ho'] at ho0; cases ho0; rw [hn'] at hm0; cases hm0
                      | step ho3 hm3 _ => rw [ho'] at ho3; cases ho3; rw [hn'] at hm3; cases hm3
              · exact (ClsSafe.to_nonValSafe hcV (hplain₁ hpEr hu).1 hbase₁.1.self.1).deepOpenUnder_nil
          have hEnvDisjBv : ∀ i b₂ ab₂, env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
              (ActiveVal σ (effVal ab₂) → Transferable σ (fun _ => False) (effVal ab₂) →
                ∀ l, OwnReach P st₁.heap b₂.val l → ¬ Reach st₁.heap bnd.val l) ∧
              (ActiveVal σ (effVal ab₂) → FootActive σ (effVal ab₂) →
                ∀ l, envFoot i l → ¬ Reach st₁.heap bnd.val l) := by
            intro i b₂ ab₂ hbi₂ habi₂ hne₂
            have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ trivial hbi₂ habi₂).2 hne₂).2
            refine ⟨fun haB htrB l horB hrV => ?_, fun haB hfB l hft hrV => ?_⟩
            · have hpB := hpEnv₁ i b₂ ab₂ trivial hbi₂ habi₂ hne₂ haB
              have horB0 : OwnReach P st.heap b₂.val l := (OwnReach_congr hpB l).mp horB
              rcases hreach₁ l hrV with hge | ⟨_, hrV0⟩
              · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 haB).1.1.reach_lt_size (OwnReach_toReach horB0))
              · have hnu₂ : ab₂.mode.usage ≠ .once := by
                  intro hu₂; apply htrB.2.2.2.1
                  have honce₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ trivial hbi₂ habi₂).2 hne₂).1
                  exact ⟨ab₂.id, rfl, by rw [honce₂]; simp [hu₂]⟩
                exact (hhdP.2.2.2.2.2.2.1 i b₂ ab₂ hbi₂ habi₂ hne₂).1 htrB.2.1 htrB.1 hnu₂ l horB0 hrV0
            · have hftR : Reach st.heap b₂.val l := by
                rcases hfB with hoO | ⟨hisB, _⟩
                · exact ((hv₂.2.2.2.2 haB).2.2.2.2.2.1 hoO).1 l hft |>.1
                · exact ((hv₂.2.2.2.2 haB).2.2.2.2.2.2.1 hisB).1 l hft |>.1
              rcases hreach₁ l hrV with hge | ⟨_, hrV0⟩
              · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 haB).1.1.reach_lt_size hftR)
              · rcases hfB with hoO | ⟨⟨id, hsrc, ho⟩, _⟩
                · have hF := hnoOO i ab₂ habi₂; dsimp [effVal] at hoO; rw [hF] at hoO; cases hoO
                · dsimp [effVal] at hsrc; cases hsrc
                  have honce₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ trivial hbi₂ habi₂).2 hne₂).1
                  rw [honce₂] at ho
                  have hu₂ : ab₂.mode.usage = .once := by simpa using Option.some.inj ho
                  exact (hhdP.2.2.2.2.2.2.1 i b₂ ab₂ hbi₂ habi₂ hne₂).2 hu₂ l hft hrV0
          have hNewNRF : NoReachForbid st₁ Forbid (· = 2) (fun _ => False)
              (effVal { id := σ.st.size, mode := p.mode, val := bv }) bnd.val := by
            intro hregs _ l hrB hnotSS₁ hnotNum₁ hF
            by_cases hbr : p.mode.isBorrowed = true
            · by_cases hcV : p.cls = .val
              · have h2in : 2 ∈ (effVal { id := σ.st.size, mode := p.mode, val := bv }).regs := by
                  change 2 ∈ (paramVal p 2).regs
                  unfold paramVal
                  have hcv' : (p.cls == .val) = true := by rw [hcV]; rfl
                  simp only [hcv', ↓reduceIte]
                  cases hm : p.mode <;> rw [hm] at hbr <;>
                    first | contradiction | (dsimp only; exact List.mem_cons_self)
                exact hregs 2 h2in rfl
              · by_cases hu : p.mode.usage = .once
                · obtain ⟨hfunO, haOnceF, haFootOk, _⟩ := hhdP.2.2.2.1 hu
                  obtain ⟨_, hneValR, _⟩ := bindAt_once_foot hst hu hhdP.1 hfunO haOnceF
                    (fun l hl => let h := haFootOk l hl; ⟨h.1, h.2.2.1, h.2.2.2⟩) hrun₁
                  rcases hneValR hcV l hrB with hge | hnum
                  · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
                  · exact hnotNum₁ hnum
                · have hnv := ClsSafe.to_nonValSafe hcV (hplain₁ hpEr hu).1 hbase₁.1.self.1
                  exact hnotNum₁ (hnv.reach_numLoc hrB)
            · have hnb : p.mode.isBorrowed = false := Bool.eq_false_iff.mpr hbr
              rcases hreach₁ l hrB with hge | ⟨_, hr0⟩
              · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
              · have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
                  hnotSS₁ (StaticStrLoc_mono (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _) hpSS₁ hss0)
                have hnotNum0 : ¬ NumLoc st.heap l := fun hnum0 => by
                  obtain ⟨o, n, ho, hcell⟩ := hnum0
                  have hlt : l < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
                  have hnotOwn : p.mode.isUnique = true → ¬ OwnReach P st.heap v l :=
                    fun _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hcell⟩
                  have hEq := hpres₁ l ⟨hlt, hnotOwn⟩
                  exact hnotNum₁ ⟨o, n, hEq.trans ho, hcell⟩
                exact hhdP.2.2.2.2.2.2.2 hnb l hr0 hnotSS0 hnotNum0 hF
          have hEnvNRF_push : EnvNoReachForbid st₁ (fun _ => True) (bnd :: env) acc₁.1 acc₁.2 Forbid (· = 2) (fun _ => False) := by
            intro i b' ab' _ hbi' habi' hne' ha'
            cases i with
            | zero =>
              dsimp only [acc₁, initBodyStep] at habi'
              simp at hbi' habi'; subst hbi'; subst habi'
              exact hNewNRF
            | succ k =>
              have hbiK : env[k]? = some b' := by simpa using hbi'
              have habiK : aenv[k]? = some ab' := by simpa [acc₁, initBodyStep] using habi'
              have hleP : AStateLe σ acc₁.2 := (hsim.2.1.pushBnd bv (p.mode.usage == .once)).2
              have hvK := ((hsim₁.2.2.2.2.2.1 k b' ab' trivial hbiK habiK).2 hne').2
              have hsrcK : ∀ x, (effVal ab').src = some x → x < σ.st.size := fun x hx => (hvK.2.2.1 x hx).1
              exact henvNRF₁ k b' ab' trivial hbiK habiK hne'
                (ActiveVal.of_AStateLe hsim.2.1 hleP hvK.2.1 hsrcK ha')
          by_cases hu : p.mode.usage = .once
          · obtain ⟨hfunO, haOnceF, haFootOk, haFootEnv⟩ := hhdP.2.2.2.1 hu
            obtain ⟨hsp, _, loc, resFoot, hlocGe, hresSub, hresOk, hresFun⟩ :=
              bindAt_once_foot hst hu hhdP.1 hfunO haOnceF
                (fun l hl => let h := haFootOk l hl; ⟨h.1, h.2.2.1, h.2.2.2⟩) hrun₁
            have hresNotFrame : ∀ l, resFoot l → ¬ Frame l := by
              intro l hl
              rcases hresSub l hl with rfl | hfa
              · exact fun hF => Nat.not_lt_of_ge hlocGe (hFrameLt l hF)
              · exact (haFootOk l hfa).2.1
            have hresNotEnv : ∀ (i : Nat) b₂ ab₂, True → env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
                ActiveVal σ (effVal ab₂) → ∀ l, resFoot l → ¬ Reach st₁.heap b₂.val l := by
              intro i b₂ ab₂ _ hbi₂ habi₂ hne₂ ha₂ l hl hr₂
              have hpB := hpEnv₁ i b₂ ab₂ trivial hbi₂ habi₂ hne₂ ha₂
              have hrOld : Reach st.heap b₂.val l := (Reach_congr hpB l).mp hr₂
              have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ trivial hbi₂ habi₂).2 hne₂).2
              rcases hresSub l hl with rfl | hfa
              · exact Nat.not_lt_of_ge hlocGe ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size hrOld)
              · exact haFootEnv i b₂ ab₂ hbi₂ habi₂ hne₂ l hfa hrOld
            have hsimP := Sim_push_once_bnd (hmode₁ ▸ hu) hbvRegsLt
              (fun d hd => by rw [hbvDeps] at hd; cases hd) hsp hbase₁ hdouBnd hcf₁
              (fun l hl => ⟨(hresOk l hl).1, hresNotFrame l hl, (hresOk l hl).2.1, (hresOk l hl).2.2⟩)
              (hbvSkel ▸ hresFun) hresNotEnv
              (fun i b₂ ab₂ _ hbi₂ habi₂ hne₂ =>
                ⟨fun haB htrB _ _ => (hEnvDisjBv i b₂ ab₂ hbi₂ habi₂ hne₂).1 haB htrB,
                 fun haB hfB _ => (hEnvDisjBv i b₂ ab₂ hbi₂ habi₂ hne₂).2 haB hfB⟩) hsim₁
            have hbu : (p.mode.usage == .once) = true := by simp [hu]
            have haccEq : acc₁ = ({ id := (σ.pushBnd bv true).1, mode := bnd.mode, val := bv } :: aenv,
                (σ.pushBnd bv true).2) := by
              dsimp only [acc₁, initBodyStep, bv]; rw [hbu, hmode₁]
            refine ⟨⟨fun i => match i with | 0 => resFoot | k + 1 => envFoot k, ?_,
              fun _ _ => Iff.rfl, fun _ l hl => ?_⟩, hEnvNRF_push⟩
            · rw [haccEq]; exact Sim_weaken_scope (fun i _ => by cases i <;> trivial) hsimP
            · rcases hresSub l hl with rfl | hfa
              · exact Or.inl hlocGe
              · exact Or.inr hfa
          · obtain ⟨hclsB, hnoB, hfunB⟩ := hplain₁ hpEr hu
            have hnotOnceBv : ¬ IsOnceSrc σ bv := by rintro ⟨_, hs, _⟩; rw [hbvSrc] at hs; cases hs
            have hvBv : VSim P ext B st₁ Frame (fun _ => False) (fun _ => False) σ I (fun _ => False) bv bnd.val := by
              refine ⟨hbvRegsLt, (fun d hd => by rw [hbvDeps] at hd; cases hd),
                (fun _ hs => by rw [hbvSrc] at hs; cases hs),
                fun _ his => absurd his hnotOnceBv, fun _ => ?_⟩
              refine ⟨hbase₁, hdouBnd, hcf₁,
                fun _ hne => ClsSafe.to_nonValSafe (hbvCls ▸ hne) hclsB hbase₁.1.self.1,
                fun _ => ⟨hnoB, fun _ h => h, hbvSkel ▸ hfunB⟩,
                (fun h => by rw [hbvOnceOnly] at h; cases h),
                fun his => absurd his hnotOnceBv,
                fun htr => ?_⟩
              have hpu : p.mode.isUnique = true := hbvOwn htr.2.1
              refine ⟨htree₁ hpu, fun l hor => ?_⟩
              rcases hown₁ l hor with hge | ⟨_, horOld⟩
              · refine ⟨fun hF => Nat.not_lt_of_ge hge (hFrameLt l hF), fun hss => ?_⟩
                exact Nat.not_lt_of_ge hge (StOk_staticStrLoc_lt hst (StaticStrLoc_of_preserves_outside hstat₁ hstr₁ hpSS₁ l hss))
              · have hdisjO := (hhdP.2.2.2.2.2.1 hpu).2.1 l horOld
                exact ⟨hdisjO.1, fun hss => hdisjO.2 (StaticStrLoc_of_preserves_outside hstat₁ hstr₁ hpSS₁ l hss)⟩
            have hdisjBv : ValEnvDisj P st₁ (fun _ => False) (fun _ => True) env aenv σ envFoot (fun _ => False) bv bnd.val := by
              intro i b₂ ab₂ _ hbi₂ habi₂ hne₂
              have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ trivial hbi₂ habi₂).2 hne₂).2
              refine ⟨fun _ htrV haB _ l hor hrB => ?_,
                fun haB htrB _ _ => (hEnvDisjBv i b₂ ab₂ hbi₂ habi₂ hne₂).1 haB htrB,
                fun _ _ _ _ _ h => False.elim h,
                fun haB hfB _ _ => (hEnvDisjBv i b₂ ab₂ hbi₂ habi₂ hne₂).2 haB hfB,
                (fun _ _ hs => by rw [hbvSrc] at hs; cases hs),
                (fun hs => by rw [hbvSrc] at hs; cases hs),
                (fun _ hs => by rw [hbvSrc] at hs; cases hs)⟩
              have hpu : p.mode.isUnique = true := hbvOwn htrV.2.1
              have hpB := hpEnv₁ i b₂ ab₂ trivial hbi₂ habi₂ hne₂ haB
              have hrB0 : Reach st.heap b₂.val l := (Reach_congr hpB l).mp hrB
              rcases hown₁ l hor with hge | ⟨_, hor0⟩
              · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 haB).1.1.reach_lt_size hrB0)
              · exact (hhdP.2.2.2.2.2.1 hpu).2.2.2 i b₂ ab₂ hbi₂ habi₂ hne₂ l hor0 hrB0
            have hsimP := Sim_push_bnd hbvSrc (fun _ _ _ h => h)
              (fun h => absurd (hmode₁ ▸ h) hu)
              (fun h => absurd (hmode₁ ▸ h) hu)
              (fun h => absurd (hmode₁ ▸ h) hu) hvBv hdisjBv hsim₁
            have haccEq : acc₁ = ({ id := (σ.pushBnd bv (bnd.mode.usage == .once)).1, mode := bnd.mode, val := bv } :: aenv,
                (σ.pushBnd bv (bnd.mode.usage == .once)).2) := by
              dsimp only [acc₁, initBodyStep, bv]; rw [hmode₁]
            refine ⟨⟨fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k, ?_,
              fun _ _ => Iff.rfl, fun hu' => absurd hu' hu⟩, hEnvNRF_push⟩
            rw [haccEq]; exact Sim_weaken_scope (fun i _ => by cases i <;> trivial) hsimP
      obtain ⟨⟨envFoot₁, hsim₁P, hftShift, hftHead⟩, henvNRF₁P⟩ := hPush
      -- Lift remaining items `rest` from `st` to `st₁`
      have hpresItem : ∀ (k : Nat) (it : Param × Val × Bool × (Nat → Prop)),
          rest[k]? = some it → it.1.mode ≠ .erased →
          PreservesLocs (Reach st.heap it.2.1) st.heap st₁.heap := by
        intro k it hget hneIt
        have hit := hitems it (List.mem_cons_of_mem _ (List.mem_of_getElem? hget)) hneIt
        refine hpres₁.mono fun l hrl => ⟨hit.1.1.reach_lt_size hrl, fun hpu hor => ?_⟩
        have hneP : p.mode ≠ .erased := by intro he; rw [he] at hpu; cases hpu
        exact (hpair 0 (k + 1) (p, v, aOnce, aFoot) it (by omega) rfl (by simpa using hget) hneP hneIt).1 hpu l hor hrl
      have hitems₁ : ∀ it ∈ rest,
          let (p2, v2, aOnce2, aFoot2) := it
          p2.mode ≠ .erased →
            ValBaseOk st₁ v2 ∧
            DeepOpenUnder st₁.heap st₁.regions (argRegs.filter (· < s)) v2 ∧
            CtorFieldsOk P ext B st₁ v2 ∧
            (p2.mode.usage = .once →
              FunOkAt P ext B st₁ p2.skel aOnce2 aFoot2 v2 ∧
              (aOnce2 = false → ∀ l, ¬ aFoot2 l) ∧
              (∀ l, aFoot2 l → Reach st₁.heap v2 l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
              (∀ (i : Nat) b ab, (bnd :: env)[i]? = some b → acc₁.1[i]? = some ab → ab.mode ≠ .erased →
                ∀ l, aFoot2 l → ¬ Reach st₁.heap b.val l)) ∧
            (p2.mode.usage ≠ .once →
              NoOnceCell st₁.heap v2 ∧ FunOkAt P ext B st₁ p2.skel false (fun _ => False) v2) ∧
            (p2.mode.isUnique = true →
              OwnTreeFull P st₁.heap v2 ∧
              (∀ l, OwnReach P st₁.heap v2 l → ¬ Frame l ∧ ¬ StaticStrLoc st₁ l) ∧
              (p2.mode.isBorrowed = false → DeepOpenUnder st₁.heap st₁.regions [] v2) ∧
              (∀ (i : Nat) b ab, (bnd :: env)[i]? = some b → acc₁.1[i]? = some ab → ab.mode ≠ .erased →
                ∀ l, OwnReach P st₁.heap v2 l → ¬ Reach st₁.heap b.val l)) ∧
            (∀ (i : Nat) b ab, (bnd :: env)[i]? = some b → acc₁.1[i]? = some ab → ab.mode ≠ .erased →
              (ab.val.own = .uniq → ab.val.cls = .val → ab.mode.usage ≠ .once →
                ∀ l, OwnReach P st₁.heap b.val l → ¬ Reach st₁.heap v2 l) ∧
              (ab.mode.usage = .once → ∀ l, envFoot₁ i l → ¬ Reach st₁.heap v2 l)) ∧
            (p2.mode.isBorrowed = false → ∀ l, Reach st₁.heap v2 l → ¬ StaticStrLoc st₁ l → ¬ NumLoc st₁.heap l → ¬ Forbid l) := by
        intro it hitMem
        obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hitMem
        have hget? : rest[k]? = some it := by rw [List.getElem?_eq_getElem hk, hget]
        rcases it with ⟨p2, v2, aOnce2, aFoot2⟩
        intro hne2
        have h0 := hitems (p2, v2, aOnce2, aFoot2) (List.mem_cons_of_mem _ hitMem) hne2
        have hp2 := hpresItem k (p2, v2, aOnce2, aFoot2) hget? hne2
        have hssBack : ∀ l, StaticStrLoc st₁ l → StaticStrLoc st l :=
          StaticStrLoc_of_preserves_outside hstat₁ hstr₁ hpSS₁
        refine ⟨ValBaseOk_congr hp2 hrf₁.1 h0.1,
          (DeepOpenUnder_congr hp2).mpr (hr₁ ▸ h0.2.1),
          CtorFieldsOk_congr h0.1.1 hp2 hrf₁ h0.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
        · intro hu2
          obtain ⟨hf2, hof2, hok2, henv2⟩ := h0.2.2.2.1 hu2
          refine ⟨FunOkAt_preserve_locs hp2 hrf₁ hf2, hof2, fun l hl => ?_, fun i b ab hbi habi hneAb l hl hrB => ?_⟩
          · obtain ⟨hrV, hnf, hnss, hnn⟩ := hok2 l hl
            exact ⟨(Reach_congr hp2 l).mpr hrV, hnf, fun hss => hnss (hssBack l hss),
              fun hnum => hnn ((NumLoc_congr hp2 hrV).mpr hnum)⟩
          · cases i with
            | zero =>
              simp at hbi; subst hbi
              dsimp only [acc₁, initBodyStep] at habi; simp at habi; subst habi
              rcases hreach₁ l hrB with hge | ⟨hneP, hrV0⟩
              · exact Nat.not_lt_of_ge hge (h0.1.1.reach_lt_size (hok2 l hl).1)
              · exact (hpair (k + 1) 0 (p2, v2, aOnce2, aFoot2) (p, v, aOnce, aFoot) (by omega)
                  (by simpa using hget?) rfl hne2 hneP).2 hu2 l hl hrV0
            | succ m =>
              have hbiM : env[m]? = some b := by simpa using hbi
              have habiM : aenv[m]? = some ab := by simpa [acc₁, initBodyStep] using habi
              have hpM := hpEnv₁ m b ab trivial hbiM habiM hneAb (hAllAct m ab habiM hneAb)
              exact henv2 m b ab hbiM habiM hneAb l hl ((Reach_congr hpM l).mp hrB)
        · intro hnu2
          obtain ⟨hno2, hf2⟩ := h0.2.2.2.2.1 hnu2
          exact ⟨NoOnceCell_congr h0.1.1 hp2 hno2, FunOkAt_preserve_locs hp2 hrf₁ hf2⟩
        · intro hu2
          obtain ⟨ht2, hdisj2, hopen2, henv2⟩ := h0.2.2.2.2.2.1 hu2
          refine ⟨(OwnTreeFull_congr hp2).mpr ht2, fun l hor => ?_,
            fun hnb => (DeepOpenUnder_congr hp2).mpr (hr₁ ▸ hopen2 hnb),
            fun i b ab hbi habi hneAb l hor hrB => ?_⟩
          · have hor0 := (OwnReach_congr hp2 l).mp hor
            exact ⟨(hdisj2 l hor0).1, fun hss => (hdisj2 l hor0).2 (hssBack l hss)⟩
          · have hor0 := (OwnReach_congr hp2 l).mp hor
            cases i with
            | zero =>
              simp at hbi; subst hbi
              dsimp only [acc₁, initBodyStep] at habi; simp at habi; subst habi
              rcases hreach₁ l hrB with hge | ⟨hneP, hrV0⟩
              · exact Nat.not_lt_of_ge hge (h0.1.1.reach_lt_size (OwnReach_toReach hor0))
              · exact (hpair (k + 1) 0 (p2, v2, aOnce2, aFoot2) (p, v, aOnce, aFoot) (by omega)
                  (by simpa using hget?) rfl hne2 hneP).1 hu2 l hor0 hrV0
            | succ m =>
              have hbiM : env[m]? = some b := by simpa using hbi
              have habiM : aenv[m]? = some ab := by simpa [acc₁, initBodyStep] using habi
              have hpM := hpEnv₁ m b ab trivial hbiM habiM hneAb (hAllAct m ab habiM hneAb)
              exact henv2 m b ab hbiM habiM hneAb l hor0 ((Reach_congr hpM l).mp hrB)
        · intro i b ab hbi habi hneAb
          cases i with
          | zero =>
            simp at hbi; subst hbi
            dsimp only [acc₁, initBodyStep] at habi; simp at habi; subst habi
            refine ⟨fun hown _ _ l hor hr2 => ?_, fun huP l hft hr2 => ?_⟩
            · have hpu : p.mode.isUnique = true := by
                dsimp only [paramVal] at hown
                cases hm : p.mode <;> rw [hm] at hown <;> first | rfl | cases hown
              have hr20 := (Reach_congr hp2 l).mp hr2
              rcases hown₁ l hor with hge | ⟨_, hor0⟩
              · exact Nat.not_lt_of_ge hge (h0.1.1.reach_lt_size hr20)
              · exact (hpair 0 (k + 1) (p, v, aOnce, aFoot) (p2, v2, aOnce2, aFoot2) (by omega)
                  rfl (by simpa using hget?) hneAb hne2).1 hpu l hor0 hr20
            · have hr20 := (Reach_congr hp2 l).mp hr2
              rcases hftHead huP l hft with hge | hfa
              · exact Nat.not_lt_of_ge hge (h0.1.1.reach_lt_size hr20)
              · exact (hpair 0 (k + 1) (p, v, aOnce, aFoot) (p2, v2, aOnce2, aFoot2) (by omega)
                  rfl (by simpa using hget?) hneAb hne2).2 huP l hfa hr20
          | succ m =>
            have hbiM : env[m]? = some b := by simpa using hbi
            have habiM : aenv[m]? = some ab := by simpa [acc₁, initBodyStep] using habi
            have hpM := hpEnv₁ m b ab trivial hbiM habiM hneAb (hAllAct m ab habiM hneAb)
            refine ⟨fun hown hcls hnu l hor hr2 => ?_, fun huM l hft hr2 => ?_⟩
            · exact (h0.2.2.2.2.2.2.1 m b ab hbiM habiM hneAb).1 hown hcls hnu l
                ((OwnReach_congr hpM l).mp hor) ((Reach_congr hp2 l).mp hr2)
            · exact (h0.2.2.2.2.2.2.1 m b ab hbiM habiM hneAb).2 huM l ((hftShift m l).mp hft) ((Reach_congr hp2 l).mp hr2)
        · intro hnb l hr2 hnotSS₁ hnotNum₁ hF
          have hr20 := (Reach_congr hp2 l).mp hr2
          have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
            hnotSS₁ (StaticStrLoc_mono (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _) hpSS₁ hss0)
          have hnotNum0 : ¬ NumLoc st.heap l := fun hnum0 => hnotNum₁ ((NumLoc_congr hp2 hr20).mp hnum0)
          exact h0.2.2.2.2.2.2.2 hnb l hr20 hnotSS0 hnotNum0 hF
      have hpair₁ : ∀ (i j : Nat) (it₁ it₂ : Param × Val × Bool × (Nat → Prop)), i ≠ j →
          rest[i]? = some it₁ → rest[j]? = some it₂ →
          it₁.1.mode ≠ .erased → it₂.1.mode ≠ .erased →
          (it₁.1.mode.isUnique = true → ∀ l, OwnReach P st₁.heap it₁.2.1 l → ¬ Reach st₁.heap it₂.2.1 l) ∧
          (it₁.1.mode.usage = .once → ∀ l, it₁.2.2.2 l → ¬ Reach st₁.heap it₂.2.1 l) := by
        intro i j it₁ it₂ hij hg₁ hg₂ hne₁ hne₂
        have hp1 := hpresItem i it₁ hg₁ hne₁
        have hp2 := hpresItem j it₂ hg₂ hne₂
        have h0 := hpair (i + 1) (j + 1) it₁ it₂ (by omega) (by simpa using hg₁) (by simpa using hg₂) hne₁ hne₂
        exact ⟨fun hu l hor hr => h0.1 hu l ((OwnReach_congr hp1 l).mp hor) ((Reach_congr hp2 l).mp hr),
          fun hu l hft hr => h0.2 hu l hft ((Reach_congr hp2 l).mp hr)⟩
      have hErIrr₁ : ∀ (i : Nat) (b : Bnd) (ab : ABnd), (bnd :: env)[i]? = some b → acc₁.1[i]? = some ab → ab.mode = .erased → b.val = .imm .irr := by
        intro i b ab hbi habi herAb
        cases i with
        | zero =>
          simp at hbi; subst hbi; dsimp only [acc₁, initBodyStep] at habi; simp at habi; subst habi
          rw [(her₁ herAb).1]
        | succ k => exact hErIrr k b ab (by simpa using hbi) (by simpa [acc₁, initBodyStep] using habi) herAb
      rcases ih (bnd :: env) acc₁.1 acc₁.2 envFoot₁ st₁ hst₁ (hnr₁ ▸ hs) (hr₁ ▸ hregsSt) hσReg₁
          (fun l hf => Nat.lt_of_lt_of_le (hFrameLt l hf) hsz₁)
          (fun l hf => Nat.lt_of_lt_of_le (hForbidLt l hf) hsz₁)
          hnoOO₁ hAllAct₁ hErIrr₁ hsim₁P henvNRF₁P hitems₁ hpair₁ with hSt2 | hOOF2 |
        ⟨env', st', hrun2, hr2, hnr2, hstat2, hstr2, hsz2, hcap2, hpFrame2, hpSS2, honceSh2, hssf2,
          hst', hsim', henvNRF', hreach2⟩
      · exact Or.inl hSt2
      · exact Or.inr (Or.inl hOOF2)
      · right; right
        have hpSS02 : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
          hpSS₁.trans (hpSS2.mono fun l hss => StaticStrLoc_mono (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _) hpSS₁ hss)
        refine ⟨env', st', hrun2, hr2.trans hr₁, hnr2.trans hnr₁, hstat2.trans hstat₁, hstr2.trans hstr₁,
          Nat.le_trans hsz₁ hsz2, Nat.le_trans hcap₁ hcap2,
          hpFrame₁.trans hpFrame2, hpSS02, honceSh₁.trans honceSh2,
          StaticStrFresh.trans hsz₁ hpSS2 hssf₁ hssf2, hst', hsim', henvNRF', ?_⟩
        intro b' hb' l hr'
        rcases hreach2 b' hb' l hr' with hge1 | ⟨b0, hb0, hr1⟩ | ⟨it, hit, hneIt, hr1⟩
        · exact Or.inl (Nat.le_trans hsz₁ hge1)
        · rcases List.mem_cons.mp hb0 with rfl | hbOld
          · rcases hreach₁ l hr1 with hge0 | ⟨hneP, hrV0⟩
            · exact Or.inl hge0
            · exact Or.inr (Or.inr ⟨(p, v, aOnce, aFoot), List.mem_cons_self, hneP, hrV0⟩)
          · obtain ⟨m, hm, hbEq⟩ := List.getElem_of_mem hbOld
            have hbiM : env[m]? = some b0 := by rw [List.getElem?_eq_getElem hm, hbEq]
            have hmA : m < aenv.length := by rw [← hsim.1]; exact hm
            let ab0 := aenv[m]
            have habiM : aenv[m]? = some ab0 := List.getElem?_eq_getElem hmA
            by_cases hne0 : ab0.mode = .erased
            · rw [hErIrr m b0 ab0 hbiM habiM hne0] at hr1; cases hr1
            · have hpM := hpEnv₁ m b0 ab0 trivial hbiM habiM hne0 (hAllAct m ab0 habiM hne0)
              exact Or.inr (Or.inl ⟨b0, hbOld, (Reach_congr hpM l).mp hr1⟩)
        · obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hit
          have hpIt := hpresItem k it (by rw [List.getElem?_eq_getElem hk, hget]) hneIt
          exact Or.inr (Or.inr ⟨it, List.mem_cons_of_mem _ hit, hneIt, (Reach_congr hpIt l).mp hr1⟩)

/-- **Bridge 5 (`bindParamsM_checked_sound`)**: simulates `enterS`'s `openRegion` + `bindParamsM`
against `initBody params`, producing `Sim`, `RegUnique`, `EnvNoReachForbid`, and a `Reach` bound. -/
theorem bindParamsM_checked_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {params : Array Param} {vs : List Val} {st : St}
    {Frame : Nat → Prop} {argRegs : List Nat}
    {argOnce : Nat → Bool} {argFoot : Nat → Nat → Prop}
    (hst : StOk P ext B st)
    (hlen : vs.length = params.size)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v → p.mode ≠ .erased →
      ValBaseOk st v ∧
      DeepOpenUnder st.heap st.regions argRegs v ∧
      CtorFieldsOk P ext B st v ∧
      (p.mode.usage = .once →
        FunOkAt P ext B st p.skel (argOnce i) (argFoot i) v ∧
        (argOnce i = false → ∀ l, ¬ argFoot i l) ∧
        (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l)) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st.heap v ∧ FunOkAt P ext B st p.skel false (fun _ => False) v) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap v ∧
        (∀ l, OwnReach P st.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st l) ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v)))
    (hpair : ∀ (i j : Nat) (p₁ p₂ : Param) (v₁ v₂ : Val), i ≠ j →
      params[i]? = some p₁ → vs[i]? = some v₁ →
      params[j]? = some p₂ → vs[j]? = some v₂ →
      p₁.mode ≠ .erased → p₂.mode ≠ .erased →
      (p₁.mode.isUnique = true → ∀ l, OwnReach P st.heap v₁ l → ¬ Reach st.heap v₂ l) ∧
      (p₁.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap v₂ l)) :
    let s := st.nextRegion
    let st₁ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
    let I : Interp := ⟨fun r => if r == 2 then [s] else argRegs.filter (· < s)⟩
    let Forbid : Nat → Prop := fun l =>
      l < st.heap.objs.size ∧ ¬ StaticStrLoc st l ∧
      ∀ (i : Nat) p v, params[i]? = some p → vs[i]? = some v →
        p.mode ≠ .erased → p.mode.isBorrowed = false → ¬ Reach st.heap v l
    (bindParamsM P fuel s (params.toList.zip vs) []).run st₁ = .error .stuck ∨
    (bindParamsM P fuel s (params.toList.zip vs) []).run st₁ = .error .outOfFuel ∨
    ∃ env st₂, (bindParamsM P fuel s (params.toList.zip vs) []).run st₁ = .ok (env, st₂) ∧
      st₂.regions = st₁.regions ∧ st₂.nextRegion = st₁.nextRegion ∧
      st₂.statics = st.statics ∧ st₂.strs = st.strs ∧
      st.heap.objs.size ≤ st₂.heap.objs.size ∧ st.heap.nextCap ≤ st₂.heap.nextCap ∧
      PreservesLocs Frame st.heap st₂.heap ∧
      PreservesLocs (StaticStrLoc st) st.heap st₂.heap ∧
      PreservesOnceShell st.heap st₂.heap ∧
      StaticStrFresh st st₂ ∧
      StOk P ext B st₂ ∧
      (∃ envFoot,
        Sim P ext B st₂ Frame (fun _ => False) (fun _ => False) (fun _ => True)
          env (initBody params).1 (initBody params).2 I envFoot) ∧
      RegUnique I (initBody params).2 2 s ∧
      EnvNoReachForbid st₂ (fun _ => True) env (initBody params).1 (initBody params).2 Forbid (· = 2) (fun _ => False) ∧
      (∀ b ∈ env, ∀ l, Reach st₂.heap b.val l →
        st.heap.objs.size ≤ l ∨
        ∃ (i : Nat) (p : Param) (v : Val), params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧ Reach st.heap v l) := by
  intro s st₁ I Forbid
  let items : List (Param × Val × Bool × (Nat → Prop)) :=
    (List.range params.size).filterMap fun i =>
      match params[i]?, vs[i]? with
      | some p, some v => some (p, v, argOnce i, argFoot i)
      | _, _ => none
  have hitemsLen : items.length = params.size := by
    have hEq : items = (List.range params.size).map fun i =>
        if h : i < params.size then (params[i], vs[i]'(hlen ▸ h), argOnce i, argFoot i)
        else (default, default, false, fun _ => False) := by
      dsimp only [items]
      have hsub : ∀ xs : List Nat, (∀ i ∈ xs, i < params.size) →
          xs.filterMap (fun i => match params[i]?, vs[i]? with
            | some p, some v => some (p, v, argOnce i, argFoot i) | _, _ => none) =
          xs.map (fun i => if h : i < params.size then (params[i], vs[i]'(hlen ▸ h), argOnce i, argFoot i)
            else (default, default, false, fun _ => False)) := by
        intro xs hxs
        induction xs with
        | nil => rfl
        | cons x rest ih =>
          have hx : x < params.size := hxs x List.mem_cons_self
          have hxV : x < vs.length := hlen ▸ hx
          simp only [List.filterMap_cons, List.map_cons, Array.getElem?_eq_getElem hx,
            List.getElem?_eq_getElem hxV, hx, ↓reduceDIte]
          exact congrArg _ (ih fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      exact hsub (List.range params.size) fun i hi => List.mem_range.mp hi
    rw [hEq, List.length_map, List.length_range]
  have hitemsGet : ∀ (i : Nat) (h : i < params.size),
      items[i]? = some (params[i], vs[i]'(hlen ▸ h), argOnce i, argFoot i) := by
    intro i hi
    have hEq : items = (List.range params.size).map fun j =>
        if hj : j < params.size then (params[j], vs[j]'(hlen ▸ hj), argOnce j, argFoot j)
        else (default, default, false, fun _ => False) := by
      dsimp only [items]
      have hsub : ∀ xs : List Nat, (∀ j ∈ xs, j < params.size) →
          xs.filterMap (fun j => match params[j]?, vs[j]? with
            | some p, some v => some (p, v, argOnce j, argFoot j) | _, _ => none) =
          xs.map (fun j => if hj : j < params.size then (params[j], vs[j]'(hlen ▸ hj), argOnce j, argFoot j)
            else (default, default, false, fun _ => False)) := by
        intro xs hxs
        induction xs with
        | nil => rfl
        | cons x rest ih =>
          have hx : x < params.size := hxs x List.mem_cons_self
          have hxV : x < vs.length := hlen ▸ hx
          simp only [List.filterMap_cons, List.map_cons, Array.getElem?_eq_getElem hx,
            List.getElem?_eq_getElem hxV, hx, ↓reduceDIte]
          exact congrArg _ (ih fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      exact hsub (List.range params.size) fun j hj => List.mem_range.mp hj
    rw [hEq, List.getElem?_map, List.getElem?_range hi]; simp [hi]
  have hpvsEq : items.map (fun it => (it.1, it.2.1)) = params.toList.zip vs := by
    apply List.ext_getElem
    · simp [hitemsLen, hlen]
    · intro i h1 h2
      have hi : i < params.size := by simpa [hitemsLen] using h1
      have hg := hitemsGet i hi
      rw [List.getElem?_eq_getElem (hitemsLen ▸ hi)] at hg
      have hitemI := Option.some.inj hg
      simp only [List.getElem_map, List.getElem_zip, Array.getElem_toList, hitemI]
  have hpsEq : items.map (·.1) = params.toList := by
    apply List.ext_getElem
    · simp [hitemsLen]
    · intro i h1 _
      have hi : i < params.size := by simpa [hitemsLen] using h1
      have hg := hitemsGet i hi
      rw [List.getElem?_eq_getElem (hitemsLen ▸ hi)] at hg
      have hitemI := Option.some.inj hg
      simp only [List.getElem_map, Array.getElem_toList, hitemI]
  let s0 : AState := { regions := [2, 1], nextRegion := 3 }
  have hinitEq : (items.map (·.1)).foldl initBodyStep ([], s0) = initBody params := by
    rw [hpsEq]; unfold initBody; rw [← Array.foldl_toList]; rfl
  have hst₁ : StOk P ext B st₁ := StOk_openRegion hst
  have hs0Ok : AStateOk s0 := ⟨rfl, rfl, by decide, by simp [s0], by simp [s0], by
    intro r hr; simp [s0] at hr; rcases hr with rfl | rfl <;> (dsimp only [s0]; omega)⟩
  have hIok0 : InterpOk s0 st₁ I := by
    refine ⟨fun r hr c hc => ?_, fun c hc => ?_⟩
    · dsimp only [I] at hc
      by_cases hr2 : r = 2
      · subst hr2; simp at hc; subst hc; exact Nat.lt_succ_self _
      · have hbf : (r == 2) = false := beq_false_of_ne hr2
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
        exact Nat.lt_succ_of_lt hc.2
    · dsimp only [st₁] at hc; cases hc; simp [s0, I]
  have hsim0 : Sim P ext B st₁ Frame (fun _ => False) (fun _ => False) (fun _ => True)
      [] [] s0 I (fun _ _ => False) :=
    ⟨rfl, hs0Ok, hIok0, (fun _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
     (fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
  have hregU : RegUnique I (initBody params).2 2 s := by
    have hnrEq : (initBody params).2.nextRegion = 3 := by
      unfold initBody; rw [← Array.foldl_toList]
      suffices ∀ (ps : List Param) (acc : List ABnd × AState), acc.2.nextRegion = 3 →
          (ps.foldl initBodyStep acc).2.nextRegion = 3 from this params.toList ([], s0) rfl
      intro ps; induction ps with
      | nil => intro acc h; exact h
      | cons _ rest ihr => intro acc h; exact ihr _ h
    refine ⟨by simp [I], fun r hr hne hc => ?_⟩
    dsimp only [I] at hc; rw [beq_false_of_ne hne] at hc
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
    exact Nat.lt_irrefl _ hc.2
  have hitemsOk : ∀ it ∈ items,
      let (p, v, aOnce, aFoot) := it
      p.mode ≠ .erased →
        ValBaseOk st₁ v ∧
        DeepOpenUnder st₁.heap st₁.regions (argRegs.filter (· < s)) v ∧
        CtorFieldsOk P ext B st₁ v ∧
        (p.mode.usage = .once →
          FunOkAt P ext B st₁ p.skel aOnce aFoot v ∧
          (aOnce = false → ∀ l, ¬ aFoot l) ∧
          (∀ l, aFoot l → Reach st₁.heap v l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
          (∀ (i : Nat) b ab, ([] : List Bnd)[i]? = some b → ([] : List ABnd)[i]? = some ab → ab.mode ≠ .erased →
            ∀ l, aFoot l → ¬ Reach st₁.heap b.val l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st₁.heap v ∧ FunOkAt P ext B st₁ p.skel false (fun _ => False) v) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st₁.heap v ∧
          (∀ l, OwnReach P st₁.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st₁ l) ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st₁.heap st₁.regions [] v) ∧
          (∀ (i : Nat) b ab, ([] : List Bnd)[i]? = some b → ([] : List ABnd)[i]? = some ab → ab.mode ≠ .erased →
            ∀ l, OwnReach P st₁.heap v l → ¬ Reach st₁.heap b.val l)) ∧
        (∀ (i : Nat) b ab, ([] : List Bnd)[i]? = some b → ([] : List ABnd)[i]? = some ab → ab.mode ≠ .erased →
          (ab.val.own = .uniq → ab.val.cls = .val → ab.mode.usage ≠ .once →
            ∀ l, OwnReach P st₁.heap b.val l → ¬ Reach st₁.heap v l) ∧
          (ab.mode.usage = .once → ∀ l, (fun _ _ => False) i l → ¬ Reach st₁.heap v l)) ∧
        (p.mode.isBorrowed = false → ∀ l, Reach st₁.heap v l → ¬ StaticStrLoc st₁ l → ¬ NumLoc st₁.heap l → ¬ Forbid l) := by
    intro it hit hne
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hit
    have hkP : k < params.size := hitemsLen ▸ hk
    have hgetK := hitemsGet k hkP
    rw [List.getElem?_eq_getElem hk, hget] at hgetK
    have hEqIt := Option.some.inj hgetK
    subst hEqIt
    dsimp only at hne ⊢
    have hpi : params[k]? = some params[k] := Array.getElem?_eq_getElem hkP
    have hvi : vs[k]? = some (vs[k]'(hlen ▸ hkP)) := List.getElem?_eq_getElem (hlen ▸ hkP)
    obtain ⟨hbv, hdou, hcf, honce, hplain, huniq⟩ := hargs k params[k] (vs[k]'(hlen ▸ hkP)) hpi hvi hne
    have hrf01 : RegsFuture st st₁ := RegsFuture.openRegion st
    have hdouFilt : DeepOpenUnder st₁.heap st₁.regions (argRegs.filter (· < s)) (vs[k]'(hlen ▸ hkP)) := by
      intro w hw r hr hopen
      have hrLt : r < s := hbv.2.2.2 w hw r hr
      have hopen0 : r ∈ st.regions := by
        rcases List.mem_cons.mp hopen with rfl | h0
        · exact absurd hrLt (Nat.lt_irrefl _)
        · exact h0
      exact List.mem_filter.mpr ⟨hdou w hw r hr hopen0, decide_eq_true hrLt⟩
    refine ⟨ValBaseOk_congr (PreservesLocs.refl _ st.heap) hrf01.1 hbv,
      hdouFilt, CtorFieldsOk_congr hbv.1 (PreservesLocs.refl _ st.heap) hrf01 hcf,
      (fun hu => let h := honce hu; ⟨FunOkAt_preserve_locs (PreservesLocs.refl _ st.heap) hrf01 h.1,
        h.2.1, h.2.2, (fun _ _ _ hb => by cases hb)⟩),
      (fun hnu => let h := hplain hnu; ⟨h.1, FunOkAt_preserve_locs (PreservesLocs.refl _ st.heap) hrf01 h.2⟩),
      (fun hu => let h := huniq hu; ⟨h.1, h.2.1,
        (fun hnb => DeepOpenUnder_of_regsFuture hbv.2.2.2 (h.2.2 hnb) hrf01),
        (fun _ _ _ hb => by cases hb)⟩),
      (fun _ _ _ hb => by cases hb),
      (fun hnb l hr _ _ hF => hF.2.2 k params[k] (vs[k]'(hlen ▸ hkP)) hpi hvi hne hnb hr)⟩
  have hpairOk : ∀ (i j : Nat) (it₁ it₂ : Param × Val × Bool × (Nat → Prop)), i ≠ j →
      items[i]? = some it₁ → items[j]? = some it₂ →
      it₁.1.mode ≠ .erased → it₂.1.mode ≠ .erased →
      (it₁.1.mode.isUnique = true → ∀ l, OwnReach P st₁.heap it₁.2.1 l → ¬ Reach st₁.heap it₂.2.1 l) ∧
      (it₁.1.mode.usage = .once → ∀ l, it₁.2.2.2 l → ¬ Reach st₁.heap it₂.2.1 l) := by
    intro i j it₁ it₂ hij hg₁ hg₂ hne₁ hne₂
    have hi : i < params.size := hitemsLen ▸ (List.getElem?_eq_some_iff.mp hg₁).1
    have hj : j < params.size := hitemsLen ▸ (List.getElem?_eq_some_iff.mp hg₂).1
    rw [hitemsGet i hi] at hg₁; cases hg₁
    rw [hitemsGet j hj] at hg₂; cases hg₂
    exact hpair i j params[i] params[j] (vs[i]'(hlen ▸ hi)) (vs[j]'(hlen ▸ hj)) hij
      (Array.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
      (Array.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (hlen ▸ hj)) hne₁ hne₂
  rcases bindParamsM_loop_checked_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s)
      (Frame := Frame) (Forbid := Forbid) (argRegs := argRegs) items [] [] s0 (fun _ _ => False) st₁
      hst₁ (Nat.lt_succ_self s) rfl ⟨rfl, rfl⟩ hFrameLt (fun _ h => h.1)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
      hsim0 (fun _ _ _ _ h => by cases h) hitemsOk hpairOk with hSt | hOOF |
    ⟨env, st₂, hrun, hr2, hnr2, hstat2, hstr2, hsz2, hcap2, hpFrame2, hpSS2, honceSh2, hssf2,
      hst₂, hsim₂, henvNRF₂, hreach₂⟩
  · exact Or.inl (hpvsEq ▸ hSt)
  · exact Or.inr (Or.inl (hpvsEq ▸ hOOF))
  · right; right
    rw [hpvsEq] at hrun
    rw [hinitEq] at hsim₂ henvNRF₂
    refine ⟨env, st₂, hrun, hr2, hnr2, hstat2, hstr2, hsz2, hcap2, hpFrame2, hpSS2, honceSh2, hssf2,
      hst₂, hsim₂, hregU, henvNRF₂, fun b hb l hr => ?_⟩
    rcases hreach₂ b hb l hr with hge | ⟨_, hnil, _⟩ | ⟨it, hit, hneIt, hrIt⟩
    · exact Or.inl hge
    · cases hnil
    · obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hit
      have hkP : k < params.size := hitemsLen ▸ hk
      have hgK := hitemsGet k hkP
      rw [List.getElem?_eq_getElem hk, hget] at hgK
      have hEqIt := Option.some.inj hgK
      subst hEqIt
      exact Or.inr ⟨k, params[k], vs[k]'(hlen ▸ hkP), Array.getElem?_eq_getElem hkP,
        List.getElem?_eq_getElem (hlen ▸ hkP), hneIt, hrIt⟩

/-! ## 4. Bridge 3 (`ctor_sat_bridge`) -/

private theorem kept_mem_iff (fields : Array Field) (k : Nat) :
    k ∈ ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).toList ↔
    ∃ f, fields[k]? = some f ∧ f.kept = true := by
  rw [Array.toList_map, Array.toList_filter, Array.toList_zipIdx, List.mem_map]
  constructor
  · rintro ⟨⟨f, j⟩, hmem, rfl⟩
    rw [List.mem_filter] at hmem
    obtain ⟨hz, hfk⟩ := hmem
    have hget := List.mem_zipIdx hz
    have hlt' : j < fields.size := by simpa using hget.2.1
    have hget' : f = fields[j] := by simpa using hget.2.2
    exact ⟨f, by rw [Array.getElem?_eq_getElem hlt', hget'], hfk⟩
  · rintro ⟨f, hfk, hkept⟩
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hfk
    refine ⟨(f, k), List.mem_filter.mpr ⟨?_, hkept⟩, rfl⟩
    have hltL : k < fields.toList.length := by simpa using hlt
    have hz := List.getElem_mem (l := fields.toList.zipIdx) (n := k) (by simpa using hltL)
    simpa [List.getElem_zipIdx, hget] using hz

private theorem constructLoop_all_not_kept (xs : List (Field × Val)) (out : Array Val) (st : St)
    (h : ∀ fv ∈ xs, fv.1.kept = false) :
    ∃ out', (constructLoop xs out).run st = .ok (out', st) ∧
      out'.size = out.size + xs.length ∧
      (∀ i, i < out.size → out'[i]? = out[i]?) := by
  induction xs generalizing out with
  | nil => exact ⟨out, rfl, by simp, fun _ _ => rfl⟩
  | cons fv rest ih =>
    have hf : fv.1.kept = false := h fv List.mem_cons_self
    unfold constructLoop
    simp only [hf, Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run]
    obtain ⟨out', hrun, hsz, hold⟩ := ih (out.push (.imm .irr)) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨out', hrun, by simp [hsz]; omega, fun i hi => ?_⟩
    have hi' : i < (out.push (.imm .irr)).size := by simp; omega
    rw [hold i hi', Array.getElem?_push_lt hi]
    exact (Array.getElem?_eq_getElem hi).symm

private theorem constructLoop_single_kept (xs : List (Field × Val)) (out : Array Val) (st : St)
    (idx : Nat) (f0 : Field) (v0 : Val)
    (hget : xs[idx]? = some (f0, v0))
    (hk0 : f0.kept = true)
    (hother : ∀ (j : Nat) fv, j ≠ idx → xs[j]? = some fv → fv.1.kept = false) :
    (∀ e, (conform f0.cls v0).run st = .error e → (constructLoop xs out).run st = .error e) ∧
    (∀ v1 st₁, (conform f0.cls v0).run st = .ok (v1, st₁) →
      ∃ out', (constructLoop xs out).run st = .ok (out', st₁) ∧
        out'[out.size + idx]? = some v1) := by
  induction xs generalizing out idx with
  | nil => simp at hget
  | cons fv rest ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hrest : ∀ x ∈ rest, x.1.kept = false := by
        intro x hx
        obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hx
        exact hother (k + 1) x (by omega) (by rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hk, heq])
      constructor
      · intro e herr
        unfold constructLoop
        simp only [hk0, ↓reduceIte, M_bind_run, herr]
      · intro v1 st₁ hok
        unfold constructLoop
        simp only [hk0, ↓reduceIte, M_bind_run, hok]
        obtain ⟨out', hrun, _, hold⟩ := constructLoop_all_not_kept rest (out.push v1) st₁ hrest
        refine ⟨out', hrun, ?_⟩
        have hlt : out.size < (out.push v1).size := by simp
        have h0 := hold out.size hlt
        rw [Array.getElem?_push_size] at h0
        simpa using h0
    | succ idx' =>
      simp only [List.getElem?_cons_succ] at hget
      have hfv : fv.1.kept = false := hother 0 fv (by omega) rfl
      have hother' : ∀ (j : Nat) fv', j ≠ idx' → rest[j]? = some fv' → fv'.1.kept = false :=
        fun j fv' hne hj => hother (j + 1) fv' (by omega) (by simpa using hj)
      have ⟨ihErr, ihOk⟩ := ih (out.push (.imm .irr)) idx' hget hother'
      constructor
      · intro e herr
        unfold constructLoop
        simp only [hfv, Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run]
        exact ihErr e herr
      · intro v1 st₁ hok
        unfold constructLoop
        simp only [hfv, Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run]
        obtain ⟨out', hrun, hget'⟩ := ihOk v1 st₁ hok
        have hidx : (out.push (.imm .irr)).size + idx' = out.size + (idx' + 1) := by simp; omega
        rw [hidx] at hget'
        exact ⟨out', hrun, hget'⟩

private theorem construct_ownReach {P : Prog} {r ind : Ref} {tag nP : Nat}
    {fields : Array Field} {vs : List Val} {c : Cls} {st st' : St} {rv : Val}
    (hfind : P.find? r = some (.ctor ind tag nP fields))
    (hc : CapsOk st.heap)
    (hvs : ∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
      DeepLive st.heap v ∧ AcyclicFrom st.heap v)
    (hrun : (construct r fields vs c).run st = .ok (rv, st')) :
    ∀ l, OwnReach P st'.heap rv l →
      st.heap.objs.size ≤ l ∨
      ∃ (i : Nat) (f : Field) (v : Val), fields[i]? = some f ∧ vs[i]? = some v ∧
        f.kept = true ∧ f.fmode = .inherited ∧ OwnReach P st.heap v l := by
  have hxs : ∀ fv ∈ fields.toList.zip vs, fv.1.kept = true →
      DeepLive st.heap fv.2 ∧ AcyclicFrom st.heap fv.2 := by
    intro fv hmem hfk
    obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hmem
    have hk' : k < min fields.size vs.length := by simpa [List.length_zip] using hk
    have hkf : k < fields.size := Nat.lt_of_lt_of_le hk' (Nat.min_le_left ..)
    have hkv : k < vs.length := Nat.lt_of_lt_of_le hk' (Nat.min_le_right ..)
    have h1 : fields[k]? = some fv.1 := by
      rw [Array.getElem?_eq_getElem hkf]; have := congrArg Prod.fst heq; simpa [List.getElem_zip] using this
    have h2 : vs[k]? = some fv.2 := by
      rw [List.getElem?_eq_getElem hkv]; have := congrArg Prod.snd heq; simpa [List.getElem_zip] using this
    exact hvs k fv.1 fv.2 h1 h2 hfk
  unfold construct at hrun
  rw [M_bind_run] at hrun
  erw [forIn_list_constructLoop] at hrun
  rcases constructLoop_spec (P := P) (out := #[]) hc (fun _ h => by simp at h) hxs with hSt |
    ⟨out, stL, hrunL, _, _, _, _, hszL, _, _, hcL, houtSz, _, _, hitems⟩
  · rw [hSt] at hrun; cases hrun
  · rw [hrunL] at hrun; dsimp only at hrun
    let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
    by_cases hke : kept.isEmpty = true
    · simp only [kept, hke, ↓reduceIte, M_pure_run] at hrun
      cases hrun
      intro l hr; cases hr
    · simp only [kept, hke, Bool.false_eq_true, ↓reduceIte] at hrun
      by_cases hwrap : ((c == .imm || c == .leaf) && kept.size == 1) = true
      · simp only [kept, hwrap, ↓reduceIte] at hrun
        cases hk0 : kept[0]? with
        | none => simp only [kept, hk0] at hrun; change Except.error _ = Except.ok _ at hrun; cases hrun
        | some idx =>
          cases ho0 : out[idx]? with
          | none => simp only [kept, hk0, ho0] at hrun; change Except.error _ = Except.ok _ at hrun; cases hrun
          | some v0 =>
            simp only [kept, hk0, ho0] at hrun
            have hcIL : c = .imm ∨ c = .leaf := by
              cases hcC : c <;> rw [hcC] at hwrap <;>
                simp only [Bool.and_eq_true, Bool.or_eq_true] at hwrap
              · rcases hwrap.1 with h | h <;> cases h
              · exact Or.inl rfl
              · exact Or.inr rfl
              · rcases hwrap.1 with h | h <;> cases h
            have hidxLt : idx < min fields.size vs.length := by
              have hlt : idx < out.size := (Array.getElem?_eq_some_iff.mp ho0).1
              simpa [houtSz, List.length_zip] using hlt
            have hidxF : idx < fields.size := Nat.lt_of_lt_of_le hidxLt (Nat.min_le_left ..)
            have hidxV : idx < vs.length := Nat.lt_of_lt_of_le hidxLt (Nat.min_le_right ..)
            have hgetZip : (fields.toList.zip vs)[idx]? = some (fields[idx], vs[idx]) := by
              rw [List.getElem?_eq_getElem (by simpa [List.length_zip] using hidxLt)]
              simp [List.getElem_zip]
            obtain ⟨w, hwGet, hwdl, hwacyc, _, _, _, _, _, _⟩ := hitems idx fields[idx] vs[idx] hgetZip
            have hwEq : w = v0 := Option.some.inj ((by simpa using hwGet : out[idx]? = some w).symm.trans ho0)
            subst hwEq
            rcases conform_spec_full (P := P) hcL hwdl hwacyc (c := c) with hStC |
              ⟨vC, stC, hrunC, _, _, _, _, _, _, _, _, _, hclsC, _, _, _, _, _, _⟩
            · rw [hStC] at hrun; cases hrun
            · rw [hrunC] at hrun; cases hrun
              intro l hor
              rcases hcIL with rfl | rfl
              · obtain ⟨_, hEq⟩ := hclsC; rw [hEq] at hor; cases hor
              · obtain ⟨loc, cap, o, n, hEq, ho, hnum, _⟩ := hclsC
                rw [hEq] at hor
                cases hor with
                | here ho' hn =>
                  rw [ho] at ho'; cases ho'
                  rcases hn with hn | hn
                  · rw [hnum] at hn; cases hn
                  · exact absurd rfl hn
                | step ho' hi _ _ => rw [ho] at ho'; cases ho'; rw [hnum] at hi; cases hi
      · simp only [kept, hwrap, Bool.false_eq_true, ↓reduceIte] at hrun
        unfold alloc at hrun
        simp only [StateT.run, get, set, MonadStateOf.set, pure, Pure.pure, bind, Bind.bind] at hrun
        cases hrun
        intro l hor
        cases hor with
        | here _ _ => exact Or.inl hszL
        | step ho hi hslot horW =>
          simp only [Array.getElem?_push_size, Option.some.injEq] at ho
          subst ho
          have hStep : ∃ (idx : Nat) (w0 : Val),
              idx ∈ ownedSlots P (.ctor r out) ∧
              (Cell.ctor r out).slot? idx = some w0 ∧
              OwnReach P { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                           nextCap := stL.heap.nextCap + 1 } w0 l := ⟨_, _, hi, hslot, horW⟩
          obtain ⟨idx, w0, hi, hslot, horW⟩ := hStep
          dsimp only [Cell.slot?] at hslot
          have hctorOf : P.ctorOf? r = some (ind, tag, nP, fields) := by
            unfold Prog.ctorOf?; rw [hfind]
          simp only [ownedSlots, hctorOf, List.mem_filter, List.mem_range] at hi
          obtain ⟨hiLt, hiFmode⟩ := hi
          have hiMin : idx < min fields.size vs.length := by simpa [houtSz, List.length_zip] using hiLt
          have hiF : idx < fields.size := Nat.lt_of_lt_of_le hiMin (Nat.min_le_left ..)
          have hiV : idx < vs.length := Nat.lt_of_lt_of_le hiMin (Nat.min_le_right ..)
          have hfEq : fields[idx]?.map (·.fmode == .inherited) = some (fields[idx].fmode == .inherited) := by
            rw [Array.getElem?_eq_getElem hiF]; rfl
          rw [hfEq] at hiFmode
          dsimp only [Option.getD] at hiFmode
          have hfInh : fields[idx].fmode = .inherited := by
            cases hm : fields[idx].fmode with
            | inherited => rfl
            | shared => rw [hm] at hiFmode; cases hiFmode
          have hgetZip : (fields.toList.zip vs)[idx]? = some (fields[idx], vs[idx]) := by
            rw [List.getElem?_eq_getElem (by simpa [List.length_zip] using hiMin)]
            simp [List.getElem_zip]
          obtain ⟨w, hwGet, hwdl, _, _, _, hwown, _, _, _⟩ := hitems idx fields[idx] vs[idx] hgetZip
          have hwEq : w = w0 := Option.some.inj ((by simpa using hwGet : out[idx]? = some w).symm.trans hslot)
          subst hwEq
          have hpW : PreservesLocs (Reach stL.heap w) stL.heap
              { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩, nextCap := stL.heap.nextCap + 1 } :=
            (alloc_preserves_old (.ctor r out) (taints out.toList) stL).mono fun x hx => hwdl.reach_lt_size hx
          have horL : OwnReach P stL.heap w l := (OwnReach_congr hpW l).mp horW
          obtain ⟨hfk, hor0⟩ := hwown l horL
          exact Or.inr ⟨idx, fields[idx], vs[idx], Array.getElem?_eq_getElem hiF, List.getElem?_eq_getElem hiV,
            hfk, hfInh, hor0⟩

/-- **Bridge 3 (`ctor_sat_bridge`)**: simulates saturated `ATerm.appConst` on a constructor
(`Runs (anCtor nP fields avs.toArray c) σ res σ'` with `nP + fields.size ≤ avs.length`)
against `Eval.construct r fields (vs.drop nP) c`. -/
theorem ctor_sat_bridge {P : Prog} {ext : ExternOracle} {B : Nat}
    {r ind : Ref} {tag nP : Nat} {fields : Array Field} {c : Cls}
    {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {res : AVal}
    (hfind : P.find? r = some (.ctor ind tag nP fields))
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hBadDep : ∀ d, BadDep d → σ'.st[d]? = some .live)
    (hvsLen : vs.length = args.length)
    (havsLen : avs.length = args.length)
    (hsat : nP + fields.size ≤ args.length)
    (hargsSync : ∀ (i : Nat),
      (args[i]? = some none → avs[i]? = some none) ∧
      (∀ v av ft, args[i]? = some (some (v, av, ft)) → vs[i]? = some v ∧ avs[i]? = some (some av)))
    (hkeptPresent : ∀ (k : Nat) (f : Field), fields[k]? = some f → f.kept = true →
      ∃ v av ft, args[nP + k]? = some (some (v, av, ft)))
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args)
    (hrunC : Runs (anCtor nP fields avs.toArray c) σ res σ') :
    (construct r fields (vs.drop nP) c).run st = .error .stuck ∨
    ∃ rv st' rFoot, (construct r fields (vs.drop nP) c).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
      EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
      VSim P ext B st' Frame NoKill NoSpend σ' I rFoot res rv ∧
      ValEnvDisj P st' NoKill Scope env aenv σ' envFoot rFoot res rv ∧
      (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
      (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) := by
  have hsatAvs : nP + fields.size ≤ avs.toArray.size := by simpa [havsLen] using hsat
  obtain ⟨hok', hle, hstSz, honceEq, hspSz, hregEq, hnrEq, _, hsatInfo⟩ := Runs_anCtor hsim.2.1 hrunC
  obtain ⟨hEmptyInfo, hWrapInfo, hAllocInfo⟩ := hsatInfo hsatAvs
  let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
  have hdropGet : ∀ (k : Nat) (v : Val), vs[nP + k]? = some v → (vs.drop nP)[k]? = some v := by
    intro k v h
    rwa [List.getElem?_drop]
  by_cases hke : kept.isEmpty = true
  · obtain ⟨hσEq, hresEq⟩ := hEmptyInfo hke
    subst σ'; subst hresEq
    have hallNK : ∀ fv ∈ fields.toList.zip (vs.drop nP), fv.1.kept = false := by
      intro fv hmem
      obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hmem
      have hk' : k < min fields.size (vs.drop nP).length := by simpa [List.length_zip] using hk
      have hkf : k < fields.size := Nat.lt_of_lt_of_le hk' (Nat.min_le_left ..)
      have h1 : fields[k]? = some fv.1 := by
        rw [Array.getElem?_eq_getElem hkf]; have := congrArg Prod.fst heq; simpa [List.getElem_zip] using this
      cases hfk : fv.1.kept with
      | false => rfl
      | true =>
        have hmemK : k ∈ kept.toList := (kept_mem_iff fields k).mpr ⟨fv.1, h1, hfk⟩
        have hpos : 0 < kept.size := by
          have := List.length_pos_of_mem hmemK; simpa using this
        have hsz0 : kept.size = 0 := by simpa [Array.isEmpty] using hke
        omega
    obtain ⟨out, hrunL, _, _⟩ := constructLoop_all_not_kept (fields.toList.zip (vs.drop nP)) #[] st hallNK
    have hrunE : (construct r fields (vs.drop nP) c).run st = .ok (.imm (.con r), st) := by
      unfold construct
      rw [M_bind_run]
      erw [forIn_list_constructLoop]
      rw [hrunL]
      simp only [kept, hke, ↓reduceIte, M_pure_run]
    have hnv : NonValSafe st.heap (.imm (.con r)) := Or.inl ⟨.con r, rfl⟩
    right
    refine ⟨.imm (.con r), st, fun _ => False, hrunE,
      rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _, hst,
      hsim, henvNRF,
      VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl (ValBaseOk_imm st (.con r)) hnv,
      ValEnvDisj_nonValSafe rfl hnv hsim,
      fun _ => NoReachForbid_nonValSafe hnv,
      fun _ _ => ⟨ValBaseOk_imm st (.con r), hnv⟩⟩
  · have hkeF : kept.isEmpty = false := Bool.eq_false_iff.mpr hke
    by_cases hwrap : ((c == .imm || c == .leaf) && kept.size == 1) = true
    · obtain ⟨hσEq, hwrapMatch⟩ := hWrapInfo hkeF hwrap
      subst σ'
      have hksz : kept.size = 1 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hwrap; exact hwrap.2
      have hcIL : c = .imm ∨ c = .leaf := by
        cases hcC : c <;> rw [hcC] at hwrap <;> simp only [Bool.and_eq_true, Bool.or_eq_true] at hwrap
        · rcases hwrap.1 with h | h <;> cases h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases hwrap.1 with h | h <;> cases h
      have h0lt : 0 < kept.size := by omega
      let idx := kept[0]
      have hk0 : kept[0]? = some idx := Array.getElem?_eq_getElem h0lt
      have hk0Bang : kept[0]! = idx := by simp [idx, h0lt]
      have hidxMem : idx ∈ kept.toList := Array.mem_toList_iff.mpr (Array.getElem_mem h0lt)
      obtain ⟨f0, hf0, hf0Kept⟩ := (kept_mem_iff fields idx).mp hidxMem
      obtain ⟨v0, av0, ft0, harg0⟩ := hkeptPresent idx f0 hf0 hf0Kept
      have ⟨hv0, hav0⟩ := (hargsSync (nP + idx)).2 v0 av0 ft0 harg0
      have hav0Arr : avs.toArray[nP + kept[0]!]? = some (some av0) := by
        rw [hk0Bang]; simpa using hav0
      rw [hav0Arr] at hwrapMatch
      obtain ⟨hvd0, hresEq⟩ := hwrapMatch
      have hidxF : idx < fields.size := (Array.getElem?_eq_some_iff.mp hf0).1
      have hidxV : idx < (vs.drop nP).length := by
        rw [List.length_drop, hvsLen]; omega
      have hzipGet : (fields.toList.zip (vs.drop nP))[idx]? = some (f0, v0) := by
        rw [List.getElem?_eq_getElem (by simp [List.length_zip]; omega)]
        have h1 : fields[idx] = f0 := Option.some.inj ((Array.getElem?_eq_getElem hidxF).symm.trans hf0)
        have h2 : (vs.drop nP)[idx] = v0 :=
          Option.some.inj ((List.getElem?_eq_getElem hidxV).symm.trans (hdropGet idx v0 hv0))
        simp [List.getElem_zip, h1, h2]
      have hother : ∀ (j : Nat) fv, j ≠ idx → (fields.toList.zip (vs.drop nP))[j]? = some fv → fv.1.kept = false := by
        intro j fv hjne hjget
        have hjlt : j < min fields.size (vs.drop nP).length := by
          have := (List.getElem?_eq_some_iff.mp hjget).1; simpa [List.length_zip] using this
        have hjf : j < fields.size := Nat.lt_of_lt_of_le hjlt (Nat.min_le_left ..)
        have hfj : fields[j]? = some fv.1 := by
          rw [Array.getElem?_eq_getElem hjf]
          have := Option.some.inj ((List.getElem?_eq_getElem (by simpa [List.length_zip] using hjlt)).symm.trans hjget)
          have h1 := congrArg Prod.fst this; simpa [List.getElem_zip] using h1
        cases hkJ : fv.1.kept with
        | false => rfl
        | true =>
          have hjMem : j ∈ kept.toList := (kept_mem_iff fields j).mpr ⟨fv.1, hfj, hkJ⟩
          obtain ⟨m, hm, hgetM⟩ := List.getElem_of_mem hjMem
          have hm0 : m = 0 := by simp [hksz] at hm; omega
          subst hm0
          have hjEq : j = idx := by simpa [idx] using hgetM.symm
          exact absurd hjEq hjne
      have ⟨hloopErr, hloopOk⟩ :=
        constructLoop_single_kept (fields.toList.zip (vs.drop nP)) #[] st idx f0 v0 hzipGet hf0Kept hother
      have hrunEq : ∀ st', (construct r fields (vs.drop nP) c).run st' = (construct r fields (vs.drop nP) c).run st' := fun _ => rfl
      have hwrapEval :
          ((conform f0.cls v0).run st = .error .stuck → (construct r fields (vs.drop nP) c).run st = .error .stuck) ∧
          (∀ v1 st₁, (conform f0.cls v0).run st = .ok (v1, st₁) →
            (construct r fields (vs.drop nP) c).run st = (conform c v1).run st₁) := by
        constructor
        · intro herr
          unfold construct; rw [M_bind_run]; erw [forIn_list_constructLoop]
          rw [hloopErr .stuck herr]
        · intro v1 st₁ hok1
          obtain ⟨out, hrunL, houtIdx⟩ := hloopOk v1 st₁ hok1
          have houtIdx' : out[idx]? = some v1 := by simpa using houtIdx
          unfold construct; rw [M_bind_run]; erw [forIn_list_constructLoop]
          rw [hrunL]; dsimp only
          simp only [kept, hkeF, Bool.false_eq_true, ↓reduceIte, hwrap, hk0, houtIdx']
      obtain ⟨hv0Sim, _, _, _⟩ := hargs.1 (nP + idx) v0 av0 ft0 harg0
      have hresRegs : ∀ rg ∈ res.regs, rg < σ.nextRegion := by rw [hresEq]; exact hv0Sim.1
      have hresDeps : ∀ d ∈ res.deps, d < σ.st.size := by rw [hresEq]; exact hv0Sim.2.1
      have hresSrc : res.src = none := by rw [hresEq]
      by_cases ha0 : ActiveVal σ av0
      · have hv0Act := hv0Sim.2.2.2.2 ha0
        have hconf1 :
            (conform f0.cls v0).run st = .error .stuck ∨
            ∃ v1 st₁, (conform f0.cls v0).run st = .ok (v1, st₁) ∧
              st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
              st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
              st.heap.objs.size ≤ st₁.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
              PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap ∧
              PreservesOnceShell st.heap st₁.heap ∧ StaticStrFresh st st₁ ∧
              StOk P ext B st₁ ∧ ValBaseOk st₁ v1 ∧ CtorFieldsOk P ext B st₁ v1 := by
          by_cases hoo : av0.onceOnly = true
          · rcases conform_sound (P := P) (ext := ext) (B := B) (c := f0.cls) (sk := av0.skel)
                (onceOnly := true) (Foot := ft0) hst hv0Act.1 hv0Act.2.2.1 (fun h => by cases h)
                (hv0Act.2.2.2.2.2.1 hoo).2.2.2 with
              hSt1 | ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, _, hcf1, _, _, _, _, _, _, _, _⟩
            · exact Or.inl hSt1
            · exact Or.inr ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, hcf1⟩
          · have hooF : av0.onceOnly = false := Bool.eq_false_iff.mpr hoo
            by_cases his : IsOnceSrc σ av0
            · rcases conform_sound (P := P) (ext := ext) (B := B) (c := f0.cls) (sk := av0.skel)
                  (onceOnly := true) (Foot := ft0) hst hv0Act.1 hv0Act.2.2.1 (fun h => by cases h)
                  (hv0Act.2.2.2.2.2.2.1 his).2.2 with
                hSt1 | ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, _, hcf1, _, _, _, _, _, _, _, _⟩
              · exact Or.inl hSt1
              · exact Or.inr ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, hcf1⟩
            · have hplain := hv0Act.2.2.2.2.1 ⟨his, hooF⟩
              rcases conform_sound (P := P) (ext := ext) (B := B) (c := f0.cls) (sk := av0.skel)
                  (onceOnly := false) (Foot := fun _ => False) hst hv0Act.1 hv0Act.2.2.1 (fun _ => hplain.1) hplain.2.2 with
                hSt1 | ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, _, hcf1, _, _, _, _, _, _, _, _⟩
              · exact Or.inl hSt1
              · exact Or.inr ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, hcf1⟩
        rcases hconf1 with hSt1 | ⟨v1, st₁, hr1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1, hst1, hbv1, hcf1⟩
        · exact Or.inl (hwrapEval.1 hSt1)
        · rw [hwrapEval.2 v1 st₁ hr1]
          have hcNe : c ≠ .val := by rcases hcIL with rfl | rfl <;> decide
          rcases conform_spec_full (P := P) hst1.1 hbv1.1 hbv1.2.1 (c := c) with hSt2 |
            ⟨rv, st', hr2, hrg2, hnr2, hstat2, hstr2, hsz2, hcap2, hp2, hc', hdl', hcls', hacyc', _, _, _, _, _⟩
          · exact Or.inl hSt2
          · right
            have hp02 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
              hp1.trans (hp2.mono fun l hl => Nat.lt_of_lt_of_le hl hsz1)
            have hos2 : PreservesOnceShell st₁.heap st'.heap :=
              PreservesOnceShell.of_preservesLocs (hp2.mono fun l ⟨o, _, _, ho, _⟩ => (Array.getElem?_eq_some_iff.mp ho).1)
            have hssf2 : StaticStrFresh st₁ st' :=
              StaticStrFresh_of_preserves_outside (S := fun _ => False) hst1 hstat2 hstr2
                (hp2.mono fun _ h => h.1) (fun _ _ h => h)
            have hos02 : PreservesOnceShell st.heap st'.heap := hos1.trans hos2
            have hssf02 : StaticStrFresh st st' := StaticStrFresh.trans hsz1 (hp2.mono fun l hl => StaticStrLoc_lt_size hst1 hl) hssf1 hssf2
            have hst' : StOk P ext B st' :=
              StOk_of_preserves_old hst1 hc' hrg2 (hnr2 ▸ Nat.le_refl _) hstat2 hstr2 hp2
            have hnv : NonValSafe st'.heap rv := ClsSafe.to_nonValSafe hcNe (ClsSafe.of_clsOk hcls') hdl'.self.1
            have htb' : DeepTaintsBounded st'.heap st'.nextRegion rv := by
              rcases hnv with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hcell⟩
              · exact DeepTaintsBounded_imm _ _ _
              · exact DeepTaintsBounded_num ho hcell
            have hbase' : ValBaseOk st' rv := ValBaseOk_of_deepLive hdl' hacyc' htb'
            have hrf02 : RegsFuture st st' :=
              RegsFuture.same_regions ((hnr2.trans hnr1) ▸ Nat.le_refl _) (hrg2.trans hrg1)
            have hIok02 : InterpOk σ st' I :=
              ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hsim.2.2.1.1 rg hlt c hc) hrf02.1,
               fun rc hrc => hsim.2.2.1.2 rc ((hrg2.trans hrg1) ▸ hrc)⟩
            have hpEnv02 : PreservesActiveEnv Scope env aenv σ st.heap st'.heap := fun i b ab hsc hbi habi hne haB =>
              hp02.mono fun l hl => (((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.2.2.2.2 haB).1.1.reach_lt_size hl
            have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1
              hIok02 hrf02 hos02 hssf02 (fun _ _ _ h => h) hpEnv02 hsim
            have hpSS02 : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
              hp02.mono fun l hss => StaticStrLoc_lt_size hst hss
            have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim)
              hsim.2.2.2.1 ((hstat2.trans hstat1) ▸ ArrayExtends.refl _) ((hstr2.trans hstr1) ▸ ArrayExtends.refl _)
              hpSS02 hpEnv02 henvNRF
            exact ⟨rv, st', fun _ => False, hr2, hrg2.trans hrg1, hnr2.trans hnr1,
              hstat2.trans hstat1, hstr2.trans hstr1, Nat.le_trans hsz1 hsz2, Nat.le_trans hcap1 hcap2,
              hp02, hos02, hssf02, hst', hsim', henvNRF',
              VSim_nonValSafe hresRegs hresDeps hresSrc hbase' hnv,
              ValEnvDisj_nonValSafe hresSrc hnv hsim',
              fun _ => NoReachForbid_nonValSafe hnv,
              fun _ _ => ⟨hbase', hnv⟩⟩
      · have his0 : IsOnceSrc σ av0 := by
          exact Classical.byContradiction fun hnot => ha0 ⟨hvd0, fun his => absurd his hnot⟩
        have hsp0 : SpentOnceSafe st.heap v0 := hv0Sim.2.2.2.1 hvd0 his0
        rcases conform_spentOnceSafe (c := f0.cls) hsp0 with hSt1 | ⟨v1, hr1, hv1Case⟩
        · exact Or.inl (hwrapEval.1 hSt1)
        · rw [hwrapEval.2 v1 st hr1]
          have hsp1 : SpentOnceSafe st.heap v1 := by
            rcases hv1Case with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact hsp0
            · exact Or.inl rfl
          rcases conform_spentOnceSafe (c := c) hsp1 with hSt2 | ⟨rv, hr2, hrvCase⟩
          · exact Or.inl hSt2
          · have hrvIrr : rv = .imm .irr := by
              rcases hrvCase with ⟨_, hcv⟩ | ⟨rfl, _⟩
              · rcases hcIL with rfl | rfl <;> cases hcv
              · rfl
            subst hrvIrr
            have hnv : NonValSafe st.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
            right
            exact ⟨.imm .irr, st, fun _ => False, hr2, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
              PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _, hst, hsim, henvNRF,
              VSim_nonValSafe hresRegs hresDeps hresSrc (ValBaseOk_imm st .irr) hnv,
              ValEnvDisj_nonValSafe hresSrc hnv hsim,
              fun _ => NoReachForbid_nonValSafe hnv,
              fun _ _ => ⟨ValBaseOk_imm st .irr, hnv⟩⟩
    · have hwrapF : ((c == .imm || c == .leaf) && kept.size == 1) = false := Bool.eq_false_iff.mpr hwrap
      obtain ⟨hresCls, hresSkel, hresOO, hresSrc, hkeptInfo, huniqInfo, hresDeps, hresRegs, hspUpd, hstUpd⟩ :=
        hAllocInfo hkeF hwrapF
      have hfieldInfo : ∀ (k : Nat) (f : Field) (v : Val),
          fields[k]? = some f → (vs.drop nP)[k]? = some v → f.kept = true →
          ∃ av ft, args[nP + k]? = some (some (v, av, ft)) ∧
            avs.toArray[nP + k]? = some (some av) ∧
            k ∈ kept.toList ∧
            ValidDeps σ av.deps ∧ av.onceOnly = false ∧ Skel.unknown.admits av.skel = true ∧
            (∀ rg ∈ av.regs, rg ∈ res.regs) ∧
            (f.fmode = .shared → (∀ rg ∈ av.regs, rg = 1) ∧ ¬ IsOnceSrc σ av) ∧
            (f.fmode = .inherited → av.cls = .val → ¬ IsOnceSrc σ av ∧ (∀ d ∈ av.deps, d ∈ res.deps)) := by
        intro k f v hfk hvk hkept
        obtain ⟨v', av, ft, hargK⟩ := hkeptPresent k f hfk hkept
        have ⟨hv', hav'⟩ := (hargsSync (nP + k)).2 v' av ft hargK
        have hvEq : v' = v := Option.some.inj ((hdropGet k v' hv').symm.trans hvk)
        subst hvEq
        have havArr : avs.toArray[nP + k]? = some (some av) := by simpa using hav'
        have hkMem : k ∈ kept.toList := (kept_mem_iff fields k).mpr ⟨f, hfk, hkept⟩
        obtain ⟨hvd, hoo, hadm, hrg, hsh, hinh⟩ := hkeptInfo k hkMem av f havArr hfk
        exact ⟨av, ft, hargK, havArr, hkMem, hvd, hoo, hadm, hrg, hsh, hinh⟩
      have hvsOk : ∀ (k : Nat) (f : Field) (v : Val),
          fields[k]? = some f → (vs.drop nP)[k]? = some v → f.kept = true →
          ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext B st v ∧
          FunOkAt P ext B st .unknown false (fun _ => False) v ∧
          DeepOpenUnder st.heap st.regions (I.regsOf res.regs) v := by
        intro k f v hfk hvk hkept
        obtain ⟨av, ft, hargK, _, _, hvd, hoo, hadm, hrg, hsh, hinh⟩ := hfieldInfo k f v hfk hvk hkept
        obtain ⟨hvSim, _, _, hnvIf⟩ := hargs.1 (nP + k) v av ft hargK
        by_cases hcV : av.cls = .val
        · have hnotOnce : ¬ IsOnceSrc σ av := by
            cases hfm : f.fmode with
            | shared => exact (hsh hfm).2
            | inherited => exact (hinh hfm hcV).1
          have haK : ActiveVal σ av := ⟨hvd, fun his => absurd his hnotOnce⟩
          have hvAct := hvSim.2.2.2.2 haK
          have hplain := hvAct.2.2.2.2.1 ⟨hnotOnce, hoo⟩
          have hadmSym : av.skel.admits .unknown = true := by rw [Skel.admits_symm]; exact hadm
          refine ⟨hvAct.1, hplain.1, hvAct.2.2.1, FunOkAt_of_admits hadmSym hplain.2.2, ?_⟩
          intro w hw rg hrgM hopen
          obtain ⟨rg', hrg', hmem'⟩ := List.mem_flatMap.mp (hvAct.2.1 w hw rg hrgM hopen)
          exact List.mem_flatMap.mpr ⟨rg', hrg rg' hrg', hmem'⟩
        · obtain ⟨hbv, hnv⟩ := hnvIf hvd hcV
          exact ⟨hbv, hnv.noOnceCell, hnv.ctorFieldsOk P ext B st,
            hnv.funOkAt P ext B st .unknown, hnv.deepOpenUnder_nil⟩
      rcases construct_sound (P := P) (ext := ext) (B := B) (r := r) (fields := fields) (vs := vs.drop nP) (c := c)
          hst (fun k f v hfk hvk hkept => let h := hvsOk k f v hfk hvk hkept; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) with
        hSt | ⟨rv, st', hrunE, hrg', hnr', hstat', hstr', hsz', hcap', hp', _, hos', hssf',
          hst', hbase', hno', hcf', hfun', hdou', hreach', _, htree'⟩
      · exact Or.inl hSt
      · right
        have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hrg'
        have hIok' : InterpOk σ' st' I :=
          ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hsim.2.2.1.1 rg (hnrEq ▸ hlt) c hc) hrf'.1,
           fun rc hrc => by rw [hregEq]; exact hsim.2.2.1.2 rc (hrg' ▸ hrc)⟩
        have hpEnv0 : PreservesActiveEnv Scope env aenv σ st.heap st'.heap := fun i b ab hsc hbi habi hne haB =>
          hp'.mono fun l hl => (((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.2.2.2.2 haB).1.1.reach_lt_size hl
        have hpEnv' : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap := fun i b ab hsc hbi habi hne haB' =>
          let hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
          hpEnv0 i b ab hsc hbi habi hne (ActiveVal.of_AStateLe hsim.2.1 hle hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) haB')
        have hsim' := Sim_step (Nat.le_refl B) hle hok' hIok' hrf' hos' hssf' (fun _ _ _ h => h) hpEnv' hsim
        have hpSS' : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
          hp'.mono fun l hss => StaticStrLoc_lt_size hst hss
        have henvNRF' := EnvNoReachForbid_step hsim.2.1 hle (Sim_deps_lt hsim)
          hsim.2.2.2.1 (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hpEnv' henvNRF
        have hresRegsLt : ∀ rg ∈ res.regs, rg < σ'.nextRegion := by
          intro rg hrg
          obtain ⟨k, _, v, f, havK, hfk, hrgV⟩ := hresRegs rg hrg
          have hkept : f.kept = true := by
            obtain ⟨f', hf', hk'⟩ := (kept_mem_iff fields k).mp ‹_›; rw [hfk] at hf'; cases hf'; exact hk'
          obtain ⟨v0, av0, ft0, hargK⟩ := hkeptPresent k f hfk hkept
          have ⟨_, hav0⟩ := (hargsSync (nP + k)).2 v0 av0 ft0 hargK
          have havEq : av0 = v := Option.some.inj (Option.some.inj ((by simpa using hav0 : avs.toArray[nP + k]? = some (some av0)).symm.trans havK))
          subst havEq
          rw [hnrEq]; exact (hargs.1 (nP + k) v0 av0 ft0 hargK).1.1 rg hrgV
        have hresDepsLt : ∀ d ∈ res.deps, d < σ'.st.size := by
          intro d hd
          obtain ⟨k, _, v, f, havK, hfk, _, _, hdV⟩ := hresDeps d hd
          have hkept : f.kept = true := by
            obtain ⟨f', hf', hk'⟩ := (kept_mem_iff fields k).mp ‹_›; rw [hfk] at hf'; cases hf'; exact hk'
          obtain ⟨v0, av0, ft0, hargK⟩ := hkeptPresent k f hfk hkept
          have ⟨_, hav0⟩ := (hargsSync (nP + k)).2 v0 av0 ft0 hargK
          have havEq : av0 = v := Option.some.inj (Option.some.inj ((by simpa using hav0 : avs.toArray[nP + k]? = some (some av0)).symm.trans havK))
          subst havEq
          rw [hstSz]; exact (hargs.1 (nP + k) v0 av0 ft0 hargK).1.2.1 d hdV
        have hnotOnceRes : ¬ IsOnceSrc σ' res := by rintro ⟨_, hs, _⟩; rw [hresSrc] at hs; cases hs
        have hctorOf : P.ctorOf? r = some (ind, tag, nP, fields) := by unfold Prog.ctorOf?; rw [hfind]
        have hownReach := construct_ownReach hfind hst.1
          (fun k f v hfk hvk hkept => let h := hvsOk k f v hfk hvk hkept; ⟨h.1.1, h.1.2.1⟩) hrunE
        have htrV : Transferable σ' NoKill res →
            OwnTreeFull P st'.heap rv ∧
            ∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l := by
          intro htrRes
          have htrOwn : res.own = .uniq := htrRes.2.1
          obtain ⟨huField, huDisj⟩ := huniqInfo htrOwn
          have hfieldTr : ∀ (k : Nat) (f : Field) (v : Val) (av : AVal) (ft : Nat → Prop),
              fields[k]? = some f → (vs.drop nP)[k]? = some v → f.kept = true →
              f.fmode = .inherited → args[nP + k]? = some (some (v, av, ft)) → av.cls = .val →
              ActiveVal σ av ∧ Transferable σ NoKill av := by
            intro k f v av ft hfk hvk hkept hinh hargK hcV
            obtain ⟨av', ft', hargK', havArr, hkMem, hvd, hoo, _, _, _, hinhInfo⟩ := hfieldInfo k f v hfk hvk hkept
            have hEq := Option.some.inj (Option.some.inj (hargK'.symm.trans hargK))
            have havEq : av' = av := congrArg (fun p => p.2.1) hEq
            subst av'
            obtain ⟨hnoSrc, hsubDeps⟩ := hinhInfo hinh hcV
            obtain ⟨havOwn, havLive⟩ := huField k hkMem av f havArr hfk hinh hcV
            refine ⟨⟨hvd, fun his => absurd his hnoSrc⟩, hcV, havOwn, hoo, hnoSrc, ?_⟩
            intro d hd
            exact ⟨havLive d hd, (htrRes.2.2.2.2 d (hsubDeps d hd)).2⟩
          refine ⟨htree' ⟨ind, tag, nP, hctorOf⟩ ?_ ?_, ?_⟩
          · intro k f v hfk hvk hkept hinh
            obtain ⟨av, ft, hargK, _, _, hvd, _, _, _, _, _⟩ := hfieldInfo k f v hfk hvk hkept
            by_cases hcV : av.cls = .val
            · obtain ⟨haK, htrK⟩ := hfieldTr k f v av ft hfk hvk hkept hinh hargK hcV
              exact ((hargs.1 (nP + k) v av ft hargK).1.2.2.2.2 haK).2.2.2.2.2.2.2 htrK |>.1
            · exact ((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.ownTreeFull.1
          · intro i j fi vi fj vj hij hfi hvi hfj hvj hki hkj hfiInh l horI hrJ
            obtain ⟨avi, fti, hargi, haviArr, hkiMem, hvdi, _, _, _, _, hinhI⟩ := hfieldInfo i fi vi hfi hvi hki
            obtain ⟨avj, ftj, hargj, havjArr, hkjMem, hvdj, _, _, _, hshJ, hinhJ⟩ := hfieldInfo j fj vj hfj hvj hkj
            by_cases hci : avi.cls = .val
            · by_cases hcj : avj.cls = .val
              · obtain ⟨haI, htrI⟩ := hfieldTr i fi vi avi fti hfi hvi hki hfiInh hargi hci
                have haJ : ActiveVal σ avj := by
                  cases hfm : fj.fmode with
                  | shared => exact ⟨hvdj, fun his => absurd his (hshJ hfm).2⟩
                  | inherited => exact ⟨hvdj, fun his => absurd his (hinhJ hfm hcj).1⟩
                have hdisjDeps : ∀ d, d ∈ avi.deps → ¬ (d ∈ avj.deps) := by
                  intro d hdi hdj
                  cases hfm : fj.fmode with
                  | inherited => exact huDisj i hkiMem j hkjMem hij avi fi avj fj haviArr hfi havjArr hfj hfiInh hci hfm hcj d hdi hdj
                  | shared =>
                    have hdSub := (hinhI hfiInh hci).2 d hdi
                    have hdLive' := (htrRes.2.2.2.2 d hdSub).1
                    have hdLive0 := (htrI.2.2.2.2 d hdi).1
                    have hdLt : d < σ.st.size := (hargs.1 (nP + i) vi avi fti hargi).1.2.1 d hdi
                    have hUpd := hstUpd d hdLt
                    have hcond : (∃ k ∈ kept.toList, ∃ v f, avs.toArray[nP + k]? = some (some v) ∧
                        fields[k]? = some f ∧ f.fmode = .shared ∧ v.cls = .val ∧ d ∈ v.deps) ∧ σ.st[d]? = some .live :=
                      ⟨⟨j, hkjMem, avj, fj, havjArr, hfj, hfm, hcj, hdj⟩, hdLive0⟩
                    split at hUpd
                    · rw [hdLive'] at hUpd; cases hUpd
                    · exact absurd hcond ‹_›
                exact (hargs.2 (nP + i) (nP + j) vi vj avi avj fti ftj (by omega) hargi hargj).1 haI htrI haJ hdisjDeps l horI hrJ
              · exact OwnReach_not_numLoc horI (((hargs.1 (nP + j) vj avj ftj hargj).2.2.2 hvdj hcj).2.reach_numLoc hrJ)
            · exact OwnReach_not_numLoc horI (((hargs.1 (nP + i) vi avi fti hargi).2.2.2 hvdi hci).2.reach_numLoc (OwnReach_toReach horI))
          · intro l hor
            rcases hownReach l hor with hge | ⟨k, f, v, hfk, hvk, hkept, hinh, horK⟩
            · exact ⟨fun hF => Nat.not_lt_of_ge hge (hFrameLt l hF),
                fun hss' => Nat.not_lt_of_ge hge (StaticStrLoc_unchanged hst hstat' hstr' hp' hss').2⟩
            · obtain ⟨av, ft, hargK, _, _, hvd, _, _, _, _, _⟩ := hfieldInfo k f v hfk hvk hkept
              by_cases hcV : av.cls = .val
              · obtain ⟨haK, htrK⟩ := hfieldTr k f v av ft hfk hvk hkept hinh hargK hcV
                have ⟨hnotF, hnotSS⟩ := (((hargs.1 (nP + k) v av ft hargK).1.2.2.2.2 haK).2.2.2.2.2.2.2 htrK).2 l horK
                exact ⟨hnotF, fun hss' => hnotSS (StaticStrLoc_unchanged hst hstat' hstr' hp' hss').1⟩
              · exact False.elim (OwnReach_not_numLoc horK (((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.reach_numLoc (OwnReach_toReach horK)))
        have hvsim' : VSim P ext B st' Frame NoKill NoSpend σ' I (fun _ => False) res rv := by
          refine ⟨hresRegsLt, hresDepsLt, (fun _ hs => by rw [hresSrc] at hs; cases hs),
            fun _ his => absurd his hnotOnceRes, fun _ => ?_⟩
          refine ⟨hbase', hdou' st'.regions (I.regsOf res.regs) (fun k f v hfk hvk hkept =>
              hrg' ▸ (hvsOk k f v hfk hvk hkept).2.2.2.2),
            hcf', fun _ hne => absurd hresCls hne,
            fun _ => ⟨hno', fun _ h => h, hresSkel ▸ hfun'⟩,
            (fun hoo => by rw [hresOO] at hoo; cases hoo),
            fun his => absurd his hnotOnceRes, htrV⟩
        have hdisj' : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv := by
          intro i b ab hsc hbi habi hne
          have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
          have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
          refine ⟨?_, ?_, (fun _ hf => by
              rcases hf with hoo | ⟨his, _⟩
              · rw [hresOO] at hoo; cases hoo
              · exact absurd his hnotOnceRes),
            ?_,
            (fun _ _ hs => by rw [hresSrc] at hs; cases hs),
            (fun hs => by rw [hresSrc] at hs; cases hs),
            (fun _ hs => by rw [hresSrc] at hs; cases hs)⟩
          · intro _ htrRes haB' hdisjD l horR hrB'
            have haB : ActiveVal σ (effVal ab) := ActiveVal.of_AStateLe hsim.2.1 hle hvB.2.1 hsrcB haB'
            have hpB := hpEnv0 i b ab hsc hbi habi hne haB
            have hrB : Reach st.heap b.val l := (Reach_congr hpB l).mp hrB'
            rcases hownReach l horR with hge | ⟨k, f, v, hfk, hvk, hkept, hinh, horK⟩
            · exact Nat.not_lt_of_ge hge ((hvB.2.2.2.2 haB).1.1.reach_lt_size hrB)
            · obtain ⟨av, ft, hargK, havArr, hkMem, hvd, hoo, _, _, _, hinhInfo⟩ := hfieldInfo k f v hfk hvk hkept
              by_cases hcV : av.cls = .val
              · obtain ⟨hnoSrc, hsubDeps⟩ := hinhInfo hinh hcV
                obtain ⟨havOwn, havLive⟩ := (huniqInfo htrRes.2.1).1 k hkMem av f havArr hfk hinh hcV
                have haK : ActiveVal σ av := ⟨hvd, fun his => absurd his hnoSrc⟩
                have htrK : Transferable σ NoKill av :=
                  ⟨hcV, havOwn, hoo, hnoSrc, fun d hd => ⟨havLive d hd, (htrRes.2.2.2.2 d (hsubDeps d hd)).2⟩⟩
                exact ((hargs.1 (nP + k) v av ft hargK).2.1 i b ab hsc hbi habi hne).1 haK htrK haB
                  (fun d hd => hdisjD d (hsubDeps d hd)) l horK hrB
              · exact OwnReach_not_numLoc horK (((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.reach_numLoc (OwnReach_toReach horK))
          · intro haB' htrB' _ hdisjD l horB' hrR'
            have haB : ActiveVal σ (effVal ab) := ActiveVal.of_AStateLe hsim.2.1 hle hvB.2.1 hsrcB haB'
            have htrB : Transferable σ NoKill (effVal ab) :=
              Transferable.of_AStateLe hsim.2.1 hle hvB.2.1 hsrcB (fun _ h => h) htrB'
            have hpB := hpEnv0 i b ab hsc hbi habi hne haB
            have horB : OwnReach P st.heap b.val l := (OwnReach_congr hpB l).mp horB'
            rcases hreach' l hrR' with hge | ⟨k, f, v, hfk, hvk, hkept, hrK⟩
            · exact Nat.not_lt_of_ge hge ((hvB.2.2.2.2 haB).1.1.reach_lt_size (OwnReach_toReach horB))
            · obtain ⟨av, ft, hargK, havArr, hkMem, hvd, _, _, _, hsh, hinh⟩ := hfieldInfo k f v hfk hvk hkept
              by_cases hcV : av.cls = .val
              · have haK : ActiveVal σ av := by
                  cases hfm : f.fmode with
                  | shared => exact ⟨hvd, fun his => absurd his (hsh hfm).2⟩
                  | inherited => exact ⟨hvd, fun his => absurd his (hinh hfm hcV).1⟩
                have hdisjK : ∀ d, d ∈ (effVal ab).deps → ¬ (d ∈ av.deps) := by
                  intro d hdB hdK
                  cases hfm : f.fmode with
                  | inherited => exact hdisjD d hdB ((hinh hfm hcV).2 d hdK)
                  | shared =>
                    have hdLive' := (htrB'.2.2.2.2 d hdB).1
                    have hdLive0 := (htrB.2.2.2.2 d hdB).1
                    have hdLt : d < σ.st.size := hvB.2.1 d hdB
                    have hUpd := hstUpd d hdLt
                    have hcond : (∃ k' ∈ kept.toList, ∃ v' f', avs.toArray[nP + k']? = some (some v') ∧
                        fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ d ∈ v'.deps) ∧ σ.st[d]? = some .live :=
                      ⟨⟨k, hkMem, av, f, havArr, hfk, hfm, hcV, hdK⟩, hdLive0⟩
                    split at hUpd
                    · rw [hdLive'] at hUpd; cases hUpd
                    · exact absurd hcond ‹_›
                exact ((hargs.1 (nP + k) v av ft hargK).2.1 i b ab hsc hbi habi hne).2.1 haB htrB haK hdisjK l horB hrK
              · exact OwnReach_not_numLoc horB (((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.reach_numLoc hrK)
          · intro haB' hfB' _ _ l hftB hrR'
            have haB : ActiveVal σ (effVal ab) := ActiveVal.of_AStateLe hsim.2.1 hle hvB.2.1 hsrcB haB'
            have hfB : FootActive σ (effVal ab) := FootActive.of_AStateLe hsim.2.1 hle hvB.2.1 hsrcB hfB'
            have hftR : Reach st.heap b.val l ∧ ¬ NumLoc st.heap l := by
              have hvBA := hvB.2.2.2.2 haB
              rcases hfB with hoo | ⟨his, _⟩
              · exact ⟨((hvBA.2.2.2.2.2.1 hoo).1 l hftB).1, ((hvBA.2.2.2.2.2.1 hoo).1 l hftB).2.2⟩
              · exact ⟨((hvBA.2.2.2.2.2.2.1 his).1 l hftB).1, ((hvBA.2.2.2.2.2.2.1 his).1 l hftB).2.2⟩
            rcases hreach' l hrR' with hge | ⟨k, f, v, hfk, hvk, hkept, hrK⟩
            · exact Nat.not_lt_of_ge hge ((hvB.2.2.2.2 haB).1.1.reach_lt_size hftR.1)
            · obtain ⟨av, ft, hargK, _, _, hvd, hoo, _, _, hsh, hinh⟩ := hfieldInfo k f v hfk hvk hkept
              by_cases hcV : av.cls = .val
              · have hnoSrc : ¬ IsOnceSrc σ av := by
                  cases hfm : f.fmode with
                  | shared => exact (hsh hfm).2
                  | inherited => exact (hinh hfm hcV).1
                have haK : ActiveVal σ av := ⟨hvd, fun his => absurd his hnoSrc⟩
                have hneSrc : av.src ≠ some ab.id := by
                  intro hEqSrc
                  rcases hfB with hooB | ⟨hisB, _⟩
                  · have h1 := ((hargs.1 (nP + k) v av ft hargK).2.1 i b ab hsc hbi habi hne).2.2.2.2.2.1 hEqSrc hooB
                    rw [hoo] at h1; cases h1
                  · obtain ⟨id, hsrcE, honceE⟩ := hisB
                    dsimp [effVal] at hsrcE; cases hsrcE
                    exact hnoSrc ⟨ab.id, hEqSrc, honceE⟩
                exact ((hargs.1 (nP + k) v av ft hargK).2.1 i b ab hsc hbi habi hne).2.2.2.1 haB hfB haK hneSrc l hftB hrK
              · exact hftR.2 (((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.reach_numLoc hrK)
        have hnrf' : ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv := by
          intro _ hbadR hbadD l hrR' hnotSS' hnotNum' hF
          rcases hreach' l hrR' with hge | ⟨k, f, v, hfk, hvk, hkept, hrK⟩
          · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
          · obtain ⟨av, ft, hargK, havArr, hkMem, hvd, _, _, hrgSub, hsh, hinh⟩ := hfieldInfo k f v hfk hvk hkept
            have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
              hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hss0)
            have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hnum⟩ =>
              hnotNum' ⟨o, n, PreservesLocs_old_num hp' l o n ho hnum, hnum⟩
            by_cases hcV : av.cls = .val
            · have hnoSrc : ¬ IsOnceSrc σ av := by
                cases hfm : f.fmode with
                | shared => exact (hsh hfm).2
                | inherited => exact (hinh hfm hcV).1
              have haK : ActiveVal σ av := ⟨hvd, fun his => absurd his hnoSrc⟩
              have hbadDK : ∀ d ∈ av.deps, ¬ BadDep d := by
                intro d hd hbd
                cases hfm : f.fmode with
                | inherited => exact hbadD d ((hinh hfm hcV).2 d hd) hbd
                | shared =>
                  have hdLive' := hBadDep d hbd
                  have hdLt : d < σ.st.size := (hargs.1 (nP + k) v av ft hargK).1.2.1 d hd
                  have hdLive0 : σ.st[d]? = some .live := by
                    have hleD := hle.2.2.1 d hdLt
                    cases h0 : σ.st[d]? with
                    | none => rw [h0, hdLive'] at hleD; cases hleD
                    | some b0 =>
                      rw [h0, hdLive'] at hleD
                      cases b0 with
                      | live => rfl
                      | shared => exact False.elim hleD
                      | dead => exact False.elim hleD
                  have hUpd := hstUpd d hdLt
                  have hcond : (∃ k' ∈ kept.toList, ∃ v' f', avs.toArray[nP + k']? = some (some v') ∧
                      fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ d ∈ v'.deps) ∧ σ.st[d]? = some .live :=
                    ⟨⟨k, hkMem, av, f, havArr, hfk, hfm, hcV, hd⟩, hdLive0⟩
                  split at hUpd
                  · rw [hdLive'] at hUpd; cases hUpd
                  · exact absurd hcond ‹_›
              exact (hargs.1 (nP + k) v av ft hargK).2.2.1 haK
                (fun rg hrg => hbadR rg (hrgSub rg hrg)) hbadDK l hrK hnotSS0 hnotNum0 hF
            · exact hnotNum0 (((hargs.1 (nP + k) v av ft hargK).2.2.2 hvd hcV).2.reach_numLoc hrK)
        exact ⟨rv, st', fun _ => False, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
          hp', hos', hssf', hst', hsim', henvNRF', hvsim', hdisj', hnrf',
          fun _ hne => absurd hresCls hne⟩

/-! ## 5. Bridge 6 (`bindInner_bridge`) -/

private theorem DeepOpenUnder_once_leaf {st : St} {v base : Val} {loc cap : Nat}
    (hbv : v = .ref loc cap base.taint)
    (ho : st.heap.objs[loc]? = some ⟨.once base false, cap⟩)
    (hnv : NonValSafe st.heap base) :
    DeepOpenUnder st.heap st.regions [] v := by
  have hbtNil : base.taint = [] := by
    rcases hnv with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, _, _, _⟩ <;> rfl
  intro w hw rg hrg _
  rw [hbv] at hw
  rcases hw with rfl | ⟨l0, o0, hr0, ho0, hm0⟩
  · rw [hbtNil] at hrg; cases hrg
  · cases hr0 with
    | here =>
      rw [ho] at ho0; cases ho0
      simp only [Cell.vals, List.mem_singleton] at hm0; subst hm0
      rw [hbtNil] at hrg; cases hrg
    | step ho2 hm2 hr2 =>
      rw [ho] at ho2; cases ho2
      simp only [Cell.vals, List.mem_singleton] at hm2; subst hm2
      rcases hnv with ⟨_, rfl⟩ | ⟨_, _, o', _, rfl, ho', _, hn'⟩
      · cases hr2
      · cases hr2 with
        | here => rw [ho'] at ho0; cases ho0; rw [hn'] at hm0; cases hm0
        | step ho3 hm3 _ => rw [ho'] at ho3; cases ho3; rw [hn'] at hm3; cases hm3

private def bindInnerVal (m : BinderMode) (d : Cls) (x : AVal) (s_a : Nat) : AVal :=
  let r : AVal := match m with
    | .erased => { cls := .irr }
    | .unique => { cls := d, own := .uniq, regs := [], skel := x.skel }
    | .uniqueBorrowed => { cls := d, own := .uniq, regs := natUnion x.regs [s_a], skel := x.skel }
    | .borrowed => { x with cls := d, regs := natUnion x.regs [s_a], src := none }
    | .once => { x with cls := d, src := none }
    | .onceBorrowed => { x with cls := d, regs := natUnion x.regs [s_a], src := none }
    | .many => { x with cls := d, src := none }
  if d == .leaf then { r with regs := [] } else r

private theorem bindInnerVal_erased (d : Cls) (x : AVal) (s_a : Nat) :
    bindInnerVal .erased d x s_a = { cls := .irr } := by
  unfold bindInnerVal; cases d <;> rfl

private theorem bindInnerVal_src {m : BinderMode} (hm : m ≠ .erased) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).src = none := by
  unfold bindInnerVal; cases m <;> cases d <;> first | exact absurd rfl hm | rfl

private theorem bindInnerVal_cls {m : BinderMode} (hm : m ≠ .erased) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).cls = d := by
  unfold bindInnerVal; cases m <;> cases d <;> first | exact absurd rfl hm | rfl

private theorem bindInnerVal_skel {m : BinderMode} (hm : m ≠ .erased) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).skel = x.skel := by
  unfold bindInnerVal; cases m <;> cases d <;> first | exact absurd rfl hm | rfl

private theorem bindInnerVal_regs_mem (m : BinderMode) (d : Cls) (x : AVal) (s_a rg : Nat)
    (h : rg ∈ (bindInnerVal m d x s_a).regs) : rg ∈ x.regs ∨ rg = s_a := by
  unfold bindInnerVal at h
  cases m <;> cases d <;> dsimp only at h <;>
    first
    | cases h
    | exact Or.inl h
    | (rcases mem_natUnion.mp h with h1 | h2; exact Or.inl h1; exact Or.inr (List.mem_singleton.mp h2))

private theorem bindInnerVal_deps_mem (m : BinderMode) (d : Cls) (x : AVal) (s_a dep : Nat)
    (h : dep ∈ (bindInnerVal m d x s_a).deps) : dep ∈ x.deps := by
  unfold bindInnerVal at h
  cases m <;> cases d <;> dsimp only at h <;> first | cases h | exact h

private theorem bindInnerVal_deps_nonUniq {m : BinderMode} (hm : m ≠ .erased)
    (hnu : m.isUnique = false) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).deps = x.deps := by
  unfold bindInnerVal
  cases m <;> cases d <;> first | contradiction | rfl

private theorem bindInnerVal_own_nonUniq {m : BinderMode} (hm : m ≠ .erased)
    (hnu : m.isUnique = false) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).own = x.own := by
  unfold bindInnerVal
  cases m <;> cases d <;> first | contradiction | rfl

private theorem bindInnerVal_onceOnly_nonUniq {m : BinderMode} (hm : m ≠ .erased)
    (hnu : m.isUnique = false) (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).onceOnly = x.onceOnly := by
  unfold bindInnerVal
  cases m <;> cases d <;> first | contradiction | rfl

private theorem bindInnerVal_onceOnly_uniq {m : BinderMode} (hu : m.isUnique = true)
    (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).onceOnly = false := by
  unfold bindInnerVal
  cases m <;> cases d <;> first | contradiction | rfl

private theorem bindInnerVal_regs_unique (d : Cls) (x : AVal) (s_a : Nat) :
    (bindInnerVal .unique d x s_a).regs = [] := by
  unfold bindInnerVal; cases d <;> rfl

private theorem bindInnerVal_regs_nonLeaf {m : BinderMode} {d : Cls} (hm : m ≠ .erased)
    (hd : d ≠ .leaf) (x : AVal) (s_a : Nat) :
    (bindInnerVal m d x s_a).regs =
      if m = .unique then []
      else if m.isBorrowed then natUnion x.regs [s_a]
      else x.regs := by
  unfold bindInnerVal
  cases m <;> cases d <;> first | exact absurd rfl hm | exact absurd rfl hd | rfl

private theorem bindInner_val_eq {m : BinderMode} {d : Cls} {x bv : AVal} {s_a : Nat} {w : String}
    {σ₁ σ₂ : AState} (hok : AStateOk σ₁) (hbind : Runs (bindInner m d x s_a w) σ₁ bv σ₂) :
    bv = bindInnerVal m d x s_a := by
  have h := (Runs_bindInner hok hbind).2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [h]; unfold bindInnerVal; cases m <;> rfl

/-- **Bridge 6 (`bindInner_bridge`)**: simulates `Check.bindInner m d x s_a w` + `pushBnd`
(used by `ATerm.letVal` and `AAlt.lamKept`) against `Eval.bindAt P fuel s_c m d xv`,
producing `Sim` and `EnvNoReachForbid` for the extended environment. -/
theorem bindInner_bridge {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {m : BinderMode} {d : Cls} {s_a s_c : Nat} {w : String}
    {st₁ : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {xFoot : Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {x bv : AVal} {xv : Val}
    (hst : StOk P ext B st₁)
    (hs_a : s_a < σ₁.nextRegion)
    (hs_c : s_c < st₁.nextRegion)
    (hI_s : s_c ∈ I.reg s_a)
    (hFrameLt : ∀ l, Frame l → l < st₁.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st₁.heap.objs.size)
    (hNoKill : NoKillOk NoKill σ₂)
    (hNoSpend : NoSpendOk NoSpend σ₂)
    (hBadDep : ∀ dep, BadDep dep → σ₂.st[dep]? = some .live)
    (hsim : Sim P ext B st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot)
    (henvNRF : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep)
    (hvX : VSim P ext B st₁ Frame NoKill NoSpend σ₁ I xFoot x xv)
    (hdisjX : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot xFoot x xv)
    (hnrfX : ActiveVal σ₁ x → NoReachForbid st₁ Forbid BadReg BadDep x xv)
    (hbind : Runs (bindInner m d x s_a w) σ₁ bv σ₂) :
    let isOnce := m.usage == .once
    let σ_push := (σ₂.pushBnd bv isOnce).2
    let ab : ABnd := { id := σ₂.st.size, mode := m, val := bv }
    let Scope' : Nat → Prop := fun i => match i with | 0 => True | k + 1 => Scope k
    (bindAt P fuel s_c m d xv).run st₁ = .error .stuck ∨
    (bindAt P fuel s_c m d xv).run st₁ = .error .outOfFuel ∨
    ∃ bnd st₂ bFoot, (bindAt P fuel s_c m d xv).run st₁ = .ok (bnd, st₂) ∧
      bnd.mode = m ∧
      st₂.regions = st₁.regions ∧ st₂.nextRegion = st₁.nextRegion ∧
      st₂.statics = st₁.statics ∧ st₂.strs = st₁.strs ∧
      st₁.heap.objs.size ≤ st₂.heap.objs.size ∧ st₁.heap.nextCap ≤ st₂.heap.nextCap ∧
      PreservesLocs Frame st₁.heap st₂.heap ∧
      PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap ∧
      PreservesOnceShell st₁.heap st₂.heap ∧
      StaticStrFresh st₁ st₂ ∧
      StOk P ext B st₂ ∧
      Sim P ext B st₂ Frame NoKill NoSpend Scope' (bnd :: env) (ab :: aenv) σ_push I
        (fun i => match i with | 0 => bFoot | k + 1 => envFoot k) ∧
      EnvNoReachForbid st₂ Scope' (bnd :: env) (ab :: aenv) σ_push Forbid BadReg BadDep := by
  intro isOnce σ_push ab Scope'
  obtain ⟨hok₂, hle, hstSz, honceEq, hspSz, hregEq, hnrEq,
    hnotOnceSrc, hvdX, huniqInfo, hunspentOnce, hspUpd, hstUpd, hbvEq⟩ :=
    Runs_bindInner hsim.2.1 hbind
  have hIok₂ : InterpOk σ₂ st₁ I :=
    ⟨fun rg hlt => hsim.2.2.1.1 rg (hnrEq ▸ hlt), fun rc hrc => by rw [hregEq]; exact hsim.2.2.1.2 rc hrc⟩
  -- Branch 1: `m = .erased`
  by_cases hmEr : m = .erased
  · subst hmEr
    have hbvIrr : bv = { cls := .irr } := hbvEq.trans (bindInnerVal_erased d x s_a)
    have hisOnceF : isOnce = false := rfl
    have hrunE : (bindAt P fuel s_c .erased d xv).run st₁ = .ok (⟨.imm .irr, .erased⟩, st₁) := by
      unfold bindAt; rfl
    have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂ (RegsFuture.refl st₁)
      (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
      (PreservesActiveEnv.refl _ _ _ _ _) hsim
    have henvNRF₂ := EnvNoReachForbid_step hsim.2.1 hle (Sim_deps_lt hsim) hsim.2.2.2.1
      (ArrayExtends.refl _) (ArrayExtends.refl _) (PreservesLocs.refl _ _)
      (PreservesActiveEnv.refl _ _ _ _ _) henvNRF
    have hsimP := Sim_push_erased hsim₂
    have hleP : AStateLe σ₂ σ_push := (hok₂.pushBnd bv false).2
    have henvNRFP : EnvNoReachForbid st₁ Scope' (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) σ_push Forbid BadReg BadDep := by
      intro i b' ab' hsc' hbi' habi' hne' ha'
      cases i with
      | zero => simp at habi'; subst habi'; exact absurd rfl hne'
      | succ k =>
        have hbiK : env[k]? = some b' := by simpa using hbi'
        have habiK : aenv[k]? = some ab' := by simpa using habi'
        have hvK := ((hsim₂.2.2.2.2.2.1 k b' ab' hsc' hbiK habiK).2 hne').2
        exact henvNRF₂ k b' ab' hsc' hbiK habiK hne'
          (ActiveVal.of_AStateLe hok₂ hleP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha')
    right; right
    refine ⟨⟨.imm .irr, .erased⟩, st₁, fun _ => False, hrunE, rfl,
      rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _,
      hst, ?_, henvNRFP⟩
    rw [show σ_push = (σ₂.pushBnd { cls := .irr } false).2 from by simp [σ_push, isOnce, hisOnceF, hbvIrr],
        show ab = { id := (σ₂.pushBnd { cls := .irr } false).1, mode := .erased, val := { cls := .irr } } from by simp [ab, hbvIrr, AState.pushBnd]]
    exact hsimP
  -- From here on: `m ≠ .erased`.
  have hbvDef : bv = bindInnerVal m d x s_a := bindInner_val_eq hsim.2.1 hbind
  have hvd : ValidDeps σ₁ x.deps := hvdX hmEr
  have haX : ActiveVal σ₁ x := by
    refine ⟨hvd, fun his => ?_⟩
    by_cases hu : m.usage = .once
    · exact hunspentOnce hu
    · exact absurd his (hnotOnceSrc hu)
  have hvXAct := hvX.2.2.2.2 haX
  -- Common properties of `bv`
  have hbvSrc : bv.src = none := hbvDef ▸ bindInnerVal_src hmEr d x s_a
  have hbvCls : bv.cls = d := hbvDef ▸ bindInnerVal_cls hmEr d x s_a
  have hbvSkel : bv.skel = x.skel := hbvDef ▸ bindInnerVal_skel hmEr d x s_a
  have hbvRegsLt : ∀ rg ∈ bv.regs, rg < σ₂.nextRegion := by
    intro rg hrg; rw [hnrEq]
    rcases bindInnerVal_regs_mem m d x s_a rg (hbvDef ▸ hrg) with h1 | rfl
    · exact hvX.1 rg h1
    · exact hs_a
  have hbvDepsLt : ∀ dep ∈ bv.deps, dep < σ₂.st.size := by
    intro dep hdep; rw [hstSz]
    exact hvX.2.1 dep (bindInnerVal_deps_mem m d x s_a dep (hbvDef ▸ hdep))
  -- Key helper: `x.onceOnly = true → x.src = some id → σ₂.st[id]? = some .dead`
  have hkillOO : x.onceOnly = true → ∀ id, x.src = some id → σ₂.st[id]? = some .dead := by
    intro hoo id hsrc
    have hidLt : id < σ₁.st.size := (hvX.2.2.1 id hsrc).1
    have hUpd := hstUpd id hidLt
    split at hUpd
    · exact hUpd
    · split at hUpd
      · exact hUpd
      · rename_i hneg; exact False.elim (hneg ⟨hoo, hsrc⟩)
  have hooNotNoKill : x.onceOnly = true → ∀ id, x.src = some id → ¬ NoKill id :=
    fun hoo id hsrc hnk => hNoKill id hnk (hkillOO hoo id hsrc)
  have hooSrcNotActive : x.onceOnly = true →
      ∀ (i : Nat) (ab₂ : ABnd), aenv[i]? = some ab₂ → ActiveVal σ₂ (effVal ab₂) → x.src ≠ some ab₂.id := by
    intro hoo i ab₂ _ ha₂ hsrc
    exact (ha₂.1 ab₂.id List.mem_cons_self).2 (hkillOO hoo ab₂.id hsrc)
  -- Key helper for unique transfer (`m.isUnique = true ∧ x.cls = .val`)
  have huniqTr : m.isUnique = true → x.cls = .val → Transferable σ₁ NoKill x := by
    intro hu hcV
    obtain ⟨hoo, hinfo⟩ := huniqInfo hu
    obtain ⟨hown, hlive, _⟩ := hinfo hcV
    have hnoSrc : ¬ IsOnceSrc σ₁ x := hnotOnceSrc (by cases m <;> simp [BinderMode.isUnique, BinderMode.usage] at hu ⊢)
    refine ⟨hcV, hown, hoo, hnoSrc, fun dep hdep => ⟨hlive dep hdep, fun hnk => ?_⟩⟩
    have hdepLt : dep < σ₁.st.size := hvX.2.1 dep hdep
    have hUpd := hstUpd dep hdepLt
    split at hUpd
    · exact hNoKill dep hnk hUpd
    · rename_i hneg; exact hneg ⟨hu, hcV, hdep⟩
  have huniqDead : m.isUnique = true → x.cls = .val → ∀ dep ∈ x.deps, σ₂.st[dep]? = some .dead := by
    intro hu hcV dep hdep
    have hUpd := hstUpd dep (hvX.2.1 dep hdep)
    split at hUpd
    · exact hUpd
    · rename_i hneg; exact False.elim (hneg ⟨hu, hcV, hdep⟩)
  -- Helper: lift `DeepOpenUnder` from `(if m.isBorrowed then s_c :: I.regsOf x.regs else I.regsOf x.regs)` to `I.regsOf bv.regs` when `d ≠ .leaf`
  have hregsSub : d ≠ .leaf →
      ∀ rc, rc ∈ (if m.isBorrowed then s_c :: I.regsOf x.regs else I.regsOf x.regs) →
        (m = .unique → x.regs = []) → rc ∈ I.regsOf bv.regs := by
    intro hneLeaf rc hrc huRegs
    rw [hbvDef, bindInnerVal_regs_nonLeaf hmEr hneLeaf x s_a]
    by_cases hmU : m = .unique
    · simp only [hmU, BinderMode.isBorrowed, Bool.false_eq_true, ↓reduceIte] at hrc
      rw [huRegs hmU, Interp.regsOf_nil] at hrc; cases hrc
    · simp only [hmU, ↓reduceIte]
      by_cases hbr : m.isBorrowed = true
      · simp only [hbr, ↓reduceIte, List.mem_cons] at hrc ⊢
        rw [Interp.mem_regsOf_natUnion]
        rcases hrc with rfl | hmem
        · exact Or.inr (Interp.mem_regsOf.mpr ⟨s_a, List.mem_singleton.mpr rfl, hI_s⟩)
        · exact Or.inl hmem
      · simp only [hbr] at hrc ⊢
        exact hrc
  -- Helper: `EnvNoReachForbid` for old bindings `k + 1` given `PreservesActiveEnv` and `PreservesLocs (StaticStrLoc st₁)`
  have hOldNRF : ∀ (st₂ : St), st₂.statics = st₁.statics → st₂.strs = st₁.strs →
      PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap →
      PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap →
      ∀ (k : Nat) (b' : Bnd) (ab' : ABnd), Scope k → env[k]? = some b' → aenv[k]? = some ab' →
        ab'.mode ≠ .erased → ActiveVal σ_push (effVal ab') →
        NoReachForbid st₂ Forbid BadReg BadDep (effVal ab') b'.val := by
    intro st₂ hstat₂ hstr₂ hpSS₂ hpEnv₂ k b' ab' hscK hbiK habiK hneK haP
    have hleP : AStateLe σ₂ σ_push := (hok₂.pushBnd bv isOnce).2
    have hvK := ((hsim.2.2.2.2.2.1 k b' ab' hscK hbiK habiK).2 hneK).2
    have hdepsK₂ : ∀ dep ∈ (effVal ab').deps, dep < σ₂.st.size := fun dep hdep => hstSz ▸ hvK.2.1 dep hdep
    have hsrcK₂ : ∀ z, (effVal ab').src = some z → z < σ₂.st.size := fun z hz => hstSz ▸ (hvK.2.2.1 z hz).1
    have ha₂ : ActiveVal σ₂ (effVal ab') := ActiveVal.of_AStateLe hok₂ hleP hdepsK₂ hsrcK₂ haP
    exact EnvNoReachForbid_step hsim.2.1 hle (Sim_deps_lt hsim) hsim.2.2.2.1
      (hstat₂ ▸ ArrayExtends.refl _) (hstr₂ ▸ ArrayExtends.refl _) hpSS₂ hpEnv₂ henvNRF
      k b' ab' hscK hbiK habiK hneK ha₂
  -- Helper: `NoReachForbid` for the newly pushed binding `(ab, bnd)`
  have hNewNRF_of : ∀ (st₂ : St) (bnd : Bnd),
      st₂.statics = st₁.statics → st₂.strs = st₁.strs →
      PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap →
      PreservesLocs (fun l => l < st₁.heap.objs.size ∧ (m.isUnique = true → ¬ OwnReach P st₁.heap xv l)) st₁.heap st₂.heap →
      (∀ l, Reach st₂.heap bnd.val l → st₁.heap.objs.size ≤ l ∨ Reach st₁.heap xv l) →
      (d = .leaf → ∀ l, Reach st₂.heap bnd.val l → st₁.heap.objs.size ≤ l ∨ NumLoc st₂.heap l) →
      NoReachForbid st₂ Forbid BadReg BadDep (effVal ab) bnd.val := by
    intro st₂ bnd hstat₂ hstr₂ hpSS₂ hpres₂ hreach₂ hleafR hbadR hbadD l hrB hnotSS₂ hnotNum₂ hF
    by_cases hdL : d = .leaf
    · rcases hleafR hdL l hrB with hge | hnum
      · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
      · exact hnotNum₂ hnum
    · rcases hreach₂ l hrB with hge | hr0
      · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
      · have hnotSS0 : ¬ StaticStrLoc st₁ l := fun hss0 =>
          hnotSS₂ (StaticStrLoc_mono (hstat₂ ▸ ArrayExtends.refl _) (hstr₂ ▸ ArrayExtends.refl _) hpSS₂ hss0)
        have hnotNum0 : ¬ NumLoc st₁.heap l := fun ⟨o, n, ho, hnum⟩ => by
          have hlt : l < st₁.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
          have hEq := hpres₂ l ⟨hlt, fun _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hnum⟩⟩
          exact hnotNum₂ ⟨o, n, hEq.trans ho, hnum⟩
        have hdlF : (d == .leaf) = false := Cls_beq_false_of_ne hdL
        have hregsX : ∀ rg ∈ x.regs, ¬ BadReg rg := by
          intro rg hrg
          by_cases hmU : m = .unique
          · by_cases hcV : x.cls = .val
            · have hnil := (huniqInfo (by rw [hmU]; rfl)).2 hcV |>.2.2 (by rw [hmU]; rfl)
              rw [hnil] at hrg; cases hrg
            · have hnotOnce : ¬ IsOnceSrc σ₁ x := hnotOnceSrc (by rw [hmU]; decide)
              exact False.elim (hnotNum0 ((hvXAct.2.2.2.1 hnotOnce hcV).reach_numLoc hr0))
          · apply hbadR rg
            change rg ∈ bv.regs
            rw [hbvDef, bindInnerVal_regs_nonLeaf hmEr hdL x s_a]
            simp only [hmU, ↓reduceIte]
            by_cases hbr : m.isBorrowed = true
            · simp only [hbr, ↓reduceIte]; exact mem_natUnion.mpr (Or.inl hrg)
            · simp only [hbr]; exact hrg
        have hdepsX : ∀ dep ∈ x.deps, ¬ BadDep dep := by
          intro dep hdep hbd
          by_cases hu : m.isUnique = true
          · by_cases hcV : x.cls = .val
            · have hdead := huniqDead hu hcV dep hdep
              rw [hBadDep dep hbd] at hdead; cases hdead
            · have hnotOnce : ¬ IsOnceSrc σ₁ x := hnotOnceSrc (by cases m <;> simp [BinderMode.isUnique, BinderMode.usage] at hu ⊢)
              exact hnotNum0 ((hvXAct.2.2.2.1 hnotOnce hcV).reach_numLoc hr0)
          · apply hbadD dep
            have huF : m.isUnique = false := Bool.eq_false_iff.mpr hu
            have hdepInBv : dep ∈ bv.deps := by
              rw [hbvDef, bindInnerVal_deps_nonUniq hmEr huF d x s_a]; exact hdep
            have hneId : dep ≠ σ₂.st.size := Nat.ne_of_lt (hstSz ▸ hvX.2.1 dep hdep)
            exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hdepInBv, bne_iff_ne.mpr hneId⟩)
            exact hbd
        exact hnrfX haX hregsX hdepsX l hr0 hnotSS0 hnotNum0 hF
  -- Now split into 3 non-erased cases:
  -- Case A: `m.usage = .once` (`.once`, `.onceBorrowed`)
  -- Case B: `m.usage ≠ .once ∧ x.onceOnly = true` (`.many`, `.borrowed` with `x.onceOnly = true`)
  -- Case C: `m.usage ≠ .once ∧ x.onceOnly = false` (`.many`, `.borrowed`, `.unique`, `.uniqueBorrowed`)
  by_cases huOnce : m.usage = .once
  · -- Case A: `m = .once ∨ m = .onceBorrowed`
    have hmNotU : m.isUnique = false := by cases m <;> simp [BinderMode.usage, BinderMode.isUnique] at huOnce ⊢
    have hisOnceT : isOnce = true := by simp [isOnce, huOnce]
    have hfootX :
        ∃ xOnce : Bool,
          FunOkAt P ext B st₁ x.skel xOnce (if xOnce then xFoot else fun _ => False) xv ∧
          (∀ l, (if xOnce then xFoot else fun _ => False) l →
            Reach st₁.heap xv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
          (∀ (i : Nat) b₂ ab₂, Scope i → env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
            ActiveVal σ₂ (effVal ab₂) →
            ∀ l, (if xOnce then xFoot else fun _ => False) l → ¬ Reach st₁.heap b₂.val l) := by
      by_cases hoo : x.onceOnly = true
      · obtain ⟨hftOk, hftNotF, _, hfun⟩ := hvXAct.2.2.2.2.2.1 hoo
        refine ⟨true, hfun, fun l hl => ⟨(hftOk l hl).1, hftNotF (hooNotNoKill hoo) l hl, (hftOk l hl).2.1, (hftOk l hl).2.2⟩,
          fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ l hl => ?_⟩
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
        exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.1 haX (Or.inl hoo) ha₁ (hooSrcNotActive hoo i ab₂ habi₂ ha₂) l hl
      · have hooF : x.onceOnly = false := Bool.eq_false_iff.mpr hoo
        by_cases his : IsOnceSrc σ₁ x
        · obtain ⟨hftOk, hftNotF, hfun⟩ := hvXAct.2.2.2.2.2.2.1 his
          have hnotSp : ∀ dep ∈ x.deps, σ₁.once[dep]? = some true → ¬ NoSpend dep := by
            intro dep hdep ho1 hns
            have hdepLt : dep < σ₁.spent.size := by rw [← hsim.2.1.2.1]; exact hvX.2.1 dep hdep
            have hUpd := hspUpd dep hdepLt
            have hcond : (m.isUnique = true ∨ m.usage = .once) ∧ dep ∈ x.deps ∧ σ₁.once[dep]? = some true :=
              ⟨Or.inr huOnce, hdep, ho1⟩
            split at hUpd
            · exact hNoSpend dep hns hUpd
            · exact absurd hcond ‹_›
          have hneSrc : ∀ (i : Nat) (ab₂ : ABnd), aenv[i]? = some ab₂ → ActiveVal σ₂ (effVal ab₂) → x.src ≠ some ab₂.id := by
            intro i ab₂ habi₂ ha₂ hsrc
            obtain ⟨id, hsrc', ho'⟩ := his
            rw [hsrc] at hsrc'; cases hsrc'
            have hidMem : ab₂.id ∈ x.deps := (hvX.2.2.1 ab₂.id hsrc).2
            have hidLt : ab₂.id < σ₁.spent.size := by rw [← hsim.2.1.2.1]; exact (hvX.2.2.1 ab₂.id hsrc).1
            have hUpd := hspUpd ab₂.id hidLt
            have hcond : (m.isUnique = true ∨ m.usage = .once) ∧ ab₂.id ∈ x.deps ∧ σ₁.once[ab₂.id]? = some true :=
              ⟨Or.inr huOnce, hidMem, ho'⟩
            have hspT : σ₂.spent[ab₂.id]? = some true := by
              split at hUpd
              · exact hUpd
              · exact absurd hcond ‹_›
            have ho2 : σ₂.once[ab₂.id]? = some true := by rw [honceEq]; exact ho'
            have hspF := ha₂.2 ⟨ab₂.id, rfl, ho2⟩ ab₂.id List.mem_cons_self ho2
            rw [hspT] at hspF; cases hspF
          refine ⟨true, hfun, fun l hl => ⟨(hftOk l hl).1, hftNotF hnotSp l hl, (hftOk l hl).2.1, (hftOk l hl).2.2⟩,
            fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ l hl => ?_⟩
          have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
          have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
          exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.1 haX (Or.inr ⟨his, hunspentOnce huOnce⟩) ha₁
            (hneSrc i ab₂ habi₂ ha₂) l hl
        · refine ⟨false, (hvXAct.2.2.2.2.1 ⟨his, hooF⟩).2.2, fun _ h => False.elim h, fun _ _ _ _ _ _ _ _ _ h => False.elim h⟩
    obtain ⟨xOnce, hfunX, hftXOk, hftXEnv⟩ := hfootX
    let xFt := if xOnce then xFoot else fun _ => False
    rcases bindAt_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s_c) (m := m) (c := d) (sk := x.skel)
        (onceOnly := xOnce) (Foot := xFt) hst hs_c (fun _ => hvXAct.1) (fun _ => hvXAct.2.2.1)
        (fun _ hne => absurd huOnce hne) (fun _ => hfunX) (fun hne => absurd huOnce hne)
        (fun hf l hl => by dsimp [xFt] at hl; rw [hf] at hl; exact hl)
        (fun _ l hl => ⟨(hftXOk l hl).1, (hftXOk l hl).2.2.1⟩)
        (fun hu => by rw [hmNotU] at hu; cases hu)
        (fun hu => by rw [hmNotU] at hu; cases hu)
        (fun hu => by rw [hmNotU] at hu; cases hu) with hSt | hOOF |
      ⟨bnd, st₂, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, _, hpres₂, hos₂, hssf₂,
        hst₂, hbase₂, hcf₂, _, _, _, _, _, hdou₂, hreach₂, _⟩
    · exact Or.inl hSt
    · exact Or.inr (Or.inl hOOF)
    · right; right
      have hpresAll : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
        hpres₂.mono fun l hl => ⟨hl, fun hu => by rw [hmNotU] at hu; cases hu⟩
      have hpFrame : PreservesLocs Frame st₁.heap st₂.heap := hpresAll.mono hFrameLt
      have hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap :=
        hpresAll.mono fun _ h => StaticStrLoc_lt_size hst h
      have hrf₂ : RegsFuture st₁ st₂ := RegsFuture.same_regions (hnr₂ ▸ Nat.le_refl _) hrg₂
      have hIok₂' : InterpOk σ₂ st₂ I :=
        ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hIok₂.1 rg hlt c hc) hrf₂.1,
         fun rc hrc => hIok₂.2 rc (hrg₂ ▸ hrc)⟩
      have hpEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ => by
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
        exact hpresAll.mono fun l hl => (hv₂.2.2.2.2 ha₁).1.1.reach_lt_size hl
      have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂' hrf₂ hos₂ hssf₂ (fun _ _ _ h => h) hpEnv₂ hsim
      obtain ⟨hsp₂, hneValR, loc, resFoot, hlocGe, hresSub, hresOk, hresFun⟩ :=
        bindAt_once_foot hst huOnce hvXAct.1 hfunX (fun hf l hl => by rw [hf] at hl; exact hl)
          (fun l hl => ⟨(hftXOk l hl).1, (hftXOk l hl).2.2.1, (hftXOk l hl).2.2.2⟩) hrunE
      have hdouBnd : DeepOpenUnder st₂.heap st₂.regions (I.regsOf bv.regs) bnd.val := by
        by_cases hdL : d = .leaf
        · rcases bindAt_spec (P := P) (fuel := fuel) (s := s_c) (m := m) (c := d) (v := xv)
              hst.1 (fun _ => hvXAct.1.1) (fun _ => hvXAct.1.2.1)
              (fun hu => by rw [hmNotU] at hu; cases hu) (fun hu => by rw [hmNotU] at hu; cases hu) with
            hS | hO | ⟨b0, s0, hr0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho0, _, _, _, _, _⟩
          · rw [hS] at hrunE; cases hrunE
          · rw [hO] at hrunE; cases hrunE
          · have hEq := Except.ok.inj (hr0.symm.trans hrunE)
            cases congrArg Prod.fst hEq; cases congrArg Prod.snd hEq
            obtain ⟨base, l0, c0, hbv0, _, _, ho, hdlB, hclsB, _, _⟩ := ho0 huOnce
            have hnvB : NonValSafe st₂.heap base :=
              ClsSafe.to_nonValSafe (by rw [hdL]; decide) (ClsSafe.of_clsOk hclsB) hdlB.self.1
            have hdouNil := DeepOpenUnder_once_leaf hbv0 ho hnvB
            exact fun w hw rg hrg hopen => False.elim (List.not_mem_nil (hdouNil w hw rg hrg hopen))
        · have hdou0 := hdou₂ st₂.regions (I.regsOf x.regs) (fun _ => hrg₂ ▸ hvXAct.2.1)
          exact fun w hw rg hrg hopen => hregsSub hdL rg (hdou0 w hw rg hrg hopen) (fun hu => by rw [hu] at huOnce; cases huOnce)
      have hresNotFrame : ∀ l, resFoot l → ¬ Frame l := fun l hl => by
        rcases hresSub l hl with rfl | hfx
        · exact fun hF => Nat.not_lt_of_ge hlocGe (hFrameLt l hF)
        · exact (hftXOk l hfx).2.1
      have hresNotEnv : ∀ (i : Nat) b₂ ab₂, Scope i → env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
          ActiveVal σ₂ (effVal ab₂) → ∀ l, resFoot l → ¬ Reach st₂.heap b₂.val l := by
        intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ l hl hr₂
        have hpB := hpEnv₂ i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂
        have hr1 := (Reach_congr hpB l).mp hr₂
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
        rcases hresSub l hl with rfl | hfx
        · exact Nat.not_lt_of_ge hlocGe ((hv₂.2.2.2.2 ha₁).1.1.reach_lt_size hr1)
        · exact hftXEnv i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ l hfx hr1
      have hbvDepsEq : bv.deps = x.deps := hbvDef ▸ bindInnerVal_deps_nonUniq hmEr hmNotU d x s_a
      have henvDisjO : ∀ (i : Nat) b₁ ab₁, Scope i → env[i]? = some b₁ → aenv[i]? = some ab₁ → ab₁.mode ≠ .erased →
          (ActiveVal σ₂ (effVal ab₁) → Transferable σ₂ NoKill (effVal ab₁) → ValidDeps σ₂ bv.deps →
            (∀ dep, dep ∈ (effVal ab₁).deps → ¬ (dep ∈ bv.deps)) →
            ∀ l, OwnReach P st₂.heap b₁.val l → ¬ Reach st₂.heap bnd.val l) ∧
          (ActiveVal σ₂ (effVal ab₁) → FootActive σ₂ (effVal ab₁) → ValidDeps σ₂ bv.deps →
            ∀ l, envFoot i l → ¬ Reach st₂.heap bnd.val l) := by
        intro i b₁ ab₁ hsc₁ hbi₁ habi₁ hne₁
        have hv₁ := ((hsim.2.2.2.2.2.1 i b₁ ab₁ hsc₁ hbi₁ habi₁).2 hne₁).2
        have hsrc₁ : ∀ z, (effVal ab₁).src = some z → z < σ₁.st.size := fun z hz => (hv₁.2.2.1 z hz).1
        refine ⟨fun ha₁' htr₁' _ hdisjD l hor₁' hrB => ?_, fun ha₁' hf₁' _ l hft₁ hrB => ?_⟩
        · have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₁.2.1 hsrc₁ ha₁'
          have htr₁ := Transferable.of_AStateLe hsim.2.1 hle hv₁.2.1 hsrc₁ (fun _ h => h) htr₁'
          have hpB := hpEnv₂ i b₁ ab₁ hsc₁ hbi₁ habi₁ hne₁ ha₁'
          have hor₁ := (OwnReach_congr hpB l).mp hor₁'
          rcases hreach₂ l hrB with hge | ⟨_, hr0⟩
          · exact Nat.not_lt_of_ge hge ((hv₁.2.2.2.2 ha₁).1.1.reach_lt_size (OwnReach_toReach hor₁))
          · exact (hdisjX i b₁ ab₁ hsc₁ hbi₁ habi₁ hne₁).2.1 ha₁ htr₁ haX
              (fun dep hdep => hbvDepsEq ▸ hdisjD dep hdep) l hor₁ hr0
        · have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₁.2.1 hsrc₁ ha₁'
          have hf₁ := FootActive.of_AStateLe hsim.2.1 hle hv₁.2.1 hsrc₁ hf₁'
          have hftR : Reach st₁.heap b₁.val l := by
            rcases hf₁ with hoo1 | ⟨his1, _⟩
            · exact (((hv₁.2.2.2.2 ha₁).2.2.2.2.2.1 hoo1).1 l hft₁).1
            · exact (((hv₁.2.2.2.2 ha₁).2.2.2.2.2.2.1 his1).1 l hft₁).1
          rcases hreach₂ l hrB with hge | ⟨_, hr0⟩
          · exact Nat.not_lt_of_ge hge ((hv₁.2.2.2.2 ha₁).1.1.reach_lt_size hftR)
          · have hneSrc : x.src ≠ some ab₁.id := by
              intro hEqSrc
              rcases hf₁ with hoo1 | ⟨his1, _⟩
              · have hooX := (hdisjX i b₁ ab₁ hsc₁ hbi₁ habi₁ hne₁).2.2.2.2.2.1 hEqSrc hoo1
                exact hooSrcNotActive hooX i ab₁ habi₁ ha₁' hEqSrc
              · obtain ⟨id, hs1, ho1⟩ := his1
                dsimp [effVal] at hs1; cases hs1
                have hidMem : ab₁.id ∈ x.deps := (hvX.2.2.1 ab₁.id hEqSrc).2
                have hidLt : ab₁.id < σ₁.spent.size := by rw [← hsim.2.1.2.1]; exact (hvX.2.2.1 ab₁.id hEqSrc).1
                have hUpd := hspUpd ab₁.id hidLt
                have hcond : (m.isUnique = true ∨ m.usage = .once) ∧ ab₁.id ∈ x.deps ∧ σ₁.once[ab₁.id]? = some true :=
                  ⟨Or.inr huOnce, hidMem, ho1⟩
                have hspT : σ₂.spent[ab₁.id]? = some true := by
                  split at hUpd
                  · exact hUpd
                  · exact absurd hcond ‹_›
                have ho2 : σ₂.once[ab₁.id]? = some true := by rw [honceEq]; exact ho1
                have hspF := ha₁'.2 ⟨ab₁.id, rfl, ho2⟩ ab₁.id List.mem_cons_self ho2
                rw [hspT] at hspF; cases hspF
            exact (hdisjX i b₁ ab₁ hsc₁ hbi₁ habi₁ hne₁).2.2.2.1 ha₁ hf₁ haX hneSrc l hft₁ hr0
      have hsimP := Sim_push_once_bnd (hmode ▸ huOnce) hbvRegsLt hbvDepsLt hsp₂ hbase₂ hdouBnd hcf₂
        (fun l hl => ⟨(hresOk l hl).1, hresNotFrame l hl, (hresOk l hl).2.1, (hresOk l hl).2.2⟩)
        (hbvSkel ▸ hresFun) hresNotEnv henvDisjO hsim₂
      have henvNRFP : EnvNoReachForbid st₂ Scope' (bnd :: env) (ab :: aenv) σ_push Forbid BadReg BadDep := by
        intro i b' ab' hsc' hbi' habi' hne' ha'
        cases i with
        | zero =>
          simp at hbi' habi'; subst hbi'; subst habi'
          exact hNewNRF_of st₂ bnd hstat₂ hstr₂ hpSS hpres₂
            (fun l hl => (hreach₂ l hl).imp id (fun h => h.2))
            (fun hdL => hneValR (by rw [hdL]; decide))
        | succ k =>
          exact hOldNRF st₂ hstat₂ hstr₂ hpSS hpEnv₂ k b' ab' hsc' (by simpa using hbi') (by simpa using habi') hne' ha'
      refine ⟨bnd, st₂, resFoot, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
        hpFrame, hpSS, hos₂, hssf₂, hst₂, ?_, henvNRFP⟩
      rw [show σ_push = (σ₂.pushBnd bv true).2 from by simp [σ_push, isOnce, hisOnceT],
          show ab = { id := (σ₂.pushBnd bv true).1, mode := bnd.mode, val := bv } from by simp [ab, hmode, AState.pushBnd]]
      exact hsimP
  -- From here on: `m.usage ≠ .once` and `m ≠ .erased`.
  have hnotOnce : ¬ IsOnceSrc σ₁ x := hnotOnceSrc huOnce
  have hisOnceF : isOnce = false := beq_false_of_ne huOnce
  by_cases hooX : x.onceOnly = true
  · -- Case B: `m = .many ∨ m = .borrowed` with `x.onceOnly = true`
    have hmNotU : m.isUnique = false := by
      cases hu : m.isUnique with
      | false => rfl
      | true => rw [(huniqInfo hu).1] at hooX; cases hooX
    have hbvOO : bv.onceOnly = true := (hbvDef ▸ bindInnerVal_onceOnly_nonUniq hmEr hmNotU d x s_a).trans hooX
    have hbvDepsEq : bv.deps = x.deps := hbvDef ▸ bindInnerVal_deps_nonUniq hmEr hmNotU d x s_a
    rcases bindAt_spec (P := P) (fuel := fuel) (s := s_c) (m := m) (c := d) (v := xv)
        hst.1 (fun _ => hvXAct.1.1) (fun _ => hvXAct.1.2.1)
        (fun hu => by rw [hmNotU] at hu; cases hu) (fun hu => by rw [hmNotU] at hu; cases hu) with
      hSt | hOOF | ⟨bnd, st₂, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hc₂, hoss₂, hpres₂,
        hdl₂, hacyc₂, _, _, hcls₂, _, ht₂, _, hdou₂, hreach₂, hown₂⟩
    · exact Or.inl hSt
    · exact Or.inr (Or.inl hOOF)
    · right; right
      have hpresAll : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
        hpres₂.mono fun l hl => ⟨hl, fun hu => by rw [hmNotU] at hu; cases hu⟩
      have hpFrame : PreservesLocs Frame st₁.heap st₂.heap := hpresAll.mono hFrameLt
      have hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap :=
        hpresAll.mono fun _ h => StaticStrLoc_lt_size hst h
      have hos₂ : PreservesOnceShell st₁.heap st₂.heap :=
        PreservesOnceShell.of_preservesLocs (hpresAll.mono fun l ⟨o, _, _, ho, _⟩ => (Array.getElem?_eq_some_iff.mp ho).1)
      have hssf₂ : StaticStrFresh st₁ st₂ :=
        StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat₂ hstr₂
          (hpresAll.mono fun _ h => h.1) (fun _ _ h => h)
      have hst₂ : StOk P ext B st₂ :=
        StOk_of_preserves_old hst hc₂ hrg₂ (hnr₂ ▸ Nat.le_refl _) hstat₂ hstr₂ hpresAll
      have hrf₂ : RegsFuture st₁ st₂ := RegsFuture.same_regions (hnr₂ ▸ Nat.le_refl _) hrg₂
      have hIok₂' : InterpOk σ₂ st₂ I :=
        ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hIok₂.1 rg hlt c hc) hrf₂.1,
         fun rc hrc => hIok₂.2 rc (hrg₂ ▸ hrc)⟩
      have hpEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ => by
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
        exact hpresAll.mono fun l hl => (hv₂.2.2.2.2 ha₁).1.1.reach_lt_size hl
      have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂' hrf₂ hos₂ hssf₂ (fun _ _ _ h => h) hpEnv₂ hsim
      have hnotOnceBv : ¬ IsOnceSrc σ₂ bv := by rintro ⟨_, hs, _⟩; rw [hbvSrc] at hs; cases hs
      have htb₂ : DeepTaintsBounded st₂.heap st₂.nextRegion bnd.val := by
        intro w hw rg hrg
        rw [hnr₂]
        rcases hw with rfl | ⟨l0, o0, hr0, ho0, hm0⟩
        · rcases ht₂ rg hrg with h1 | ⟨_, rfl⟩
          · exact hvXAct.1.2.2.2 xv (HeldBy.refl _ _) rg h1
          · exact hs_c
        · rcases hreach₂ l0 hr0 with hge | ⟨_, hr0'⟩
          · -- Only possible if `d ≠ .val` allocated a `.num` cell (whose `vals = []`).
            have hdNe : d ≠ .val := by
              intro hdV
              have hszEq := (bindAt_plain_val_shape hmEr huOnce hst.1 hvXAct.1.1 hvXAct.1.2.1
                (fun hu => by rw [hmNotU] at hu; cases hu) (fun hu => by rw [hmNotU] at hu; cases hu) (hdV ▸ hrunE)).1
              exact Nat.not_lt_of_ge (hszEq ▸ hge) (hdl₂.reach_lt_size hr0)
            have hnv := ClsSafe.to_nonValSafe hdNe (ClsSafe.of_clsOk (hcls₂ hmEr huOnce)) hdl₂.self.1
            rcases hnv with ⟨_, hEq⟩ | ⟨l1, c1, o1, n1, hEq, ho1, _, hnum1⟩
            · rw [hEq] at hr0; cases hr0
            · rw [hEq] at hr0
              cases hr0 with
              | here => rw [ho1] at ho0; cases ho0; rw [hnum1] at hm0; cases hm0
              | step ho2 hm2 _ => rw [ho1] at ho2; cases ho2; rw [hnum1] at hm2; cases hm2
          · have hlt0 : l0 < st₁.heap.objs.size := hvXAct.1.1.reach_lt_size hr0'
            have ho1 : st₁.heap.objs[l0]? = some o0 := (hpresAll l0 hlt0).symm.trans ho0
            exact hvXAct.1.2.2.2 w (Or.inr ⟨l0, o0, hr0', ho1, hm0⟩) rg hrg
      have hbase₂ : ValBaseOk st₂ bnd.val := ValBaseOk_of_deepLive hdl₂ hacyc₂ htb₂
      have henvNRFP : EnvNoReachForbid st₂ Scope' (bnd :: env) (ab :: aenv) σ_push Forbid BadReg BadDep := by
        intro i b' ab' hsc' hbi' habi' hne' ha'
        cases i with
        | zero =>
          simp at hbi' habi'; subst hbi'; subst habi'
          exact hNewNRF_of st₂ bnd hstat₂ hstr₂ hpSS hpres₂
            (fun l hl => (hreach₂ l hl).imp id (fun h => h.2))
            (fun hdL l hrB => Or.inr ((ClsSafe.to_nonValSafe (by rw [hdL]; decide) (ClsSafe.of_clsOk (hcls₂ hmEr huOnce)) hdl₂.self.1).reach_numLoc hrB))
        | succ k =>
          exact hOldNRF st₂ hstat₂ hstr₂ hpSS hpEnv₂ k b' ab' hsc' (by simpa using hbi') (by simpa using habi') hne' ha'
      by_cases hdV : d = .val
      · obtain ⟨hszEq, hloc⟩ := bindAt_plain_val_shape hmEr huOnce hst.1 hvXAct.1.1 hvXAct.1.2.1
          (fun hu => by rw [hmNotU] at hu; cases hu) (fun hu => by rw [hmNotU] at hu; cases hu) (hdV ▸ hrunE)
        have hcf₂ : CtorFieldsOk P ext B st₂ bnd.val :=
          CtorFieldsOk_of_sameShape hvXAct.1.1 (hoss₂.to_sameShapeOn _) hloc hrf₂ hvXAct.2.2.1
        obtain ⟨hftOk, hftNotF, hftCtor, hfunX⟩ := hvXAct.2.2.2.2.2.1 hooX
        have hdouBnd : DeepOpenUnder st₂.heap st₂.regions (I.regsOf bv.regs) bnd.val := by
          have hdou0 := hdou₂ st₂.regions (I.regsOf x.regs) (fun _ => hrg₂ ▸ hvXAct.2.1)
          exact fun w hw rg hrg hopen => hregsSub (by rw [hdV]; decide) rg (hdou0 w hw rg hrg hopen) (fun hu => by rw [hu] at hmNotU; cases hmNotU)
        have hreachEq : ∀ l, Reach st₂.heap bnd.val l ↔ Reach st₁.heap xv l := fun l =>
          ⟨fun h => Reach_of_sameShapeOn_rev hvXAct.1.1 (hoss₂.to_sameShapeOn _) hloc h,
           fun h => Reach_of_sameShapeOn (hoss₂.to_sameShapeOn _) hloc h⟩
        have hvsimBv : VSim P ext B st₂ Frame NoKill NoSpend σ₂ I xFoot bv bnd.val := by
          refine ⟨hbvRegsLt, hbvDepsLt, (fun _ hs => by rw [hbvSrc] at hs; cases hs),
            fun _ his => absurd his hnotOnceBv, fun _ => ?_⟩
          refine ⟨hbase₂, hdouBnd, hcf₂,
            fun _ hne => absurd (hbvCls.trans hdV) hne,
            (fun ⟨_, hF⟩ => by rw [hbvOO] at hF; cases hF),
            fun _ => ⟨fun l hl => ⟨(hreachEq l).mpr (hftOk l hl).1,
              fun hss₂ => (hftOk l hl).2.1 (StaticStrLoc_unchanged hst hstat₂ hstr₂ hpresAll hss₂).1,
              fun ⟨o, n, ho, hnum⟩ => (hftOk l hl).2.2 ⟨o, n, (hpresAll l (hvXAct.1.1.reach_lt_size (hftOk l hl).1)).symm.trans ho, hnum⟩⟩,
              fun _ l hl => hftNotF (hooNotNoKill hooX) l hl,
              (fun loc cap t o r' fs' hbEq ho hc l hl => by
                have hlt : loc < st₁.heap.objs.size := by rw [← hszEq]; exact (Array.getElem?_eq_some_iff.mp ho).1
                have ho1 : st₁.heap.objs[loc]? = some o := (hpresAll loc hlt).symm.trans ho
                cases hxv : xv with
                | imm _ => rw [hxv, hbEq] at hloc; cases hloc
                | ref l' c1 t1 =>
                  rw [hxv, hbEq] at hloc; dsimp only [SameLoc] at hloc; subst hloc
                  exact hftCtor l' c1 t1 o r' fs' hxv ho1 hc l hl),
              hbvSkel ▸ FunOkAt_preserve_sameShape hloc (hoss₂.to_sameShapeOn _) hrf₂ hfunX⟩,
            fun his => absurd his hnotOnceBv,
            (fun htr => by have h := htr.2.2.1; rw [hbvOO] at h; cases h)⟩
        have hdisjBv : ValEnvDisj P st₂ NoKill Scope env aenv σ₂ envFoot xFoot bv bnd.val := by
          intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
          have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
          have hsrc₂ : ∀ z, (effVal ab₂).src = some z → z < σ₁.st.size := fun z hz => (hv₂.2.2.1 z hz).1
          refine ⟨(fun _ htr => by have h := htr.2.2.1; rw [hbvOO] at h; cases h),
            fun ha₂' htr₂' _ hdisjD l hor₂' hrB => ?_,
            fun _ _ ha₂' _ l hl hr₂' => ?_,
            fun ha₂' hf₂' _ _ l hft₂ hrB => ?_,
            (fun _ _ hs => by rw [hbvSrc] at hs; cases hs),
            (fun hs => by rw [hbvSrc] at hs; cases hs),
            (fun _ hs => by rw [hbvSrc] at hs; cases hs)⟩
          · have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
            have htr₂ := Transferable.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ (fun _ h => h) htr₂'
            have hpB := hpEnv₂ i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
            exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haX
              (fun dep hdep => hbvDepsEq ▸ hdisjD dep hdep) l ((OwnReach_congr hpB l).mp hor₂') ((hreachEq l).mp hrB)
          · have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
            have hpB := hpEnv₂ i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
            exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.1 haX (Or.inl hooX) ha₂
              (hooSrcNotActive hooX i ab₂ habi₂ ha₂') l hl ((Reach_congr hpB l).mp hr₂')
          · have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
            have hf₂ := FootActive.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ hf₂'
            exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.1 ha₂ hf₂ haX
              (hooSrcNotActive hooX i ab₂ habi₂ ha₂') l hft₂ ((hreachEq l).mp hrB)
        have hsimP := Sim_push_bnd hbvSrc (fun hF => by rw [hbvOO] at hF; cases hF)
          (fun hu => absurd (hmode ▸ hu) huOnce) (fun hu => absurd (hmode ▸ hu) huOnce)
          (fun hu => absurd (hmode ▸ hu) huOnce) hvsimBv hdisjBv hsim₂
        refine ⟨bnd, st₂, xFoot, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
          hpFrame, hpSS, hos₂, hssf₂, hst₂, ?_, henvNRFP⟩
        rw [show σ_push = (σ₂.pushBnd bv (bnd.mode.usage == .once)).2 from by simp [σ_push, isOnce, hmode],
            show ab = { id := (σ₂.pushBnd bv (bnd.mode.usage == .once)).1, mode := bnd.mode, val := bv } from by simp [ab, hmode, AState.pushBnd]]
        exact hsimP
      · have hnv := ClsSafe.to_nonValSafe hdV (ClsSafe.of_clsOk (hcls₂ hmEr huOnce)) hdl₂.self.1
        have hsimP := Sim_push_bnd hbvSrc (fun _ _ _ h => h)
          (fun hu => absurd (hmode ▸ hu) huOnce) (fun hu => absurd (hmode ▸ hu) huOnce)
          (fun hu => absurd (hmode ▸ hu) huOnce)
          (VSim_nonValSafe hbvRegsLt hbvDepsLt hbvSrc hbase₂ hnv)
          (ValEnvDisj_nonValSafe hbvSrc hnv hsim₂) hsim₂
        refine ⟨bnd, st₂, fun _ => False, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
          hpFrame, hpSS, hos₂, hssf₂, hst₂, ?_, henvNRFP⟩
        rw [show σ_push = (σ₂.pushBnd bv (bnd.mode.usage == .once)).2 from by simp [σ_push, isOnce, hmode],
            show ab = { id := (σ₂.pushBnd bv (bnd.mode.usage == .once)).1, mode := bnd.mode, val := bv } from by simp [ab, hmode, AState.pushBnd]]
        exact hsimP
  · -- Case C: `m.usage ≠ .once ∧ x.onceOnly = false` (`.many`, `.borrowed`, `.unique`, `.uniqueBorrowed`)
    have hooF : x.onceOnly = false := Bool.eq_false_iff.mpr hooX
    have hplain := hvXAct.2.2.2.2.1 ⟨hnotOnce, hooF⟩
    have hbvOO : bv.onceOnly = false := by
      by_cases hu : m.isUnique = true
      · exact hbvDef ▸ bindInnerVal_onceOnly_uniq hu d x s_a
      · exact (hbvDef ▸ bindInnerVal_onceOnly_nonUniq hmEr (Bool.eq_false_iff.mpr hu) d x s_a).trans hooF
    have htreeX : m.isUnique = true → OwnTreeFull P st₁.heap xv := fun hu => by
      by_cases hcV : x.cls = .val
      · exact (hvXAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).1
      · exact (hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.1
    have hdisjSSX : m.isUnique = true → ∀ l, OwnReach P st₁.heap xv l → ¬ StaticStrLoc st₁ l := fun hu l hor => by
      by_cases hcV : x.cls = .val
      · exact ((hvXAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor).2
      · exact False.elim ((hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.2 l hor)
    have hconfX : m.isUnique = true → m.isBorrowed = false → OpenUnder st₁.regions [] xv := fun hu hnb => by
      by_cases hcV : x.cls = .val
      · have hregsNil := ((huniqInfo hu).2 hcV).2.2 hnb
        have hdou := hvXAct.2.1; rw [hregsNil, Interp.regsOf_nil] at hdou
        exact hdou xv (HeldBy.refl _ _)
      · exact (hvXAct.2.2.2.1 hnotOnce hcV).deepOpenUnder_nil xv (HeldBy.refl _ _)
    rcases bindAt_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s_c) (m := m) (c := d) (sk := x.skel)
        (onceOnly := false) (Foot := fun _ => False) hst hs_c (fun _ => hvXAct.1) (fun _ => hvXAct.2.2.1)
        (fun _ _ => hplain.1) (fun _ => hplain.2.2) (fun _ => rfl) (fun _ _ h => h)
        (fun h => absurd h huOnce) htreeX hdisjSSX hconfX with hSt | hOOF |
      ⟨bnd, st₂, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, _, hpres₂, hos₂, hssf₂,
        hst₂, hbase₂, hcf₂, _, hplain₂, _, htree₂, _, hdou₂, hreach₂, hown₂⟩
    · exact Or.inl hSt
    · exact Or.inr (Or.inl hOOF)
    · right; right
      have hpFrame : PreservesLocs Frame st₁.heap st₂.heap := hpres₂.mono fun l hF =>
        ⟨hFrameLt l hF, fun hu hor => by
          by_cases hcV : x.cls = .val
          · exact ((hvXAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor).1 hF
          · exact (hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.2 l hor⟩
      have hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap := hpres₂.mono fun l hss =>
        ⟨StaticStrLoc_lt_size hst hss, fun hu hor => hdisjSSX hu l hor hss⟩
      have hrf₂ : RegsFuture st₁ st₂ := RegsFuture.same_regions (hnr₂ ▸ Nat.le_refl _) hrg₂
      have hIok₂' : InterpOk σ₂ st₂ I :=
        ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hIok₂.1 rg hlt c hc) hrf₂.1,
         fun rc hrc => hIok₂.2 rc (hrg₂ ▸ hrc)⟩
      have hpEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ => by
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
        refine hpres₂.mono fun l hl => ⟨(hv₂.2.2.2.2 ha₁).1.1.reach_lt_size hl, fun hu hor => ?_⟩
        by_cases hcV : x.cls = .val
        · have hdisjD : ∀ dep, dep ∈ x.deps → ¬ (dep ∈ (effVal ab₂).deps) := fun dep hdep hmem =>
            (ha₂.1 dep hmem).2 (huniqDead hu hcV dep hdep)
          exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haX (huniqTr hu hcV) ha₁ hdisjD l hor hl
        · exact (hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.2 l hor
      have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂' hrf₂ hos₂ hssf₂ (fun _ _ _ h => h) hpEnv₂ hsim
      obtain ⟨hcls₂, hno₂, hfun₂⟩ := hplain₂ hmEr huOnce
      have hnotOnceBv : ¬ IsOnceSrc σ₂ bv := by rintro ⟨_, hs, _⟩; rw [hbvSrc] at hs; cases hs
      have hdouBnd : DeepOpenUnder st₂.heap st₂.regions (I.regsOf bv.regs) bnd.val := by
        by_cases hdL : d = .leaf
        · have hnv := ClsSafe.to_nonValSafe (by rw [hdL]; decide) hcls₂ hbase₂.1.self.1
          exact fun w hw rg hrg hopen => False.elim (List.not_mem_nil (hnv.deepOpenUnder_nil w hw rg hrg hopen))
        · by_cases hmU : m = .unique
          · have hdou0 : DeepOpenUnder st₁.heap st₁.regions [] xv := by
              by_cases hcV : x.cls = .val
              · have hnil := ((huniqInfo (by rw [hmU]; rfl)).2 hcV).2.2 (by rw [hmU]; rfl)
                have h := hvXAct.2.1; rw [hnil, Interp.regsOf_nil] at h; exact h
              · exact (hvXAct.2.2.2.1 hnotOnce hcV).deepOpenUnder_nil
            have h1 := hdou₂ st₂.regions [] (fun _ => hrg₂ ▸ hdou0)
            have hbvNil : bv.regs = [] := by rw [hbvDef, hmU]; exact bindInnerVal_regs_unique d x s_a
            rw [hbvNil, Interp.regsOf_nil]
            simpa [hmU, BinderMode.isBorrowed] using h1
          · have hdou0 := hdou₂ st₂.regions (I.regsOf x.regs) (fun _ => hrg₂ ▸ hvXAct.2.1)
            exact fun w hw rg hrg hopen => hregsSub hdL rg (hdou0 w hw rg hrg hopen) (fun hu => absurd hu hmU)
      have htrBv : Transferable σ₂ NoKill bv →
          OwnTreeFull P st₂.heap bnd.val ∧
          ∀ l, OwnReach P st₂.heap bnd.val l → ¬ Frame l ∧ ¬ StaticStrLoc st₂ l := by
        intro htr
        have hdV : d = .val := hbvCls ▸ htr.1
        by_cases hu : m.isUnique = true
        · refine ⟨htree₂ hu, fun l hor => ?_⟩
          rcases hown₂ l hor with hge | ⟨_, hor0⟩
          · exact ⟨fun hF => Nat.not_lt_of_ge hge (hFrameLt l hF),
              fun hss₂ => Nat.not_lt_of_ge hge (StaticStrLoc_unchanged_of_preserves hst hstat₂ hstr₂ hpSS hss₂).2⟩
          · by_cases hcV : x.cls = .val
            · have ⟨hnotF, hnotSS⟩ := (hvXAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor0
              exact ⟨hnotF, fun hss₂ => hnotSS (StaticStrLoc_unchanged_of_preserves hst hstat₂ hstr₂ hpSS hss₂).1⟩
            · exact False.elim ((hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.2 l hor0)
        · have huF : m.isUnique = false := Bool.eq_false_iff.mpr hu
          have hbvDepsEq : bv.deps = x.deps := hbvDef ▸ bindInnerVal_deps_nonUniq hmEr huF d x s_a
          have hbvOwnEq : bv.own = x.own := hbvDef ▸ bindInnerVal_own_nonUniq hmEr huF d x s_a
          obtain ⟨hszEq, hloc⟩ := bindAt_plain_val_shape hmEr huOnce hst.1 hvXAct.1.1 hvXAct.1.2.1
            (fun h => by rw [huF] at h; cases h) (fun h => by rw [huF] at h; cases h) (hdV ▸ hrunE)
          have hpresAll : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
            hpres₂.mono fun l hl => ⟨hl, fun h => by rw [huF] at h; cases h⟩
          have hownEq : ∀ l, OwnReach P st₂.heap bnd.val l → OwnReach P st₁.heap xv l := fun l hor => by
            rcases hown₂ l hor with hge | ⟨_, hor0⟩
            · exact False.elim (Nat.not_lt_of_ge (hszEq ▸ hge) (hbase₂.1.reach_lt_size (OwnReach_toReach hor)))
            · exact hor0
          have hownTreeOfLoc : OwnTreeFull P st₁.heap xv → OwnTreeFull P st₂.heap bnd.val := fun hot0 =>
            OwnTreeFull_of_sameLoc hloc
              ((OwnTreeFull_congr (hpresAll.mono fun l hr => hvXAct.1.1.reach_lt_size hr)).mpr hot0)
          by_cases hcV : x.cls = .val
          · have htrX : Transferable σ₁ NoKill x :=
              ⟨hcV, hbvOwnEq ▸ htr.2.1, hooF, hnotOnce,
               LiveDeps.of_AStateLe hle hvX.2.1 (hbvDepsEq ▸ htr.2.2.2.2)⟩
            refine ⟨hownTreeOfLoc (hvXAct.2.2.2.2.2.2.2 htrX).1, fun l hor => ?_⟩
            have hor0 := hownEq l hor
            have ⟨hnotF, hnotSS⟩ := (hvXAct.2.2.2.2.2.2.2 htrX).2 l hor0
            exact ⟨hnotF, fun hss₂ => hnotSS (StaticStrLoc_unchanged hst hstat₂ hstr₂ hpresAll hss₂).1⟩
          · have hnv0 := hvXAct.2.2.2.1 hnotOnce hcV
            exact ⟨hownTreeOfLoc hnv0.ownTreeFull.1, fun l hor => False.elim (hnv0.ownTreeFull.2 l (hownEq l hor))⟩
      have hvsimBv : VSim P ext B st₂ Frame NoKill NoSpend σ₂ I (fun _ => False) bv bnd.val := by
        refine ⟨hbvRegsLt, hbvDepsLt, (fun _ hs => by rw [hbvSrc] at hs; cases hs),
          fun _ his => absurd his hnotOnceBv, fun _ => ?_⟩
        refine ⟨hbase₂, hdouBnd, hcf₂,
          fun _ hne => ClsSafe.to_nonValSafe (hbvCls ▸ hne) hcls₂ hbase₂.1.self.1,
          fun _ => ⟨hno₂, fun _ h => h, hbvSkel ▸ hfun₂⟩,
          (fun hoo => by rw [hbvOO] at hoo; cases hoo),
          fun his => absurd his hnotOnceBv, htrBv⟩
      have hdisjBv : ValEnvDisj P st₂ NoKill Scope env aenv σ₂ envFoot (fun _ => False) bv bnd.val := by
        intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have hsrc₂ : ∀ z, (effVal ab₂).src = some z → z < σ₁.st.size := fun z hz => (hv₂.2.2.1 z hz).1
        refine ⟨?_, ?_, (fun _ hf => by
            rcases hf with hoo | ⟨his, _⟩
            · rw [hbvOO] at hoo; cases hoo
            · exact absurd his hnotOnceBv),
          ?_,
          (fun _ _ hs => by rw [hbvSrc] at hs; cases hs),
          (fun hs => by rw [hbvSrc] at hs; cases hs),
          (fun _ hs => by rw [hbvSrc] at hs; cases hs)⟩
        · intro _ htrBv' ha₂' hdisjD l horB hr₂'
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have hpB := hpEnv₂ i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
          have hr₂ := (Reach_congr hpB l).mp hr₂'
          rcases hown₂ l horB with hge | ⟨_, hor0⟩
          · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size hr₂)
          · by_cases hcV : x.cls = .val
            · by_cases hu : m.isUnique = true
              · have hdisjX0 : ∀ dep, dep ∈ x.deps → ¬ (dep ∈ (effVal ab₂).deps) := fun dep hdep hmem =>
                  (ha₂'.1 dep hmem).2 (huniqDead hu hcV dep hdep)
                exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haX (huniqTr hu hcV) ha₂ hdisjX0 l hor0 hr₂
              · have huF : m.isUnique = false := Bool.eq_false_iff.mpr hu
                have hbvDepsEq : bv.deps = x.deps := hbvDef ▸ bindInnerVal_deps_nonUniq hmEr huF d x s_a
                have hbvOwnEq : bv.own = x.own := hbvDef ▸ bindInnerVal_own_nonUniq hmEr huF d x s_a
                have htrX : Transferable σ₁ NoKill x :=
                  ⟨hcV, hbvOwnEq ▸ htrBv'.2.1, hooF, hnotOnce,
                   LiveDeps.of_AStateLe hle hvX.2.1 (hbvDepsEq ▸ htrBv'.2.2.2.2)⟩
                exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haX htrX ha₂ (hbvDepsEq ▸ hdisjD) l hor0 hr₂
            · exact (hvXAct.2.2.2.1 hnotOnce hcV).ownTreeFull.2 l hor0
        · intro ha₂' htr₂' _ hdisjD l hor₂' hrB
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have htr₂ := Transferable.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ (fun _ h => h) htr₂'
          have hpB := hpEnv₂ i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
          have hor₂ := (OwnReach_congr hpB l).mp hor₂'
          rcases hreach₂ l hrB with hge | ⟨_, hr0⟩
          · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size (OwnReach_toReach hor₂))
          · by_cases hu : m.isUnique = true
            · by_cases hcV : x.cls = .val
              · have hdisjX0 : ∀ dep, dep ∈ (effVal ab₂).deps → ¬ (dep ∈ x.deps) := fun dep hmem hdep =>
                  (ha₂'.1 dep hmem).2 (huniqDead hu hcV dep hdep)
                exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haX hdisjX0 l hor₂ hr0
              · exact OwnReach_not_numLoc hor₂ ((hvXAct.2.2.2.1 hnotOnce hcV).reach_numLoc hr0)
            · have huF : m.isUnique = false := Bool.eq_false_iff.mpr hu
              have hbvDepsEq : bv.deps = x.deps := hbvDef ▸ bindInnerVal_deps_nonUniq hmEr huF d x s_a
              exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haX (hbvDepsEq ▸ hdisjD) l hor₂ hr0
        · intro ha₂' hf₂' _ _ l hft₂ hrB
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have hf₂ := FootActive.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ hf₂'
          have hftR : Reach st₁.heap b₂.val l := by
            rcases hf₂ with hoo2 | ⟨his2, _⟩
            · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.1 hoo2).1 l hft₂).1
            · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.2.1 his2).1 l hft₂).1
          rcases hreach₂ l hrB with hge | ⟨_, hr0⟩
          · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size hftR)
          · have hneSrc : x.src ≠ some ab₂.id := by
              intro hEqSrc
              rcases hf₂ with hoo2 | ⟨his2, _⟩
              · have h1 := (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.1 hEqSrc hoo2
                rw [hooF] at h1; cases h1
              · obtain ⟨id, hs2, ho2⟩ := his2
                dsimp [effVal] at hs2; cases hs2
                exact hnotOnce ⟨ab₂.id, hEqSrc, ho2⟩
            exact (hdisjX i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.1 ha₂ hf₂ haX hneSrc l hft₂ hr0
      have hsimP := Sim_push_bnd hbvSrc (fun _ _ _ h => h)
        (fun hu => absurd (hmode ▸ hu) huOnce) (fun hu => absurd (hmode ▸ hu) huOnce)
        (fun hu => absurd (hmode ▸ hu) huOnce) hvsimBv hdisjBv hsim₂
      have henvNRFP : EnvNoReachForbid st₂ Scope' (bnd :: env) (ab :: aenv) σ_push Forbid BadReg BadDep := by
        intro i b' ab' hsc' hbi' habi' hne' ha'
        cases i with
        | zero =>
          simp at hbi' habi'; subst hbi'; subst habi'
          exact hNewNRF_of st₂ bnd hstat₂ hstr₂ hpSS hpres₂
            (fun l hl => (hreach₂ l hl).imp id (fun h => h.2))
            (fun hdL l hrB => Or.inr ((ClsSafe.to_nonValSafe (by rw [hdL]; decide) hcls₂ hbase₂.1.self.1).reach_numLoc hrB))
        | succ k =>
          exact hOldNRF st₂ hstat₂ hstr₂ hpSS hpEnv₂ k b' ab' hsc' (by simpa using hbi') (by simpa using habi') hne' ha'
      refine ⟨bnd, st₂, fun _ => False, hrunE, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
        hpFrame, hpSS, hos₂, hssf₂, hst₂, ?_, henvNRFP⟩
      rw [show σ_push = (σ₂.pushBnd bv (bnd.mode.usage == .once)).2 from by simp [σ_push, isOnce, hmode],
          show ab = { id := (σ₂.pushBnd bv (bnd.mode.usage == .once)).1, mode := bnd.mode, val := bv } from by simp [ab, hmode, AState.pushBnd]]
      exact hsimP

/-! ## 6. Bridge 7 (`retCheck_bridge` & `retCheck_altRetVal_bridge`) -/

private theorem renameTaint_noop {s cur : Nat} {v : Val} (h : s ∉ v.taint) :
    renameTaint s cur v = v := by
  cases v with
  | imm _ => rfl
  | ref l c t =>
    dsimp only [Val.taint] at h
    unfold renameTaint
    simp [h]

private theorem ret_val_shape {P : Prog} {fuel s cur : Nat} {res : ResultMode} {v rv' : Val}
    {st st' : St}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v)
    (htree : res.isUnique = true → OwnTreeFull P st.heap v)
    (hnoOpen : res = .unique → OpenUnder st.regions [] v)
    (hrun : (ret P fuel s cur res .val v).run st = .ok (rv', st')) :
    SameLoc v rv' ∧
    (res.isBorrowed = true → s ∉ v.taint →
      ∀ rs A, DeepOpenUnder st.heap rs A v → DeepOpenUnder st'.heap rs A rv') := by
  unfold ret at hrun
  rw [M_bind_run] at hrun
  have hconf : (conform .val v).run st = .ok (v, st) := rfl
  rw [hconf] at hrun; dsimp only at hrun
  cases res with
  | shared =>
    by_cases hcf : confinedTo s v = true
    · simp only [hcf, ↓reduceIte] at hrun; change Except.error _ = Except.ok _ at hrun; cases hrun
    · simp only [hcf, Bool.false_eq_true, ↓reduceIte, M_pure_run] at hrun
      cases hrun; exact ⟨SameLoc.refl v, fun h => by cases h⟩
  | unique =>
    by_cases hcf : confinedTo s v = true
    · simp only [hcf, ↓reduceIte] at hrun; change Except.error _ = Except.ok _ at hrun; cases hrun
    · simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hrun
      rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := false) hc hdl hacyc (htree rfl)
          (fun _ => hnoOpen rfl) with hOOF | ⟨v1, st1, htr, _, _, _, _, _, _, _, _, hvsh, _, _⟩
      · rw [hOOF] at hrun; cases hrun
      · rw [htr] at hrun; cases hrun
        exact ⟨SameLoc.of_valSameShape hvsh, fun h => by cases h⟩
  | borrowed =>
    rw [M_pure_run] at hrun; cases hrun
    exact ⟨SameLoc.renameTaint_right s cur v, fun _ hns rs A hdou => by rw [renameTaint_noop hns]; exact hdou⟩
  | uniqueBorrowed =>
    rw [M_bind_run] at hrun
    rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := true) hc hdl hacyc (htree rfl)
        (fun h => by cases h) with hOOF | ⟨v1, st1, htr, _, _, _, _, _, _, _, hsh, hvsh, _, _⟩
    · rw [hOOF] at hrun; cases hrun
    · rw [htr] at hrun; dsimp only at hrun; rw [M_pure_run] at hrun; cases hrun
      refine ⟨(SameLoc.of_valSameShape hvsh).trans (SameLoc.renameTaint_right s cur v1),
        fun _ hns rs A hdou => ?_⟩
      have hns1 : s ∉ v1.taint := by rw [← hvsh.taint_eq]; exact hns
      rw [renameTaint_noop hns1]
      exact DeepOpenUnder_of_sameShape hsh hvsh hdou

private theorem ret_nonVal_run {P : Prog} {fuel s cur : Nat} {res : ResultMode} {rc : Cls}
    {v : Val} {st : St}
    (hrc : rc ≠ .val)
    (hst : StOk P ext B st) (hbase : ValBaseOk st v)
    (hcf : CtorFieldsOk P ext B st v) (hno : NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st sk false (fun _ => False) v) :
    (ret P fuel s cur res rc v).run st = .error .stuck ∨
    (ret P fuel s cur res rc v).run st = .error .outOfFuel ∨
    ∃ rv' st', (ret P fuel s cur res rc v).run st = .ok (rv', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
      StOk P ext B st' ∧ ValBaseOk st' rv' ∧ ClsSafe st'.heap rc rv' ∧
      NonValSafe st'.heap rv' ∧
      (∀ l, Reach st'.heap rv' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) := by
  unfold ret
  rw [M_bind_run]
  rcases conform_sound (P := P) (ext := ext) (B := B) (c := rc) (sk := sk)
      (onceOnly := false) (Foot := fun _ => False) hst hbase hcf (fun _ => hno) hfun with
    hSt | ⟨v1, st1, hrun1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1,
      hst1, hbase1, hcls1, _, _, hreach1, _, _, _, _, _, _⟩
  · left; rw [hSt]
  · rw [hrun1]; dsimp only
    have hnv1 : NonValSafe st1.heap v1 := ClsSafe.to_nonValSafe hrc hcls1 hbase1.1.self.1
    have htNil : v1.taint = [] := by rcases hnv1 with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, _, _, _⟩ <;> rfl
    have hconfF : confinedTo s v1 = false := by simp [confinedTo, htNil]
    have hrenEq : renameTaint s cur v1 = v1 := renameTaint_noop (by rw [htNil]; simp)
    have htrRun : ∀ (tb : Bool),
        (transfer P fuel tb v1).run st1 = .error .outOfFuel ∨
        (transfer P fuel tb v1).run st1 = .ok (v1, st1) := by
      intro tb
      rcases hnv1 with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, hcap, hnum⟩
      · unfold transfer
        rw [M_bind_run, isLeaf_ok hbase1.1.self.1]
        dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
        have hco : (confinedOpen (.imm i)).run st1 = .ok (false, st1) := by
          unfold confinedOpen; simp [Val.taint]; rfl
        rw [M_bind_run, hco]; dsimp only; simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases fuel with
        | zero => exact Or.inl rfl
        | succ _ => exact Or.inr rfl
      · right
        unfold transfer
        rw [M_bind_run, isLeaf_ok hbase1.1.self.1]
        simp only [ho, hnum, Cell.isNum, ↓reduceIte, M_pure_run]
    have hfin : (ret_tail : M Val) →
        (ret_tail.run st1 = .error .outOfFuel ∨ ret_tail.run st1 = .ok (v1, st1)) →
        ret_tail.run st1 = .error .stuck ∨ ret_tail.run st1 = .error .outOfFuel ∨
        ∃ rv' st', ret_tail.run st1 = .ok (rv', st') ∧
          st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
          st'.statics = st.statics ∧ st'.strs = st.strs ∧
          st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
          PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
          PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
          StOk P ext B st' ∧ ValBaseOk st' rv' ∧ ClsSafe st'.heap rc rv' ∧
          NonValSafe st'.heap rv' ∧
          (∀ l, Reach st'.heap rv' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) := fun _ hr => by
      rcases hr with hO | hOk
      · exact Or.inr (Or.inl hO)
      · exact Or.inr (Or.inr ⟨v1, st1, hOk, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1,
          hp1, hos1, hssf1, hst1, hbase1, hcls1, hnv1, hreach1⟩)
    cases res with
    | shared =>
      simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
      exact hfin _ (Or.inr rfl)
    | unique =>
      simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
      exact hfin _ (htrRun false)
    | borrowed =>
      rw [hrenEq]
      exact hfin _ (Or.inr rfl)
    | uniqueBorrowed =>
      refine hfin _ ?_
      rw [M_bind_run]
      rcases htrRun true with hO | hOk
      · exact Or.inl (by rw [hO])
      · rw [hOk]; dsimp only; rw [hrenEq]; exact Or.inr rfl

/-- **Bridge 7 (`retCheck_bridge`)**: simulates `Check.retCheck exp res s_a { r with cls := rc } w`
against `Eval.ret P fuel s_c cur res rc rv` (used by `enterS`, closure return, and `AAlt`). -/
theorem retCheck_bridge {P : Prog} {ext : ExternOracle} {B fuel s_a s_c cur : Nat}
    {exp : Skel} {res : ResultMode} {rc : Cls} {w : String}
    {st_body : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ_body σ_ret : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {rFoot : Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {r : AVal} {rv : Val}
    (hst : StOk P ext B st_body)
    (hsim : Sim P ext B st_body Frame NoKill NoSpend Scope env aenv σ_body I envFoot)
    (henvNRF : EnvNoReachForbid st_body Scope env aenv σ_body Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st_body.heap.objs.size)
    (hNoKill : NoKillOk NoKill σ_ret)
    (hcur : cur < st_body.nextRegion)
    (hregU : RegUnique I σ_body s_a s_c)
    (hs_in : s_c ∈ st_body.regions)
    (hvR : VSim P ext B st_body Frame NoKill NoSpend σ_body I rFoot r rv)
    (hdisjR : ValEnvDisj P st_body NoKill Scope env aenv σ_body envFoot rFoot r rv)
    (hretChk : Runs (retCheck exp res s_a { r with cls := rc } w) σ_body () σ_ret) :
    (ret P fuel s_c cur res rc rv).run st_body = .error .stuck ∨
    (ret P fuel s_c cur res rc rv).run st_body = .error .outOfFuel ∨
    ∃ rv' st_ret, (ret P fuel s_c cur res rc rv).run st_body = .ok (rv', st_ret) ∧
      st_ret.regions = st_body.regions ∧ st_ret.nextRegion = st_body.nextRegion ∧
      st_ret.statics = st_body.statics ∧ st_ret.strs = st_body.strs ∧
      st_body.heap.objs.size ≤ st_ret.heap.objs.size ∧ st_body.heap.nextCap ≤ st_ret.heap.nextCap ∧
      PreservesLocs Frame st_body.heap st_ret.heap ∧
      PreservesLocs (StaticStrLoc st_body) st_body.heap st_ret.heap ∧
      PreservesOnceShell st_body.heap st_ret.heap ∧
      StaticStrFresh st_body st_ret ∧
      StOk P ext B st_ret ∧
      Sim P ext B st_ret Frame NoKill NoSpend Scope env aenv σ_ret I envFoot ∧
      EnvNoReachForbid st_ret Scope env aenv σ_ret Forbid BadReg BadDep ∧
      ValBaseOk st_ret rv' ∧
      ClsSafe st_ret.heap rc rv' ∧
      NoOnceCell st_ret.heap rv' ∧
      CtorFieldsOk P ext B st_ret rv' ∧
      FunOkAt P ext B st_ret exp false (fun _ => False) rv' ∧
      FunOkAt P ext B st_ret r.skel false (fun _ => False) rv' ∧
      (rc ≠ .val → NonValSafe st_ret.heap rv') ∧
      (rc = .val → SameLoc rv rv') ∧
      (res.isUnique = true ∧ rc = .val →
        OwnTreeFull P st_ret.heap rv' ∧
        ∀ l, OwnReach P st_ret.heap rv' l → ¬ Frame l ∧ ¬ StaticStrLoc st_ret l) ∧
      (∀ A, (res = .shared ∨ res = .unique) →
        (∀ x ∈ I.regsOf (r.regs.filter (· != s_a)), x ∈ A) →
        DeepOpenUnder st_ret.heap (st_body.regions.filter (· != s_c)) A rv') ∧
      (res = .unique → DeepOpenUnder st_ret.heap (st_body.regions.filter (· != s_c)) [] rv') ∧
      (∀ A, res.isBorrowed = true →
        (∀ x ∈ I.regsOf (r.regs.filter (· != s_a)), x ∈ A) →
        (s_a ∉ r.regs ∨ cur = 0 ∨ cur ∈ A) →
        DeepOpenUnder st_ret.heap (st_body.regions.filter (· != s_c)) A rv') ∧
      (∀ l, Reach st_ret.heap rv' l → st_body.heap.objs.size ≤ l ∨ Reach st_body.heap rv l) ∧
      (∀ l, OwnReach P st_ret.heap rv' l → OwnReach P st_body.heap rv l) ∧
      (∀ l, StaticStrLoc st_ret l → StaticStrLoc st_body l ∧ l < st_body.heap.objs.size) ∧
      PreservesActiveEnv Scope env aenv σ_ret st_body.heap st_ret.heap := by
  obtain ⟨hokRet, hle, hstSz, honceEq, hspEq, hregEq, hnrEq,
    hvdR, hadm, hooR, hnotOnceR, hvalInfo, hstUpd⟩ := Runs_retCheck hsim.2.1 hretChk
  have haR : ActiveVal σ_body r := ⟨hvdR, fun his => absurd his hnotOnceR⟩
  have hvRAct := hvR.2.2.2.2 haR
  have hplain := hvRAct.2.2.2.2.1 ⟨hnotOnceR, hooR⟩
  have hadmSym : r.skel.admits exp = true := by rw [Skel.admits_symm]; exact hadm
  have hfunExp : FunOkAt P ext B st_body exp false (fun _ => False) rv :=
    FunOkAt_of_admits hadmSym hplain.2.2
  have hIokRet : InterpOk σ_ret st_body I :=
    ⟨fun rg hlt => hsim.2.2.1.1 rg (hnrEq ▸ hlt), fun rc' hrc' => by rw [hregEq]; exact hsim.2.2.1.2 rc' hrc'⟩
  by_cases hrcV : rc = .val
  · subst hrcV
    obtain ⟨hnoS_a, huNil_a, huOwn_a⟩ := hvalInfo rfl
    have huniqDead : res.isUnique = true → ∀ d ∈ r.deps, σ_ret.st[d]? = some .dead := by
      intro hu d hd
      have hUpd := hstUpd d (hvR.2.1 d hd)
      split at hUpd
      · exact hUpd
      · rename_i hneg; exact False.elim (hneg ⟨rfl, hu, hd⟩)
    have huniqTr : res.isUnique = true → r.cls = .val → Transferable σ_body NoKill r := by
      intro hu hcV
      obtain ⟨hown, hlive⟩ := huOwn_a hu
      refine ⟨hcV, hown, hooR, hnotOnceR, fun d hd => ⟨hlive d hd, fun hnk => hNoKill d hnk (huniqDead hu d hd)⟩⟩
    have hscNotIn : s_a ∉ r.regs → s_c ∉ I.regsOf r.regs := by
      intro hnotIn hmem
      obtain ⟨rg, hrgM, hscM⟩ := Interp.mem_regsOf.mp hmem
      have hne : rg ≠ s_a := fun hEq => hnotIn (hEq ▸ hrgM)
      exact hregU.2 rg (hvR.1 rg hrgM) hne hscM
    have hnoS_c : (res = .shared ∨ res = .unique) → OpenUnder [s_c] [] rv := by
      intro hsu x hx hmem
      simp only [List.mem_singleton] at hmem; subst x
      have hmemI := hvRAct.2.1 rv (HeldBy.refl _ _) s_c hx hs_in
      exact False.elim (hscNotIn (hnoS_a hsu) hmemI)
    have hnoOpen_c : res = .unique → OpenUnder st_body.regions [] rv := by
      intro hu
      have hdou := hvRAct.2.1; rw [huNil_a hu, Interp.regsOf_nil] at hdou
      exact hdou rv (HeldBy.refl _ _)
    have htreeR : res.isUnique = true → OwnTreeFull P st_body.heap rv := fun hu => by
      by_cases hcV : r.cls = .val
      · exact (hvRAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).1
      · exact (hvRAct.2.2.2.1 hnotOnceR hcV).ownTreeFull.1
    have hdisjSSR : res.isUnique = true → ∀ l, OwnReach P st_body.heap rv l → ¬ StaticStrLoc st_body l := fun hu l hor => by
      by_cases hcV : r.cls = .val
      · exact ((hvRAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor).2
      · exact False.elim ((hvRAct.2.2.2.1 hnotOnceR hcV).ownTreeFull.2 l hor)
    rcases ret_sound (P := P) (ext := ext) (B := B) (fuel := fuel) (s := s_c) (cur := cur)
        (r := res) (c := .val) (sk := exp) hst hvRAct.1 hplain.1 hvRAct.2.2.1 hfunExp
        hcur htreeR hnoS_c hnoOpen_c hdisjSSR with hSt | hOOF |
      ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap', _, hpres', hos', hssf',
        hst', hbase', hcls', hno', hcf', hfunExp', htree', hdouSU', hdouB', hreach', hown'⟩
    · exact Or.inl hSt
    · exact Or.inr (Or.inl hOOF)
    · right; right
      have hpFrame : PreservesLocs Frame st_body.heap st_ret.heap := hpres'.mono fun l hF =>
        ⟨hFrameLt l hF, fun hu hor => by
          by_cases hcV : r.cls = .val
          · exact ((hvRAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor).1 hF
          · exact (hvRAct.2.2.2.1 hnotOnceR hcV).ownTreeFull.2 l hor⟩
      have hpSS : PreservesLocs (StaticStrLoc st_body) st_body.heap st_ret.heap := hpres'.mono fun l hss =>
        ⟨StaticStrLoc_lt_size hst hss, fun hu hor => hdisjSSR hu l hor hss⟩
      have hrf' : RegsFuture st_body st_ret := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hrg'
      have hIok' : InterpOk σ_ret st_ret I :=
        ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hIokRet.1 rg hlt c hc) hrf'.1,
         fun rc' hrc' => hIokRet.2 rc' (hrg' ▸ hrc')⟩
      have hpEnv' : PreservesActiveEnv Scope env aenv σ_ret st_body.heap st_ret.heap :=
        fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ => by
          have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
          have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂
          refine hpres'.mono fun l hl => ⟨(hv₂.2.2.2.2 ha₁).1.1.reach_lt_size hl, fun hu hor => ?_⟩
          by_cases hcV : r.cls = .val
          · have hdisjD : ∀ d, d ∈ r.deps → ¬ (d ∈ (effVal ab₂).deps) := fun d hd hmem =>
              (ha₂.1 d hmem).2 (huniqDead hu d hd)
            exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haR (huniqTr hu hcV) ha₁ hdisjD l hor hl
          · exact (hvRAct.2.2.2.1 hnotOnceR hcV).ownTreeFull.2 l hor
      have hsim' := Sim_step (Nat.le_refl B) hle hokRet hIok' hrf' hos' hssf' (fun _ _ _ h => h) hpEnv' hsim
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 hle (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS hpEnv' henvNRF
      have hfunSkel' : FunOkAt P ext B st_ret r.skel false (fun _ => False) rv' :=
        FunOkAt_of_admits hadm hfunExp'
      have ⟨hlocRv, hdouNoS⟩ := ret_val_shape hst.1 hvRAct.1.1 hvRAct.1.2.1 htreeR hnoOpen_c hrunE
      have hssOld : ∀ l, StaticStrLoc st_ret l → StaticStrLoc st_body l ∧ l < st_body.heap.objs.size :=
        fun l hss => StaticStrLoc_unchanged_of_preserves hst hstat' hstr' hpSS hss
      refine ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
        hpFrame, hpSS, hos', hssf', hst', hsim', henvNRF',
        hbase', hcls', hno', hcf', hfunExp', hfunSkel',
        fun h => absurd rfl h, fun _ => hlocRv,
        fun ⟨hu, _⟩ => ⟨htree' hu, fun l hor => ?_⟩,
        fun A hsu hsub => ?_,
        fun hu => ?_,
        fun A hbr hsub hcases => ?_,
        hreach', hown', hssOld, hpEnv'⟩
      · have hor0 := hown' l hor
        by_cases hcV : r.cls = .val
        · have ⟨hnotF, hnotSS⟩ := (hvRAct.2.2.2.2.2.2.2 (huniqTr hu hcV)).2 l hor0
          exact ⟨hnotF, fun hss' => hnotSS (hssOld l hss').1⟩
        · exact False.elim ((hvRAct.2.2.2.1 hnotOnceR hcV).ownTreeFull.2 l hor0)
      · have hdou0 := hdouSU' st_body.regions (I.regsOf r.regs) hsu hvRAct.2.1
        intro u hu x hx hopen
        rw [List.mem_filter] at hopen
        have hxI := hdou0 u hu x hx hopen.1
        obtain ⟨rg, hrgM, hxRg⟩ := Interp.mem_regsOf.mp hxI
        have hrgNe : rg ≠ s_a := fun hEq => hnoS_a hsu (hEq ▸ hrgM)
        exact hsub x (Interp.mem_regsOf.mpr ⟨rg, List.mem_filter.mpr ⟨hrgM, bne_iff_ne.mpr hrgNe⟩, hxRg⟩)
      · have hdouNil : DeepOpenUnder st_body.heap st_body.regions [] rv := by
          have h := hvRAct.2.1; rw [huNil_a hu, Interp.regsOf_nil] at h; exact h
        have h1 := hdouSU' st_body.regions [] (Or.inr hu) hdouNil
        exact fun u hu' x hx hopen => h1 u hu' x hx (List.mem_filter.mp hopen).1
      · rcases hcases with hnotSa | hcurA
        · have hnotSc : s_c ∉ rv.taint := fun hmem =>
            hscNotIn hnotSa (hvRAct.2.1 rv (HeldBy.refl _ _) s_c hmem hs_in)
          have hdou1 := hdouNoS hbr hnotSc st_body.regions (I.regsOf r.regs) hvRAct.2.1
          intro u hu x hx hopen
          rw [List.mem_filter] at hopen
          have hxI := hdou1 u hu x hx hopen.1
          obtain ⟨rg, hrgM, hxRg⟩ := Interp.mem_regsOf.mp hxI
          have hrgNe : rg ≠ s_a := fun hEq => hnotSa (hEq ▸ hrgM)
          exact hsub x (Interp.mem_regsOf.mpr ⟨rg, List.mem_filter.mpr ⟨hrgM, bne_iff_ne.mpr hrgNe⟩, hxRg⟩)
        · have hdouIn : DeepOpenUnder st_body.heap st_body.regions (s_c :: A) rv := by
            intro u hu x hx hopen
            have hxI := hvRAct.2.1 u hu x hx hopen
            obtain ⟨rg, hrgM, hxRg⟩ := Interp.mem_regsOf.mp hxI
            by_cases hEq : rg = s_a
            · subst hEq; rw [hregU.1] at hxRg; simp at hxRg; subst hxRg; exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hsub x (Interp.mem_regsOf.mpr
                ⟨rg, List.mem_filter.mpr ⟨hrgM, bne_iff_ne.mpr hEq⟩, hxRg⟩))
          exact hdouB' st_body.regions A hcurA hdouIn
  · -- Branch 2: `rc ≠ .val`
    have hσEq : σ_ret = σ_body := by
      cases σ_body; cases σ_ret
      simp only [AState.mk.injEq] at hstSz honceEq hspEq hregEq hnrEq ⊢
      refine ⟨?_, honceEq, hspEq, hregEq, hnrEq⟩
      apply Array.ext
      · exact hstSz
      · intro i h1 h2
        have hUpd := hstUpd i h2
        have hfalse : ¬ (rc = .val ∧ res.isUnique = true ∧ i ∈ r.deps) := fun h => hrcV h.1
        simp only [hfalse, ↓reduceIte] at hUpd
        rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at hUpd
        exact Option.some.inj hUpd
    subst σ_ret
    rcases ret_nonVal_run (P := P) (fuel := fuel) (s := s_c) (cur := cur) (res := res) (rc := rc)
        (sk := exp) hrcV hst hvRAct.1 hvRAct.2.2.1 hplain.1 hfunExp with
      hSt | hOOF | ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap', hp', hos', hssf',
        hst', hbase', hcls', hnv', hreach'⟩
    · exact Or.inl hSt
    · exact Or.inr (Or.inl hOOF)
    · right; right
      have hpFrame : PreservesLocs Frame st_body.heap st_ret.heap := hp'.mono hFrameLt
      have hpSS : PreservesLocs (StaticStrLoc st_body) st_body.heap st_ret.heap :=
        hp'.mono fun _ h => StaticStrLoc_lt_size hst h
      have hrf' : RegsFuture st_body st_ret := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hrg'
      have hIok' : InterpOk σ_body st_ret I :=
        ⟨fun rg hlt c hc => Nat.lt_of_lt_of_le (hsim.2.2.1.1 rg hlt c hc) hrf'.1,
         fun rc' hrc' => hsim.2.2.1.2 rc' (hrg' ▸ hrc')⟩
      have hpEnv' : PreservesActiveEnv Scope env aenv σ_body st_body.heap st_ret.heap :=
        fun i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂ =>
          hp'.mono fun l hl => (((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2.2.2.2.2 ha₂).1.1.reach_lt_size hl
      have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl _) hsim.2.1 hIok' hrf' hos' hssf' (fun _ _ _ h => h) hpEnv' hsim
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS hpEnv' henvNRF
      exact ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
        hpFrame, hpSS, hos', hssf', hst', hsim', henvNRF',
        hbase', hcls', hnv'.noOnceCell, hnv'.ctorFieldsOk P ext B st_ret,
        hnv'.funOkAt P ext B st_ret exp, hnv'.funOkAt P ext B st_ret r.skel,
        fun _ => hnv', fun h => absurd h hrcV, fun ⟨_, h⟩ => absurd h hrcV,
        fun _ _ _ => hnv'.deepOpenUnder_nil, fun _ => hnv'.deepOpenUnder_nil,
        fun _ _ _ _ => hnv'.deepOpenUnder_nil,
        hreach', fun l hor => False.elim (hnv'.ownTreeFull.2 l hor),
        fun l hss => StaticStrLoc_unchanged hst hstat' hstr' hp' hss, hpEnv'⟩

/-- **Bridge 7b (`retCheck_altRetVal_bridge`)**: packages `retCheck_bridge` + `closeRegion s_c`
into `Sim`, `EnvNoReachForbid`, `VSim`, `ValEnvDisj`, and `NoReachForbid` for
`altRetVal res rc s_a inner r` in `σ_ret.closeReg s_a` (used directly by `AAlt.lamErased` / `AAlt.lamKept`). -/
theorem retCheck_altRetVal_bridge {P : Prog} {ext : ExternOracle} {B fuel s_a s_c cur : Nat}
    {res : ResultMode} {rc : Cls} {w : String}
    {st_body : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ_body σ_ret : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {rFoot : Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {r : AVal} {rv : Val}
    (hst : StOk P ext B st_body)
    (hsim : Sim P ext B st_body Frame NoKill NoSpend Scope env aenv σ_body I envFoot)
    (henvNRF : EnvNoReachForbid st_body Scope env aenv σ_body Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st_body.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st_body.heap.objs.size)
    (hNoKill : NoKillOk NoKill σ_ret)
    (hBadDep : ∀ d, BadDep d → σ_ret.st[d]? = some .live)
    (hNotBadS : ¬ BadReg s_a)
    (hsaNe1 : s_a ≠ 1)
    (hcur : cur < st_body.nextRegion)
    (hcurIn : cur = 0 ∨ cur ∈ I.reg ((σ_ret.closeReg s_a).regions.headD 1))
    (hIokClose0 : InterpOk (σ_ret.closeReg s_a) { st_body with regions := st_body.regions.filter (· != s_c) } I)
    (hregU : RegUnique I σ_body s_a s_c)
    (hs_in : s_c ∈ st_body.regions)
    (hvR : VSim P ext B st_body Frame NoKill NoSpend σ_body I rFoot r rv)
    (hdisjR : ValEnvDisj P st_body NoKill Scope env aenv σ_body envFoot rFoot r rv)
    (hnrfR : ActiveVal σ_body r → NoReachForbid st_body Forbid BadReg BadDep r rv)
    (hretChk : Runs (retCheck r.skel res s_a { r with cls := rc } w) σ_body () σ_ret) :
    let σ_close := σ_ret.closeReg s_a
    let inner := σ_close.regions.headD 1
    let arv := altRetVal res rc s_a inner r
    (ret P fuel s_c cur res rc rv).run st_body = .error .stuck ∨
    (ret P fuel s_c cur res rc rv).run st_body = .error .outOfFuel ∨
    ∃ rv' st_ret, (ret P fuel s_c cur res rc rv).run st_body = .ok (rv', st_ret) ∧
      let st_close : St := { st_ret with regions := st_ret.regions.filter (· != s_c) }
      st_ret.regions = st_body.regions ∧ st_ret.nextRegion = st_body.nextRegion ∧
      st_ret.statics = st_body.statics ∧ st_ret.strs = st_body.strs ∧
      st_body.heap.objs.size ≤ st_ret.heap.objs.size ∧ st_body.heap.nextCap ≤ st_ret.heap.nextCap ∧
      PreservesLocs Frame st_body.heap st_ret.heap ∧
      PreservesLocs (StaticStrLoc st_body) st_body.heap st_ret.heap ∧
      PreservesOnceShell st_body.heap st_ret.heap ∧
      StaticStrFresh st_body st_ret ∧
      StOk P ext B st_close ∧
      Sim P ext B st_close Frame NoKill NoSpend Scope env aenv σ_close I envFoot ∧
      EnvNoReachForbid st_close Scope env aenv σ_close Forbid BadReg BadDep ∧
      VSim P ext B st_close Frame NoKill NoSpend σ_close I (fun _ => False) arv rv' ∧
      ValEnvDisj P st_close NoKill Scope env aenv σ_close envFoot (fun _ => False) arv rv' ∧
      (ActiveVal σ_close arv → NoReachForbid st_close Forbid BadReg BadDep arv rv') := by
  intro σ_close inner arv
  obtain ⟨hokRet, hle, hstSz, honceEq, hspEq, hregEq, hnrEq,
    hvdR, _, hooR, hnotOnceR, hvalInfo, hstUpd⟩ := Runs_retCheck hsim.2.1 hretChk
  have haR : ActiveVal σ_body r := ⟨hvdR, fun his => absurd his hnotOnceR⟩
  rcases retCheck_bridge hst hsim henvNRF hFrameLt hNoKill hcur hregU hs_in hvR hdisjR hretChk with
    hSt | hOOF | ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
      hpFrame, hpSS, hos', hssf', hst', hsim', henvNRF',
      hbase', hcls', hno', hcf', _, hfunSkel', hnvNe, hlocVal, htrVal,
      hdouSU, hdouU, hdouB, hreach', hown', hssOld, hpEnv'⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    let st_close : St := { st_ret with regions := st_ret.regions.filter (· != s_c) }
    have hIokClose : InterpOk σ_close st_close I :=
      ⟨fun rg hlt c hc => hnr' ▸ hIokClose0.1 rg hlt c hc,
       fun rc' hrc' => hIokClose0.2 rc' (by dsimp only [st_close] at hrc'; rw [hrg'] at hrc'; exact hrc')⟩
    have hstClose : StOk P ext B st_close := StOk_closeRegion s_c hst'
    have hsimClose : Sim P ext B st_close Frame NoKill NoSpend Scope env aenv σ_close I envFoot :=
      Sim_closeRegion s_a s_c hsaNe1 hIokClose hsim'
    have henvNRFClose : EnvNoReachForbid st_close Scope env aenv σ_close Forbid BadReg BadDep :=
      fun i b ab hsc hbi habi hne haC => henvNRF' i b ab hsc hbi habi hne haC
    have hinnerLt : inner < σ_close.nextRegion := by
      have hokC := hsimClose.2.1
      cases hrg : σ_close.regions with
      | nil => simp [inner, hrg]; exact (hokC.2.2.2.2.2 1 hokC.2.2.2.1).2
      | cons hd tl =>
        simp only [inner, hrg, List.headD_cons]
        exact (hokC.2.2.2.2.2 hd (by rw [hrg]; exact List.mem_cons_self)).2
    have harvRegsLt : ∀ rg ∈ arv.regs, rg < σ_close.nextRegion := by
      intro rg hrg
      dsimp only [arv, altRetVal] at hrg
      by_cases hneV : (rc == .irr || rc == .imm || rc == .leaf) = true
      · simp only [hneV, ↓reduceIte] at hrg; cases hrg
      · simp only [hneV, Bool.false_eq_true, ↓reduceIte] at hrg
        by_cases hb : (res.isBorrowed && r.regs.contains s_a) = true
        · simp only [hb, ↓reduceIte, mem_natUnion, List.mem_filter, List.mem_singleton] at hrg
          rcases hrg with ⟨h1, _⟩ | rfl
          · exact hnrEq ▸ hvR.1 rg h1
          · exact hinnerLt
        · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hrg
          exact hnrEq ▸ hvR.1 rg hrg.1
    have harvDepsLt : ∀ d ∈ arv.deps, d < σ_close.st.size := by
      intro d hd; dsimp only [arv, altRetVal] at hd
      by_cases hu : (res.isUnique && rc == .val) = true
      · simp only [hu, ↓reduceIte] at hd; cases hd
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hd
        exact hstSz ▸ hvR.2.1 d hd
    have harvSrc : ∀ x, arv.src = some x → x < σ_close.st.size ∧ x ∈ arv.deps := by
      intro x hx; dsimp only [arv, altRetVal] at hx ⊢
      by_cases hu : (res.isUnique && rc == .val) = true
      · simp only [hu, ↓reduceIte] at hx; cases hx
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hx ⊢
        exact ⟨hstSz ▸ (hvR.2.2.1 x hx).1, (hvR.2.2.1 x hx).2⟩
    have harvNotOnce : ¬ IsOnceSrc σ_close arv := by
      rintro ⟨id, hsrc, ho⟩
      dsimp only [arv, altRetVal] at hsrc
      by_cases hu : (res.isUnique && rc == .val) = true
      · simp only [hu, ↓reduceIte] at hsrc; cases hsrc
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hsrc
        exact hnotOnceR ⟨id, hsrc, honceEq ▸ ho⟩
    have hbaseC : ValBaseOk st_close rv' := hbase'
    have hcfC : CtorFieldsOk P ext B st_close rv' :=
      CtorFieldsOk_congr hbase'.1 (PreservesLocs.refl _ st_ret.heap) (RegsFuture.closeRegion st_ret s_c) hcf'
    have hfunC : FunOkAt P ext B st_close arv.skel false (fun _ => False) rv' :=
      FunOkAt_preserve_locs (PreservesLocs.refl _ st_ret.heap) (RegsFuture.closeRegion st_ret s_c) hfunSkel'
    by_cases hrcV : rc = .val
    · subst hrcV
      have hnvFlag : (Cls.val == .irr || Cls.val == .imm || Cls.val == .leaf) = false := rfl
      have harvRegsEq : arv.regs =
          if res.isBorrowed && r.regs.contains s_a then natUnion (r.regs.filter (· != s_a)) [inner]
          else r.regs.filter (· != s_a) := by
        dsimp only [arv, altRetVal]; simp only [hnvFlag, Bool.false_eq_true, ↓reduceIte]
      have hdouC : DeepOpenUnder st_close.heap st_close.regions (I.regsOf arv.regs) rv' := by
        dsimp only [st_close]; rw [hrg']
        have hsub : ∀ x ∈ I.regsOf (r.regs.filter (· != s_a)), x ∈ I.regsOf arv.regs := by
          intro x hx; rw [harvRegsEq]
          by_cases hb : (res.isBorrowed && r.regs.contains s_a) = true
          · simp only [hb, ↓reduceIte, Interp.mem_regsOf_natUnion]; exact Or.inl hx
          · simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact hx
        cases hres : res with
        | shared => exact hdouSU (I.regsOf arv.regs) (Or.inl hres) hsub
        | unique => exact hdouSU (I.regsOf arv.regs) (Or.inr hres) hsub
        | borrowed | uniqueBorrowed =>
          have hbr : res.isBorrowed = true := by rw [hres]; rfl
          refine hdouB (I.regsOf arv.regs) hbr hsub ?_
          by_cases hsa : s_a ∈ r.regs
          · right
            rcases hcurIn with h0 | hIn
            · exact Or.inl h0
            · right; rw [harvRegsEq]
              have hct : r.regs.contains s_a = true := List.elem_eq_true_of_mem hsa
              simp only [hbr, hct, Bool.and_self, ↓reduceIte, Interp.mem_regsOf_natUnion]
              exact Or.inr (Interp.mem_regsOf.mpr ⟨inner, List.mem_singleton.mpr rfl, hIn⟩)
          · exact Or.inl hsa
      have huniqDead : res.isUnique = true → ∀ d ∈ r.deps, σ_ret.st[d]? = some .dead := by
        intro hu d hd
        have hUpd := hstUpd d (hvR.2.1 d hd)
        split at hUpd
        · exact hUpd
        · rename_i hneg; exact False.elim (hneg ⟨rfl, hu, hd⟩)
      have htrC : Transferable σ_close NoKill arv →
          OwnTreeFull P st_close.heap rv' ∧
          ∀ l, OwnReach P st_close.heap rv' l → ¬ Frame l ∧ ¬ StaticStrLoc st_close l := by
        intro htrA
        by_cases hu : res.isUnique = true
        · exact htrVal ⟨hu, rfl⟩
        · have huF : res.isUnique = false := Bool.eq_false_iff.mpr hu
          have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [huF]
          have htrR : r.cls = .val → Transferable σ_body NoKill r := fun hcV =>
            ⟨hcV, htrA.2.1, hooR, hnotOnceR, LiveDeps.of_AStateLe hle hvR.2.1 (harvDeps ▸ htrA.2.2.2.2)⟩
          have hvRAct := hvR.2.2.2.2 haR
          have hpresAll : PreservesLocs (fun l => l < st_body.heap.objs.size) st_body.heap st_ret.heap := by
            have h1 : st_ret.heap = st_body.heap := by
              unfold ret at hrunE; rw [M_bind_run] at hrunE
              have hconf : (conform .val rv).run st_body = .ok (rv, st_body) := rfl
              rw [hconf] at hrunE; dsimp only at hrunE
              cases res with
              | unique | uniqueBorrowed => cases huF
              | shared =>
                by_cases hc : confinedTo s_c rv = true
                · simp only [hc, ↓reduceIte] at hrunE; change Except.error _ = Except.ok _ at hrunE; cases hrunE
                · simp only [hc, Bool.false_eq_true, ↓reduceIte, M_pure_run] at hrunE; cases hrunE; rfl
              | borrowed => rw [M_pure_run] at hrunE; cases hrunE; rfl
            rw [h1]; exact PreservesLocs.refl _ _
          by_cases hcV : r.cls = .val
          · have hot0 := (hvRAct.2.2.2.2.2.2.2 (htrR hcV)).1
            have hot' := OwnTreeFull_of_sameLoc (hlocVal rfl)
              ((OwnTreeFull_congr (hpresAll.mono fun l hr => hvRAct.1.1.reach_lt_size hr)).mpr hot0)
            refine ⟨hot', fun l hor => ?_⟩
            have hor0 := hown' l hor
            have ⟨hnotF, hnotSS⟩ := (hvRAct.2.2.2.2.2.2.2 (htrR hcV)).2 l hor0
            exact ⟨hnotF, fun hss' => hnotSS (hssOld l hss').1⟩
          · have hnv0 := hvRAct.2.2.2.1 hnotOnceR hcV
            exact ⟨OwnTreeFull_of_sameLoc (hlocVal rfl)
                ((OwnTreeFull_congr (hpresAll.mono fun l hr => hvRAct.1.1.reach_lt_size hr)).mpr hnv0.ownTreeFull.1),
              fun l hor => False.elim (hnv0.ownTreeFull.2 l (hown' l hor))⟩
      have hvsimC : VSim P ext B st_close Frame NoKill NoSpend σ_close I (fun _ => False) arv rv' :=
        ⟨harvRegsLt, harvDepsLt, harvSrc, fun _ his => absurd his harvNotOnce, fun _ =>
          ⟨hbaseC, hdouC, hcfC, fun _ hne => absurd rfl hne,
           fun _ => ⟨hno', fun _ h => h, hfunC⟩,
           (fun hoo => by change r.onceOnly = true at hoo; rw [hooR] at hoo; cases hoo),
           fun his => absurd his harvNotOnce, htrC⟩⟩
      have hdisjC : ValEnvDisj P st_close NoKill Scope env aenv σ_close envFoot (fun _ => False) arv rv' := by
        intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
        have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
        have hsrc₂ : ∀ z, (effVal ab₂).src = some z → z < σ_body.st.size := fun z hz => (hv₂.2.2.1 z hz).1
        refine ⟨?_, ?_, (fun _ hf => by
            rcases hf with hoo | ⟨his, _⟩
            · change r.onceOnly = true at hoo; rw [hooR] at hoo; cases hoo
            · exact absurd his harvNotOnce),
          ?_,
          (fun _ hf => by
            rcases hf with hoo | ⟨his, _⟩
            · change r.onceOnly = true at hoo; rw [hooR] at hoo; cases hoo
            · exact absurd his harvNotOnce),
          ?_, ?_⟩
        · intro _ htrA ha₂' hdisjD l horR hr₂'
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have hpB := hpEnv' i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
          have hr₂ := (Reach_congr hpB l).mp hr₂'
          have hor0 := hown' l horR
          by_cases hcV : r.cls = .val
          · by_cases hu : res.isUnique = true
            · obtain ⟨hown, hlive⟩ := (hvalInfo rfl).2.2 hu
              have htrR : Transferable σ_body NoKill r :=
                ⟨hcV, hown, hooR, hnotOnceR, fun d hd => ⟨hlive d hd, fun hnk => hNoKill d hnk (huniqDead hu d hd)⟩⟩
              have hdisj0 : ∀ d, d ∈ r.deps → ¬ (d ∈ (effVal ab₂).deps) := fun d hd hm =>
                (ha₂'.1 d hm).2 (huniqDead hu d hd)
              exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haR htrR ha₂ hdisj0 l hor0 hr₂
            · have huF : res.isUnique = false := Bool.eq_false_iff.mpr hu
              have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [huF]
              have htrR : Transferable σ_body NoKill r :=
                ⟨hcV, htrA.2.1, hooR, hnotOnceR, LiveDeps.of_AStateLe hle hvR.2.1 (harvDeps ▸ htrA.2.2.2.2)⟩
              exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haR htrR ha₂ (harvDeps ▸ hdisjD) l hor0 hr₂
          · exact (hvR.2.2.2.2 haR).2.2.2.1 hnotOnceR hcV |>.ownTreeFull.2 l hor0
        · intro ha₂' htr₂' _ hdisjD l hor₂' hrR'
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have htr₂ := Transferable.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ (fun _ h => h) htr₂'
          have hpB := hpEnv' i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂'
          have hor₂ := (OwnReach_congr hpB l).mp hor₂'
          rcases hreach' l hrR' with hge | hr0
          · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size (OwnReach_toReach hor₂))
          · by_cases hu : res.isUnique = true
            · have hdisj0 : ∀ d, d ∈ (effVal ab₂).deps → ¬ (d ∈ r.deps) := fun d hm hd =>
                (ha₂'.1 d hm).2 (huniqDead hu d hd)
              exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haR hdisj0 l hor₂ hr0
            · have huF : res.isUnique = false := Bool.eq_false_iff.mpr hu
              have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [huF]
              exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haR (harvDeps ▸ hdisjD) l hor₂ hr0
        · intro ha₂' hf₂' _ _ l hft₂ hrR'
          have ha₂ := ActiveVal.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ ha₂'
          have hf₂ := FootActive.of_AStateLe hsim.2.1 hle hv₂.2.1 hsrc₂ hf₂'
          have hftR : Reach st_body.heap b₂.val l := by
            rcases hf₂ with hoo2 | ⟨his2, _⟩
            · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.1 hoo2).1 l hft₂).1
            · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.2.1 his2).1 l hft₂).1
          rcases hreach' l hrR' with hge | hr0
          · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size hftR)
          · have hneSrc : r.src ≠ some ab₂.id := by
              intro hEqSrc
              rcases hf₂ with hoo2 | ⟨his2, _⟩
              · have h1 := (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.1 hEqSrc hoo2
                rw [hooR] at h1; cases h1
              · obtain ⟨id, hs2, ho2⟩ := his2
                dsimp [effVal] at hs2; cases hs2
                exact hnotOnceR ⟨ab₂.id, hEqSrc, ho2⟩
            exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.1 ha₂ hf₂ haR hneSrc l hft₂ hr0
        · intro hsrc hooB
          dsimp only [arv, altRetVal] at hsrc ⊢
          by_cases hu : (res.isUnique && Cls.val == .val) = true
          · simp only [hu, ↓reduceIte] at hsrc; cases hsrc
          · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hsrc
            exact (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.1 hsrc hooB
        · intro _ hsrc
          dsimp only [arv, altRetVal] at hsrc
          by_cases hu : (res.isUnique && Cls.val == .val) = true
          · simp only [hu, ↓reduceIte] at hsrc; cases hsrc
          · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hsrc
            rcases (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.2 haR hsrc with hlocB | hnumB
            · exact Or.inl (hlocB.trans (hlocVal rfl))
            · right; intro l hr'
              rcases hreach' l hr' with hge | hr0
              · have hszEq : st_ret.heap.objs.size = st_body.heap.objs.size := by
                  have huF : res.isUnique = false := by
                    cases h : res.isUnique with
                    | false => rfl
                    | true => exact absurd (by simp [h, show (Cls.val == Cls.val) = true from rfl]) hu
                  unfold ret at hrunE; rw [M_bind_run] at hrunE
                  have hconf : (conform .val rv).run st_body = .ok (rv, st_body) := rfl
                  rw [hconf] at hrunE; dsimp only at hrunE
                  cases res with
                  | unique | uniqueBorrowed => cases huF
                  | shared =>
                    by_cases hc : confinedTo s_c rv = true
                    · simp only [hc, ↓reduceIte] at hrunE; change Except.error _ = Except.ok _ at hrunE; cases hrunE
                    · simp only [hc, Bool.false_eq_true, ↓reduceIte, M_pure_run] at hrunE; cases hrunE; rfl
                  | borrowed => rw [M_pure_run] at hrunE; cases hrunE; rfl
                exact False.elim (Nat.not_lt_of_ge (hszEq ▸ hge) (hbase'.1.reach_lt_size hr'))
              · obtain ⟨o, n, ho, hnum⟩ := hnumB l hr0
                have hlt : l < st_body.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
                have huF : res.isUnique = false := by
                  cases h : res.isUnique with
                  | false => rfl
                  | true => exact absurd (by simp [h, show (Cls.val == Cls.val) = true from rfl]) hu
                have hstEq : st_ret.heap = st_body.heap := by
                  unfold ret at hrunE; rw [M_bind_run] at hrunE
                  have hconf : (conform .val rv).run st_body = .ok (rv, st_body) := rfl
                  rw [hconf] at hrunE; dsimp only at hrunE
                  cases res with
                  | unique | uniqueBorrowed => cases huF
                  | shared =>
                    by_cases hc : confinedTo s_c rv = true
                    · simp only [hc, ↓reduceIte] at hrunE; change Except.error _ = Except.ok _ at hrunE; cases hrunE
                    · simp only [hc, Bool.false_eq_true, ↓reduceIte, M_pure_run] at hrunE; cases hrunE; rfl
                  | borrowed => rw [M_pure_run] at hrunE; cases hrunE; rfl
                exact ⟨o, n, hstEq ▸ ho, hnum⟩
      have hnrfC : ActiveVal σ_close arv → NoReachForbid st_close Forbid BadReg BadDep arv rv' := by
        intro _ hbadR hbadD l hrR' hnotSS' hnotNum' hF
        rcases hreach' l hrR' with hge | hr0
        · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
        · have hnotSS0 : ¬ StaticStrLoc st_body l := fun hss0 =>
            hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS hss0)
          have hnotNum0 : ¬ NumLoc st_body.heap l := fun ⟨o, n, ho, hnum⟩ => by
            -- Note: `ret` only mutates `cap` on `OwnReach`, never `.num` cells!
            have hlt : l < st_body.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
            have hsame : st_ret.heap.objs[l]? = st_body.heap.objs[l]? := by
              -- Use `ret_spec`'s `PreservesLocs`: `OwnReach_not_numLoc`!
              rcases ret_spec (P := P) (fuel := fuel) (s := s_c) (cur := cur) (r := res) (c := .val)
                  hst.1 (hvR.2.2.2.2 haR).1.1 (hvR.2.2.2.2 haR).1.2.1
                  (fun hu => by
                    by_cases hcV : r.cls = .val
                    · obtain ⟨hown, hlive⟩ := (hvalInfo rfl).2.2 hu
                      exact ((hvR.2.2.2.2 haR).2.2.2.2.2.2.2 ⟨hcV, hown, hooR, hnotOnceR,
                        fun d hd => ⟨hlive d hd, fun hnk => hNoKill d hnk (huniqDead hu d hd)⟩⟩).1
                    · exact ((hvR.2.2.2.2 haR).2.2.2.1 hnotOnceR hcV).ownTreeFull.1)
                  (fun hsu x hx hm => by
                    simp only [List.mem_singleton] at hm; subst x
                    obtain ⟨rg, hrgM, hscM⟩ := Interp.mem_regsOf.mp ((hvR.2.2.2.2 haR).2.1 rv (HeldBy.refl _ _) s_c hx hs_in)
                    exact False.elim (hregU.2 rg (hvR.1 rg hrgM) (fun hEq => (hvalInfo rfl).1 hsu (hEq ▸ hrgM)) hscM))
                  (fun hu => by
                    have h := (hvR.2.2.2.2 haR).2.1; rw [(hvalInfo rfl).2.1 hu, Interp.regsOf_nil] at h
                    exact h rv (HeldBy.refl _ _)) with hS | hO | ⟨v0, s0, hr0', _, _, _, _, _, _, _, _, hp0, _⟩
              · rw [hS] at hrunE; cases hrunE
              · rw [hO] at hrunE; cases hrunE
              · have hEq := Except.ok.inj (hr0'.symm.trans hrunE)
                cases congrArg Prod.snd hEq
                exact hp0 l ⟨hlt, fun _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hnum⟩⟩
            exact hnotNum' ⟨o, n, hsame.trans ho, hnum⟩
          have hbadR0 : ∀ rg ∈ r.regs, ¬ BadReg rg := by
            intro rg hrg
            by_cases hEq : rg = s_a
            · exact hEq ▸ hNotBadS
            · apply hbadR rg; rw [harvRegsEq]
              have hmemF : rg ∈ r.regs.filter (· != s_a) := List.mem_filter.mpr ⟨hrg, bne_iff_ne.mpr hEq⟩
              by_cases hb : (res.isBorrowed && r.regs.contains s_a) = true
              · simp only [hb, ↓reduceIte, mem_natUnion]; exact Or.inl hmemF
              · simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact hmemF
          have hbadD0 : ∀ d ∈ r.deps, ¬ BadDep d := by
            intro d hd hbd
            by_cases hu : res.isUnique = true
            · have hdead := huniqDead hu d hd
              rw [hBadDep d hbd] at hdead; cases hdead
            · have huF : res.isUnique = false := Bool.eq_false_iff.mpr hu
              have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [huF]
              exact hbadD d (harvDeps ▸ hd) hbd
          exact hnrfR haR hbadR0 hbadD0 l hr0 hnotSS0 hnotNum0 hF
      exact ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
        hpFrame, hpSS, hos', hssf', hstClose, hsimClose, henvNRFClose, hvsimC, hdisjC, hnrfC⟩
    · -- `rc ≠ .val`: `NonValSafe st_ret.heap rv'`!
      have hnv' : NonValSafe st_close.heap rv' := hnvNe hrcV
      have hnvFlag : (rc == .irr || rc == .imm || rc == .leaf) = true := by
        cases rc <;> first | exact absurd rfl hrcV | rfl
      have hnotUFlag : (res.isUnique && rc == .val) = false := by
        rw [Cls_beq_false_of_ne hrcV, Bool.and_false]
      have harvSrcEq : arv.src = r.src := by dsimp only [arv, altRetVal]; simp [hnotUFlag]
      have hvsimC : VSim P ext B st_close Frame NoKill NoSpend σ_close I (fun _ => False) arv rv' :=
        ⟨harvRegsLt, harvDepsLt, harvSrc, fun _ his => absurd his harvNotOnce, fun _ =>
          ⟨hbaseC, hnv'.deepOpenUnder_nil, hcfC, fun _ _ => hnv',
           fun _ => ⟨hnv'.noOnceCell, fun _ h => h, hfunC⟩,
           (fun hoo => by change r.onceOnly = true at hoo; rw [hooR] at hoo; cases hoo),
           fun his => absurd his harvNotOnce,
           fun _ => ⟨hnv'.ownTreeFull.1, fun _ hor => False.elim (hnv'.ownTreeFull.2 _ hor)⟩⟩⟩
      have hdisjC : ValEnvDisj P st_close NoKill Scope env aenv σ_close envFoot (fun _ => False) arv rv' := by
        intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
        refine ⟨fun _ _ _ _ _ hor => False.elim (hnv'.ownTreeFull.2 _ hor),
          fun _ _ _ _ l hor hr => OwnReach_not_numLoc hor (hnv'.reach_numLoc hr),
          fun _ _ _ _ _ h => False.elim h,
          fun haB hfB _ _ l hft hr => ?_,
          (fun _ hf => by
            rcases hf with hoo | ⟨his, _⟩
            · change r.onceOnly = true at hoo; rw [hooR] at hoo; cases hoo
            · exact absurd his harvNotOnce),
          fun hsrc hooB => (hdisjR i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.1 (harvSrcEq ▸ hsrc) hooB,
          fun _ _ => Or.inr fun _ hr => hnv'.reach_numLoc hr⟩
        have hvB := ((hsimClose.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2.2.2.2.2 haB
        have hnum := hnv'.reach_numLoc hr
        rcases hfB with hoo | ⟨his, _⟩
        · exact ((hvB.2.2.2.2.2.1 hoo).1 l hft).2.2 hnum
        · exact ((hvB.2.2.2.2.2.2.1 his).1 l hft).2.2 hnum
      exact ⟨rv', st_ret, hrunE, hrg', hnr', hstat', hstr', hsz', hcap',
        hpFrame, hpSS, hos', hssf', hstClose, hsimClose, henvNRFClose, hvsimC, hdisjC,
        fun _ => NoReachForbid_nonValSafe hnv'⟩

/-! ## 7. Bridge 8 (`caseField_fromCell_clear` & `select_caseAltArgs_bridge`) -/

private theorem conform_idemp {c : Cls} {v v1 : Val} {st st1 : St}
    (h1 : (conform c v).run st = .ok (v1, st1)) :
    (conform c v1).run st1 = .ok (v1, st1) := by
  cases c with
  | irr =>
    unfold conform at h1 ⊢; rw [M_pure_run] at h1; cases h1; rfl
  | val =>
    unfold conform at h1 ⊢; rw [M_pure_run] at h1; cases h1; rfl
  | imm =>
    unfold conform at h1 ⊢
    cases v with
    | imm i => rw [M_pure_run] at h1; cases h1; rfl
    | ref l cap t =>
      rw [M_bind_run] at h1
      cases hnum : (numOf? (.ref l cap t)).run st with
      | error e => rw [hnum] at h1; cases h1
      | ok p =>
        rcases p with ⟨o?, s1⟩
        rw [hnum] at h1; dsimp only at h1
        cases o? with
        | none => change Except.error _ = Except.ok _ at h1; cases h1
        | some n => rw [M_pure_run] at h1; cases h1; rfl
  | leaf =>
    unfold conform at h1 ⊢
    cases v with
    | imm i =>
      cases i with
      | bits n =>
        unfold alloc at h1
        simp only [StateT.run, get, set, MonadStateOf.set, pure, Pure.pure, bind, Bind.bind] at h1
        cases h1
        have hlive : LiveRef (Heap.mk (st.heap.objs.push ⟨.num n, st.heap.nextCap⟩) (st.heap.nextCap + 1))
            (.ref st.heap.objs.size st.heap.nextCap []) :=
          ⟨⟨.num n, st.heap.nextCap⟩, by simp, rfl⟩
        rw [M_bind_run, numOf?_ok hlive]
        simp only [Array.getElem?_push_size, M_pure_run]
      | irr | con _ => change Except.error _ = Except.ok _ at h1; cases h1
    | ref l cap t =>
      rw [M_bind_run] at h1
      cases hnum : (numOf? (.ref l cap t)).run st with
      | error e => rw [hnum] at h1; cases h1
      | ok p =>
        rcases p with ⟨o?, s1⟩
        rw [hnum] at h1; dsimp only at h1
        cases o? with
        | none => change Except.error _ = Except.ok _ at h1; cases h1
        | some n =>
          have hs1Eq : s1 = st := by
            unfold numOf? at hnum
            rw [M_bind_run] at hnum
            cases ho : st.heap.objs[l]? with
            | none =>
              have hobj : (obj l).run st = .error .stuck := by unfold obj; simp [ho]; rfl
              rw [hobj] at hnum; cases hnum
            | some o =>
              have hobj : (obj l).run st = .ok (o, st) := by unfold obj; simp [ho]; rfl
              rw [hobj] at hnum; dsimp only at hnum
              cases hcap : (o.cap == cap) with
              | false => rw [hcap] at hnum; simp only [Bool.false_eq_true, ↓reduceIte, M_bind_run] at hnum; cases hnum
              | true =>
                rw [hcap] at hnum; simp only [↓reduceIte] at hnum
                cases hcell : o.cell <;> rw [hcell] at hnum <;> rw [M_pure_run] at hnum <;> cases hnum <;> rfl
          subst hs1Eq
          rw [M_pure_run] at h1; cases h1
          rw [M_bind_run, hnum]; rfl

private theorem bindAt_conform_prefix {P : Prog} {fuel s_c : Nat} {m : BinderMode} {c : Cls}
    {v : Val} {st : St} (hm : m ≠ .erased) :
    ((conform c v).run st = .error .stuck → (bindAt P fuel s_c m c v).run st = .error .stuck) ∧
    (∀ v1 st1, (conform c v).run st = .ok (v1, st1) →
      (bindAt P fuel s_c m c v).run st = (bindAt P fuel s_c m c v1).run st1) := by
  have hmF : (m == .erased) = false := BinderMode_beq_false_of_ne hm
  constructor
  · intro herr
    unfold bindAt
    simp only [hmF, Bool.false_eq_true, ↓reduceIte, M_bind_run, herr]
  · intro v1 st1 hok
    unfold bindAt
    simp only [hmF, Bool.false_eq_true, ↓reduceIte, M_bind_run, hok, conform_idemp hok]

/-- **Bridge 8b (`caseField_fromCell_clear`)**: justifies `AAlt.lamKept`'s clearing of `deps`/`regs`
when `fromCell = true` and `p.cls ≠ .val`: pre-running `conform p.cls v` either gets stuck or
produces `(v1, st1)` with `NonValSafe st1.heap v1`, preserving `Sim`/`EnvNoReachForbid` and satisfying
`VSim`/`ValEnvDisj`/`NoReachForbid` for `{ a0 with deps := [], regs := [] }` while leaving `bindAt`
behavior identical. -/
theorem caseField_fromCell_clear {P : Prog} {ext : ExternOracle} {B fuel s_c : Nat}
    {m : BinderMode} {c : Cls} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {a0 : AVal} {v : Val}
    (hm : m ≠ .erased)
    (hcNe : c ≠ .val)
    (hsrcNone : a0.src = none)
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hbase : ValBaseOk st v)
    (hcf : CtorFieldsOk P ext B st v)
    (hno : NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st a0.skel false (fun _ => False) v) :
    let a0' : AVal := { a0 with deps := [], regs := [] }
    (bindAt P fuel s_c m c v).run st = .error .stuck ∨
    ∃ v1 st1,
      (bindAt P fuel s_c m c v).run st = (bindAt P fuel s_c m c v1).run st1 ∧
      st1.regions = st.regions ∧ st1.nextRegion = st.nextRegion ∧
      st1.statics = st.statics ∧ st1.strs = st.strs ∧
      st.heap.objs.size ≤ st1.heap.objs.size ∧ st.heap.nextCap ≤ st1.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st1.heap ∧
      PreservesOnceShell st.heap st1.heap ∧ StaticStrFresh st st1 ∧
      StOk P ext B st1 ∧
      Sim P ext B st1 Frame NoKill NoSpend Scope env aenv σ I envFoot ∧
      EnvNoReachForbid st1 Scope env aenv σ Forbid BadReg BadDep ∧
      VSim P ext B st1 Frame NoKill NoSpend σ I (fun _ => False) a0' v1 ∧
      ValEnvDisj P st1 NoKill Scope env aenv σ envFoot (fun _ => False) a0' v1 ∧
      NoReachForbid st1 Forbid BadReg BadDep a0' v1 := by
  intro a0'
  have ⟨hprefErr, hprefOk⟩ := bindAt_conform_prefix (P := P) (fuel := fuel) (s_c := s_c) (m := m) (c := c) (v := v) (st := st) hm
  rcases conform_sound (P := P) (ext := ext) (B := B) (c := c) (sk := a0.skel)
      (onceOnly := false) (Foot := fun _ => False) hst hbase hcf (fun _ => hno) hfun with
    hSt | ⟨v1, st1, hrun1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1, hp1, hos1, hssf1,
      hst1, hbase1, hcls1, _, _, _, _, _, _, _, _, _⟩
  · exact Or.inl (hprefErr hSt)
  · right
    have hrf1 : RegsFuture st st1 := RegsFuture.same_regions (hnr1 ▸ Nat.le_refl _) hrg1
    have hIok1 : InterpOk σ st1 I :=
      ⟨fun rg hlt rc hrc => Nat.lt_of_lt_of_le (hsim.2.2.1.1 rg hlt rc hrc) hrf1.1,
       fun rc hrc => hsim.2.2.1.2 rc (hrg1 ▸ hrc)⟩
    have hpEnv1 : PreservesActiveEnv Scope env aenv σ st.heap st1.heap := fun i b ab hsc hbi habi hne haB =>
      hp1.mono fun l hl => (((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.2.2.2.2 haB).1.1.reach_lt_size hl
    have hsim1 := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok1 hrf1 hos1 hssf1 (fun _ _ _ h => h) hpEnv1 hsim
    have hpSS1 : PreservesLocs (StaticStrLoc st) st.heap st1.heap := hp1.mono fun _ h => StaticStrLoc_lt_size hst h
    have henvNRF1 := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim) hsim.2.2.2.1
      (hstat1 ▸ ArrayExtends.refl _) (hstr1 ▸ ArrayExtends.refl _) hpSS1 hpEnv1 henvNRF
    have hnv1 : NonValSafe st1.heap v1 := ClsSafe.to_nonValSafe hcNe hcls1 hbase1.1.self.1
    exact ⟨v1, st1, hprefOk v1 st1 hrun1, hrg1, hnr1, hstat1, hstr1, hsz1, hcap1,
      hp1, hos1, hssf1, hst1, hsim1, henvNRF1,
      VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) hsrcNone hbase1 hnv1,
      ValEnvDisj_nonValSafe hsrcNone hnv1 hsim1,
      NoReachForbid_nonValSafe hnv1⟩

private theorem list_getElem?_zip {α β : Type _} (xs : List α) (ys : List β) (i : Nat) :
    (xs.zip ys)[i]? = match xs[i]?, ys[i]? with | some a, some b => some (a, b) | _, _ => none := by
  induction xs generalizing ys i with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      cases i with
      | zero => simp
      | succ i' => simpa using ih ys i'

private theorem wrapperField?_kept {P : Prog} {k : CaseInfo} {wi : Nat}
    (h : P.wrapperField? k.ind = some wi) :
    ∃ f, (selectFieldsOf P k 0)[wi]? = some f ∧ f.kept = true := by
  unfold Prog.wrapperField? at h
  cases hsz : ((P.ctorsOf k.ind).size == 1) with
  | false =>
    simp only [guard, hsz, Bool.false_eq_true, ↓reduceIte, failure, Option.bind_eq_bind, Option.bind_none] at h
    cases h
  | true =>
    simp only [guard, hsz, ↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some] at h
    cases hc0 : (P.ctorsOf k.ind)[0]? with
    | none => rw [hc0] at h; cases h
    | some c =>
      rw [hc0] at h; dsimp only [Option.bind] at h
      cases hct : P.ctorOf? c with
      | none => rw [hct] at h; cases h
      | some q =>
        rcases q with ⟨ind', cidx', nP, fields⟩
        rw [hct] at h; dsimp only [Option.bind] at h
        have hsf : selectFieldsOf P k 0 = fields := by
          unfold selectFieldsOf; rw [hc0]; dsimp only; rw [hct]
        rw [hsf]
        let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
        cases hk1 : (kept.size == 1) with
        | false =>
          change (if (kept.size == 1) = true then pure () else none) >>= (fun _ => kept[0]?) = some wi at h
          rw [hk1] at h; cases h
        | true =>
          change (if (kept.size == 1) = true then pure () else none) >>= (fun _ => kept[0]?) = some wi at h
          rw [hk1] at h; simp only [↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some] at h
          have hmem : wi ∈ kept.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)
          exact (kept_mem_iff fields wi).mp hmem

private theorem caseField_basic {P : Prog} {k : CaseInfo} {fields : Array Field}
    {av_mv : AVal} {consuming : Bool} {q : Nat} {a0 : AVal} {er fc : Bool}
    (hcf : caseField P k fields av_mv consuming q = (a0, er, fc)) :
    a0.src = none ∧
    (∀ rg ∈ a0.regs, rg ∈ av_mv.regs) ∧
    (∀ d ∈ a0.deps, d ∈ av_mv.deps) ∧
    (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown) ∧
    (P.nat = some k.ind → a0 = { cls := natClass } ∧ er = false ∧ fc = false) ∧
    (P.nat ≠ some k.ind →
      match fields[q]? with
      | none => a0 = { cls := .irr } ∧ er = false ∧ fc = false
      | some f => er = (f.mode == .erased) ∧ (f.mode = .erased → a0 = { cls := .irr } ∧ fc = false)) := by
  unfold caseField at hcf
  by_cases hnat : P.nat = some k.ind
  · have hnatB : (some k.ind == P.nat) = true := by rw [hnat]; exact beq_self_eq_true _
    simp only [hnatB, ↓reduceIte, Prod.mk.injEq] at hcf
    obtain ⟨rfl, rfl, rfl⟩ := hcf
    exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
      fun _ => ⟨rfl, rfl, rfl⟩, fun hne => absurd hnat hne⟩
  · have hnatB : (some k.ind == P.nat) = false := by
      cases h : (some k.ind == P.nat) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h).symm hnat
    simp only [hnatB, Bool.false_eq_true, ↓reduceIte] at hcf
    cases hfq : fields[q]? with
    | none =>
      rw [hfq] at hcf; simp only [Prod.mk.injEq] at hcf
      obtain ⟨rfl, rfl, rfl⟩ := hcf
      exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
        fun h => absurd h hnat, fun _ => ⟨rfl, rfl, rfl⟩⟩
    | some f =>
      rw [hfq] at hcf; dsimp only at hcf
      by_cases her : (f.mode == .erased) = true
      · simp only [her, ↓reduceIte, Prod.mk.injEq] at hcf
        obtain ⟨rfl, rfl, rfl⟩ := hcf
        exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
          fun h => absurd h hnat, fun _ => ⟨her.symm, fun _ => ⟨rfl, rfl⟩⟩⟩
      · have herF : (f.mode == .erased) = false := Bool.eq_false_iff.mpr her
        have hmodeNe : f.mode ≠ .erased := fun hEq => by rw [hEq] at herF; cases herF
        simp only [herF, Bool.false_eq_true, ↓reduceIte] at hcf
        by_cases hcirr : (f.cls == .irr) = true
        · simp only [hcirr, ↓reduceIte, Prod.mk.injEq] at hcf
          obtain ⟨rfl, rfl, rfl⟩ := hcf
          exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
            fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩
        · simp only [hcirr, Bool.false_eq_true, ↓reduceIte] at hcf
          by_cases hwr : (av_mv.cls != .val && P.wrapperField? k.ind == some q) = true
          · simp only [hwr, ↓reduceIte, Prod.mk.injEq] at hcf
            obtain ⟨rfl, rfl, rfl⟩ := hcf
            exact ⟨rfl, fun _ h => h, fun _ h => h, (fun h => by cases h),
              fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩
          · simp only [hwr, Bool.false_eq_true, ↓reduceIte] at hcf
            by_cases hfne : (f.cls != .val) = true
            · simp only [hfne, ↓reduceIte, Prod.mk.injEq] at hcf
              obtain ⟨rfl, rfl, rfl⟩ := hcf
              exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
                fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩
            · simp only [hfne, Bool.false_eq_true, ↓reduceIte] at hcf
              by_cases hfsh : (f.fmode == .shared) = true
              · simp only [hfsh, ↓reduceIte, Prod.mk.injEq] at hcf
                obtain ⟨rfl, rfl, rfl⟩ := hcf
                exact ⟨rfl, fun _ h => h, fun _ h => h, fun _ => ⟨rfl, rfl, rfl⟩,
                  fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩
              · simp only [hfsh, Bool.false_eq_true, ↓reduceIte] at hcf
                cases consuming with
                | true =>
                  simp only [↓reduceIte, Prod.mk.injEq] at hcf
                  obtain ⟨rfl, rfl, rfl⟩ := hcf
                  exact ⟨rfl, fun _ h => h, (fun _ h => by cases h), fun _ => ⟨rfl, rfl, rfl⟩,
                    fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hcf
                  obtain ⟨rfl, rfl, rfl⟩ := hcf
                  exact ⟨rfl, fun _ h => h, fun _ h => h, fun _ => ⟨rfl, rfl, rfl⟩,
                    fun h => absurd h hnat, fun _ => ⟨herF.symm, fun h => absurd h hmodeNe⟩⟩

/-- **Bridge 8 (`select_caseAltArgs_bridge`)**: simulates `Eval.select P k mv` against
`ModeOk.caseAltArgs P k av_mv consuming cidx ca`, handling both active and spent `@once`
scrutinees across all 4 `select_spec` branches (`Nat`, all-`irr`, `wrapperCase`, `.ctor`),
producing exact erased-flag parity and `ArgListOk` for the alternative's field arguments. -/
theorem select_caseAltArgs_bridge {P : Prog} {ext : ExternOracle} {B : Nat}
    {k : CaseInfo} {consuming : Bool} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {mvFoot : Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {av_mv : AVal} {mv : Val}
    (hst : StOk P ext B st)
    (hidx : CtorsIndexed P)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hvdMv : ValidDeps σ av_mv.deps)
    (hvMv : VSim P ext B st Frame NoKill NoSpend σ I mvFoot av_mv mv)
    (hdisjMv : ValEnvDisj P st NoKill Scope env aenv σ envFoot mvFoot av_mv mv)
    (hnrfMv : ActiveVal σ av_mv → NoReachForbid st Forbid BadReg BadDep av_mv mv)
    (hcons : consuming = true →
      ActiveVal σ av_mv ∧ Transferable σ NoKill av_mv ∧ av_mv.deps = [] ∧ av_mv.src = none) :
    (select P k mv).run st = .error .stuck ∨
    ∃ cidx out st', (select P k mv).run st = .ok ((cidx, out), st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot ∧
      EnvNoReachForbid st' Scope env aenv σ Forbid BadReg BadDep ∧
      ∀ (ca : CaseAlt),
        (∀ (i₁ i₂ q : Nat), ca.args[i₁]? = some (.field q) → ca.args[i₂]? = some (.field q) → i₁ = i₂) →
        let cargs : List (Val × Bool) := ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)
        let aargs := caseAltArgs P k av_mv consuming cidx ca
        let argList : List (Option (Val × AVal × (Nat → Prop))) :=
          (cargs.zip aargs).map fun ((v, _), (a0, er, _)) =>
            if er then none else some (v, a0, fun _ => False)
        cargs.length = aargs.length ∧
        (∀ (idx : Nat) v er_c a0 er_a fc,
          cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
          er_c = er_a ∧ a0.src = none ∧ (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown)) ∧
        ArgListOk P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep argList := by
  -- Helper: build the final `ca` result when every concrete arg is `NonValSafe` (covers spent-once `.imm .irr`, `Nat`, all-irr, and `wrapperCase`).
  have hAllNonVal : ∀ (cidx : Nat) (out : Array (Val × Bool)) (st' : St),
      st'.regions = st.regions → st'.nextRegion = st.nextRegion →
      st'.statics = st.statics → st'.strs = st.strs →
      st.heap.objs.size ≤ st'.heap.objs.size → st.heap.nextCap ≤ st'.heap.nextCap →
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap →
      StOk P ext B st' →
      Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot →
      (∀ (q : Nat),
        let (v, er_c) := out[q]?.getD (.imm .irr, false)
        let (a0, er_a, _) := caseField P k (selectFieldsOf P k cidx) av_mv consuming q
        er_c = er_a ∧ ValBaseOk st' v ∧ NonValSafe st'.heap v) →
      ∀ (ca : CaseAlt),
        let cargs : List (Val × Bool) := ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)
        let aargs := caseAltArgs P k av_mv consuming cidx ca
        let argList : List (Option (Val × AVal × (Nat → Prop))) :=
          (cargs.zip aargs).map fun ((v, _), (a0, er, _)) =>
            if er then none else some (v, a0, fun _ => False)
        cargs.length = aargs.length ∧
        (∀ (idx : Nat) v er_c a0 er_a fc,
          cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
          er_c = er_a ∧ a0.src = none ∧ (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown)) ∧
        ArgListOk P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep argList := by
    intro cidx out st' _ _ _ _ _ _ _ _ hsim' hqOk ca cargs aargs argList
    have hlen : cargs.length = aargs.length := by simp [cargs, aargs, caseAltArgs]
    have hpairGet : ∀ (idx : Nat) v er_c a0 er_a fc,
        cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
        er_c = er_a ∧ a0.src = none ∧
        (∀ rg ∈ a0.regs, rg < σ.nextRegion) ∧ (∀ d ∈ a0.deps, d < σ.st.size) ∧
        (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown) ∧
        ValBaseOk st' v ∧ NonValSafe st'.heap v := by
      intro idx v er_c a0 er_a fc hc ha
      have hidxLt : idx < ca.args.size := by
        have := (List.getElem?_eq_some_iff.mp hc).1; simpa [cargs] using this
      have hfa : ca.args.toList[idx]? = some ca.args[idx] := by
        rw [List.getElem?_eq_getElem (by simpa using hidxLt)]; simp
      simp only [cargs, List.getElem?_map, hfa, Option.map_some, Option.some.injEq] at hc
      simp only [aargs, caseAltArgs, List.getElem?_map, hfa, Option.map_some, Option.some.injEq] at ha
      cases hfaE : ca.args[idx] with
      | irr =>
        rw [hfaE] at hc ha; cases hc; cases ha
        exact ⟨rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
          ValBaseOk_imm st' .irr, Or.inl ⟨.irr, rfl⟩⟩
      | unit =>
        rw [hfaE] at hc ha; cases hc; cases ha
        exact ⟨rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h),
          ValBaseOk_imm st' .irr, Or.inl ⟨.irr, rfl⟩⟩
      | field q =>
        rw [hfaE] at hc ha; dsimp only at hc ha
        have hq := hqOk q
        have ha' : caseField P k (selectFieldsOf P k cidx) av_mv consuming q = (a0, er_a, fc) := ha
        have hcb := caseField_basic ha'
        rw [hc, ha'] at hq
        exact ⟨hq.1, hcb.1, fun rg hrg => hvMv.1 rg (hcb.2.1 rg hrg),
          fun d hd => hvMv.2.1 d (hcb.2.2.1 d hd), hcb.2.2.2.1, hq.2.1, hq.2.2⟩
    refine ⟨hlen, fun idx v er_c a0 er_a fc hc ha =>
        let h := hpairGet idx v er_c a0 er_a fc hc ha; ⟨h.1, h.2.1, h.2.2.2.2.1⟩, ?_, ?_⟩
    · intro idx v av ft harg
      simp only [argList, List.getElem?_map, list_getElem?_zip] at harg
      cases hc : cargs[idx]? with
      | none => simp [hc] at harg
      | some pc =>
        cases ha : aargs[idx]? with
        | none => simp [hc, ha] at harg
        | some pa =>
          rcases pc with ⟨vc, er_c⟩; rcases pa with ⟨a0, er_a, fc⟩
          simp only [hc, ha, Option.map_some] at harg
          cases er_a with
          | true => simp at harg
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at harg
            obtain ⟨rfl, rfl, rfl⟩ := harg
            obtain ⟨_, hsrc, hregs, hdeps, _, hbv, hnv⟩ := hpairGet idx vc er_c a0 false fc hc ha
            exact ⟨VSim_nonValSafe hregs hdeps hsrc hbv hnv,
              ValEnvDisj_nonValSafe hsrc hnv hsim',
              fun _ => NoReachForbid_nonValSafe hnv,
              fun _ _ => ⟨hbv, hnv⟩⟩
    · intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ _ hi _
      simp only [argList, List.getElem?_map, list_getElem?_zip] at hi
      cases hc : cargs[i]? with
      | none => simp [hc] at hi
      | some pc =>
        cases ha : aargs[i]? with
        | none => simp [hc, ha] at hi
        | some pa =>
          rcases pc with ⟨vc, er_c⟩; rcases pa with ⟨a0, er_a, fc⟩
          simp only [hc, ha, Option.map_some] at hi
          cases er_a with
          | true => simp at hi
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hi
            obtain ⟨rfl, rfl, rfl⟩ := hi
            obtain ⟨_, _, _, _, _, _, hnv₁⟩ := hpairGet i vc er_c a0 false fc hc ha
            exact ⟨fun _ _ _ _ l hor _ => False.elim (hnv₁.ownTreeFull.2 l hor),
              fun _ _ _ _ _ h => False.elim h⟩
  -- Split: active `mv` vs spent-once `mv`
  by_cases haMv : ActiveVal σ av_mv
  · have hvMvAct := hvMv.2.2.2.2 haMv
    rcases select_spec (P := P) (k := k) (mv := mv) hidx hst.1 hvMvAct.1.1 hvMvAct.1.2.1 with
      hSt | ⟨cidx, out, st', hrunE, hrg', hnr', hstat', hstr', hsz', hcap', hp', hc', hoss', hnewNum, hcases⟩
    · exact Or.inl hSt
    · right
      have hos' : PreservesOnceShell st.heap st'.heap :=
        PreservesOnceShell.of_preservesLocs (hp'.mono fun l ⟨o, _, _, ho, _⟩ => (Array.getElem?_eq_some_iff.mp ho).1)
      have hssf' : StaticStrFresh st st' :=
        StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat' hstr'
          (hp'.mono fun _ h => h.1) (fun _ _ h => h)
      have hst' : StOk P ext B st' :=
        StOk_of_preserves_old hst hc' hrg' (hnr' ▸ Nat.le_refl _) hstat' hstr' hp'
      have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hrg'
      have hIok' : InterpOk σ st' I :=
        ⟨fun rg hlt rc hrc => Nat.lt_of_lt_of_le (hsim.2.2.1.1 rg hlt rc hrc) hrf'.1,
         fun rc hrc => hsim.2.2.1.2 rc (hrg' ▸ hrc)⟩
      have hpEnv' : PreservesActiveEnv Scope env aenv σ st.heap st'.heap := fun i b ab hsc hbi habi hne haB =>
        hp'.mono fun l hl => (((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.2.2.2.2 haB).1.1.reach_lt_size hl
      have hsim' := Sim_step (Nat.le_refl B) (AStateLe.refl σ) hsim.2.1 hIok' hrf' hos' hssf' (fun _ _ _ h => h) hpEnv' hsim
      have hpSS' : PreservesLocs (StaticStrLoc st) st.heap st'.heap := hp'.mono fun _ h => StaticStrLoc_lt_size hst h
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl σ) (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hpEnv' henvNRF
      refine ⟨cidx, out, st', hrunE, hrg', hnr', hstat', hstr', hsz', hcap', hp', hos', hssf',
        hst', hsim', henvNRF', fun ca hdist => ?_⟩
      rcases hcases with ⟨hnat, hnatCase⟩ | ⟨hnotNat, hIrrCase | hWrapCase | hCtorCase⟩
      · -- Branch 1: `P.nat = some k.ind`
        refine hAllNonVal cidx out st' hrg' hnr' hstat' hstr' hsz' hcap' hp' hst' hsim' (fun q => ?_) ca
        rcases hcfQ : caseField P k (selectFieldsOf P k cidx) av_mv consuming q with ⟨a0, er_a, fc⟩
        have hcb := (caseField_basic hcfQ).2.2.2.2.1 hnat
        dsimp only
        rcases hnatCase with ⟨hcEq, houtEq, hstEq⟩ | ⟨hcEq, m, v, houtEq, _, hdlV, hclsV, _, hacycV, _, _⟩
        · subst cidx; subst out; subst st'
          rw [hcb.2.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
        · subst cidx; subst out
          have hnvV : NonValSafe st'.heap v :=
            ClsSafe.to_nonValSafe (by decide : natClass ≠ .val) (ClsSafe.of_clsOk hclsV) hdlV.self.1
          have htbV : DeepTaintsBounded st'.heap st'.nextRegion v := by
            rcases hnvV with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, ho, _, hnum⟩
            · exact DeepTaintsBounded_imm _ _ _
            · exact DeepTaintsBounded_num ho hnum
          have hbvV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV htbV
          cases q with
          | zero =>
            simp only [Array.getElem?_eq_getElem (by simp : 0 < #[(v, false)].size), Option.getD_some]
            rw [hcb.2.1]; exact ⟨rfl, hbvV, hnvV⟩
          | succ q' =>
            have hnone : (#[(v, false)] : Array (Val × Bool))[q' + 1]? = none :=
              Array.getElem?_eq_none (by simp)
            simp only [hnone, Option.getD_none]
            rw [hcb.2.1]; exact ⟨rfl, ValBaseOk_imm st' .irr, Or.inl ⟨.irr, rfl⟩⟩
      · -- Branch 2: all-`irr`
        obtain ⟨hstEq, houtEq⟩ := hIrrCase; subst st'; subst out
        refine hAllNonVal cidx _ st hrg' hnr' hstat' hstr' hsz' hcap' hp' hst' hsim' (fun q => ?_) ca
        rcases hcfQ : caseField P k (selectFieldsOf P k cidx) av_mv consuming q with ⟨a0, er_a, fc⟩
        have hcb := (caseField_basic hcfQ).2.2.2.2.2 hnotNat
        dsimp only; rw [Array.getElem?_map]
        cases hfq : (selectFieldsOf P k cidx)[q]? with
        | none =>
          rw [hfq] at hcb; simp only [Option.map_none, Option.getD_none]
          rw [hcb.2.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
        | some f =>
          rw [hfq] at hcb; simp only [Option.map_some, Option.getD_some]
          rw [hcb.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
      · -- Branch 3: `wrapperCase`
        obtain ⟨hstEq, hcEq, wi, hwi, houtEq, hmvNV⟩ := hWrapCase; subst st'; subst cidx; subst out
        have hnvMv : NonValSafe st.heap mv := by
          rcases hmvNV with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, hnum⟩
          · exact Or.inl ⟨i, rfl⟩
          · obtain ⟨o', ho', hcap⟩ := hvMvAct.1.1.self.1
            rw [ho] at ho'; cases ho'
            exact Or.inr ⟨loc, cap, o, n, rfl, ho, hcap, hnum⟩
        obtain ⟨fwi, hfwi, hfwiKept⟩ := wrapperField?_kept hwi
        have hwiLt : wi < (selectFieldsOf P k 0).size := (Array.getElem?_eq_some_iff.mp hfwi).1
        have hwiLtMap : wi < ((selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased))).size := by
          simpa using hwiLt
        refine hAllNonVal 0 _ st hrg' hnr' hstat' hstr' hsz' hcap' hp' hst' hsim' (fun q => ?_) ca
        rcases hcfQ : caseField P k (selectFieldsOf P k 0) av_mv consuming q with ⟨a0, er_a, fc⟩
        have hcb := (caseField_basic hcfQ).2.2.2.2.2 hnotNat
        dsimp only
        by_cases hqEq : q = wi
        · subst hqEq
          rw [hfwi] at hcb
          have hget : (((selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased))).set! q (mv, false))[q]? =
              some (mv, false) := by
            simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, hwiLtMap, ↓reduceIte]
          rw [hget, Option.getD_some]
          have hneEr : (fwi.mode == .erased) = false := by
            unfold Field.kept at hfwiKept
            cases hm : fwi.mode <;> rw [hm] at hfwiKept <;> first | cases hfwiKept | rfl
          rw [hcb.1, hneEr]; exact ⟨rfl, hvMvAct.1, hnvMv⟩
        · have hget : (((selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased))).set! wi (mv, false))[q]? =
              ((selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased)))[q]? := by
            rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hqEq)]
          rw [hget, Array.getElem?_map]
          cases hfq : (selectFieldsOf P k 0)[q]? with
          | none =>
            rw [hfq] at hcb; simp only [Option.map_none, Option.getD_none]
            rw [hcb.2.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
          | some f =>
            rw [hfq] at hcb; simp only [Option.map_some, Option.getD_some]
            rw [hcb.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
      · -- Branch 4: `.ctor` cell!
        intro cargs aargs argList
        obtain ⟨loc, cap, t, o, r, fs, nP, fdefs, hmvEq, hoMv, hcapMv, hcellMv, hctorOf, hsfEq, houtSz, hfieldSpec, hpairSpec⟩ := hCtorCase
        -- Deduce `¬ IsOnceSrc σ av_mv` and `av_mv.cls = .val` from `.ctor` cell!
        have hnotOnceMv : ¬ IsOnceSrc σ av_mv := by
          intro his
          rcases hvMv.2.2.2.1 hvdMv his with h | ⟨_, _, _, o', _, _, hEq, ho', _, hc'⟩
          · rw [h] at hmvEq; cases hmvEq
          · rw [hmvEq] at hEq; cases hEq; rw [hoMv] at ho'; cases ho'; rw [hcellMv] at hc'; cases hc'
        have havMvCls : av_mv.cls = .val := by
          exact Classical.byContradiction fun hne => by
            rcases hvMvAct.2.2.2.1 hnotOnceMv hne with ⟨_, hEq⟩ | ⟨_, _, o', _, hEq, ho', _, hc'⟩
            · rw [hEq] at hmvEq; cases hmvEq
            · rw [hmvEq] at hEq; cases hEq; rw [hoMv] at ho'; cases ho'; rw [hcellMv] at hc'; cases hc'
        have hlen : cargs.length = aargs.length := by simp [cargs, aargs, caseAltArgs]
        -- Per-field lemma on `(out[q]?.getD ..., caseField P k fdefs av_mv consuming q)`
        have hfieldBridge : ∀ (q : Nat),
            let (v, er_c) := out[q]?.getD (.imm .irr, false)
            let (a0, er_a, fc) := caseField P k fdefs av_mv consuming q
            er_c = er_a ∧ a0.src = none ∧
            (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown) ∧
            (er_a = false →
              VSim P ext B st' Frame NoKill NoSpend σ I (fun _ => False) a0 v ∧
              ValEnvDisj P st' NoKill Scope env aenv σ envFoot (fun _ => False) a0 v ∧
              (ActiveVal σ a0 → NoReachForbid st' Forbid BadReg BadDep a0 v) ∧
              (ValidDeps σ a0.deps → a0.cls ≠ .val → ValBaseOk st' v ∧ NonValSafe st'.heap v) ∧
              (Transferable σ NoKill a0 → ∃ f, fdefs[q]? = some f ∧ f.fmode = .inherited ∧ consuming = true ∧ out[q]? = some (v, false))) := by
          intro q
          rcases hcfQ : caseField P k fdefs av_mv consuming q with ⟨a0, er_a, fc⟩
          have hcb := caseField_basic hcfQ
          have hcbN := hcb.2.2.2.2.2 hnotNat
          dsimp only
          cases hfq : fdefs[q]? with
          | none =>
            rw [hfq] at hcbN
            have hge : out.size ≤ q := by rw [houtSz]; exact (Array.getElem?_eq_none_iff.mp hfq)
            rw [Array.getElem?_eq_none hge, Option.getD_none, hcbN.1, hcbN.2.1]
            refine ⟨rfl, rfl, (fun h => by rw [hcbN.2.2] at h; cases h), fun _ => ?_⟩
            have hnv : NonValSafe st'.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
            exact ⟨VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl (ValBaseOk_imm st' .irr) hnv,
              ValEnvDisj_nonValSafe rfl hnv hsim', fun _ => NoReachForbid_nonValSafe hnv,
              fun _ _ => ⟨ValBaseOk_imm st' .irr, hnv⟩, (fun htr => by cases htr.1)⟩
          | some f =>
            rw [hfq] at hcbN; dsimp only at hcbN
            obtain ⟨v, hvOut, hnotKept, hkeptSpec⟩ := hfieldSpec q f hfq
            rw [hvOut, Option.getD_some]
            have hnatB : (some k.ind == P.nat) = false := by
              cases h : (some k.ind == P.nat) with
              | false => rfl
              | true => exact absurd (beq_iff_eq.mp h).symm hnotNat
            refine ⟨hcbN.1.symm, hcb.1, hcb.2.2.2.1, fun herF => ?_⟩
            have hmodeNe : f.mode ≠ .erased := by
              intro hEq; rw [hEq] at hcbN; rw [herF] at hcbN; cases hcbN.1
            have hmodeB : (f.mode == .erased) = false := BinderMode_beq_false_of_ne hmodeNe
            have hcfUnf : (a0, er_a, fc) =
                if f.cls == .irr then ({ cls := .irr }, false, false)
                else if f.cls != .val then ({ cls := f.cls }, false, false)
                else if f.fmode == .shared then ({ cls := .val, deps := av_mv.deps, regs := av_mv.regs }, false, (P.ctorsOf k.ind).size != 1)
                else if consuming then ({ cls := .val, own := .uniq, regs := av_mv.regs }, false, (P.ctorsOf k.ind).size != 1)
                else ({ cls := .val, deps := av_mv.deps, regs := av_mv.regs }, false, (P.ctorsOf k.ind).size != 1) := by
              rw [← hcfQ]; unfold caseField
              simp only [hnatB, Bool.false_eq_true, ↓reduceIte, hfq, hmodeB, havMvCls,
                show (Cls.val != Cls.val) = false from rfl, Bool.false_and]
            by_cases hcirr : f.cls = .irr
            · have hkf : f.kept = false := by unfold Field.kept; rw [hcirr]; exact Bool.and_false _
              have hvIrr : v = .imm .irr := hnotKept hkf
              have haEq : a0 = { cls := .irr } := by
                have := congrArg Prod.fst hcfUnf; rw [hcirr] at this; exact this
              rw [hvIrr, haEq]
              have hnv : NonValSafe st'.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
              exact ⟨VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl (ValBaseOk_imm st' .irr) hnv,
                ValEnvDisj_nonValSafe rfl hnv hsim', fun _ => NoReachForbid_nonValSafe hnv,
                fun _ _ => ⟨ValBaseOk_imm st' .irr, hnv⟩, (fun htr => by cases htr.1)⟩
            · have hkeptT : f.kept = true := by
                unfold Field.kept
                simp only [bne, BinderMode_beq_false_of_ne hmodeNe, Cls_beq_false_of_ne hcirr]; rfl
              obtain ⟨hrawMem, hrawVal, hclsV, hdlV, hacycV, htV, hneValT, hreachV, hheldV, hownV, htreeV, hdouV⟩ :=
                hkeptSpec hkeptT
              have hcirrB : (f.cls == .irr) = false := Cls_beq_false_of_ne hcirr
              by_cases hfVal : f.cls = .val
              · -- Kept `.val` field read out of `.ctor` cell!
                have hfneB : (f.cls != .val) = false := by rw [hfVal]; rfl
                let raw := fs[q]?.getD (.imm .irr)
                have hrawProps :
                    ValBaseOk st raw ∧ NoOnceCell st.heap raw ∧ CtorFieldsOk P ext B st raw ∧
                    FunOkAt P ext B st .unknown false (fun _ => False) raw ∧
                    DeepOpenUnder st.heap st.regions (I.regsOf av_mv.regs) raw ∧
                    (∀ l, Reach st.heap raw l → Reach st.heap mv l) := by
                  rcases hrawMem with hIrr | hInFs
                  · dsimp only [raw]; rw [hIrr]
                    exact ⟨ValBaseOk_imm st .irr, NoOnceCell_imm _ _,
                      ClsSafe_ctorFieldsOk P ext B st (by decide : Cls.irr ≠ .val) (ClsSafe.irr _ _),
                      FunOkAt_imm_irr .., DeepOpenUnder_imm _ _ _ _, (fun _ h => by cases h)⟩
                  · have hmVals : raw ∈ o.cell.vals := by rw [hcellMv]; exact hInFs
                    have hhb : HeldBy st.heap mv raw := Or.inr ⟨loc, o, by rw [hmvEq]; exact .here, hoMv, hmVals⟩
                    have hcfRaw := hvMvAct.2.2.1 loc o r fs raw (by rw [hmvEq]; exact .here) hoMv hcellMv hInFs
                    refine ⟨ValBaseOk_of_deepLive (hvMvAct.1.1.sub hhb) (hvMvAct.1.2.1.sub hhb)
                        (fun w hw => hvMvAct.1.2.2.2 w (hhb.trans hw)),
                      hcfRaw.1,
                      fun l' o' r' fs' w' hr' ho' hc' hw' =>
                        hvMvAct.2.2.1 l' o' r' fs' w' (Reach.step_trans (by rw [hmvEq]; exact .here) hoMv hmVals hr') ho' hc' hw',
                      hcfRaw.2,
                      fun w hw => hvMvAct.2.1 w (hhb.trans hw),
                      fun l hl => Reach.step_trans (by rw [hmvEq]; exact .here) hoMv hmVals hl⟩
                have hlocRaw : SameLoc raw v := by
                  rcases hrawVal hfVal with ⟨i, h1, h2⟩ | ⟨l', c', t1, t2, h1, h2⟩
                  · dsimp only [raw]; rw [h1, h2]; trivial
                  · dsimp only [raw]; rw [h1, h2]; rfl
                have htbV : DeepTaintsBounded st'.heap st'.nextRegion v := by
                  intro w hw rg hrg
                  rw [hnr']
                  rcases hheldV w hw with rfl | hhb
                  · rcases htV rg hrg with h1 | ⟨_, h2⟩
                    · exact hrawProps.1.2.2.2 raw (HeldBy.refl _ _) rg h1
                    · exact hvMvAct.1.2.2.2 mv (HeldBy.refl _ _) rg (by rw [hmvEq]; exact h2)
                  · exact hrawProps.1.2.2.2 w hhb rg hrg
                have hbaseV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV htbV
                have hnoV : NoOnceCell st'.heap v := by
                  intro l' o' hr' ho' tgt sp hcell'
                  have hrRaw : Reach st.heap raw l' := Reach_of_sameShapeOn_rev hrawProps.1.1 (hoss'.to_sameShapeOn _) hlocRaw hr'
                  have hlt : l' < st.heap.objs.size := hrawProps.1.1.reach_lt_size hrRaw
                  have ho0 : st.heap.objs[l']? = some o' := (hp' l' hlt).symm.trans ho'
                  exact hrawProps.2.1 l' o' hrRaw ho0 tgt sp hcell'
                have hcfV : CtorFieldsOk P ext B st' v :=
                  CtorFieldsOk_of_sameShape hrawProps.1.1 (hoss'.to_sameShapeOn _) hlocRaw hrf' hrawProps.2.2.1
                have hfunV : FunOkAt P ext B st' .unknown false (fun _ => False) v :=
                  FunOkAt_preserve_sameShape hlocRaw (hoss'.to_sameShapeOn _) hrf' hrawProps.2.2.2.1
                have hdouV' : DeepOpenUnder st'.heap st'.regions (I.regsOf av_mv.regs) v := by
                  rw [hrg']
                  exact hdouV st.regions (I.regsOf av_mv.regs) hrawProps.2.2.2.2.1
                    (fun _ => hvMvAct.2.1 mv (HeldBy.refl _ _))
                -- Express `a0` explicitly:
                have ha0Fields : a0.cls = .val ∧ a0.skel = .unknown ∧ a0.onceOnly = false ∧
                    a0.src = none ∧ a0.regs = av_mv.regs ∧
                    (a0.own = .uniq → f.fmode = .inherited ∧ consuming = true) ∧
                    (a0.deps = if f.fmode = .inherited ∧ consuming = true then [] else av_mv.deps) := by
                  have hfst := congrArg Prod.fst hcfUnf
                  simp only [hcirrB, hfneB, Bool.false_eq_true, ↓reduceIte] at hfst
                  cases hfm : f.fmode with
                  | shared =>
                    rw [hfm] at hfst
                    simp only [show (FieldMode.shared == FieldMode.shared) = true from rfl, ↓reduceIte] at hfst
                    rw [hfst]
                    exact ⟨rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), by simp⟩
                  | inherited =>
                    rw [hfm] at hfst
                    simp only [show (FieldMode.inherited == FieldMode.shared) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hfst
                    cases hconsB : consuming with
                    | true =>
                      rw [hconsB] at hfst; simp only [↓reduceIte] at hfst; rw [hfst]
                      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩
                    | false =>
                      rw [hconsB] at hfst; simp only [Bool.false_eq_true, ↓reduceIte] at hfst; rw [hfst]
                      exact ⟨rfl, rfl, rfl, rfl, rfl, (fun h => by cases h), rfl⟩
                have ha0NotOnce : ¬ IsOnceSrc σ a0 := by rintro ⟨_, hs, _⟩; rw [ha0Fields.2.2.2.1] at hs; cases hs
                have hreachMv : ∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ Reach st.heap mv l := fun l hr =>
                  (hreachV l hr).imp id (hrawProps.2.2.2.2.2 l)
                have htrA0 : Transferable σ NoKill a0 →
                    OwnTreeFull P st'.heap v ∧
                    ∀ l, OwnReach P st'.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st' l := by
                  intro htr
                  obtain ⟨hinh, hconsT⟩ := ha0Fields.2.2.2.2.2.1 htr.2.1
                  obtain ⟨_, htrMv, _, _⟩ := hcons hconsT
                  have hotMv := (hvMvAct.2.2.2.2.2.2.2 htrMv).1
                  refine ⟨htreeV hotMv hinh, fun l hor => ?_⟩
                  have horMv := (hownV l hor).2 hinh
                  have ⟨hnotF, hnotSS⟩ := (hvMvAct.2.2.2.2.2.2.2 htrMv).2 l horMv
                  exact ⟨hnotF, fun hss' => hnotSS (StaticStrLoc_unchanged hst hstat' hstr' hp' hss').1⟩
                have hvsimA0 : VSim P ext B st' Frame NoKill NoSpend σ I (fun _ => False) a0 v :=
                  ⟨fun rg hrg => hvMv.1 rg (ha0Fields.2.2.2.2.1 ▸ hrg),
                   fun d hd => hvMv.2.1 d (hcb.2.2.1 d hd),
                   (fun _ hs => by rw [ha0Fields.2.2.2.1] at hs; cases hs),
                   fun _ his => absurd his ha0NotOnce, fun _ =>
                    ⟨hbaseV, ha0Fields.2.2.2.2.1 ▸ hdouV', hcfV,
                     fun _ hne => absurd ha0Fields.1 hne,
                     fun _ => ⟨hnoV, fun _ h => h, ha0Fields.2.1 ▸ hfunV⟩,
                     (fun hoo => by rw [ha0Fields.2.2.1] at hoo; cases hoo),
                     fun his => absurd his ha0NotOnce, htrA0⟩⟩
                have hdisjA0 : ValEnvDisj P st' NoKill Scope env aenv σ envFoot (fun _ => False) a0 v := by
                  intro i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂
                  have hv₂ := ((hsim.2.2.2.2.2.1 i b₂ ab₂ hsc₂ hbi₂ habi₂).2 hne₂).2
                  refine ⟨?_, ?_, (fun _ hf => by
                      rcases hf with hoo | ⟨his, _⟩
                      · rw [ha0Fields.2.2.1] at hoo; cases hoo
                      · exact absurd his ha0NotOnce),
                    ?_,
                    (fun _ _ hs => by rw [ha0Fields.2.2.2.1] at hs; cases hs),
                    (fun hs => by rw [ha0Fields.2.2.2.1] at hs; cases hs),
                    (fun _ hs => by rw [ha0Fields.2.2.2.1] at hs; cases hs)⟩
                  · intro _ htrA ha₂ _ l horV hr₂'
                    obtain ⟨hinh, hconsT⟩ := ha0Fields.2.2.2.2.2.1 htrA.2.1
                    obtain ⟨_, htrMv, hdepsNil, _⟩ := hcons hconsT
                    have hpB := hpEnv' i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂
                    exact (hdisjMv i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).1 haMv htrMv ha₂
                      (fun d hd => by rw [hdepsNil] at hd; cases hd) l ((hownV l horV).2 hinh) ((Reach_congr hpB l).mp hr₂')
                  · intro ha₂ htr₂ _ hdisjD l hor₂' hrV'
                    have hpB := hpEnv' i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂ ha₂
                    have hor₂ := (OwnReach_congr hpB l).mp hor₂'
                    rcases hreachMv l hrV' with hge | hrMv
                    · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size (OwnReach_toReach hor₂))
                    · have hdisjMvD : ∀ d, d ∈ (effVal ab₂).deps → ¬ (d ∈ av_mv.deps) := by
                        intro d hdB hdMv
                        by_cases hc2 : f.fmode = .inherited ∧ consuming = true
                        · rw [(hcons hc2.2).2.2.1] at hdMv; cases hdMv
                        · have hdEq : a0.deps = av_mv.deps := by rw [ha0Fields.2.2.2.2.2.2]; simp [hc2]
                          exact hdisjD d hdB (hdEq ▸ hdMv)
                      exact (hdisjMv i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.1 ha₂ htr₂ haMv hdisjMvD l hor₂ hrMv
                  · intro ha₂ hf₂ _ _ l hft₂ hrV'
                    have hftR : Reach st.heap b₂.val l := by
                      rcases hf₂ with hoo2 | ⟨his2, _⟩
                      · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.1 hoo2).1 l hft₂).1
                      · exact (((hv₂.2.2.2.2 ha₂).2.2.2.2.2.2.1 his2).1 l hft₂).1
                    rcases hreachMv l hrV' with hge | hrMv
                    · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 ha₂).1.1.reach_lt_size hftR)
                    · have hneSrcMv : av_mv.src ≠ some ab₂.id := by
                        intro hEqSrc
                        rcases hf₂ with hoo2 | ⟨his2, _⟩
                        · rcases (hdisjMv i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.2.2.2 haMv hEqSrc with hlocB | hnumB
                          · cases hbV : b₂.val with
                            | imm _ => rw [hbV, hmvEq] at hlocB; cases hlocB
                            | ref lB cB tB =>
                              rw [hbV, hmvEq] at hlocB; dsimp only [SameLoc] at hlocB; subst hlocB
                              exact ((hv₂.2.2.2.2 ha₂).2.2.2.2.2.1 hoo2).2.2.1 lB cB tB o r fs hbV hoMv hcellMv l hft₂
                          · obtain ⟨o', n', ho', hc'⟩ := hnumB loc (by rw [hmvEq]; exact .here)
                            rw [hoMv] at ho'; cases ho'; rw [hcellMv] at hc'; cases hc'
                        · obtain ⟨id, hs2, ho2⟩ := his2
                          dsimp [effVal] at hs2; cases hs2
                          exact hnotOnceMv ⟨ab₂.id, hEqSrc, ho2⟩
                      exact (hdisjMv i b₂ ab₂ hsc₂ hbi₂ habi₂ hne₂).2.2.2.1 ha₂ hf₂ haMv hneSrcMv l hft₂ hrMv
                have hnrfA0 : ActiveVal σ a0 → NoReachForbid st' Forbid BadReg BadDep a0 v := by
                  intro _ hbadR hbadD l hrV' hnotSS' hnotNum' hF
                  rcases hreachMv l hrV' with hge | hrMv
                  · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
                  · have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
                      hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hss0)
                    have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o', n', ho', hnum'⟩ =>
                      hnotNum' ⟨o', n', PreservesLocs_old_num hp' l o' n' ho' hnum', hnum'⟩
                    have hbadDMv : ∀ d ∈ av_mv.deps, ¬ BadDep d := by
                      intro d hd
                      by_cases hc2 : f.fmode = .inherited ∧ consuming = true
                      · rw [(hcons hc2.2).2.2.1] at hd; cases hd
                      · have hdEq : a0.deps = av_mv.deps := by rw [ha0Fields.2.2.2.2.2.2]; simp [hc2]
                        exact hbadD d (hdEq ▸ hd)
                    exact hnrfMv haMv (ha0Fields.2.2.2.2.1 ▸ hbadR) hbadDMv l hrMv hnotSS0 hnotNum0 hF
                refine ⟨hvsimA0, hdisjA0, hnrfA0, fun _ hne => absurd ha0Fields.1 hne, fun htr => ?_⟩
                obtain ⟨hinh, hconsT⟩ := ha0Fields.2.2.2.2.2.1 htr.2.1
                exact ⟨f, rfl, hinh, hconsT, by rw [hmodeB]⟩
              · -- Kept non-`.val` field (`f.cls = .imm ∨ f.cls = .leaf`)!
                have hfneB : (f.cls != .val) = true := by simp [bne, Cls_beq_false_of_ne hfVal]
                have haEq : a0 = { cls := f.cls } := by
                  have hfst := congrArg Prod.fst hcfUnf
                  simp only [hcirrB, Bool.false_eq_true, ↓reduceIte, hfneB] at hfst
                  exact hfst
                have hnvV : NonValSafe st'.heap v :=
                  ClsSafe.to_nonValSafe hfVal (ClsSafe.of_clsOk hclsV) hdlV.self.1
                have htbV : DeepTaintsBounded st'.heap st'.nextRegion v := by
                  rcases hnvV with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, ho, _, hnum⟩
                  · exact DeepTaintsBounded_imm _ _ _
                  · exact DeepTaintsBounded_num ho hnum
                have hbvV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV htbV
                rw [haEq]
                exact ⟨VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl hbvV hnvV,
                  ValEnvDisj_nonValSafe rfl hnvV hsim', fun _ => NoReachForbid_nonValSafe hnvV,
                  fun _ _ => ⟨hbvV, hnvV⟩, (fun htr => by cases htr.2.1)⟩
        have hitemEq : ∀ (idx : Nat) v er_c a0 er_a fc,
            cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
            er_c = er_a ∧ a0.src = none ∧
            (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown) ∧
            (er_a = false →
              VSim P ext B st' Frame NoKill NoSpend σ I (fun _ => False) a0 v ∧
              ValEnvDisj P st' NoKill Scope env aenv σ envFoot (fun _ => False) a0 v ∧
              (ActiveVal σ a0 → NoReachForbid st' Forbid BadReg BadDep a0 v) ∧
              (ValidDeps σ a0.deps → a0.cls ≠ .val → ValBaseOk st' v ∧ NonValSafe st'.heap v) ∧
              (Transferable σ NoKill a0 → ∃ q f, ca.args[idx]? = some (.field q) ∧
                fdefs[q]? = some f ∧ f.fmode = .inherited ∧ consuming = true ∧ out[q]? = some (v, false)) ∧
              (∀ l, Reach st'.heap v l → ∃ q, ca.args[idx]? = some (.field q) ∧
                ∃ f, fdefs[q]? = some f ∧ out[q]? = some (v, false))) := by
          intro idx v er_c a0 er_a fc hc ha
          have hidxLt : idx < ca.args.size := by
            have := (List.getElem?_eq_some_iff.mp hc).1; simpa [cargs] using this
          have hfaL : ca.args.toList[idx]? = some ca.args[idx] := by
            rw [List.getElem?_eq_getElem (by simpa using hidxLt)]; simp
          have hfaA : ca.args[idx]? = some ca.args[idx] := Array.getElem?_eq_getElem hidxLt
          simp only [cargs, List.getElem?_map, hfaL, Option.map_some, Option.some.injEq] at hc
          simp only [aargs, caseAltArgs, List.getElem?_map, hfaL, Option.map_some, Option.some.injEq] at ha
          cases hfaE : ca.args[idx] with
          | irr =>
            rw [hfaE] at hc ha; cases hc; cases ha
            have hnv : NonValSafe st'.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
            exact ⟨rfl, rfl, (fun h => by cases h), fun _ =>
              ⟨VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl (ValBaseOk_imm st' .irr) hnv,
               ValEnvDisj_nonValSafe rfl hnv hsim', fun _ => NoReachForbid_nonValSafe hnv,
               fun _ _ => ⟨ValBaseOk_imm st' .irr, hnv⟩, (fun htr => by cases htr.1), (fun _ hr => by cases hr)⟩⟩
          | unit =>
            rw [hfaE] at hc ha; cases hc; cases ha
            have hnv : NonValSafe st'.heap (.imm .irr) := Or.inl ⟨.irr, rfl⟩
            exact ⟨rfl, rfl, (fun h => by cases h), fun _ =>
              ⟨VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl (ValBaseOk_imm st' .irr) hnv,
               ValEnvDisj_nonValSafe rfl hnv hsim', fun _ => NoReachForbid_nonValSafe hnv,
               fun _ _ => ⟨ValBaseOk_imm st' .irr, hnv⟩, (fun htr => by cases htr.1), (fun _ hr => by cases hr)⟩⟩
          | field q =>
            rw [hfaE] at hc ha hfaA; dsimp only at hc ha
            have hfb := hfieldBridge q
            have ha' : caseField P k fdefs av_mv consuming q = (a0, er_a, fc) := by
              change caseField P k (selectFieldsOf P k cidx) av_mv consuming q = (a0, er_a, fc) at ha
              rwa [hsfEq] at ha
            rw [hc, ha'] at hfb
            refine ⟨hfb.1, hfb.2.1, hfb.2.2.1, fun herF => ?_⟩
            obtain ⟨hv0, hd0, hn0, hnv0, htr0⟩ := hfb.2.2.2 herF
            refine ⟨hv0, hd0, hn0, hnv0, fun htr => let ⟨f, hfq, hinh, hct, hoq⟩ := htr0 htr; ⟨q, f, hfaA, hfq, hinh, hct, hoq⟩,
              fun l hr => ?_⟩
            cases hfq : fdefs[q]? with
            | none =>
              have hge : out.size ≤ q := by rw [houtSz]; exact Array.getElem?_eq_none_iff.mp hfq
              rw [Array.getElem?_eq_none hge, Option.getD_none] at hc
              cases hc; cases hr
            | some f =>
              obtain ⟨v', hv', _, _⟩ := hfieldSpec q f hfq
              rw [hv', Option.getD_some] at hc; cases hc
              exact ⟨q, hfaA, f, hfq, by rw [← herF, ← hfb.1]; exact hv'⟩
        refine ⟨hlen, fun idx v er_c a0 er_a fc hc ha =>
            let h := hitemEq idx v er_c a0 er_a fc hc ha; ⟨h.1, h.2.1, h.2.2.1⟩, ?_, ?_⟩
        · intro idx v av ft harg
          simp only [argList, List.getElem?_map, list_getElem?_zip] at harg
          cases hc : cargs[idx]? with
          | none => simp [hc] at harg
          | some pc =>
            cases ha : aargs[idx]? with
            | none => simp [hc, ha] at harg
            | some pa =>
              rcases pc with ⟨vc, er_c⟩; rcases pa with ⟨a0, er_a, fc⟩
              simp only [hc, ha, Option.map_some] at harg
              cases er_a with
              | true => simp at harg
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at harg
                obtain ⟨rfl, rfl, rfl⟩ := harg
                obtain ⟨_, _, _, hok⟩ := hitemEq idx vc er_c a0 false fc hc ha
                obtain ⟨hv0, hd0, hn0, hnv0, _, _⟩ := hok rfl
                exact ⟨hv0, hd0, hn0, hnv0⟩
        · intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hi hj
          simp only [argList, List.getElem?_map, list_getElem?_zip] at hi hj
          cases hc1 : cargs[i]? with
          | none => simp [hc1] at hi
          | some pc1 =>
            cases ha1 : aargs[i]? with
            | none => simp [hc1, ha1] at hi
            | some pa1 =>
              cases hc2 : cargs[j]? with
              | none => simp [hc2] at hj
              | some pc2 =>
                cases ha2 : aargs[j]? with
                | none => simp [hc2, ha2] at hj
                | some pa2 =>
                  rcases pc1 with ⟨vc1, er_c1⟩; rcases pa1 with ⟨a01, er_a1, fc1⟩
                  rcases pc2 with ⟨vc2, er_c2⟩; rcases pa2 with ⟨a02, er_a2, fc2⟩
                  simp only [hc1, ha1, Option.map_some] at hi
                  simp only [hc2, ha2, Option.map_some] at hj
                  cases er_a1 with
                  | true => simp at hi
                  | false =>
                    cases er_a2 with
                    | true => simp at hj
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hi hj
                      obtain ⟨rfl, rfl, rfl⟩ := hi; obtain ⟨rfl, rfl, rfl⟩ := hj
                      obtain ⟨_, _, _, hok1⟩ := hitemEq i vc1 er_c1 a01 false fc1 hc1 ha1
                      obtain ⟨_, _, _, hok2⟩ := hitemEq j vc2 er_c2 a02 false fc2 hc2 ha2
                      refine ⟨fun _ htr1 _ _ l hor1 hr2 => ?_, fun _ _ _ _ _ h => False.elim h⟩
                      obtain ⟨q1, f1, hfa1, hfq1, hinh1, hconsT, hoq1⟩ := (hok1 rfl).2.2.2.2.1 htr1
                      obtain ⟨q2, hfa2, f2, hfq2, hoq2⟩ := (hok2 rfl).2.2.2.2.2 l hr2
                      have hqNe : q1 ≠ q2 := fun hEq => hij (hdist i j q1 hfa1 (hEq ▸ hfa2))
                      have hotMv := (hvMvAct.2.2.2.2.2.2.2 (hcons hconsT).2.1).1
                      exact hpairSpec hotMv q1 q2 f1 f2 vc1 vc2 false false hqNe hfq1 hfq2 hoq1 hoq2 hinh1 l hor1 hr2
  · -- Spent-once `mv`: `SpentOnceSafe st.heap mv`!
    have hisMv : IsOnceSrc σ av_mv :=
      Classical.byContradiction fun hnot => haMv ⟨hvdMv, fun his => absurd his hnot⟩
    rcases hvMv.2.2.2.1 hvdMv hisMv with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩
    · -- `mv = .imm .irr`
      by_cases hnat : P.nat = some k.ind
      · left
        unfold select
        have hnatB : (P.nat == some k.ind) = true := by rw [hnat]; exact beq_self_eq_true _
        simp only [hnatB, ↓reduceIte, M_bind_run]
        have hnum : (numOf? (.imm .irr)).run st = .ok (none, st) := rfl
        rw [hnum]; rfl
      · have hnatB : (P.nat == some k.ind) = false := by
          cases h : (P.nat == some k.ind) with
          | false => rfl
          | true => exact absurd (beq_iff_eq.mp h) hnat
        by_cases hsz1 : ((P.ctorsOf k.ind).size == 1) = true
        · right
          have hrunE : (select P k (.imm .irr)).run st =
              .ok ((0, (selectFieldsOf P k 0).map (fun f => (Val.imm .irr, f.mode == .erased))), st) := by
            unfold select
            simp only [hnatB, Bool.false_eq_true, ↓reduceIte, hsz1, M_pure_run]
            rfl
          refine ⟨0, _, st, hrunE, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
            PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _, hst, hsim, henvNRF,
            fun ca _ => hAllNonVal 0 _ st rfl rfl rfl rfl (Nat.le_refl _) (Nat.le_refl _)
              (PreservesLocs.refl _ _) hst hsim (fun q => ?_) ca⟩
          rcases hcfQ : caseField P k (selectFieldsOf P k 0) av_mv consuming q with ⟨a0, er_a, fc⟩
          have hcb := (caseField_basic hcfQ).2.2.2.2.2 hnat
          dsimp only; rw [Array.getElem?_map]
          cases hfq : (selectFieldsOf P k 0)[q]? with
          | none =>
            rw [hfq] at hcb; simp only [Option.map_none, Option.getD_none]
            rw [hcb.2.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
          | some f =>
            rw [hfq] at hcb; simp only [Option.map_some, Option.getD_some]
            rw [hcb.1]; exact ⟨rfl, ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩
        · left
          unfold select
          simp only [hnatB, hsz1, Bool.false_eq_true, ↓reduceIte]; rfl
    · -- `mv = .ref loc cap t` pointing to `.once tgt sp` cell -> ALWAYS `.error .stuck`!
      left
      have hlive : LiveRef st.heap (.ref loc cap t) := ⟨o, ho, hcap⟩
      unfold select
      by_cases hnat : (P.nat == some k.ind) = true
      · simp only [hnat, ↓reduceIte, M_bind_run, numOf?_ok hlive, ho, hcell]; rfl
      · simp only [hnat, Bool.false_eq_true, ↓reduceIte, M_bind_run]
        have hobj : (obj loc).run st = .ok (o, st) := by unfold obj; simp [ho]; rfl
        rw [hobj]; dsimp only
        simp only [hcap, beq_self_eq_true, ↓reduceIte, hcell]; rfl

/-! ## 8. Bridge 9 (`acaps_formClosure_bridge` & `clo_call_sim_of_captures`) -/

private theorem foldl_set_live_spec (owned : List Nat) (arr : Array BSt) :
    (owned.foldl (fun a x => a.set! x BSt.live) arr).size = arr.size ∧
    ∀ i, i < arr.size →
      (owned.foldl (fun a x => a.set! x BSt.live) arr)[i]? =
        if i ∈ owned then some .live else arr[i]? := by
  induction owned generalizing arr with
  | nil => exact ⟨rfl, fun _ _ => by simp⟩
  | cons y ys ih =>
    simp only [List.foldl_cons]
    let arr' := arr.set! y BSt.live
    have hsz' : arr'.size = arr.size := by
      simp [arr', Array.set!_eq_setIfInBounds]
    obtain ⟨hsz, hget⟩ := ih arr'
    refine ⟨hsz.trans hsz', fun i hi => ?_⟩
    rw [hget i (hsz'.symm ▸ hi)]
    by_cases hys : i ∈ ys
    · have hmem : i ∈ y :: ys := List.mem_cons_of_mem y hys
      simp only [hys, hmem, ↓reduceIte]
    · simp only [hys, ↓reduceIte]
      by_cases hy : i = y
      · subst hy
        have hmem : i ∈ i :: ys := List.mem_cons_self
        simp only [hmem, ↓reduceIte, arr', Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self, hi]
      · have hnotMem : i ∉ y :: ys := by
          intro h; rcases List.mem_cons.mp h with rfl | h'
          · exact hy rfl
          · exact hys h'
        simp only [hnotMem, ↓reduceIte, arr', Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm hy)]

private theorem restoreOwned_spec (owned : List Nat) (σ : AState) :
    (restoreOwned owned σ).st.size = σ.st.size ∧
    (restoreOwned owned σ).once = σ.once ∧
    (restoreOwned owned σ).spent = σ.spent ∧
    (restoreOwned owned σ).regions = σ.regions ∧
    (restoreOwned owned σ).nextRegion = σ.nextRegion ∧
    (∀ i, i < σ.st.size →
      (restoreOwned owned σ).st[i]? = if i ∈ owned then some .live else σ.st[i]?) ∧
    (AStateOk σ → AStateOk (restoreOwned owned σ)) := by
  obtain ⟨hsz, hget⟩ := foldl_set_live_spec owned σ.st
  refine ⟨hsz, rfl, rfl, rfl, rfl, hget, fun hok => ?_⟩
  exact ⟨hsz.trans hok.1, hsz.trans hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2⟩

private theorem OwnReach_of_sameShapeOn_rev {P : Prog} {h₁ h₂ : Heap} {v₁ v₂ : Val} {l : Nat}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hr : OwnReach P h₂ v₂ l) : OwnReach P h₁ v₁ l := by
  induction hr generalizing v₁ with
  | @here loc cap t o₂ ho₂ hnot₂ =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₁, ho₁, _⟩ := hdl.self.1
      obtain ⟨o₂', ho₂', hcs⟩ := hs l₁ o₁ .here ho₁
      rw [ho₂] at ho₂'; cases ho₂'
      have hnot₁ : o₁.cell.isNum = false ∨ natClass ≠ .leaf := by
        rw [hcs.isNum_eq]; exact hnot₂
      exact .here ho₁ hnot₁
  | @step loc cap t o₂ i sv₂ l' ho₂ hi₂ hs₂ _ ih =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₁, ho₁, _⟩ := hdl.self.1
      obtain ⟨o₂', ho₂', hcs⟩ := hs l₁ o₁ .here ho₁
      rw [ho₂] at ho₂'; cases ho₂'
      have hi₁ : i ∈ ownedSlots P o₁.cell := by rw [hcs.ownedSlots_eq]; exact hi₂
      have hslot := hcs.slot? i
      cases hs₁ : o₁.cell.slot? i with
      | none => simp [hs₁, hs₂] at hslot
      | some sv₁ =>
        simp only [hs₁, hs₂] at hslot
        have hmem₁ : sv₁ ∈ o₁.cell.vals := mem_vals_of_ownedSlot hi₁ hs₁
        have hdl' : DeepLive h₁ sv₁ := hdl.sub (HeldBy_of_mem_vals ho₁ hmem₁)
        have hs' : SameShapeOn (Reach h₁ sv₁) h₁ h₂ := hs.mono fun x hx => .step ho₁ hmem₁ hx
        exact .step ho₁ hi₁ hs₁ (ih hdl' hs' (SameLoc.of_valSameShape hslot))

private theorem OwnTreeFull_of_sameShapeOn {P : Prog} {h₁ h₂ : Heap} {v₁ v₂ : Val}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (ht : OwnTreeFull P h₁ v₁) : OwnTreeFull P h₂ v₂ := by
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
    have hp₁' := OwnReach_of_sameShapeOn_rev hdl hs hloc hp₁
    have hp₂' := OwnReach_of_sameShapeOn_rev hdl hs hloc hp₂
    have hrp₁ : Reach h₁ v₁ p₁ := OwnReach_toReach hp₁'
    have hrp₂ : Reach h₁ v₁ p₂ := OwnReach_toReach hp₂'
    obtain ⟨o₁', ho₁'⟩ := hdl.exists_obj hrp₁
    obtain ⟨o₂', ho₂'⟩ := hdl.exists_obj hrp₂
    obtain ⟨o₁b, ho₁b, hsh₁⟩ := hs p₁ o₁' hrp₁ ho₁'
    obtain ⟨o₂b, ho₂b, hsh₂⟩ := hs p₂ o₂' hrp₂ ho₂'
    rw [ho₁] at ho₁b; cases ho₁b
    rw [ho₂] at ho₂b; cases ho₂b
    have hslot1 := hsh₁.slot? i₁
    have hslot2 := hsh₂.slot? i₂
    cases hs₁' : o₁'.cell.slot? i₁ with
    | none => simp [hs₁, hs₁'] at hslot1
    | some w₁' =>
      cases hs₂' : o₂'.cell.slot? i₂ with
      | none => simp [hs₂, hs₂'] at hslot2
      | some w₂' =>
        simp only [hs₁, hs₁'] at hslot1
        simp only [hs₂, hs₂'] at hslot2
        cases w₁' with
        | imm _ => exact False.elim hslot1
        | ref l₁' c₁' t₁' =>
          cases w₂' with
          | imm _ => exact False.elim hslot2
          | ref l₂' c₂' t₂' =>
            rcases hslot1 with ⟨hl1, _⟩; subst l₁'
            rcases hslot2 with ⟨hl2, _⟩; subst l₂'
            have hi₁' : i₁ ∈ ownedSlots P o₁'.cell := by rw [hsh₁.ownedSlots_eq]; exact hi₁
            have hi₂' : i₂ ∈ ownedSlots P o₂'.cell := by rw [hsh₂.ownedSlots_eq]; exact hi₂
            have hrl₁ : Reach h₁ v₁ l :=
              Reach.step_trans hrp₁ ho₁' (mem_vals_of_ownedSlot hi₁' hs₁') .here
            have hnl' : ∀ (o : Obj), h₁.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf := by
              intro o ho
              obtain ⟨o', ho', hsho⟩ := hs l o hrl₁ ho
              rw [hsho.isNum_eq]
              exact hnl o' ho'
            exact ht.1 p₁ p₂ i₁ i₂ l c₁' c₂' o₁' o₂' t₁' t₂' hp₁' hp₂' ho₁' ho₂' hi₁' hi₂' hs₁' hs₂' hnl'
  · intro p l i o₂ r fs₂ w₂ hrp2 ho2 hcell2 hi2 hs2 hrl2 hwl2
    have hrp1 := OwnReach_of_sameShapeOn_rev hdl hs hloc hrp2
    have hrl1 := OwnReach_of_sameShapeOn_rev hdl hs hloc hrl2
    have hRp1 : Reach h₁ v₁ p := OwnReach_toReach hrp1
    obtain ⟨o₁, ho1⟩ := hdl.exists_obj hRp1
    obtain ⟨o₂', ho2', hsh⟩ := hs p o₁ hRp1 ho1
    rw [ho2] at ho2'; cases ho2'
    have hi1 : i ∉ ownedSlots P o₁.cell := by rw [hsh.ownedSlots_eq]; exact hi2
    cases hcell1 : o₁.cell with
    | ctor r₁ fs₁ =>
      have hsh' : CellSameShape (.ctor r₁ fs₁) (.ctor r fs₂) := by
        rw [← hcell1, ← hcell2]; exact hsh
      rcases hsh' with ⟨rfl, hsz, hfs⟩
      obtain ⟨hlt2, hw2eq⟩ := Array.getElem?_eq_some_iff.mp hs2
      have hlt1 : i < fs₁.size := hsz ▸ hlt2
      have hs1 : fs₁[i]? = some fs₁[i] := Array.getElem?_eq_getElem hlt1
      have hwsh : ValSameShape fs₁[i] w₂ := hw2eq ▸ hfs i hlt1 hlt2
      have hmem1 : fs₁[i] ∈ o₁.cell.vals := by
        rw [hcell1]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hlt1)
      have hdlW : DeepLive h₁ fs₁[i] := hdl.sub (Or.inr ⟨p, o₁, hRp1, ho1, hmem1⟩)
      have hsW : SameShapeOn (Reach h₁ fs₁[i]) h₁ h₂ :=
        hs.mono fun x hx => Reach.step_trans hRp1 ho1 hmem1 hx
      exact ht.2 p l i o₁ r₁ fs₁ fs₁[i] hrp1 ho1 hcell1 hi1 hs1 hrl1
        (Reach_of_sameShapeOn_rev hdlW hsW (SameLoc.of_valSameShape hwsh) hwl2)
    | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
      rw [hcell1, hcell2] at hsh; exact hsh

private theorem DeepOpenUnder_of_sameShapeOn {h₁ h₂ : Heap} {rs A : List Nat} {v₁ v₂ : Val}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hvs : ValSameShape v₁ v₂)
    (hdou : DeepOpenUnder h₁ rs A v₁) : DeepOpenUnder h₂ rs A v₂ := by
  intro w₂ hw₂ r hr hopen
  rcases hw₂ with rfl | ⟨l, o₂, hr₂, ho₂, hm₂⟩
  · rw [← hvs.taint_eq] at hr
    exact hdou v₁ (HeldBy.refl _ _) r hr hopen
  · have hr₁ := Reach_of_sameShapeOn_rev hdl hs (SameLoc.of_valSameShape hvs) hr₂
    obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hr₁
    obtain ⟨o₂', ho₂', hcs⟩ := hs l o₁ hr₁ ho₁
    rw [ho₂] at ho₂'; cases ho₂'
    obtain ⟨w₁, hm₁, hvsW⟩ := hcs.symm.vals_fwd hm₂
    rw [hvsW.taint_eq] at hr
    exact hdou w₁ (Or.inr ⟨l, o₁, hr₁, ho₁, hm₁⟩) r hr hopen

/-- Complete structural unpacking of `ModeOk.ACaps`: state monotonicity, per-capture checks
and ownership/sharing effects, accumulator provenance, and pairwise dep-disjointness for
`formClosure_sound`'s `hdisj`. -/
private theorem ACaps_info {aenv : List ABnd} {fvs : List Nat} {σ σ₁ : AState}
    {deps₀ regs₀ owned₀ deps regs owned : List Nat}
    (hok : AStateOk σ)
    (hcaps : ACaps aenv fvs σ deps₀ regs₀ owned₀ deps regs owned σ₁) :
    AStateOk σ₁ ∧ AStateLe σ σ₁ ∧
    σ₁.st.size = σ.st.size ∧ σ₁.once = σ.once ∧ σ₁.spent.size = σ.spent.size ∧
    σ₁.regions = σ.regions ∧ σ₁.nextRegion = σ.nextRegion ∧
    (∀ d ∈ deps₀, d ∈ deps) ∧ (∀ rg ∈ regs₀, rg ∈ regs) ∧
    (∀ i ∈ fvs, ∃ ab, aenv[i]? = some ab ∧ ab.mode ≠ .erased ∧
      ValidDeps σ (effVal ab).deps ∧ (effVal ab).onceOnly = false ∧ ¬ IsOnceSrc σ (effVal ab) ∧
      (∀ rg ∈ (effVal ab).regs, rg ∈ regs) ∧
      (ab.mode.isUnique = true → ab.id ∈ owned ∧
        ((effVal ab).cls = .val → (effVal ab).own = .uniq ∧
          (∀ d ∈ (effVal ab).deps, σ.st[d]? = some .live ∧ σ₁.st[d]? = some .dead) ∧
          (ab.mode.isBorrowed = false → (effVal ab).regs = []))) ∧
      (ab.mode.isUnique = false → (∀ d ∈ (effVal ab).deps, d ∈ deps) ∧
        ((effVal ab).cls = .val → ∀ d ∈ (effVal ab).deps, σ₁.st[d]? ≠ some .live))) ∧
    (∀ d ∈ deps, d ∈ deps₀ ∨ ∃ i ∈ fvs, ∃ ab, aenv[i]? = some ab ∧ ab.mode.isUnique = false ∧ d ∈ (effVal ab).deps) ∧
    (∀ rg ∈ regs, rg ∈ regs₀ ∨ ∃ i ∈ fvs, ∃ ab, aenv[i]? = some ab ∧ rg ∈ (effVal ab).regs) ∧
    (∀ x, x ∈ owned ↔ x ∈ owned₀ ∨ ∃ i ∈ fvs, ∃ ab, aenv[i]? = some ab ∧ ab.mode.isUnique = true ∧ x = ab.id) ∧
    (∀ d, d < σ.st.size → σ₁.st[d]? = some .dead →
      σ.st[d]? = some .dead ∨
      ∃ i ∈ fvs, ∃ ab, aenv[i]? = some ab ∧ ab.mode.isUnique = true ∧ (effVal ab).cls = .val ∧ d ∈ (effVal ab).deps) ∧
    (∀ (a b ia ib : Nat) aba abb, a ≠ b →
      fvs[a]? = some ia → fvs[b]? = some ib →
      aenv[ia]? = some aba → aenv[ib]? = some abb →
      aba.mode.isUnique = true → (effVal aba).cls = .val → (effVal abb).cls = .val →
      ∀ d ∈ (effVal aba).deps, d ∉ (effVal abb).deps) := by
  induction hcaps with
  | nil =>
    refine ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, fun _ h => h, fun _ h => h,
      (fun _ h => by cases h), fun _ h => Or.inl h, fun _ h => Or.inl h,
      fun _ => ⟨fun h => Or.inl h, fun h => h.elim id (fun ⟨_, h', _⟩ => by cases h')⟩,
      fun _ _ h => Or.inl h, fun _ _ _ _ _ _ _ ha => by cases ha⟩
  | @consUniq i rest b v σ σa σ₂ deps₀ regs₀ owned₀ deps regs owned σ' hbi hread htr hflow hrest ih =>
    obtain ⟨b', hbi', hneB, rfl, hvd0, hσaEq⟩ := Runs_readVar hread
    rw [hbi] at hbi'; cases hbi'
    subst σa
    have huniq : b.mode.isUnique = true := htr
    obtain ⟨hok₂, hle₂, hszSt₂, honce₂, hszSp₂, hreg₂, hnr₂, _, _, hnonOnce, _, _, _, _, huniqFlow⟩ :=
      Runs_flowTo hok hflow
    obtain ⟨_, hoo, hnotOnce⟩ := hnonOnce (fun h => by cases h)
    obtain ⟨hflowVal, hst₂⟩ := huniqFlow b.mode.isBorrowed rfl
    obtain ⟨hok', hle', hszSt', honce', hszSp', hreg', hnr', hdepsSub, hregsSub, hrestMem,
      hdepsProv, hregsProv, hownedIff, hdeadProv, hpairRest⟩ := ih hok₂
    have hleAll : AStateLe σ σ' := hle₂.trans hle'
    have hszAll : σ'.st.size = σ.st.size := hszSt'.trans hszSt₂
    have honceAll : σ'.once = σ.once := honce'.trans honce₂
    have hdeadOfLe : ∀ d, d < σ.st.size → σ₂.st[d]? = some .dead → σ'.st[d]? = some .dead := by
      intro d hd hdead
      have h1 := hle'.2.2.1 d (hszSt₂.symm ▸ hd)
      rw [hdead] at h1
      cases h2 : σ'.st[d]? with
      | none => rw [h2] at h1; cases h1
      | some bst =>
        rw [h2] at h1
        cases bst with
        | dead => rfl
        | live | shared => exact False.elim h1
    have hliveOfLe : ∀ d, d < σ.st.size → σ₂.st[d]? = some .live → σ.st[d]? = some .live := by
      intro d hd hlv
      have h1 := hle₂.2.2.1 d hd
      rw [hlv] at h1
      cases h0 : σ.st[d]? with
      | none => rw [h0] at h1; cases h1
      | some bst =>
        rw [h0] at h1
        cases bst with
        | live => rfl
        | shared | dead => exact False.elim h1
    refine ⟨hok', hleAll, hszAll, honceAll, hszSp'.trans hszSp₂, hreg'.trans hreg₂, hnr'.trans hnr₂,
      hdepsSub, fun rg hrg => hregsSub rg (mem_natUnion.mpr (Or.inl hrg)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hmem
      · refine ⟨b, hbi, hneB, hvd0, hoo, hnotOnce,
          fun rg hrg => hregsSub rg (mem_natUnion.mpr (Or.inr hrg)),
          fun _ => ⟨(hownedIff b.id).mpr (Or.inl List.mem_cons_self), fun hcv => ?_⟩,
          fun hnf => absurd huniq (by rw [hnf]; decide)⟩
        obtain ⟨hown, hlv, hbr⟩ := hflowVal hcv
        refine ⟨hown, fun d hd => ⟨hlv d hd, hdeadOfLe d (hvd0 d hd).1 ?_⟩, hbr⟩
        rw [hst₂ d (hvd0 d hd).1]; simp only [hcv, hd, and_self, ↓reduceIte]
      · obtain ⟨ab, habj, hneAb, hvd₂, hooAb, hnotOnce₂, hregsAb, huAb, hshAb⟩ := hrestMem j hmem
        have hvdAb0 : ValidDeps σ (effVal ab).deps :=
          ValidDeps.of_AStateLe hle₂ (fun d hd => hszSt₂ ▸ (hvd₂ d hd).1) hvd₂
        have hnotOnceAb0 : ¬ IsOnceSrc σ (effVal ab) := fun ⟨id, hsrc, ho⟩ =>
          hnotOnce₂ ⟨id, hsrc, by rw [honce₂]; exact ho⟩
        refine ⟨ab, habj, hneAb, hvdAb0, hooAb, hnotOnceAb0, hregsAb, fun hu => ?_, hshAb⟩
        obtain ⟨hownMem, hvalCase⟩ := huAb hu
        refine ⟨hownMem, fun hcv => ?_⟩
        obtain ⟨hown, hlv₂, hbr⟩ := hvalCase hcv
        exact ⟨hown, fun d hd => ⟨hliveOfLe d (hvdAb0 d hd).1 (hlv₂ d hd).1, (hlv₂ d hd).2⟩, hbr⟩
    · intro d hd
      rcases hdepsProv d hd with h0 | ⟨j, hj, ab, habj, hnu, hdAb⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hnu, hdAb⟩
    · intro rg hrg
      rcases hregsProv rg hrg with h0 | ⟨j, hj, ab, habj, hrgAb⟩
      · rcases mem_natUnion.mp h0 with h0' | hvb
        · exact Or.inl h0'
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, hvb⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hrgAb⟩
    · intro x
      rw [hownedIff x, List.mem_cons]
      constructor
      · rintro ((rfl | h0) | ⟨j, hj, ab, habj, hu, rfl⟩)
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, huniq, rfl⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hu, rfl⟩
      · rintro (h0 | ⟨j, hj, ab, habj, hu, rfl⟩)
        · exact Or.inl (Or.inr h0)
        · rcases List.mem_cons.mp hj with rfl | hj'
          · rw [hbi] at habj; cases habj; exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨j, hj', ab, habj, hu, rfl⟩
    · intro d hd hdead
      rcases hdeadProv d (hszSt₂.symm ▸ hd) hdead with hdead₂ | ⟨j, hj, ab, habj, hu, hcv, hdAb⟩
      · rw [hst₂ d hd] at hdead₂
        by_cases hc : (effVal b).cls = .val ∧ d ∈ (effVal b).deps
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, huniq, hc.1, hc.2⟩
        · simp only [hc, ↓reduceIte] at hdead₂
          exact Or.inl hdead₂
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hu, hcv, hdAb⟩
    · intro a bIdx ia ib aba abb hab hfa hfb haba habb hua hca hcb d hdA hdB
      cases a with
      | zero =>
        cases bIdx with
        | zero => exact absurd rfl hab
        | succ b' =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hfa; subst hfa
          simp only [List.getElem?_cons_succ] at hfb
          rw [hbi] at haba; cases haba
          have hmemB : ib ∈ rest := List.mem_of_getElem? hfb
          obtain ⟨abB, habB, _, hvdB, _, _, _, _, _⟩ := hrestMem ib hmemB
          rw [habb] at habB; cases habB
          have hdead₂ : σ₂.st[d]? = some .dead := by
            rw [hst₂ d (hvd0 d hdA).1]; simp only [hca, hdA, and_self, ↓reduceIte]
          exact (hvdB d hdB).2 hdead₂
      | succ a' =>
        cases bIdx with
        | zero =>
          simp only [List.getElem?_cons_succ] at hfa
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hfb; subst hfb
          rw [hbi] at habb; cases habb
          have hmemA : ia ∈ rest := List.mem_of_getElem? hfa
          obtain ⟨abA, habA, _, hvdA, _, _, _, _, _⟩ := hrestMem ia hmemA
          rw [haba] at habA; cases habA
          have hdead₂ : σ₂.st[d]? = some .dead := by
            rw [hst₂ d (hvd0 d hdB).1]; simp only [hcb, hdB, and_self, ↓reduceIte]
          exact (hvdA d hdA).2 hdead₂
        | succ b' =>
          simp only [List.getElem?_cons_succ] at hfa hfb
          exact hpairRest a' b' ia ib aba abb (fun h => hab (congrArg Nat.succ h)) hfa hfb haba habb hua hca hcb d hdA hdB
  | @consShare i rest b v σ σa σ₂ deps₀ regs₀ owned₀ deps regs owned σ' hbi hread htr hflow hrest ih =>
    obtain ⟨b', hbi', hneB, rfl, hvd0, hσaEq⟩ := Runs_readVar hread
    rw [hbi] at hbi'; cases hbi'
    subst σa
    have hnotUniq : b.mode.isUnique = false := htr
    obtain ⟨hok₂, hle₂, hszSt₂, honce₂, hszSp₂, hreg₂, hnr₂, _, _, hnonOnce, _, _, hstSh₂, _, _⟩ :=
      Runs_flowTo hok hflow
    obtain ⟨_, hoo, hnotOnce⟩ := hnonOnce (fun h => by cases h)
    have hst₂ := hstSh₂ rfl
    obtain ⟨hok', hle', hszSt', honce', hszSp', hreg', hnr', hdepsSub, hregsSub, hrestMem,
      hdepsProv, hregsProv, hownedIff, hdeadProv, hpairRest⟩ := ih hok₂
    have hleAll : AStateLe σ σ' := hle₂.trans hle'
    have hszAll : σ'.st.size = σ.st.size := hszSt'.trans hszSt₂
    have honceAll : σ'.once = σ.once := honce'.trans honce₂
    have hnotLiveOfLe : ∀ d, d < σ.st.size → σ₂.st[d]? ≠ some .live → σ'.st[d]? ≠ some .live := by
      intro d hd hnl hlv'
      have h1 := hle'.2.2.1 d (hszSt₂.symm ▸ hd)
      rw [hlv'] at h1
      cases h2 : σ₂.st[d]? with
      | none => rw [h2] at h1; cases h1
      | some bst =>
        rw [h2] at h1
        cases bst with
        | live => exact hnl h2
        | shared | dead => exact h1
    have hliveOfLe : ∀ d, d < σ.st.size → σ₂.st[d]? = some .live → σ.st[d]? = some .live := by
      intro d hd hlv
      have h1 := hle₂.2.2.1 d hd
      rw [hlv] at h1
      cases h0 : σ.st[d]? with
      | none => rw [h0] at h1; cases h1
      | some bst =>
        rw [h0] at h1
        cases bst with
        | live => rfl
        | shared | dead => exact False.elim h1
    refine ⟨hok', hleAll, hszAll, honceAll, hszSp'.trans hszSp₂, hreg'.trans hreg₂, hnr'.trans hnr₂,
      fun d hd => hdepsSub d (mem_natUnion.mpr (Or.inl hd)),
      fun rg hrg => hregsSub rg (mem_natUnion.mpr (Or.inl hrg)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hmem
      · refine ⟨b, hbi, hneB, hvd0, hoo, hnotOnce,
          fun rg hrg => hregsSub rg (mem_natUnion.mpr (Or.inr hrg)),
          fun hu => absurd hnotUniq (by rw [hu]; decide),
          fun _ => ⟨fun d hd => hdepsSub d (mem_natUnion.mpr (Or.inr hd)), fun hcv d hd => ?_⟩⟩
        apply hnotLiveOfLe d (hvd0 d hd).1
        rw [hst₂ d (hvd0 d hd).1]
        by_cases hlv0 : σ.st[d]? = some .live
        · simp only [hcv, hd, hlv0, and_self, ↓reduceIte]; intro h; cases h
        · have hcf : ¬ ((effVal b).cls = .val ∧ d ∈ (effVal b).deps ∧ σ.st[d]? = some .live) := fun h => hlv0 h.2.2
          simp only [hcf, ↓reduceIte]; exact hlv0
      · obtain ⟨ab, habj, hneAb, hvd₂, hooAb, hnotOnce₂, hregsAb, huAb, hshAb⟩ := hrestMem j hmem
        have hvdAb0 : ValidDeps σ (effVal ab).deps :=
          ValidDeps.of_AStateLe hle₂ (fun d hd => hszSt₂ ▸ (hvd₂ d hd).1) hvd₂
        have hnotOnceAb0 : ¬ IsOnceSrc σ (effVal ab) := fun ⟨id, hsrc, ho⟩ =>
          hnotOnce₂ ⟨id, hsrc, by rw [honce₂]; exact ho⟩
        refine ⟨ab, habj, hneAb, hvdAb0, hooAb, hnotOnceAb0, hregsAb, fun hu => ?_, hshAb⟩
        obtain ⟨hownMem, hvalCase⟩ := huAb hu
        refine ⟨hownMem, fun hcv => ?_⟩
        obtain ⟨hown, hlv₂, hbr⟩ := hvalCase hcv
        exact ⟨hown, fun d hd => ⟨hliveOfLe d (hvdAb0 d hd).1 (hlv₂ d hd).1, (hlv₂ d hd).2⟩, hbr⟩
    · intro d hd
      rcases hdepsProv d hd with h0 | ⟨j, hj, ab, habj, hnu, hdAb⟩
      · rcases mem_natUnion.mp h0 with h0' | hdb
        · exact Or.inl h0'
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, hnotUniq, hdb⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hnu, hdAb⟩
    · intro rg hrg
      rcases hregsProv rg hrg with h0 | ⟨j, hj, ab, habj, hrgAb⟩
      · rcases mem_natUnion.mp h0 with h0' | hvb
        · exact Or.inl h0'
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, hvb⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hrgAb⟩
    · intro x
      rw [hownedIff x]
      constructor
      · rintro (h0 | ⟨j, hj, ab, habj, hu, rfl⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hu, rfl⟩
      · rintro (h0 | ⟨j, hj, ab, habj, hu, rfl⟩)
        · exact Or.inl h0
        · rcases List.mem_cons.mp hj with rfl | hj'
          · rw [hbi] at habj; cases habj; rw [hnotUniq] at hu; cases hu
          · exact Or.inr ⟨j, hj', ab, habj, hu, rfl⟩
    · intro d hd hdead
      rcases hdeadProv d (hszSt₂.symm ▸ hd) hdead with hdead₂ | ⟨j, hj, ab, habj, hu, hcv, hdAb⟩
      · rw [hst₂ d hd] at hdead₂
        by_cases hc : (effVal b).cls = .val ∧ d ∈ (effVal b).deps ∧ σ.st[d]? = some .live
        · simp only [hc] at hdead₂; cases hdead₂
        · simp only [hc, ↓reduceIte] at hdead₂
          exact Or.inl hdead₂
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, ab, habj, hu, hcv, hdAb⟩
    · intro a bIdx ia ib aba abb hab hfa hfb haba habb hua hca hcb d hdA hdB
      cases a with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hfa; subst hfa
        rw [hbi] at haba; cases haba
        rw [hnotUniq] at hua; cases hua
      | succ a' =>
        cases bIdx with
        | zero =>
          simp only [List.getElem?_cons_succ] at hfa
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hfb; subst hfb
          rw [hbi] at habb; cases habb
          have hmemA : ia ∈ rest := List.mem_of_getElem? hfa
          obtain ⟨abA, habA, _, _, _, _, _, huA, _⟩ := hrestMem ia hmemA
          rw [haba] at habA; cases habA
          obtain ⟨_, hvalA⟩ := huA hua
          have hlv₂ : σ₂.st[d]? = some .live := ((hvalA hca).2.1 d hdA).1
          rw [hst₂ d (hvd0 d hdB).1] at hlv₂
          by_cases hlv0 : σ.st[d]? = some .live
          · simp only [hcb, hdB, hlv0, and_self, ↓reduceIte] at hlv₂; cases hlv₂
          · have hcf : ¬ ((effVal b).cls = .val ∧ d ∈ (effVal b).deps ∧ σ.st[d]? = some .live) := fun h => hlv0 h.2.2
            simp only [hcf, ↓reduceIte] at hlv₂
            exact hlv0 hlv₂
        | succ b' =>
          simp only [List.getElem?_cons_succ] at hfa hfb
          exact hpairRest a' b' ia ib aba abb (fun h => hab (congrArg Nat.succ h)) hfa hfb haba habb hua hca hcb d hdA hdB

/-- **Bridge 9a (`acaps_formClosure_bridge`)**: simulates `ACaps` + `formClosure` for `ATerm.lam`,
advancing the environment simulation to `σ_end = { σ₁ with nextRegion := nextReg_end }` and
producing `ValEnvDisj`, `NoReachForbid`, `cloFoot`, capture preservation witnesses, and `VSim`
parameterized on `FunOkAt` for the newly allocated `.clo` cell. -/
theorem acaps_formClosure_bridge {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {deps regs owned : List Nat} {nextReg_end : Nat} {consumed : Bool} {r_body_skel : Skel}
    (hst : StOk P ext B st)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hNoKill : NoKillOk NoKill σ₁)
    (hBadDep : ∀ d, BadDep d → σ₁.st[d]? = some .live)
    (hfvsScope : ∀ i ∈ fvs.toList, Scope i)
    (hcaps : ACaps aenv fvs.toList σ [] [] [] deps regs owned σ₁)
    (hnextLe : σ₁.nextRegion ≤ nextReg_end) :
    let σ_end : AState := { σ₁ with nextRegion := nextReg_end }
    let I_end : Interp := ⟨fun r => if r < σ₁.nextRegion then I.reg r else []⟩
    let cloAv : AVal := { cls := .val, deps := deps, regs := regs, onceOnly := consumed, skel := .arrow p.mode p.skel res r_body_skel }
    let cloFoot : Nat → Prop := fun l =>
      consumed = true ∧ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧
        b.mode.isUnique = true ∧ OwnReach P st.heap b.val l
    AStateOk σ₁ ∧ AStateLe σ σ₁ ∧ AStateOk σ_end ∧ AStateLe σ σ_end ∧
    (∀ r, r < σ.nextRegion → I_end.reg r = I.reg r) ∧
    ((formClosure P fuel env p res rc fvs body).run st = .error .stuck ∨
     (formClosure P fuel env p res rc fvs body).run st = .error .outOfFuel ∨
     ∃ rv env' taint st',
       (formClosure P fuel env p res rc fvs body).run st = .ok (rv, st') ∧
       st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
       st'.statics = st.statics ∧ st'.strs = st.strs ∧
       st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
       OldSameShape st.heap st'.heap ∧
       PreservesLocs Frame st.heap st'.heap ∧
       PreservesOnceShell st.heap st'.heap ∧
       StaticStrFresh st st' ∧
       StOk P ext B st' ∧
       Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ_end I_end envFoot ∧
       EnvNoReachForbid st' Scope env aenv σ_end Forbid BadReg BadDep ∧
       (∃ cap, rv = .ref st.heap.objs.size cap taint ∧
         st'.heap.objs[st.heap.objs.size]? = some ⟨.clo env' p res rc fvs body, cap⟩) ∧
       env'.length = env.length ∧
       (∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
         ValSameShape b.val v' ∧ ValBaseOk st' v' ∧ NoOnceCell st'.heap v' ∧
         CtorFieldsOk P ext B st' v' ∧
         (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot b.val →
           FunOkAt P ext B st' sk onceOnly Foot v')) ∧
       ValBaseOk st' rv ∧
       NoOnceCell st'.heap rv ∧
       CtorFieldsOk P ext B st' rv ∧
       DeepOpenUnder st'.heap st'.regions (I_end.regsOf cloAv.regs) rv ∧
       (∀ l, Reach st'.heap rv l →
         l = st.heap.objs.size ∨ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ Reach st.heap b.val l) ∧
       (∀ l, cloFoot l → Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
       (FunOkAt P ext B st' cloAv.skel consumed cloFoot rv →
         VSim P ext B st' Frame NoKill NoSpend σ_end I_end cloFoot cloAv rv) ∧
       ValEnvDisj P st' NoKill Scope env aenv σ_end envFoot cloFoot cloAv rv ∧
       (ActiveVal σ_end cloAv → NoReachForbid st' Forbid BadReg BadDep cloAv rv)) := by
  intro σ_end I_end cloAv cloFoot
  obtain ⟨hok₁, hle₁, hszSt₁, honce₁, hszSp₁, hreg₁, hnr₁, _, _, hcapMem,
    hdepsProv, hregsProv, _, _, hpairCaps⟩ := ACaps_info hsim.2.1 hcaps
  have hokEnd : AStateOk σ_end :=
    ⟨hok₁.1, hok₁.2.1, Nat.le_trans hok₁.2.2.1 hnextLe, hok₁.2.2.2.1, hok₁.2.2.2.2.1,
     fun r hr => let ⟨h1, h2⟩ := hok₁.2.2.2.2.2 r hr; ⟨h1, Nat.lt_of_lt_of_le h2 hnextLe⟩⟩
  have hleEnd : AStateLe σ σ_end :=
    ⟨hle₁.1, Nat.le_trans hle₁.2.1 hnextLe, hle₁.2.2.1, hle₁.2.2.2.1, hle₁.2.2.2.2⟩
  have hIendEq : ∀ r, r < σ.nextRegion → I_end.reg r = I.reg r := by
    intro r hr
    have hr1 : r < σ₁.nextRegion := hnr₁ ▸ hr
    dsimp only [I_end]; simp only [hr1, ↓reduceIte]
  -- Helper: extract capture `VSim` & `Transferable` facts for any `i ∈ fvs.toList`
  have hcapInfo : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b →
      ∃ ab, aenv[i]? = some ab ∧ b.mode = ab.mode ∧ ab.mode ≠ .erased ∧
        ActiveVal σ (effVal ab) ∧ (effVal ab).onceOnly = false ∧ ¬ IsOnceSrc σ (effVal ab) ∧
        VSim P ext B st Frame NoKill NoSpend σ I (envFoot i) (effVal ab) b.val ∧
        (ab.mode.isUnique = true → (effVal ab).cls = .val →
          Transferable σ NoKill (effVal ab) ∧
          (∀ d ∈ (effVal ab).deps, σ₁.st[d]? = some .dead) ∧
          (ab.mode.isBorrowed = false → (effVal ab).regs = [])) := by
    intro i hi b hbi
    obtain ⟨ab, habi, hneAb, hvdAb, hooAb, hnotOnce, _, huAb, _⟩ := hcapMem i hi
    obtain ⟨hmode, hneBody⟩ := hsim.2.2.2.2.2.1 i b ab (hfvsScope i hi) hbi habi
    obtain ⟨_, hvB⟩ := hneBody hneAb
    have hactAb : ActiveVal σ (effVal ab) := ⟨hvdAb, fun his => absurd his hnotOnce⟩
    refine ⟨ab, habi, hmode, hneAb, hactAb, hooAb, hnotOnce, hvB, fun hu hcv => ?_⟩
    obtain ⟨_, hvalC⟩ := huAb hu
    obtain ⟨hown, hlvDead, hbr⟩ := hvalC hcv
    refine ⟨⟨hcv, hown, hooAb, hnotOnce, fun d hd => ⟨(hlvDead d hd).1, fun hnk => hNoKill d hnk (hlvDead d hd).2⟩⟩,
      fun d hd => (hlvDead d hd).2, hbr⟩
  -- Build `formClosure_sound` preconditions
  have hfvsCond : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b →
      b.mode ≠ .erased ∧ ValBaseOk st b.val ∧ NoOnceCell st.heap b.val ∧ CtorFieldsOk P ext B st b.val ∧
      (b.mode.isUnique = true →
        OwnTreeFull P st.heap b.val ∧
        (b.mode.isBorrowed = false → OpenUnder st.regions [] b.val) ∧
        ∀ l, OwnReach P st.heap b.val l → ¬ StaticStrLoc st l) := by
    intro i hi b hbi
    obtain ⟨ab, _, hmode, hneAb, hactAb, hooAb, hnotOnce, hvB, huTr⟩ := hcapInfo i hi b hbi
    have hvAct := hvB.2.2.2.2 hactAb
    have hnoB := (hvAct.2.2.2.2.1 ⟨hnotOnce, hooAb⟩).1
    refine ⟨hmode ▸ hneAb, hvAct.1, hnoB, hvAct.2.2.1, fun huB => ?_⟩
    have huAb : ab.mode.isUnique = true := hmode ▸ huB
    by_cases hcv : (effVal ab).cls = .val
    · obtain ⟨htrAb, _, hbrAb⟩ := huTr huAb hcv
      obtain ⟨hot, hownF⟩ := hvAct.2.2.2.2.2.2.2 htrAb
      refine ⟨hot, fun hnb => ?_, fun l hor => (hownF l hor).2⟩
      have hregsNil := hbrAb (hmode ▸ hnb)
      have hdou := hvAct.2.1
      rw [hregsNil, Interp.regsOf_nil] at hdou
      exact hdou.self
    · have hnv := hvAct.2.2.2.1 hnotOnce hcv
      exact ⟨hnv.ownTreeFull.1, fun _ => hnv.deepOpenUnder_nil.self,
        fun l hor => False.elim (hnv.ownTreeFull.2 l hor)⟩
  have hdisjCond : ∀ (a bIdx : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ bIdx →
      fvs.toList[a]? = some ia → fvs.toList[bIdx]? = some ib →
      env[ia]? = some ba → env[ib]? = some bb →
      ba.mode.isUnique = true →
      ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l := by
    intro a bIdx ia ib ba bb hab hfa hfb hba hbb huA l horA hrB
    have hiaMem : ia ∈ fvs.toList := List.mem_of_getElem? hfa
    have hibMem : ib ∈ fvs.toList := List.mem_of_getElem? hfb
    obtain ⟨aba, haba, hmodeA, hneA, hactA, _, hnotOnceA, hvA, huTrA⟩ := hcapInfo ia hiaMem ba hba
    obtain ⟨abb, habb, _, hneB, hactB, _, hnotOnceB, hvB, _⟩ := hcapInfo ib hibMem bb hbb
    have huAbA : aba.mode.isUnique = true := hmodeA ▸ huA
    have hcvA : (effVal aba).cls = .val := by
      exact Classical.byContradiction fun hne =>
        ((hvA.2.2.2.2 hactA).2.2.2.1 hnotOnceA hne).ownTreeFull.2 l horA
    by_cases hcvB : (effVal abb).cls = .val
    · have hdepsDisj := hpairCaps a bIdx ia ib aba abb hab hfa hfb haba habb huAbA hcvA hcvB
      have hiaNe : ia ≠ ib := by
        intro hEq; subst hEq
        rw [haba] at habb; cases habb
        exact hdepsDisj aba.id (List.mem_cons_self) (List.mem_cons_self)
      obtain ⟨htrA, _, _⟩ := huTrA huAbA hcvA
      exact (hsim.2.2.2.2.2.2 ia ib ba bb aba abb hiaNe (hfvsScope ia hiaMem) (hfvsScope ib hibMem)
        hba haba hbb habb hneA hneB).1 hactA htrA hactB hdepsDisj l horA hrB
    · have hnvB := (hvB.2.2.2.2 hactB).2.2.2.1 hnotOnceB hcvB
      exact OwnReach_not_numLoc horA (hnvB.reach_numLoc hrB)
  refine ⟨hok₁, hle₁, hokEnd, hleEnd, hIendEq, ?_⟩
  rcases formClosure_sound (P := P) (ext := ext) (B := B) (fuel := fuel)
      (p := p) (res := res) (rc := rc) (fvs := fvs) (body := body) hst hfvsCond hdisjCond with
    hSt | hOOF | ⟨rv, env', taint, st', hrun, hrg', hnrSt', hstat', hstr', hsz', hcap',
      hoss', hpres', hos', hssf', hst', hrvObj, hcapProps, henvOut, hbaseRv, hnoRv, hcfRv, hdouRv, hreachRv⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnrSt' ▸ Nat.le_refl _) hrg'
    have hIokEnd : InterpOk σ_end st' I_end := by
      refine ⟨fun r hr c hc => ?_, fun c hc => ?_⟩
      · dsimp only [I_end] at hc
        by_cases hr1 : r < σ₁.nextRegion
        · simp only [hr1, ↓reduceIte] at hc
          exact hnrSt' ▸ hsim.2.2.1.1 r (hnr₁ ▸ hr1) c hc
        · simp only [hr1, ↓reduceIte] at hc; cases hc
      · have hhdLt : σ.regions.headD 1 < σ.nextRegion := by
          cases hreg : σ.regions with
          | nil => dsimp only [List.headD]; exact Nat.lt_of_lt_of_le (by decide : 1 < 2) hsim.2.1.2.2.1
          | cons r0 rs => exact (hsim.2.1.2.2.2.2.2 r0 (hreg ▸ List.mem_cons_self)).2
        have hhdEq : σ_end.regions.headD 1 = σ.regions.headD 1 := by simp [σ_end, hreg₁]
        rw [hhdEq, hIendEq _ hhdLt]
        exact hsim.2.2.1.2 c (hrg' ▸ hc)
    have hPresFrame : PreservesLocs Frame st.heap st'.heap := by
      refine hpres'.mono fun l hF => ⟨hFrameLt l hF, fun i hi b hbi huB hor => ?_⟩
      obtain ⟨ab, _, hmode, _, hactAb, _, hnotOnce, hvB, huTr⟩ := hcapInfo i hi b hbi
      by_cases hcv : (effVal ab).cls = .val
      · obtain ⟨htrAb, _, _⟩ := huTr (hmode ▸ huB) hcv
        exact ((hvB.2.2.2.2 hactAb).2.2.2.2.2.2.2 htrAb).2 l hor |>.1 hF
      · exact ((hvB.2.2.2.2 hactAb).2.2.2.1 hnotOnce hcv).ownTreeFull.2 l hor
    have hPresEnv : PreservesActiveEnv Scope env aenv σ_end st.heap st'.heap := by
      intro j bj abj hscJ hbj habj hneJ hactEndJ
      have hact0J : ActiveVal σ (effVal abj) :=
        ActiveVal.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
          (Sim_src_lt hsim j abj habj) hactEndJ
      have hvJ := ((hsim.2.2.2.2.2.1 j bj abj hscJ hbj habj).2 hneJ).2
      refine hpres'.mono fun l hrJ =>
        ⟨(hvJ.2.2.2.2 hact0J).1.1.reach_lt_size hrJ, fun i hi bi hbi huB horI => ?_⟩
      obtain ⟨abi, habi, hmodeI, hneI, hactI, _, hnotOnceI, hvI, huTrI⟩ := hcapInfo i hi bi hbi
      have hcvI : (effVal abi).cls = .val := Classical.byContradiction fun hne =>
        ((hvI.2.2.2.2 hactI).2.2.2.1 hnotOnceI hne).ownTreeFull.2 l horI
      obtain ⟨htrI, hdeadI, _⟩ := huTrI (hmodeI ▸ huB) hcvI
      have hdisjD : ∀ d ∈ (effVal abi).deps, d ∉ (effVal abj).deps := fun d hdI hdJ =>
        (hactEndJ.1 d hdJ).2 (hdeadI d hdI)
      have hij : i ≠ j := by
        intro hEq; subst hEq; rw [habi] at habj; cases habj
        exact hdisjD abj.id List.mem_cons_self List.mem_cons_self
      exact (hsim.2.2.2.2.2.2 i j bi bj abi abj hij (hfvsScope i hi) hscJ hbi habi hbj habj hneI hneJ).1
        hactI htrI hact0J hdisjD l horI hrJ
    have hIsub : ∀ r, r < σ.nextRegion → ∀ c ∈ I.reg r, c ∈ I_end.reg r := fun r hr _ hc =>
      (hIendEq r hr).symm ▸ hc
    have hsim' := Sim_step (Nat.le_refl B) hleEnd hokEnd hIokEnd hrf' hos' hssf' hIsub hPresEnv hsim
    have hpSS' : PreservesLocs (StaticStrLoc st) st.heap st'.heap := by
      refine hpres'.mono fun l hss => ⟨StaticStrLoc_lt_size hst hss, fun i hi b hbi huB hor => ?_⟩
      exact (hfvsCond i hi b hbi).2.2.2.2 huB |>.2.2 l hor hss
    have henvNRF' := EnvNoReachForbid_step hsim.2.1 hleEnd (Sim_deps_lt hsim) hsim.2.2.2.1
      (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hPresEnv henvNRF
    -- `env'.length = env.length`
    have henvLen' : env'.length = env.length := by
      have hisSome : ∀ (j : Nat), env'[j]?.isSome = env[j]?.isSome := by
        intro j
        by_cases hj : j ∈ fvs.toList
        · obtain ⟨b, v', hbj, hbj', _⟩ := hcapProps j hj
          simp [hbj, hbj']
        · rw [henvOut j hj]
      apply Nat.le_antisymm
      · exact Classical.byContradiction fun hgt => by
          have hlt : env.length < env'.length := Nat.lt_of_not_ge hgt
          have h1 := hisSome env.length
          rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_none (Nat.le_refl _)] at h1
          cases h1
      · exact Classical.byContradiction fun hgt => by
          have hlt : env'.length < env.length := Nat.lt_of_not_ge hgt
          have h1 := hisSome env'.length
          rw [List.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem hlt] at h1
          cases h1
    -- `DeepOpenUnder st'.heap st'.regions (I_end.regsOf cloAv.regs) rv`
    have hdouClo : DeepOpenUnder st'.heap st'.regions (I_end.regsOf cloAv.regs) rv := by
      rw [hrg']
      refine hdouRv st.regions (I_end.regsOf cloAv.regs) fun i hi b hbi => ?_
      obtain ⟨ab, habi, _, _, hactAb, _, _, hvB, _⟩ := hcapInfo i hi b hbi
      obtain ⟨ab', habi', _, _, _, _, hregsSub, _, _⟩ := hcapMem i hi
      rw [habi] at habi'; cases habi'
      refine (hvB.2.2.2.2 hactAb).2.1.mono fun c hc => ?_
      obtain ⟨rg, hrg, hcRg⟩ := Interp.mem_regsOf.mp hc
      exact Interp.mem_regsOf.mpr ⟨rg, hregsSub rg hrg, (hIendEq rg (hvB.1 rg hrg)).symm ▸ hcRg⟩
    -- `cloFoot` properties
    have hcloFootProps : ∀ l, cloFoot l →
        Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l := by
      intro l ⟨_, i, hi, b, hbi, huB, hor⟩
      obtain ⟨ab, _, hmode, _, hactAb, _, hnotOnce, hvB, huTr⟩ := hcapInfo i hi b hbi
      have hcv : (effVal ab).cls = .val := Classical.byContradiction fun hne =>
        ((hvB.2.2.2.2 hactAb).2.2.2.1 hnotOnce hne).ownTreeFull.2 l hor
      obtain ⟨htrAb, _, _⟩ := huTr (hmode ▸ huB) hcv
      obtain ⟨hnotF, hnotSS⟩ := ((hvB.2.2.2.2 hactAb).2.2.2.2.2.2.2 htrAb).2 l hor
      obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
      obtain ⟨b', v', hbi', hbi'New, hvsh, _, _, _, _⟩ := hcapProps i hi
      rw [hbi] at hbi'; cases hbi'
      have hrSt' : Reach st'.heap v' l :=
        Reach_of_sameShapeOn (fun x o _ ho => hoss'.2 x o ho) (SameLoc.of_valSameShape hvsh) (OwnReach_toReach hor)
      have hvMem : v' ∈ (Cell.clo env' p res rc fvs body).vals := by
        simp only [Cell.vals, List.mem_filterMap]
        exact ⟨i, hi, by simp [hbi'New]⟩
      have hrRv : Reach st'.heap rv l := by
        rw [hrvEq]; exact .step hoNew hvMem hrSt'
      have hnotSS' : ¬ StaticStrLoc st' l := fun hss' =>
        hnotSS (StaticStrLoc_unchanged_of_preserves hst hstat' hstr' hpSS' hss').1
      have hnotNum' : ¬ NumLoc st'.heap l := by
        rintro ⟨o', n', ho', hnum'⟩
        have hr0 : Reach st.heap b.val l := OwnReach_toReach hor
        obtain ⟨o0, ho0⟩ := (hvB.2.2.2.2 hactAb).1.1.exists_obj hr0
        obtain ⟨o'₂, ho'₂, hcs⟩ := hoss'.2 l o0 ho0
        rw [ho'] at ho'₂; cases ho'₂
        have hisNum := hcs.isNum_eq
        rw [hnum'] at hisNum
        obtain ⟨o0', ho0', hnotN⟩ := OwnReach_nonNum hor
        rw [ho0] at ho0'; cases ho0'
        rcases hnotN with h1 | h2
        · rw [h1] at hisNum; cases hisNum
        · exact h2 rfl
      exact ⟨hrRv, hnotF, hnotSS', hnotNum'⟩
    -- `VSim` parameterized on `FunOkAt`
    have hvsimClo : FunOkAt P ext B st' cloAv.skel consumed cloFoot rv →
        VSim P ext B st' Frame NoKill NoSpend σ_end I_end cloFoot cloAv rv := by
      intro hfun
      refine ⟨fun rg hrg => ?_, fun d hd => ?_, (fun _ h => by cases h),
        (fun _ ⟨_, h, _⟩ => by cases h), fun _ => ?_⟩
      · rcases hregsProv rg hrg with h0 | ⟨i, hi, ab, habi, hrgAb⟩
        · cases h0
        · have hiLt : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp habi).1
          obtain ⟨ab', habi', _, _, _, _, _, hvB, _⟩ := hcapInfo i hi env[i] (List.getElem?_eq_getElem hiLt)
          rw [habi] at habi'; cases habi'
          exact Nat.lt_of_lt_of_le (hnr₁ ▸ hvB.1 rg hrgAb) hnextLe
      · rcases hdepsProv d hd with h0 | ⟨i, hi, ab, habi, _, hdAb⟩
        · cases h0
        · have hiLt : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp habi).1
          obtain ⟨ab', habi', _, _, _, _, _, hvB, _⟩ := hcapInfo i hi env[i] (List.getElem?_eq_getElem hiLt)
          rw [habi] at habi'; cases habi'
          exact hszSt₁.symm ▸ hvB.2.1 d hdAb
      · refine ⟨hbaseRv, hdouClo, hcfRv, fun _ hne => absurd rfl hne, ?_, ?_,
          (fun ⟨_, h, _⟩ => by cases h), (fun htr => by cases htr.2.1)⟩
        · intro ⟨_, hconsF⟩
          change consumed = false at hconsF
          have hnoFoot : ∀ l, ¬ cloFoot l := fun l ⟨hc, _⟩ => by rw [hconsF] at hc; cases hc
          have hfun' : FunOkAt P ext B st' cloAv.skel false (fun _ => False) rv := by
            rw [hconsF] at hfun
            exact FunOkAt_weaken_foot (fun l h => False.elim (hnoFoot l h)) hfun
          exact ⟨hnoRv, hnoFoot, hfun'⟩
        · intro hconsT
          change consumed = true at hconsT
          obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
          refine ⟨fun l hl => let h := hcloFootProps l hl; ⟨h.1, h.2.2.1, h.2.2.2⟩,
            fun _ l hl => (hcloFootProps l hl).2.1,
            (fun loc' cap' t' o' r' fs' hEq ho' hc' _ _ => by
              rw [hrvEq] at hEq; cases hEq; rw [hoNew] at ho'; cases ho'; cases hc'),
            by rw [hconsT] at hfun; exact hfun⟩
    -- `ValEnvDisj`
    have hdisjClo : ValEnvDisj P st' NoKill Scope env aenv σ_end envFoot cloFoot cloAv rv := by
      intro j bj abj hscJ hbj habj hneJ
      refine ⟨(fun _ htr => by cases htr.2.1), ?_, ?_, ?_, (fun _ _ h => by cases h),
        (fun h => by cases h), (fun _ h => by cases h)⟩
      · -- `Transferable abj` vs `Reach rv`
        intro hactEndJ htrEndJ _ hdepsDisj l horJ' hrRv
        have hact0J : ActiveVal σ (effVal abj) :=
          ActiveVal.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
            (Sim_src_lt hsim j abj habj) hactEndJ
        have htr0J : Transferable σ NoKill (effVal abj) :=
          Transferable.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
            (Sim_src_lt hsim j abj habj) (fun _ h => h) htrEndJ
        have hpJ : PreservesLocs (Reach st.heap bj.val) st.heap st'.heap :=
          hPresEnv j bj abj hscJ hbj habj hneJ hactEndJ
        have horJ0 : OwnReach P st.heap bj.val l := (OwnReach_congr hpJ l).mp horJ'
        have hrJ0 : Reach st.heap bj.val l := OwnReach_toReach horJ0
        have hlLt : l < st.heap.objs.size :=
          (((hsim.2.2.2.2.2.1 j bj abj hscJ hbj habj).2 hneJ).2.2.2.2.2 hact0J).1.1.reach_lt_size hrJ0
        rcases hreachRv l hrRv with hEq | ⟨i, hi, bi, hbi, hrI⟩
        · exact Nat.ne_of_lt hlLt hEq
        · obtain ⟨abi, habi, hmodeI, hneI, hactI, _, hnotOnceI, hvI, huTrI⟩ := hcapInfo i hi bi hbi
          by_cases hcvI : (effVal abi).cls = .val
          · have hlvJ : ∀ d ∈ (effVal abj).deps, σ₁.st[d]? = some .live := fun d hd =>
              (htrEndJ.2.2.2.2 d hd).1
            have hdepsJI : ∀ d ∈ (effVal abj).deps, d ∉ (effVal abi).deps := by
              intro d hdJ hdI
              cases huI : abi.mode.isUnique with
              | true =>
                obtain ⟨_, hdeadI, _⟩ := huTrI huI hcvI
                have h1 := hlvJ d hdJ; rw [hdeadI d hdI] at h1; cases h1
              | false =>
                obtain ⟨abi', habi', _, _, _, _, _, _, hshI⟩ := hcapMem i hi
                rw [habi] at habi'; cases habi'
                exact hdepsDisj d hdJ ((hshI huI).1 d hdI)
            have hij : j ≠ i := by
              intro hEq; subst hEq; rw [habi] at habj; cases habj
              exact hdepsJI abj.id List.mem_cons_self List.mem_cons_self
            exact (hsim.2.2.2.2.2.2 j i bj bi abj abi hij hscJ (hfvsScope i hi) hbj habj hbi habi hneJ hneI).1
              hact0J htr0J hactI hdepsJI l horJ0 hrI
          · exact OwnReach_not_numLoc horJ0 (((hvI.2.2.2.2 hactI).2.2.2.1 hnotOnceI hcvI).reach_numLoc hrI)
      · -- `cloFoot` vs `Reach bj`
        intro _ _ hactEndJ _ l ⟨_, i, hi, bi, hbi, huB, horI⟩ hrJ'
        have hact0J : ActiveVal σ (effVal abj) :=
          ActiveVal.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
            (Sim_src_lt hsim j abj habj) hactEndJ
        have hpJ : PreservesLocs (Reach st.heap bj.val) st.heap st'.heap :=
          hPresEnv j bj abj hscJ hbj habj hneJ hactEndJ
        have hrJ0 : Reach st.heap bj.val l := (Reach_congr hpJ l).mp hrJ'
        obtain ⟨abi, habi, hmodeI, hneI, hactI, _, hnotOnceI, hvI, huTrI⟩ := hcapInfo i hi bi hbi
        have hcvI : (effVal abi).cls = .val := Classical.byContradiction fun hne =>
          ((hvI.2.2.2.2 hactI).2.2.2.1 hnotOnceI hne).ownTreeFull.2 l horI
        obtain ⟨htrI, hdeadI, _⟩ := huTrI (hmodeI ▸ huB) hcvI
        have hdisjD : ∀ d ∈ (effVal abi).deps, d ∉ (effVal abj).deps := fun d hdI hdJ =>
          (hactEndJ.1 d hdJ).2 (hdeadI d hdI)
        have hij : i ≠ j := by
          intro hEq; subst hEq; rw [habi] at habj; cases habj
          exact hdisjD abj.id List.mem_cons_self List.mem_cons_self
        exact (hsim.2.2.2.2.2.2 i j bi bj abi abj hij (hfvsScope i hi) hscJ hbi habi hbj habj hneI hneJ).1
          hactI htrI hact0J hdisjD l horI hrJ0
      · -- `envFoot j` vs `Reach rv`
        intro hactEndJ hftEndJ _ _ l hfj hrRv
        have hact0J : ActiveVal σ (effVal abj) :=
          ActiveVal.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
            (Sim_src_lt hsim j abj habj) hactEndJ
        have hft0J : FootActive σ (effVal abj) :=
          FootActive.of_AStateLe hsim.2.1 hleEnd (Sim_deps_lt hsim j abj hscJ habj hneJ)
            (Sim_src_lt hsim j abj habj) hftEndJ
        have hvJ := ((hsim.2.2.2.2.2.1 j bj abj hscJ hbj habj).2 hneJ).2
        have hrJ0 : Reach st.heap bj.val l := by
          rcases hft0J with hoo | ⟨his, _⟩
          · exact ((hvJ.2.2.2.2 hact0J).2.2.2.2.2.1 hoo).1 l hfj |>.1
          · exact ((hvJ.2.2.2.2 hact0J).2.2.2.2.2.2.1 his).1 l hfj |>.1
        have hlLt : l < st.heap.objs.size := (hvJ.2.2.2.2 hact0J).1.1.reach_lt_size hrJ0
        rcases hreachRv l hrRv with hEq | ⟨i, hi, bi, hbi, hrI⟩
        · exact Nat.ne_of_lt hlLt hEq
        · obtain ⟨abi, habi, _, hneI, hactI, hooI, hnotOnceI, _, _⟩ := hcapInfo i hi bi hbi
          have hij : j ≠ i := by
            intro hEq; subst hEq; rw [habi] at habj; cases habj
            rcases hft0J with hoo | ⟨his, _⟩
            · rw [hooI] at hoo; cases hoo
            · exact hnotOnceI his
          exact (hsim.2.2.2.2.2.2 j i bj bi abj abi hij hscJ (hfvsScope i hi) hbj habj hbi habi hneJ hneI).2
            hact0J hft0J hactI l hfj hrI
    -- `NoReachForbid`
    have hnrfClo : ActiveVal σ_end cloAv → NoReachForbid st' Forbid BadReg BadDep cloAv rv := by
      intro _ hbadR hbadD l hrRv hnotSS' hnotNum' hF
      have hlLt : l < st.heap.objs.size := hForbidLt l hF
      rcases hreachRv l hrRv with hEq | ⟨i, hi, bi, hbi, hrI⟩
      · exact Nat.ne_of_lt hlLt hEq
      · obtain ⟨abi, habi, _, hneI, hactI, _, hnotOnceI, hvI, huTrI⟩ := hcapInfo i hi bi hbi
        obtain ⟨abi', habi', _, _, _, _, hregsSub, _, hshI⟩ := hcapMem i hi
        rw [habi] at habi'; cases habi'
        have hbadRI : ∀ rg ∈ (effVal abi).regs, ¬ BadReg rg := fun rg hrg => hbadR rg (hregsSub rg hrg)
        have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
          hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpSS' hss0)
        have hnotNum0 : ¬ NumLoc st.heap l := by
          rintro ⟨o0, n0, ho0, hnum0⟩
          obtain ⟨o', ho', hcs⟩ := hoss'.2 l o0 ho0
          have hc' : o'.cell = .num n0 := by
            rw [hnum0] at hcs
            cases hco' : o'.cell <;> rw [hco'] at hcs <;> try cases hcs
            rfl
          exact hnotNum' ⟨o', n0, ho', hc'⟩
        by_cases hcvI : (effVal abi).cls = .val
        · have hbadDI : ∀ d ∈ (effVal abi).deps, ¬ BadDep d := by
            intro d hd
            cases huI : abi.mode.isUnique with
            | true =>
              obtain ⟨_, hdeadI, _⟩ := huTrI huI hcvI
              intro hbd
              have h1 := hBadDep d hbd; rw [hdeadI d hd] at h1; cases h1
            | false =>
              exact hbadD d ((hshI huI).1 d hd)
          exact henvNRF i bi abi (hfvsScope i hi) hbi habi hneI hactI hbadRI hbadDI l hrI hnotSS0 hnotNum0 hF
        · exact hnotNum0 (((hvI.2.2.2.2 hactI).2.2.2.1 hnotOnceI hcvI).reach_numLoc hrI)
    exact ⟨rv, env', taint, st', hrun, hrg', hnrSt', hstat', hstr', hsz', hcap',
      hoss', hPresFrame, hos', hssf', hst', hsim', henvNRF', hrvObj, henvLen', hcapProps,
      hbaseRv, hnoRv, hcfRv, hdouClo, hreachRv, hcloFootProps, hvsimClo, hdisjClo, hnrfClo⟩

/-- **Bridge 9b (`clo_call_sim_of_captures`)**: at closure call time inside `FunOkAt`, lifts
the creation-time `ACaps` + `formClosure` witnesses across `SameLoc`/`SameShapeOn`/`RegsFuture`
and opens the call region `(s_a, s_c)`, building `Sim` on `(env_call, aenv, σ_open, I_open)`
with `Scope := (· ∈ fvs.toList)` and `NoKill := if consumed then fun _ => False else (· ∈ owned)`,
ready for single-parameter `bindAt` + `evalS_sound` IH + `retCheck_bridge`. -/
theorem clo_call_sim_of_captures {P : Prog} {ext : ExternOracle} {B B_call : Nat}
    {st st' st_call : St}
    {Frame NoKill NoSpend Scope Frame_call : Nat → Prop}
    {env env' : List Bnd} {aenv : List ABnd} {σ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {deps regs owned : List Nat} {consumed : Bool}
    {rv f_call : Val} {cap : Nat} {taint fRegs aRegs : List Nat}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hNoKill : NoKillOk NoKill σ₁)
    (hfvsScope : ∀ i ∈ fvs.toList, Scope i)
    (hcaps : ACaps aenv fvs.toList σ [] [] [] deps regs owned σ₁)
    (hrvEq : rv = .ref st.heap.objs.size cap taint)
    (hoNew : st'.heap.objs[st.heap.objs.size]? = some ⟨.clo env' p res rc fvs body, cap⟩)
    (hrg' : st'.regions = st.regions)
    (hoss' : OldSameShape st.heap st'.heap)
    (henvLen' : env'.length = env.length)
    (hcapProps : ∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
      ValSameShape b.val v' ∧ ValBaseOk st' v' ∧ NoOnceCell st'.heap v' ∧
      CtorFieldsOk P ext B st' v' ∧
      (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot b.val →
        FunOkAt P ext B st' sk onceOnly Foot v'))
    (hB : B_call ≤ B)
    (hst_call : StOk P ext B_call st_call)
    (hstat_call : ∀ l, StaticStrLoc st_call l → Frame_call l)
    (hloc : SameLoc rv f_call)
    (hsh : SameShapeOn (Reach st'.heap rv) st'.heap st_call.heap)
    (hrf : RegsFuture st' st_call)
    (hfBase : ValBaseOk st_call f_call)
    (hfOpen : DeepOpenUnder st_call.heap st_call.regions fRegs f_call)
    (hfCf : CtorFieldsOk P ext B_call st_call f_call)
    (hFclo : ∀ l, Frame_call l → ¬ (consumed = true ∧ ∃ i ∈ fvs.toList, ∃ b,
      env[i]? = some b ∧ b.mode.isUnique = true ∧ OwnReach P st.heap b.val l)) :
    let σ_call := restoreOwned owned σ₁
    let s_a := σ_call.openReg.1
    let σ_open := σ_call.openReg.2
    let s_c := st_call.nextRegion
    let st_open : St := { st_call with nextRegion := s_c + 1, regions := s_c :: st_call.regions }
    let NoKill_call : Nat → Prop := if consumed then fun _ => False else (· ∈ owned)
    let I_base : Interp := ⟨fun r =>
      if r == 1 then (aRegs ++ fRegs).filter (· < s_c) else fRegs.filter (· < s_c)⟩
    let I_open : Interp := I_base.extend s_a s_c
    ∃ cap_c taint_c o_c env_call,
      f_call = .ref st.heap.objs.size cap_c taint_c ∧
      st_call.heap.objs[st.heap.objs.size]? = some o_c ∧
      o_c.cap = cap_c ∧
      o_c.cell = .clo env_call p res rc fvs body ∧
      AStateOk σ_call ∧ AStateOk σ_open ∧ StOk P ext B_call st_open ∧
      RegUnique I_open σ_open s_a s_c ∧
      NoKillOk NoKill_call σ_open ∧ NoSpendOk (fun _ => False) σ_open ∧
      Sim P ext B_call st_open Frame_call NoKill_call (fun _ => False) (· ∈ fvs.toList)
        env_call aenv σ_open I_open (fun _ _ => False) ∧
      (∀ (Forbid BadReg BadDep : Nat → Prop),
        (∀ l, Reach st_call.heap f_call l → ¬ Forbid l) →
        EnvNoReachForbid st_open (· ∈ fvs.toList) env_call aenv σ_open Forbid BadReg BadDep) ∧
      (∀ r, r < σ_open.nextRegion → r ≠ s_a → ∀ c ∈ I_open.reg r, c ∈ aRegs ++ fRegs ∧ c < s_c) ∧
      (∀ c, c ∈ aRegs → c < s_c → c ∈ I_open.reg 1) ∧
      (∀ i ∈ fvs.toList, ∀ b_c, env_call[i]? = some b_c →
        ∀ l, Reach st_call.heap b_c.val l → Reach st_call.heap f_call l) := by
  intro σ_call s_a σ_open s_c st_open NoKill_call I_base I_open
  obtain ⟨hok₁, _, hszSt₁, honce₁, hszSp₁, hreg₁, hnr₁, _, _, hcapMem,
    _, _, hownedIff, _, hpairCaps⟩ := ACaps_info hsim.2.1 hcaps
  obtain ⟨hszCall, honceCall, hspCall, hregCall, hnrCall, hgetCall, hokCallFn⟩ := restoreOwned_spec owned σ₁
  have hokCall : AStateOk σ_call := hokCallFn hok₁
  have hokOpen : AStateOk σ_open := (AStateOk.openReg hokCall).1
  have hstOpen : StOk P ext B_call st_open := StOk_openRegion hst_call
  -- Unpack `f_call` and its `.clo env_call` cell via `SameLoc` + `SameShapeOn`
  cases f_call with
  | imm _ => rw [hrvEq] at hloc; cases hloc
  | ref loc_c cap_c taint_c =>
    rw [hrvEq] at hloc; simp only [SameLoc] at hloc; subst loc_c
    have hrHere : Reach st'.heap rv st.heap.objs.size := by rw [hrvEq]; exact .here
    obtain ⟨o_c, ho_c, hcsClo⟩ := hsh st.heap.objs.size ⟨.clo env' p res rc fvs body, cap⟩ hrHere hoNew
    obtain ⟨o_c', ho_c', hcap_c⟩ := hfBase.1.self.1
    rw [ho_c] at ho_c'; cases ho_c'
    cases hcell_c : o_c.cell with
    | ctor _ _ | num _ | str _ | pap _ _ | once _ _ =>
      rw [hcell_c] at hcsClo; cases hcsClo
    | clo env_call p2 res2 rc2 fvs2 body2 =>
      rw [hcell_c] at hcsClo
      obtain ⟨rfl, rfl, rfl, rfl, rfl, henvCallLen, hcloEnv⟩ := hcsClo
      -- `InterpOk` and `RegUnique` for `I_open` on `(σ_open, st_open)`
      have hIokOpen : InterpOk σ_open st_open I_open := by
        refine ⟨fun r hr c hc => ?_, fun c hc => ?_⟩
        · dsimp only [I_open, Interp.extend] at hc
          by_cases hEq : r = s_a
          · subst hEq; simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton] at hc
            subst hc; exact Nat.lt_succ_self s_c
          · rw [beq_false_of_ne hEq] at hc
            simp only [Bool.false_eq_true, ↓reduceIte, I_base] at hc
            by_cases h1 : (r == 1) = true
            · simp only [h1, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
              exact Nat.lt_succ_of_lt hc.2
            · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
              exact Nat.lt_succ_of_lt hc.2
        · dsimp only [st_open] at hc; cases hc
          dsimp only [I_open, Interp.extend, σ_open, AState.openReg, s_a]
          simp only [List.headD_cons, beq_self_eq_true, ↓reduceIte, List.mem_singleton]
      have hregU : RegUnique I_open σ_open s_a s_c := by
        refine ⟨by simp [I_open, Interp.extend], fun r hr hne hc => ?_⟩
        dsimp only [I_open, Interp.extend] at hc
        rw [beq_false_of_ne hne] at hc
        simp only [Bool.false_eq_true, ↓reduceIte, I_base] at hc
        by_cases h1 : (r == 1) = true
        · simp only [h1, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
          exact Nat.lt_irrefl _ hc.2
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
          exact Nat.lt_irrefl _ hc.2
      have hNoKillOpen : NoKillOk NoKill_call σ_open := by
        intro d hnk hdead
        cases consumed with
        | true => simp [NoKill_call] at hnk
        | false =>
          simp only [NoKill_call, Bool.false_eq_true, ↓reduceIte] at hnk
          have hmem : d ∈ owned := hnk
          rcases (hownedIff d).mp hmem with h0 | ⟨i, _, ab, habi, _, rfl⟩
          · cases h0
          · have hlt : ab.id < σ₁.st.size := hszSt₁.symm ▸ hsim.2.2.2.1 i ab habi
            have hget : σ_open.st[ab.id]? = some .live := by
              change σ_call.st[ab.id]? = some .live
              rw [hgetCall ab.id hlt]; simp only [hmem, ↓reduceIte]
            rw [hget] at hdead; cases hdead
      -- Helper: reach from any capture in `env_call` to `f_call`
      have hreachCapCall : ∀ i ∈ fvs.toList, ∀ b_c, env_call[i]? = some b_c →
          HeldBy st_call.heap (.ref st.heap.objs.size cap_c taint_c) b_c.val ∧
          ∀ l, Reach st_call.heap b_c.val l → Reach st_call.heap (.ref st.heap.objs.size cap_c taint_c) l := by
        intro i hi b_c hbc
        have hvMem : b_c.val ∈ o_c.cell.vals := by
          rw [hcell_c]; simp only [Cell.vals, List.mem_filterMap]
          exact ⟨i, hi, by simp [hbc]⟩
        exact ⟨Or.inr ⟨st.heap.objs.size, o_c, .here, ho_c, hvMem⟩,
          fun l hr => .step ho_c hvMem hr⟩
      -- Helper: relate `env[i]?`, `env'[i]?`, `env_call[i]?`, `aenv[i]?` for `i ∈ fvs.toList`
      have hcapRel : ∀ i ∈ fvs.toList, ∀ b_c ab, env_call[i]? = some b_c → aenv[i]? = some ab →
          ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
            b_c.mode = b.mode ∧ b.mode = ab.mode ∧ ab.mode ≠ .erased ∧
            ValSameShape b.val v' ∧ ValSameShape v' b_c.val ∧
            ActiveVal σ (effVal ab) ∧ (effVal ab).onceOnly = false ∧ ¬ IsOnceSrc σ (effVal ab) ∧
            VSim P ext B st Frame NoKill NoSpend σ I (envFoot i) (effVal ab) b.val ∧
            ValBaseOk st' v' ∧ NoOnceCell st'.heap v' ∧
            (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot b.val →
              FunOkAt P ext B st' sk onceOnly Foot v') ∧
            SameShapeOn (Reach st'.heap v') st'.heap st_call.heap := by
        intro i hi b_c ab hbc habi
        obtain ⟨b, v', hbi, hbi', hvsh1, hbv', hno', _, hfun'⟩ := hcapProps i hi
        have hrel := hcloEnv i
        rw [hbi', hbc] at hrel
        obtain ⟨hmodeC, hvsh2⟩ := hrel
        obtain ⟨ab', habi', hneAb, hvdAb, hooAb, hnotOnce, _, _, _⟩ := hcapMem i hi
        rw [habi] at habi'; cases habi'
        obtain ⟨hmode0, hneBody⟩ := hsim.2.2.2.2.2.1 i b ab (hfvsScope i hi) hbi habi
        have hact0 : ActiveVal σ (effVal ab) := ⟨hvdAb, fun his => absurd his hnotOnce⟩
        have hv'Mem : v' ∈ (Cell.clo env' p res rc fvs body).vals := by
          simp only [Cell.vals, List.mem_filterMap]
          exact ⟨i, hi, by simp [hbi']⟩
        have hshV' : SameShapeOn (Reach st'.heap v') st'.heap st_call.heap :=
          hsh.mono fun x hx => by rw [hrvEq]; exact .step hoNew hv'Mem hx
        exact ⟨b, v', hbi, hbi', hmodeC.symm, hmode0, hneAb, hvsh1, hvsh2, hact0, hooAb, hnotOnce,
          (hneBody hneAb).2, hbv', hno', hfun', hshV'⟩
      -- Helper: `Transferable` in `σ_open` only holds for unique `.val` captures when `consumed = true`
      have htrOnlyUniq : ∀ i ∈ fvs.toList, ∀ ab, aenv[i]? = some ab →
          Transferable σ_open NoKill_call (effVal ab) →
          ab.mode.isUnique = true ∧ (effVal ab).cls = .val ∧ consumed = true := by
        intro i hi ab habi htr
        have hcv : (effVal ab).cls = .val := htr.1
        obtain ⟨ab', habi', _, _, _, _, _, huAb, hshAb⟩ := hcapMem i hi
        rw [habi] at habi'; cases habi'
        cases hu : ab.mode.isUnique with
        | false =>
          have hnotOwn : ab.id ∉ owned := by
            intro hmem
            rcases (hownedIff ab.id).mp hmem with h0 | ⟨j, _, ab2, hab2, hu2, hEq⟩
            · cases h0
            · have hij := hsim.2.2.2.2.1 i j ab ab2 habi hab2 hEq
              subst hij; rw [habi] at hab2; cases hab2
              rw [hu] at hu2; cases hu2
          have hlvOpen : σ_open.st[ab.id]? = some .live := (htr.2.2.2.2 ab.id List.mem_cons_self).1
          have hlt1 : ab.id < σ₁.st.size := hszSt₁.symm ▸ hsim.2.2.2.1 i ab habi
          have hget : σ_open.st[ab.id]? = σ₁.st[ab.id]? := by
            change σ_call.st[ab.id]? = σ₁.st[ab.id]?
            rw [hgetCall ab.id hlt1]; simp only [hnotOwn, ↓reduceIte]
          rw [hget] at hlvOpen
          exact False.elim ((hshAb hu).2 hcv ab.id List.mem_cons_self hlvOpen)
        | true =>
          have hownMem : ab.id ∈ owned := (huAb hu).1
          cases hc : consumed with
          | true => exact ⟨rfl, hcv, rfl⟩
          | false =>
            have hnk : ¬ NoKill_call ab.id := (htr.2.2.2.2 ab.id List.mem_cons_self).2
            simp only [NoKill_call, hc, Bool.false_eq_true, ↓reduceIte] at hnk
            exact False.elim (hnk hownMem)
      -- Build `Sim` on `(env_call, aenv, σ_open, I_open)`
      have hsimCall : Sim P ext B_call st_open Frame_call NoKill_call (fun _ => False) (· ∈ fvs.toList)
          env_call aenv σ_open I_open (fun _ _ => False) := by
        refine ⟨by rw [← henvCallLen, henvLen', hsim.1], hokOpen, hIokOpen,
          fun i ab habi => by
            change ab.id < σ_call.st.size
            rw [hszCall, hszSt₁]; exact hsim.2.2.2.1 i ab habi,
          hsim.2.2.2.2.1, ?_, ?_⟩
        · intro i b_c ab hi hbc habi
          obtain ⟨b, v', hbi, _, hmodeC, hmode0, hneAb, hvsh1, hvsh2, hact0, hooAb, hnotOnce0,
            hvB, hbv', hno', hfun', hshV'⟩ := hcapRel i hi b_c ab hbc habi
          have honceEq : σ_open.once = σ.once := by
            change σ_call.once = σ.once; rw [honceCall, honce₁]
          have hnotOnceOpen : ¬ IsOnceSrc σ_open (effVal ab) := fun ⟨id, hs, ho⟩ =>
            hnotOnce0 ⟨id, hs, honceEq ▸ ho⟩
          refine ⟨hmodeC.trans hmode0, fun _ => ⟨by
            rw [honceEq]; exact ((hsim.2.2.2.2.2.1 i b ab (hfvsScope i hi) hbi habi).2 hneAb).1, ?_⟩⟩
          -- `VSim` for capture `i`
          refine ⟨fun rg hrg => by
              change rg < σ_call.nextRegion + 1
              rw [hnrCall, hnr₁]; exact Nat.lt_succ_of_lt (hvB.1 rg hrg),
            fun d hd => by
              change d < σ_call.st.size
              rw [hszCall, hszSt₁]; exact hvB.2.1 d hd,
            fun x hx => by
              obtain ⟨hx1, hx2⟩ := hvB.2.2.1 x hx
              exact ⟨by change x < σ_call.st.size; rw [hszCall, hszSt₁]; exact hx1, hx2⟩,
            fun _ his => absurd his hnotOnceOpen, fun _ => ?_⟩
          have hhb : HeldBy st_call.heap (.ref st.heap.objs.size cap_c taint_c) b_c.val :=
            (hreachCapCall i hi b_c hbc).1
          have hbaseC : ValBaseOk st_call b_c.val := ValBaseOk.sub hfBase hhb
          have hbaseOpen : ValBaseOk st_open b_c.val :=
            ValBaseOk_congr (st := st_call) (st' := st_open) (PreservesLocs.refl _ _) (Nat.le_succ _) hbaseC
          have hcfOpen : CtorFieldsOk P ext B_call st_open b_c.val :=
            CtorFieldsOk_congr hbaseC.1 (PreservesLocs.refl _ _) (RegsFuture.openRegion st_call)
              (CtorFieldsOk.sub hfCf hhb)
          have hdouOpen : DeepOpenUnder st_open.heap st_open.regions (I_open.regsOf (effVal ab).regs) b_c.val := by
            cases hregs : (effVal ab).regs with
            | nil =>
              have hdou0 : DeepOpenUnder st.heap st.regions [] b.val := by
                have := (hvB.2.2.2.2 hact0).2.1; rw [hregs, Interp.regsOf_nil] at this; exact this
              have hdou' : DeepOpenUnder st'.heap st'.regions [] v' := by
                rw [hrg']
                exact DeepOpenUnder_of_sameShapeOn (hvB.2.2.2.2 hact0).1.1
                  (fun l o _ ho => hoss'.2 l o ho) hvsh1 hdou0
              have hdouC0 : DeepOpenUnder st_call.heap st'.regions [] b_c.val :=
                DeepOpenUnder_of_sameShapeOn hbv'.1 hshV' hvsh2 hdou'
              have htbC' : DeepTaintsBounded st_call.heap st'.nextRegion b_c.val := by
                intro w₂ hw₂ r hr
                rcases hw₂ with rfl | ⟨l, o₂, hr₂, ho₂, hm₂⟩
                · rw [← hvsh2.taint_eq] at hr
                  exact hbv'.2.2.2 v' (HeldBy.refl _ _) r hr
                · have hr₁ := Reach_of_sameShapeOn_rev hbv'.1 hshV' (SameLoc.of_valSameShape hvsh2) hr₂
                  obtain ⟨o₁, ho₁⟩ := hbv'.1.exists_obj hr₁
                  obtain ⟨o₂', ho₂', hcs⟩ := hshV' l o₁ hr₁ ho₁
                  rw [ho₂] at ho₂'; cases ho₂'
                  obtain ⟨w₁, hm₁, hvsW⟩ := hcs.symm.vals_fwd hm₂
                  rw [hvsW.taint_eq] at hr
                  exact hbv'.2.2.2 w₁ (Or.inr ⟨l, o₁, hr₁, ho₁, hm₁⟩) r hr
              have hdouC : DeepOpenUnder st_call.heap st_call.regions [] b_c.val :=
                DeepOpenUnder_of_regsFuture htbC' hdouC0 hrf
              exact DeepOpenUnder_of_regsFuture hbaseC.2.2.2 hdouC (RegsFuture.openRegion st_call)
            | cons rg0 rgs =>
              have hrg0Lt : rg0 < s_a := by
                change rg0 < σ_call.nextRegion
                rw [hnrCall, hnr₁]; exact hvB.1 rg0 (hregs ▸ List.mem_cons_self)
              have hrg0Ne : rg0 ≠ s_a := Nat.ne_of_lt hrg0Lt
              have hdouC : DeepOpenUnder st_call.heap st_call.regions fRegs b_c.val :=
                hfOpen.sub hhb
              intro w hw r hr hopen
              have hrLt : r < s_c := hbaseC.2.2.2 w hw r hr
              have hopenC : r ∈ st_call.regions := by
                rcases List.mem_cons.mp hopen with rfl | hm
                · exact absurd hrLt (Nat.lt_irrefl _)
                · exact hm
              have hrF : r ∈ fRegs := hdouC w hw r hr hopenC
              refine Interp.mem_regsOf.mpr ⟨rg0, List.mem_cons_self, ?_⟩
              dsimp only [I_open, Interp.extend]
              rw [beq_false_of_ne hrg0Ne]
              simp only [Bool.false_eq_true, ↓reduceIte, I_base]
              by_cases h1 : (rg0 == 1) = true
              · simp only [h1, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
                exact ⟨List.mem_append_right _ hrF, hrLt⟩
              · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
                exact ⟨hrF, hrLt⟩
          have hnoOpen : NoOnceCell st_open.heap b_c.val :=
            NoOnceCell_of_sameShape hbv'.1 hshV' (SameLoc.of_valSameShape hvsh2) hno'
          have hfunOpen : FunOkAt P ext B_call st_open (effVal ab).skel false (fun _ => False) b_c.val := by
            have hfun0 := ((hvB.2.2.2.2 hact0).2.2.2.2.1 ⟨hnotOnce0, hooAb⟩).2.2
            have hfunB' := FunOkAt_mono hB (hfun' (effVal ab).skel false (fun _ => False) hfun0)
            exact FunOkAt_preserve_sameShape (SameLoc.of_valSameShape hvsh2) hshV'
              (hrf.trans (RegsFuture.openRegion st_call)) hfunB'
          refine ⟨hbaseOpen, hdouOpen, hcfOpen, ?_, fun _ => ⟨hnoOpen, fun _ h => h, hfunOpen⟩,
            (fun hoo => by rw [hooAb] at hoo; cases hoo),
            fun his => absurd his hnotOnceOpen, ?_⟩
          · intro _ hneCls
            have hnv0 := (hvB.2.2.2.2 hact0).2.2.2.1 hnotOnce0 hneCls
            have hnv' := NonValSafe.of_sameShape (fun l o _ ho => hoss'.2 l o ho) hvsh1 hbv'.1.self.1 hnv0
            exact NonValSafe.of_sameShape hshV' hvsh2 hbaseC.1.self.1 hnv'
          · intro htrOpen
            obtain ⟨huAb, hcvAb, hconsT⟩ := htrOnlyUniq i hi ab habi htrOpen
            obtain ⟨ab', habi', _, _, _, _, _, huInfo, _⟩ := hcapMem i hi
            rw [habi] at habi'; cases habi'
            obtain ⟨hown0, hlvDead0, _⟩ := (huInfo huAb).2 hcvAb
            have htr0 : Transferable σ NoKill (effVal ab) :=
              ⟨hcvAb, hown0, hooAb, hnotOnce0,
               fun d hd => ⟨(hlvDead0 d hd).1, fun hnk => hNoKill d hnk (hlvDead0 d hd).2⟩⟩
            have hot0 : OwnTreeFull P st.heap b.val := ((hvB.2.2.2.2 hact0).2.2.2.2.2.2.2 htr0).1
            have hot' : OwnTreeFull P st'.heap v' :=
              OwnTreeFull_of_sameShapeOn (hvB.2.2.2.2 hact0).1.1
                (fun l o _ ho => hoss'.2 l o ho) (SameLoc.of_valSameShape hvsh1) hot0
            have hotC : OwnTreeFull P st_open.heap b_c.val :=
              OwnTreeFull_of_sameShapeOn hbv'.1 hshV' (SameLoc.of_valSameShape hvsh2) hot'
            refine ⟨hotC, fun l horC => ?_⟩
            have hor' : OwnReach P st'.heap v' l :=
              OwnReach_of_sameShapeOn_rev hbv'.1 hshV' (SameLoc.of_valSameShape hvsh2) horC
            have hor0 : OwnReach P st.heap b.val l :=
              OwnReach_of_sameShapeOn_rev (hvB.2.2.2.2 hact0).1.1
                (fun x o _ ho => hoss'.2 x o ho) (SameLoc.of_valSameShape hvsh1) hor'
            have hcfL : consumed = true ∧ ∃ idx ∈ fvs.toList, ∃ b0,
                env[idx]? = some b0 ∧ b0.mode.isUnique = true ∧ OwnReach P st.heap b0.val l :=
              ⟨hconsT, i, hi, b, hbi, hmode0 ▸ huAb, hor0⟩
            have hnotF : ¬ Frame_call l := fun hF => hFclo l hF hcfL
            exact ⟨hnotF, fun hss => hnotF (hstat_call l hss)⟩
        · -- Pairwise disjointness across `i ≠ j` in `fvs.toList`
          intro i j b₁ b₂ ab₁ ab₂ hij hi hj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
          refine ⟨fun _ htr₁ _ _ l hor₁ hr₂ => ?_, fun _ _ _ _ h => False.elim h⟩
          obtain ⟨hu₁, hcv₁, _⟩ := htrOnlyUniq i hi ab₁ hab₁ htr₁
          obtain ⟨b₁_0, v₁', hb₁_0, _, _, _, _, hvsh1a, hvsh1b, hact1, hoo1, hnotOnce1,
            hv1, hbv1', _, _, hshV1'⟩ := hcapRel i hi b₁ ab₁ hb₁ hab₁
          obtain ⟨b₂_0, v₂', hb₂_0, _, _, _, _, hvsh2a, hvsh2b, hact2, _, hnotOnce2,
            hv2, hbv2', _, _, hshV2'⟩ := hcapRel j hj b₂ ab₂ hb₂ hab₂
          by_cases hcv₂ : (effVal ab₂).cls = .val
          · obtain ⟨aIdx, haLt, haEq⟩ := List.mem_iff_getElem.mp hi
            obtain ⟨bIdx, hbLt, hbEq⟩ := List.mem_iff_getElem.mp hj
            have hfa : fvs.toList[aIdx]? = some i := by rw [List.getElem?_eq_getElem haLt, haEq]
            have hfb : fvs.toList[bIdx]? = some j := by rw [List.getElem?_eq_getElem hbLt, hbEq]
            have habNe : aIdx ≠ bIdx := fun hEq => by subst hEq; exact hij (haEq.symm.trans hbEq)
            have hdisjD := hpairCaps aIdx bIdx i j ab₁ ab₂ habNe hfa hfb hab₁ hab₂ hu₁ hcv₁ hcv₂
            obtain ⟨ab₁', hab₁', _, _, _, _, _, huInfo1, _⟩ := hcapMem i hi
            rw [hab₁] at hab₁'; cases hab₁'
            obtain ⟨hown1, hlvDead1, _⟩ := (huInfo1 hu₁).2 hcv₁
            have htr1_0 : Transferable σ NoKill (effVal ab₁) :=
              ⟨hcv₁, hown1, hoo1, hnotOnce1,
               fun d hd => ⟨(hlvDead1 d hd).1, fun hnk => hNoKill d hnk (hlvDead1 d hd).2⟩⟩
            have hor1_0 : OwnReach P st.heap b₁_0.val l :=
              OwnReach_of_sameShapeOn_rev (hv1.2.2.2.2 hact1).1.1 (fun x o _ ho => hoss'.2 x o ho)
                (SameLoc.of_valSameShape hvsh1a)
                (OwnReach_of_sameShapeOn_rev hbv1'.1 hshV1' (SameLoc.of_valSameShape hvsh1b) hor₁)
            have hr2_0 : Reach st.heap b₂_0.val l :=
              Reach_of_sameShapeOn_rev (hv2.2.2.2.2 hact2).1.1 (fun x o _ ho => hoss'.2 x o ho)
                (SameLoc.of_valSameShape hvsh2a)
                (Reach_of_sameShapeOn_rev hbv2'.1 hshV2' (SameLoc.of_valSameShape hvsh2b) hr₂)
            exact (hsim.2.2.2.2.2.2 i j b₁_0 b₂_0 ab₁ ab₂ hij (hfvsScope i hi) (hfvsScope j hj)
              hb₁_0 hab₁ hb₂_0 hab₂ hne₁ hne₂).1 hact1 htr1_0 hact2 hdisjD l hor1_0 hr2_0
          · have hnv2_0 := (hv2.2.2.2.2 hact2).2.2.2.1 hnotOnce2 hcv₂
            have hnv2' := NonValSafe.of_sameShape (fun x o _ ho => hoss'.2 x o ho) hvsh2a hbv2'.1.self.1 hnv2_0
            have hbase2 := ValBaseOk.sub hfBase (hreachCapCall j hj b₂ hb₂).1
            have hnv2 := NonValSafe.of_sameShape hshV2' hvsh2b hbase2.1.self.1 hnv2'
            exact OwnReach_not_numLoc hor₁ (hnv2.reach_numLoc hr₂)
      refine ⟨cap_c, taint_c, o_c, env_call, rfl, ho_c, hcap_c, hcell_c,
        hokCall, hokOpen, hstOpen, hregU, hNoKillOpen, fun _ h => False.elim h, hsimCall, ?_, ?_, ?_, ?_⟩
      · intro Forbid BadReg BadDep hforbidDisj i b_c ab hi hbc _ _ _ _ _ l hr _ _ hF
        exact hforbidDisj l ((hreachCapCall i hi b_c hbc).2 l hr) hF
      · intro r _ hne c hc
        dsimp only [I_open, Interp.extend] at hc
        rw [beq_false_of_ne hne] at hc
        simp only [Bool.false_eq_true, ↓reduceIte, I_base] at hc
        by_cases h1 : (r == 1) = true
        · simp only [h1, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
          exact hc
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hc
          exact ⟨List.mem_append_right _ hc.1, hc.2⟩
      · intro c hc hlt
        have h1ne : (1 : Nat) ≠ s_a := by
          have h2 : 2 ≤ σ_call.nextRegion := hokCall.2.2.1
          change (1 : Nat) ≠ σ_call.nextRegion; omega
        dsimp only [I_open, Interp.extend]
        rw [beq_false_of_ne h1ne]
        simp only [Bool.false_eq_true, ↓reduceIte, I_base, beq_self_eq_true, List.mem_filter, decide_eq_true_eq]
        exact ⟨List.mem_append_left _ hc, hlt⟩
      · intro i hi b_c hbc
        exact (hreachCapCall i hi b_c hbc).2

end IxCK.Resource.Proof
