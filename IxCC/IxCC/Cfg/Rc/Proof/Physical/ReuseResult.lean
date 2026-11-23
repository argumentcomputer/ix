import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Physical.ReuseWrappers
import IxCC.Cfg.Rc.Proof.Physical.DropStep
import IxCC.Cfg.Rc.Proof.Physical.FrameTransport
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorTables
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Own.Plain.Proof.Owned.Reset
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Fir.Proof.Unfold

/-! # Physical simulation steps for `dropSlot`, `reuse`, and `reset` (Track A4)

Each theorem mirrors its abstract counterpart in `Own/Plain/Proof/Owned/Reset.lean` while
driving the concrete native LIR wrapper (`decrementWrapper`, `mkReuseWrapper` / `mkReuseUWrapper`,
`mkResetWrapper` / `mkResetUWrapper`) proved in `ReuseWrappers.lean`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-! ## Pure helpers shared by `dropSlot`, `reuse`, and `reset` -/

private theorem generate_known {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) : P.base.known = F.known := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P; rfl

private theorem ctorOk_of_validReuse {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {ctor : Fir.CtorInfo} {cls : Nat}
    (hct : Fir.CtorInfo.ofKey F.ctors ctor.key = some ctor)
    (hnz : F.known.natZero ≠ some ctor.key) (hns : F.known.natSucc ≠ some ctor.key)
    (hvc : Own.Plain.Ctx.validReuseCtor ctor = some cls) :
    Rt.Proof.CtorOk (tablesOf P pairs) ctor := by
  have hgen := (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have hctors : P.base.ctors = F.ctors := generate_ctors hgen
  have hknown : P.base.known = F.known := generate_known hgen
  obtain ⟨_, _, _, htag, _, _, _, _, _, _, _, _⟩ := validReuseCtor_full hvc
  refine ⟨by simpa [tablesOf, Rt.Lower.tables, consumed, hctors] using hct, ?_, htag⟩
  simp [tablesOf, Rt.Lower.tables, consumed, Rt.Lower.isNatKey, hknown, hnz, hns]

private theorem envRoots_cons_inv {m : Src.NatMap RVal} {a : Nat} {l : List Nat} {xs : List RVal}
    (h : Own.Plain.EnvRoots m (a :: l) xs) :
    ∃ v xs', m.get? a = some v ∧ Own.Plain.EnvRoots m l xs' ∧ xs = v :: xs' := by
  simp only [Own.Plain.EnvRoots, List.map_cons, Own.evalArgs, Own.evalArg] at h
  cases hm : m.get? a with
  | none => simp [hm] at h
  | some v =>
    cases hl : Own.evalArgs m (l.map Fir.Arg.var) with
    | none => simp [hm, hl] at h
    | some xs' =>
      simp only [hm, hl, Option.some.injEq] at h
      exact ⟨v, xs', rfl, hl, h.symm⟩

private theorem envRoots_cons {m : Src.NatMap RVal} {a : Nat} {l : List Nat} {v : RVal} {xs : List RVal}
    (hm : m.get? a = some v) (h : Own.Plain.EnvRoots m l xs) :
    Own.Plain.EnvRoots m (a :: l) (v :: xs) := by
  change Own.evalArgs m (l.map Fir.Arg.var) = some xs at h
  simp only [Own.Plain.EnvRoots, List.map_cons, Own.evalArgs, Own.evalArg, hm, h]

private theorem envRoots_perm_sameRefs {m : Src.NatMap RVal} {p q : List Nat}
    (hp : p.Perm q) :
    ∀ {xs ys : List RVal}, Own.Plain.EnvRoots m p xs → Own.Plain.EnvRoots m q ys →
      Own.Plain.SameRefs xs ys := by
  induction hp with
  | nil =>
    intro xs ys hx hy
    have h1 := Own.Plain.EnvRoots.nil_inv hx
    have h2 := Own.Plain.EnvRoots.nil_inv hy
    subst h1; subst h2; intro _; rfl
  | cons a _ ih =>
    intro xs ys hx hy
    obtain ⟨v1, xs', hma1, hx', rfl⟩ := envRoots_cons_inv hx
    obtain ⟨v2, ys', hma2, hy', rfl⟩ := envRoots_cons_inv hy
    have hv : v1 = v2 := Option.some.inj (hma1.symm.trans hma2)
    subst hv
    have hs := ih hx' hy'
    intro l; simp only [refsIn, hs l]
  | swap a b rest =>
    intro xs ys hx hy
    obtain ⟨vb1, xs1, hmb1, hx1, rfl⟩ := envRoots_cons_inv hx
    obtain ⟨va1, xs2, hma1, hx2, rfl⟩ := envRoots_cons_inv hx1
    obtain ⟨va2, ys1, hma2, hy1, rfl⟩ := envRoots_cons_inv hy
    obtain ⟨vb2, ys2, hmb2, hy2, rfl⟩ := envRoots_cons_inv hy1
    have h1 : va1 = va2 := Option.some.inj (hma1.symm.trans hma2)
    have h2 : vb1 = vb2 := Option.some.inj (hmb1.symm.trans hmb2)
    subst h1; subst h2
    have hrest : xs2 = ys2 := Option.some.inj (hx2.symm.trans hy2)
    subst hrest
    intro l; simp only [refsIn]; omega
  | trans _ _ ih1 ih2 =>
    intro xs ys hx hy
    have hex : ∀ {l : List Nat} {zs : List RVal}, Own.Plain.EnvRoots m l zs →
        ∀ l', l.Perm l' → ∃ zs', Own.Plain.EnvRoots m l' zs' := by
      intro l zs hzs l' hperm
      induction hperm generalizing zs with
      | nil =>
        have h1 := Own.Plain.EnvRoots.nil_inv hzs; subst h1
        exact ⟨[], rfl⟩
      | cons a _ ihp =>
        obtain ⟨v, zs', hma, hzs', rfl⟩ := envRoots_cons_inv hzs
        obtain ⟨zs'', hz'⟩ := ihp hzs'
        exact ⟨v :: zs'', envRoots_cons hma hz'⟩
      | swap a b rest =>
        obtain ⟨vb, zs1, hmb, h1, rfl⟩ := envRoots_cons_inv hzs
        obtain ⟨va, zs2, hma, h2, rfl⟩ := envRoots_cons_inv h1
        exact ⟨va :: vb :: zs2, envRoots_cons hma (envRoots_cons hmb h2)⟩
      | trans _ _ ihp1 ihp2 =>
        obtain ⟨z1, hz1⟩ := ihp1 hzs
        exact ihp2 hz1
    rename_i hperm1 _
    obtain ⟨zm, hzm⟩ := hex hx _ hperm1
    have h1 := ih1 hx hzm
    have h2 := ih2 hzm hy
    intro l; exact (h1 l).trans (h2 l)

private theorem slotVals_erase_sameRefs {Γ Γ' : Ctx} {rslots : Src.NatMap RVal}
    {slotVals slotVals' : List RVal} {s : Nat} {sv : RVal}
    (hs1 : ∃ keys, Own.Plain.Ctx.SlotKeys Γ keys ∧ Own.Plain.EnvRoots rslots keys slotVals)
    (hs2 : ∃ keys', Own.Plain.Ctx.SlotKeys Γ' keys' ∧ Own.Plain.EnvRoots (rslots.erase s) keys' slotVals')
    (hsv : rslots.get? s = some sv)
    (hscont : Γ.rset.contains s = true)
    (hrset : Γ'.rset = Γ.rset.erase s) :
    Own.Plain.SameRefs slotVals (sv :: slotVals') := by
  obtain ⟨skeys, hsk, hsroots⟩ := hs1
  obtain ⟨skeys', hsk', hsroots'⟩ := hs2
  obtain ⟨hsmem, hsk₁⟩ := hsk.erase hscont (Γ' := Γ') hrset
  obtain ⟨slotVals₁, hsroots₁_old, hssame⟩ := Own.Plain.EnvRoots.erase hsv hsroots hsmem
  have hsroots₁ : Own.Plain.EnvRoots (rslots.erase s) (skeys.erase s) slotVals₁ :=
    hsroots₁_old.congr (fun s' hs' => by
      have hne : s' ≠ s := (hsk.nodup.mem_erase_iff.mp hs').1
      simp [Src.NatMap.get?_erase, hne])
  have hperm : (skeys.erase s).Perm skeys' :=
    (List.perm_ext_iff_of_nodup hsk₁.nodup hsk'.nodup).mpr (fun s' => by
      rw [hsk₁.mem s', hsk'.mem s'])
  have hsr : Own.Plain.SameRefs slotVals₁ slotVals' :=
    envRoots_perm_sameRefs hperm hsroots₁ hsroots'
  intro l
  have h1 := hssame l
  have h2 := hsr l
  simp only [refsIn] at h1 ⊢; omega

private theorem bindParams_range_aux : ∀ (n off : Nat) (env : Lir.Env) (ws : List Lir.Word)
    (hlen : ws.length = n),
    ∃ env', Lir.bindParams env ((List.range n).map (off + ·)) ws = some env' ∧
      (∀ r < off, env'[r]? = env[r]?) ∧
      (∀ j (hj : j < n), env'[off + j]? = some (ws[j]'(by omega)))
  | 0, off, env, [], _ =>
    ⟨env, rfl, fun _ _ => rfl, fun _ hj => by omega⟩
  | 0, _, _, _ :: _, hlen => by simp at hlen
  | n + 1, _, _, [], hlen => by simp at hlen
  | n + 1, off, env, w :: ws, hlen => by
    have hrange : (List.range (n + 1)).map (off + ·) = off :: (List.range n).map (off + 1 + ·) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _; dsimp only [Function.comp_apply]; omega
    obtain ⟨env', hbp, hkeep, hset⟩ :=
      bindParams_range_aux n (off + 1) (env.insert off w) ws (by simpa using hlen)
    refine ⟨env', ?_, ?_, ?_⟩
    · rw [hrange]; simp only [Lir.bindParams]; exact hbp
    · intro r hr
      rw [hkeep r (by omega), Lir.env_insert_ne _ _ (by omega)]
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.add_zero, hkeep off (by omega), Lir.env_insert_self]
        rfl
      | succ j' =>
        have h1 := hset j' (by omega)
        rw [show off + (j' + 1) = off + 1 + j' by omega]
        exact h1

private theorem bindParams_range (n : Nat) (ws : List Lir.Word) (hlen : ws.length = n) :
    ∃ env, Lir.bindParams ({} : Lir.Env) (List.range n) ws = some env ∧
      (∀ j (hj : j < n), env[j]? = some (ws[j]'(by omega))) := by
  obtain ⟨env, hbp, _, hset⟩ := bindParams_range_aux n 0 {} ws hlen
  refine ⟨env, by simpa using hbp, fun j hj => by simpa using hset j hj⟩

private theorem listRel_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Rt.Proof.ListRel R xs ys →
      xs.length = ys.length ∧
      ∀ (j : Nat) (u : α), xs[j]? = some u → ∃ w, ys[j]? = some w ∧ R u w
  | [], [], .nil => ⟨rfl, fun _ _ h => by cases h⟩
  | x :: xs, y :: ys, .cons hxy hrel => by
    obtain ⟨hlen, hget⟩ := listRel_getElem hrel
    refine ⟨by simp [hlen], ?_⟩
    intro j u hj
    cases j with
    | zero => simp at hj; subst hj; exact ⟨y, rfl, hxy⟩
    | succ j' => exact hget j' u hj

private theorem reusedHeap_size (H : Heap) (l : Nat) (b' : Body) :
    (reusedHeap H l b').size = H.size + 1 := by
  unfold reusedHeap
  simp only [Own.Heap.alloc, Own.Heap.size, Array.size_push]
  have hs := setCell_size H l .dead
  simp only [Own.Heap.size] at hs
  omega

private theorem reset_inv {ctors : List Lam.CtorInfo} {K : Lam.Known} {Γ : Ctx}
    {s : Nat} {x : Fir.Var} {ctor : Fir.CtorInfo}
    {fields : List (Option Fir.Var)} {uniq : Bool} {Γ' : Ctx}
    (h : Γ.reset ctors s x ctor fields uniq K = .ok Γ') :
    Fir.CtorInfo.ofKey ctors ctor.key = some ctor ∧
    K.natZero ≠ some ctor.key ∧ K.natSucc ≠ some ctor.key ∧
    (∃ cls, Ctx.validReuseCtor ctor = some cls ∧
      Γ.rset.contains s = false ∧
      Γ.ctorOf.get? x = some ctor.key ∧
      fields.length = ctor.arity ∧
      Γ.isImm x = false ∧
      (uniq = true → Γ.isUniq x = true) ∧
      ∃ Γ₁ Γ₂, Γ.take x = .ok Γ₁ ∧
        Ctx.promoteResetFields Γ x ctor.key 0 fields Γ₁ = .ok Γ₂ ∧
        Γ' = { Γ₂.release with rset := Γ₂.rset.insert s (cls, uniq) }) := by
  unfold Ctx.reset at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hct : (Fir.CtorInfo.ofKey ctors ctor.key == some ctor) with
  | false => simp [hct] at h
  | true =>
    simp only [hct, ↓reduceIte] at h
    have hct' : Fir.CtorInfo.ofKey ctors ctor.key = some ctor := beq_iff_eq.mp hct
    cases hnat : (K.natZero == some ctor.key || K.natSucc == some ctor.key) with
    | true => simp [hnat] at h
    | false =>
      simp only [hnat, Bool.false_eq_true, ↓reduceIte] at h
      have hnz : K.natZero ≠ some ctor.key := by intro he; simp [he] at hnat
      have hns : K.natSucc ≠ some ctor.key := by intro he; simp [he] at hnat
      cases hvc : Ctx.validReuseCtor ctor with
      | none => simp [hvc] at h
      | some cls =>
        simp only [hvc] at h
        cases hrs : Γ.rset.contains s with
        | true => simp [hrs] at h
        | false =>
          simp only [hrs, Bool.false_eq_true, ↓reduceIte] at h
          cases hco : (Γ.ctorOf.get? x == some ctor.key) with
          | false => simp [hco] at h
          | true =>
            simp only [hco, ↓reduceIte] at h
            have hco' : Γ.ctorOf.get? x = some ctor.key := beq_iff_eq.mp hco
            cases hfl : (fields.length == ctor.arity) with
            | false => simp [hfl] at h
            | true =>
              simp only [hfl, ↓reduceIte] at h
              have hfl' : fields.length = ctor.arity := beq_iff_eq.mp hfl
              cases him : Γ.isImm x with
              | true => simp [him] at h
              | false =>
                simp only [him, Bool.false_eq_true, ↓reduceIte] at h
                cases huq : (uniq && !Γ.isUniq x) with
                | true => simp [huq] at h
                | false =>
                  simp only [huq, Bool.false_eq_true, ↓reduceIte] at h
                  have huq' : uniq = true → Γ.isUniq x = true := by intro hu; subst hu; simpa using huq
                  cases ht : Γ.take x with
                  | error _ => simp [ht] at h
                  | ok Γ₁ =>
                    simp only [ht] at h
                    cases hprom : Ctx.promoteResetFields Γ x ctor.key 0 fields Γ₁ with
                    | error _ => simp [hprom] at h
                    | ok Γ₂ =>
                      simp only [hprom, Except.ok.injEq] at h
                      exact ⟨hct', hnz, hns, cls, rfl, rfl, hco', hfl', rfl, huq', Γ₁, Γ₂, rfl, hprom, h.symm⟩

private theorem reuse_inv {ctors : List Lam.CtorInfo} {K : Lam.Known} {Γ : Ctx}
    {x : Fir.Var} {s : Nat} {ctor : Fir.CtorInfo}
    {args : List Fir.Arg} {uniq : Bool} {Γ' : Ctx}
    (h : Γ.reuse ctors x s ctor args uniq K = .ok Γ') :
    Γ.known x = false ∧
    Fir.CtorInfo.ofKey ctors ctor.key = some ctor ∧
    K.natZero ≠ some ctor.key ∧ K.natSucc ≠ some ctor.key ∧
    (∃ cls slotUniq, Ctx.validReuseCtor ctor = some cls ∧
      args.length = ctor.arity ∧
      Γ.rset.get? s = some (cls, slotUniq) ∧
      (uniq = true → slotUniq = true) ∧
      ∃ Γ₂, ({ Γ with rset := Γ.rset.erase s } : Ctx).takeArgs args = .ok Γ₂ ∧
        Γ' = Γ₂.addUniqOwn x) := by
  unfold Ctx.reuse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hkn : Γ.known x with
  | true => simp [hkn] at h
  | false =>
    simp only [hkn, Bool.false_eq_true, ↓reduceIte] at h
    cases hct : (Fir.CtorInfo.ofKey ctors ctor.key == some ctor) with
    | false => simp [hct] at h
    | true =>
      simp only [hct, ↓reduceIte] at h
      have hct' : Fir.CtorInfo.ofKey ctors ctor.key = some ctor := beq_iff_eq.mp hct
      cases hnat : (K.natZero == some ctor.key || K.natSucc == some ctor.key) with
      | true => simp [hnat] at h
      | false =>
        simp only [hnat, Bool.false_eq_true, ↓reduceIte] at h
        have hnz : K.natZero ≠ some ctor.key := by intro he; simp [he] at hnat
        have hns : K.natSucc ≠ some ctor.key := by intro he; simp [he] at hnat
        cases hvc : Ctx.validReuseCtor ctor with
        | none => simp [hvc] at h
        | some cls =>
          simp only [hvc] at h
          cases hal : (args.length == ctor.arity) with
          | false => simp [hal] at h
          | true =>
            simp only [hal, ↓reduceIte] at h
            have hal' : args.length = ctor.arity := beq_iff_eq.mp hal
            cases hrs : Γ.rset.get? s with
            | none => simp [hrs] at h
            | some pair =>
              obtain ⟨slotCls, slotUniq⟩ := pair
              simp only [hrs] at h
              cases hcm : (slotCls == cls) with
              | false => simp [hcm] at h
              | true =>
                simp only [hcm, ↓reduceIte] at h
                have hce : slotCls = cls := beq_iff_eq.mp hcm
                subst hce
                cases huq : (uniq && !slotUniq) with
                | true => simp [huq] at h
                | false =>
                  simp only [huq, Bool.false_eq_true, ↓reduceIte] at h
                  have huq' : uniq = true → slotUniq = true := by intro hu; subst hu; simpa using huq
                  cases ht : ({ Γ with rset := Γ.rset.erase s } : Ctx).takeArgs args with
                  | error _ => simp [ht] at h
                  | ok Γ₂ =>
                    simp only [ht, Except.ok.injEq] at h
                    exact ⟨rfl, hct', hnz, hns, slotCls, slotUniq, rfl, hal', rfl, huq', Γ₂, rfl, h.symm⟩

private theorem dropSlot_inv {Γ : Ctx} {s : Nat} {Γ' : Ctx}
    (h : Γ.dropSlot s = .ok Γ') :
    Γ.rset.contains s = true ∧ Γ' = { Γ.release with rset := Γ.rset.erase s } := by
  unfold Ctx.dropSlot at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hc : Γ.rset.contains s with
  | false => simp [hc] at h
  | true =>
    simp only [hc, ↓reduceIte, Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩

private theorem heapHistory_reuseCell {H H' : Heap} {l : Nat} {b' : Body}
    (hc : H.cell? l = some (.live 1 .dyn b'))
    {b'' : Body} (hrc : reuseCell H l b'' = some (.loc H.size, H'))
    (addresses : AddressMap) (address : Lir.Word) :
    H'.size = H.size + 1 ∧
    HeapHistory H.size addresses H'.size (placeFresh addresses H.size address) := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hrc
  refine ⟨reusedHeap_size H l b'', ⟨by rw [reusedHeap_size]; omega, ?_⟩⟩
  intro loc hlt
  simp [placeFresh, Nat.ne_of_lt hlt]

private theorem envBounded_insert {n : Nat} {env : Own.Env}
    (hb : Own.Plain.EnvBounded n env) {x : Nat} {v : RVal} (hv : Own.Plain.Bounded n v) :
    Own.Plain.EnvBounded n (env.insert x v) := by
  intro y u hy
  by_cases h : y = x
  · subst h; rw [Src.NatMap.get?_insert_self] at hy; cases hy; exact hv
  · rw [Src.NatMap.get?_insert_ne _ _ h] at hy; exact hb y u hy

private theorem fails_prefix_res {α β : Type} {step : α → Sem.Step α β} {s s' : α} {c : Nat}
    (h : Sem.Star step s c s') (hf : Sem.Fails step s') : Sem.Fails step s :=
  let ⟨c', t, r, ht, hr⟩ := hf
  ⟨c + c', t, r, h.trans ht, hr⟩

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

/-! ## `physical_dropSlot` -/

/-- **Drop a reset slot** (`.dropSlot s k`): executes the lowered `dec (slotBase + s)` marker
via `decrementWrapper` + `Gen.dec`, matching `Own.Plain.dropSlot_step`. -/
theorem physical_dropSlot (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {s : Nat} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.dropSlot s k) borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  obtain ⟨Γ', hdrop, typed⟩ := Own.Plain.checkCode_dropSlot before.typed
  obtain ⟨hscont, hΓ'eq⟩ := dropSlot_inv hdrop
  obtain ⟨sv, H', slotVals', hsv, hev, state, hreach, hpriv⟩ :=
    Own.Plain.dropSlot_step before.owned hdrop
  -- Extract the exact `dec (slotBase + s)` marker from `before.layout`.
  obtain ⟨fd, scope, params, acc, nextB, first, lo, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before.layout
  have head : source.rest = marker P.base.size first (.dec (slotBase + s)) ::
      Cfg.Proof.spine (skeleton P.base.size (first + 1) k F.ctors slotBase) := by
    simpa only [skeleton, Cfg.Proof.spine, markerRhs_eq] using cursor
  obtain ⟨_, blockLookup⟩ := Cfg.Proof.impl_head layout
  have member : marker P.base.size first (.dec (slotBase + s)) ∈
      (acc.reverse ++ Cfg.Proof.spine (skeleton P.base.size first (.dropSlot s k) F.ctors slotBase)) := by
    simp [skeleton, Cfg.Proof.spine, markerRhs_eq]
  have markerBound : funcFirst bodies source.fn sourceFunction ≤ first :=
    (checked_marker_bounds admission.scopedProgram range sourceLookup lookup blockLookup
      member (reserved_marker P.base.size first (.dec (slotBase + s)))
      (decode_marker P.base.size first (.dec (slotBase + s)))).1
  have frameLookup : source.env.get? (slotBase + s) = some sv := slotSub s sv hsv
  have consuming : consume P (layoutOf P) (marker P.base.size first (.dec (slotBase + s))) =
      .ok (.bind first (.fir (.call (P.base.size + 1) [.var (slotBase + s)]))) :=
    IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_decrement P (layoutOf P) first (slotBase + s)
  have liveOperand : ¬ Rt.Proof.Fused (tablesOf P pairs) function (slotBase + s) :=
    consumed_call_live before.frame.cursor head consuming before.frame.lookup (.var (slotBase + s))
      (by simp) (slotBase + s) rfl
  obtain ⟨svWord, hsvWord, hreg⟩ := before.frame.words.word frameLookup liveOperand
  -- Lower the call instruction via `cursor.call`.
  let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
  rcases before.frame.cursor.call head consuming memory context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookupLir,
      position, statement, continuation⟩ := success
    have operandsKnown : Rt.Lower.operands source.fn [.var (slotBase + s)] =
        .ok (some [.v (slotBase + s)]) := rfl
    rw [operandsKnown] at lowered
    cases lowered
    obtain ⟨wrapLookup, decLookup⟩ :=
      source_stage_decrement_runtime P (Public.Spec.rawSource config P pairs) main
    let cont : Lir.Frame := { target with pos := target.pos + 1, dsts := [first] }
    have henterWrap : Lir.enter lp (P.base.size + 1) [svWord] =
        some { fn := P.base.size + 1, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 svWord } := by
      simp [Lir.enter, lp, wrapLookup, decrementWrapper, Lir.bindParams]
    have hcallWrap := Lir.step_call (p := lp) (mem := memory) (ctx := context) (rest := callers)
      (fr := target) functionLookup blockLookupLir position statement
      (vs := [svWord]) (by simp [Lir.evalArgs, Lir.Arg.eval, hreg]) henterWrap
    have henterDec : Lir.enter lp (layoutOf P).decProc [svWord] =
        some { fn := (layoutOf P).decProc, label := 0, pos := 0, env := Gen.decEnv svWord } := by
      simp [Lir.enter, lp, decLookup, Gen.dec, Lir.bindParams, Gen.decEnv]
    let wrapAfterDec : Lir.Frame :=
      { fn := P.base.size + 1, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 svWord, dsts := [] }
    have hwrapBlk0 : (decrementWrapper (layoutOf P).decProc).blocks[0]? =
        some { body := #[.call [] (layoutOf P).decProc [.v 0]], term := .ret [.imm 1] } := rfl
    have hcallDec := Lir.step_call (p := lp) (mem := memory) (ctx := context) (rest := cont :: callers)
      (fr := { fn := P.base.size + 1, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 svWord })
      wrapLookup hwrapBlk0 (by simp) rfl (vs := [svWord])
      (by simp [Lir.evalArgs, Lir.Arg.eval]) henterDec
    -- Rebase roots to `[sv] ++ (roots ++ slotVals')`.
    have hsrSlots := slotVals_erase_sameRefs before.owned.slotRoots state.slotRoots hsv hscont
      (by rw [hΓ'eq])
    have hsrAll : Own.Plain.SameRefs (roots ++ slotVals) (sv :: (roots ++ slotVals')) := by
      intro l; have h1 := hsrSlots l; simp only [refsIn_append, refsIn] at h1 ⊢; omega
    have hreadySplit : Gen.AllocatorReady maxClass H addresses memory
        (fun k => holdRoots external (roots ++ slotVals') k + refsIn k [sv])
        context base bump limit slots lists := by
      have heq : holdRoots external (roots ++ slotVals) =
          fun k => holdRoots external (roots ++ slotVals') k + refsIn k [sv] := by
        funext k; have h1 := hsrAll k; simp only [holdRoots, refsIn] at h1 ⊢; omega
      rw [← heq]; exact heap.ready
    obtain ⟨H₂, mem', slots', lists', chDec, hda, hready', hdecTrace⟩ :=
      hreadySplit.release_caller_ready svWord hsvWord lp (layoutOf P).decProc decLookup
        wrapAfterDec (cont :: callers) rfl
    have hHeq : H' = H₂ := by
      simp only [Own.Plain.evalDropVal, hda, Sem.Result.ofOption, Sem.Result.ok.injEq] at hev
      exact hev.symm
    subst hHeq
    have hretWrap := Lir.step_ret_caller (p := lp) (vals := [1]) (ρ := target.env.insert first 1)
      (mem := mem') (ctx := context) (fr := wrapAfterDec) (caller := cont) (rest' := callers)
      wrapLookup hwrapBlk0 (by simp [wrapAfterDec]) rfl
      (by simp [Lir.evalArgs, Lir.Arg.eval]) (by simp [cont, Lir.bindParams])
    have htrace : Sem.Star (Lir.semStep lp)
        { mem := memory, ctx := context, stack := target :: callers } (1 + (1 + chDec))
        { mem := mem', ctx := context,
          stack := { target with pos := target.pos + 1, env := target.env.insert first 1, dsts := [] } :: callers } := by
      have hjoin := (Sem.Star.single (Lir.semStep_next.mpr hcallWrap)).trans
        ((Sem.Star.single (Lir.semStep_next.mpr hcallDec)).trans
          (hdecTrace.trans (Sem.Star.single (Lir.semStep_next.mpr hretWrap))))
      simpa [cont, wrapAfterDec, Nat.add_assoc] using hjoin
    have hsize : H'.size = H.size := dropAll_size H [sv] hda
    have hbalSplit : Balance H (holdRoots external (roots ++ slotVals')) [sv] :=
      balance_hold.mp (hsrAll.balance before.owned.counts)
    have hok' : HeapOk H' := by
      obtain ⟨H₃, hda₃, _, hok₃⟩ := dropAll_heapOk H [sv] hbalSplit heap.ordered
      rw [hda] at hda₃; cases hda₃; exact hok₃
    have heap' : HeapState P pairs H' addresses mem' external (roots ++ slotVals')
        context base bump limit regionBytes slots' lists' :=
      ⟨hready', hok', heap.compatible.dropAll H [sv] hda, heap.extent⟩
    have afterLayout : At F P
        { source with rest := Cfg.Proof.spine (skeleton P.base.size (first + 1) k F.ctors slotBase) }
        ownedEnv ownedJoins k (rslots.erase s) :=
      ⟨fd, scope, params, marker P.base.size first (.dec (slotBase + s)) :: acc, nextB, first + 1,
        lo, slotBase, lookup, range, impl_after_dropSlot layout, rfl, sub, below, loSlot,
        slotSub.erase s, scopedNames, vb, rc, joins⟩
    have activation : Activation F P pairs lp H' addresses external live Γ' Δ
        sourceEnv ownedEnv roots lex sourceJoins ownedJoins k
        (funcFirst bodies source.fn sourceFunction) function
        { source with rest := Cfg.Proof.spine (skeleton P.base.size (first + 1) k F.ctors slotBase) }
        { target with pos := target.pos + 1, env := target.env.insert first 1, dsts := [] }
        borrows uniqs retUniq priv (rslots.erase s) slotVals' :=
      ⟨state, typed, afterLayout,
        ⟨before.frame.lookup, continuation.withEnvs source.env (target.env.insert first 1) [],
          before.frame.words.marker markerBound 1, by rw [hsize]; exact before.frame.bounded,
          before.frame.compatible⟩,
        before.scope, rfl,
        consumed_call_done before.frame.lookup before.frame.cursor head consuming source.env⟩
    have history : HeapHistory H.size addresses H'.size addresses :=
      ⟨by omega, fun _ _ => rfl⟩
    exact ResultAt.prefix htrace hreach hpriv history (by omega)
      (next H' addresses external retUniq priv (rslots.erase s) slotVals' live Γ' Δ sourceEnv
        ownedEnv roots lex ownedJoins sourceFunction function
        { source with rest := Cfg.Proof.spine (skeleton P.base.size (first + 1) k F.ctors slotBase) }
        { target with pos := target.pos + 1, env := target.env.insert first 1, dsts := [] }
        mem' context base bump limit regionBytes slots' lists' callers sourceLookup activation heap')
  · have same : Lir.atState memory context target.fn target.label target.pos target.env callers =
        ({ mem := memory, ctx := context, stack := target :: callers } : Lir.State) := by
      have hr := before.running; cases target; simp_all [Lir.atState]
    rw [same] at failure
    exact ResultAt.of_fails failure

/-! ## `physical_reuse` -/

/-- **Reuse a reset slot** (`.reuse x s ctor args uniq k`): executes `mkReuseUWrapper` (`uniq = true`)
or `mkReuseWrapper` (`uniq = false`, in-place on `.loc l` or fallback allocation on `.erased`),
matching `Own.Plain.reuse_step`. -/
theorem physical_reuse (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {x : Fir.Var} {s : Nat} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {uniq : Bool}
    {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.reuse x s ctor args uniq k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.ctor ctor args) (Own.Plain.eraseCode k)))
    F.ctors retUniq priv
  have scopeFacts := before.scope
  simp only [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] at scopeFacts
  obtain ⟨freshBool, _, bodyScope⟩ := scopeFacts
  have fresh : x ∉ live := by simpa using freshBool
  obtain ⟨Γ', hreuse, typed⟩ := Own.Plain.checkCode_reuse before.typed
  obtain ⟨_, hct, hnz, hns, cls, slotUniq, hvc, halen, hrs, huq, Γ₂, ht, hΓ'eq⟩ :=
    reuse_inv hreuse
  obtain ⟨hpos, _, _, htag, hnsc, hnobj, hfk, _, _, hclsLay, _, _⟩ := validReuseCtor_full hvc
  -- Evaluate the constructor arguments on both source and owned environments.
  let Γ₁ : Ctx := { Γ with rset := Γ.rset.erase s }
  have htinv₁ : Own.Plain.TakeInv H Γ₁ sourceEnv ownedEnv roots := by
    obtain ⟨toks0, htok0, hroots0⟩ := before.owned.roots
    exact ⟨before.owned.den, ⟨toks0, htok0.same rfl rfl, hroots0⟩, before.owned.immOk⟩
  obtain ⟨vs, logical, owned₁, ownArgs, sourceArgs, den, _, hrefsOwned, _⟩ :=
    Own.Plain.takeArgs_sem htinv₁ ht
  have hvlen : vs.length = ctor.arity := (Own.evalArgs_length ownedEnv ownArgs).trans halen
  have hllen : logical.length = ctor.arity := den.length.symm.trans hvlen
  have hfirRhs : Fir.evalRhs F sourceEnv (.ctor ctor args) = .ok (.ctor ctor logical) := by
    rw [Fir.evalRhs_ctor, sourceArgs]
    simp [Sem.Result.ofOption, hllen]
  rw [Fir.eval_bind_ctor, hfirRhs]
  simp only [Sem.Result.bind_ok]
  -- Abstract reuse step.
  obtain ⟨sv, v, H', owned', slotVals', hsv, hev, state, hreach, hpriv⟩ :=
    Own.Plain.reuse_step before.owned fresh hreuse hfirRhs
  -- Unpack `before.layout` to obtain the reuse marker and real-register bound for `x`.
  obtain ⟨fd, scope, params, acc, nextB, first, lo, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before.layout
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  simp only [varsBelow, Bool.and_eq_true, decide_eq_true_eq] at vb
  simp only [reuseCtorsOk, Bool.and_eq_true, decide_eq_true_eq] at rc
  let ci := heapCtorIndex F.ctors ctor.key
  let ins := reuseMarker P.base.size x (slotBase + s) ci uniq args
  let tail := Cfg.Proof.spine (skeleton P.base.size first k F.ctors slotBase)
  have head : source.rest = ins :: tail := cursor
  have xReal : x < funcFirst bodies source.fn sourceFunction := by
    obtain ⟨_, blockLookup⟩ := Cfg.Proof.impl_head layout
    have hfb := checked_source_bounds admission.scopedProgram range sourceLookup lookup
    have heach := (functionBounds_block hfb blockLookup).2.1
    have hmem : ins ∈ acc.reverse ++ Cfg.Proof.spine
        (skeleton P.base.size first (.reuse x s ctor args uniq k) F.ctors slotBase) := by
      simp [ins, ci, reuseMarker, skeleton, Cfg.Proof.spine]
    have hbd := List.all_eq_true.mp heach _ hmem
    have hnr : reserved P.base.size ins = false := by simp [ins, reuseMarker, reserved]
    have hir : isReuseOp P.base.size ins = true := by simp [ins, reuseMarker, isReuseOp]
    have hdr : decodeReset P.base.size ins = none := by simp [ins, reuseMarker, decodeReset]
    have hdu : decodeReuse P.base.size ins = some (x, slotBase + s, ci, uniq, args) := by
      cases uniq <;> simp [ins, reuseMarker, decodeReuse]
    simp only [instrBound, hnr, hir, hdr, hdu, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq] at hbd
    exact hbd.1.1
  -- Invert `consume` on the reuse marker and obtain runtime wrapper lookups.
  obtain ⟨row, hrow, htagRow, harityRow⟩ := layout_ctor_at_index admission.scopedProgram hct hpos
  obtain ⟨actual, _, hcons0, _, _⟩ := before.frame.cursor.next head
  have hactEq := consume_reuse_of hcons0 hrow
  subst hactEq
  let callee := if uniq then (layoutOf P).reuseUWrapper ci else (layoutOf P).reuseWrapper ci
  have consuming : consume P (layoutOf P) ins =
      .ok (.bind x (.fir (.call callee (.var (slotBase + s) :: args)))) := hcons0
  have liveArgs := consumed_call_live before.frame.cursor head consuming before.frame.lookup
  -- Evaluate `.var (slotBase + s) :: args` in `source.env`.
  have hframeArgs : Own.evalArgs source.env (.var (slotBase + s) :: args) = some (sv :: vs) := by
    simp only [Own.evalArgs, Own.evalArg, slotSub s sv hsv, Cfg.Proof.evalArgs_sub sub ownArgs]
  let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
  obtain ⟨hreuseWrap, hreuseUWrap, hallocProc⟩ :=
    source_stage_reuse_runtime P (Public.Spec.rawSource config P pairs) main ci hrow
      (by rw [harityRow, htagRow]; exact hclsLay)
  rw [harityRow, htagRow] at hreuseWrap hreuseUWrap hallocProc
  have hcalleeFn : lp.funcs[callee]? = some (if uniq
      then mkReuseUWrapper (CellLayout.ofFields ctor.arity ctor.tag) cls
      else mkReuseWrapper ((layoutOf P).allocProc ci) (CellLayout.ofFields ctor.arity ctor.tag) cls) := by
    cases uniq <;> simpa [callee] using (by first | exact hreuseUWrap | exact hreuseWrap)
  -- Execute the LIR call into `callee`.
  rcases before.frame.cursor.call head consuming memory context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookupLir,
      position, statement, continuation⟩ := success
    obtain ⟨words, hevalWords, hrelWords, _⟩ :=
      fused_operands_words before.frame.words lowered liveArgs hframeArgs
    obtain ⟨hwlen, hgetWord⟩ := listRel_getElem hrelWords
    have hwsLen : words.length = ctor.arity + 1 := by simp at hwlen; omega
    obtain ⟨wrapEnv, hbindWrap, hwrapGet⟩ := bindParams_range (ctor.arity + 1) words hwsLen
    have henter : Lir.enter lp callee words = some { fn := callee, label := 0, pos := 0, env := wrapEnv } := by
      cases uniq <;>
        simp [Lir.enter, hcalleeFn, mkReuseUWrapper, mkReuseWrapper, CellLayout.ofFields, hbindWrap]
    let cont : Lir.Frame := { target with pos := target.pos + 1, dsts := [x] }
    have hcall := Lir.step_call (p := lp) (mem := memory) (ctx := context) (rest := callers)
      (fr := target) functionLookup blockLookupLir position statement hevalWords henter
    -- Extract slot word `words[0]` and field words `fun j => words[j + 1]!`.
    have hsvRel : valueWord addresses sv = some (words[0]'(by omega)) := by
      obtain ⟨w0, hw0, hvw0⟩ := hgetWord 0 sv rfl
      rw [List.getElem?_eq_getElem (by omega : 0 < words.length)] at hw0
      cases hw0; exact hvw0
    have hwrap0 : wrapEnv[0]? = some (words[0]'(by omega)) := hwrapGet 0 (by omega)
    let argWords : Nat → Lir.Word := fun j => words[j + 1]!
    have hwrapArgs : ∀ j < ctor.arity, wrapEnv[j + 1]? = some (argWords j) := by
      intro j hj
      have hj1 : j + 1 < words.length := by omega
      simpa [argWords, hj1] using hwrapGet (j + 1) (by omega)
    have hargVals : ∀ j u, vs[j]? = some u → valueWord addresses u = some (argWords j) := by
      intro j u hj
      have hjLt : j < ctor.arity := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
      obtain ⟨wj, hwj, hvwj⟩ := hgetWord (j + 1) u (by simpa using hj)
      have hj1 : j + 1 < words.length := by omega
      rw [List.getElem?_eq_getElem hj1] at hwj
      cases hwj
      simpa [argWords, hj1] using hvwj
    -- Common `BodyOk`, `BodyCtorOk`, and slot root-erasure facts.
    have hframeOnlyArgs : Own.evalArgs source.env args = some vs := Cfg.Proof.evalArgs_sub sub ownArgs
    have hfieldBounds := before.frame.bounded.args args hframeOnlyArgs
    have hbodyOk : BodyOk H.size { ctor, fields := vs } :=
      ⟨hvlen, hpos, fun loc hm => hfieldBounds (.loc loc) hm⟩
    have hliveOnlyArgs : ∀ a ∈ args, Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) a :=
      fun a ha => liveArgs a (List.mem_cons_of_mem _ ha)
    have hbodyCtorOk : BodyCtorOk (tablesOf P pairs) { ctor, fields := vs } :=
      ⟨ctorOk_of_validReuse admission.scopedProgram hct hnz hns hvc,
        by simp [Fir.CtorInfo.fieldless]; omega,
        before.frame.compatible.args hliveOnlyArgs hframeOnlyArgs⟩
    have hscont : Γ.rset.contains s = true := by simp [Src.NatMap.contains, hrs]
    have hsrSlots := slotVals_erase_sameRefs before.owned.slotRoots state.slotRoots hsv hscont
      (by
        rw [hΓ'eq]
        have hr2 := (Own.Plain.Ctx.takeArgs_weaker ht).rset
        simpa [Γ₁, Own.Plain.Ctx.addUniqOwn] using hr2)
    -- Split on `before.owned.rsetOk s cls slotUniq hrs` (`sv = .erased` vs `sv = .loc l`).
    obtain ⟨sv0, hsv0, hsvCase⟩ := before.owned.rsetOk s cls slotUniq hrs
    have hEqSv : sv0 = sv := Option.some.inj (hsv0.symm.trans hsv)
    subst hEqSv
    rcases hsvCase with ⟨rfl, hsluF⟩ | ⟨l, b, rfl, hcl, hvcb, hbfErased, _, _, _⟩
    · -- Fallback allocation on `.erased` (`uniq = false`).
      have huqF : uniq = false := by
        cases hu : uniq with
        | false => rfl
        | true => exact absurd (huq hu) (by simp [hsluF])
      subst huqF
      simp only [Bool.false_eq_true, ↓reduceIte] at hcalleeFn
      have hw0Eq : words[0]'(by omega) = 1 := Option.some.inj (hsvRel.symm.trans rfl)
      rw [hw0Eq] at hwrap0
      have hsrReady : Own.Plain.SameRefs (roots ++ slotVals) (vs ++ (owned₁ ++ slotVals')) := by
        intro k; have h1 := hrefsOwned k; have h2 := hsrSlots k
        simp only [refsIn_append, refsIn, reduceCtorEq, ↓reduceIte] at h1 h2 ⊢; omega
      have hreadySplit : Gen.AllocatorReady maxClass H addresses memory
          (fun k => holdRoots external (owned₁ ++ slotVals') k + refsIn k vs)
          context base bump limit slots lists := by
        have heq : holdRoots external (roots ++ slotVals) =
            fun k => holdRoots external (owned₁ ++ slotVals') k + refsIn k vs := by
          funext k; have h1 := hsrReady k; simp only [holdRoots, refsIn_append] at h1 ⊢; omega
        rw [← heq]; exact heap.ready
      rcases reuse_wrapper_fallback_exec hcalleeFn hallocProc hreadySplit hvc hvlen hwrap0
          hwrapArgs hargVals cont callers rfl with
        ⟨address, bump', mem', slots', lists', hreadyOut, hwrapTrace⟩ | hfail
      · -- Fallback allocation succeeded: match `H.alloc .rc { ctor, fields := vs }`.
        have hnotfl : ctor.fieldless = false := by simp [Fir.CtorInfo.fieldless]; omega
        have hevEq : v = (H.alloc .rc { ctor, fields := vs }).1 ∧
            H' = (H.alloc .rc { ctor, fields := vs }).2 := by
          simp only [Own.Plain.evalReuseVal, ownArgs, hnotfl, Bool.not_false, hvlen,
            decide_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true, Sem.Result.ok.injEq] at hev
          exact ⟨(congrArg Prod.fst hev).symm, (congrArg Prod.snd hev).symm⟩
        obtain ⟨rfl, rfl⟩ := hevEq
        have hbalOut : Balance (H.alloc .rc { ctor, fields := vs }).2 external
            ((H.alloc .rc { ctor, fields := vs }).1 :: (owned₁ ++ slotVals')) := by
          have hb := Gen.balance_idle.mp hreadyOut.idle.balance
          intro k; have h1 := hb k
          simp only [holdRoots, refsIn_append, refsIn] at h1 ⊢; omega
        have hsrOut : Own.Plain.SameRefs (owned' ++ slotVals')
            ((H.alloc .rc { ctor, fields := vs }).1 :: (owned₁ ++ slotVals')) :=
          sameRefs_of_balance state.counts hbalOut
        have hreadyFinal : Gen.AllocatorReady maxClass (H.alloc .rc { ctor, fields := vs }).2
            (placeFresh addresses H.size address) mem' (holdRoots external (owned' ++ slotVals'))
            context base bump' limit slots' lists' := by
          have heq : (fun k => holdRoots external (owned₁ ++ slotVals') k +
              refsIn k [(H.alloc .rc { ctor, fields := vs }).1]) =
              holdRoots external (owned' ++ slotVals') := by
            funext k; have h1 := hsrOut k
            simp only [holdRoots, refsIn_append, refsIn] at h1 ⊢; omega
          rwa [← heq]
        have htrace : Sem.Star (Lir.semStep lp)
            { mem := memory, ctx := context, stack := target :: callers } 2
            { mem := mem', ctx := context,
              stack := { target with pos := target.pos + 1, env := target.env.insert x address, dsts := [] } :: callers } := by
          simpa [cont] using (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans hwrapTrace
        have hbounds' : Own.Plain.EnvBounded (H.alloc .rc { ctor, fields := vs }).2.size
            (source.env.insert x (H.alloc .rc { ctor, fields := vs }).1) :=
          envBounded_insert (before.frame.bounded.mono (by simp [Own.Heap.alloc, Own.Heap.size]))
            (by simp [Own.Plain.Bounded, Own.Heap.alloc, Own.Heap.size])
        have afterLayout : At F P { source with rest := tail, env := source.env.insert x (H.alloc .rc { ctor, fields := vs }).1 }
            (ownedEnv.insert x (H.alloc .rc { ctor, fields := vs }).1) ownedJoins k (rslots.erase s) := by
          refine ⟨fd, scope, params, ins :: acc, nextB, first, x + 1, slotBase,
            lookup, range, layout, rfl, Cfg.Proof.Sub.insert sub x _, ?_, vb.1,
            (slotSub.erase s).insert_var vb.1 _, scopedNames.2, vb.2, rc.2, ?_⟩
          · intro y u hy
            by_cases eq : y = x
            · subst y; exact Nat.lt_succ_self x
            · rw [Src.NatMap.get?_insert_ne _ _ eq] at hy
              exact Nat.lt_of_lt_of_le (below y u hy) (by omega)
          · apply (joins.agree ?_).mono (show lo ≤ x + 1 by omega)
            intro y hy; exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)
        have heap' : HeapState P pairs (H.alloc .rc { ctor, fields := vs }).2
            (placeFresh addresses H.size address) mem' external (owned' ++ slotVals')
            context base bump' limit regionBytes slots' lists' :=
          ⟨hreadyFinal, heapOk_alloc heap.ordered hbodyOk, heap.compatible.alloc hbodyCtorOk, heap.extent⟩
        have activation : Activation F P pairs lp (H.alloc .rc { ctor, fields := vs }).2
            (placeFresh addresses H.size address) external (live ++ [x]) Γ' Δ
            (sourceEnv.insert x (.ctor ctor logical))
            (ownedEnv.insert x (H.alloc .rc { ctor, fields := vs }).1)
            owned' lex sourceJoins ownedJoins k (funcFirst bodies source.fn sourceFunction) function
            { source with rest := tail, env := source.env.insert x (H.alloc .rc { ctor, fields := vs }).1 }
            { target with pos := target.pos + 1, env := target.env.insert x address, dsts := [] }
            borrows uniqs retUniq priv (rslots.erase s) slotVals' :=
          ⟨state, typed, afterLayout,
            ⟨before.frame.lookup, continuation.withEnvs _ _ [],
              before.frame.words.publish xReal before.frame.bounded address, hbounds',
              before.frame.compatible.bind x (by show ValueCtorOk (tablesOf P pairs) (.loc H.size); trivial)⟩,
            bodyScope, rfl, consumed_call_done before.frame.lookup before.frame.cursor head consuming _⟩
        have history := HeapHistory.allocate H { ctor, fields := vs } addresses address
        exact ResultAt.prefix htrace hreach hpriv history (by omega)
          (next _ (placeFresh addresses H.size address) external retUniq priv (rslots.erase s) slotVals'
            (live ++ [x]) Γ' Δ (sourceEnv.insert x (.ctor ctor logical))
            (ownedEnv.insert x (H.alloc .rc { ctor, fields := vs }).1) owned' lex ownedJoins
            sourceFunction function
            { source with rest := tail, env := source.env.insert x (H.alloc .rc { ctor, fields := vs }).1 }
            { target with pos := target.pos + 1, env := target.env.insert x address, dsts := [] }
            mem' context base bump' limit regionBytes slots' lists' callers sourceLookup activation heap')
      · -- Fallback allocation ran out of heap.
        exact ResultAt.of_fails (fails_prefix_res (Sem.Star.single (Lir.semStep_next.mpr hcall))
          (reaches_resource_fails hfail))
    · -- In-place reuse on unique live shell `.loc l` (`uniq = true` or `uniq = false`).
      have hclsB : Gen.classOf b.ctor = cls := (validReuseCtor_full hvcb).2.2.2.2.2.2.2.2.2.2.1
      have hbfZero : ∀ j, refsIn j b.fields = 0 := by
        intro j; rw [hbfErased]
        induction b.ctor.arity with
        | zero => rfl
        | succ m ih => simp [List.replicate, refsIn, ih]
      have hsrReady : Own.Plain.SameRefs (roots ++ slotVals) (.loc l :: (vs ++ (owned₁ ++ slotVals'))) := by
        intro j; have h1 := hrefsOwned j; have h2 := hsrSlots j
        simp only [refsIn_append, refsIn] at h1 h2 ⊢; omega
      have hreadySplit : Gen.AllocatorReady maxClass H addresses memory
          (fun j => external j + refsIn j (.loc l :: (vs ++ (owned₁ ++ slotVals'))))
          context base bump limit slots lists := by
        have heq : holdRoots external (roots ++ slotVals) =
            fun j => external j + refsIn j (.loc l :: (vs ++ (owned₁ ++ slotVals'))) := by
          funext j; have h1 := hsrReady j; simp only [holdRoots] at h1 ⊢; omega
        rw [← heq]; exact heap.ready
      obtain ⟨H₁, slots', hrc, hreadyOut, hwrapTrace⟩ :=
        reuse_wrapper_inplace_exec hcalleeFn hreadySplit hcl hsvRel hbfZero hvc hclsB hvlen
          hwrap0 hwrapArgs hargVals cont callers rfl
      have hnotfl : ctor.fieldless = false := by simp [Fir.CtorInfo.fieldless]; omega
      have hevEq : v = .loc H.size ∧ H' = H₁ := by
        simp only [Own.Plain.evalReuseVal, ownArgs, hnotfl, Bool.not_false, hvlen,
          decide_true, Bool.and_self, ↓reduceIte, hrc, Sem.Result.ofOption,
          Sem.Result.ok.injEq, Prod.mk.injEq] at hev
        exact ⟨hev.1.symm, hev.2.symm⟩
      obtain ⟨rfl, rfl⟩ := hevEq
      have hbalOut : Balance H' external (.loc H.size :: (owned₁ ++ slotVals')) :=
        Gen.balance_idle.mp hreadyOut.idle.balance
      have hsrOut : Own.Plain.SameRefs (owned' ++ slotVals') (.loc H.size :: (owned₁ ++ slotVals')) :=
        sameRefs_of_balance state.counts hbalOut
      have hreadyFinal : Gen.AllocatorReady maxClass H' (placeFresh addresses H.size (words[0]'(by omega)))
          (Gen.writeCell memory addresses (words[0]'(by omega)) { ctor, fields := vs } cls)
          (holdRoots external (owned' ++ slotVals')) context base bump limit slots' lists := by
        rw [holdRoots_sameRefs hsrOut]; exact hreadyOut
      have htrace : Sem.Star (Lir.semStep lp)
          { mem := memory, ctx := context, stack := target :: callers } 1
          { mem := Gen.writeCell memory addresses (words[0]'(by omega)) { ctor, fields := vs } cls,
            ctx := context,
            stack := { target with pos := target.pos + 1, env := target.env.insert x (words[0]'(by omega)), dsts := [] } :: callers } := by
        simpa [cont] using (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans hwrapTrace
      obtain ⟨hsize', history⟩ := heapHistory_reuseCell hcl hrc addresses (words[0]'(by omega))
      obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hrc
      have hlLt : l < H.size := Own.Proof.cell?_some hcl
      have hbounds' : Own.Plain.EnvBounded (reusedHeap H l { ctor, fields := vs }).size
          (source.env.insert x (.loc H.size)) :=
        envBounded_insert (before.frame.bounded.mono (by omega))
          (by show H.size < (reusedHeap H l { ctor, fields := vs }).size; omega)
      have afterLayout : At F P { source with rest := tail, env := source.env.insert x (.loc H.size) }
          (ownedEnv.insert x (.loc H.size)) ownedJoins k (rslots.erase s) := by
        refine ⟨fd, scope, params, ins :: acc, nextB, first, x + 1, slotBase,
          lookup, range, layout, rfl, Cfg.Proof.Sub.insert sub x _, ?_, vb.1,
          (slotSub.erase s).insert_var vb.1 _, scopedNames.2, vb.2, rc.2, ?_⟩
        · intro y u hy
          by_cases eq : y = x
          · subst y; exact Nat.lt_succ_self x
          · rw [Src.NatMap.get?_insert_ne _ _ eq] at hy
            exact Nat.lt_of_lt_of_le (below y u hy) (by omega)
        · apply (joins.agree ?_).mono (show lo ≤ x + 1 by omega)
          intro y hy; exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)
      have heap' : HeapState P pairs (reusedHeap H l { ctor, fields := vs })
          (placeFresh addresses H.size (words[0]'(by omega)))
          (Gen.writeCell memory addresses (words[0]'(by omega)) { ctor, fields := vs } cls)
          external (owned' ++ slotVals') context base bump limit regionBytes slots' lists :=
        ⟨hreadyFinal, heapOk_reuseCell heap.ordered hlLt hbodyOk,
          heapCtorOk_reuseCell heap.compatible hlLt hbodyCtorOk, heap.extent⟩
      have activation : Activation F P pairs lp (reusedHeap H l { ctor, fields := vs })
          (placeFresh addresses H.size (words[0]'(by omega))) external (live ++ [x]) Γ' Δ
          (sourceEnv.insert x (.ctor ctor logical)) (ownedEnv.insert x (.loc H.size))
          owned' lex sourceJoins ownedJoins k (funcFirst bodies source.fn sourceFunction) function
          { source with rest := tail, env := source.env.insert x (.loc H.size) }
          { target with pos := target.pos + 1, env := target.env.insert x (words[0]'(by omega)), dsts := [] }
          borrows uniqs retUniq priv (rslots.erase s) slotVals' :=
        ⟨state, typed, afterLayout,
          ⟨before.frame.lookup, continuation.withEnvs _ _ [],
            before.frame.words.publish xReal before.frame.bounded (words[0]'(by omega)), hbounds',
            before.frame.compatible.bind x (by show ValueCtorOk (tablesOf P pairs) (.loc H.size); trivial)⟩,
          bodyScope, rfl, consumed_call_done before.frame.lookup before.frame.cursor head consuming _⟩
      exact ResultAt.prefix htrace hreach hpriv history (by omega)
        (next _ (placeFresh addresses H.size (words[0]'(by omega))) external retUniq priv
          (rslots.erase s) slotVals' (live ++ [x]) Γ' Δ (sourceEnv.insert x (.ctor ctor logical))
          (ownedEnv.insert x (.loc H.size)) owned' lex ownedJoins sourceFunction function
          { source with rest := tail, env := source.env.insert x (.loc H.size) }
          { target with pos := target.pos + 1, env := target.env.insert x (words[0]'(by omega)), dsts := [] }
          (Gen.writeCell memory addresses (words[0]'(by omega)) { ctor, fields := vs } cls)
          context base bump limit regionBytes slots' lists callers sourceLookup activation heap')
  · have same : Lir.atState memory context target.fn target.label target.pos target.env callers =
        ({ mem := memory, ctx := context, stack := target :: callers } : Lir.State) := by
      have hr := before.running; cases target; simp_all [Lir.atState]
    rw [same] at failure
    exact ResultAt.of_fails failure

/-! ## `physical_reset` -/

/-- **Reset a scrutinee into a slot** (`.reset s x ctor fields uniq k`): executes `mkResetUWrapper`
(`uniq = true`) or `mkResetWrapper` (`uniq = false`, unique / shared / immediate paths),
matching `Own.Plain.reset_step`. -/
theorem physical_reset (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {s : Nat} {x : Fir.Var} {ctor : Fir.CtorInfo} {fields : List (Option Fir.Var)} {uniq : Bool}
    {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.reset s x ctor fields uniq k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  obtain ⟨Γ', hreset, typed⟩ := Own.Plain.checkCode_reset before.typed
  obtain ⟨hct, hnz, hns, cls, hvc, hsfree, hco, hfl, hnimm, huq, Γ₁, Γ₂, ht, hprom, hΓ'eq⟩ :=
    reset_inv hreset
  obtain ⟨hpos, h61, hmaxF, htag, hnsc, hnobj, hfk, _, _, hclsLay, _, _⟩ := validReuseCtor_full hvc
  obtain ⟨sv, H', owned', slotVals', hev, state, hreach, hpriv⟩ :=
    Own.Plain.reset_step before.owned hreset
  -- Scrutinee `vx` and owned-root split from `Γ.take x`.
  obtain ⟨vx, _, owned₁, hvx, _, _, _, hrefsX, _⟩ := Own.Plain.take_sem before.owned.takeInv ht
  -- Unpack `before.layout`.
  obtain ⟨fd, scope, params, acc, nextB, first, lo, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before.layout
  simp only [reuseCtorsOk, Bool.and_eq_true, decide_eq_true_eq] at rc
  let ci := heapCtorIndex F.ctors ctor.key
  let mask := Own.Plain.fieldsMask fields
  let ins := resetMarker P.base.size (slotBase + s) x ci mask uniq
  let tail := Cfg.Proof.spine (skeleton P.base.size first k F.ctors slotBase)
  have head : source.rest = ins :: tail := cursor
  have slotReal : slotBase + s < funcFirst bodies source.fn sourceFunction := by
    obtain ⟨_, blockLookup⟩ := Cfg.Proof.impl_head layout
    have hfb := checked_source_bounds admission.scopedProgram range sourceLookup lookup
    have heach := (functionBounds_block hfb blockLookup).2.1
    have hmem : ins ∈ acc.reverse ++ Cfg.Proof.spine
        (skeleton P.base.size first (.reset s x ctor fields uniq k) F.ctors slotBase) := by
      simp [ins, ci, mask, resetMarker, skeleton, Cfg.Proof.spine]
    have hbd := List.all_eq_true.mp heach _ hmem
    have hnr : reserved P.base.size ins = false := by simp [ins, resetMarker, reserved]
    have hir : isReuseOp P.base.size ins = true := by simp [ins, resetMarker, isReuseOp]
    have hdr : decodeReset P.base.size ins = some (slotBase + s, x, ci, mask, uniq) := by
      cases uniq <;> simp [ins, resetMarker, decodeReset]
    have hdu : decodeReuse P.base.size ins = none := by simp [ins, resetMarker, decodeReuse]
    simp only [instrBound, hnr, hir, hdr, hdu, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq] at hbd
    exact hbd.1
  -- Invert `consume` on the reset marker and obtain runtime wrapper lookups.
  obtain ⟨row, hrow, htagRow, harityRow⟩ := layout_ctor_at_index admission.scopedProgram hct hpos
  let callee := if uniq then (layoutOf P).resetUWrapper ci else (layoutOf P).resetWrapper ci
  have consuming : consume P (layoutOf P) ins =
      .ok (.bind (slotBase + s) (.fir (.call callee [.var x, .lit (.nat mask)]))) :=
    consume_reset_of hrow (by omega) (by omega)
  have liveX : ¬ Rt.Proof.Fused (tablesOf P pairs) function x :=
    consumed_call_live before.frame.cursor head consuming before.frame.lookup (.var x) (by simp) x rfl
  obtain ⟨vxWord, hvxWord, hregX⟩ := before.frame.words.word (sub x vx hvx) liveX
  have hmaskLt : mask < 2 ^ 61 :=
    Nat.lt_of_lt_of_le (fieldsMask_lt fields) (Nat.pow_le_pow_right (by omega) (by omega))
  have hmaskNat := natWord_fieldsMask (fs := fields) (by omega)
  -- Helper for building the post-reset `At` layout for any slot value `sv`.
  have mkAfterLayout : ∀ sv',
      At F P { source with rest := tail, env := source.env.insert (slotBase + s) sv' }
        ownedEnv ownedJoins k (rslots.insert s sv') := by
    intro sv'
    refine ⟨fd, scope, params, ins :: acc, nextB, first, lo, slotBase,
      lookup, range, layout, rfl, ?_, below, loSlot, slotSub.insert_slot s sv',
      scopedNames, vb, rc.2, ?_⟩
    · intro y u hy
      have hlt := below y u hy
      rw [Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ slotBase + s)]
      exact sub y u hy
    · apply joins.agree
      intro y hy; exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ slotBase + s)
  -- Runtime lookups in `lp`.
  let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
  have hisULookup := source_stage_isUnique_runtime P (Public.Spec.rawSource config P pairs) main
  obtain ⟨_, hincLookup⟩ := source_stage_increment_runtime P (Public.Spec.rawSource config P pairs) main
  obtain ⟨_, hdecLookup⟩ := source_stage_decrement_runtime P (Public.Spec.rawSource config P pairs) main
  obtain ⟨hresetWrap, hresetUWrap⟩ :=
    source_stage_reset_runtime P (Public.Spec.rawSource config P pairs) main ci hrow
      (by rw [harityRow, htagRow]; exact hclsLay)
  rw [harityRow, htagRow] at hresetWrap hresetUWrap
  have hcalleeFn : lp.funcs[callee]? = some (if uniq
      then mkResetUWrapper (layoutOf P).decProc (CellLayout.ofFields ctor.arity ctor.tag) cls
      else mkResetWrapper (layoutOf P).isUniqueProc (layoutOf P).incProc (layoutOf P).decProc
        (CellLayout.ofFields ctor.arity ctor.tag) cls) := by
    cases uniq <;> simpa [callee] using (by first | exact hresetUWrap | exact hresetWrap)
  -- Execute the LIR call into `callee`.
  rcases before.frame.cursor.call head consuming memory context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookupLir,
      position, statement, continuation⟩ := success
    have hop : Rt.Lower.operands source.fn [.var x, .lit (.nat mask)] =
        .ok (some [.v x, .imm (UInt64.ofNat (2 * mask + 1))]) := by
      simp only [Rt.Lower.operands, Rt.Lower.operand, mask, hmaskNat, Option.map_some,
        pure, Except.pure, bind, Except.bind]
    rw [hop] at lowered
    cases lowered
    let wrapEnv : Lir.Env := (({} : Lir.Env).insert 0 vxWord).insert 1 (UInt64.ofNat (2 * mask + 1))
    have henter : Lir.enter lp callee [vxWord, UInt64.ofNat (2 * mask + 1)] =
        some { fn := callee, label := 0, pos := 0, env := wrapEnv } := by
      cases uniq <;>
        simp [Lir.enter, hcalleeFn, mkResetUWrapper, mkResetWrapper, Lir.bindParams, wrapEnv]
    let cont : Lir.Frame := { target with pos := target.pos + 1, dsts := [slotBase + s] }
    have hcall := Lir.step_call (p := lp) (mem := memory) (ctx := context) (rest := callers)
      (fr := target) functionLookup blockLookupLir position statement
      (vs := [vxWord, UInt64.ofNat (2 * mask + 1)])
      (by simp [Lir.evalArgs, Lir.Arg.eval, hregX]) henter
    have hwrap0 : wrapEnv[0]? = some vxWord := by
      rw [Lir.env_insert_ne _ _ (by omega)]; exact Lir.env_insert_self ..
    have hwrap1 : wrapEnv[1]? = some (UInt64.ofNat (2 * mask + 1)) := Lir.env_insert_self ..
    have hsrStart : Own.Plain.SameRefs (roots ++ slotVals) (vx :: (owned₁ ++ slotVals)) := by
      intro k; have h1 := hrefsX k; simp only [refsIn_append, refsIn] at h1 ⊢; omega
    have hreadyStart : Gen.AllocatorReady maxClass H addresses memory
        (holdRoots external (vx :: (owned₁ ++ slotVals))) context base bump limit slots lists := by
      rw [← holdRoots_sameRefs hsrStart]; exact heap.ready
    have hnotfl : ctor.fieldless = false := by simp [Fir.CtorInfo.fieldless]; omega
    -- Shared immediate handler for `.lit`, `.ctor0`, `.erased`.
    have finishImm : (∀ l, vx ≠ .loc l) →
        ResultAt P pairs lp H addresses external context base limit regionBytes clock
          { mem := memory, ctx := context, stack := target :: callers } callers
          (Fir.eval F clock sourceEnv sourceJoins (Own.Plain.eraseCode (.reset s x ctor fields uniq k)))
          F.ctors retUniq priv := by
      intro himm
      have hevParts : uniq = false ∧ mask = 0 ∧ sv = .erased ∧ H' = H := by
        cases hvxCases : vx with
        | loc l => exact absurd hvxCases (himm l)
        | lit _ | ctor0 _ | erased =>
          subst hvxCases
          simp only [Own.Plain.evalResetMask, hnotfl, Bool.false_eq_true, ↓reduceIte, hvx] at hev
          change (if uniq || (mask != 0) then Sem.Result.stuck else Sem.Result.ok (.erased, H)) =
            Sem.Result.ok (sv, H') at hev
          cases hu : uniq with
          | true => simp [hu] at hev
          | false =>
            cases hm : (mask != 0) with
            | true => simp [hu, hm] at hev
            | false =>
              simp only [hu, hm, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
                Sem.Result.ok.injEq, Prod.mk.injEq] at hev
              have hm0 : mask = 0 := by simpa [bne] using hm
              exact ⟨rfl, hm0, hev.1.symm, hev.2.symm⟩
      obtain ⟨huqF, hmask0, hsvE, hHEq⟩ := hevParts
      subst huqF; subst hsvE; subst H'
      simp only [Bool.false_eq_true, ↓reduceIte] at hcalleeFn
      have hwrap1' : wrapEnv[1]? = some 1 := by simpa [hmask0] using hwrap1
      obtain ⟨mem', slots', lists', costW, hreadyOut, hwrapTrace⟩ :=
        reset_wrapper_imm_exec hcalleeFn hisULookup hdecLookup hvc hreadyStart himm hvxWord
          hwrap0 hwrap1' cont callers rfl
      have hsrOut := sameRefs_of_balance state.counts (Gen.balance_idle.mp hreadyOut.idle.balance)
      have hreadyFinal : Gen.AllocatorReady maxClass H addresses mem'
          (holdRoots external (owned' ++ slotVals')) context base bump limit slots' lists' := by
        rw [holdRoots_sameRefs hsrOut]; exact hreadyOut
      have htrace : Sem.Star (Lir.semStep lp)
          { mem := memory, ctx := context, stack := target :: callers } (1 + costW)
          { mem := mem', ctx := context,
            stack := { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] } :: callers } := by
        simpa [cont] using (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans hwrapTrace
      have heap' : HeapState P pairs H addresses mem' external (owned' ++ slotVals')
          context base bump limit regionBytes slots' lists' :=
        ⟨hreadyFinal, heap.ordered, heap.compatible, heap.extent⟩
      have activation : Activation F P pairs lp H addresses external live Γ' Δ
          sourceEnv ownedEnv owned' lex sourceJoins ownedJoins k
          (funcFirst bodies source.fn sourceFunction) function
          { source with rest := tail, env := source.env.insert (slotBase + s) .erased }
          { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] }
          borrows uniqs retUniq priv (rslots.insert s .erased) slotVals' :=
        ⟨state, typed, mkAfterLayout .erased,
          ⟨before.frame.lookup, continuation.withEnvs _ _ [],
            before.frame.words.bind slotReal (show valueWord addresses .erased = some 1 from rfl),
            envBounded_insert before.frame.bounded (show Own.Plain.Bounded H.size .erased from trivial),
            before.frame.compatible.bind (slotBase + s) trivial⟩,
          before.scope, rfl, consumed_call_done before.frame.lookup before.frame.cursor head consuming _⟩
      exact ResultAt.prefix htrace hreach hpriv (HeapHistory.refl H.size addresses) (by omega)
        (next H addresses external retUniq priv (rslots.insert s .erased) slotVals'
          live Γ' Δ sourceEnv ownedEnv owned' lex ownedJoins sourceFunction function
          { source with rest := tail, env := source.env.insert (slotBase + s) .erased }
          { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] }
          mem' context base bump limit regionBytes slots' lists' callers sourceLookup activation heap')
    -- Split on `vx` (`loc l` unique / shared vs immediate).
    cases vx with
    | loc l =>
      have havailX : Γ.avail x = true := by
        rcases Own.Plain.Ctx.take_ok ht with ⟨hi, _⟩ | ⟨_, m, hm, _⟩
        · simp [Own.Plain.Ctx.avail_eq, hi]
        · simp [Own.Plain.Ctx.avail_eq, Own.Plain.Ctx.tokens_eq, hm]
      obtain ⟨vx', _, hvx', hac⟩ := before.owned.ctorOfOk x ctor.key havailX hco
      have hvxEq : vx' = .loc l := Option.some.inj (hvx'.symm.trans hvx)
      subst hvxEq
      cases hcl : H.cell? l with
      | none => simp [RVal.asCtor, hcl] at hac
      | some c =>
        cases c with
        | dead => simp [RVal.asCtor, hcl] at hac
        | live rcCell mode b =>
          obtain ⟨hmDyn, _, _, _⟩ := heap.ready.idle.live.cell l rcCell mode b hcl
          subst hmDyn
          -- Derive `b.ctor = ctor` from `heap.compatible` + `hct`!
          have hbkey : b.ctor.key = ctor.key := by
            simp only [RVal.asCtor, hcl, Option.some.injEq, Prod.mk.injEq] at hac
            exact hac.1
          have hbctor : b.ctor = ctor := by
            have hbc := (heap.compatible l rcCell .dyn b hcl).1.table
            have hctors : P.base.ctors = F.ctors :=
              generate_ctors (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
            simp only [tablesOf, Rt.Lower.tables, consumed, hctors, hbkey] at hbc
            exact Option.some.inj (hbc.symm.trans hct)
          by_cases hrc1 : rcCell = 1
          · -- Unique in-place shell reset (`rc = 1, mode = .dyn`).
            subst hrc1
            obtain ⟨H₁, H₂, mem', slots', lists', costW, hrc, hda, hreadyOut, hwrapTrace⟩ :=
              reset_wrapper_unique_exec hcalleeFn hisULookup hdecLookup hvc hmaskLt
                hreadyStart hcl hvxWord hbctor hwrap0 hwrap1 cont callers rfl
            have hevEq : sv = .loc H.size ∧ H' = H₂ := by
              simp only [Own.Plain.evalResetMask, hnotfl, Bool.false_eq_true, ↓reduceIte, hvx, hcl,
                hrc] at hev
              have hda' : dropAll H₁ (b.fields.zipIdx.filterMap fun (u, j) =>
                  if !Nat.testBit (Own.Plain.fieldsMask fields) j then some u else none) = some H₂ := hda
              simp only [hda', Option.map_some, Sem.Result.ofOption, Sem.Result.ok.injEq,
                Prod.mk.injEq] at hev
              exact ⟨hev.1.symm, hev.2.symm⟩
            obtain ⟨hsvEq, hH'Eq⟩ := hevEq
            subst hsvEq; subst H'
            have hbalOut : Balance H₂ external (.loc H.size ::
                ((b.fields.zipIdx.filterMap fun (u, j) => if Nat.testBit mask j then some u else none) ++
                  (owned₁ ++ slotVals))) :=
              Gen.balance_idle.mp hreadyOut.idle.balance
            have hsrOut := sameRefs_of_balance state.counts hbalOut
            have hreadyFinal : Gen.AllocatorReady maxClass H₂ (placeFresh addresses H.size vxWord) mem'
                (holdRoots external (owned' ++ slotVals')) context base bump limit slots' lists' := by
              rw [holdRoots_sameRefs hsrOut]; exact hreadyOut
            have htrace : Sem.Star (Lir.semStep lp)
                { mem := memory, ctx := context, stack := target :: callers } (1 + costW)
                { mem := mem', ctx := context,
                  stack := { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) vxWord, dsts := [] } :: callers } := by
              simpa [cont] using (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans hwrapTrace
            -- Heap invariants (`HeapOk`, `HeapCtorOk`, `HeapHistory`, `EnvBounded`).
            have hlLt : l < H.size := Own.Proof.cell?_some hcl
            have hshellOk : BodyOk H.size (Own.Plain.resetShell ctor) := by
              refine ⟨by simp [Own.Plain.resetShell], hpos, fun _ hm => ?_⟩
              simp [Own.Plain.resetShell] at hm
            have hshellCtorOk : BodyCtorOk (tablesOf P pairs) (Own.Plain.resetShell ctor) := by
              refine ⟨ctorOk_of_validReuse admission.scopedProgram hct hnz hns hvc,
                hnotfl, fun u hu => ?_⟩
              simp only [Own.Plain.resetShell, List.mem_replicate] at hu
              rw [hu.2]; trivial
            obtain ⟨hsize1, history1⟩ := heapHistory_reuseCell hcl hrc addresses vxWord
            obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hrc
            have hsize2 : H₂.size = H.size + 1 :=
              (dropAll_size (reusedHeap H l (Own.Plain.resetShell ctor)) _ hda).trans hsize1
            have history : HeapHistory H.size addresses H₂.size (placeFresh addresses H.size vxWord) :=
              ⟨by omega, history1.retained⟩
            have hbal1 : Balance (reusedHeap H l (Own.Plain.resetShell ctor))
                (holdRoots external (.loc H.size ::
                  ((b.fields.zipIdx.filterMap fun (u, j) => if Nat.testBit mask j then some u else none) ++
                    (owned₁ ++ slotVals))))
                (b.fields.zipIdx.filterMap fun (u, j) => if !Nat.testBit mask j then some u else none) := by
              apply balance_hold.mp
              obtain ⟨H₁', hrc', hrb⟩ := Own.Rc.reuseCell_balance (b' := Own.Plain.resetShell ctor)
                (kept := b.fields ++ (owned₁ ++ slotVals)) hcl (hsrStart.balance before.owned.counts) (by
                  intro k
                  have hrep : ∀ n, refsIn k (List.replicate n RVal.erased) = 0 := fun n => by
                    induction n with
                    | zero => rfl
                    | succ m ih => simp [List.replicate, refsIn, ih]
                  simp only [Own.Plain.resetShell, refsIn_append, hrep, Nat.zero_add])
              obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hrc'
              refine Own.Plain.SameRefs.balance ?_ hrb
              intro k
              have hpart := Own.Plain.refsIn_zipIdx_partition mask b.fields 0 k
              simp only [refsIn_append, refsIn] at hpart ⊢; omega
            have hok2 : HeapOk H₂ := by
              have hok1 := heapOk_reuseCell heap.ordered hlLt hshellOk
              obtain ⟨H₃, hda₃, _, hok₃⟩ := dropAll_heapOk _ _ hbal1 hok1
              rw [hda] at hda₃; cases hda₃; exact hok₃
            have hcok2 : HeapCtorOk (tablesOf P pairs) H₂ :=
              (heapCtorOk_reuseCell heap.compatible hlLt hshellCtorOk).dropAll _ _ hda
            have hbounds' : Own.Plain.EnvBounded H₂.size (source.env.insert (slotBase + s) (.loc H.size)) :=
              envBounded_insert (before.frame.bounded.mono (by omega)) (by show H.size < H₂.size; omega)
            have heap' : HeapState P pairs H₂ (placeFresh addresses H.size vxWord) mem' external
                (owned' ++ slotVals') context base bump limit regionBytes slots' lists' :=
              ⟨hreadyFinal, hok2, hcok2, heap.extent⟩
            have activation : Activation F P pairs lp H₂ (placeFresh addresses H.size vxWord) external
                live Γ' Δ sourceEnv ownedEnv owned' lex sourceJoins ownedJoins k
                (funcFirst bodies source.fn sourceFunction) function
                { source with rest := tail, env := source.env.insert (slotBase + s) (.loc H.size) }
                { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) vxWord, dsts := [] }
                borrows uniqs retUniq priv (rslots.insert s (.loc H.size)) slotVals' :=
              ⟨state, typed, mkAfterLayout (.loc H.size),
                ⟨before.frame.lookup, continuation.withEnvs _ _ [],
                  before.frame.words.publish slotReal before.frame.bounded vxWord, hbounds',
                  before.frame.compatible.bind (slotBase + s)
                    (by show ValueCtorOk (tablesOf P pairs) (.loc H.size); trivial)⟩,
                before.scope, rfl, consumed_call_done before.frame.lookup before.frame.cursor head consuming _⟩
            exact ResultAt.prefix htrace hreach hpriv history (by omega)
              (next H₂ (placeFresh addresses H.size vxWord) external retUniq priv
                (rslots.insert s (.loc H.size)) slotVals' live Γ' Δ sourceEnv ownedEnv owned'
                lex ownedJoins sourceFunction function
                { source with rest := tail, env := source.env.insert (slotBase + s) (.loc H.size) }
                { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) vxWord, dsts := [] }
                mem' context base bump limit regionBytes slots' lists' callers sourceLookup activation heap')
          · -- Shared live cell (`rc ≠ 1, mode = .dyn`, `uniq = false`).
            have huqF : uniq = false := by
              cases hu : uniq with
              | false => rfl
              | true =>
                cases rcCell with
                | zero => simp [Own.Plain.evalResetMask, hnotfl, hvx, hcl, hu] at hev
                | succ m =>
                  cases m with
                  | zero => exact absurd rfl hrc1
                  | succ _ => simp [Own.Plain.evalResetMask, hnotfl, hvx, hcl, hu] at hev
            subst huqF
            simp only [Bool.false_eq_true, ↓reduceIte] at hcalleeFn
            rcases reset_wrapper_shared_exec hcalleeFn hisULookup hincLookup hdecLookup hvc hmaskLt
                hreadyStart hcl hrc1 hvxWord hbctor hwrap0 hwrap1 cont callers rfl with
              ⟨H₁, H₂, mem', slots', lists', costW, hi, hda, hreadyOut, hwrapTrace⟩ | hfail
            · have hi' : Own.Plain.incList H (b.fields.zipIdx.filterMap fun (u, j) =>
                  if Nat.testBit (Own.Plain.fieldsMask fields) j then some u else none) = some H₁ := hi
              have hevEq : sv = .erased ∧ H' = H₂ := by
                cases rcCell with
                | zero =>
                  simp only [Own.Plain.evalResetMask, hnotfl, Bool.false_eq_true, ↓reduceIte, hvx, hcl,
                    hi', hda, Option.map_some, Sem.Result.ofOption, Sem.Result.ok.injEq, Prod.mk.injEq] at hev
                  exact ⟨hev.1.symm, hev.2.symm⟩
                | succ m =>
                  cases m with
                  | zero => exact absurd rfl hrc1
                  | succ _ =>
                    simp only [Own.Plain.evalResetMask, hnotfl, Bool.false_eq_true, ↓reduceIte, hvx, hcl,
                      hi', hda, Option.map_some, Sem.Result.ofOption, Sem.Result.ok.injEq, Prod.mk.injEq] at hev
                    exact ⟨hev.1.symm, hev.2.symm⟩
              obtain ⟨hsvEq, hH'Eq⟩ := hevEq
              subst hsvEq; subst H'
              have hbalOut : Balance H₂ external
                  ((b.fields.zipIdx.filterMap fun (u, j) => if Nat.testBit mask j then some u else none) ++
                    (owned₁ ++ slotVals)) :=
                Gen.balance_idle.mp hreadyOut.idle.balance
              have hsrOut := sameRefs_of_balance state.counts hbalOut
              have hreadyFinal : Gen.AllocatorReady maxClass H₂ addresses mem'
                  (holdRoots external (owned' ++ slotVals')) context base bump limit slots' lists' := by
                rw [holdRoots_sameRefs hsrOut]; exact hreadyOut
              have htrace : Sem.Star (Lir.semStep lp)
                  { mem := memory, ctx := context, stack := target :: callers } (1 + costW)
                  { mem := mem', ctx := context,
                    stack := { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] } :: callers } := by
                simpa [cont] using (Sem.Star.single (Lir.semStep_next.mpr hcall)).trans hwrapTrace
              have hsize2 : H₂.size = H.size :=
                (dropAll_size H₁ [.loc l] hda).trans (incList_size hi)
              have hbal1 : Balance H₁
                  (holdRoots external
                    ((b.fields.zipIdx.filterMap fun (u, j) => if Nat.testBit mask j then some u else none) ++
                      (owned₁ ++ slotVals))) [.loc l] := by
                apply balance_hold.mp
                have hliveBrw : ∀ u ∈ (b.fields.zipIdx.filterMap fun (u, j) =>
                    if Nat.testBit mask j then some u else none), Own.Plain.BorrowVal H u := by
                  intro u hu
                  have hmem : u ∈ b.fields := Own.Plain.zipIdx_filterMap_mem_fst (Nat.testBit mask) hu
                  exact Own.Plain.BorrowVal.asCtor_field (parent := .loc l)
                    (show RVal.asCtor F.known H (.loc l) = some (b.ctor.key, b.fields) by
                      simp [RVal.asCtor, hcl]) hmem
                obtain ⟨H₁', hi'', hb₁', _, _, _⟩ := Own.Plain.incList_sound (P := fun _ => False) _
                  before.owned.counts hliveBrw (fun _ h => False.elim h) (fun _ h => False.elim h)
                rw [hi] at hi''; cases hi''
                refine Own.Plain.SameRefs.balance ?_ hb₁'
                intro k; have h1 := hrefsX k
                simp only [List.cons_append, refsIn_append, refsIn] at h1 ⊢; omega
              have hok2 : HeapOk H₂ := by
                obtain ⟨H₃, hda₃, _, hok₃⟩ := dropAll_heapOk H₁ [.loc l] hbal1 (heapOk_incList heap.ordered hi)
                rw [hda] at hda₃; cases hda₃; exact hok₃
              have hcok2 : HeapCtorOk (tablesOf P pairs) H₂ :=
                (heapCtorOk_incList heap.compatible hi).dropAll H₁ [.loc l] hda
              have hbounds' : Own.Plain.EnvBounded H₂.size (source.env.insert (slotBase + s) .erased) :=
                envBounded_insert (before.frame.bounded.mono (by omega)) trivial
              have heap' : HeapState P pairs H₂ addresses mem' external (owned' ++ slotVals')
                  context base bump limit regionBytes slots' lists' :=
                ⟨hreadyFinal, hok2, hcok2, heap.extent⟩
              have activation : Activation F P pairs lp H₂ addresses external live Γ' Δ
                  sourceEnv ownedEnv owned' lex sourceJoins ownedJoins k
                  (funcFirst bodies source.fn sourceFunction) function
                  { source with rest := tail, env := source.env.insert (slotBase + s) .erased }
                  { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] }
                  borrows uniqs retUniq priv (rslots.insert s .erased) slotVals' :=
                ⟨state, typed, mkAfterLayout .erased,
                  ⟨before.frame.lookup, continuation.withEnvs _ _ [],
                    before.frame.words.bind slotReal (show valueWord addresses .erased = some 1 from rfl),
                    hbounds', before.frame.compatible.bind (slotBase + s) trivial⟩,
                  before.scope, rfl, consumed_call_done before.frame.lookup before.frame.cursor head consuming _⟩
              have history : HeapHistory H.size addresses H₂.size addresses :=
                ⟨by omega, fun _ _ => rfl⟩
              exact ResultAt.prefix htrace hreach hpriv history (by omega)
                (next H₂ addresses external retUniq priv (rslots.insert s .erased) slotVals'
                  live Γ' Δ sourceEnv ownedEnv owned' lex ownedJoins sourceFunction function
                  { source with rest := tail, env := source.env.insert (slotBase + s) .erased }
                  { target with pos := target.pos + 1, env := target.env.insert (slotBase + s) 1, dsts := [] }
                  mem' context base bump limit regionBytes slots' lists' callers sourceLookup activation heap')
            · exact ResultAt.of_fails (fails_prefix_res (Sem.Star.single (Lir.semStep_next.mpr hcall)) hfail)
    | lit _ => exact finishImm (fun _ h => by cases h)
    | ctor0 _ => exact finishImm (fun _ h => by cases h)
    | erased => exact finishImm (fun _ h => by cases h)
  · have same : Lir.atState memory context target.fn target.label target.pos target.env callers =
        ({ mem := memory, ctx := context, stack := target :: callers } : Lir.State) := by
      have hr := before.running; cases target; simp_all [Lir.atState]
    rw [same] at failure
    exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
