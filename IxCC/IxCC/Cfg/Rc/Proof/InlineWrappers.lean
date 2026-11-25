import IxCC.Cfg.Rc.InlineWrappers
import IxCC.Cfg.Rc.Proof.Inline

/-! # Semantic preservation of `Cfg.Rc.InlineWrappers`

Proves `inlineProgram_sim`: inlining `isUniqueProc`, `incProc`, `decProc`, and
`allocProc` fast paths inside surviving reuse/reset wrappers preserves exact
`Lir.eval` execution (`Sem.Sim Eq (fun k => k + 3 * Lir.fuelFor (inlineProgram l p) k)`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.InlineWrappers

open IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Inline (cellAddr ctxAddr relabelEdge relabelTerm freshBase AgreeBelow)
open IxCC.Rt.Rc.Procs (v to)

@[local simp] private theorem env_get?_insert_eq (e : Lir.Env) (k k' : Lir.VReg) (val : Lir.Word) :
    (e.insert k val)[k']? = if k = k' then some val else e[k']? := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h, Lir.env_insert_ne _ _ h]

@[local simp] private theorem env_get_insert_eq (e : Lir.Env) (k k' : Lir.VReg) (val : Lir.Word)
    (h : k' ∈ e.insert k val) :
    (e.insert k val)[k']'h =
      if heq : k = k' then val
      else e[k']'(by simpa [Std.HashMap.mem_insert, beq_iff_eq, heq] using h) := by
  by_cases heq : k = k'
  · subst heq; simp
  · simp [Std.HashMap.getElem_insert, beq_iff_eq, heq]

@[local simp] private theorem v_def (x : Lir.VReg) : Rt.Rc.Procs.v x = Lir.Arg.v x := rfl
@[local simp] private theorem i_def (n : Nat) : Rt.Rc.Procs.i n = Lir.Arg.imm (UInt64.ofNat n) := rfl
@[local simp] private theorem dispWord_0 : Lir.dispWord 0 = 0 := by decide
@[local simp] private theorem dispWord_1 : Lir.dispWord 1 = 1 := by decide
@[local simp] private theorem dispWord_4 : Lir.dispWord 4 = 4 := by decide
@[local simp] private theorem dispWord_8 : Lir.dispWord 8 = 8 := by decide
@[local simp] private theorem dispWord_16 : Lir.dispWord 16 = 16 := by decide

/-! ## Runtime procedure precondition -/

structure WrapperRuntime (l : Layout) (p : Lir.Program) : Prop where
  incProc : p.funcs[l.incProc]? = some Rt.Rc.Procs.inc
  decProc : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec
  isUniqueProc : p.funcs[l.isUniqueProc]? = some Rt.Rc.Gen.isUnique
  allocProc : ∀ i c, l.ctors[i]? = some c →
    p.funcs[l.allocProc i]? = some (Rt.Rc.Gen.alloc (Rt.Rc.CellLayout.ofFields c.arity c.tag))

/-! ## Basic program & lookup lemmas -/

theorem inlineProgram_main (l : Layout) (p : Lir.Program) : (inlineProgram l p).main = p.main := rfl

theorem inlineProgram_funcs_size (l : Layout) (p : Lir.Program) :
    (inlineProgram l p).funcs.size = p.funcs.size := by
  simp [inlineProgram]

theorem inlineProgram_get_not_prunable {l : Layout} {p : Lir.Program} {f : Lir.FunId}
    (hnp : Prune.isPrunableReuse l f = false) :
    (inlineProgram l p).funcs[f]? = p.funcs[f]? := by
  simp only [inlineProgram, Array.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => simp
  | some F => simp [hnp]

theorem inlineProgram_get_le {l : Layout} {p : Lir.Program} {f : Lir.FunId}
    (hle : f ≤ l.isUniqueProc) :
    (inlineProgram l p).funcs[f]? = p.funcs[f]? :=
  inlineProgram_get_not_prunable (by
    simp only [Prune.isPrunableReuse, decide_eq_false_iff_not]
    exact fun h => Nat.not_lt.mpr hle h.1)

theorem inlineProgram_get_prunable {l : Layout} {p : Lir.Program} {f : Lir.FunId}
    (hp : Prune.isPrunableReuse l f = true) :
    (inlineProgram l p).funcs[f]? = (p.funcs[f]?).map (inlineFunc l) := by
  simp only [inlineProgram, Array.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => simp
  | some F => simp [hp]

theorem inlineProgram_push {l : Layout} {p : Lir.Program} {F : Lir.Func}
    (hsize : l.init + 4 + 4 * l.ctors.length ≤ p.funcs.size) :
    inlineProgram l { p with funcs := p.funcs.push F } =
      { inlineProgram l p with funcs := (inlineProgram l p).funcs.push F } := by
  have hnp : Prune.isPrunableReuse l p.funcs.size = false := by
    simp [Prune.isPrunableReuse]; omega
  simp [inlineProgram, Array.mapIdx_push, hnp]

/-! ## Structural lemmas for `classify`, `findUniqueSite`, `expandBlock`, `expandBlocks` -/

theorem classify_isUnique {l : Layout} {s : Lir.Stmt} {dst x : Lir.VReg}
    (h : classify l s = some (.isUnique dst x)) :
    s = .call [dst] l.isUniqueProc [.v x] ∧ dst ≠ x := by
  unfold classify at h
  split at h
  · rename_i dst' g' x'
    split at h
    · rename_i hc
      simp only [Option.some.injEq, WrapperSite.isUnique.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
      exact ⟨by rw [hc.1], hc.2⟩
    · cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · split at h
    · dsimp only at h
      split at h
      · split at h
        · split at h <;> cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem classify_inc {l : Layout} {s : Lir.Stmt} {x : Lir.VReg}
    (h : classify l s = some (.inc x)) :
    s = .call [] l.incProc [.v x] := by
  unfold classify at h
  split at h
  · split at h <;> cases h
  · rename_i g' x'
    split at h
    · rename_i hc
      simp only [Option.some.injEq, WrapperSite.inc.injEq] at h
      subst h
      simp only [beq_iff_eq] at hc
      rw [hc]
    · split at h <;> cases h
  · split at h
    · dsimp only at h
      split at h
      · split at h
        · split at h <;> cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem classify_dec {l : Layout} {s : Lir.Stmt} {x : Lir.VReg}
    (h : classify l s = some (.dec x)) :
    s = .call [] l.decProc [.v x] := by
  unfold classify at h
  split at h
  · split at h <;> cases h
  · rename_i g' x'
    split at h
    · cases h
    · split at h
      · rename_i hc
        simp only [Option.some.injEq, WrapperSite.dec.injEq] at h
        subst h
        simp only [beq_iff_eq] at hc
        rw [hc]
      · cases h
  · split at h
    · dsimp only at h
      split at h
      · split at h
        · split at h <;> cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem classify_alloc {l : Layout} {s : Lir.Stmt} {dst : Lir.VReg} {idx : Nat}
    {lay : Rt.Rc.CellLayout} {cls : Nat}
    (h : classify l s = some (.alloc dst idx lay cls)) :
    ∃ c, l.ctors[idx]? = some c ∧
      lay = Rt.Rc.CellLayout.ofFields c.arity c.tag ∧
      lay.ok = true ∧ lay.cls? = some cls ∧
      s = .call [dst] (l.allocProc idx) [] := by
  unfold classify at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i dst' g'
    split at h
    · rename_i hrange
      dsimp only at h
      split at h
      · rename_i c hc
        split at h
        · rename_i hok
          split at h
          · rename_i cls' hcls
            simp only [Option.some.injEq, WrapperSite.alloc.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
            refine ⟨c, hc, rfl, hok, hcls, ?_⟩
            have hg : l.allocProc (g' - (l.incProc + 2)) = g' := by
              simp only [Layout.allocProc]; omega
            rw [hg]
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem findUniqueSite_spec {l : Layout} :
    ∀ {ss pre post : List Lir.Stmt} {site : WrapperSite},
      findUniqueSite l ss = some (pre, site, post) →
      ∃ s, ss = pre ++ s :: post ∧ classify l s = some site
  | [], _, _, _, h => by cases h
  | s :: rest, pre, post, site, h => by
    unfold findUniqueSite at h
    cases hc : classify l s with
    | some site' =>
      simp only [hc] at h
      split at h
      · cases h
        exact ⟨s, rfl, hc⟩
      · cases h
    | none =>
      simp only [hc] at h
      cases hf : findUniqueSite l rest with
      | none => simp [hf] at h
      | some triple =>
        rcases triple with ⟨pre', site', post'⟩
        simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨s0, hss, hc0⟩ := findUniqueSite_spec hf
        exact ⟨s0, by rw [hss]; rfl, hc0⟩

theorem expandSite_length (l : Layout) (rel : Lir.Label → Lir.Label) (b : Lir.Block)
    (cur nextTmp : Nat) (pre : List Lir.Stmt) (site : WrapperSite) (post : List Lir.Stmt) :
    (expandSite l rel b cur nextTmp pre site post).length = 1 + siteExtra site := by
  cases site <;> rfl

theorem expandBlock_length (l : Layout) (rel : Lir.Label → Lir.Label) (cur nextTmp : Nat)
    (b : Lir.Block) :
    (expandBlock l rel cur nextTmp b).length = 1 + blockExtra l b := by
  unfold expandBlock blockExtra
  cases h : findUniqueSite l b.body.toList with
  | none => rfl
  | some triple =>
    rcases triple with ⟨pre, site, post⟩
    exact expandSite_length l rel b cur nextTmp pre site post

theorem expandBlocks_length (l : Layout) (rel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (cur nextTmp : Nat),
      (expandBlocks l rel bs cur nextTmp).length =
        bs.length + (bs.map (blockExtra l)).sum
  | [], _, _ => rfl
  | b :: bs, cur, nextTmp => by
    simp only [expandBlocks, List.length_append, expandBlock_length,
      expandBlocks_length l rel bs, List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem expandBlocks_at (l : Layout) (rel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (cur nextTmp i : Nat) (B : Lir.Block),
      bs[i]? = some B →
      ∀ k, k < 1 + blockExtra l B →
        (expandBlocks l rel bs cur nextTmp)[i + ((bs.map (blockExtra l)).take i).sum + k]? =
          (expandBlock l rel (cur + (i + ((bs.map (blockExtra l)).take i).sum))
            (nextTmp + ((bs.map (blockTemps l)).take i).sum) B)[k]?
  | [], _, _, _, _, h => by cases h
  | b :: bs, cur, nextTmp, 0, B, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    intro k hk
    simp only [List.take_zero, List.sum_nil, Nat.add_zero, Nat.zero_add]
    rw [expandBlocks, List.getElem?_append_left (by rw [expandBlock_length]; exact hk)]
  | b :: bs, cur, nextTmp, i + 1, B, h => by
    simp only [List.getElem?_cons_succ] at h
    intro k hk
    have ih := expandBlocks_at l rel bs (cur + 1 + blockExtra l b) (nextTmp + blockTemps l b) i B h k hk
    have hlen : (expandBlock l rel cur nextTmp b).length = 1 + blockExtra l b :=
      expandBlock_length l rel cur nextTmp b
    simp only [expandBlocks, List.map_cons, List.take_succ_cons, List.sum_cons]
    have hge : (expandBlock l rel cur nextTmp b).length ≤
        i + 1 + (blockExtra l b + ((bs.map (blockExtra l)).take i).sum) + k := by
      omega
    rw [List.getElem?_append_right hge]
    have hidx : i + 1 + (blockExtra l b + ((bs.map (blockExtra l)).take i).sum) + k -
        (expandBlock l rel cur nextTmp b).length =
        i + ((bs.map (blockExtra l)).take i).sum + k := by omega
    rw [hidx]
    have hcur : cur + (i + 1 + (blockExtra l b + ((bs.map (blockExtra l)).take i).sum)) =
        cur + 1 + blockExtra l b + (i + ((bs.map (blockExtra l)).take i).sum) := by omega
    have htmp : nextTmp + (blockTemps l b + ((bs.map (blockTemps l)).take i).sum) =
        nextTmp + blockTemps l b + ((bs.map (blockTemps l)).take i).sum := by omega
    rw [hcur, htmp]
    exact ih

def blockTmpBase (l : Layout) (F : Lir.Func) (i : Nat) : Nat :=
  freshBase F + ((F.blocks.toList.map (blockTemps l)).take i).sum

theorem freshBase_le_blockTmpBase (l : Layout) (F : Lir.Func) (i : Nat) :
    freshBase F ≤ blockTmpBase l F i := by
  simp [blockTmpBase]

theorem inlineFunc_block_at (l : Layout) (F : Lir.Func) {i : Nat} {B : Lir.Block}
    (hB : F.blocks[i]? = some B) {k : Nat} (hk : k < 1 + blockExtra l B) :
    (inlineFunc l F).blocks[newLabel l F i + k]? =
      (expandBlock l (newLabel l F) (newLabel l F i) (blockTmpBase l F i) B)[k]? := by
  have hB' : F.blocks.toList[i]? = some B := by simpa using hB
  have h := expandBlocks_at l (newLabel l F) F.blocks.toList 0 (freshBase F) i B hB' k hk
  simp only [inlineFunc, List.getElem?_toArray]
  simpa [newLabel, blockTmpBase] using h

theorem newLabel_oob (l : Layout) (F : Lir.Func) {t : Nat} (ht : F.blocks.size ≤ t) :
    (inlineFunc l F).blocks[newLabel l F t]? = none := by
  apply Array.getElem?_eq_none
  simp only [inlineFunc, List.size_toArray, expandBlocks_length, Array.length_toList, newLabel]
  have htake : ((F.blocks.toList.map (blockExtra l)).take t).sum =
      (F.blocks.toList.map (blockExtra l)).sum := by
    rw [List.take_of_length_le (by simp; omega)]
  omega

theorem inlineFunc_entry_params (l : Layout) (F : Lir.Func) {i : Nat} {B : Lir.Block}
    (hB : F.blocks[i]? = some B) :
    ∃ B', (inlineFunc l F).blocks[newLabel l F i]? = some B' ∧ B'.params = B.params := by
  have h := inlineFunc_block_at l F hB (k := 0) (by omega)
  simp only [Nat.add_zero] at h
  rw [h]
  unfold expandBlock
  cases hf : findUniqueSite l B.body.toList with
  | none => exact ⟨_, rfl, rfl⟩
  | some triple =>
    rcases triple with ⟨pre, site, post⟩
    cases site <;> exact ⟨_, rfl, rfl⟩

/-! ## Arithmetic & step helpers -/

private theorem star_free {p : Lir.Program} {s s' s'' : Lir.State} {c : Nat}
    (h1 : Lir.step p s = .next s' false) (h2 : Sem.Star (Lir.semStep p) s' c s'') :
    Sem.Star (Lir.semStep p) s c s'' :=
  .free (Lir.semStep_next.mpr h1) h2

private theorem star_charge {p : Lir.Program} {s s' s'' : Lir.State} {c : Nat}
    (h1 : Lir.step p s = .next s' true) (h2 : Sem.Star (Lir.semStep p) s' c s'') :
    Sem.Star (Lir.semStep p) s (c + 1) s'' :=
  .charge (Lir.semStep_next.mpr h1) h2

private theorem star_reaches_stuck {p : Lir.Program} {s s' : Lir.State} {c : Nat}
    (hstar : Sem.Star (Lir.semStep p) s c s') (hst : Lir.step p s' = .stuck) :
    Sem.Reaches (Lir.semStep p) s c .stuck := by
  have := Inline.reaches_of_star_reaches hstar (.final (k := 0) (by rw [Lir.semStep, hst]; exact .stuck))
  simpa using this

private theorem star_reaches_fail {p : Lir.Program} {s s' : Lir.State} {c : Nat} {r : Sem.Resource}
    (hstar : Sem.Star (Lir.semStep p) s c s') (hf : Lir.step p s' = .fail r) :
    Sem.Reaches (Lir.semStep p) s c (.resource r) := by
  have := Inline.reaches_of_star_reaches hstar (.final (k := 0) (by rw [Lir.semStep, hf]; exact .fail))
  simpa using this

private theorem w64_trunc (x : Lir.Word) : X86.Width.w64.truncate x = x := by
  apply UInt64.toBitVec_inj.mp
  have hall : (X86.Width.w64.mask).toBitVec = BitVec.allOnes 64 := by decide
  rw [X86.Width.truncate, UInt64.toBitVec_and, hall, BitVec.and_allOnes]

private theorem w64_tnz_1 (x : Lir.Word) :
    Lir.Cond.holds .tnz .w64 x 1 = ((x &&& 1) != 0) := by
  simp [Lir.Cond.holds, w64_trunc]

private theorem w64_eq_iff (a b : Lir.Word) :
    Lir.Cond.holds .eq .w64 a b = (a == b) := by
  simp [Lir.Cond.holds, w64_trunc]

private theorem w64_ule_iff (a b : Lir.Word) :
    Lir.Cond.holds .ule .w64 a b = decide (a ≤ b) := by
  simp [Lir.Cond.holds, w64_trunc]

private theorem cond_ult_iff {val : Lir.Word} :
    Lir.Cond.holds .ult .w32 val (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true ↔
      (Lir.Cond.holds .slt .w32 val 0 = false ∧
       Lir.Cond.holds .eq .w32 val (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false) := by
  rw [Inline.w32_ult_maxMinus1, Inline.w32_signedValue_lt_zero, Inline.w32_eq_maxMinus1]
  have hlt := Inline.w32_truncate_lt val
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private theorem slt_zero_of_eq_zero {val : Lir.Word}
    (h : Lir.Cond.holds .eq .w32 val 0 = true) :
    Lir.Cond.holds .slt .w32 val 0 = false := by
  rw [Inline.w32_eq_zero] at h
  rw [Inline.w32_signedValue_lt_zero]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  omega

private theorem slt_zero_of_eq_max {val : Lir.Word}
    (h : Lir.Cond.holds .eq .w32 val (UInt64.ofNat (Rt.Rc.maxCount - 1)) = true) :
    Lir.Cond.holds .slt .w32 val 0 = false := by
  rw [Inline.w32_eq_maxMinus1] at h
  rw [Inline.w32_signedValue_lt_zero]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  omega

private theorem slt_zero_of_not_ult_not_eq {val : Lir.Word}
    (hu : Lir.Cond.holds .ult .w32 val (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false)
    (he : Lir.Cond.holds .eq .w32 val (UInt64.ofNat (Rt.Rc.maxCount - 1)) = false) :
    Lir.Cond.holds .slt .w32 val 0 = true := by
  rw [Inline.w32_ult_maxMinus1] at hu
  rw [Inline.w32_eq_maxMinus1] at he
  rw [Inline.w32_signedValue_lt_zero]
  have hlt := Inline.w32_truncate_lt val
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hu he ⊢
  omega

/-! ## Simulation relations -/

inductive FrameRel (l : Layout) (p : Lir.Program) : Lir.Frame → Lir.Frame → Prop
  | other {fr : Lir.Frame} (hnp : Prune.isPrunableReuse l fr.fn = false) :
      FrameRel l p fr fr
  | wrapInvalid {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts : List Lir.VReg} {e₁ e₂ : Lir.Env}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hnone : F.blocks[i]? = none) :
      FrameRel l p
        { fn, label := i, pos, dsts, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts, env := e₂ }
  | wrapUnexpanded {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hnone : findUniqueSite l B.body.toList = none)
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      FrameRel l p
        { fn, label := i, pos, dsts, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts, env := e₂ }
  | wrapBefore {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      {pre post : List Lir.Stmt} {site : WrapperSite}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hsite : findUniqueSite l B.body.toList = some (pre, site, post))
      (hle : pos ≤ pre.length)
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      FrameRel l p
        { fn, label := i, pos, dsts, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts, env := e₂ }
  | wrapAfter {fn : Lir.FunId} {F : Lir.Func} {i m : Nat}
      {dsts : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      {pre post : List Lir.Stmt} {site : WrapperSite}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hsite : findUniqueSite l B.body.toList = some (pre, site, post))
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      FrameRel l p
        { fn, label := i, pos := pre.length + 1 + m, dsts, env := e₁ }
        { fn, label := newLabel l F i + siteExtra site, pos := sitePostOff site + m, dsts, env := e₂ }
  | decSlow {fn : Lir.FunId} {F : Lir.Func} {i : Nat}
      {e₁ e₂ : Lir.Env} {B : Lir.Block}
      {pre post : List Lir.Stmt} {x : Lir.VReg}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hsite : findUniqueSite l B.body.toList = some (pre, .dec x, post))
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      FrameRel l p
        { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
        { fn, label := newLabel l F i + 2, pos := 1, dsts := [], env := e₂ }

inductive TopFrameRel (l : Layout) (p : Lir.Program) : Lir.Frame → Lir.Frame → Prop
  | other {fr : Lir.Frame} (hnp : Prune.isPrunableReuse l fr.fn = false) :
      TopFrameRel l p fr fr
  | wrapInvalid {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts₁ dsts₂ : List Lir.VReg} {e₁ e₂ : Lir.Env}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hnone : F.blocks[i]? = none) :
      TopFrameRel l p
        { fn, label := i, pos, dsts := dsts₁, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts := dsts₂, env := e₂ }
  | wrapUnexpanded {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts₁ dsts₂ : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hnone : findUniqueSite l B.body.toList = none)
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      TopFrameRel l p
        { fn, label := i, pos, dsts := dsts₁, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts := dsts₂, env := e₂ }
  | wrapBefore {fn : Lir.FunId} {F : Lir.Func} {i pos : Nat}
      {dsts₁ dsts₂ : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      {pre post : List Lir.Stmt} {site : WrapperSite}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hsite : findUniqueSite l B.body.toList = some (pre, site, post))
      (hle : pos ≤ pre.length)
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      TopFrameRel l p
        { fn, label := i, pos, dsts := dsts₁, env := e₁ }
        { fn, label := newLabel l F i, pos, dsts := dsts₂, env := e₂ }
  | wrapAfter {fn : Lir.FunId} {F : Lir.Func} {i m : Nat}
      {dsts₁ dsts₂ : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
      {pre post : List Lir.Stmt} {site : WrapperSite}
      (hp : Prune.isPrunableReuse l fn = true)
      (hF : p.funcs[fn]? = some F)
      (hB : F.blocks[i]? = some B)
      (hsite : findUniqueSite l B.body.toList = some (pre, site, post))
      (hag : AgreeBelow (freshBase F) e₁ e₂) :
      TopFrameRel l p
        { fn, label := i, pos := pre.length + 1 + m, dsts := dsts₁, env := e₁ }
        { fn, label := newLabel l F i + siteExtra site, pos := sitePostOff site + m, dsts := dsts₂, env := e₂ }

inductive TailRel (l : Layout) (p : Lir.Program) : List Lir.Frame → List Lir.Frame → Prop
  | nil : TailRel l p [] []
  | cons {c₁ c₂ : Lir.Frame} {r₁ r₂ : List Lir.Frame} :
      FrameRel l p c₁ c₂ → TailRel l p r₁ r₂ → TailRel l p (c₁ :: r₁) (c₂ :: r₂)

inductive StackRel (l : Layout) (p : Lir.Program) : List Lir.Frame → List Lir.Frame → Prop
  | nil : StackRel l p [] []
  | cons {fr₁ fr₂ : Lir.Frame} {t₁ t₂ : List Lir.Frame} :
      TopFrameRel l p fr₁ fr₂ → TailRel l p t₁ t₂ →
      StackRel l p (fr₁ :: t₁) (fr₂ :: t₂)

def WStateRel (l : Layout) (p : Lir.Program) (s₁ s₂ : Lir.State) : Prop :=
  s₁.mem = s₂.mem ∧ s₁.ctx = s₂.ctx ∧ StackRel l p s₁.stack s₂.stack

inductive MatchedStep (l : Layout) (p : Lir.Program) (s₁ s₂ : Lir.State) : Prop
  | rawStuck : Lir.step p s₁ = .stuck → MatchedStep l p s₁ s₂
  | rawStuckWithin {c₁ : Nat} : c₁ ≤ 3 →
      Sem.Reaches (Lir.semStep p) s₁ c₁ .stuck →
      MatchedStep l p s₁ s₂
  | sameFinal {r : Sem.Result (List Lir.Word × X86.Memory)} :
      Sem.Final (Lir.semStep p s₁) r → Sem.Final (Lir.semStep (inlineProgram l p) s₂) r →
      MatchedStep l p s₁ s₂
  | sameReachFinal {c₁ c₂ : Nat} {r : Sem.Result (List Lir.Word × X86.Memory)} :
      c₁ ≤ 3 → r ≠ .timeout → r ≠ .stuck →
      Sem.Reaches (Lir.semStep p) s₁ c₁ r →
      Sem.Reaches (Lir.semStep (inlineProgram l p)) s₂ c₂ r →
      MatchedStep l p s₁ s₂
  | sync {s₁' s₂' s₁'' s₂'' : Lir.State} {b₁ b₂ : Bool} {c₁ c₂ : Nat} :
      Lir.semStep p s₁ = .next s₁' b₁ → Sem.Star (Lir.semStep p) s₁' c₁ s₁'' →
      Lir.semStep (inlineProgram l p) s₂ = .next s₂' b₂ →
      Sem.Star (Lir.semStep (inlineProgram l p)) s₂' c₂ s₂'' →
      b₁.toNat + c₁ ≤ b₂.toNat + c₂ + 3 →
      WStateRel l p s₁'' s₂'' →
      MatchedStep l p s₁ s₂

/-! ## Entry, return, edge, and normal-statement helpers -/

private theorem enter_rel (l : Layout) (p : Lir.Program) (g : Lir.FunId) (vs : List Lir.Word) :
    (∀ fr₁, Lir.enter p g vs = some fr₁ →
      ∃ fr₂, Lir.enter (inlineProgram l p) g vs = some fr₂ ∧ TopFrameRel l p fr₁ fr₂) ∧
    (Lir.enter p g vs = none ↔ Lir.enter (inlineProgram l p) g vs = none) := by
  by_cases hp : Prune.isPrunableReuse l g = true
  · have hget := inlineProgram_get_prunable (p := p) hp
    simp only [Lir.enter, hget]
    cases hF : p.funcs[g]? with
    | none => simp
    | some F =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      have hparams : (inlineFunc l F).params = F.params := rfl
      rw [hparams]
      cases hbp : Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        simp only [Option.bind_some, Option.some.injEq, forall_eq']
        refine ⟨⟨_, rfl, ?_⟩, by simp⟩
        have h0 : newLabel l F 0 = 0 := by simp [newLabel]
        cases hB : F.blocks[0]? with
        | none =>
          simpa [h0] using TopFrameRel.wrapInvalid (e₁ := ρ) (e₂ := ρ) hp hF hB
        | some B =>
          cases hf : findUniqueSite l B.body.toList with
          | none =>
            simpa [h0] using TopFrameRel.wrapUnexpanded hp hF hB hf AgreeBelow.refl
          | some triple =>
            rcases triple with ⟨pre, site, post⟩
            simpa [h0] using TopFrameRel.wrapBefore hp hF hB hf (Nat.zero_le _) AgreeBelow.refl
  · have hnp : Prune.isPrunableReuse l g = false := Bool.eq_false_iff.mpr hp
    have hget := inlineProgram_get_not_prunable (p := p) hnp
    simp only [Lir.enter, hget]
    cases p.funcs[g]? with
    | none => simp
    | some F =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        simp only [Option.bind_some, Option.some.injEq, forall_eq']
        exact ⟨⟨_, rfl, .other hnp⟩, by simp⟩

private theorem matched_of_ret {l : Layout} {p : Lir.Program}
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ fr₂ : Lir.Frame}
    {t₁ t₂ : List Lir.Frame} {vals : List Lir.Word}
    (h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
      match t₁ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: t₂ } =
      match t₂ with
      | [] => .done vals mem
      | caller :: rest =>
        match Lir.bindParams caller.env caller.dsts vals with
        | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest } false
        | none => .stuck)
    (htail : TailRel l p t₁ t₂) :
    MatchedStep l p { mem, ctx, stack := fr₁ :: t₁ } { mem, ctx, stack := fr₂ :: t₂ } := by
  cases htail with
  | nil =>
    exact .sameFinal (r := .ok (vals, mem))
      (by rw [Lir.semStep, h1]; exact .done)
      (by rw [Lir.semStep, h2]; exact .done)
  | @cons c₁ c₂ rest₁ rest₂ hc hrest =>
    cases hc with
    | other hnp =>
      cases hbp : Lir.bindParams c₁.env c₁.dsts vals with
      | none => exact .rawStuck (by rw [h1]; simp [hbp])
      | some ρ =>
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: c₁ :: rest₁ } =
            .next { mem, ctx, stack := { c₁ with env := ρ, dsts := [] } :: rest₁ } false := by
          rw [h1]; simp [hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: c₁ :: rest₂ } =
            .next { mem, ctx, stack := { c₁ with env := ρ, dsts := [] } :: rest₂ } false := by
          rw [h2]; simp [hbp]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons (.other hnp) hrest⟩
    | @wrapInvalid fn F i pos dsts e₁ e₂ hp hF hnone =>
      cases hbp : Lir.bindParams e₁ dsts vals with
      | none => exact .rawStuck (by rw [h1]; simp [hbp])
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, _⟩ :=
          (AgreeBelow.bindParams_agree (bound := 0) (e₁ := e₁) (e₂ := e₂) dsts vals
            (fun _ h => absurd h (by omega))).1 ρ₁ hbp
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: { fn, label := i, pos, dsts, env := e₁ } :: rest₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos, dsts := [], env := ρ₁ } :: rest₁ } false := by
          rw [h1]; simp [hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: { fn, label := newLabel l F i, pos, dsts, env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i, pos, dsts := [], env := ρ₂ } :: rest₂ } false := by
          rw [h2]; simp [hbp₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons (.wrapInvalid hp hF hnone) hrest⟩
    | @wrapUnexpanded fn F i pos dsts e₁ e₂ B hp hF hB hnone hag =>
      cases hbp : Lir.bindParams e₁ dsts vals with
      | none => exact .rawStuck (by rw [h1]; simp [hbp])
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, hag'⟩ := (AgreeBelow.bindParams_agree dsts vals hag).1 ρ₁ hbp
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: { fn, label := i, pos, dsts, env := e₁ } :: rest₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos, dsts := [], env := ρ₁ } :: rest₁ } false := by
          rw [h1]; simp [hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: { fn, label := newLabel l F i, pos, dsts, env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i, pos, dsts := [], env := ρ₂ } :: rest₂ } false := by
          rw [h2]; simp [hbp₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons (.wrapUnexpanded hp hF hB hnone hag') hrest⟩
    | @wrapBefore fn F i pos dsts e₁ e₂ B pre post site hp hF hB hsite hle hag =>
      cases hbp : Lir.bindParams e₁ dsts vals with
      | none => exact .rawStuck (by rw [h1]; simp [hbp])
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, hag'⟩ := (AgreeBelow.bindParams_agree dsts vals hag).1 ρ₁ hbp
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: { fn, label := i, pos, dsts, env := e₁ } :: rest₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos, dsts := [], env := ρ₁ } :: rest₁ } false := by
          rw [h1]; simp [hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: { fn, label := newLabel l F i, pos, dsts, env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i, pos, dsts := [], env := ρ₂ } :: rest₂ } false := by
          rw [h2]; simp [hbp₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons (.wrapBefore hp hF hB hsite hle hag') hrest⟩
    | @wrapAfter fn F i m dsts e₁ e₂ B pre post site hp hF hB hsite hag =>
      cases hbp : Lir.bindParams e₁ dsts vals with
      | none => exact .rawStuck (by rw [h1]; simp [hbp])
      | some ρ₁ =>
        obtain ⟨ρ₂, hbp₂, hag'⟩ := (AgreeBelow.bindParams_agree dsts vals hag).1 ρ₁ hbp
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: { fn, label := i, pos := pre.length + 1 + m, dsts, env := e₁ } :: rest₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1 + m, dsts := [], env := ρ₁ } :: rest₁ } false := by
          rw [h1]; simp [hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: { fn, label := newLabel l F i + siteExtra site, pos := sitePostOff site + m, dsts, env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i + siteExtra site, pos := sitePostOff site + m, dsts := [], env := ρ₂ } :: rest₂ } false := by
          rw [h2]; simp [hbp₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons (.wrapAfter hp hF hB hsite hag') hrest⟩
    | @decSlow fn F i e₁ e₂ B pre post x hp hF hB hsite hag =>
      cases vals with
      | cons _ _ =>
        exact .rawStuck (by rw [h1]; simp [Lir.bindParams])
      | nil =>
        have hF' : (inlineProgram l p).funcs[fn]? = some (inlineFunc l F) := by
          rw [inlineProgram_get_prunable hp, hF]; rfl
        have hB2 : (inlineFunc l F).blocks[newLabel l F i + 2]? =
            some { body := #[Lir.Stmt.call [] l.decProc [.v x]],
                   term := .jump ⟨newLabel l F i + 5, []⟩, cold := true } := by
          have hk : 2 < 1 + blockExtra l B := by simp [blockExtra, hsite, siteExtra]
          have h := inlineFunc_block_at l F hB hk
          simpa [expandBlock, hsite, expandSite] using h
        have hB5 : (inlineFunc l F).blocks[newLabel l F i + 5]? =
            some { body := post.toArray, term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
          have hk : 5 < 1 + blockExtra l B := by simp [blockExtra, hsite, siteExtra]
          have h := inlineFunc_block_at l F hB hk
          simpa [expandBlock, hsite, expandSite] using h
        have h1' : Lir.step p { mem, ctx, stack := fr₁ :: { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: rest₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: rest₁ } false := by
          rw [h1]; simp [Lir.bindParams]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₂ :: { fn, label := newLabel l F i + 2, pos := 1, dsts := [], env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i + 2, pos := 1, dsts := [], env := e₂ } :: rest₂ } false := by
          rw [h2]; simp [Lir.bindParams]
        have h2jump : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := newLabel l F i + 2, pos := 1, dsts := [], env := e₂ } :: rest₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F i + 5, pos := 0, dsts := [], env := e₂ } :: rest₂ } false := by
          unfold Lir.step
          simp [hF', hB2, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _)
          (Lir.semStep_next.mpr h2') (star_free h2jump (.refl _)) (by decide)
          ⟨rfl, rfl, .cons (by
            simpa [siteExtra, sitePostOff] using
              TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := []) hp hF hB hsite hag) hrest⟩

private theorem matched_of_wrap_edge {l : Layout} {p : Lir.Program}
    {mem : X86.Memory} {ctx : Lir.Word} {fn : Lir.FunId} {F : Lir.Func}
    {i pos₁ lbl₂ pos₂ : Nat} {dsts₁ dsts₂ : List Lir.VReg}
    {e₁ e₂ ρ₁ ρ₂ : Lir.Env} {t₁ t₂ : List Lir.Frame} {e : Lir.Edge}
    (hp : Prune.isPrunableReuse l fn = true)
    (hF : p.funcs[fn]? = some F)
    (hEdgeMax : Inline.edgeMax e 0 < freshBase F)
    (hag : AgreeBelow (freshBase F) ρ₁ ρ₂)
    (htail : TailRel l p t₁ t₂)
    (h1 : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
      Lir.takeEdge F { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ }
        { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } t₁ ρ₁ e)
    (h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
      Lir.takeEdge (inlineFunc l F) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ }
        { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } t₂ ρ₂ (relabelEdge (newLabel l F) e)) :
    MatchedStep l p
      { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ }
      { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } := by
  have hargs : Lir.evalArgs ρ₂ e.args = Lir.evalArgs ρ₁ e.args :=
    (AgreeBelow.evalArgs_eq hag hEdgeMax).symm
  cases ha : Lir.evalArgs ρ₁ e.args with
  | none =>
    exact .rawStuck (by rw [h1]; simp [Lir.takeEdge, ha])
  | some vals =>
    cases htb : F.blocks[e.target]? with
    | none =>
      exact .rawStuck (by rw [h1]; simp [Lir.takeEdge, ha, htb])
    | some target =>
      obtain ⟨target', htb', hparams⟩ := inlineFunc_entry_params l F htb
      cases hbp : Lir.bindParams ρ₁ target.params vals with
      | none =>
        exact .rawStuck (by rw [h1]; simp [Lir.takeEdge, ha, htb, hbp])
      | some ρ₁' =>
        obtain ⟨ρ₂', hbp', hag'⟩ := (AgreeBelow.bindParams_agree target.params vals hag).1 ρ₁' hbp
        have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
            .next { mem, ctx, stack := { fn, label := e.target, pos := 0, dsts := dsts₁, env := ρ₁' } :: t₁ }
              (decide (e.target ≤ i)) := by
          rw [h1]; simp [Lir.takeEdge, ha, htb, hbp]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := newLabel l F e.target, pos := 0, dsts := dsts₂, env := ρ₂' } :: t₂ }
              (decide (newLabel l F e.target ≤ lbl₂)) := by
          rw [h2]; simp [Lir.takeEdge, relabelEdge, hargs, ha, htb', hparams, hbp']; rfl
        have htop : TopFrameRel l p
            { fn, label := e.target, pos := 0, dsts := dsts₁, env := ρ₁' }
            { fn, label := newLabel l F e.target, pos := 0, dsts := dsts₂, env := ρ₂' } := by
          cases hf : findUniqueSite l target.body.toList with
          | none => exact .wrapUnexpanded hp hF htb hf hag'
          | some triple =>
            rcases triple with ⟨pre, site, post⟩
            exact .wrapBefore hp hF htb hf (Nat.zero_le _) hag'
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by cases decide (e.target ≤ i) <;> cases decide (newLabel l F e.target ≤ lbl₂) <;> decide)
          ⟨rfl, rfl, .cons htop htail⟩

private theorem step_match_term {l : Layout} {p : Lir.Program}
    {mem : X86.Memory} {ctx : Lir.Word} {fn : Lir.FunId} {F : Lir.Func}
    {i pos₁ lbl₂ pos₂ : Nat} {dsts₁ dsts₂ : List Lir.VReg}
    {e₁ e₂ : Lir.Env} {B B' : Lir.Block} {t₁ t₂ : List Lir.Frame}
    (hp : Prune.isPrunableReuse l fn = true)
    (hF : p.funcs[fn]? = some F)
    (hB : F.blocks[i]? = some B)
    (hB' : (inlineFunc l F).blocks[lbl₂]? = some B')
    (hpos₁ : ¬ pos₁ < B.body.size)
    (hpos₂ : ¬ pos₂ < B'.body.size)
    (hterm : B'.term = relabelTerm (newLabel l F) B.term)
    (hag : AgreeBelow (freshBase F) e₁ e₂)
    (htail : TailRel l p t₁ t₂) :
    MatchedStep l p
      { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ }
      { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } := by
  have hF' : (inlineProgram l p).funcs[fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_prunable hp, hF]; rfl
  have htermMax : Inline.termMax B.term 0 < freshBase F := by
    have := Inline.term_le_maxVReg hB
    simp only [freshBase]; omega
  cases ht : B.term with
  | jump e =>
    rw [ht] at htermMax hterm
    exact matched_of_wrap_edge hp hF (by simpa [Inline.termMax] using htermMax) hag htail
      (by unfold Lir.step; simp [hF, hB, hpos₁, ht])
      (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm])
  | br cond w a b' tr fa =>
    rw [ht] at htermMax hterm
    simp only [Inline.termMax] at htermMax
    obtain ⟨hfaLt, h1⟩ := AgreeBelow.edge_lt_of_chain htermMax
    obtain ⟨htrLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
    obtain ⟨hbLt, haLt⟩ := AgreeBelow.arg_lt_of_chain h2
    have haEq : a.eval e₂ = a.eval e₁ := (AgreeBelow.arg_eval hag haLt).symm
    have hbEq : b'.eval e₂ = b'.eval e₁ := (AgreeBelow.arg_eval hag hbLt).symm
    cases ha : a.eval e₁ with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha])
    | some va =>
      cases hb : b'.eval e₁ with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb])
      | some vb =>
        cases hc : cond.holds w va vb with
        | true =>
          exact matched_of_wrap_edge hp hF htrLt hag htail
            (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb, hc])
            (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha, hbEq, hb, hc])
        | false =>
          exact matched_of_wrap_edge hp hF hfaLt hag htail
            (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb, hc])
            (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha, hbEq, hb, hc])
  | brOvf op x a b' ok ovf =>
    rw [ht] at htermMax hterm
    simp only [Inline.termMax] at htermMax
    obtain ⟨hovfLt, h1⟩ := AgreeBelow.edge_lt_of_chain htermMax
    obtain ⟨hokLt, h2⟩ := AgreeBelow.edge_lt_of_chain h1
    obtain ⟨hbLt, h3⟩ := AgreeBelow.arg_lt_of_chain h2
    obtain ⟨haLt, _⟩ := AgreeBelow.arg_lt_of_chain h3
    have haEq : a.eval e₂ = a.eval e₁ := (AgreeBelow.arg_eval hag haLt).symm
    have hbEq : b'.eval e₂ = b'.eval e₁ := (AgreeBelow.arg_eval hag hbLt).symm
    cases ha : a.eval e₁ with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha])
    | some va =>
      cases hb : b'.eval e₁ with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb])
      | some vb =>
        let res := op.eval va vb
        have hag' : AgreeBelow (freshBase F) (e₁.insert x res.1) (e₂.insert x res.1) :=
          AgreeBelow.insert_same hag x res.1
        cases hc : res.2 with
        | true =>
          exact matched_of_wrap_edge hp hF hovfLt hag' htail
            (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb, res, hc])
            (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha, hbEq, hb, res, hc])
        | false =>
          exact matched_of_wrap_edge hp hF hokLt hag' htail
            (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hb, res, hc])
            (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha, hbEq, hb, res, hc])
  | ret as =>
    rw [ht] at htermMax hterm
    have haEq : Lir.evalArgs e₂ as = Lir.evalArgs e₁ as :=
      (AgreeBelow.evalArgs_eq hag (by simpa [Inline.termMax] using htermMax)).symm
    cases ha : Lir.evalArgs e₁ as with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha])
    | some vals =>
      exact matched_of_ret (vals := vals)
        (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha]; cases t₁ <;> rfl)
        (by unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha]; cases t₂ <;> rfl)
        htail
  | tail g as =>
    rw [ht] at htermMax hterm
    have haEq : Lir.evalArgs e₂ as = Lir.evalArgs e₁ as :=
      (AgreeBelow.evalArgs_eq hag (by simpa [Inline.termMax] using htermMax)).symm
    cases ha : Lir.evalArgs e₁ as with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha])
    | some vs =>
      cases hent : Lir.enter p g vs with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hent])
      | some callee₁ =>
        obtain ⟨callee₂, hent₂, htop⟩ := (enter_rel l p g vs).1 callee₁ hent
        have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
            .next { mem, ctx, stack := callee₁ :: t₁ } true := by
          unfold Lir.step; simp [hF, hB, hpos₁, ht, ha, hent]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := callee₂ :: t₂ } true := by
          unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm, haEq, ha, hent₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons htop htail⟩
  | fail r =>
    rw [ht] at hterm
    exact .sameFinal (r := .resource r)
      (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos₁, ht]; exact .fail)
      (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm]; exact .fail)
  | trap =>
    rw [ht] at hterm
    exact .sameFinal (r := .trap)
      (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos₁, ht]; exact .trap)
      (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB', hpos₂, hterm, relabelTerm]; exact .trap)

private theorem step_match_stmt {l : Layout} {p : Lir.Program}
    {mem : X86.Memory} {ctx : Lir.Word} {fn : Lir.FunId} {F : Lir.Func}
    {i pos₁ lbl₂ pos₂ : Nat} {dsts₁ dsts₂ : List Lir.VReg}
    {e₁ e₂ : Lir.Env} {B B' : Lir.Block} {s : Lir.Stmt} {t₁ t₂ : List Lir.Frame}
    (hp : Prune.isPrunableReuse l fn = true)
    (hF : p.funcs[fn]? = some F)
    (hB : F.blocks[i]? = some B)
    (hB' : (inlineFunc l F).blocks[lbl₂]? = some B')
    (hpos₁ : pos₁ < B.body.size)
    (hpos₂ : pos₂ < B'.body.size)
    (hs₁ : B.body[pos₁] = s)
    (hs₂ : B'.body[pos₂] = s)
    (hag : AgreeBelow (freshBase F) e₁ e₂)
    (htail : TailRel l p t₁ t₂)
    (hNextTop : ∀ {e₁' e₂' : Lir.Env}, AgreeBelow (freshBase F) e₁' e₂' →
      TopFrameRel l p
        { fn, label := i, pos := pos₁ + 1, dsts := dsts₁, env := e₁' }
        { fn, label := lbl₂, pos := pos₂ + 1, dsts := dsts₂, env := e₂' })
    (hNextCall : ∀ (rs : List Lir.VReg),
      FrameRel l p
        { fn, label := i, pos := pos₁ + 1, dsts := rs, env := e₁ }
        { fn, label := lbl₂, pos := pos₂ + 1, dsts := rs, env := e₂ }) :
    MatchedStep l p
      { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ }
      { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } := by
  have hF' : (inlineProgram l p).funcs[fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_prunable hp, hF]; rfl
  have hsm : Inline.stmtMax s 0 < freshBase F := by
    have hmem : s ∈ B.body.toList := by
      rw [← hs₁]; exact Array.getElem_mem_toList hpos₁
    have := Inline.stmt_le_maxVReg hB hmem
    simp only [freshBase]; omega
  cases hsc : s with
  | assign x r =>
    rw [hsc] at hs₁ hs₂ hsm
    cases hex : Lir.Stmt.exec e₁ mem ctx (.assign x r) with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex])
    | some pr =>
      obtain ⟨e₂', hex₂, hag'⟩ := (AgreeBelow.stmt_exec hag hsm mem ctx).1 pr.1 pr.2 hex
      have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem := pr.2, ctx, stack := { fn, label := i, pos := pos₁ + 1, dsts := dsts₁, env := pr.1 } :: t₁ } false := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex]
      have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
          .next { mem := pr.2, ctx, stack := { fn, label := lbl₂, pos := pos₂ + 1, dsts := dsts₂, env := e₂' } :: t₂ } false := by
        unfold Lir.step; simp [hF', hB', hpos₂, hs₂, hex₂]
      exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
        (by decide) ⟨rfl, rfl, .cons (hNextTop hag') htail⟩
  | limb r1 r2 op =>
    rw [hsc] at hs₁ hs₂ hsm
    cases hex : Lir.Stmt.exec e₁ mem ctx (.limb r1 r2 op) with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex])
    | some pr =>
      obtain ⟨e₂', hex₂, hag'⟩ := (AgreeBelow.stmt_exec hag hsm mem ctx).1 pr.1 pr.2 hex
      have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem := pr.2, ctx, stack := { fn, label := i, pos := pos₁ + 1, dsts := dsts₁, env := pr.1 } :: t₁ } false := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex]
      have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
          .next { mem := pr.2, ctx, stack := { fn, label := lbl₂, pos := pos₂ + 1, dsts := dsts₂, env := e₂' } :: t₂ } false := by
        unfold Lir.step; simp [hF', hB', hpos₂, hs₂, hex₂]
      exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
        (by decide) ⟨rfl, rfl, .cons (hNextTop hag') htail⟩
  | store w m a =>
    rw [hsc] at hs₁ hs₂ hsm
    cases hex : Lir.Stmt.exec e₁ mem ctx (.store w m a) with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex])
    | some pr =>
      obtain ⟨e₂', hex₂, hag'⟩ := (AgreeBelow.stmt_exec hag hsm mem ctx).1 pr.1 pr.2 hex
      have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem := pr.2, ctx, stack := { fn, label := i, pos := pos₁ + 1, dsts := dsts₁, env := pr.1 } :: t₁ } false := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, hex]
      have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
          .next { mem := pr.2, ctx, stack := { fn, label := lbl₂, pos := pos₂ + 1, dsts := dsts₂, env := e₂' } :: t₂ } false := by
        unfold Lir.step; simp [hF', hB', hpos₂, hs₂, hex₂]
      exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
        (by decide) ⟨rfl, rfl, .cons (hNextTop hag') htail⟩
  | call rs g as =>
    rw [hsc] at hs₁ hs₂ hsm
    have hargsMax : Inline.argsMax as 0 < freshBase F := by
      have h1 := Inline.call_args_lt_freshBase hB (by rw [← hs₁]; exact Array.getElem_mem_toList hpos₁)
      exact h1
    have haEq : Lir.evalArgs e₂ as = Lir.evalArgs e₁ as := (AgreeBelow.evalArgs_eq hag hargsMax).symm
    cases ha : Lir.evalArgs e₁ as with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, ha])
    | some vs =>
      cases hent : Lir.enter p g vs with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, ha, hent])
      | some callee₁ =>
        obtain ⟨callee₂, hent₂, htop⟩ := (enter_rel l p g vs).1 callee₁ hent
        have h1' : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pos₁, dsts := dsts₁, env := e₁ } :: t₁ } =
            .next { mem, ctx, stack := callee₁ :: { fn, label := i, pos := pos₁ + 1, dsts := rs, env := e₁ } :: t₁ } true := by
          unfold Lir.step; simp [hF, hB, hpos₁, hs₁, ha, hent]
        have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := lbl₂, pos := pos₂, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := callee₂ :: { fn, label := lbl₂, pos := pos₂ + 1, dsts := rs, env := e₂ } :: t₂ } true := by
          unfold Lir.step; simp [hF', hB', hpos₂, hs₂, haEq, ha, hent₂]
        exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
          (by decide) ⟨rfl, rfl, .cons htop (.cons (hNextCall rs) htail)⟩

/-! ## Site execution matching for the 4 inlined runtime procedures -/

private theorem step_match_site {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p)
    {mem : X86.Memory} {ctx : Lir.Word} {fn : Lir.FunId} {F : Lir.Func}
    {i : Nat} {dsts₁ dsts₂ : List Lir.VReg} {e₁ e₂ : Lir.Env} {B : Lir.Block}
    {pre post : List Lir.Stmt} {site : WrapperSite} {t₁ t₂ : List Lir.Frame}
    (hp : Prune.isPrunableReuse l fn = true)
    (hF : p.funcs[fn]? = some F)
    (hB : F.blocks[i]? = some B)
    (hsite : findUniqueSite l B.body.toList = some (pre, site, post))
    (hag : AgreeBelow (freshBase F) e₁ e₂)
    (htail : TailRel l p t₁ t₂) :
    MatchedStep l p
      { mem, ctx, stack := { fn, label := i, pos := pre.length, dsts := dsts₁, env := e₁ } :: t₁ }
      { mem, ctx, stack := { fn, label := newLabel l F i, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } := by
  obtain ⟨s0, hbody, hcl⟩ := findUniqueSite_spec hsite
  have hF' : (inlineProgram l p).funcs[fn]? = some (inlineFunc l F) := by
    rw [inlineProgram_get_prunable hp, hF]; rfl
  have hpos₁ : pre.length < B.body.size := by
    have := congrArg List.length hbody; simp at this; omega
  have hs₁ : B.body[pre.length] = s0 := by
    have h1 : B.body.toList[pre.length]? = some s0 := by rw [hbody]; simp
    have h2 : B.body.toList[pre.length]? = some (B.body[pre.length]) := by
      simp [hpos₁]
    exact Option.some.inj (h2.symm.trans h1)
  have hs0Mem : s0 ∈ B.body.toList := by rw [hbody]; simp
  let cur := newLabel l F i
  let nt := blockTmpBase l F i
  have hnt : freshBase F ≤ nt := freshBase_le_blockTmpBase l F i
  have hblk : ∀ k, k < 1 + siteExtra site →
      (inlineFunc l F).blocks[cur + k]? =
        (expandSite l (newLabel l F) B cur nt pre site post)[k]? := by
    intro k hk
    have hk' : k < 1 + blockExtra l B := by simp [blockExtra, hsite, hk]
    simpa [cur, nt, expandBlock, hsite] using inlineFunc_block_at l F hB hk'
  cases site with
  | isUnique dst x =>
    obtain ⟨hsEq, _⟩ := classify_isUnique hcl
    subst hsEq
    have hxLt : x < freshBase F := by
      have h1 := Inline.call_args_lt_freshBase hB hs0Mem
      have h2 : x ≤ Inline.argsMax [.v x] 0 := Inline.mem_le_argsMax (by simp)
      exact Nat.lt_of_le_of_lt h2 h1
    have hxEq : e₂[x]? = e₁[x]? := (hag x hxLt).symm
    have hB0 : (inlineFunc l F).blocks[cur]? = some
        { params := B.params, body := pre.toArray,
          term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 0 (by simp [siteExtra])
    have hB1 : (inlineFunc l F).blocks[cur + 1]? = some
        { body := #[Lir.Stmt.assign nt (.load .w32 .zero (cellAddr x 4))],
          term := .br .eq .w32 (.v nt) (.imm 0) ⟨cur + 3, [.imm 1]⟩ ⟨cur + 2, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 1 (by simp [siteExtra])
    have hB2 : (inlineFunc l F).blocks[cur + 2]? = some
        { body := #[], term := .jump ⟨cur + 3, [.imm 0]⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 2 (by simp [siteExtra])
    have hB3 : (inlineFunc l F).blocks[cur + 3]? = some
        { params := [dst], body := post.toArray,
          term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
      simpa [expandSite] using hblk 3 (by simp [siteExtra])
    cases hwx : e₁[x]? with
    | none =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx])
    | some wx =>
      have hwx₂ : e₂[x]? = some wx := by rw [hxEq, hwx]
      let caller₁ : Lir.Frame := { fn, label := i, pos := pre.length + 1, dsts := [dst], env := e₁ }
      have h1call : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pre.length, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } true := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx,
          Lir.enter, hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.bindParams, caller₁]
      by_cases hodd : (wx &&& 1) != 0
      · have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 3, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Arg.eval, v, to, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h1_3 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 3, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 0 } :: t₁ } false := by
          unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.evalArgs, Lir.Arg.eval, caller₁, Lir.bindParams]
        have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, hB2, Lir.bindParams]
        have h2_2 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert dst 0 } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB2, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hB3, Lir.bindParams]
        have htop : TopFrameRel l p
            { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 0 }
            { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert dst 0 } := by
          simpa [cur, siteExtra, sitePostOff] using
            TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite (hag.insert_same dst 0)
        exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_3 (.refl _)))
          (Lir.semStep_next.mpr h2_0) (star_free h2_2 (.refl _)) (by decide) ⟨rfl, rfl, .cons htop htail⟩
      · have hev : ((wx &&& 1) != 0) = false := Bool.eq_false_iff.mpr hodd
        have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Arg.eval, v, to, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        cases hrc : mem.read? .w32 (wx + 4) with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (.refl _)))
            (by unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]))
        | ok rc =>
          have h1_1 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
              .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
            unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]
          have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, hB1, Lir.bindParams]
          have h2_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, hwx₂, Lir.dispWord, hrc]
          cases hrc0 : Lir.Cond.holds .eq .w32 rc 0 with
          | true =>
            have h1_1t : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Arg.eval, v, to, hrc0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            have h1_2 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 1 } :: t₁ } false := by
              unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.evalArgs, Lir.Arg.eval, caller₁, Lir.bindParams]
            have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert dst 1 } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hrc0, Lir.takeEdge, Lir.evalArgs, hB3, Lir.bindParams]
            have htop : TopFrameRel l p
                { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 1 }
                { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert dst 1 } := by
              simpa [cur, siteExtra, sitePostOff] using
                TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite
                  ((hag.insert_ge hnt rc).insert_same dst 1)
            exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_2 (.refl _)))))
              (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (.refl _))) (by decide) ⟨rfl, rfl, .cons htop htail⟩
          | false =>
            have h1_1t : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.isUniqueProc, label := 3, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.Arg.eval, v, to, hrc0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            have h1_3 : Lir.step p { mem, ctx, stack := { fn := l.isUniqueProc, label := 3, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 0 } :: t₁ } false := by
              unfold Lir.step; simp [hr.isUniqueProc, Rt.Rc.Gen.isUnique, Lir.evalArgs, Lir.Arg.eval, caller₁, Lir.bindParams]
            have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hrc0, Lir.takeEdge, Lir.evalArgs, hB2, Lir.bindParams]
            have h2_2 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert dst 0 } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB2, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hB3, Lir.bindParams]
            have htop : TopFrameRel l p
                { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst 0 }
                { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert dst 0 } := by
              simpa [cur, siteExtra, sitePostOff] using
                TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite
                  ((hag.insert_ge hnt rc).insert_same dst 0)
            exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_3 (.refl _)))))
              (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_free h2_2 (.refl _)))) (by decide) ⟨rfl, rfl, .cons htop htail⟩
  | inc x =>
    have hsEq := classify_inc hcl
    subst hsEq
    have hxLt : x < freshBase F := by
      have h1 := Inline.call_args_lt_freshBase hB hs0Mem
      have h2 : x ≤ Inline.argsMax [.v x] 0 := Inline.mem_le_argsMax (by simp)
      exact Nat.lt_of_le_of_lt h2 h1
    have hxEq : e₂[x]? = e₁[x]? := (hag x hxLt).symm
    let maxM1 := UInt64.ofNat (Rt.Rc.maxCount - 1)
    have hB0 : (inlineFunc l F).blocks[cur]? = some
        { params := B.params, body := pre.toArray,
          term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 5, []⟩ ⟨cur + 1, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 0 (by simp [siteExtra])
    have hB1 : (inlineFunc l F).blocks[cur + 1]? = some
        { body := #[Lir.Stmt.assign nt (.load .w32 .zero (cellAddr x 4))],
          term := .br .ult .w32 (.v nt) (.imm maxM1) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩, cold := B.cold } := by
      simpa [expandSite, maxM1] using hblk 1 (by simp [siteExtra])
    have hB2 : (inlineFunc l F).blocks[cur + 2]? = some
        { body := #[Lir.Stmt.assign (nt + 1) (.bin .add .w32 (.v nt) (.imm 1)),
            Lir.Stmt.store .w32 (cellAddr x 4) (.v (nt + 1))],
          term := .jump ⟨cur + 5, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 2 (by simp [siteExtra])
    have hB3 : (inlineFunc l F).blocks[cur + 3]? = some
        { body := #[], term := .br .eq .w32 (.v nt) (.imm maxM1) ⟨cur + 4, []⟩ ⟨cur + 5, []⟩, cold := true } := by
      simpa [expandSite, maxM1] using hblk 3 (by simp [siteExtra])
    have hB4 : (inlineFunc l F).blocks[cur + 4]? = some
        { body := #[], term := .fail .heap, cold := true } := by
      simpa [expandSite] using hblk 4 (by simp [siteExtra])
    have hB5 : (inlineFunc l F).blocks[cur + 5]? = some
        { body := post.toArray, term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
      simpa [expandSite] using hblk 5 (by simp [siteExtra])
    cases hwx : e₁[x]? with
    | none =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx])
    | some wx =>
      have hwx₂ : e₂[x]? = some wx := by rw [hxEq, hwx]
      let caller₁ : Lir.Frame := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
      have h1call : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pre.length, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem, ctx, stack := { fn := l.incProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } true := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx,
          Lir.enter, hr.incProc, Rt.Rc.Procs.inc, Lir.bindParams, caller₁]
      by_cases hodd : (wx &&& 1) != 0
      · have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h1_5 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
          unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.evalArgs, caller₁, Lir.bindParams]
        have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
        have htop : TopFrameRel l p
            { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
            { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂ } := by
          simpa [cur, siteExtra, sitePostOff] using
            TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite hag
        exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_5 (.refl _)))
          (Lir.semStep_next.mpr h2_0) (.refl _) (by decide) ⟨rfl, rfl, .cons htop htail⟩
      · have hev : ((wx &&& 1) != 0) = false := Bool.eq_false_iff.mpr hodd
        have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 0, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        cases hrc : mem.read? .w32 (wx + 4) with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (.refl _)))
            (by unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]))
        | ok rc =>
          have h1_1 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 wx } :: caller₁ :: t₁ } =
              .next { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
            unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]
          have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, hB1, Lir.bindParams]
          have h2_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, hwx₂, Lir.dispWord, hrc]
          cases hult : Lir.Cond.holds .ult .w32 rc maxM1 with
          | true =>
            obtain ⟨hslt, heqm⟩ := cond_ult_iff.mp hult
            have h1_1t : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            have h1_2 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, heqm, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
            let rc1 := X86.Width.w32.truncate (rc + 1)
            have h1_3_0 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, v, Lir.BinOp.eval, rc1]
            cases hw : mem.write? .w32 (wx + 4) rc1 with
            | error _ =>
              exact .rawStuckWithin (by omega) (star_reaches_stuck
                (star_charge h1call (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_2 (star_free h1_3_0 (.refl _)))))))
                (by unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hw]))
            | ok mem' =>
              have h1_3_1 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 3, pos := 1, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } =
                  .next { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hw]
              have h1_3_2 : Lir.step p { mem := mem', ctx, stack := { fn := l.incProc, label := 3, pos := 2, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } =
                  .next { mem := mem', ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.takeEdge, to, Lir.evalArgs, Lir.bindParams]
              have h1_5 : Lir.step p { mem := mem', ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := ((({} : Lir.Env).insert 0 wx).insert 1 rc).insert 2 rc1 } :: caller₁ :: t₁ } =
                  .next { mem := mem', ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.evalArgs, caller₁, Lir.bindParams]
              have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hult, Lir.takeEdge, Lir.evalArgs, hB2, Lir.bindParams]
              have h2_2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 2, pos := 1, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB2, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, Lir.BinOp.eval, rc1]
              have hx2' : ((e₂.insert nt rc).insert (nt + 1) rc1)[x]? = some wx := by
                have hne1 : nt + 1 ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxLt (Nat.le_trans hnt (Nat.le_succ _)))
                have hne2 : nt ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxLt hnt)
                simp [hne1, hne2, hwx₂]
              have h2_2_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 1, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } =
                  .next { mem := mem', ctx, stack := { fn, label := cur + 2, pos := 2, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, hx2', Lir.dispWord, hw]
              have h2_2_2 : Lir.step (inlineProgram l p) { mem := mem', ctx, stack := { fn, label := cur + 2, pos := 2, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } =
                  .next { mem := mem', ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB2, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
              have htop : TopFrameRel l p
                  { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
                  { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } := by
                simpa [cur, siteExtra, sitePostOff] using
                  TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite
                    ((hag.insert_ge hnt rc).insert_ge (Nat.le_trans hnt (Nat.le_succ _)) rc1)
              exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_2 (star_free h1_3_0 (star_free h1_3_1 (star_free h1_3_2 (star_free h1_5 (.refl _)))))))))
                (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_free h2_2_0 (star_free h2_2_1 (star_free h2_2_2 (.refl _)))))) (by decide)
                ⟨rfl, rfl, .cons htop htail⟩
          | false =>
            have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hult, Lir.takeEdge, Lir.evalArgs, hB3, Lir.bindParams]
            cases heqm : Lir.Cond.holds .eq .w32 rc maxM1 with
            | true =>
              have hslt := slt_zero_of_eq_max heqm
              have h1_1t : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_2 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 2, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, heqm, maxM1, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_4 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 4, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } = .fail .heap := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc]
              have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB3, Lir.Arg.eval, heqm, Lir.takeEdge, Lir.evalArgs, hB4, Lir.bindParams]
              have h2_4 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } = .fail .heap := by
                unfold Lir.step; simp [hF', hB4]
              exact .sameReachFinal (c₁ := 1) (c₂ := 0) (by omega) (by simp) (by simp)
                (star_reaches_fail (star_charge h1call (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_2 (.refl _)))))) h1_4)
                (star_reaches_fail (star_free h2_0 (star_free h2_1 (star_free h2_1t (star_free h2_3 (.refl _))))) h2_4)
            | false =>
              have hslt := slt_zero_of_not_ult_not_eq hult heqm
              have h1_1t : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.Arg.eval, v, to, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_5 : Lir.step p { mem, ctx, stack := { fn := l.incProc, label := 5, pos := 0, env := (({} : Lir.Env).insert 0 wx).insert 1 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
                unfold Lir.step; simp [hr.incProc, Rt.Rc.Procs.inc, Lir.evalArgs, caller₁, Lir.bindParams]
              have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB3, Lir.Arg.eval, heqm, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
              have htop : TopFrameRel l p
                  { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
                  { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } := by
                simpa [cur, siteExtra, sitePostOff] using
                  TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite (hag.insert_ge hnt rc)
              exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_1t (star_free h1_5 (.refl _)))))
                (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_free h2_3 (.refl _)))) (by decide)
                ⟨rfl, rfl, .cons htop htail⟩
  | dec x =>
    have hsEq := classify_dec hcl
    subst hsEq
    have hxLt : x < freshBase F := by
      have h1 := Inline.call_args_lt_freshBase hB hs0Mem
      have h2 : x ≤ Inline.argsMax [.v x] 0 := Inline.mem_le_argsMax (by simp)
      exact Nat.lt_of_le_of_lt h2 h1
    have hxEq : e₂[x]? = e₁[x]? := (hag x hxLt).symm
    have hdec2 : (inlineProgram l p).funcs[l.decProc]? = some Rt.Rc.Gen.dec := by
      rw [inlineProgram_get_le (by simp [Layout.isUniqueProc, Layout.init, Layout.decProc]; omega), hr.decProc]
    have hdecNp : Prune.isPrunableReuse l l.decProc = false := by
      simp only [Prune.isPrunableReuse, decide_eq_false_iff_not]
      exact fun h => by simp [Layout.isUniqueProc, Layout.init, Layout.decProc] at h; omega
    have hB0 : (inlineFunc l F).blocks[cur]? = some
        { params := B.params, body := pre.toArray,
          term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 5, []⟩ ⟨cur + 1, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 0 (by simp [siteExtra])
    have hB1 : (inlineFunc l F).blocks[cur + 1]? = some
        { body := #[Lir.Stmt.assign nt (.load .w32 .zero (cellAddr x 4))],
          term := .br .eq .w32 (.v nt) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 1 (by simp [siteExtra])
    have hB2 : (inlineFunc l F).blocks[cur + 2]? = some
        { body := #[Lir.Stmt.call [] l.decProc [.v x]],
          term := .jump ⟨cur + 5, []⟩, cold := true } := by
      simpa [expandSite] using hblk 2 (by simp [siteExtra])
    have hB3 : (inlineFunc l F).blocks[cur + 3]? = some
        { body := #[], term := .br .slt .w32 (.v nt) (.imm 0) ⟨cur + 5, []⟩ ⟨cur + 4, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 3 (by simp [siteExtra])
    have hB4 : (inlineFunc l F).blocks[cur + 4]? = some
        { body := #[Lir.Stmt.assign (nt + 1) (.bin .sub .w32 (.v nt) (.imm 1)),
            Lir.Stmt.store .w32 (cellAddr x 4) (.v (nt + 1))],
          term := .jump ⟨cur + 5, []⟩, cold := B.cold } := by
      simpa [expandSite] using hblk 4 (by simp [siteExtra])
    have hB5 : (inlineFunc l F).blocks[cur + 5]? = some
        { body := post.toArray, term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
      simpa [expandSite] using hblk 5 (by simp [siteExtra])
    cases hwx : e₁[x]? with
    | none =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx])
    | some wx =>
      have hwx₂ : e₂[x]? = some wx := by rw [hxEq, hwx]
      let caller₁ : Lir.Frame := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
      let decEnv0 : Lir.Env := ({} : Lir.Env).insert 0 wx
      let decEnv1 : Lir.Env := (decEnv0.insert 1 wx).insert 2 0
      have h1call : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pre.length, dsts := dsts₁, env := e₁ } :: t₁ } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := decEnv0 } :: caller₁ :: t₁ } true := by
        unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.Arg.eval, hwx,
          Lir.enter, hr.decProc, Rt.Rc.Gen.dec, Lir.bindParams, caller₁, decEnv0]
      have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := decEnv0 } :: caller₁ :: t₁ } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := decEnv1 } :: caller₁ :: t₁ } false := by
        unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, decEnv0, decEnv1, Lir.bindParams]
      by_cases hodd : (wx &&& 1) != 0
      · have h1_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := decEnv1 } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := decEnv1.insert 8 0 } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, decEnv1, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := decEnv1.insert 8 0 } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := decEnv1.insert 8 0 } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, w64_eq_iff, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h1_10 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := decEnv1.insert 8 0 } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
          unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.evalArgs, caller₁, Lir.bindParams]
        have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hodd, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
        have htop : TopFrameRel l p
            { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
            { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂ } := by
          simpa [cur, siteExtra, sitePostOff] using
            TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite hag
        exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_6 (star_free h1_10 (.refl _)))))
          (Lir.semStep_next.mpr h2_0) (.refl _) (by decide) ⟨rfl, rfl, .cons htop htail⟩
      · have hev : ((wx &&& 1) != 0) = false := Bool.eq_false_iff.mpr hodd
        have h1_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := decEnv1 } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := decEnv1 } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, decEnv1, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        cases hrc : mem.read? .w32 (wx + 4) with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (star_free h1_1 (.refl _))))
            (by unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]))
        | ok rc =>
          have h1_2_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := decEnv1 } :: caller₁ :: t₁ } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } false := by
            unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hrc]
          have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, hwx₂, w64_tnz_1, hev, Lir.takeEdge, Lir.evalArgs, hB1, Lir.bindParams]
          have h2_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂ } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, hwx₂, Lir.dispWord, hrc]
          cases hrc0 : Lir.Cond.holds .eq .w32 rc 0 with
          | true =>
            have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hrc0, Lir.takeEdge, Lir.evalArgs, hB2, Lir.bindParams]
            have hx2' : (e₂.insert nt rc)[x]? = some wx := by
              have hne : nt ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxLt hnt)
              simp [hne, hwx₂]
            have h2_call : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := decEnv0 } ::
                  { fn, label := cur + 2, pos := 1, dsts := [], env := e₂.insert nt rc } :: t₂ } true := by
              unfold Lir.step; simp [hF', hB2, Lir.evalArgs, Lir.Arg.eval, hx2',
                Lir.enter, hdec2, Rt.Rc.Gen.dec, Lir.bindParams, decEnv0]
            exact .sync (Lir.semStep_next.mpr h1call) (.refl _)
              (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_charge h2_call (.refl _)))) (by decide)
              ⟨rfl, rfl, .cons (.other hdecNp) (.cons (.decSlow hp hF hB hsite (hag.insert_ge hnt rc)) htail)⟩
          | false =>
            have h2_1t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB1, Lir.Arg.eval, hrc0, Lir.takeEdge, Lir.evalArgs, hB3, Lir.bindParams]
            cases hslt : Lir.Cond.holds .slt .w32 rc 0 with
            | true =>
              have h1_2_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := (decEnv1.insert 3 rc).insert 8 0 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.Arg.eval, v, to, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := (decEnv1.insert 3 rc).insert 8 0 } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := (decEnv1.insert 3 rc).insert 8 0 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, w64_eq_iff, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_10 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := (decEnv1.insert 3 rc).insert 8 0 } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.evalArgs, caller₁, Lir.bindParams]
              have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB3, Lir.Arg.eval, hslt, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
              have htop : TopFrameRel l p
                  { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
                  { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } := by
                simpa [cur, siteExtra, sitePostOff] using
                  TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite (hag.insert_ge hnt rc)
              exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_2_0 (star_free h1_2_1 (star_free h1_6 (star_free h1_10 (.refl _)))))))
                (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_free h2_3 (.refl _)))) (by decide)
                ⟨rfl, rfl, .cons htop htail⟩
            | false =>
              have h1_2_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, hslt, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_3 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, hrc0, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              let rc1 := X86.Width.w32.truncate (rc - 1)
              have h1_4_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := decEnv1.insert 3 rc } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (decEnv1.insert 3 rc).insert 4 rc1 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, v, Lir.BinOp.eval, rc1]
              cases hw : mem.write? .w32 (wx + 4) rc1 with
              | error _ =>
                exact .rawStuckWithin (by omega) (star_reaches_stuck
                  (star_charge h1call (star_free h1_0 (star_free h1_1 (star_free h1_2_0 (star_free h1_2_1 (star_free h1_3 (star_free h1_4_0 (.refl _))))))))
                  (by unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hw]))
              | ok mem' =>
                have h1_4_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (decEnv1.insert 3 rc).insert 4 rc1 } :: caller₁ :: t₁ } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (decEnv1.insert 3 rc).insert 4 rc1 } :: caller₁ :: t₁ } false := by
                  unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hw]
                have h1_4_2 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (decEnv1.insert 3 rc).insert 4 rc1 } :: caller₁ :: t₁ } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((decEnv1.insert 3 rc).insert 4 rc1).insert 8 0 } :: caller₁ :: t₁ } false := by
                  unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, decEnv1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                have h1_6 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((decEnv1.insert 3 rc).insert 4 rc1).insert 8 0 } :: caller₁ :: t₁ } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := ((decEnv1.insert 3 rc).insert 4 rc1).insert 8 0 } :: caller₁ :: t₁ } false := by
                  unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.Arg.eval, v, to, w64_eq_iff, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                have h1_10 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := ((decEnv1.insert 3 rc).insert 4 rc1).insert 8 0 } :: caller₁ :: t₁ } =
                    .next { mem := mem', ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ } :: t₁ } false := by
                  unfold Lir.step; simp [hr.decProc, Rt.Rc.Gen.dec, Lir.evalArgs, caller₁, Lir.bindParams]
                have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                    .next { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB3, Lir.Arg.eval, hslt, Lir.takeEdge, Lir.evalArgs, hB4, Lir.bindParams]
                have h2_4_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e₂.insert nt rc } :: t₂ } =
                    .next { mem, ctx, stack := { fn, label := cur + 4, pos := 1, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB4, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, Lir.BinOp.eval, rc1]
                have hx2' : ((e₂.insert nt rc).insert (nt + 1) rc1)[x]? = some wx := by
                  have hne1 : nt + 1 ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxLt (Nat.le_trans hnt (Nat.le_succ _)))
                  have hne2 : nt ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hxLt hnt)
                  simp [hne1, hne2, hwx₂]
                have h2_4_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 4, pos := 1, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } =
                    .next { mem := mem', ctx, stack := { fn, label := cur + 4, pos := 2, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB4, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, hx2', Lir.dispWord, hw]
                have h2_4_2 : Lir.step (inlineProgram l p) { mem := mem', ctx, stack := { fn, label := cur + 4, pos := 2, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } =
                    .next { mem := mem', ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB4, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
                have htop : TopFrameRel l p
                    { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁ }
                    { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := (e₂.insert nt rc).insert (nt + 1) rc1 } := by
                  simpa [cur, siteExtra, sitePostOff] using
                    TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite
                      ((hag.insert_ge hnt rc).insert_ge (Nat.le_trans hnt (Nat.le_succ _)) rc1)
                exact .sync (Lir.semStep_next.mpr h1call) (star_free h1_0 (star_free h1_1 (star_free h1_2_0 (star_free h1_2_1 (star_free h1_3 (star_free h1_4_0 (star_free h1_4_1 (star_free h1_4_2 (star_free h1_6 (star_free h1_10 (.refl _)))))))))))
                  (Lir.semStep_next.mpr h2_0) (star_free h2_1 (star_free h2_1t (star_free h2_3 (star_free h2_4_0 (star_free h2_4_1 (star_free h2_4_2 (.refl _))))))) (by decide)
                  ⟨rfl, rfl, .cons htop htail⟩
  | alloc dst idx lay cls =>
    obtain ⟨c, hc, hlayEq, hok, hcls, hsEq⟩ := classify_alloc hcl
    subst hsEq hlayEq
    have halloc : p.funcs[l.allocProc idx]? = some (Rt.Rc.Gen.allocFunc (Rt.Rc.CellLayout.ofFields c.arity c.tag) cls) := by
      rw [hr.allocProc idx c hc, Rt.Rc.Gen.alloc_eq hok hcls]
    let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
    let headOff : Int := 8 * Int.ofNat cls
    let bytes := UInt64.ofNat (Rt.Rc.classBytes cls)
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    have hB0 : (inlineFunc l F).blocks[cur]? = some
        { params := B.params,
          body := (pre ++ [Lir.Stmt.assign nt (.load .w64 .zero (ctxAddr headOff))]).toArray,
          term := .br .eq .w64 (.v nt) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩, cold := false } := by
      simpa [expandSite, lay, headOff] using hblk 0 (by simp [siteExtra])
    have hB1 : (inlineFunc l F).blocks[cur + 1]? = some
        { body := #[Lir.Stmt.assign (nt + 1) (.load .w64 .zero (cellAddr nt)),
            Lir.Stmt.store .w64 (ctxAddr headOff) (.v (nt + 1))],
          term := .jump ⟨cur + 6, [.v nt]⟩, cold := false } := by
      simpa [expandSite, headOff] using hblk 1 (by simp [siteExtra])
    have hB2 : (inlineFunc l F).blocks[cur + 2]? = some
        { body := #[Lir.Stmt.assign (nt + 2) (.load .w64 .zero (ctxAddr Rt.bumpOff)),
            Lir.Stmt.assign (nt + 3) (.load .w64 .zero (ctxAddr Rt.limitOff))],
          term := .brOvf .addC (nt + 4) (.v (nt + 2)) (.imm bytes) ⟨cur + 3, []⟩ ⟨cur + 5, []⟩, cold := false } := by
      simpa [expandSite, bytes] using hblk 2 (by simp [siteExtra])
    have hB3 : (inlineFunc l F).blocks[cur + 3]? = some
        { body := #[], term := .br .ule .w64 (.v (nt + 4)) (.v (nt + 3)) ⟨cur + 4, []⟩ ⟨cur + 5, []⟩, cold := false } := by
      simpa [expandSite] using hblk 3 (by simp [siteExtra])
    have hB4 : (inlineFunc l F).blocks[cur + 4]? = some
        { body := #[Lir.Stmt.store .w64 (ctxAddr Rt.bumpOff) (.v (nt + 4))],
          term := .jump ⟨cur + 6, [.v (nt + 2)]⟩, cold := false } := by
      simpa [expandSite] using hblk 4 (by simp [siteExtra])
    have hB5 : (inlineFunc l F).blocks[cur + 5]? = some
        { body := #[], term := .fail .heap, cold := true } := by
      simpa [expandSite] using hblk 5 (by simp [siteExtra])
    have hB6 : (inlineFunc l F).blocks[cur + 6]? = some
        { params := [dst],
          body := (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray,
          term := relabelTerm (newLabel l F) B.term, cold := false } := by
      simpa [expandSite, lay, hdr] using hblk 6 (by simp [siteExtra])
    let caller₁ : Lir.Frame := { fn, label := i, pos := pre.length + 1, dsts := [dst], env := e₁ }
    have h1call : Lir.step p { mem, ctx, stack := { fn, label := i, pos := pre.length, dsts := dsts₁, env := e₁ } :: t₁ } =
        .next { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 0, env := {} } :: caller₁ :: t₁ } true := by
      unfold Lir.step; simp [hF, hB, hpos₁, hs₁, Lir.evalArgs, Lir.enter, halloc, Rt.Rc.Gen.allocFunc, Lir.bindParams, caller₁]
    cases hhead : mem.read? .w64 (ctx + Lir.dispWord (8 * (cls : Int))) with
    | error _ =>
      exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (.refl _))
        (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hhead]))
    | ok head =>
      have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 0, env := {} } :: caller₁ :: t₁ } =
          .next { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 head } :: caller₁ :: t₁ } false := by
        unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hhead]
      have h2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length, dsts := dsts₂, env := e₂ } :: t₂ } =
          .next { mem, ctx, stack := { fn, label := cur, pos := pre.length + 1, dsts := dsts₂, env := e₂.insert nt head } :: t₂ } false := by
        unfold Lir.step; simp [hF', hB0, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, ctxAddr, headOff, hhead]
      by_cases hh0 : head = 0
      · subst hh0
        have h1_0t : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 0 } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := ({} : Lir.Env).insert 0 0 } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Arg.eval, v, to, w64_eq_iff, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h2_0t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length + 1, dsts := dsts₂, env := e₂.insert nt 0 } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt 0 } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, Lir.evalArgs, hB2, Lir.bindParams]
        cases hbump : mem.read? .w64 (ctx + Lir.dispWord Rt.bumpOff) with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (star_free h1_0t (.refl _))))
            (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hbump]))
        | ok bump =>
          have h1_2_0 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 0, env := ({} : Lir.Env).insert 0 0 } :: caller₁ :: t₁ } =
              .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := (({} : Lir.Env).insert 0 0).insert 2 bump } :: caller₁ :: t₁ } false := by
            unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hbump]
          have h2_2_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 0, dsts := dsts₂, env := e₂.insert nt 0 } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 2, pos := 1, dsts := dsts₂, env := (e₂.insert nt 0).insert (nt + 2) bump } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB2, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, ctxAddr, hbump]
          cases hlim : mem.read? .w64 (ctx + Lir.dispWord Rt.limitOff) with
          | error _ =>
            exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (.refl _)))))
              (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hlim]))
          | ok lim =>
            let e1_2 := ((({} : Lir.Env).insert 0 0).insert 2 bump).insert 3 lim
            let e2_2 := ((e₂.insert nt 0).insert (nt + 2) bump).insert (nt + 3) lim
            have h1_2_1 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 1, env := (({} : Lir.Env).insert 0 0).insert 2 bump } :: caller₁ :: t₁ } =
                .next { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e1_2 } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.ctx, hlim, e1_2]
            have h2_2_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 1, dsts := dsts₂, env := (e₂.insert nt 0).insert (nt + 2) bump } :: t₂ } =
                .next { mem, ctx, stack := { fn, label := cur + 2, pos := 2, dsts := dsts₂, env := e2_2 } :: t₂ } false := by
              unfold Lir.step; simp [hF', hB2, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, ctxAddr, hlim, e2_2]
            let res := Lir.Ovf.addC.eval bump bytes
            cases hovf : res.2 with
            | true =>
              have h1_2t : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e1_2 } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, e1_2, Lir.Arg.eval, v, to, bytes, res, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } = .fail .heap := by
                unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc]
              have h2_2t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 2, dsts := dsts₂, env := e2_2 } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB2, e2_2, Lir.Arg.eval, bytes, res, hovf, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
              have h2_5 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } = .fail .heap := by
                unfold Lir.step; simp [hF', hB5]
              exact .sameReachFinal (c₁ := 1) (c₂ := 0) (by omega) (by simp) (by simp)
                (star_reaches_fail (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (star_free h1_2_1 (star_free h1_2t (.refl _))))))) h1_6)
                (star_reaches_fail (star_free h2_0 (star_free h2_0t (star_free h2_2_0 (star_free h2_2_1 (star_free h2_2t (.refl _)))))) h2_5)
            | false =>
              have h1_2t : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 2, pos := 2, env := e1_2 } :: caller₁ :: t₁ } =
                  .next { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, e1_2, Lir.Arg.eval, v, to, bytes, res, hovf, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
              have h2_2t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 2, pos := 2, dsts := dsts₂, env := e2_2 } :: t₂ } =
                  .next { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB2, e2_2, Lir.Arg.eval, bytes, res, hovf, Lir.takeEdge, Lir.evalArgs, hB3, Lir.bindParams]
              cases hule : Lir.Cond.holds .ule .w64 res.1 lim with
              | false =>
                have h1_3 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } false := by
                  unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, e1_2, Lir.Arg.eval, v, to, hule, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 6, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } = .fail .heap := by
                  unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc]
                have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } =
                    .next { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB3, e2_2, Lir.Arg.eval, hule, Lir.takeEdge, Lir.evalArgs, hB5, Lir.bindParams]
                have h2_5 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 5, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } = .fail .heap := by
                  unfold Lir.step; simp [hF', hB5]
                exact .sameReachFinal (c₁ := 1) (c₂ := 0) (by omega) (by simp) (by simp)
                  (star_reaches_fail (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (star_free h1_2_1 (star_free h1_2t (star_free h1_3 (.refl _)))))))) h1_6)
                  (star_reaches_fail (star_free h2_0 (star_free h2_0t (star_free h2_2_0 (star_free h2_2_1 (star_free h2_2t (star_free h2_3 (.refl _))))))) h2_5)
              | true =>
                have h1_3 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 3, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } =
                    .next { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } false := by
                  unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, e1_2, Lir.Arg.eval, v, to, hule, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
                have h2_3 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 3, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } =
                    .next { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB3, e2_2, Lir.Arg.eval, hule, Lir.takeEdge, Lir.evalArgs, hB4, Lir.bindParams]
                cases hw1 : mem.write? .w64 (ctx + Lir.dispWord Rt.bumpOff) res.1 with
                | error _ =>
                  exact .rawStuckWithin (by omega) (star_reaches_stuck
                    (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (star_free h1_2_1 (star_free h1_2t (star_free h1_3 (.refl _))))))))
                    (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.ctx, hw1]))
                | ok mem1 =>
                  have h1_4_0 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 0, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } =
                      .next { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } false := by
                    unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.ctx, hw1]
                  have h1_4_1 : Lir.step p { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 4, pos := 1, env := e1_2.insert 4 res.1 } :: caller₁ :: t₁ } =
                      .next { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := (e1_2.insert 4 res.1).insert 5 bump } :: caller₁ :: t₁ } false := by
                    unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, e1_2, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                  cases hw2 : mem1.write? .w64 bump hdr with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (star_free h1_2_1 (star_free h1_2t (star_free h1_3 (star_free h1_4_0 (star_free h1_4_1 (.refl _))))))))))
                      (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, lay, hdr, hw2]))
                  | ok mem2 =>
                    have h1_5_0 : Lir.step p { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := (e1_2.insert 4 res.1).insert 5 bump } :: caller₁ :: t₁ } =
                        .next { mem := mem2, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := (e1_2.insert 4 res.1).insert 5 bump } :: caller₁ :: t₁ } false := by
                      unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, lay, hdr, hw2]
                    have h1_5_1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := (e1_2.insert 4 res.1).insert 5 bump } :: caller₁ :: t₁ } =
                        .next { mem := mem2, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst bump } :: t₁ } false := by
                      unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.evalArgs, Lir.Arg.eval, v, caller₁, Lir.bindParams]
                    have h2_4_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 4, pos := 0, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } =
                        .next { mem := mem1, ctx, stack := { fn, label := cur + 4, pos := 1, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } false := by
                      unfold Lir.step; simp [hF', hB4, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, ctxAddr, hw1]
                    have h2_4_1 : Lir.step (inlineProgram l p) { mem := mem1, ctx, stack := { fn, label := cur + 4, pos := 1, dsts := dsts₂, env := e2_2.insert (nt + 4) res.1 } :: t₂ } =
                        .next { mem := mem1, ctx, stack := { fn, label := cur + 6, pos := 0, dsts := dsts₂, env := (e2_2.insert (nt + 4) res.1).insert dst bump } :: t₂ } false := by
                      unfold Lir.step; simp [hF', hB4, e2_2, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hB6, Lir.bindParams]
                    have h2_6_0 : Lir.step (inlineProgram l p) { mem := mem1, ctx, stack := { fn, label := cur + 6, pos := 0, dsts := dsts₂, env := (e2_2.insert (nt + 4) res.1).insert dst bump } :: t₂ } =
                        .next { mem := mem2, ctx, stack := { fn, label := cur + 6, pos := 1, dsts := dsts₂, env := (e2_2.insert (nt + 4) res.1).insert dst bump } :: t₂ } false := by
                      unfold Lir.step; simp [hF', hB6, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                    have hag' : AgreeBelow (freshBase F) (e₁.insert dst bump) ((e2_2.insert (nt + 4) res.1).insert dst bump) :=
                      ((((hag.insert_ge hnt 0).insert_ge (Nat.le_trans hnt (by omega)) bump).insert_ge (Nat.le_trans hnt (by omega)) lim).insert_ge (Nat.le_trans hnt (by omega)) res.1).insert_same dst bump
                    have htop : TopFrameRel l p
                        { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst bump }
                        { fn, label := cur + 6, pos := 1, dsts := dsts₂, env := (e2_2.insert (nt + 4) res.1).insert dst bump } := by
                      simpa [cur, siteExtra, sitePostOff] using
                        TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite hag'
                    exact .sync (Lir.semStep_next.mpr h1call)
                      (star_free h1_0 (star_free h1_0t (star_free h1_2_0 (star_free h1_2_1 (star_free h1_2t (star_free h1_3 (star_free h1_4_0 (star_free h1_4_1 (star_free h1_5_0 (star_free h1_5_1 (.refl _)))))))))))
                      (Lir.semStep_next.mpr h2_0)
                      (star_free h2_0t (star_free h2_2_0 (star_free h2_2_1 (star_free h2_2t (star_free h2_3 (star_free h2_4_0 (star_free h2_4_1 (star_free h2_6_0 (.refl _)))))))))
                      (by decide) ⟨rfl, rfl, .cons htop htail⟩
      · have hhne : (head == 0) = false := beq_false_of_ne hh0
        have h1_0t : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 0, pos := 1, env := ({} : Lir.Env).insert 0 head } :: caller₁ :: t₁ } =
            .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 head } :: caller₁ :: t₁ } false := by
          unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Arg.eval, v, to, w64_eq_iff, hhne, Lir.takeEdge, Lir.evalArgs, Lir.bindParams]
        have h2_0t : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur, pos := pre.length + 1, dsts := dsts₂, env := e₂.insert nt head } :: t₂ } =
            .next { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂.insert nt head } :: t₂ } false := by
          unfold Lir.step; simp [hF', hB0, Lir.Arg.eval, w64_eq_iff, hhne, Lir.takeEdge, Lir.evalArgs, hB1, Lir.bindParams]
        cases hnext : mem.read? .w64 head with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (star_free h1_0t (.refl _))))
            (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hnext]))
        | ok next =>
          have h1_1_0 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 0, env := ({} : Lir.Env).insert 0 head } :: caller₁ :: t₁ } =
              .next { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 head).insert 1 next } :: caller₁ :: t₁ } false := by
            unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, hnext]
          have h2_1_0 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 0, dsts := dsts₂, env := e₂.insert nt head } :: t₂ } =
              .next { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := (e₂.insert nt head).insert (nt + 1) next } :: t₂ } false := by
            unfold Lir.step; simp [hF', hB1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hnext]
          cases hw1 : mem.write? .w64 (ctx + Lir.dispWord (8 * (cls : Int))) next with
          | error _ =>
            exact .rawStuckWithin (by omega) (star_reaches_stuck (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_1_0 (.refl _)))))
              (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.ctx, hw1]))
          | ok mem1 =>
            have h1_1_1 : Lir.step p { mem, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 1, env := (({} : Lir.Env).insert 0 head).insert 1 next } :: caller₁ :: t₁ } =
                .next { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := (({} : Lir.Env).insert 0 head).insert 1 next } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, v, Lir.Addr.eval, Rt.Rc.Procs.ctx, hw1]
            have h1_1_2 : Lir.step p { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 1, pos := 2, env := (({} : Lir.Env).insert 0 head).insert 1 next } :: caller₁ :: t₁ } =
                .next { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := ((({} : Lir.Env).insert 0 head).insert 1 next).insert 5 head } :: caller₁ :: t₁ } false := by
              unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
            cases hw2 : mem1.write? .w64 head hdr with
            | error _ =>
              exact .rawStuckWithin (by omega) (star_reaches_stuck
                (star_charge h1call (star_free h1_0 (star_free h1_0t (star_free h1_1_0 (star_free h1_1_1 (star_free h1_1_2 (.refl _)))))))
                (by unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, lay, hdr, hw2]))
            | ok mem2 =>
              have h1_5_0 : Lir.step p { mem := mem1, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 0, env := ((({} : Lir.Env).insert 0 head).insert 1 next).insert 5 head } :: caller₁ :: t₁ } =
                  .next { mem := mem2, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := ((({} : Lir.Env).insert 0 head).insert 1 next).insert 5 head } :: caller₁ :: t₁ } false := by
                unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, Rt.Rc.Procs.cellAddr, Lir.dispWord, lay, hdr, hw2]
              have h1_5_1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.allocProc idx, label := 5, pos := 1, env := ((({} : Lir.Env).insert 0 head).insert 1 next).insert 5 head } :: caller₁ :: t₁ } =
                  .next { mem := mem2, ctx, stack := { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst head } :: t₁ } false := by
                unfold Lir.step; simp [halloc, Rt.Rc.Gen.allocFunc, Lir.evalArgs, Lir.Arg.eval, v, caller₁, Lir.bindParams]
              have h2_1_1 : Lir.step (inlineProgram l p) { mem, ctx, stack := { fn, label := cur + 1, pos := 1, dsts := dsts₂, env := (e₂.insert nt head).insert (nt + 1) next } :: t₂ } =
                  .next { mem := mem1, ctx, stack := { fn, label := cur + 1, pos := 2, dsts := dsts₂, env := (e₂.insert nt head).insert (nt + 1) next } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, ctxAddr, headOff, hw1]
              have h2_1_2 : Lir.step (inlineProgram l p) { mem := mem1, ctx, stack := { fn, label := cur + 1, pos := 2, dsts := dsts₂, env := (e₂.insert nt head).insert (nt + 1) next } :: t₂ } =
                  .next { mem := mem1, ctx, stack := { fn, label := cur + 6, pos := 0, dsts := dsts₂, env := ((e₂.insert nt head).insert (nt + 1) next).insert dst head } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB1, Lir.takeEdge, Lir.evalArgs, Lir.Arg.eval, hB6, Lir.bindParams]
              have h2_6_0 : Lir.step (inlineProgram l p) { mem := mem1, ctx, stack := { fn, label := cur + 6, pos := 0, dsts := dsts₂, env := ((e₂.insert nt head).insert (nt + 1) next).insert dst head } :: t₂ } =
                  .next { mem := mem2, ctx, stack := { fn, label := cur + 6, pos := 1, dsts := dsts₂, env := ((e₂.insert nt head).insert (nt + 1) next).insert dst head } :: t₂ } false := by
                unfold Lir.step; simp [hF', hB6, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
              have hag' : AgreeBelow (freshBase F) (e₁.insert dst head) (((e₂.insert nt head).insert (nt + 1) next).insert dst head) :=
                ((hag.insert_ge hnt head).insert_ge (Nat.le_trans hnt (by omega)) next).insert_same dst head
              have htop : TopFrameRel l p
                  { fn, label := i, pos := pre.length + 1, dsts := [], env := e₁.insert dst head }
                  { fn, label := cur + 6, pos := 1, dsts := dsts₂, env := ((e₂.insert nt head).insert (nt + 1) next).insert dst head } := by
                simpa [cur, siteExtra, sitePostOff] using
                  TopFrameRel.wrapAfter (m := 0) (dsts₁ := []) (dsts₂ := dsts₂) hp hF hB hsite hag'
              exact .sync (Lir.semStep_next.mpr h1call)
                (star_free h1_0 (star_free h1_0t (star_free h1_1_0 (star_free h1_1_1 (star_free h1_1_2 (star_free h1_5_0 (star_free h1_5_1 (.refl _))))))))
                (Lir.semStep_next.mpr h2_0)
                (star_free h2_0t (star_free h2_1_0 (star_free h2_1_1 (star_free h2_1_2 (star_free h2_6_0 (.refl _))))))
                (by decide) ⟨rfl, rfl, .cons htop htail⟩

/-! ## Unified step match -/

private theorem step_match {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p)
    {s₁ s₂ : Lir.State} (hrel : WStateRel l p s₁ s₂) :
    MatchedStep l p s₁ s₂ := by
  obtain ⟨hmem, hctx, hst⟩ := hrel
  cases s₁ with
  | mk mem ctx stack₁ =>
  cases s₂ with
  | mk mem₂ ctx₂ stack₂ =>
  simp only at hmem hctx
  subst hmem hctx
  cases hst with
  | nil => exact .rawStuck (by unfold Lir.step; rfl)
  | @cons fr₁ fr₂ t₁ t₂ htop htail =>
    cases htop with
    | other hnp =>
      have hFget := inlineProgram_get_not_prunable (p := p) hnp
      cases hF : p.funcs[fr₁.fn]? with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF])
      | some F =>
        have hF' : (inlineProgram l p).funcs[fr₁.fn]? = some F := by rw [hFget, hF]
        cases hB : F.blocks[fr₁.label]? with
        | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB])
        | some B =>
          by_cases hpos : fr₁.pos < B.body.size
          · cases hs : B.body[fr₁.pos] with
            | assign x r =>
              cases hex : Lir.Stmt.exec fr₁.env mem ctx (.assign x r) with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
              | some pr =>
                have h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₁ } false := by
                  unfold Lir.step; simp [hF, hB, hpos, hs, hex]
                have h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB, hpos, hs, hex]
                exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _)
                  (by decide) ⟨rfl, rfl, .cons (.other hnp) htail⟩
            | limb r1 r2 op =>
              cases hex : Lir.Stmt.exec fr₁.env mem ctx (.limb r1 r2 op) with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
              | some pr =>
                have h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₁ } false := by
                  unfold Lir.step; simp [hF, hB, hpos, hs, hex]
                have h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB, hpos, hs, hex]
                exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _)
                  (by decide) ⟨rfl, rfl, .cons (.other hnp) htail⟩
            | store w m a =>
              cases hex : Lir.Stmt.exec fr₁.env mem ctx (.store w m a) with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
              | some pr =>
                have h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₁ } false := by
                  unfold Lir.step; simp [hF, hB, hpos, hs, hex]
                have h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                    .next { mem := pr.2, ctx, stack := { fr₁ with pos := fr₁.pos + 1, env := pr.1 } :: t₂ } false := by
                  unfold Lir.step; simp [hF', hB, hpos, hs, hex]
                exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _)
                  (by decide) ⟨rfl, rfl, .cons (.other hnp) htail⟩
            | call rs g as =>
              cases ha : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, ha])
              | some vs =>
                cases hent : Lir.enter p g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, ha, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, htop'⟩ := (enter_rel l p g vs).1 callee₁ hent
                  have h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                      .next { mem, ctx, stack := callee₁ :: { fr₁ with pos := fr₁.pos + 1, dsts := rs } :: t₁ } true := by
                    unfold Lir.step; simp [hF, hB, hpos, hs, ha, hent]
                  have h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                      .next { mem, ctx, stack := callee₂ :: { fr₁ with pos := fr₁.pos + 1, dsts := rs } :: t₂ } true := by
                    unfold Lir.step; simp [hF', hB, hpos, hs, ha, hent₂]
                  exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _)
                    (by decide) ⟨rfl, rfl, .cons htop' (.cons (.other hnp) htail)⟩
          · have matchEdge : ∀ (ρ : Lir.Env) (e : Lir.Edge),
                Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                  Lir.takeEdge F { mem, ctx, stack := fr₁ :: t₁ } fr₁ t₁ ρ e →
                Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                  Lir.takeEdge F { mem, ctx, stack := fr₁ :: t₂ } fr₁ t₂ ρ e →
                MatchedStep l p { mem, ctx, stack := fr₁ :: t₁ } { mem, ctx, stack := fr₁ :: t₂ } := by
              intro ρ e h1 h2
              unfold Lir.takeEdge at h1 h2
              cases ha : Lir.evalArgs ρ e.args with
              | none => exact .rawStuck (by rw [h1]; simp [ha])
              | some vals =>
                cases htb : F.blocks[e.target]? with
                | none => exact .rawStuck (by rw [h1]; simp [ha, htb])
                | some target =>
                  cases hbp : Lir.bindParams ρ target.params vals with
                  | none => exact .rawStuck (by rw [h1]; simp [ha, htb, hbp])
                  | some ρ' =>
                    have h1' : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                        .next { mem, ctx, stack := { fr₁ with label := e.target, pos := 0, env := ρ' } :: t₁ }
                          (decide (e.target ≤ fr₁.label)) := by
                      rw [h1]; simp [ha, htb, hbp]
                    have h2' : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                        .next { mem, ctx, stack := { fr₁ with label := e.target, pos := 0, env := ρ' } :: t₂ }
                          (decide (e.target ≤ fr₁.label)) := by
                      rw [h2]; simp [ha, htb, hbp]
                    exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _)
                      (by omega) ⟨rfl, rfl, .cons (.other hnp) htail⟩
            cases ht : B.term with
            | jump e =>
              exact matchEdge fr₁.env e
                (by unfold Lir.step; simp [hF, hB, hpos, ht])
                (by unfold Lir.step; simp [hF', hB, hpos, ht])
            | br cond w a b' tr fa =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb])
                | some vb =>
                  cases hc : cond.holds w va vb with
                  | true =>
                    exact matchEdge fr₁.env tr
                      (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, hc])
                      (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, hc])
                  | false =>
                    exact matchEdge fr₁.env fa
                      (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, hc])
                      (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, hc])
            | brOvf op x a b' ok ovf =>
              cases ha : a.eval fr₁.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
              | some va =>
                cases hb : b'.eval fr₁.env with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb])
                | some vb =>
                  let res := op.eval va vb
                  let ρ₁ := fr₁.env.insert x res.1
                  cases hc : res.2 with
                  | true =>
                    exact matchEdge ρ₁ ovf
                      (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, res, ρ₁, hc])
                      (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, res, ρ₁, hc])
                  | false =>
                    exact matchEdge ρ₁ ok
                      (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, res, ρ₁, hc])
                      (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, res, ρ₁, hc])
            | ret as =>
              cases ha : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
              | some vals =>
                exact matched_of_ret (vals := vals)
                  (by unfold Lir.step; simp [hF, hB, hpos, ht, ha]; cases t₁ <;> rfl)
                  (by unfold Lir.step; simp [hF', hB, hpos, ht, ha]; cases t₂ <;> rfl)
                  htail
            | tail g as =>
              cases ha : Lir.evalArgs fr₁.env as with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
              | some vs =>
                cases hent : Lir.enter p g vs with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hent])
                | some callee₁ =>
                  obtain ⟨callee₂, hent₂, htop'⟩ := (enter_rel l p g vs).1 callee₁ hent
                  have h1 : Lir.step p { mem, ctx, stack := fr₁ :: t₁ } =
                      .next { mem, ctx, stack := callee₁ :: t₁ } true := by
                    unfold Lir.step; simp [hF, hB, hpos, ht, ha, hent]
                  have h2 : Lir.step (inlineProgram l p) { mem, ctx, stack := fr₁ :: t₂ } =
                      .next { mem, ctx, stack := callee₂ :: t₂ } true := by
                    unfold Lir.step; simp [hF', hB, hpos, ht, ha, hent₂]
                  exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _)
                    (by decide) ⟨rfl, rfl, .cons htop' htail⟩
            | fail r =>
              exact .sameFinal (r := .resource r)
                (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos, ht]; exact .fail)
                (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hpos, ht]; exact .fail)
            | trap =>
              exact .sameFinal (r := .trap)
                (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos, ht]; exact .trap)
                (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hpos, ht]; exact .trap)
    | @wrapInvalid fn F i pos dsts₁ dsts₂ e₁ e₂ hp hF hnone =>
      exact .rawStuck (by unfold Lir.step; simp [hF, hnone])
    | @wrapUnexpanded fn F i pos dsts₁ dsts₂ e₁ e₂ B hp hF hB hnone hag =>
      have hB' : (inlineFunc l F).blocks[newLabel l F i]? =
          some { B with term := relabelTerm (newLabel l F) B.term } := by
        simpa [expandBlock, hnone] using inlineFunc_block_at l F hB (k := 0) (by omega)
      by_cases hpos : pos < B.body.size
      · exact step_match_stmt hp hF hB hB' hpos hpos rfl rfl hag htail
          (fun hag' => .wrapUnexpanded hp hF hB hnone hag')
          (fun _ => .wrapUnexpanded hp hF hB hnone hag)
      · exact step_match_term hp hF hB hB' hpos hpos rfl hag htail
    | @wrapBefore fn F i pos dsts₁ dsts₂ e₁ e₂ B pre post site hp hF hB hsite hle hag =>
      by_cases hlt : pos < pre.length
      · obtain ⟨s0, hbody, _⟩ := findUniqueSite_spec hsite
        have hpos₁ : pos < B.body.size := by
          have := congrArg List.length hbody; simp at this; omega
        have hblk0 := inlineFunc_block_at l F hB (k := 0) (by omega)
        simp only [Nat.add_zero, expandBlock, hsite] at hblk0
        cases hsc : site with
        | isUnique dst x =>
          rw [hsc] at hblk0 hsite
          have hB' : (inlineFunc l F).blocks[newLabel l F i]? = some
              { params := B.params, body := pre.toArray,
                term := .br .tnz .w64 (.v x) (.imm 1) ⟨newLabel l F i + 2, []⟩ ⟨newLabel l F i + 1, []⟩, cold := B.cold } := by
            simpa [expandSite] using hblk0
          have hsEq : B.body[pos] = pre.toArray[pos] := by
            have h1 : B.body.toList[pos]? = pre[pos]? := by rw [hbody, List.getElem?_append_left hlt]
            simp [hpos₁, hlt] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [hlt]) hsEq rfl hag htail
            (fun hag' => .wrapBefore hp hF hB hsite (by omega) hag')
            (fun _ => .wrapBefore hp hF hB hsite (by omega) hag)
        | inc x =>
          rw [hsc] at hblk0 hsite
          have hB' : (inlineFunc l F).blocks[newLabel l F i]? = some
              { params := B.params, body := pre.toArray,
                term := .br .tnz .w64 (.v x) (.imm 1) ⟨newLabel l F i + 5, []⟩ ⟨newLabel l F i + 1, []⟩, cold := B.cold } := by
            simpa [expandSite] using hblk0
          have hsEq : B.body[pos] = pre.toArray[pos] := by
            have h1 : B.body.toList[pos]? = pre[pos]? := by rw [hbody, List.getElem?_append_left hlt]
            simp [hpos₁, hlt] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [hlt]) hsEq rfl hag htail
            (fun hag' => .wrapBefore hp hF hB hsite (by omega) hag')
            (fun _ => .wrapBefore hp hF hB hsite (by omega) hag)
        | dec x =>
          rw [hsc] at hblk0 hsite
          have hB' : (inlineFunc l F).blocks[newLabel l F i]? = some
              { params := B.params, body := pre.toArray,
                term := .br .tnz .w64 (.v x) (.imm 1) ⟨newLabel l F i + 5, []⟩ ⟨newLabel l F i + 1, []⟩, cold := B.cold } := by
            simpa [expandSite] using hblk0
          have hsEq : B.body[pos] = pre.toArray[pos] := by
            have h1 : B.body.toList[pos]? = pre[pos]? := by rw [hbody, List.getElem?_append_left hlt]
            simp [hpos₁, hlt] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [hlt]) hsEq rfl hag htail
            (fun hag' => .wrapBefore hp hF hB hsite (by omega) hag')
            (fun _ => .wrapBefore hp hF hB hsite (by omega) hag)
        | alloc dst idx lay cls =>
          rw [hsc] at hblk0 hsite
          let nt := blockTmpBase l F i
          let headOff := Int.ofNat (8 * cls)
          have hB' : (inlineFunc l F).blocks[newLabel l F i]? = some
              { params := B.params,
                body := (pre ++ [Lir.Stmt.assign nt (.load .w64 .zero (ctxAddr headOff))]).toArray,
                term := .br .eq .w64 (.v nt) (.imm 0) ⟨newLabel l F i + 2, []⟩ ⟨newLabel l F i + 1, []⟩, cold := false } := by
            simpa [expandSite, nt, headOff] using hblk0
          have hpos₂ : pos < (pre ++ [Lir.Stmt.assign nt (.load .w64 .zero (ctxAddr headOff))]).toArray.size := by
            simp; omega
          have hsEq : B.body[pos] = (pre ++ [Lir.Stmt.assign nt (.load .w64 .zero (ctxAddr headOff))]).toArray[pos] := by
            have h1 : B.body.toList[pos]? = pre[pos]? := by rw [hbody, List.getElem?_append_left hlt]
            simp [hpos₁, hlt] at h1
            exact h1.trans (List.getElem_append_left hlt).symm
          exact step_match_stmt hp hF hB hB' hpos₁ hpos₂ hsEq rfl hag htail
            (fun hag' => .wrapBefore hp hF hB hsite (by omega) hag')
            (fun _ => .wrapBefore hp hF hB hsite (by omega) hag)
      · have heq : pos = pre.length := by omega
        subst heq
        exact step_match_site hr hp hF hB hsite hag htail
    | @wrapAfter fn F i m dsts₁ dsts₂ e₁ e₂ B pre post site hp hF hB hsite hag =>
      obtain ⟨s0, hbody, _⟩ := findUniqueSite_spec hsite
      have hblkj := inlineFunc_block_at l F hB (k := siteExtra site) (by simp [blockExtra, hsite])
      simp only [expandBlock, hsite] at hblkj
      have hsz₁ : B.body.size = pre.length + 1 + post.length := by
        have := congrArg List.length hbody; simp at this; omega
      cases hsc : site with
      | isUnique dst x =>
        rw [hsc] at hblkj hsite
        have hB' : (inlineFunc l F).blocks[newLabel l F i + 3]? = some
            { params := [dst], body := post.toArray,
              term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
          simpa [expandSite, siteExtra] using hblkj
        by_cases hm : m < post.length
        · have hpos₁ : pre.length + 1 + m < B.body.size := by omega
          have hsEq : B.body[pre.length + 1 + m] = post.toArray[m] := by
            have h1 : B.body.toList[pre.length + 1 + m]? = post[m]? := by
              rw [hbody, List.getElem?_append_right (by omega)]
              have : pre.length + 1 + m - pre.length = m + 1 := by omega
              rw [this]; rfl
            simp [hpos₁, hm] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [sitePostOff, hm]) hsEq (by simp [sitePostOff]) hag htail
            (fun hag' => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              TopFrameRel.wrapAfter (m := m + 1) (dsts₁ := dsts₁) (dsts₂ := dsts₂) hp hF hB hsite hag')
            (fun _ => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              FrameRel.wrapAfter (m := m + 1) hp hF hB hsite hag)
        · exact step_match_term hp hF hB hB' (by omega) (by simp [sitePostOff]; omega) rfl hag htail
      | inc x =>
        rw [hsc] at hblkj hsite
        have hB' : (inlineFunc l F).blocks[newLabel l F i + 5]? = some
            { body := post.toArray, term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
          simpa [expandSite, siteExtra] using hblkj
        by_cases hm : m < post.length
        · have hpos₁ : pre.length + 1 + m < B.body.size := by omega
          have hsEq : B.body[pre.length + 1 + m] = post.toArray[m] := by
            have h1 : B.body.toList[pre.length + 1 + m]? = post[m]? := by
              rw [hbody, List.getElem?_append_right (by omega)]
              have : pre.length + 1 + m - pre.length = m + 1 := by omega
              rw [this]; rfl
            simp [hpos₁, hm] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [sitePostOff, hm]) hsEq (by simp [sitePostOff]) hag htail
            (fun hag' => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              TopFrameRel.wrapAfter (m := m + 1) (dsts₁ := dsts₁) (dsts₂ := dsts₂) hp hF hB hsite hag')
            (fun _ => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              FrameRel.wrapAfter (m := m + 1) hp hF hB hsite hag)
        · exact step_match_term hp hF hB hB' (by omega) (by simp [sitePostOff]; omega) rfl hag htail
      | dec x =>
        rw [hsc] at hblkj hsite
        have hB' : (inlineFunc l F).blocks[newLabel l F i + 5]? = some
            { body := post.toArray, term := relabelTerm (newLabel l F) B.term, cold := B.cold } := by
          simpa [expandSite, siteExtra] using hblkj
        by_cases hm : m < post.length
        · have hpos₁ : pre.length + 1 + m < B.body.size := by omega
          have hsEq : B.body[pre.length + 1 + m] = post.toArray[m] := by
            have h1 : B.body.toList[pre.length + 1 + m]? = post[m]? := by
              rw [hbody, List.getElem?_append_right (by omega)]
              have : pre.length + 1 + m - pre.length = m + 1 := by omega
              rw [this]; rfl
            simp [hpos₁, hm] at h1; exact h1
          exact step_match_stmt hp hF hB hB' hpos₁ (by simp [sitePostOff, hm]) hsEq (by simp [sitePostOff]) hag htail
            (fun hag' => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              TopFrameRel.wrapAfter (m := m + 1) (dsts₁ := dsts₁) (dsts₂ := dsts₂) hp hF hB hsite hag')
            (fun _ => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              FrameRel.wrapAfter (m := m + 1) hp hF hB hsite hag)
        · exact step_match_term hp hF hB hB' (by omega) (by simp [sitePostOff]; omega) rfl hag htail
      | alloc dst idx lay cls =>
        rw [hsc] at hblkj hsite
        let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
        have hB' : (inlineFunc l F).blocks[newLabel l F i + 6]? = some
            { params := [dst],
              body := (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray,
              term := relabelTerm (newLabel l F) B.term, cold := false } := by
          simpa [expandSite, siteExtra, hdr] using hblkj
        by_cases hm : m < post.length
        · have hpos₁ : pre.length + 1 + m < B.body.size := by omega
          have hpos₂ : 1 + m < (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray.size := by
            simp; omega
          have hsEq : B.body[pre.length + 1 + m] =
              (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray[1 + m] := by
            have h1 : B.body.toList[pre.length + 1 + m]? = post[m]? := by
              rw [hbody, List.getElem?_append_right (by omega)]
              have : pre.length + 1 + m - pre.length = m + 1 := by omega
              rw [this]; rfl
            simp [hpos₁, hm] at h1
            have h2 : (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray[1 + m] = post[m] := by
              change (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post)[1 + m] = post[m]
              have hlt2 : 1 + m < (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).length := by simp; omega
              have hq : (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post)[1 + m]? = some post[m] := by
                rw [show 1 + m = m + 1 by omega]; simp [hm]
              rw [List.getElem?_eq_getElem hlt2] at hq
              exact Option.some.inj hq
            exact h1.trans h2.symm
          exact step_match_stmt hp hF hB hB' hpos₁ hpos₂ hsEq rfl hag htail
            (fun hag' => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              TopFrameRel.wrapAfter (m := m + 1) (dsts₁ := dsts₁) (dsts₂ := dsts₂) hp hF hB hsite hag')
            (fun _ => by simpa [siteExtra, sitePostOff, Nat.add_assoc] using
              FrameRel.wrapAfter (m := m + 1) hp hF hB hsite hag)
        · exact step_match_term hp hF hB hB' (by omega) (by simp [sitePostOff]; omega) rfl hag htail

/-! ## Clocked forward & backward runs and simulation theorem -/

private theorem forward_run {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p) :
    ∀ fuel k s₁ s₂ r, WStateRel l p s₁ s₂ →
      Sem.runClocked (Lir.semStep p) fuel k s₁ = r →
      r ≠ .timeout → r ≠ .stuck →
      ∃ k', Sem.Reaches (Lir.semStep (inlineProgram l p)) s₂ k' r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hns
    have hr1 : Sem.Reaches (Lir.semStep p) s₁ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      have h2 : Sem.Reaches (Lir.semStep p) s₁ k .stuck := .final (by rw [Lir.semStep, hst]; exact .stuck)
      exact absurd (hr1.det h2) hns
    | @rawStuckWithin c₁ _ hst =>
      have h2 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) .stuck := hst.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      exact absurd (h1.det h2) hns
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr1.det (.final hf₁)
      subst heq
      exact ⟨0, .final hf₂⟩
    | @sameReachFinal c₁ c₂ r₀ _ hr0nt _ hreach₁ hreach₂ =>
      have h1 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      have h2 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) r₀ := hreach₁.mono hr0nt (Nat.le_max_right k c₁)
      have heq : r = r₀ := h1.det h2
      subst heq
      exact ⟨c₂, hreach₂⟩
    | sync hs₁ hstar₁ hs₂ hstar₂ _ hrel' =>
      obtain ⟨fuel', k', hflt, _, hrun'⟩ := Inline.runClocked_star_inv_lt hs₁ hstar₁ hrun hnt
      obtain ⟨k₂, hreach₂⟩ := ih fuel' hflt k' _ _ r hrel' hrun' hnt hns
      exact ⟨_, Inline.reaches_of_star_reaches (Sem.Star.head hs₂ hstar₂) hreach₂⟩

private theorem backward_run {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p) :
    ∀ fuel k s₁ s₂ r, WStateRel l p s₁ s₂ →
      Sem.runClocked (Lir.semStep (inlineProgram l p)) fuel k s₂ = r →
      r ≠ .timeout → (∀ fail, r ≠ .resource fail) →
      ∃ r₁, r₁ ≠ .timeout ∧ Sem.Reaches (Lir.semStep p) s₁ (k + 3 * fuel) r₁ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hnr
    have hfuelPos : 1 ≤ fuel := by
      cases fuel with
      | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hnt
      | succ _ => omega
    have hr2 : Sem.Reaches (Lir.semStep (inlineProgram l p)) s₂ k r := Sem.runClocked_sound hrun hnt
    cases step_match hr hrel with
    | rawStuck hst =>
      exact ⟨.stuck, by simp, .final (by rw [Lir.semStep, hst]; exact .stuck)⟩
    | rawStuckWithin hc hst =>
      exact ⟨.stuck, by simp, hst.mono (by simp) (by omega)⟩
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr2.det (.final hf₂)
      subst heq
      exact ⟨r, hnt, .final hf₁⟩
    | @sameReachFinal c₁ c₂ r₀ hc₁ hr0nt _ hreach₁ hreach₂ =>
      have h1 : Sem.Reaches (Lir.semStep (inlineProgram l p)) s₂ (max k c₂) r := hr2.mono hnt (Nat.le_max_left k c₂)
      have h2 : Sem.Reaches (Lir.semStep (inlineProgram l p)) s₂ (max k c₂) r₀ := hreach₂.mono hr0nt (Nat.le_max_right k c₂)
      have heq : r = r₀ := h1.det h2
      subst heq
      exact ⟨r, hnt, hreach₁.mono hnt (by omega)⟩
    | @sync s₁' s₂' s₁'' s₂'' b₁ b₂ c₁ c₂ hs₁ hstar₁ hs₂ hstar₂ hchg hrel' =>
      obtain ⟨fuel', k', hflt, hkEq, hrun'⟩ := Inline.runClocked_star_inv_lt hs₂ hstar₂ hrun hnt
      obtain ⟨r₁, hr₁nt, hreach₁⟩ := ih fuel' hflt k' s₁'' s₂'' r hrel' hrun' hnt hnr
      have htotal := Inline.reaches_of_star_reaches (Sem.Star.head hs₁ hstar₁) hreach₁
      exact ⟨r₁, hr₁nt, htotal.mono hr₁nt (by omega)⟩

/-- Exact forward preservation of any non-timeout, non-stuck `Lir.eval` outcome across `InlineWrappers.inlineProgram`. -/
theorem inlineProgram_forward_eq {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p)
    {k : Nat} {args : List Lir.Word} {mem : X86.Memory} {ctx : Lir.Word}
    (hnt : Lir.eval p k args mem ctx ≠ .timeout)
    (hns : Lir.eval p k args mem ctx ≠ .stuck) :
    ∃ k', Lir.eval (inlineProgram l p) k' args mem ctx = Lir.eval p k args mem ctx := by
  let q := inlineProgram l p
  have hmain : q.main = p.main := rfl
  obtain ⟨heFwd, _⟩ := enter_rel l p p.main args
  cases hent : Lir.enter p p.main args with
  | none => exact absurd (by simp [Lir.eval, Lir.State.initial, hent]) hns
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, htop⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial p args mem ctx = some s₁ := by simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial q args mem ctx = some s₂ := by simp [Lir.State.initial, hmain, q, hent₂, s₂]
    have hrun : Sem.runClocked (Lir.semStep p) (Lir.fuelFor p k) k s₁ = Lir.eval p k args mem ctx := by
      rw [Lir.eval_eq, hinit₁]
    obtain ⟨k', hreach₂⟩ := forward_run hr (Lir.fuelFor p k) k s₁ s₂ _ ⟨rfl, rfl, .cons htop .nil⟩ hrun hnt hns
    exact ⟨k', (Lir.runs_eval hinit₂).eq hreach₂⟩

/-- **`InlineWrappers.inlineProgram l p` simulates `p` with exact value and memory equality.** -/
theorem inlineProgram_sim {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq (fun k => k + 3 * Lir.fuelFor (inlineProgram l p) k)
      (fun k => Lir.eval p k args mem ctx)
      (fun k => Lir.eval (inlineProgram l p) k args mem ctx) := by
  let q := inlineProgram l p
  have hmain : q.main = p.main := rfl
  obtain ⟨heFwd, heNone⟩ := enter_rel l p p.main args
  cases hent : Lir.enter p p.main args with
  | none =>
    have hent₂ : Lir.enter q q.main args = none := by rw [hmain]; exact heNone.mp hent
    have he1 : ∀ k, Lir.eval p k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent]
    have he2 : ∀ k, Lir.eval q k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent₂]
    exact {
      forward := fun k _ => ⟨k, by rw [he1, he2]; exact .stuck⟩
      timeout := fun k hk => by rw [he1] at hk; cases hk }
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, htop⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial p args mem ctx = some s₁ := by simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial q args mem ctx = some s₂ := by simp [Lir.State.initial, hmain, q, hent₂, s₂]
    have hruns₁ := Lir.runs_eval hinit₁
    have hruns₂ := Lir.runs_eval hinit₂
    have hrel : WStateRel l p s₁ s₂ := ⟨rfl, rfl, .cons htop .nil⟩
    exact {
      forward := fun k hk => by
        by_cases hst1 : Lir.eval p k args mem ctx = .stuck
        · exact ⟨0, hst1 ▸ .stuck⟩
        · have hrun : Sem.runClocked (Lir.semStep p) (Lir.fuelFor p k) k s₁ =
              Lir.eval p k args mem ctx := by
            rw [Lir.eval_eq, hinit₁]
          obtain ⟨k', hreach₂⟩ := forward_run hr (Lir.fuelFor p k) k s₁ s₂ _ hrel hrun hk hst1
          exact ⟨k', hruns₂.eq hreach₂ ▸ Sem.Result.Refines.refl (fun _ => rfl)⟩
      timeout := fun k hk => by
        by_cases hto : Lir.eval q k args mem ctx = .timeout
        · exact .inl hto
        · by_cases hres : ∃ fail, Lir.eval q k args mem ctx = .resource fail
          · exact .inr hres
          · have hres' : ∀ fail, Lir.eval q k args mem ctx ≠ .resource fail :=
              fun fail h => hres ⟨fail, h⟩
            have hrun₂ : Sem.runClocked (Lir.semStep q) (Lir.fuelFor q k) k s₂ =
                Lir.eval q k args mem ctx := by
              rw [Lir.eval_eq, hinit₂]
            obtain ⟨r₁, hr₁nt, hreach₁⟩ := backward_run hr (Lir.fuelFor q k) k s₁ s₂ _ hrel hrun₂ hto hres'
            have hto₁ : Sem.Reaches (Lir.semStep p) s₁ (k + 3 * Lir.fuelFor q k) .timeout :=
              hk ▸ hruns₁ (k + 3 * Lir.fuelFor q k)
            exact absurd (hreach₁.det hto₁) hr₁nt }

theorem inlineProgram_sim_clock {l : Layout} {p : Lir.Program}
    (hr : WrapperRuntime l p)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    {f : Nat → Nat} (hf : ∀ k, k + 3 * Lir.fuelFor (inlineProgram l p) k ≤ f k) :
    Sem.Sim Eq f
      (fun k => Lir.eval p k args mem ctx)
      (fun k => Lir.eval (inlineProgram l p) k args mem ctx) :=
  let hsim := inlineProgram_sim hr args mem ctx
  { forward := hsim.forward
    timeout := fun k hk => by
      apply hsim.timeout k
      by_cases h0 : Lir.eval p (k + 3 * Lir.fuelFor (inlineProgram l p) k) args mem ctx = .timeout
      · exact h0
      · have heq := Lir.eval_mono p args mem ctx (hf k) h0
        dsimp only at heq
        rw [hk] at heq
        exact absurd heq.symm h0 }

/-! ## Size monotonicity (`p.size ≤ (inlineProgram l p).size`) -/

private theorem expandBlock_size_ge (l : Layout) (rel : Lir.Label → Lir.Label) (cur nextTmp : Nat)
    (b : Lir.Block) :
    b.size ≤ ((expandBlock l rel cur nextTmp b).map Lir.Block.size).sum := by
  unfold expandBlock
  cases hf : findUniqueSite l b.body.toList with
  | none =>
    simp [Lir.Block.size]
  | some triple =>
    rcases triple with ⟨pre, site, post⟩
    obtain ⟨s0, hbody, _⟩ := findUniqueSite_spec hf
    have hsz : b.body.size = pre.length + 1 + post.length := by
      have := congrArg List.length hbody; simp at this; omega
    cases site <;> simp [expandSite, Lir.Block.size, hsz] <;> omega

private theorem expandBlocks_size_ge (l : Layout) (rel : Lir.Label → Lir.Label) :
    ∀ (bs : List Lir.Block) (cur nextTmp : Nat),
      (bs.map Lir.Block.size).sum ≤ ((expandBlocks l rel bs cur nextTmp).map Lir.Block.size).sum
  | [], _, _ => Nat.le_refl _
  | b :: bs, cur, nextTmp => by
    simp only [expandBlocks, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have h1 := expandBlock_size_ge l rel cur nextTmp b
    have h2 := expandBlocks_size_ge l rel bs (cur + 1 + blockExtra l b) (nextTmp + blockTemps l b)
    omega

theorem inlineFunc_size_ge (l : Layout) (F : Lir.Func) : F.size ≤ (inlineFunc l F).size := by
  rw [Inline.func_size_eq_sum, Inline.func_size_eq_sum]
  simpa [inlineFunc] using expandBlocks_size_ge l (newLabel l F) F.blocks.toList 0 (freshBase F)

private theorem list_sum_map_le_pt {α : Type} (f g : α → Nat) :
    ∀ (xs ys : List α) (hlen : xs.length = ys.length),
      (∀ i (hi : i < xs.length), f xs[i] ≤ g (ys[i]'(by omega))) →
      (xs.map f).sum ≤ (ys.map g).sum
  | [], [], _, _ => Nat.le_refl _
  | x :: xs, y :: ys, hlen, hpt => by
    simp only [List.map_cons, List.sum_cons]
    have h0 := hpt 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := list_sum_map_le_pt f g xs ys (by simpa using hlen) (fun i hi => by
      have := hpt (i + 1) (by simp; omega)
      simpa using this)
    omega

theorem inlineProgram_size_ge (l : Layout) (p : Lir.Program) :
    p.size ≤ (inlineProgram l p).size := by
  rw [Inline.program_size_eq_sum, Inline.program_size_eq_sum]
  exact list_sum_map_le_pt Lir.Func.size Lir.Func.size p.funcs.toList (inlineProgram l p).funcs.toList
    (by simp [inlineProgram]) (fun i hi => by
      have hi' : i < (inlineProgram l p).funcs.size := by simpa [inlineProgram] using hi
      have hi1 : i < p.funcs.size := by simpa using hi
      by_cases hp : Prune.isPrunableReuse l i = true
      · have hget := inlineProgram_get_prunable (p := p) hp
        rw [Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hi1] at hget
        simp only [Option.map_some, Option.some.injEq] at hget
        simpa [hget] using inlineFunc_size_ge l (p.funcs[i]'hi1)
      · have hnp : Prune.isPrunableReuse l i = false := Bool.eq_false_iff.mpr hp
        have hget := inlineProgram_get_not_prunable (p := p) hnp
        rw [Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hi1] at hget
        simp only [Option.some.injEq] at hget
        simp [hget])

theorem fuelFor_le_inlineProgram (l : Layout) (p : Lir.Program) (k : Nat) :
    Lir.fuelFor p k ≤ Lir.fuelFor (inlineProgram l p) k := by
  unfold Lir.fuelFor
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (inlineProgram_size_ge l p) 1)

end IxCC.Cfg.Rc.InlineWrappers
