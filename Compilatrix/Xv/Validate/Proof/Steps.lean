import Compilatrix.Xv.Validate.Proof.Lookup
import Compilatrix.Sem.Smallstep

/-!
# Xl steps

Lemmas about the Xl semantics the simulation uses: a non-call instruction
is one silent step, a run of edits is silent steps (`xl_edits`), a callee
starts with its arguments where the entry convention puts them
(`entry_agree`), and after a return the caller's abstract state at the
return point agrees with the returned registers (`call_agree`, CompCert's
`return_regs` discipline, 05 §3).
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.Xv.Alloc (Edit Output BlockOut)
open Compilatrix.Xv
open Compilatrix.Xv.Xl (WriteOk)

/-! ## Register files -/

theorem regs_size_foldl_set :
    ∀ (ps : List (X86.GPR × Word)) (rs : Xl.Regs),
      (ps.foldl (fun rs (d : X86.GPR × Word) => rs.set d.1 (some d.2)) rs).size = rs.size
  | [], _ => rfl
  | d :: ps, rs => by simp only [List.foldl_cons]; rw [regs_size_foldl_set, Xl.Regs.size_set]

theorem get_foldl_set {r : X86.GPR} :
    ∀ (ps : List (X86.GPR × Word)) (rs : Xl.Regs), rs.size = 16 →
      (ps.foldl (fun rs (d : X86.GPR × Word) => rs.set d.1 (some d.2)) rs).get r =
        match ps.reverse.find? (·.1 == r) with
        | some d => some d.2
        | none => rs.get r
  | [], rs, _ => by simp
  | d :: ps, rs, hs => by
      simp only [List.foldl_cons, List.reverse_cons]
      rw [get_foldl_set ps _ (by rw [Xl.Regs.size_set, hs]), List.find?_append]
      cases ps.reverse.find? (·.1 == r) with
      | some d' => rfl
      | none =>
        simp only [Option.none_or, List.find?_cons, List.find?_nil]
        rw [Xl.Regs.get_set _ hs]
        by_cases e : r = d.1
        · subst e; simp
        · have : (d.1 == r) = false := by simpa [beq_iff_eq] using fun h => e h.symm
          simp [this, e]

theorem entryRegs_size (vals : List Word) : (Xl.entryRegs vals).size = 16 := by
  unfold Xl.entryRegs; rw [regs_size_foldl_set]; rfl

theorem argRegs_nodup : Lir.Conv.argRegs.Nodup := by decide

theorem resultRegs_nodup : Lir.Conv.resultRegs.Nodup := by decide

/-- The register a list of distinct keys sets. -/
theorem find?_zip_nodup {ks : List X86.GPR} {vs : List Word} (hk : ks.Nodup) {i : Nat}
    (hi : i < ks.length) (hv : i < vs.length) :
    (ks.zip vs).reverse.find? (·.1 == ks[i]) = some (ks[i], vs[i]) := by
  have hmem : (ks[i], vs[i]) ∈ (ks.zip vs).reverse := by
    rw [List.mem_reverse, List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩
  have hex : ((ks.zip vs).reverse.find? (·.1 == ks[i])).isSome :=
    List.find?_isSome.2 ⟨_, hmem, by simp⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hex
  have hdm := List.mem_of_find?_eq_some hd
  have hd1 : d.1 = ks[i] := by simpa using List.find?_some hd
  rw [hd]
  rw [List.mem_reverse, List.mem_iff_getElem] at hdm
  obtain ⟨j, hj, e⟩ := hdm
  simp only [List.getElem_zip] at e
  have hj' : j < ks.length := by simp at hj; omega
  have hji : j = i := by
    rw [← e] at hd1
    exact (List.Nodup.getElem_inj hk).1 hd1
  subst hji
  rw [← e]

theorem entryRegs_get {vals : List Word} {i : Nat} (hi : i < Lir.Conv.argRegs.length) (hv : i < vals.length) :
    (Xl.entryRegs vals).get Lir.Conv.argRegs[i] = some vals[i] := by
  unfold Xl.entryRegs
  rw [get_foldl_set _ _ rfl, find?_zip_nodup argRegs_nodup hi hv]

theorem returnRegs_size {saved : Xl.Regs} (hs : saved.size = 16) (clob : List X86.GPR) (vals : List Word) :
    (Xl.returnRegs saved clob vals).size = 16 := by
  unfold Xl.returnRegs
  simp only
  rw [regs_size_foldl_set]
  have : ∀ (rs : List X86.GPR) (x : Xl.Regs),
      (rs.foldl (fun rs r => if clob.contains r then rs.set r none else rs) x).size = x.size := by
    intro rs
    induction rs with
    | nil => intro x; rfl
    | cons r rs ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih]
      split <;> simp [Xl.Regs.size_set]
  rw [this, hs]

theorem clearFold_get {clob : List X86.GPR} {r : X86.GPR} :
    ∀ (rs : List X86.GPR) (x : Xl.Regs), x.size = 16 →
      (rs.foldl (fun rs r => if clob.contains r then rs.set r none else rs) x).get r =
        if r ∈ rs ∧ r ∈ clob then none else x.get r
  | [], x, _ => by simp
  | r' :: rs, x, hs => by
      simp only [List.foldl_cons]
      have hs' : (if clob.contains r' then x.set r' none else x).size = 16 := by
        split <;> simp [Xl.Regs.size_set, hs]
      rw [clearFold_get rs _ hs']
      by_cases hc : clob.contains r' = true
      · simp only [hc, ↓reduceIte, Xl.Regs.get_set _ hs]
        by_cases e : r = r'
        · subst e; simp [List.contains_iff_mem.1 hc]
        · simp [e]
      · have hc' : clob.contains r' = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte]
        by_cases e : r = r'
        · subst e
          have : r ∉ clob := fun hm => by rw [List.contains_iff_mem.2 hm] at hc'; cases hc'
          simp [this]
        · simp [e]

theorem allGPRs_mem (r : X86.GPR) : r ∈ allGPRs := by cases r <;> decide

theorem returnRegs_result {saved : Xl.Regs} (hs : saved.size = 16) (clob : List X86.GPR) {vals : List Word}
    {i : Nat} (hi : i < Lir.Conv.resultRegs.length) (hv : i < vals.length) :
    (Xl.returnRegs saved clob vals).get Lir.Conv.resultRegs[i] = some vals[i] := by
  unfold Xl.returnRegs
  simp only
  have hs' : (allGPRs.foldl (fun rs r => if clob.contains r then rs.set r none else rs) saved).size = 16 := by
    have := returnRegs_size hs clob []
    unfold Xl.returnRegs at this
    simpa using this
  rw [get_foldl_set _ _ hs', find?_zip_nodup resultRegs_nodup hi hv]

theorem returnRegs_other {saved : Xl.Regs} (hs : saved.size = 16) {clob : List X86.GPR} {vals : List Word}
    {r : X86.GPR} (hc : r ∉ clob) (hr : ∀ i (h : i < Lir.Conv.resultRegs.length), i < vals.length →
      r ≠ Lir.Conv.resultRegs[i]) :
    (Xl.returnRegs saved clob vals).get r = saved.get r := by
  unfold Xl.returnRegs
  simp only
  have hs' : (allGPRs.foldl (fun rs r => if clob.contains r then rs.set r none else rs) saved).size = 16 := by
    have := returnRegs_size hs clob []
    unfold Xl.returnRegs at this
    simpa using this
  rw [get_foldl_set _ _ hs']
  have hnone : (Lir.Conv.resultRegs.zip vals).reverse.find? (·.1 == r) = none := by
    rw [List.find?_eq_none]
    intro d hd e
    simp only [beq_iff_eq] at e
    rw [List.mem_reverse, List.mem_iff_getElem] at hd
    obtain ⟨j, hj, hdj⟩ := hd
    simp only [List.length_zip] at hj
    rw [← hdj] at e
    simp only [List.getElem_zip] at e
    exact hr j (by omega) (by omega) e.symm
  rw [hnone]
  simp only
  rw [clearFold_get _ _ hs]
  simp [hc]

/-! ## Entering a function -/

theorem argLoc_eq {i : Nat} : Xl.argLoc i =
    if h : i < Lir.Conv.argRegs.length then .reg Lir.Conv.argRegs[i] else .outArg (i - Xl.nArgRegs) := by
  unfold Xl.argLoc
  split
  · rename_i r hr
    rw [List.getElem?_eq_some_iff] at hr
    obtain ⟨h, rfl⟩ := hr
    simp [h]
  · rename_i hr
    rw [List.getElem?_eq_none_iff] at hr
    simp [show ¬ i < Lir.Conv.argRegs.length by omega]

theorem paramLoc_eq {i : Nat} : Xl.paramLoc i =
    if h : i < Lir.Conv.argRegs.length then .reg Lir.Conv.argRegs[i] else .inArg (i - Xl.nArgRegs) := by
  unfold Xl.paramLoc
  split
  · rename_i r hr
    rw [List.getElem?_eq_some_iff] at hr
    obtain ⟨h, rfl⟩ := hr
    simp [h]
  · rename_i hr
    rw [List.getElem?_eq_none_iff] at hr
    simp [show ¬ i < Lir.Conv.argRegs.length by omega]

theorem argRegs_not_reserved {i : Nat} (h : i < Lir.Conv.argRegs.length) :
    Xl.reserved Lir.Conv.argRegs[i] = false := by
  have : i < 7 := h
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

theorem entry_read {vals : List Word} {g : Nat} {i : Nat} (hv : i < vals.length) :
    Xl.read (Xl.entryRegs vals) { fn := g, label := 0, pos := 0, inArgs := (vals.drop Xl.nArgRegs).toArray }
      (Xl.paramLoc i) = some vals[i] := by
  rw [paramLoc_eq]
  split
  · rename_i h
    simp only [Xl.read, argRegs_not_reserved h, Bool.false_eq_true, ↓reduceIte]
    exact entryRegs_get h hv
  · rename_i h
    simp only [Xl.read, List.getElem?_toArray, List.getElem?_drop]
    have : Xl.nArgRegs + (i - Xl.nArgRegs) = i := by
      simp only [Xl.nArgRegs] at *; omega
    rw [this, List.getElem?_eq_getElem hv]

/-- A callee's entry state agrees with its arguments. -/
theorem entry_agree {params : List VReg} {vals : List Word} {ρ : Env} {g : Nat} (hnd : params.Nodup)
    (hb : Lir.bindParams {} params vals = some ρ) :
    (entryState params).Agree ρ
      (Xl.read (Xl.entryRegs vals) { fn := g, label := 0, pos := 0, inArgs := (vals.drop Xl.nArgRegs).toArray }) := by
  have hlen := bindParams_length hb
  unfold entryState
  have key : ∀ (l : List (VReg × Nat)) (a : AState), a.Agree ρ (Xl.read (Xl.entryRegs vals)
        { fn := g, label := 0, pos := 0, inArgs := (vals.drop Xl.nArgRegs).toArray }) →
      (∀ d ∈ l, d ∈ params.zipIdx) →
      (l.foldl (fun a (d : VReg × Nat) => a.set (Xl.paramLoc d.2) [d.1]) a).Agree ρ
        (Xl.read (Xl.entryRegs vals) { fn := g, label := 0, pos := 0, inArgs := (vals.drop Xl.nArgRegs).toArray }) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons d l ih =>
      intro a ha hl
      simp only [List.foldl_cons]
      apply ih _ _ (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd'))
      apply ha.set_single
      have hd := hl d List.mem_cons_self
      obtain ⟨hi, hx⟩ := List.mem_zipIdx' hd
      have hv : d.2 < vals.length := by omega
      refine ⟨vals[d.2], ?_, entry_read hv⟩
      apply bindParams_zip hnd hb
      rw [hx, List.mem_iff_getElem]
      exact ⟨d.2, by simp; omega, by simp⟩
  exact key _ _ AState.Agree.empty (fun d hd => hd)

/-! ## Returning -/

theorem resultLocs_eq (n : Nat) (h : n ≤ Xl.nResultRegs) :
    resultLocs n = (Lir.Conv.resultRegs.take n).map Loc.reg := by
  have : n ≤ 2 := h
  rcases n with _ | _ | _ | n <;> first | rfl | omega

/-- After a return, the caller's abstract state at the return point agrees
with the returned registers: the results where the convention puts them,
nothing in the callee's clobber set or the released outgoing cells, and
everything else as it was at the call. -/
theorem call_agree {a : AState} {ρ : Env} {regs : Xl.Regs} {fl : Xl.Frame} (hag : a.Agree ρ (Xl.read regs fl))
    (hsize : regs.size = 16) {rets : List VReg} (hk : rets.length ≤ Xl.nResultRegs) (hnd : rets.Nodup)
    {clob : List X86.GPR} {vals : List Word} {ρ' : Env} (hb : Lir.bindParams ρ rets vals = some ρ')
    (fl' : Xl.Frame) (hslots : fl'.slots = fl.slots) (hin : fl'.inArgs = fl.inArgs)
    (hout : fl'.outArgs = {}) :
    ((a.clearOutArgs).define (rets.zip (resultLocs rets.length)) (clob.map Loc.reg)).Agree ρ'
      (Xl.read (Xl.returnRegs regs clob vals) fl') := by
  have hlen := bindParams_length hb
  have hmid : (a.clearOutArgs).Agree ρ (Xl.read regs { fl with outArgs := {} }) :=
    hag.clearOutArgs fun l hl => by cases l <;> first | rfl | exact absurd rfl (hl _)
  refine hmid.define (fun v l h => ?_) (fun v hv => ?_) (fun l hl hc => ?_)
  · rw [resultLocs_eq _ hk] at h
    rw [List.mem_iff_getElem] at h
    obtain ⟨i, hi, e⟩ := h
    simp only [List.length_zip, List.length_map, List.length_take] at hi
    simp only [List.getElem_zip, List.getElem_map, List.getElem_take, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hi₁ : i < rets.length := by omega
    have hi₂ : i < Lir.Conv.resultRegs.length := by omega
    have hi₃ : i < vals.length := by omega
    refine ⟨vals[i], bindParams_zip hnd hb (List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩), ?_⟩
    have hres : Xl.reserved Lir.Conv.resultRegs[i] = false := by
      have : i < 2 := hi₂
      rcases i with _ | _ | i <;> first | rfl | omega
    simp only [Xl.read, hres, Bool.false_eq_true, ↓reduceIte]
    exact returnRegs_result hsize clob hi₂ hi₃
  · have hl : (resultLocs rets.length).length = rets.length := by
      have : Xl.nResultRegs = 2 := rfl
      rw [resultLocs_eq _ hk]; simp [Lir.Conv.resultRegs]; omega
    exact bindParams_other hb (by rwa [List.map_fst_zip (by omega)] at hv)
  · cases l with
    | reg r =>
      have hrc : r ∉ clob := fun hm => hc (List.mem_map_of_mem hm)
      simp only [Xl.read]
      split
      · rfl
      · rw [returnRegs_other hsize hrc]
        intro i hi hv e
        apply hl
        rw [List.mem_map]
        refine ⟨(rets[i]'(by omega), Loc.reg Lir.Conv.resultRegs[i]), ?_, by simp [e]⟩
        rw [resultLocs_eq _ hk, List.mem_iff_getElem]
        exact ⟨i, by simp; omega, by simp⟩
    | slot i => simp [Xl.read, hslots]
    | inArg i => simp [Xl.read, hin]
    | outArg i => simp [Xl.read, hout]

/-! ## Stepping through a block -/

theorem drop_getElem {α : Type} {arr : Array α} {j : Nat} {x : α} {more : List α}
    (h : arr.toList.drop j = x :: more) : ∃ hj : j < arr.size, arr[j] = x := by
  have h1 : arr.toList[j]? = some x := by rw [← List.head?_drop, h]; rfl
  rw [List.getElem?_eq_some_iff] at h1
  obtain ⟨hj, e⟩ := h1
  exact ⟨by simpa using hj, by simpa using e⟩

theorem drop_nil_size {α : Type} {arr : Array α} {j : Nat} (h : arr.toList.drop j = []) :
    ¬ j < arr.size := by
  rw [List.drop_eq_nil_iff] at h; simp at h; omega

theorem drop_succ_of_cons {α : Type} {l : List α} {j : Nat} {x : α} {more : List α}
    (h : l.drop j = x :: more) : l.drop (j + 1) = more := by
  rw [← List.drop_drop, h]; rfl

theorem read_pos (regs : Xl.Regs) (fr : Xl.Frame) (p : Nat) :
    Xl.read regs { fr with pos := p } = Xl.read regs fr := by
  funext l; cases l <;> rfl

section XlStep

variable (q : LProgram) (env : Xl.Env)

theorem xl_step_inst {t : Xl.State} {fl : Xl.Frame} {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    {g : Func Loc} (hg : q.funcs[fl.fn]? = some g) {bl : Block Loc} (hbl : g.blocks[fl.label]? = some bl)
    {x : Inst Loc} {more : List (Inst Loc)} (hd : bl.body.toList.drop fl.pos = x :: more)
    (hnc : ∀ g' a r, x ≠ .call g' a r)
    {regs' : Xl.Regs} {fl' : Xl.Frame} {mem' : X86.Memory}
    (hx : Xl.execInst t.regs fl t.mem t.ctx x = some (regs', fl', mem')) :
    Xl.step q env t =
      .next { t with mem := mem', regs := regs', stack := { fl' with pos := fl.pos + 1 } :: rest } false := by
  obtain ⟨hj, hx'⟩ := drop_getElem hd
  unfold Xl.step
  rw [ht]
  simp only [hg, hbl, hj, ↓reduceDIte, hx']
  cases x with
  | call g' a r => exact absurd rfl (hnc g' a r)
  | _ => simp [hx]

/-- A run of edits is a run of silent Xl steps under which the abstract state
follows the validator's transfer. -/
theorem xl_edits {c : Ctx} {g : Func Loc} {bl : Block Loc} {ρ : Env} :
    ∀ {now : List Edit} {a a' : AState} {t : Xl.State} {fl : Xl.Frame} {rest : List Xl.Frame}
      {more : List (Inst Loc)},
      t.stack = fl :: rest → q.funcs[fl.fn]? = some g → g.blocks[fl.label]? = some bl →
      bl.body.toList.drop fl.pos = now.map Edit.toInst ++ more →
      stepEdits c a now = .ok a' → a.Agree ρ (Xl.read t.regs fl) → t.regs.size = 16 →
      fl.inArgs.size = c.stackParams →
      ∃ regs' fl', Sem.Star (Xl.step q env) t 0 { t with regs := regs', stack := fl' :: rest } ∧
        fl'.pos = fl.pos + now.length ∧ fl'.fn = fl.fn ∧ fl'.label = fl.label ∧
        fl'.inArgs.size = fl.inArgs.size ∧
        a'.Agree ρ (Xl.read regs' fl') ∧ regs'.size = 16 ∧ bl.body.toList.drop fl'.pos = more
  | [], a, a', t, fl, rest, more, ht, _, _, hd, hv, hag, hs, _ => by
      simp only [stepEdits, pure, Except.pure, Except.ok.injEq] at hv
      subst hv
      refine ⟨t.regs, fl, ?_, by simp, rfl, rfl, rfl, hag, hs, by simpa using hd⟩
      rcases t with ⟨mem, ctx, regs, stack⟩
      simp only at ht
      subst ht
      exact .refl _
  | e :: now, a, a', t, fl, rest, more, ht, hg, hbl, hd, hv, hag, hs, hin => by
      simp only [stepEdits, bind, Except.bind] at hv
      cases he : stepEdit c a e with
      | error err => simp [he] at hv
      | ok a₁ =>
        simp only [he] at hv
        obtain ⟨dst, src⟩ := e
        obtain ⟨regs₁, fl₁, hx, hs₁, hctl, hag₁⟩ := stepEdit_sound (mem := t.mem) (ctx := t.ctx) he hag hs hin
        have hd' : bl.body.toList.drop fl.pos = Inst.move dst src :: (now.map Edit.toInst ++ more) := by
          simpa [Edit.toInst] using hd
        have hstep := xl_step_inst q env ht hg hbl hd' (fun _ _ _ => by simp) hx
        let fl₂ : Xl.Frame := { fl₁ with pos := fl.pos + 1 }
        let t₁ : Xl.State := { t with mem := t.mem, regs := regs₁, stack := fl₂ :: rest }
        obtain ⟨regs', fl', hstar, hpos, hfn, hlab, hin', hag', hs', hd''⟩ :=
          xl_edits (t := t₁) (fl := fl₂) rfl
            (by simp only [fl₂]; rw [hctl.fn]; exact hg) (by simp only [fl₂]; rw [hctl.label]; exact hbl)
            (by simp only [fl₂]; exact drop_succ_of_cons hd') hv
            (by simp only [t₁, fl₂]; rw [read_pos]; exact hag₁) hs₁
            (by simp only [fl₂]; rw [hctl.inArgs]; exact hin)
        refine ⟨regs', fl', .free hstep hstar, by rw [hpos]; simp [fl₂]; omega, by rw [hfn]; exact hctl.fn,
          by rw [hlab]; exact hctl.label, by rw [hin']; exact hctl.inArgs, hag', hs', hd''⟩

end XlStep

end Compilatrix.Xv.Validate
