import IxCC.Recheck.Proof.Live
import IxCC.Src.Relevance.Proof.P1.Main

/-! # P1's consumption, with P1's root proved and `Front.RunSortAgree` discharged

`Front.goesWrong_live_closed` and `sound_live_closed` keep the approved signatures parameterized by
`Front.RunSortAgree`. Below them, this module discharges `Front.RunSortAgree` in two ways while
preserving the build-graph isolation (`IxCC` does not import `IxCCGrounding` or `IxCK.Kernel.Denotes`):

1. **Concrete kernel-evaluable static discharge (`SortClosed`):** a D17 kernel-evaluable `Bool`
   checker on `(p, ann, ch)` verifying that every reached irrelevant application spine, projection,
   recursor rule, `case` key with sort-dropped fields, and `Quot.lift` satisfies `SortCoherent`.
   Proved sound (`runSortAgree_of_sortClosed`, `Front.runSortAgree_of_sortClosed`), yielding
   `Front.goesWrong_live_discharged` and `sound_live_discharged` with **no** `RunSortAgree`
   and **no** `ShapeOk` hypotheses.
2. **Semantic `BinderMeta.pw` + `M.graded` bridge (`GradedSortBridge`):** the clean local
   sort-agreement interface that `IxCCGrounding` instantiates from Ixon v5 `BinderMeta.pw` and
   `M.graded` (covering higher-order `dite` and mixed `Prod`+`Fin` programs beyond the syntactic
   checker), yielding `Front.runSortAgree_of_graded`, `Front.goesWrong_live_of_graded`, and
   `sound_live_of_graded`. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram Agree)
open IxCC.Src.Relevance.Proof.P1

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- **The narrowing.** Under `Recheck.run`'s acceptance and the run's sort events, the source goes
wrong only by being stuck, trapping, or returning a `Live` value the view rejects: never because
of a marker. -/
theorem Front.goesWrong_live_closed (h : run cfg P c = .ok a) {i : Nat × List Nat}
    (hsa : a.front.RunSortAgree c.relevance i) :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i :=
  Front.goesWrong_live run_live h hsa

/-- **`Recheck.sound` with the narrowed escape**, under the run's sort events. -/
theorem sound_live_closed (h : run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hsa : a.front.RunSortAgree c.relevance i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
        ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  sound_live run_live h D hD i hi hsa

/-! ## Shared local-to-global discharge of `RunSortAgree` -/

namespace SortDischarge

open IxCC.Src
open IxCC.Src.Relevance IxCC.Src.Relevance.Proof
open IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical

/- Every slot held in an environment/value/call is either a `LiveSlot` (carrying `Frame`),
a `MarkerSlot`, or a shielded by-name variable suspension over a safe environment. -/
mutual

inductive SafeVal (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Value → Prop
  | lit (n : Nat) : SafeVal p ann ch (.lit n)
  | str (s : String) : SafeVal p ann ch (.str s)
  | irr (t : Option Term) (ρ : Env) (ls : Levels) : SafeVal p ann ch (.irr t ρ ls)
  | con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} :
      (∀ v ∈ fs, SafeVal p ann ch v) → SafeVal p ann ch (.con c ls ps fs)
  | clo {b : Binder} {d body : Term} {ρ : Env} {ls : Levels} :
      (∀ s ∈ ρ, SafeSlot p ann ch s) → SafeVal p ann ch (.clo b d body ρ ls)
  | pap {h : Head} {ls : Levels} {args : List Slot} :
      (∀ s ∈ args, SafeSlot p ann ch s) → SafeVal p ann ch (.pap h ls args)

inductive SafeSlot (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Slot → Prop
  | val {v : Value} : SafeVal p ann ch v → SafeSlot p ann ch (.val v)
  | name {t : Term} {ρ : Env} {ls : Levels} :
      (LiveSlot p ann ch (.name t ρ ls) ∨ ∃ x, t = .var x) →
      (∀ s ∈ ρ, SafeSlot p ann ch s) →
      SafeSlot p ann ch (.name t ρ ls)

end

private def SafeSlots (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Call → Prop
  | .eval _ _ ρ _ => ∀ s ∈ ρ, SafeSlot p ann ch s
  | .evalConst .. | .headValue .. => True
  | .apply _ f s => SafeVal p ann ch f ∧ SafeSlot p ann ch s
  | .applyAll _ f ss => SafeVal p ann ch f ∧ ∀ s ∈ ss, SafeSlot p ann ch s
  | .fire _ _ _ args => ∀ s ∈ args, SafeSlot p ann ch s
  | .force _ s => SafeSlot p ann ch s
  | .forceAll _ ss => ∀ s ∈ ss, SafeSlot p ann ch s

private def SafePost (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Call → Prop
  | .eval k ls ρ t => ∀ v, eval p k ls ρ t = .ok v → SafeVal p ann ch v
  | .evalConst k ls c => ∀ v, evalConst p k ls c = .ok v → SafeVal p ann ch v
  | .headValue k ls h => ∀ v, headValue p k ls h = .ok v → SafeVal p ann ch v
  | .apply k f s => ∀ v, apply p k f s = .ok v → SafeVal p ann ch v
  | .applyAll k f ss => ∀ v, applyAll p k f ss = .ok v → SafeVal p ann ch v
  | .fire k h ls args => ∀ v, fire p k h ls args = .ok v → SafeVal p ann ch v
  | .force k s => ∀ v, force p k s = .ok v → SafeVal p ann ch v
  | .forceAll k ss => ∀ vs, forceAll p k ss = .ok vs → ∀ v ∈ vs, SafeVal p ann ch v

/-- A local sort-coherence hypothesis at every reached call whose precondition holds, given the
`Post` of every child call whose precondition holds. -/
def LocalSortCoherent (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) (top : Call) :
    Prop :=
  ∀ c, Reach p top c → Pre p ann ch c →
    (∀ c', Step p c c' → Pre p ann ch c' → Post p ann ch c') →
    SortCoherent p ann c

/-- From `LocalSortCoherent`, every reached call whose `Pre` holds satisfies `SortCoherent`,
`Post`, and `StepPre` (`Inv`). -/
theorem inv_of_local {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call}
    (hloc : LocalSortCoherent p ann ch top) :
    ∀ c, Reach p top c → Pre p ann ch c →
      SortCoherent p ann c ∧ Post p ann ch c ∧ StepPre p ann ch c := by
  intro c
  induction c using callLt_wf.induction with
  | _ c ih =>
    intro hr hpre
    have hbelow : Below p ann ch c := fun d htg hpred =>
      let h := ih d (transGen_lt htg) (reach_transGen hr htg) hpred
      ⟨h.2.1, h.2.2⟩
    have hcoh : SortCoherent p ann c :=
      hloc c hr hpre (fun c' hst hpre' => (hbelow c' (.single hst) hpre').1)
    have hres := case_all_of cases_all hf hs hpre hcoh hbelow
    exact ⟨hcoh, hres.1, hres.2⟩

private def SafeState (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) (c : Call) : Prop :=
  (Pre p ann ch c ∧ SafeSlots p ann ch c) ∨
  (∃ k ls ρ x, c = .eval k ls ρ (.var x) ∧ ∀ s ∈ ρ, SafeSlot p ann ch s) ∨
  (∃ k s, c = .force k s ∧ SafeSlot p ann ch s)

private theorem safeVal_mkWord {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {w : Width} {n : Nat} {v : Value} (h : p.mkWord? w n = some v) : SafeVal p ann ch v := by
  unfold Program.mkWord? at h
  cases h1 : p.wordCtor? w <;> simp [h1] at h
  cases h2 : p.known.bitVecOfFin <;> simp [h2] at h
  cases h3 : p.known.finMk <;> simp [h3] at h
  subst h
  refine .con fun v1 hv1 => ?_
  simp only [List.mem_singleton] at hv1
  subst hv1
  refine .con fun v2 hv2 => ?_
  simp only [List.mem_singleton] at hv2
  subst hv2
  refine .con fun v3 hv3 => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
  rcases hv3 with rfl | rfl
  · exact .lit n
  · exact .irr ..

private theorem safe_getD {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {args : List Slot} (hargs : ∀ s ∈ args, SafeSlot p ann ch s) (i : Nat) :
    SafeSlot p ann ch (args.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : args[i]? with
  | none => exact .val (.lit 0)
  | some s => exact hargs s (List.mem_iff_getElem?.2 ⟨i, hi⟩)

private theorem safe_getD_irr {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {args : List Slot} {ls : Levels} (hargs : ∀ s ∈ args, SafeSlot p ann ch s) (i : Nat) :
    SafeSlot p ann ch (args.getD i (Slot.irrNone ls)) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : args[i]? with
  | none => exact .val (.irr ..)
  | some s => exact hargs s (List.mem_iff_getElem?.2 ⟨i, hi⟩)

private theorem safe_selectRule {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ind np j : Nat} {major : Value} {fields : List Slot}
    (hm : SafeVal p ann ch major) (hsel : p.selectRule ind np major = some (j, fields)) :
    ∀ s ∈ fields, SafeSlot p ann ch s := by
  cases major with
  | lit m =>
    simp only [Program.selectRule] at hsel
    split at hsel
    · split at hsel
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        rw [← hsel.2]; intro _ h; cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        rw [← hsel.2]; intro s hs
        simp only [List.mem_singleton] at hs; subst hs
        exact .val (.lit _)
    · cases hsel
  | con c lsv ps fs =>
    cases hm with
    | con hfs =>
      simp only [Program.selectRule] at hsel
      cases hd : p.decl? c with
      | none => rw [hd] at hsel; cases hsel
      | some d =>
        rw [hd] at hsel
        cases d with
        | ctor =>
          simp only at hsel
          split at hsel
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
            rw [← hsel.2]
            intro s hs
            obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hs
            exact .val (hfs v hv)
          · cases hsel
        | _ => simp at hsel
  | _ => simp [Program.selectRule] at hsel

private theorem safe_subsingleton_fields {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {srcs : List FieldSrc} {indices : List Slot}
    (hi : ∀ s ∈ indices, SafeSlot p ann ch s) :
    ∀ s ∈ srcs.map (fun
      | .index i => indices.getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls), SafeSlot p ann ch s := by
  intro s hs
  obtain ⟨src, -, rfl⟩ := List.mem_map.1 hs
  cases src with
  | proof => exact .val (.irr ..)
  | index i =>
    dsimp only
    rw [List.getD_eq_getElem?_getD]
    cases hget : indices[i]? with
    | none => exact .val (.irr ..)
    | some s' => exact hi s' (List.mem_iff_getElem?.2 ⟨i, hget⟩)

/-- Given `inv_of_local`, every call in `SafeState` preserves `SafeState` along every `Step` and
produces `SafeVal` results. -/
private theorem safe_core {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {top : Call}
    (hinv : ∀ c, Reach p top c → Pre p ann ch c →
      SortCoherent p ann c ∧ Post p ann ch c ∧ StepPre p ann ch c) :
    ∀ c, Reach p top c → SafeState p ann ch c →
      SafePost p ann ch c ∧ ∀ c', Step p c c' → SafeState p ann ch c' := by
  intro c
  induction c using callLt_wf.induction with
  | _ c ih =>
    intro hr hst
    have ihStep : ∀ {c'}, (h : Step p c c') → SafeState p ann ch c' → SafePost p ann ch c' :=
      fun h hsc' => (ih _ (step_lt h) (.step hr h) hsc').1
    rcases hst with ⟨hpre, hsafe⟩ | ⟨k, ls, ρ, x, rfl, hρ⟩ | ⟨k, s, rfl, hs⟩
    · have hsp : StepPre p ann ch c := (hinv c hr hpre).2.2
      cases c with
      | eval k ls ρ t =>
        cases t with
        | var i =>
          refine ⟨fun v hv => ?_, fun c' hstep => ?_⟩
          · rw [eval_var] at hv
            cases hget : ρ[i]? with
            | none => rw [hget] at hv; cases hv
            | some s =>
              rw [hget] at hv
              have hs' := hsafe s (List.mem_iff_getElem?.2 ⟨i, hget⟩)
              exact ihStep (Step.var hget) (Or.inr (Or.inr ⟨k, s, rfl, hs'⟩)) v hv
          · cases hstep with
            | var hget =>
              exact Or.inr (Or.inr ⟨k, _, rfl, hsafe _ (List.mem_iff_getElem?.2 ⟨i, hget⟩)⟩)
        | sort u =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [eval_sort] at hv; cases hv; exact .irr ..
        | pi b d c0 =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [eval_pi] at hv; cases hv; exact .irr ..
        | natLit n =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [eval_natLit] at hv; cases hv; exact .lit n
        | strLit s =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [eval_strLit] at hv; cases hv; exact .str s
        | lam b d body =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [eval_lam] at hv; cases hv; exact .clo hsafe
        | letE nd m r ty v b =>
          have hStep : ∀ c', Step p (.eval k ls ρ (.letE nd m r ty v b)) c' → SafeState p ann ch c' := by
            intro c' hstep
            have hpre' := hsp c' hstep (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1)
            cases hstep with
            | letIrr hirr =>
              refine Or.inl ⟨hpre', fun s hs' => ?_⟩
              rcases List.mem_cons.1 hs' with rfl | hs'
              · exact .val (.irr ..)
              · exact hsafe s hs'
            | letVal hrel => exact Or.inl ⟨hpre', hsafe⟩
            | letBody hrel hv =>
              have hval : SafeVal p ann ch _ :=
                ihStep (Step.letVal hrel) (Or.inl ⟨hsp _ (Step.letVal hrel) (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1), hsafe⟩) _ hv
              refine Or.inl ⟨hpre', fun s hs' => ?_⟩
              rcases List.mem_cons.1 hs' with rfl | hs'
              · exact .val hval
              · exact hsafe s hs'
          refine ⟨fun w hw => ?_, hStep⟩
          rw [eval_letE] at hw
          split at hw
          · rename_i hirr
            exact ihStep (Step.letIrr hirr) (hStep _ (Step.letIrr hirr)) w hw
          · rename_i hrel
            have hrel' : r.irrAt ls = false := by simpa using hrel
            obtain ⟨x, hx, hw⟩ := bind_ok_inv hw
            exact ihStep (Step.letBody hrel' hx) (hStep _ (Step.letBody hrel' hx)) w hw
        | proj s i e =>
          have hpe : SafeState p ann ch (.eval k ls ρ e) :=
            Or.inl ⟨hsp _ Step.proj (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1), hsafe⟩
          refine ⟨fun v hv => ?_, fun c' hstep => by cases hstep; exact hpe⟩
          rw [eval_proj] at hv
          obtain ⟨v0, hv0, hpf⟩ := bind_ok_inv hv
          have hsv0 := ihStep Step.proj hpe v0 hv0
          cases v0 with
          | con c0 lsv ps fs =>
            cases hsv0 with
            | con hfs =>
              simp only [Program.projectField] at hpf
              split at hpf
              · split at hpf
                · cases hfi : fs[i]? with
                  | none => simp [hfi, Sem.Result.ofOption] at hpf
                  | some w =>
                    simp [hfi, Sem.Result.ofOption] at hpf
                    subst hpf
                    exact hfs w (List.mem_iff_getElem?.2 ⟨i, hfi⟩)
                · cases hpf
              · cases hpf
          | _ => simp [Program.projectField] at hpf
        | app f a m r =>
          have hpf : SafeState p ann ch (.eval k ls ρ f) :=
            Or.inl ⟨hsp _ Step.appFun not_shielded_fun, hsafe⟩
          have hStep : ∀ c', Step p (.eval k ls ρ (.app f a m r)) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | appFun => exact hpf
            | appIrr hfv hirr =>
              have hpre' := hsp _ (Step.appIrr hfv hirr) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', ihStep Step.appFun hpf _ hfv, .val (.irr ..)⟩
            | appArg hfv hrel =>
              by_cases hsh : ∃ x, a = .var x ∧ ShieldedIn x ρ (.app f a .strict r)
              · obtain ⟨x, rfl, -⟩ := hsh
                exact Or.inr (Or.inl ⟨k, ls, ρ, x, rfl, hsafe⟩)
              · have hpre' := hsp _ (Step.appArg hfv hrel) (by
                  rintro ⟨_, _, _, _, _, _, x, h1, h2, hsi⟩
                  simp only [Call.eval.injEq, Term.app.injEq] at h1 h2
                  obtain ⟨-, -, rfl, rfl, rfl, rfl, rfl⟩ := h1
                  obtain ⟨-, -, -, hax⟩ := h2
                  exact hsh ⟨x, hax.symm, hsi⟩)
                exact Or.inl ⟨hpre', hsafe⟩
            | appStrict hfv hrel hx =>
              have hpre' := hsp _ (Step.appStrict hfv hrel hx) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              have hpa : SafeState p ann ch (.eval k ls ρ a) := by
                by_cases hsh : ∃ x0, a = .var x0 ∧ ShieldedIn x0 ρ (.app f a .strict r)
                · obtain ⟨x0, rfl, -⟩ := hsh
                  exact Or.inr (Or.inl ⟨k, ls, ρ, x0, rfl, hsafe⟩)
                · have hprea := hsp _ (Step.appArg hfv hrel) (by
                    rintro ⟨_, _, _, _, _, _, x0, h1, h2, hsi⟩
                    simp only [Call.eval.injEq, Term.app.injEq] at h1 h2
                    obtain ⟨-, -, rfl, rfl, rfl, rfl, rfl⟩ := h1
                    obtain ⟨-, -, -, hax⟩ := h2
                    exact hsh ⟨x0, hax.symm, hsi⟩)
                  exact Or.inl ⟨hprea, hsafe⟩
              exact Or.inl ⟨hpre', ihStep Step.appFun hpf _ hfv, .val (ihStep (Step.appArg hfv hrel) hpa _ hx)⟩
            | appName hfv hrel =>
              have hpre' := hsp _ (Step.appName hfv hrel) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              have hslot : SafeSlot p ann ch (.name a ρ ls) := by
                by_cases hsh : ∃ x0, a = .var x0 ∧ ShieldedIn x0 ρ (.app f a .byName r)
                · obtain ⟨x0, rfl, -⟩ := hsh
                  exact .name (Or.inr ⟨x0, rfl⟩) hsafe
                · obtain ⟨q, bs, hag, henva, htoka⟩ := frame_arg hpre hrel hsh
                  exact .name (Or.inl (.name q bs hag htoka henva)) hsafe
              exact Or.inl ⟨hpre', ihStep Step.appFun hpf _ hfv, hslot⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [eval_app_slot] at hv
          obtain ⟨fv, hfv, hv⟩ := bind_ok_inv hv
          obtain ⟨s, hs0, hv⟩ := bind_ok_inv hv
          have hst := slotOf_step hfv hs0
          exact ihStep hst (hStep _ hst) v hv
        | const c0 us =>
          have hpc : SafeState p ann ch (.evalConst k (us.map (evalUniv ls)) c0) :=
            Or.inl ⟨hsp _ Step.const (not_shielded_of_ne (fun _ _ _ _ h => by cases h)), trivial⟩
          refine ⟨fun v hv => ?_, fun c' hstep => by cases hstep; exact hpc⟩
          rw [eval_const] at hv
          exact ihStep Step.const hpc v hv
      | evalConst k ls c0 =>
        have hStep : ∀ c', Step p (.evalConst k ls c0) c' → SafeState p ann ch c' := by
          intro c' hstep
          have hpre' := hsp c' hstep (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1)
          cases hstep <;> exact Or.inl ⟨hpre', by simp [SafeSlots]⟩
        refine ⟨fun v hv => ?_, hStep⟩
        rw [evalConst_eq] at hv
        cases hres : p.table.resolveOf c0 with
        | some e =>
          rw [hres] at hv
          cases e with
          | prim op => exact ihStep (Step.prim hres) (hStep _ (Step.prim hres)) v hv
          | word w op thm => exact ihStep (Step.word hres) (hStep _ (Step.word hres)) v hv
          | csimp g vs thm =>
            cases k with
            | zero => cases hv
            | succ k' =>
              simp only [Sem.later_succ] at hv
              exact ihStep (Step.csimp hres) (hStep _ (Step.csimp hres)) v hv
          | eqn thm body =>
            cases k with
            | zero => cases hv
            | succ k' =>
              simp only [Sem.later_succ] at hv
              exact ihStep (Step.eqn hres) (hStep _ (Step.eqn hres)) v hv
          | case r' => exact ihStep (Step.case hres) (hStep _ (Step.case hres)) v hv
        | none =>
          rw [hres] at hv
          cases hd : p.decl? c0 with
          | none => rw [hd] at hv; cases hv
          | some d =>
            rw [hd] at hv
            cases d with
            | ctor => exact ihStep (Step.ctor hres hd) (hStep _ (Step.ctor hres hd)) v hv
            | recr => exact ihStep (Step.recr hres hd) (hStep _ (Step.recr hres hd)) v hv
            | quot qk lv ty =>
              cases qk with
              | ctor => exact ihStep (Step.quotMk hres hd) (hStep _ (Step.quotMk hres hd)) v hv
              | lift => exact ihStep (Step.quotLift hres hd) (hStep _ (Step.quotLift hres hd)) v hv
              | _ => cases hv
            | defn kind safety lv ty body =>
              cases kind with
              | defn =>
                cases safety with
                | safe =>
                  cases k with
                  | zero => cases hv
                  | succ k' =>
                    simp only [Sem.later_succ] at hv
                    exact ihStep (Step.defn hres hd) (hStep _ (Step.defn hres hd)) v hv
                | _ => cases hv
              | opaq =>
                cases safety with
                | safe =>
                  simp only at hv
                  split at hv
                  · rename_i hop
                    cases k with
                    | zero => cases hv
                    | succ k' =>
                      simp only [Sem.later_succ] at hv
                      exact ihStep (Step.opaq hres hd hop) (hStep _ (Step.opaq hres hd hop)) v hv
                  · cases hv
                | _ => cases hv
              | thm => cases hv
            | _ => cases hv
      | headValue k ls h =>
        have hStep : ∀ c', Step p (.headValue k ls h) c' → SafeState p ann ch c' := by
          intro c' hstep
          have hpre' := hsp c' hstep (not_shielded_of_ne (fun _ _ _ _ h' => by cases hstep; cases h'))
          cases hstep
          exact Or.inl ⟨hpre', by simp [SafeSlots]⟩
        refine ⟨fun v hv => ?_, hStep⟩
        rw [headValue_eq] at hv
        split at hv
        · rename_i h0
          have har := beq_iff_eq.1 h0
          exact ihStep (Step.nullary har) (hStep _ (Step.nullary har)) v hv
        · cases hv
          exact .pap (fun _ hmem => by cases hmem)
      | apply k f s =>
        obtain ⟨hsf, hss⟩ := hsafe
        have hStep : ∀ c', Step p (.apply k f s) c' → SafeState p ann ch c' := by
          intro c' hstep
          have hpre' := hsp c' hstep (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1)
          cases hstep with
          | beta hbeta =>
            cases hsf with
            | clo hρ =>
              refine Or.inl ⟨hpre', fun s' hs' => ?_⟩
              rcases List.mem_cons.1 hs' with rfl | hs'
              · exact hss
              · exact hρ s' hs'
          | papFire har =>
            cases hsf with
            | pap hargs =>
              refine Or.inl ⟨hpre', fun s' hs' => ?_⟩
              rcases List.mem_append.1 hs' with hs' | hs'
              · exact hargs s' hs'
              · simp only [List.mem_singleton] at hs'; subst hs'; exact hss
        refine ⟨fun v hv => ?_, hStep⟩
        cases f with
        | clo b d body ρ ls =>
          rw [apply_clo] at hv
          split at hv
          · rename_i hbeta
            cases k with
            | zero => cases hv
            | succ k' =>
              simp only [Sem.later_succ] at hv
              exact ihStep (Step.beta hbeta) (hStep _ (Step.beta hbeta)) v hv
          · cases hv
        | pap h ls args =>
          rw [apply_pap] at hv
          split at hv
          · rename_i har
            have har' := beq_iff_eq.1 har
            exact ihStep (Step.papFire har') (hStep _ (Step.papFire har')) v hv
          · split at hv
            · cases hv
              cases hsf with
              | pap hargs =>
                refine .pap fun s' hs' => ?_
                rcases List.mem_append.1 hs' with hs' | hs'
                · exact hargs s' hs'
                · simp only [List.mem_singleton] at hs'; subst hs'; exact hss
            · cases hv
        | lit _ | str _ | con _ _ _ _ | irr _ _ _ =>
          rw [apply_other p k _ s (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)] at hv
          cases hv
      | applyAll k f ss =>
        obtain ⟨hsf, hss⟩ := hsafe
        cases ss with
        | nil =>
          refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
          rw [applyAll_nil] at hv; cases hv; exact hsf
        | cons s rest =>
          have hHead : SafeState p ann ch (.apply k f s) :=
            Or.inl ⟨hsp _ Step.allHead (not_shielded_of_ne (fun _ _ _ _ h => by cases h)),
              hsf, hss s (List.mem_cons_self ..)⟩
          have hStep : ∀ c', Step p (.applyAll k f (s :: rest)) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | allHead => exact hHead
            | allRest hv =>
              have hpre' := hsp _ (Step.allRest hv) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', ihStep Step.allHead hHead _ hv,
                fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [applyAll_cons] at hv
          obtain ⟨v0, hv0, hv⟩ := bind_ok_inv hv
          exact ihStep (Step.allRest hv0) (hStep _ (Step.allRest hv0)) v hv
      | fire k h ls args =>
        cases h with
        | ctor c0 =>
          have hStep : ∀ c', Step p (.fire k (.ctor c0) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | ctorArgs hd =>
              have hpre' := hsp _ (Step.ctorArgs hd) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', fun s hs' => hsafe s (mem_of_mem_drop' hs')⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [fire_ctor] at hv
          cases hd : p.decl? c0 with
          | none => rw [hd] at hv; cases hv
          | some d =>
            rw [hd] at hv
            cases d with
            | ctor sf lv ind cidx np nf ty =>
              obtain ⟨vs, hvs, hv⟩ := bind_ok_inv hv
              have hsvs := ihStep (Step.ctorArgs hd) (hStep _ (Step.ctorArgs hd)) vs hvs
              unfold ctorResult at hv
              split at hv
              · cases hv; exact .lit 0
              · split at hv
                · cases vs with
                  | cons v1 r1 =>
                    cases v1 with
                    | lit n => cases r1 with
                      | nil => cases hv; exact .lit (n + 1)
                      | cons _ _ => cases hv
                    | _ => cases hv
                  | nil => cases hv
                · cases hv; exact .con hsvs
            | _ => cases hv
        | quotMk c0 =>
          have hStep : ∀ c', Step p (.fire k (.quotMk c0) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | mkArg =>
              have hpre' := hsp _ Step.mkArg (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', hsafe _ (by simp)⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [fire_quotMk] at hv
          match args with
          | [α, r0, a0] =>
            obtain ⟨v0, hv0, hv⟩ := bind_ok_inv hv
            cases hv
            have hsv0 := ihStep Step.mkArg (hStep _ Step.mkArg) v0 hv0
            exact .con (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hsv0)
          | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => cases hv
        | quotLift c0 =>
          have hStep : ∀ c', Step p (.fire k (.quotLift c0) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | liftQuot =>
              have hpre' := hsp _ Step.liftQuot (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', hsafe _ (by simp)⟩
            | liftFun hq hiq =>
              have hpre' := hsp _ (Step.liftFun hq hiq) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', hsafe _ (by simp)⟩
            | liftApply hq hiq hf0 =>
              have hpre' := hsp _ (Step.liftApply hq hiq hf0) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              have hpq : SafeState p ann ch (.force _ _) :=
                Or.inl ⟨hsp _ Step.liftQuot (not_shielded_of_ne (fun _ _ _ _ h => by cases h)), hsafe _ (by simp)⟩
              have hpf : SafeState p ann ch (.force _ _) :=
                Or.inl ⟨hsp _ (Step.liftFun hq hiq) (not_shielded_of_ne (fun _ _ _ _ h => by cases h)), hsafe _ (by simp)⟩
              have hsq := ihStep Step.liftQuot hpq _ hq
              have hsf := ihStep (Step.liftFun hq hiq) hpf _ hf0
              cases hsq with
              | con hfs =>
                exact Or.inl ⟨hpre', hsf, .val (hfs _ (List.mem_singleton.2 rfl))⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [fire_quotLift] at hv
          cases k with
          | zero => cases hv
          | succ k' =>
            simp only [Sem.later_succ] at hv
            match args with
            | [α, r0, β, f0, h0, q0] =>
              obtain ⟨qv, hqv, hv⟩ := bind_ok_inv hv
              cases qv with
              | con c' l' ps fs =>
                cases fs with
                | cons a0 rest =>
                  cases rest with
                  | nil =>
                    simp only at hv
                    split at hv
                    · rename_i hiq
                      obtain ⟨fv, hfv, hv⟩ := bind_ok_inv hv
                      exact ihStep (Step.liftApply hqv hiq hfv) (hStep _ (Step.liftApply hqv hiq hfv)) v hv
                    · cases hv
                  | cons _ _ => cases hv
                | nil => cases hv
              | _ => cases hv
            | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
            | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => cases hv
        | recr r0 =>
          have hStep : ∀ c', Step p (.fire k (.recr r0) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | recMajor hd hk =>
              have hpre' := hsp _ (Step.recMajor hd hk) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', safe_getD hsafe _⟩
            | recRule hd hk hch hrule hpeel =>
              rename_i kind j fields rule body
              have hpre' := hsp _ (Step.recRule hd hk hch hrule hpeel)
                (by rintro ⟨_, _, _, _, _, _, _, h1, -⟩; cases h1)
              have hfields : ∀ s ∈ fields, SafeSlot p ann ch s := by
                cases kind with
                | empty => simp [P1.recChosen] at hch
                | subsingleton w srcs =>
                  simp only [P1.recChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
                  rw [← hch.2]
                  exact safe_subsingleton_fields fun s hs' =>
                    hsafe s (mem_of_mem_drop' (List.mem_of_mem_take hs'))
                | ordinary =>
                  simp only [P1.recChosen] at hch
                  cases hfm : force p _ (args.getD _ default) with
                  | ok major =>
                    rw [hfm] at hch
                    simp only at hch
                    cases hsel : p.selectRule _ _ major with
                    | none => rw [hsel] at hch; cases hch
                    | some jf =>
                      rw [hsel] at hch
                      simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                      have hpm : SafeState p ann ch (.force _ _) :=
                        Or.inl ⟨hsp _ (Step.recMajor hd hk) (not_shielded_of_ne (fun _ _ _ _ h => by cases h)),
                          safe_getD hsafe _⟩
                      have hsm := ihStep (Step.recMajor hd hk) hpm major hfm
                      rw [hch] at hsel
                      exact safe_selectRule hsm hsel
                  | _ => rw [hfm] at hch; cases hch
              refine Or.inl ⟨hpre', fun s hs' => ?_⟩
              rw [List.mem_reverse, List.mem_append] at hs'
              rcases hs' with hs' | hs'
              · exact hsafe s (List.mem_of_mem_take hs')
              · exact hfields s hs'
          refine ⟨fun v hv => ?_, hStep⟩
          cases k with
          | zero => simp [fire] at hv
          | succ k' =>
            cases hd : p.decl? r0 with
            | none => simp [fire, hd] at hv
            | some d =>
              cases d with
              | recr sf kk lv np nmot nmin ni ind rules ty =>
                cases hk : (p.table.recKindOf r0).map (·.atLevels ls) with
                | none => simp only [fire, hd, hk] at hv; cases hv
                | some kind =>
                  obtain ⟨j, fields, rule, body, hch, hrule, hpeel, heval⟩ :=
                    fire_recr_ok hd hk hv
                  exact ihStep (Step.recRule hd hk hch hrule hpeel)
                    (hStep _ (Step.recRule hd hk hch hrule hpeel)) v heval
              | _ => simp [fire, hd] at hv
        | cases c0 =>
          have hStep : ∀ c', Step p (.fire k (.cases c0) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | caseMajor hres hd hk =>
              have hpre' := hsp _ (Step.caseMajor hres hd hk) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', safe_getD hsafe _⟩
            | caseMinor hres hd hk hch =>
              have hpre' := hsp _ (Step.caseMinor hres hd hk hch) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', safe_getD hsafe _⟩
            | caseApply hres hd hk hch hfm =>
              rename_i kind j fields mv
              have hpre' := hsp _ (Step.caseApply hres hd hk hch hfm)
                (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              have hpm : SafeState p ann ch (.force _ _) :=
                Or.inl ⟨hsp _ (Step.caseMinor hres hd hk hch) (not_shielded_of_ne (fun _ _ _ _ h => by cases h)),
                  safe_getD hsafe _⟩
              have hsmv := ihStep (Step.caseMinor hres hd hk hch) hpm mv hfm
              refine Or.inl ⟨hpre', hsmv, ?_⟩
              cases kind with
              | empty => simp [caseChosen] at hch
              | subsingleton w srcs =>
                simp only [caseChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
                rw [← hch.2]
                intro s hs'
                obtain ⟨src, -, rfl⟩ := List.mem_map.1 hs'
                cases src with
                | proof => exact .val (.irr ..)
                | index i => exact safe_getD_irr hsafe _
              | ordinary =>
                simp only [caseChosen] at hch
                cases hfmaj : force p _ (args.getD _ default) with
                | ok major =>
                  rw [hfmaj] at hch
                  simp only at hch
                  cases hsel : p.selectRule _ _ major with
                  | none => rw [hsel] at hch; cases hch
                  | some jf =>
                    rw [hsel] at hch
                    simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                    have hpmaj : SafeState p ann ch (.force _ _) :=
                      Or.inl ⟨hsp _ (Step.caseMajor hres hd hk) (not_shielded_of_ne (fun _ _ _ _ h => by cases h)),
                        safe_getD hsafe _⟩
                    have hsmaj := ihStep (Step.caseMajor hres hd hk) hpmaj major hfmaj
                    rw [hch] at hsel
                    exact safe_selectRule hsmaj hsel
                | _ => rw [hfmaj] at hch; cases hch
          refine ⟨fun v hv => ?_, hStep⟩
          cases k with
          | zero => simp [fire] at hv
          | succ k' =>
            cases hres : p.table.resolveOf c0 with
            | none => rw [fire] at hv; simp [hres] at hv
            | some e =>
              cases e with
              | case r0 =>
                obtain ⟨sf, kk, lv, np, nmot, nmin, ni, ind, rules, ty, kind, hd, hk⟩ :=
                  fire_cases_decl hres hv
                obtain ⟨j, fields, mv, hch, hfm, happ⟩ := fire_cases_ok hres hd hk hv
                exact ihStep (Step.caseApply hres hd hk hch hfm)
                  (hStep _ (Step.caseApply hres hd hk hch hfm)) v happ
              | _ => rw [fire] at hv; simp [hres] at hv
        | prim op =>
          have hStep : ∀ c', Step p (.fire k (.prim op) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | primArgs =>
              have hpre' := hsp _ Step.primArgs (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', hsafe⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [fire_prim] at hv
          obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
          unfold primValue at hv
          cases hlit : litArgs vs with
          | none => rw [hlit] at hv; cases hv
          | some ns =>
            rw [hlit] at hv; dsimp only at hv
            cases hop : op.evalLits ns with
            | none => rw [hop] at hv; cases hv
            | some res =>
              rw [hop] at hv
              cases res with
              | nat n => dsimp only at hv; cases hv; exact .lit n
              | bool b =>
                dsimp only at hv
                obtain ⟨c0, rfl⟩ := boolValue_ok hv
                exact .con (fun _ hmem => by cases hmem)
        | word w op =>
          have hStep : ∀ c', Step p (.fire k (.word w op) ls args) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | wordArgs =>
              have hpre' := hsp _ Step.wordArgs (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', hsafe⟩
          refine ⟨fun v hv => ?_, hStep⟩
          rw [fire_word] at hv
          obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
          obtain ⟨r0, hr0⟩ := wordValue_ok hv
          cases r0 with
          | word w' n =>
            simp only [Program.wordResult] at hr0
            cases hm : p.mkWord? w' n with
            | none => rw [hm] at hr0; cases hr0
            | some t =>
              rw [hm] at hr0
              simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hr0
              subst hr0
              exact safeVal_mkWord hm
          | nat n => simp only [Program.wordResult, Sem.Result.ok.injEq] at hr0; subst hr0; exact .lit n
          | dec b => simp [Program.wordResult] at hr0
      | force k s =>
        cases hsafe with
        | val hv =>
          refine ⟨fun v heq => ?_, fun _ hstep => by cases hstep⟩
          rw [force_val] at heq; cases heq; exact hv
        | name hlive hρ =>
          rename_i t ρ ls
          have hStep : ∀ c', Step p (.force k (.name t ρ ls)) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | forceName =>
              rcases hlive with hl | ⟨x, rfl⟩
              · exact Or.inl ⟨(liveSlot_name_frame hl).1 _, hρ⟩
              · exact Or.inr (Or.inl ⟨_, _, _, x, rfl, hρ⟩)
          refine ⟨fun v hv => ?_, hStep⟩
          rw [force_name] at hv
          cases k with
          | zero => cases hv
          | succ k' =>
            simp only [Sem.later_succ] at hv
            exact ihStep Step.forceName (hStep _ Step.forceName) v hv
      | forceAll k ss =>
        cases ss with
        | nil =>
          refine ⟨fun vs hvs => ?_, fun _ hstep => by cases hstep⟩
          rw [forceAll_nil] at hvs; cases hvs; intro _ hm; cases hm
        | cons s rest =>
          have hHead : SafeState p ann ch (.force k s) :=
            Or.inr (Or.inr ⟨k, s, rfl, hsafe s (List.mem_cons_self ..)⟩)
          have hStep : ∀ c', Step p (.forceAll k (s :: rest)) c' → SafeState p ann ch c' := by
            intro c' hstep
            cases hstep with
            | allForce => exact hHead
            | allForceRest hv =>
              have hpre' := hsp _ (Step.allForceRest hv) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
              exact Or.inl ⟨hpre', fun s' hs' => hsafe s' (List.mem_cons_of_mem _ hs')⟩
          refine ⟨fun vs hvs => ?_, hStep⟩
          rw [forceAll_cons] at hvs
          obtain ⟨v0, hv0, hvs⟩ := bind_ok_inv hvs
          obtain ⟨vs0, hvs0, hvs⟩ := bind_ok_inv hvs
          cases hvs
          intro v hv
          rcases List.mem_cons.1 hv with rfl | hv
          · exact ihStep Step.allForce hHead v hv0
          · exact ihStep (Step.allForceRest hv0) (hStep _ (Step.allForceRest hv0)) vs0 hvs0 v hv
    · -- Shielded `.eval k ls ρ (.var x)`
      refine ⟨fun v hv => ?_, fun c' hstep => ?_⟩
      · rw [eval_var] at hv
        cases hget : ρ[x]? with
        | none => rw [hget] at hv; cases hv
        | some s =>
          rw [hget] at hv
          exact ihStep (Step.var hget) (Or.inr (Or.inr ⟨k, s, rfl, hρ s (List.mem_iff_getElem?.2 ⟨x, hget⟩)⟩)) v hv
      · cases hstep with
        | var hget => exact Or.inr (Or.inr ⟨k, _, rfl, hρ _ (List.mem_iff_getElem?.2 ⟨x, hget⟩)⟩)
    · -- `.force k s` with `SafeSlot s`
      cases hs with
      | val hv =>
        refine ⟨fun v heq => ?_, fun _ hstep => by cases hstep⟩
        rw [force_val] at heq; cases heq; exact hv
      | name hlive hρ =>
        rename_i t ρ ls
        have hStep : ∀ c', Step p (.force k (.name t ρ ls)) c' → SafeState p ann ch c' := by
          intro c' hstep
          cases hstep with
          | forceName =>
            rcases hlive with hl | ⟨x, rfl⟩
            · exact Or.inl ⟨(liveSlot_name_frame hl).1 _, hρ⟩
            · exact Or.inr (Or.inl ⟨_, _, _, x, rfl, hρ⟩)
        refine ⟨fun v hv => ?_, hStep⟩
        rw [force_name] at hv
        cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ] at hv
          exact ihStep Step.forceName (hStep _ Step.forceName) v hv

/-- From `LocalSortCoherent` and an initial `SafeState` at `top`, `SortAgree p ann top` holds. -/
theorem sortAgree_of_local {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call}
    (htop : Pre p ann ch top) (hsafe : SafeSlots p ann ch top)
    (hloc : LocalSortCoherent p ann ch top) :
    SortAgree p ann top := by
  have hinv := inv_of_local hf hs hloc
  have hsafeReach : ∀ c, Reach p top c → SafeState p ann ch c := by
    intro c hr
    induction hr with
    | refl => exact Or.inl ⟨htop, hsafe⟩
    | step hr' hst ih => exact (safe_core hinv _ hr' ih).2 _ hst
  intro c hr
  rcases hsafeReach c hr with ⟨hpre, -⟩ | ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, rfl, -⟩
  · exact (hinv c hr hpre).1
  · trivial
  · trivial

/-- From a `LocalSortCoherent` proof for any call reachable from `evalConst` and `applyAll`,
`RunSortAgree` holds on a root with literal arguments. -/
theorem runSortAgree_of_local {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hs : ShapeOk p) {k : Nat} {root : CId} {ns : List Nat}
    (hroot : ∃ a, (a, root) ∈ p.roots)
    (hloc1 : LocalSortCoherent p ann ch (.evalConst k [] root))
    (hloc2 : ∀ f, evalConst p k [] root = .ok f →
      LocalSortCoherent p ann ch (.applyAll k f ((ns.map .lit).map .val))) :
    RunSortAgree p ann k root (ns.map .lit) := by
  obtain ⟨ar, ha⟩ := hroot
  have hpre1 : Pre p ann ch (.evalConst k [] root) := by
    rcases hf.wa.roots _ ha with hge | hin
    · exact Or.inl hge
    · exact Or.inr ⟨_, agree_nil_normalize (Agree.root _) _, hin⟩
  have hsa1 : SortAgree p ann (.evalConst k [] root) :=
    sortAgree_of_local hf hs hpre1 trivial hloc1
  refine ⟨hsa1, fun f hf0 => ?_⟩
  have hinv1 := inv_of_local hf hs hloc1
  have hfl : Live p ann ch f := (hinv1 _ .refl hpre1).2.1 f hf0 |>.1
  have hsf : SafeVal p ann ch f := (safe_core hinv1 _ .refl (Or.inl ⟨hpre1, trivial⟩)).1 f hf0
  -- Note: `AllFit` on literal slots depends only on `inv_of_local` at `.applyAll`, so we prove
  -- `AllFit` simultaneously using `hloc2 f hf0`? Even cleaner: build `AllFit` directly via
  -- `inv_of_local` on each literal step, or lift `hpre2` via `allFit_lits_local`!
  have hpre2 : ∀ (ss : List Slot) (g : Value),
      (∀ s ∈ ss, ∃ n, s = .val (.lit n)) →
      Live p ann ch g → SafeVal p ann ch g →
      LocalSortCoherent p ann ch (.applyAll k g ss) →
      SortAgree p ann (.applyAll k g ss) := by
    intro ss
    induction ss with
    | nil =>
      intro g _ hlg hsg hlocg
      exact sortAgree_of_local hf hs ⟨hlg, trivial⟩ ⟨hsg, fun _ hm => by cases hm⟩ hlocg
    | cons s rest ihss =>
      intro g hss hlg hsg hlocg
      obtain ⟨n, rfl⟩ := hss s (List.mem_cons_self ..)
      have hfit : SlotFits p ann ch g (.val (.lit n)) := by
        have hls : LiveSlot p ann ch (.val (.lit n)) := .val (.lit n) whole_lit
        cases g with
        | clo => exact fun _ => hls
        | pap _ _ _ =>
          cases hlg with
          | pap _ _ hmin _ =>
            exact ⟨fun _ => hls, minorsIgnore_snoc hmin (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)⟩
        | lit _ | str _ | con _ _ _ _ | irr _ _ _ => trivial
      have hlocHead : LocalSortCoherent p ann ch (.apply k g (.val (.lit n))) :=
        fun c hrc hprec hpost => hlocg c (by
          clear hprec hpost
          induction hrc with
          | refl => exact .step .refl Step.allHead
          | step _ hst ih' => exact .step ih' hst) hprec hpost
      have hsaHead : SortAgree p ann (.apply k g (.val (.lit n))) :=
        sortAgree_of_local hf hs ⟨hlg, hfit⟩ ⟨hsg, .val (.lit n)⟩ hlocHead
      have hinvHead := inv_of_local hf hs hlocHead
      have hsafeHead := safe_core hinvHead _ .refl (Or.inl ⟨⟨hlg, hfit⟩, hsg, .val (.lit n)⟩)
      -- Now every call reachable from `.applyAll k g (s :: rest)` is either itself (`SortCoherent = True`),
      -- reachable from `.apply k g s` (covered by `hsaHead`), or reachable from `.applyAll k v rest`
      -- (covered by `ihss`).
      intro c hrc
      cases hrc with
      | refl => trivial
      | step hrc' hst =>
        have hsplit : ∀ d, Reach p (.applyAll k g (.val (.lit n) :: rest)) d →
            d = .applyAll k g (.val (.lit n) :: rest) ∨
            Reach p (.apply k g (.val (.lit n))) d ∨
            ∃ v, apply p k g (.val (.lit n)) = .ok v ∧ Reach p (.applyAll k v rest) d := by
          intro d hrd
          induction hrd with
          | refl => exact Or.inl rfl
          | step _ hst' ihd =>
            rcases ihd with rfl | h1 | ⟨v, hv, h2⟩
            · cases hst' with
              | allHead => exact Or.inr (Or.inl .refl)
              | allRest hv => exact Or.inr (Or.inr ⟨_, hv, .refl⟩)
            · exact Or.inr (Or.inl (.step h1 hst'))
            · exact Or.inr (Or.inr ⟨v, hv, .step h2 hst'⟩)
        rcases hsplit _ (.step hrc' hst) with heq | h1 | ⟨v, hv, h2⟩
        · rw [heq]; trivial
        · exact hsaHead _ h1
        · have hlv : Live p ann ch v := (hinvHead _ .refl ⟨hlg, hfit⟩).2.1 v hv |>.1
          have hsv : SafeVal p ann ch v := hsafeHead.1 v hv
          have hlocRest : LocalSortCoherent p ann ch (.applyAll k v rest) :=
            fun d hrd hpred hpost => hlocg d (by
              clear hpred hpost
              induction hrd with
              | refl => exact .step .refl (Step.allRest hv)
              | step _ hst' ih' => exact .step ih' hst') hpred hpost
          exact ihss v (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) hlv hsv hlocRest _ h2
  exact hpre2 ((ns.map .lit).map .val) f (fun s hs' => by
    simp only [List.map_map, List.mem_map, Function.comp] at hs'
    obtain ⟨n, -, rfl⟩ := hs'
    exact ⟨n, rfl⟩) hfl hsf (hloc2 f hf0)

/-! ## Concrete kernel-evaluable static discharge (`SortClosed`) -/

/-- Structural `all` over a `NatMap` trie (D17 kernel-evaluable). -/
def natMapAll {α : Type} (f : Nat → α → Bool) : NatMap α → Nat → Nat → Bool
  | .leaf, _, _ => true
  | .node v z o, base, w =>
    (match v with | none => true | some x => f base x) &&
    natMapAll f z base (2 * w) &&
    natMapAll f o (base + w) (2 * w)

theorem natMapAll_get? {α : Type} {f : Nat → α → Bool} :
    ∀ (m : NatMap α) (base w k : Nat) {x : α},
      natMapAll f m base w = true → m.get? k = some x → f (base + w * k) x = true
  | .leaf, _, _, _, _, _, h => by simp [NatMap.get?] at h
  | .node v z o, base, w, k, x, ha, hg => by
    simp only [natMapAll, Bool.and_eq_true] at ha
    simp only [NatMap.get?] at hg
    split at hg
    · rename_i hk0
      have hk : k = 0 := beq_iff_eq.1 hk0
      subst hk; subst hg
      simpa using ha.1.1
    · split at hg
      · rename_i hk0 hmod
        have h1 := natMapAll_get? z base (2 * w) (k / 2) ha.1.2 hg
        have hk2 : 2 * (k / 2) = k := by have : k % 2 = 0 := beq_iff_eq.1 hmod; omega
        have heq : base + 2 * w * (k / 2) = base + w * k := by
          rw [Nat.mul_comm 2 w, Nat.mul_assoc, hk2]
        rwa [heq] at h1
      · rename_i hk0 hmod
        have h1 := natMapAll_get? o (base + w) (2 * w) (k / 2) ha.2 hg
        have hk2 : 2 * (k / 2) + 1 = k := by
          have : k % 2 ≠ 0 := fun h => hmod (beq_iff_eq.2 h); omega
        have heq : base + w + 2 * w * (k / 2) = base + w * k := by
          calc base + w + 2 * w * (k / 2)
              = base + (w * (2 * (k / 2)) + w) := by
                  rw [Nat.mul_comm 2 w, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm w]
            _ = base + w * (2 * (k / 2) + 1) := by rw [Nat.mul_succ]
            _ = base + w * k := by rw [hk2]
        rwa [heq] at h1

/-- Whether a `PropWhen` condition can ever hold (i.e., is not `.never`). -/
def propWhenCanHold : PropWhen → Bool
  | .never => false
  | .allZero _ => true

theorem propWhenCanHold_of_holds {ls : Levels} {pw : PropWhen}
    (h : pw.holds ls = true) : propWhenCanHold pw = true := by
  cases pw with
  | never => cases h
  | allZero _ => rfl

theorem propWhenCanHold_of_holdsP {q : Profile} {pw : PropWhen}
    (h : pw.holdsP q = true) : propWhenCanHold pw = true := by
  cases pw with
  | never => cases h
  | allZero _ => rfl

/-- Whether evaluating constant `c` at profile `q` and applying `n` arguments yields a receiver
that ignores argument `n` (`IgnoresNext`). Follows `csimp` chains up to `fuel` steps. -/
def headIgnoresAt (p : Program) (ann : Relevance.Ann) :
    Nat → CId → Profile → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, c, q, n =>
    match p.table.resolveOf c with
    | some (.csimp g vs _) =>
      decide (vs.length ≤ lvlsOf p g) && headIgnoresAt p ann fuel g ((q.inst vs).normalize (lvlsOf p g)) n
    | some (.eqn _ body) =>
      match (lamRels body)[n]? with
      | some r => r.irrP q
      | none => false
    | some (.case _) =>
      decide (n < p.headArity (.cases c)) &&
        match ann.constRel? c with
        | some cr =>
          match cr.params[n]? with
          | some r => r.irrP q
          | none => false
        | none => false
    | some (.prim _) => false
    | some (.word ..) => false
    | none =>
      match p.decl? c with
      | some (.defn .defn .safe _ _ body) =>
        match (lamRels body)[n]? with
        | some r => r.irrP q
        | none => false
      | some (.defn .opaq .safe _ _ body) =>
        p.table.isOpaqueByValue c &&
          match (lamRels body)[n]? with
          | some r => r.irrP q
          | none => false
      | some (.ctor ..) =>
        decide (n < p.headArity (.ctor c)) &&
          match ann.constRel? c with
          | some cr =>
            match cr.params[n]? with
            | some r => r.irrP q
            | none => false
          | none => false
      | some (.recr ..) =>
        decide (n < p.headArity (.recr c)) &&
          match ann.constRel? c with
          | some cr =>
            match cr.params[n]? with
            | some r => r.irrP q
            | none => false
          | none => false
      | some (.quot .ctor ..) =>
        decide (n < p.headArity (.quotMk c)) &&
          match ann.constRel? c with
          | some cr =>
            match cr.params[n]? with
            | some r => r.irrP q
            | none => false
          | none => false
      | some (.quot .lift ..) =>
        decide (n < p.headArity (.quotLift c)) &&
          match ann.constRel? c with
          | some cr =>
            match cr.params[n]? with
            | some r => r.irrP q
            | none => false
          | none => false
      | _ => false

/-- Whether rule `j`, field `i` of `case` key `c` may produce a non-erased sort-dropped marker. -/
def caseRuleSortDrop (p : Program) (ann : Relevance.Ann) (c : CId) (j i : Nat) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ _ ni _ rules _) =>
      let ordDrop :=
        match rules[j]? with
        | some rule =>
          match ann.ctorRel? rule.ctor with
          | some kr =>
            match kr.fields[i]? with
            | some cls => propWhenCanHold cls.dropWhen && !fieldWrittenErased p rule.ctor i
            | none => false
          | none => false
        | none => false
      let subDrop :=
        (j == 0) &&
        match p.table.recKindOf r with
        | some (.subsingleton _ srcs) =>
          match srcs[i]? with
          | some .proof => true
          | some (.index i') =>
            decide (ni ≤ i') ||
              match ann.constRel? c with
              | some cr =>
                match cr.params[np + 1 + i']? with
                | some rp => propWhenCanHold rp.irrWhen
                | none => false
              | none => false
          | none => false
        | _ => false
      ordDrop || subDrop
    | _ => false
  | _ => false

/-- Upper bound on the field index checked by `caseRuleSortDrop p ann c j`. -/
def caseRuleFieldCount (p : Program) (ann : Relevance.Ann) (c : CId) (j : Nat) : Nat :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ _ _ _ _ _ rules _) =>
      let ordN :=
        match rules[j]? with
        | some rule =>
          match ann.ctorRel? rule.ctor with
          | some kr => kr.fields.length
          | none => 0
        | none => 0
      let subN :=
        if j == 0 then
          match p.table.recKindOf r with
          | some (.subsingleton _ srcs) => srcs.length
          | _ => 0
        else 0
      max ordN subN
    | _ => 0
  | _ => 0

/-- Whether any minor of `case` key `c` can meet a non-erased sort-dropped field. -/
def caseHasSortDrop (p : Program) (ann : Relevance.Ann) (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ _ _ nmin _ _ _ _) =>
      (List.range nmin).any fun j =>
        (List.range (caseRuleFieldCount p ann c j)).any fun i =>
          caseRuleSortDrop p ann c j i
    | _ => false
  | _ => false

/-- Saturated spine check for a `caseHasSortDrop` key: every minor is relevant and its leading λs
ignore every sort-dropped field of its rule at `q`. -/
def caseSpineMinorsOk (p : Program) (ann : Relevance.Ann) (q : Profile)
    (c : CId) (args : List Term.Arg) : Bool :=
  if !caseHasSortDrop p ann c then true
  else
    match p.table.resolveOf c with
    | some (.case r) =>
      match p.decl? r with
      | some (.recr _ _ _ np _ nmin ni _ _ _) =>
        decide (p.headArity (.cases c) ≤ args.length) &&
        (List.range nmin).all fun j =>
          match args[np + 1 + ni + 1 + j]? with
          | some (minor, _, r_m) =>
            !r_m.irrP q &&
            (List.range (caseRuleFieldCount p ann c j)).all fun i =>
              if caseRuleSortDrop p ann c j i then
                match (lamRels minor)[i]? with
                | some br => br.irrP q
                | none => false
              else true
          | none => false
      | _ => false
    | _ => false

/-- Check Clause (f) for a projection at field index `i`: no constructor in `ch.ctors` drops field
`i` without writing it erased, and (for `i == 0`) no reached `Quot.mk` drops its element by sort. -/
def sortProjOk (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) (i : Nat) : Bool :=
  natMapAll (fun k kr =>
    match kr.fields[i]? with
    | some cls => if propWhenCanHold cls.dropWhen then fieldWrittenErased p k i else true
    | none => true) ch.ctors 0 1 &&
  (if i == 0 then
    ch.reached.all fun c =>
      match p.decl? c with
      | some (.quot .ctor _ _) =>
        match ann.constRel? c with
        | some cr =>
          match cr.params[2]? with
          | some rp => !propWhenCanHold rp.irrWhen
          | none => true
        | none => true
      | _ => true
   else true)

/-- Check Clause (a) at an irrelevant application spine `f`. -/
def sortAppIgnores (p : Program) (ann : Relevance.Ann) (q : Profile) (f : Term) : Bool :=
  let (hd, args) := f.spineL
  match hd with
  | .const c us => headIgnoresAt p ann 16 c ((q.inst us).normalize (lvlsOf p c)) args.length
  | .lam b d body =>
    match (lamRels (.lam b d body))[args.length]? with
    | some br => br.irrP q
    | none => false
  | _ => false

/-- Syntactic sort-coherence check over a term `t` at profile `q` (`inSpine = true` inside the
function prefix of an application spine). -/
def sortTermOk (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked)
    (q : Profile) : Bool → Term → Bool
  | _, .var _ | _, .sort _ | _, .pi .. | _, .natLit _ | _, .strLit _ => true
  | inSpine, .const c _ => inSpine || !caseHasSortDrop p ann c
  | _, .lam b _ body =>
    if b.propWhen.holdsP q then true
    else sortTermOk p ann ch q false body
  | _, .letE _ _ r _ v b =>
    (if r.irrP q then true else sortTermOk p ann ch q false v) &&
      sortTermOk p ann ch q false b
  | _, .proj _ i e =>
    sortProjOk p ann ch i && sortTermOk p ann ch q false e
  | inSpine, .app f a m r =>
    let wholeCheck :=
      if inSpine then true
      else
        match (Term.app f a m r).spineL with
        | (.const c _, args) => caseSpineMinorsOk p ann q c args
        | _ => true
    let appCheck :=
      if r.irrP q then sortAppIgnores p ann q f
      else sortTermOk p ann ch q false a
    wholeCheck && appCheck && sortTermOk p ann ch q true f

/-- Check Clause (d) on every rule of a reached recursor instance `(r, q)`. -/
def sortRecRuleOk (p : Program) (ann : Relevance.Ann) (r : CId) (q : Profile)
    (np nmot nmin ni : Nat) (rules : List Rule) : Bool :=
  let npre := np + nmot + nmin
  let cr? := ann.constRel? r
  let rk? := (p.table.recKindOf r).map (·.atProfile q)
  rules.zipIdx.all fun (rule, j) =>
    let lams := lamRels rule.rhs
    let lamIrr (idx : Nat) : Bool :=
      match lams[idx]? with
      | some b => b.irrP q
      | none => false
    let preOk := (List.range npre).all fun n =>
      match cr? with
      | some cr =>
        match cr.params[n]? with
        | some rp => if rp.irrP q then lamIrr n else true
        | none => true
      | none => true
    let fieldsOk :=
      match rk? with
      | some .ordinary =>
        match ann.ctorRel? rule.ctor with
        | some kr =>
          kr.fields.zipIdx.all fun (cls, fi) =>
            if propWhenCanHold cls.dropWhen && !fieldWrittenErased p rule.ctor fi then
              lamIrr (npre + fi)
            else true
        | none => true
      | some (.subsingleton _ srcs) =>
        if j == 0 then
          srcs.zipIdx.all fun (src, fi) =>
            match src with
            | .proof => lamIrr (npre + fi)
            | .index i =>
              if i ≥ ni then lamIrr (npre + fi)
              else
                match cr? with
                | some cr =>
                  match cr.params[npre + i]? with
                  | some rp => if rp.irrP q then lamIrr (npre + fi) else true
                  | none => true
                | none => true
        else true
      | _ => true
    preOk && fieldsOk

/-- Check Clause (e): if any `Quot.lift` is reached, no reached `Quot.mk` drops its element by sort. -/
def sortQuotOk (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Bool :=
  let hasLift := ch.reached.any fun c =>
    match specialHead? p c with
    | some (.quotLift _) => true
    | _ => false
  if !hasLift then true
  else
    ch.reached.all fun c =>
      match p.decl? c with
      | some (.quot .ctor _ ty) =>
        if 2 ∈ erasedParams ty then true
        else
          match ann.constRel? c with
          | some cr =>
            match cr.params[2]? with
            | some rp => !propWhenCanHold rp.irrWhen
            | none => true
          | none => true
      | _ => true

/-- **Kernel-evaluable static sort-coherence checker (D17).** When `SortClosed p ann ch = true` on a
recheck-accepted program, `Front.RunSortAgree` is discharged unconditionally. -/
def SortClosed (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Bool :=
  sortQuotOk p ann ch &&
  (p.roots.all fun (_, root) => !caseHasSortDrop p ann root) &&
  ch.instances.all fun (c, q) =>
    let termsOk := (p.runtimeKeys c).all fun key =>
      match p.termOf key with
      | some t => sortTermOk p ann ch q false t
      | none => true
    let csimpOk :=
      match p.table.resolveOf c with
      | some (.csimp g _ _) => !caseHasSortDrop p ann g
      | _ => true
    let recOk :=
      match specialHead? p c, p.decl? c with
      | some (.recr _), some (.recr _ _ _ np nmot nmin ni _ rules _) =>
        sortRecRuleOk p ann c q np nmot nmin ni rules
      | _, _ => true
    let caseOk :=
      match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r with
        | some (.recr _ _ _ _ _ nmin _ _ rules _) => decide (nmin ≤ rules.length)
        | _ => true
      | _ => true
    termsOk && csimpOk && recOk && caseOk

/-! ### Soundness of `SortClosed` -/

private theorem headIgnoresAt_special {p : Program} {ann : Relevance.Ann}
    {k1 k2 : Nat} {ls ls' : Levels} {ρ : Env} {c : CId} {q : Profile} {h : Head}
    {args : List Term.Arg} {v0 fv : Value}
    (hc : headConst? h = some c) (hag : Agree ls' q)
    (hlt : args.length < p.headArity h)
    (hcr : ∃ cr r, ann.constRel? c = some cr ∧ cr.params[args.length]? = some r ∧ r.irrP q = true)
    (hv0 : headValue p k1 ls' h = .ok v0) (he : applySpine p k2 ls ρ v0 args = .ok fv) :
    IgnoresNext ann fv := by
  obtain ⟨cr, r, hcr', hrp, hirrP⟩ := hcr
  have hne : (p.headArity h == 0) = false := by simp; omega
  rw [headValue_eq, hne] at hv0
  simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at hv0
  subst hv0
  rw [applySpine_pap_lt p k2 ls ρ h ls' [] args (by simpa using hlt)] at he
  obtain ⟨ss, hss, he⟩ := bind_ok_inv he
  simp only [List.nil_append, Sem.Result.ok.injEq] at he
  subst he
  have hl := slotsOf_length p k2 ls ρ _ _ hss
  exact ⟨c, cr, r, hc, hcr', by rw [hl]; exact hrp, by rw [← hag.irr]; exact hirrP⟩

private theorem evalConst_applySpine_ignoresAt {p : Program} {ann : Relevance.Ann} :
    ∀ (fuel : Nat) {k1 k2 : Nat} {ls ls' : Levels} {ρ : Env} {c : CId} {q : Profile}
      {args : List Term.Arg} {v0 fv : Value},
      Agree ls' q →
      headIgnoresAt p ann fuel c q args.length = true →
      evalConst p k1 ls' c = .ok v0 →
      applySpine p k2 ls ρ v0 args = .ok fv →
      IgnoresNext ann fv
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _, _ => by cases h
  | fuel + 1, k1, k2, ls, ls', ρ, c, q, args, v0, fv, hag, h, hv0, he => by
    unfold headIgnoresAt at h
    rw [evalConst_eq] at hv0
    cases hres : p.table.resolveOf c with
    | some e =>
      rw [hres] at h hv0
      cases e with
      | csimp g vs thm =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        cases k1 with
        | zero => cases hv0
        | succ k' =>
          simp only [Sem.later_succ, eval_const] at hv0
          exact evalConst_applySpine_ignoresAt fuel (hag.inst vs (lvlsOf p g) h.1) h.2 hv0 he
      | eqn thm body =>
        cases hr : (lamRels body)[args.length]? with
        | none => simp [hr] at h
        | some r =>
          simp only [hr] at h
          cases k1 with
          | zero => cases hv0
          | succ k' =>
            simp only [Sem.later_succ] at hv0
            cases body with
            | lam b d t =>
              rw [eval_lam] at hv0
              cases hv0
              exact (applySpine_lamChain args b d t [] ls' r fv hr (by rw [← hag.irr]; exact h) he).1
            | _ => simp [lamRels] at hr
      | case r' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        cases hcr : ann.constRel? c with
        | none => simp [hcr] at h
        | some cr =>
          rw [hcr] at h
          cases hrp : cr.params[args.length]? with
          | none => simp [hrp] at h
          | some r =>
            simp only [hrp] at h
            exact headIgnoresAt_special (h := .cases c) rfl hag h.1 ⟨cr, r, hcr, hrp, h.2⟩ hv0 he
      | prim _ => cases h
      | word _ _ _ => cases h
    | none =>
      rw [hres] at h hv0
      cases hd : p.decl? c with
      | none => rw [hd] at h; cases h
      | some d =>
        rw [hd] at h hv0
        cases d with
        | defn kind safety lv ty body =>
          cases kind <;> cases safety <;> try (cases h; done)
          · cases hr : (lamRels body)[args.length]? with
            | none => simp [hr] at h
            | some r =>
              simp only [hr] at h
              cases k1 with
              | zero => cases hv0
              | succ k' =>
                simp only [Sem.later_succ] at hv0
                cases body with
                | lam b d t =>
                  rw [eval_lam] at hv0
                  cases hv0
                  exact (applySpine_lamChain args b d t [] ls' r fv hr (by rw [← hag.irr]; exact h) he).1
                | _ => simp [lamRels] at hr
          · simp only [Bool.and_eq_true] at h
            rw [h.1] at hv0
            simp only [ite_true] at hv0
            cases hr : (lamRels body)[args.length]? with
            | none => simp [hr] at h
            | some r =>
              simp only [hr] at h
              cases k1 with
              | zero => cases hv0
              | succ k' =>
                simp only [Sem.later_succ] at hv0
                cases body with
                | lam b d t =>
                  rw [eval_lam] at hv0
                  cases hv0
                  exact (applySpine_lamChain args b d t [] ls' r fv hr (by rw [← hag.irr]; exact h.2) he).1
                | _ => simp [lamRels] at hr
        | ctor =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          cases hcr : ann.constRel? c with
          | none => simp [hcr] at h
          | some cr =>
            rw [hcr] at h
            cases hrp : cr.params[args.length]? with
            | none => simp [hrp] at h
            | some r =>
              simp only [hrp] at h
              exact headIgnoresAt_special (h := .ctor c) rfl hag h.1 ⟨cr, r, hcr, hrp, h.2⟩ hv0 he
        | recr =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          cases hcr : ann.constRel? c with
          | none => simp [hcr] at h
          | some cr =>
            rw [hcr] at h
            cases hrp : cr.params[args.length]? with
            | none => simp [hrp] at h
            | some r =>
              simp only [hrp] at h
              exact headIgnoresAt_special (h := .recr c) rfl hag h.1 ⟨cr, r, hcr, hrp, h.2⟩ hv0 he
        | quot qk lv ty =>
          cases qk with
          | ctor =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            cases hcr : ann.constRel? c with
            | none => simp [hcr] at h
            | some cr =>
              rw [hcr] at h
              cases hrp : cr.params[args.length]? with
              | none => simp [hrp] at h
              | some r =>
                simp only [hrp] at h
                exact headIgnoresAt_special (h := .quotMk c) rfl hag h.1 ⟨cr, r, hcr, hrp, h.2⟩ hv0 he
          | lift =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            cases hcr : ann.constRel? c with
            | none => simp [hcr] at h
            | some cr =>
              rw [hcr] at h
              cases hrp : cr.params[args.length]? with
              | none => simp [hrp] at h
              | some r =>
                simp only [hrp] at h
                exact headIgnoresAt_special (h := .quotLift c) rfl hag h.1 ⟨cr, r, hcr, hrp, h.2⟩ hv0 he
          | _ => cases h
        | _ => cases h

private theorem univsOk_spineHead {p : Program} : ∀ {t : Term},
    univsOk p t = true → univsOk p t.spineL.1 = true
  | .app f a m r, hu => by
    rw [spineL_app]
    simp only [univsOk, Bool.and_eq_true] at hu
    exact univsOk_spineHead hu.1
  | .var _, hu | .sort _, hu | .const .., hu | .lam .., hu | .pi .., hu
  | .letE .., hu | .proj .., hu | .natLit _, hu | .strLit _, hu => by
    simpa [Term.spineL, Term.spine, Term.spine.go] using hu

private theorem eval_sort_prefix {p : Program} {ann : Relevance.Ann}
    {k : Nat} {ls : Levels} {ρ : Env} {q : Profile} {f : Term} {fv : Value}
    (hag : Agree ls q) (hu : univsOk p f = true)
    (hig : sortAppIgnores p ann q f = true) (he : eval p k ls ρ f = .ok fv) :
    IgnoresNext ann fv := by
  have hmk := mkApps_spineL f
  rw [← hmk, eval_mkApps] at he
  obtain ⟨v0, hv0, he⟩ := bind_ok_inv he
  have huhd := univsOk_spineHead hu
  unfold sortAppIgnores at hig
  cases hsp : f.spineL with
  | mk H args =>
    rw [hsp] at hv0 he huhd hig
    dsimp only at hv0 he huhd hig
    cases H with
    | const c us =>
      rw [eval_const] at hv0
      have hlen : us.length ≤ lvlsOf p c := by simpa [univsOk] using huhd
      exact evalConst_applySpine_ignoresAt 16 (hag.inst us (lvlsOf p c) hlen) hig hv0 he
    | lam b d body =>
      rw [eval_lam] at hv0
      cases hv0
      cases hbr : (lamRels (.lam b d body))[args.length]? with
      | none => simp [hbr] at hig
      | some br =>
        simp only [hbr] at hig
        exact (applySpine_lamChain args b d body ρ ls br fv hbr (by rw [← hag.irr]; exact hig) he).1
    | _ => cases hig

private theorem caseRuleSortDrop_lt_fieldCount {p : Program} {ann : Relevance.Ann}
    {c : CId} {j i : Nat} (h : caseRuleSortDrop p ann c j i = true) :
    i < caseRuleFieldCount p ann c j := by
  unfold caseRuleSortDrop at h
  unfold caseRuleFieldCount
  cases hres : p.table.resolveOf c with
  | none => simp [hres] at h
  | some e =>
    rw [hres] at h
    cases e with
    | case r =>
      dsimp only at h
      cases hd : p.decl? r with
      | none => simp [hd] at h
      | some d =>
        rw [hd] at h
        cases d with
        | recr sf kk lv np nmot nmin ni ind rules ty =>
          dsimp only at h
          simp only [Bool.or_eq_true] at h
          rcases h with hord | hsub
          · cases hr : rules[j]? with
            | none => simp [hr] at hord
            | some rule =>
              rw [hr] at hord; dsimp only at hord
              cases hkr : ann.ctorRel? rule.ctor with
              | none => simp [hkr] at hord
              | some kr =>
                rw [hkr] at hord; dsimp only at hord
                cases hf : kr.fields[i]? with
                | none => simp [hf] at hord
                | some cls =>
                  have hlt := (List.getElem?_eq_some_iff.1 hf).1
                  simp only [hd, hr, hkr]
                  exact Nat.lt_of_lt_of_le hlt (Nat.le_max_left ..)
          · simp only [Bool.and_eq_true, beq_iff_eq] at hsub
            obtain ⟨rfl, hsub⟩ := hsub
            cases hrk : p.table.recKindOf r with
            | none => simp [hrk] at hsub
            | some rk =>
              rw [hrk] at hsub
              cases rk with
              | subsingleton w srcs =>
                dsimp only at hsub
                cases hs : srcs[i]? with
                | none => simp [hs] at hsub
                | some src =>
                  have hlt := (List.getElem?_eq_some_iff.1 hs).1
                  simp only [hd, beq_self_eq_true, ↓reduceIte, hrk]
                  exact Nat.lt_of_lt_of_le hlt (Nat.le_max_right ..)
              | _ => simp at hsub
        | _ => simp at h
    | _ => simp at h

private theorem caseHasSortDrop_false_rule {p : Program} {ann : Relevance.Ann}
    {c r : CId} {sf kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hres : p.table.resolveOf c = some (.case r))
    (hd : p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty))
    (hno : caseHasSortDrop p ann c = false) {j i : Nat} (hj : j < nmin) :
    caseRuleSortDrop p ann c j i = false := by
  cases hdrop : caseRuleSortDrop p ann c j i with
  | false => rfl
  | true =>
    exfalso
    have hlt := caseRuleSortDrop_lt_fieldCount hdrop
    have htrue : caseHasSortDrop p ann c = true := by
      unfold caseHasSortDrop
      rw [hres]; dsimp only; rw [hd]
      simp only [List.any_eq_true, List.mem_range]
      exact ⟨j, hj, i, hlt, hdrop⟩
    rw [hno] at htrue
    cases htrue

/-- `SortWhole`: not a partial application of a `case` key with sort-dropped fields. -/
private def SortWhole (p : Program) (ann : Relevance.Ann) (v : Value) : Prop :=
  ∀ c ls args, v = .pap (.cases c) ls args → caseHasSortDrop p ann c = false

/-- `SortWholeTerm`: a term whose spine head is not an unsaturated `caseHasSortDrop` key. -/
private def SortWholeTerm (p : Program) (ann : Relevance.Ann) (t : Term) : Prop :=
  ∀ c us, t.spineL.1 = .const c us → caseHasSortDrop p ann c = true →
    p.headArity (.cases c) ≤ t.spineL.2.length

/-- Per-minor sort invariant on `.cases c` partial applications. -/
private def SortMinorsIgnore (p : Program) (ann : Relevance.Ann) (h : Head) (args : List Slot) : Prop :=
  ∀ c r sf kk lv np nmot nmin ni ind rules ty,
    h = .cases c → p.table.resolveOf c = some (.case r) →
    p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
    ∀ j s, j < nmin → args[np + 1 + ni + 1 + j]? = some s →
    ∀ i, caseRuleSortDrop p ann c j i = true → IgnoresSlot s i

/-- Constructor marker well-formedness tracked for Clauses (c), (d), (e), (f). -/
private def ConMarkerWF (p : Program) (ch : Relevance.Checked) (c : CId) (fs : List Value) : Prop :=
  (∀ i v, fs[i]? = some v → v.isIrr = true →
    ∀ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) → i < nf) ∧
  (∀ i v, fs[i]? = some v → v.isIrr = true → p.isQuotCtor c = true → i = 0 ∧ c ∈ ch.reached)

mutual

private inductive GoodVal (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Value → Prop
  | lit (n : Nat) : GoodVal p ann ch (.lit n)
  | str (s : String) : GoodVal p ann ch (.str s)
  | irr (t : Option Term) (ρ : Env) (ls : Levels) : GoodVal p ann ch (.irr t ρ ls)
  | con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} :
      ConMarkerWF p ch c fs →
      (∀ v ∈ fs, GoodVal p ann ch v) →
      (∀ v ∈ fs, SortWhole p ann v) →
      GoodVal p ann ch (.con c ls ps fs)
  | clo {b : Binder} {d body : Term} {ρ : Env} {ls : Levels} (q : Profile) :
      Agree ls q →
      RefsHandled p ch q (.lam b d body) →
      univsOk p (.lam b d body) = true →
      sortTermOk p ann ch q false (.lam b d body) = true →
      GoodEnv p ann ch ρ →
      GoodVal p ann ch (.clo b d body ρ ls)
  | pap {h : Head} {ls : Levels} {args : List Slot} :
      HeadSeen p ch ls h →
      (∀ s ∈ args, GoodSlot p ann ch s) →
      SortMinorsIgnore p ann h args →
      args.length < p.headArity h →
      GoodVal p ann ch (.pap h ls args)

private inductive GoodSlot (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Slot → Prop
  | val {v : Value} : GoodVal p ann ch v → SortWhole p ann v → GoodSlot p ann ch (.val v)
  | name {t : Term} {ρ : Env} {ls : Levels} (q : Profile) :
      Agree ls q →
      RefsHandled p ch q t →
      univsOk p t = true →
      sortTermOk p ann ch q false t = true →
      GoodEnv p ann ch ρ →
      GoodSlot p ann ch (.name t ρ ls)

private inductive GoodEnv (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Env → Prop
  | mk {ρ : Env} : (∀ s ∈ ρ, GoodSlot p ann ch s) → GoodEnv p ann ch ρ

end

private def GoodFrame (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked)
    (ls : Levels) (ρ : Env) (t : Term) : Prop :=
  ∃ q, Agree ls q ∧ GoodEnv p ann ch ρ ∧ RefsHandled p ch q t ∧ univsOk p t = true ∧
    (sortTermOk p ann ch q false t = true ∨
      ∃ more : List Term.Arg, more ≠ [] ∧ sortTermOk p ann ch q true t = true ∧
        match (Term.mkApps t more).spineL with
        | (.const c _, args) => caseSpineMinorsOk p ann q c args = true
        | _ => True)

private def GoodSlotFits (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) :
    Value → Slot → Prop
  | .pap h _ args, s => GoodSlot p ann ch s ∧ SortMinorsIgnore p ann h (args ++ [s])
  | _, s => GoodSlot p ann ch s

private def GoodAllFit (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked)
    (k : Nat) : Value → List Slot → Prop
  | _, [] => True
  | f, s :: ss => GoodSlotFits p ann ch f s ∧ ∀ v, apply p k f s = .ok v → GoodAllFit p ann ch k v ss

private def GoodCall (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Call → Prop
  | .eval _ ls ρ t => GoodFrame p ann ch ls ρ t
  | .evalConst _ ls c => p.size ≤ c ∨ ∃ q, Agree ls q ∧ (c, q) ∈ ch.instances
  | .headValue _ ls h => HeadSeen p ch ls h
  | .apply _ f s => GoodVal p ann ch f ∧ GoodSlotFits p ann ch f s
  | .applyAll k f ss => GoodVal p ann ch f ∧ GoodAllFit p ann ch k f ss
  | .fire _ h ls args => args.length = p.headArity h ∧ HeadSeen p ch ls h ∧
      (∀ s ∈ args, GoodSlot p ann ch s) ∧ SortMinorsIgnore p ann h args
  | .force _ s => GoodSlot p ann ch s
  | .forceAll _ ss => ∀ s ∈ ss, GoodSlot p ann ch s

private def GoodPost (p : Program) (ann : Relevance.Ann) (ch : Relevance.Checked) : Call → Prop
  | .eval k ls ρ t => ∀ v, eval p k ls ρ t = .ok v →
      GoodVal p ann ch v ∧ (SortWholeTerm p ann t → SortWhole p ann v)
  | .evalConst k ls c => ∀ v, evalConst p k ls c = .ok v →
      GoodVal p ann ch v ∧ (caseHasSortDrop p ann c = false → SortWhole p ann v)
  | .headValue k ls h => ∀ v, headValue p k ls h = .ok v →
      GoodVal p ann ch v ∧ ((∀ c, h = .cases c → caseHasSortDrop p ann c = false) → SortWhole p ann v)
  | .apply k f s => ∀ v, apply p k f s = .ok v →
      GoodVal p ann ch v ∧ (SortWhole p ann f → SortWhole p ann v)
  | .applyAll k f ss => ∀ v, applyAll p k f ss = .ok v →
      GoodVal p ann ch v ∧ (SortWhole p ann f → SortWhole p ann v)
  | .fire k h ls args => ∀ v, fire p k h ls args = .ok v →
      GoodVal p ann ch v ∧ SortWhole p ann v
  | .force k s => ∀ v, force p k s = .ok v →
      GoodVal p ann ch v ∧ SortWhole p ann v
  | .forceAll k ss => ∀ vs, forceAll p k ss = .ok vs →
      ∀ v ∈ vs, GoodVal p ann ch v ∧ SortWhole p ann v

private theorem sortWhole_lit {p : Program} {ann : Relevance.Ann} {n : Nat} :
    SortWhole p ann (.lit n) := fun _ _ _ h => nomatch h

private theorem sortWhole_str {p : Program} {ann : Relevance.Ann} {s : String} :
    SortWhole p ann (.str s) := fun _ _ _ h => nomatch h

private theorem sortWhole_irr {p : Program} {ann : Relevance.Ann} {t : Option Term} {ρ : Env} {ls : Levels} :
    SortWhole p ann (.irr t ρ ls) := fun _ _ _ h => nomatch h

private theorem sortWhole_con {p : Program} {ann : Relevance.Ann} {c : CId} {ls : Levels}
    {ps : List Slot} {fs : List Value} :
    SortWhole p ann (.con c ls ps fs) := fun _ _ _ h => nomatch h

private theorem sortWhole_clo {p : Program} {ann : Relevance.Ann} {b : Binder} {d body : Term}
    {ρ : Env} {ls : Levels} :
    SortWhole p ann (.clo b d body ρ ls) := fun _ _ _ h => nomatch h

private theorem sortMinorsIgnore_of_sortWhole {p : Program} {ann : Relevance.Ann}
    {h : Head} {ls : Levels} {args args' : List Slot} (hw : SortWhole p ann (.pap h ls args)) :
    SortMinorsIgnore p ann h args' := by
  intro c r sf kk lv np nmot nmin ni ind rules ty hh hres hd j s hj _ i hdrop
  subst hh
  have hno := hw c ls args rfl
  rw [caseHasSortDrop_false_rule hres hd hno hj] at hdrop
  cases hdrop

private theorem sortMinorsIgnore_snoc {p : Program} {ann : Relevance.Ann}
    {h : Head} {args : List Slot} {s : Slot} (hm : SortMinorsIgnore p ann h args)
    (hnew : ∀ c r sf kk lv np nmot nmin ni ind rules ty,
      h = .cases c → p.table.resolveOf c = some (.case r) →
      p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      ∀ j, j < nmin → np + 1 + ni + 1 + j = args.length →
      ∀ i, caseRuleSortDrop p ann c j i = true → IgnoresSlot s i) :
    SortMinorsIgnore p ann h (args ++ [s]) := by
  intro c r sf kk lv np nmot nmin ni ind rules ty hh hres hd j s' hj hget i hdrop
  by_cases hlt : np + 1 + ni + 1 + j < args.length
  · rw [List.getElem?_append_left hlt] at hget
    exact hm c r sf kk lv np nmot nmin ni ind rules ty hh hres hd j s' hj hget i hdrop
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hget
    have hlt' := (List.getElem?_eq_some_iff.1 hget).1
    simp only [List.length_singleton] at hlt'
    have heq : np + 1 + ni + 1 + j = args.length := by omega
    rw [heq, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact hnew c r sf kk lv np nmot nmin ni ind rules ty hh hres hd j hj heq i hdrop

private theorem sortWholeTerm_of_sortTermOk {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {q : Profile} {t : Term} (h : sortTermOk p ann ch q false t = true) :
    SortWholeTerm p ann t := by
  intro c us hhd hdrop
  cases t with
  | const c' us' =>
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.const.injEq] at hhd
    obtain ⟨rfl, rfl⟩ := hhd
    simp [sortTermOk, hdrop] at h
  | app f a m r =>
    simp only [sortTermOk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    have hw := h.1.1
    rw [show (Term.app f a m r).spineL = ((Term.app f a m r).spineL.1, (Term.app f a m r).spineL.2) from rfl, hhd] at hw
    unfold caseSpineMinorsOk at hw
    simp only [hdrop, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
    cases hres : p.table.resolveOf c with
    | none => simp [hres] at hw
    | some e =>
      rw [hres] at hw
      cases e with
      | case r' =>
        dsimp only at hw
        cases hd : p.decl? r' with
        | none => simp [hd] at hw
        | some d =>
          rw [hd] at hw
          cases d with
          | recr =>
            dsimp only at hw
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
            exact hw.1
          | _ => simp at hw
      | _ => simp at hw
  | _ => simp [Term.spineL, Term.spine, Term.spine.go] at hhd

private theorem sortTermOk_peel {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {lvls : Nat} {q : Profile} :
    ∀ (n : Nat) (t body : Term) (bs : List Rel),
      peelLams n t = some body → TermS p ann lvls q bs t →
      sortTermOk p ann ch q false t = true →
      sortTermOk p ann ch q false body = true
  | 0, t, body, _, h, _, hst => by
    simp only [peelLams, Option.some.injEq] at h; subst h; exact hst
  | n + 1, t, body, bs, h, hts, hst => by
    cases t with
    | lam b d t =>
      simp only [peelLams] at h
      cases hts with
      | lam _ _ hp hts' =>
        simp only [sortTermOk, hp, Bool.false_eq_true, ↓reduceIte] at hst
        exact sortTermOk_peel n t body _ h hts' hst
    | _ => simp [peelLams] at h

private theorem goodFrame_nonAppConst {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {ρ : Env} {t : Term}
    (h : GoodFrame p ann ch ls ρ t) (happ : ∀ f a m r, t ≠ .app f a m r) (hc : ∀ c us, t ≠ .const c us) :
    ∃ q, Agree ls q ∧ GoodEnv p ann ch ρ ∧ RefsHandled p ch q t ∧ univsOk p t = true ∧
      sortTermOk p ann ch q false t = true := by
  obtain ⟨q, hag, henv, hrefs, hu, hok | ⟨_, -, hok, -⟩⟩ := h
  · exact ⟨q, hag, henv, hrefs, hu, hok⟩
  · cases t with
    | app f a m r => exact (happ f a m r rfl).elim
    | const c us => exact (hc c us rfl).elim
    | _ => exact ⟨q, hag, henv, hrefs, hu, hok⟩

private theorem goodFrame_app_parts {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : GoodFrame p ann ch ls ρ (.app f a m r)) :
    ∃ q, Agree ls q ∧ GoodEnv p ann ch ρ ∧ RefsHandled p ch q (.app f a m r) ∧
      univsOk p (.app f a m r) = true ∧ sortTermOk p ann ch q true f = true ∧
      (r.irrP q = true → sortAppIgnores p ann q f = true) ∧
      (r.irrP q = false → sortTermOk p ann ch q false a = true) ∧
      ∃ more : List Term.Arg,
        match (Term.mkApps f ((a, m, r) :: more)).spineL with
        | (.const c _, args) => caseSpineMinorsOk p ann q c args = true
        | _ => True := by
  obtain ⟨q, hag, henv, hrefs, hu, hok | ⟨more, -, hok, hsp⟩⟩ := h
  · simp only [sortTermOk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
    refine ⟨q, hag, henv, hrefs, hu, hok.2, ?_, ?_, [], ?_⟩
    · intro hr; simpa [hr] using hok.1.2
    · intro hr; simpa [hr] using hok.1.2
    · have hw := hok.1.1
      simp only [Term.mkApps, List.foldl_cons, List.foldl_nil]
      cases hsp : (Term.app f a m r).spineL with
      | mk hd args =>
        rw [hsp] at hw
        cases hd with
        | const _ _ => exact hw
        | _ => trivial
  · simp only [sortTermOk, ↓reduceIte, Bool.true_and, Bool.and_eq_true] at hok
    refine ⟨q, hag, henv, hrefs, hu, hok.2, ?_, ?_, more, ?_⟩
    · intro hr; simpa [hr] using hok.1
    · intro hr; simpa [hr] using hok.1
    · exact hsp

private theorem goodFrame_fun {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : GoodFrame p ann ch ls ρ (.app f a m r)) : GoodFrame p ann ch ls ρ f := by
  obtain ⟨q, hag, henv, hrefs, hu, hfok, -, -, more, hsp⟩ := goodFrame_app_parts h
  refine ⟨q, hag, henv, ?_, ?_, Or.inr ⟨(a, m, r) :: more, List.cons_ne_nil _ _, hfok, hsp⟩⟩
  · intro x hx
    apply hrefs x
    simp only [Term.relevantRefs]
    split
    · exact hx
    · exact relevantRefs_mono q a _ hx
  · simp only [univsOk, Bool.and_eq_true] at hu
    exact hu.1

private theorem goodFrame_arg {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : GoodFrame p ann ch ls ρ (.app f a m r)) (hrel : r.irrAt ls = false) :
    ∃ q, Agree ls q ∧ GoodEnv p ann ch ρ ∧ RefsHandled p ch q a ∧ univsOk p a = true ∧
      sortTermOk p ann ch q false a = true := by
  obtain ⟨q, hag, henv, hrefs, hu, -, -, haok, -⟩ := goodFrame_app_parts h
  have hrq : r.irrP q = false := by rw [hag.irr]; exact hrel
  refine ⟨q, hag, henv, ?_, ?_, haok hrq⟩
  · intro x hx
    apply hrefs x
    simp only [Term.relevantRefs, hrq, Bool.false_eq_true, ↓reduceIte]
    rw [relevantRefs_append q a]
    exact List.mem_append_left _ hx
  · simp only [univsOk, Bool.and_eq_true, Bool.or_eq_true] at hu
    rcases hu.2 with h' | h'
    · rw [alwaysIrr_irrAt h' ls] at hrel; cases hrel
    · exact h'

private theorem good_mkWord {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) {c : CId} (hc : c ∈ ch.reached) {w : Width} {op : WordOp} {thm : CId}
    (hres : p.table.resolveOf c = some (.word w op thm)) {w' : Width} {n : Nat} {v : Value}
    (hm : p.mkWord? w' n = some v) :
    GoodVal p ann ch v ∧ SortWhole p ann v := by
  cases h1 : p.wordCtor? w' with
  | none => simp [Program.mkWord?, h1] at hm
  | some c0 =>
    cases h2 : p.known.bitVecOfFin with
    | none => simp [Program.mkWord?, h1, h2] at hm
    | some bv =>
      cases h3 : p.known.finMk with
      | none => simp [Program.mkWord?, h1, h2, h3] at hm
      | some fin =>
        simp [Program.mkWord?, h1, h2, h3] at hm
        subst hm
        obtain ⟨⟨sf, lv, ind, cidx, np, ty, hdfin⟩, -⟩ :=
          hf.canon.finProof c hc w op thm hres fin h3
        refine ⟨.con ⟨fun i v hi hirr => ?_, fun i v hi hirr => ?_⟩ (fun v1 hv1 => ?_) (fun v1 hv1 => ?_), sortWhole_con⟩
        · cases i with
          | zero => cases hi; simp [Value.isIrr] at hirr
          | succ _ => simp at hi
        · cases i with
          | zero => cases hi; simp [Value.isIrr] at hirr
          | succ _ => simp at hi
        · simp only [List.mem_singleton] at hv1; subst hv1
          refine .con ⟨fun i v hi hirr => ?_, fun i v hi hirr => ?_⟩ (fun v2 hv2 => ?_) (fun v2 hv2 => ?_)
          · cases i with
            | zero => cases hi; simp [Value.isIrr] at hirr
            | succ _ => simp at hi
          · cases i with
            | zero => cases hi; simp [Value.isIrr] at hirr
            | succ _ => simp at hi
          · simp only [List.mem_singleton] at hv2; subst hv2
            refine .con ⟨fun i v hi hirr sf' lv' ind' cidx' np' nf' ty' hd' => ?_,
                fun i v hi hirr hiq => ?_⟩ (fun v3 hv3 => ?_) (fun v3 hv3 => ?_)
            · rw [hdfin] at hd'
              simp only [Option.some.injEq, Decl.ctor.injEq] at hd'
              obtain ⟨-, -, -, -, -, rfl, -⟩ := hd'
              have hlt := (List.getElem?_eq_some_iff.1 hi).1
              simpa using hlt
            · obtain ⟨lv', ty', hdq⟩ := decl_of_isQuotCtor hiq
              rw [hdfin] at hdq; cases hdq
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
              rcases hv3 with rfl | rfl
              · exact .lit n
              · exact .irr ..
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
              rcases hv3 with rfl | rfl
              · exact sortWhole_lit
              · exact sortWhole_irr
          · simp only [List.mem_singleton] at hv2; subst hv2; exact sortWhole_con
        · simp only [List.mem_singleton] at hv1; subst hv1; exact sortWhole_con

private theorem good_getD {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {args : List Slot} (hargs : ∀ s ∈ args, GoodSlot p ann ch s) (i : Nat) :
    GoodSlot p ann ch (args.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : args[i]? with
  | none => exact .val (.lit 0) sortWhole_lit
  | some s => exact hargs s (List.mem_iff_getElem?.2 ⟨i, hi⟩)

private theorem good_getD_irr {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {args : List Slot} {ls : Levels} (hargs : ∀ s ∈ args, GoodSlot p ann ch s) (i : Nat) :
    GoodSlot p ann ch (args.getD i (Slot.irrNone ls)) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : args[i]? with
  | none => exact .val (.irr ..) sortWhole_irr
  | some s => exact hargs s (List.mem_iff_getElem?.2 ⟨i, hi⟩)

private theorem good_selectRule {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ind np j : Nat} {major : Value} {fields : List Slot}
    (hm : GoodVal p ann ch major) (hsel : p.selectRule ind np major = some (j, fields)) :
    ∀ s ∈ fields, GoodSlot p ann ch s := by
  cases major with
  | lit m =>
    simp only [Program.selectRule] at hsel
    split at hsel
    · split at hsel
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        rw [← hsel.2]; intro _ h; cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        rw [← hsel.2]; intro s hs
        simp only [List.mem_singleton] at hs; subst hs
        exact .val (.lit _) sortWhole_lit
    · cases hsel
  | con c lsv ps fs =>
    cases hm with
    | con _ hfs hws =>
      simp only [Program.selectRule] at hsel
      cases hd : p.decl? c with
      | none => rw [hd] at hsel; cases hsel
      | some d =>
        rw [hd] at hsel
        cases d with
        | ctor =>
          simp only at hsel
          split at hsel
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
            rw [← hsel.2]
            intro s hs
            obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hs
            exact .val (hfs v hv) (hws v hv)
          · cases hsel
        | _ => simp at hsel
  | _ => simp [Program.selectRule] at hsel

private theorem good_subsingleton_fields {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {ls : Levels} {srcs : List FieldSrc} {indices : List Slot}
    (hi : ∀ s ∈ indices, GoodSlot p ann ch s) :
    ∀ s ∈ srcs.map (fun
      | .index i => indices.getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls), GoodSlot p ann ch s := by
  intro s hs
  obtain ⟨src, -, rfl⟩ := List.mem_map.1 hs
  cases src with
  | proof => exact .val (.irr ..) sortWhole_irr
  | index i =>
    dsimp only
    rw [List.getD_eq_getElem?_getD]
    cases hget : indices[i]? with
    | none => exact .val (.irr ..) sortWhole_irr
    | some s' => exact hi s' (List.mem_iff_getElem?.2 ⟨i, hget⟩)

/-- Unrolling a spine prefix whose value is not `SortWhole`: it must be `.pap (.cases c) ls' args`
with `c` the spine head and `args.length = f.spineL.2.length`. -/
private theorem unroll_sort {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    {k : Nat} {ls : Levels} {ρ : Env} :
    ∀ (f : Term) {fv : Value},
      (∀ d, CallLt d (.eval k ls ρ f) → GoodCall p ann ch d →
        GoodPost p ann ch d ∧ ∀ c', Step p d c' → GoodCall p ann ch c') →
      GoodPost p ann ch (.eval k ls ρ f) →
      (∀ c', Step p (.eval k ls ρ f) c' → GoodCall p ann ch c') →
      eval p k ls ρ f = .ok fv → ¬ SortWhole p ann fv →
      ∃ c us ls' args, f.spineL.1 = .const c us ∧ fv = .pap (.cases c) ls' args ∧
        args.length = f.spineL.2.length
  | .app f a m r, fv, ih, hpost, hsteps, he, hnw => by
    rw [eval_app_slot] at he
    obtain ⟨fv', hfv', he⟩ := bind_ok_inv he
    obtain ⟨s, hs, he⟩ := bind_ok_inv he
    have hst := slotOf_step hfv' hs
    have hpa := hsteps _ hst
    obtain ⟨hpost_a, hsteps_a⟩ := ih _ (step_lt hst) hpa
    have hnw' : ¬ SortWhole p ann fv' := fun hw => hnw ((hpost_a fv he).2 hw)
    have hpf := hsteps _ Step.appFun
    have ihf : ∀ d, CallLt d (.eval k ls ρ f) → GoodCall p ann ch d →
        GoodPost p ann ch d ∧ ∀ c', Step p d c' → GoodCall p ann ch c' :=
      fun d hlt => ih d (callLt_trans hlt (step_lt (p := p) Step.appFun))
    obtain ⟨hpost_f, hsteps_f⟩ := ih _ (step_lt (p := p) Step.appFun) hpf
    obtain ⟨c, us, ls', args, hhd, rfl, hlen⟩ := unroll_sort f ihf hpost_f hsteps_f hfv' hnw'
    rw [apply_pap] at he
    split at he
    · rename_i heq
      have harity : (args ++ [s]).length = p.headArity (.cases c) := beq_iff_eq.1 heq
      have hpfire := hsteps_a _ (Step.papFire harity)
      have hlt_fire : CallLt (.fire k (.cases c) ls' (args ++ [s])) (.eval k ls ρ (.app f a m r)) :=
        callLt_trans (step_lt (Step.papFire harity)) (step_lt hst)
      exact (hnw ((ih _ hlt_fire hpfire).1 fv he).2).elim
    · split at he
      · simp only [Sem.Result.ok.injEq] at he
        subst he
        exact ⟨c, us, ls', args ++ [s], by simp [spineL_app, hhd], rfl, by simp [spineL_app, hlen]⟩
      · cases he
  | .const c us, fv, ih, _, hsteps, he, hnw => by
    rw [eval_const] at he
    have hpc := hsteps _ Step.const
    have hpost := (ih _ (step_lt (p := p) Step.const) hpc).1 fv he
    have hdrop : caseHasSortDrop p ann c = true := by
      cases hd : caseHasSortDrop p ann c
      · exact (hnw (hpost.2 hd)).elim
      · rfl
    unfold caseHasSortDrop at hdrop
    cases hres : p.table.resolveOf c with
    | none => simp [hres] at hdrop
    | some e =>
      rw [hres] at hdrop
      cases e with
      | case r =>
        dsimp only at hdrop
        cases hdr : p.decl? r with
        | none => simp [hdr] at hdrop
        | some d =>
          rw [hdr] at hdrop
          cases d with
          | recr sf kk lv np nmot nmin ni ind rules ty =>
            dsimp only at hdrop
            rw [evalConst_eq, hres, headValue_eq] at he
            have hne : (p.headArity (.cases c) == 0) = false := by
              rw [headArity_cases hres hdr]; simp
            rw [hne] at he
            simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at he
            exact ⟨c, us, us.map (evalUniv ls), [], rfl, he.symm, rfl⟩
          | _ => simp at hdrop
      | _ => simp at hdrop
  | .var _, fv, _, hpost, _, he, hnw | .sort _, fv, _, hpost, _, he, hnw
  | .lam .., fv, _, hpost, _, he, hnw | .pi .., fv, _, hpost, _, he, hnw
  | .letE .., fv, _, hpost, _, he, hnw | .proj .., fv, _, hpost, _, he, hnw
  | .natLit _, fv, _, hpost, _, he, hnw | .strLit _, fv, _, hpost, _, he, hnw => by
    exact (hnw ((hpost fv he).2 (fun c us hhd _ => by
      simp [Term.spineL, Term.spine, Term.spine.go] at hhd))).elim

/-- **Theorem 1 (`SortClosed` invariant):** `GoodCall` is preserved by every `Step` and produces
`GoodPost` values, with zero dependence on `Pre` or `Live`. -/
private theorem good_core {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hsc : SortClosed p ann ch = true) :
    ∀ c, GoodCall p ann ch c → GoodPost p ann ch c ∧ ∀ c', Step p c c' → GoodCall p ann ch c' := by
  have hinstsAll : ∀ inst ∈ ch.instances,
      (∀ key ∈ p.runtimeKeys inst.1, ∀ t, p.termOf key = some t →
        sortTermOk p ann ch inst.2 false t = true) ∧
      (∀ g vs thm, p.table.resolveOf inst.1 = some (.csimp g vs thm) →
        caseHasSortDrop p ann g = false) := by
    unfold SortClosed at hsc
    simp only [Bool.and_eq_true, List.all_eq_true] at hsc
    intro inst hin
    have hi := hsc.2 inst hin
    refine ⟨fun key hk t ht => ?_, fun g vs thm hres => ?_⟩
    · have h1 := hi.1.1.1 key hk
      simpa [ht] using h1
    · have h2 := hi.1.1.2
      rw [hres] at h2
      simpa using h2
  intro c
  induction c using callLt_wf.induction with
  | _ c ih =>
    intro hgood
    have ihStep : ∀ {c'}, (h : Step p c c') → GoodCall p ann ch c' → GoodPost p ann ch c' :=
      fun h hg' => (ih _ (step_lt h) hg').1
    cases c with
    | eval k ls ρ t =>
      cases t with
      | var i =>
        obtain ⟨_, _, henv, -, -, -⟩ :=
          goodFrame_nonAppConst hgood (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        cases henv with
        | mk hρ =>
          refine ⟨fun v hv => ?_, fun c' hstep => ?_⟩
          · rw [eval_var] at hv
            cases hget : ρ[i]? with
            | none => rw [hget] at hv; cases hv
            | some s =>
              rw [hget] at hv
              have hgs := hρ s (List.mem_iff_getElem?.2 ⟨i, hget⟩)
              have hp := ihStep (Step.var hget) hgs v hv
              exact ⟨hp.1, fun _ => hp.2⟩
          · cases hstep with
            | var hget => exact hρ _ (List.mem_iff_getElem?.2 ⟨i, hget⟩)
      | sort u =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [eval_sort] at hv; cases hv; exact ⟨.irr .., fun _ => sortWhole_irr⟩
      | pi b d c0 =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [eval_pi] at hv; cases hv; exact ⟨.irr .., fun _ => sortWhole_irr⟩
      | natLit n =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [eval_natLit] at hv; cases hv; exact ⟨.lit n, fun _ => sortWhole_lit⟩
      | strLit s =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [eval_strLit] at hv; cases hv; exact ⟨.str s, fun _ => sortWhole_str⟩
      | lam b d body =>
        obtain ⟨q, hag, henv, hrefs, hu, hok⟩ :=
          goodFrame_nonAppConst hgood (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [eval_lam] at hv; cases hv
        exact ⟨.clo q hag hrefs hu hok henv, fun _ => sortWhole_clo⟩
      | letE nd m r ty v b =>
        obtain ⟨q, hag, henv, hrefs, hu, hok⟩ :=
          goodFrame_nonAppConst hgood (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        simp only [sortTermOk, Bool.and_eq_true] at hok
        simp only [univsOk, Bool.and_eq_true] at hu
        have hrb : RefsHandled p ch q b := fun x hx => by
          apply hrefs x
          simp only [Term.relevantRefs]
          rw [relevantRefs_append q b]
          exact List.mem_append_left _ hx
        have hrv : r.irrAt ls = false → RefsHandled p ch q v := fun hrel x hx => by
          have hrq : r.irrP q = false := by rw [hag.irr]; exact hrel
          apply hrefs x
          simp only [Term.relevantRefs, hrq, Bool.false_eq_true, ↓reduceIte]
          apply relevantRefs_mono q b
          rw [relevantRefs_append q v]
          exact List.mem_append_left _ hx
        have huv : r.irrAt ls = false → univsOk p v = true := fun hrel => by
          simp only [Bool.or_eq_true] at hu
          rcases hu.1 with h' | h'
          · rw [alwaysIrr_irrAt h' ls] at hrel; cases hrel
          · exact h'
        have hokv : r.irrAt ls = false → sortTermOk p ann ch q false v = true := fun hrel => by
          have hrq : r.irrP q = false := by rw [hag.irr]; exact hrel
          simpa [hrq] using hok.1
        have hStep : ∀ c', Step p (.eval k ls ρ (.letE nd m r ty v b)) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases henv with
          | mk hρ =>
            cases hstep with
            | letIrr _ =>
              exact ⟨q, hag, .mk fun s hs => by
                rcases List.mem_cons.1 hs with rfl | hs
                · exact .val (.irr ..) sortWhole_irr
                · exact hρ s hs, hrb, hu.2, Or.inl hok.2⟩
            | letVal hrel =>
              exact ⟨q, hag, .mk hρ, hrv hrel, huv hrel, Or.inl (hokv hrel)⟩
            | letBody hrel hv =>
              have hgv := ihStep (Step.letVal hrel) ⟨q, hag, .mk hρ, hrv hrel, huv hrel, Or.inl (hokv hrel)⟩ _ hv
              exact ⟨q, hag, .mk fun s hs => by
                rcases List.mem_cons.1 hs with rfl | hs
                · exact .val hgv.1 (hgv.2 (sortWholeTerm_of_sortTermOk (hokv hrel)))
                · exact hρ s hs, hrb, hu.2, Or.inl hok.2⟩
        refine ⟨fun w hw => ?_, hStep⟩
        rw [eval_letE] at hw
        split at hw
        · rename_i hirr
          have hp := ihStep (Step.letIrr hirr) (hStep _ (Step.letIrr hirr)) w hw
          exact ⟨hp.1, fun _ => hp.2 (sortWholeTerm_of_sortTermOk hok.2)⟩
        · rename_i hrel
          have hrel' : r.irrAt ls = false := by simpa using hrel
          obtain ⟨x, hx, hw⟩ := bind_ok_inv hw
          have hp := ihStep (Step.letBody hrel' hx) (hStep _ (Step.letBody hrel' hx)) w hw
          exact ⟨hp.1, fun _ => hp.2 (sortWholeTerm_of_sortTermOk hok.2)⟩
      | proj s i e =>
        obtain ⟨q, hag, henv, hrefs, hu, hok⟩ :=
          goodFrame_nonAppConst hgood (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
        simp only [sortTermOk, Bool.and_eq_true] at hok
        have hpe : GoodCall p ann ch (.eval k ls ρ e) := ⟨q, hag, henv, hrefs, hu, Or.inl hok.2⟩
        refine ⟨fun v hv => ?_, fun c' hstep => by cases hstep; exact hpe⟩
        rw [eval_proj] at hv
        obtain ⟨v0, hv0, hpf⟩ := bind_ok_inv hv
        have hgv0 := (ihStep Step.proj hpe v0 hv0).1
        cases v0 with
        | con c0 lsv ps fs =>
          cases hgv0 with
          | con _ hfs hws =>
            simp only [Program.projectField] at hpf
            split at hpf
            · split at hpf
              · cases hfi : fs[i]? with
                | none => simp [hfi, Sem.Result.ofOption] at hpf
                | some w =>
                  simp [hfi, Sem.Result.ofOption] at hpf
                  subst hpf
                  exact ⟨hfs w (List.mem_iff_getElem?.2 ⟨i, hfi⟩), fun _ => hws w (List.mem_iff_getElem?.2 ⟨i, hfi⟩)⟩
              · cases hpf
            · cases hpf
        | _ => simp [Program.projectField] at hpf
      | app f a m r =>
        have hgf : GoodCall p ann ch (.eval k ls ρ f) := goodFrame_fun hgood
        obtain ⟨hpost_f, hsteps_f⟩ := ih _ (step_lt (p := p) Step.appFun) hgf
        have ihf : ∀ d, CallLt d (.eval k ls ρ f) → GoodCall p ann ch d →
            GoodPost p ann ch d ∧ ∀ c', Step p d c' → GoodCall p ann ch c' :=
          fun d hlt => ih d (callLt_trans hlt (step_lt (p := p) Step.appFun))
        -- Helper: build `GoodCall (.apply k fv s)` from `eval f = .ok fv` and `slotOf = .ok s`
        have hgoodApply : ∀ {fv s}, eval p k ls ρ f = .ok fv → slotOf p k ls ρ (a, m, r) = .ok s →
            GoodCall p ann ch (.apply k fv s) := by
          intro fv s hfv hs0
          have hgv := (hpost_f fv hfv).1
          have hgs : GoodSlot p ann ch s := by
            simp only [slotOf] at hs0
            split at hs0
            · cases hs0; exact .val (.irr ..) sortWhole_irr
            · rename_i hrel
              have hrel' : r.irrAt ls = false := by simpa using hrel
              obtain ⟨qa, haga, henva, hrefsa, hua, hoka⟩ := goodFrame_arg hgood hrel'
              cases m with
              | strict =>
                obtain ⟨x, hx, hs0⟩ := bind_ok_inv hs0
                cases hs0
                have hgx := ihStep (Step.appArg hfv hrel') ⟨qa, haga, henva, hrefsa, hua, Or.inl hoka⟩ x hx
                exact .val hgx.1 (hgx.2 (sortWholeTerm_of_sortTermOk hoka))
              | byName =>
                cases hs0
                exact .name qa haga hrefsa hua hoka henva
          refine ⟨hgv, ?_⟩
          cases fv with
          | pap h ls' args =>
            refine ⟨hgs, ?_⟩
            by_cases hw : SortWhole p ann (.pap h ls' args)
            · exact sortMinorsIgnore_of_sortWhole hw
            · cases hgv with
              | pap _ _ hmin _ =>
                refine sortMinorsIgnore_snoc hmin ?_
                obtain ⟨c0, us, ls'', args', hhd, he', hlen⟩ :=
                  unroll_sort f ihf hpost_f hsteps_f hfv hw
                cases he'
                intro c' r' sf kk lv np nmot nmin ni ind rules ty hc' hres hd j hj hpos i hdrop
                cases hc'
                obtain ⟨q, hag, -, -, -, -, -, -, more, hsp⟩ := goodFrame_app_parts hgood
                have hspine : (Term.mkApps f ((a, m, r) :: more)).spineL =
                    (.const c0 us, f.spineL.2 ++ (a, m, r) :: more) := by
                  rw [spineL_mkApps', hhd]
                rw [hspine] at hsp
                have hcd : caseHasSortDrop p ann c0 = true := by
                  unfold caseHasSortDrop
                  rw [hres]; dsimp only; rw [hd]
                  simp only [List.any_eq_true, List.mem_range]
                  exact ⟨j, hj, i, caseRuleSortDrop_lt_fieldCount hdrop, hdrop⟩
                unfold caseSpineMinorsOk at hsp
                simp only [hcd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hres, hd,
                  Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsp
                have hmj := hsp.2 j hj
                have hget : (f.spineL.2 ++ (a, m, r) :: more)[np + 1 + ni + 1 + j]? = some (a, m, r) := by
                  rw [hpos, hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
                    List.getElem?_cons_zero]
                rw [hget] at hmj
                simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at hmj
                have hrrel : r.irrAt ls = false := by rw [← hag.irr]; exact hmj.1
                have hmi := hmj.2 i (caseRuleSortDrop_lt_fieldCount hdrop)
                simp only [hdrop, ↓reduceIte] at hmi
                cases hbr : (lamRels a)[i]? with
                | none => simp [hbr] at hmi
                | some br =>
                  simp only [hbr] at hmi
                  exact ignoresSlot_of_slotOf hs0 hrrel i br hbr (by rw [← hag.irr]; exact hmi)
          | _ => exact hgs
        have hStep : ∀ c', Step p (.eval k ls ρ (.app f a m r)) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | appFun => exact hgf
          | appIrr hfv hirr => exact hgoodApply hfv (by simp [slotOf, hirr])
          | appArg _ hrel =>
            obtain ⟨qa, haga, henva, hrefsa, hua, hoka⟩ := goodFrame_arg hgood hrel
            exact ⟨qa, haga, henva, hrefsa, hua, Or.inl hoka⟩
          | appStrict hfv hrel hx => exact hgoodApply hfv (by simp [slotOf, hrel, hx, Sem.Result.bind])
          | appName hfv hrel => exact hgoodApply hfv (by simp [slotOf, hrel])
        refine ⟨fun v hv => ?_, hStep⟩
        rw [eval_app_slot] at hv
        obtain ⟨fv, hfv, hv⟩ := bind_ok_inv hv
        obtain ⟨s, hs0, hv⟩ := bind_ok_inv hv
        have hst := slotOf_step hfv hs0
        have hpa := hgoodApply hfv hs0
        obtain ⟨hpost_a, hsteps_a⟩ := ih _ (step_lt hst) hpa
        refine ⟨(hpost_a v hv).1, fun hwt => ?_⟩
        by_cases hw : SortWhole p ann fv
        · exact (hpost_a v hv).2 hw
        · obtain ⟨c0, us, ls', args, hhd, rfl, hlen⟩ :=
            unroll_sort f ihf hpost_f hsteps_f hfv hw
          have hcd : caseHasSortDrop p ann c0 = true := by
            cases hd : caseHasSortDrop p ann c0
            · exact (hw (fun c' _ _ he => by cases he; exact hd)).elim
            · rfl
          have harle := hwt c0 us (by simp [spineL_app, hhd]) hcd
          simp only [spineL_app, List.length_append, List.length_singleton] at harle
          cases hpa.1 with
          | pap _ _ _ hlt =>
            have harity : (args ++ [s]).length = p.headArity (.cases c0) := by
              simp only [List.length_append, List.length_singleton]; omega
            have hv' : fire p k (.cases c0) ls' (args ++ [s]) = .ok v := by
              rw [apply_pap] at hv
              simp only [harity, beq_self_eq_true, ↓reduceIte] at hv
              exact hv
            have hpfire := hsteps_a _ (Step.papFire harity)
            have hlt_fire : CallLt (.fire k (.cases c0) ls' (args ++ [s])) (.eval k ls ρ (.app f a m r)) :=
              callLt_trans (step_lt (Step.papFire harity)) (step_lt hst)
            exact ((ih _ hlt_fire hpfire).1 v hv').2
      | const c0 us =>
        obtain ⟨q, hag, -, hrefs, hu, -⟩ := hgood
        have hpc : GoodCall p ann ch (.evalConst k (us.map (evalUniv ls)) c0) := by
          have hmem : (c0, q.inst us) ∈ (Term.const c0 us).relevantRefs q [] := by
            simp [Term.relevantRefs]
          rcases hrefs _ hmem with hge | hin
          · exact Or.inl hge
          · exact Or.inr ⟨_, hag.inst us (lvlsOf p c0) (by simpa [univsOk] using hu), hin⟩
        refine ⟨fun v hv => ?_, fun c' hstep => by cases hstep; exact hpc⟩
        rw [eval_const] at hv
        obtain ⟨hgv, hw⟩ := ihStep Step.const hpc v hv
        refine ⟨hgv, fun hwt => hw ?_⟩
        cases hcd : caseHasSortDrop p ann c0
        · rfl
        · exfalso
          have harle := hwt c0 us rfl hcd
          simp only [Term.spineL, Term.spine, Term.spine.go, List.length_nil] at harle
          unfold caseHasSortDrop at hcd
          cases hres : p.table.resolveOf c0 with
          | none => simp [hres] at hcd
          | some e =>
            rw [hres] at hcd
            cases e with
            | case r0 =>
              dsimp only at hcd
              cases hd : p.decl? r0 with
              | none => simp [hd] at hcd
              | some d =>
                rw [hd] at hcd
                cases d with
                | recr => rw [headArity_cases hres hd] at harle; omega
                | _ => simp at hcd
            | _ => simp at hcd
    | evalConst k ls c0 =>
      rcases hgood with hge | ⟨q, hag, hinst⟩
      · obtain ⟨hent, hres⟩ := hf.canon.dense c0 hge
        have hd : p.decl? c0 = none := by simp [Program.decl?, hent]
        refine ⟨fun v hv => ?_, fun c' hstep => ?_⟩
        · rw [evalConst_eq] at hv; simp [hres, hd] at hv
        · cases hstep <;> simp_all
      · have hreached : c0 ∈ ch.reached := hf.reached (c0, q) hinst
        obtain ⟨htermOk, hcsimpNoDrop⟩ := hinstsAll (c0, q) hinst
        have hseen : ∀ h, specialHead? p c0 = some h → headConst? h = some c0 → HeadSeen p ch ls h :=
          fun h hsp hc => ⟨fun c' hc' => by rw [hc] at hc'; cases hc'; exact ⟨hsp, q, hag, hinst⟩,
            fun _ _ hw => by subst hw; simp [headConst?] at hc⟩
        have hbody : ∀ key t, key ∈ p.runtimeKeys c0 → p.termOf key = some t →
            GoodFrame p ann ch ls [] t ∧ SortWholeTerm p ann t := by
          intro key t hk ht
          have hst := htermOk key hk t ht
          exact ⟨⟨q, hag, (.mk fun _ hm => by cases hm), refsHandled_runtime hf hinst hk ht,
            (hf.canon.univs c0 hreached).1 key hk t ht, Or.inl hst⟩, sortWholeTerm_of_sortTermOk hst⟩
        have hcsimp : ∀ g vs thm, p.table.resolveOf c0 = some (.csimp g vs thm) →
            GoodFrame p ann ch ls [] (.const g vs) ∧ SortWholeTerm p ann (.const g vs) := by
          intro g vs thm hres
          have hnd := hcsimpNoDrop g vs thm hres
          have hrefs : RefsHandled p ch q (.const g vs) := fun x hx => by
            simp only [Term.relevantRefs, List.mem_singleton] at hx
            subst hx
            apply hf.wa.closed (c0, q) hinst
            simp [Program.instRefs, Program.runtimeRefs, hres]
          have hst : sortTermOk p ann ch q false (.const g vs) = true := by
            simp [sortTermOk, hnd]
          exact ⟨⟨q, hag, (.mk fun _ hm => by cases hm), hrefs,
            (hf.canon.univs c0 hreached).2 g vs thm hres, Or.inl hst⟩, sortWholeTerm_of_sortTermOk hst⟩
        have hStep : ∀ c', Step p (.evalConst k ls c0) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | prim _ => exact ⟨fun _ hc' => by simp [headConst?] at hc', fun _ _ hw => by cases hw⟩
          | word hres => exact ⟨fun _ hc' => by simp [headConst?] at hc', fun _ _ hw => by cases hw; exact ⟨c0, hreached, _, hres⟩⟩
          | csimp hres => exact (hcsimp _ _ _ hres).1
          | eqn hres => exact (hbody (.eqn c0) _ (by simp [Program.runtimeKeys, hres]) (by simp [Program.termOf, hres])).1
          | case hres => exact hseen _ (by simp [specialHead?, hres]) rfl
          | ctor hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
          | recr hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
          | quotMk hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
          | quotLift hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
          | defn hres hd => exact (hbody (.value c0) _ (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd]) (by simp [Program.termOf, hd])).1
          | opaq hres hd hop => exact (hbody (.value c0) _ (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd, hop]) (by simp [Program.termOf, hd])).1
        refine ⟨fun v hv => ?_, hStep⟩
        rw [evalConst_eq] at hv
        cases hres : p.table.resolveOf c0 with
        | some e =>
          rw [hres] at hv
          cases e with
          | prim op =>
            have hp := ihStep (Step.prim hres) (hStep _ (Step.prim hres)) v hv
            exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
          | word w op thm =>
            have hp := ihStep (Step.word hres) (hStep _ (Step.word hres)) v hv
            exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
          | csimp g vs thm =>
            cases k with
            | zero => cases hv
            | succ k' =>
              simp only [Sem.later_succ] at hv
              have hp := ihStep (Step.csimp hres) (hStep _ (Step.csimp hres)) v hv
              exact ⟨hp.1, fun _ => hp.2 (hcsimp g vs thm hres).2⟩
          | eqn thm body =>
            cases k with
            | zero => cases hv
            | succ k' =>
              simp only [Sem.later_succ] at hv
              have hp := ihStep (Step.eqn hres) (hStep _ (Step.eqn hres)) v hv
              exact ⟨hp.1, fun _ => hp.2 (hbody (.eqn c0) body (by simp [Program.runtimeKeys, hres]) (by simp [Program.termOf, hres])).2⟩
          | case r' =>
            have hp := ihStep (Step.case hres) (hStep _ (Step.case hres)) v hv
            exact ⟨hp.1, fun hnd => hp.2 (fun c' hc' => by cases hc'; exact hnd)⟩
        | none =>
          rw [hres] at hv
          cases hd : p.decl? c0 with
          | none => rw [hd] at hv; cases hv
          | some d =>
            rw [hd] at hv
            cases d with
            | ctor =>
              have hp := ihStep (Step.ctor hres hd) (hStep _ (Step.ctor hres hd)) v hv
              exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
            | recr =>
              have hp := ihStep (Step.recr hres hd) (hStep _ (Step.recr hres hd)) v hv
              exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
            | quot qk lv ty =>
              cases qk with
              | ctor =>
                have hp := ihStep (Step.quotMk hres hd) (hStep _ (Step.quotMk hres hd)) v hv
                exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
              | lift =>
                have hp := ihStep (Step.quotLift hres hd) (hStep _ (Step.quotLift hres hd)) v hv
                exact ⟨hp.1, fun _ => hp.2 (fun _ hc => nomatch hc)⟩
              | _ => cases hv
            | defn kind safety lv ty body =>
              cases kind with
              | defn =>
                cases safety with
                | safe =>
                  cases k with
                  | zero => cases hv
                  | succ k' =>
                    simp only [Sem.later_succ] at hv
                    have hp := ihStep (Step.defn hres hd) (hStep _ (Step.defn hres hd)) v hv
                    exact ⟨hp.1, fun _ => hp.2 (hbody (.value c0) body (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd]) (by simp [Program.termOf, hd])).2⟩
                | _ => cases hv
              | opaq =>
                cases safety with
                | safe =>
                  simp only at hv
                  split at hv
                  · rename_i hop
                    cases k with
                    | zero => cases hv
                    | succ k' =>
                      simp only [Sem.later_succ] at hv
                      have hp := ihStep (Step.opaq hres hd hop) (hStep _ (Step.opaq hres hd hop)) v hv
                      exact ⟨hp.1, fun _ => hp.2 (hbody (.value c0) body (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd, hop]) (by simp [Program.termOf, hd])).2⟩
                  · cases hv
                | _ => cases hv
              | thm => cases hv
            | _ => cases hv
    | headValue k ls h =>
      have hStep : ∀ c', Step p (.headValue k ls h) c' → GoodCall p ann ch c' := by
        intro c' hstep
        cases hstep with
        | nullary h0 =>
          exact ⟨by simp [h0], hgood, (fun _ hm => by cases hm),
            (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hget => by simp at hget)⟩
      refine ⟨fun v hv => ?_, hStep⟩
      rw [headValue_eq] at hv
      split at hv
      · rename_i h0
        have hp := ihStep (Step.nullary (beq_iff_eq.1 h0)) (hStep _ (Step.nullary (beq_iff_eq.1 h0))) v hv
        exact ⟨hp.1, fun _ => hp.2⟩
      · rename_i hne
        cases hv
        have hpos : 0 < p.headArity h := by
          have : p.headArity h ≠ 0 := fun h0 => hne (beq_iff_eq.2 h0); omega
        exact ⟨.pap hgood (fun _ hm => by cases hm)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hget => by simp at hget) hpos,
          fun hnd c' _ _ he => by cases he; exact hnd c' rfl⟩
    | apply k f s =>
      obtain ⟨hgf, hgs⟩ := hgood
      have hStep : ∀ c', Step p (.apply k f s) c' → GoodCall p ann ch c' := by
        intro c' hstep
        cases hstep with
        | @beta _ b d body ρ' ls' _ hbeta =>
          cases hgf with
          | clo q hag hrefs hu hok henv =>
            have hnotp : b.propWhen.holdsP q = false := by
              have hb : b.propWhen.holds ls' = false := by
                simpa [PropWhen.allowsBeta] using hbeta
              rwa [← hag.holds] at hb
            have hok' : sortTermOk p ann ch q false body = true := by
              simpa [sortTermOk, hnotp] using hok
            have hrefs' : RefsHandled p ch q body := fun x hx =>
              hrefs x (by simpa [Term.relevantRefs, hnotp] using hx)
            have hu' : univsOk p body = true := by simpa [univsOk] using hu
            cases henv with
            | mk hρ =>
              exact ⟨q, hag, .mk fun s' hs' => by
                rcases List.mem_cons.1 hs' with rfl | hs'
                · exact hgs
                · exact hρ s' hs', hrefs', hu', Or.inl hok'⟩
        | papFire har =>
          cases hgf with
          | pap hseen hargs _ _ =>
            exact ⟨har, hseen, fun s' hs' => by
              rcases List.mem_append.1 hs' with hs' | hs'
              · exact hargs s' hs'
              · simp only [List.mem_singleton] at hs'; subst hs'; exact hgs.1, hgs.2⟩
      refine ⟨fun v hv => ?_, hStep⟩
      cases f with
      | clo b d body ρ ls =>
        rw [apply_clo] at hv
        split at hv
        · rename_i hbeta
          cases k with
          | zero => cases hv
          | succ k' =>
            simp only [Sem.later_succ] at hv
            have hp := ihStep (Step.beta hbeta) (hStep _ (Step.beta hbeta)) v hv
            cases hgf with
            | clo q hag _ _ hok _ =>
              have hnotp : b.propWhen.holdsP q = false := by
                have hb : b.propWhen.holds ls = false := by simpa [PropWhen.allowsBeta] using hbeta
                rwa [← hag.holds] at hb
              have hok' : sortTermOk p ann ch q false body = true := by simpa [sortTermOk, hnotp] using hok
              exact ⟨hp.1, fun _ => hp.2 (sortWholeTerm_of_sortTermOk hok')⟩
        · cases hv
      | pap h ls args =>
        rw [apply_pap] at hv
        split at hv
        · rename_i har
          have hp := ihStep (Step.papFire (beq_iff_eq.1 har)) (hStep _ (Step.papFire (beq_iff_eq.1 har))) v hv
          exact ⟨hp.1, fun _ => hp.2⟩
        · split at hv
          · rename_i hlt
            cases hv
            cases hgf with
            | pap hseen hargs _ _ =>
              refine ⟨.pap hseen (fun s' hs' => ?_) hgs.2 hlt, fun hw c' _ _ he => ?_⟩
              · rcases List.mem_append.1 hs' with hs' | hs'
                · exact hargs s' hs'
                · simp only [List.mem_singleton] at hs'; subst hs'; exact hgs.1
              · cases he; exact hw c' ls args rfl
          · cases hv
      | lit _ | str _ | con _ _ _ _ | irr _ _ _ =>
        rw [apply_other p k _ s (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)] at hv
        cases hv
    | applyAll k f ss =>
      obtain ⟨hgf, hfit⟩ := hgood
      cases ss with
      | nil =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [applyAll_nil] at hv; cases hv; exact ⟨hgf, id⟩
      | cons s rest =>
        have hStep : ∀ c', Step p (.applyAll k f (s :: rest)) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | allHead => exact ⟨hgf, hfit.1⟩
          | allRest hv =>
            exact ⟨(ihStep Step.allHead ⟨hgf, hfit.1⟩ _ hv).1, hfit.2 _ hv⟩
        refine ⟨fun v hv => ?_, hStep⟩
        rw [applyAll_cons] at hv
        obtain ⟨v0, hv0, hv⟩ := bind_ok_inv hv
        have hp1 := ihStep Step.allHead ⟨hgf, hfit.1⟩ v0 hv0
        have hp2 := ihStep (Step.allRest hv0) (hStep _ (Step.allRest hv0)) v hv
        exact ⟨hp2.1, fun hw => hp2.2 (hp1.2 hw)⟩
    | fire k h ls args =>
      obtain ⟨har, hseen, hargs, hmin⟩ := hgood
      cases h with
      | ctor c0 =>
        have hStep : ∀ c', Step p (.fire k (.ctor c0) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | ctorArgs _ => exact fun s hs' => hargs s (mem_of_mem_drop' hs')
        refine ⟨fun v hv => ?_, hStep⟩
        rw [fire_ctor] at hv
        cases hd : p.decl? c0 with
        | none => rw [hd] at hv; cases hv
        | some d =>
          rw [hd] at hv
          cases d with
          | ctor sf lv ind cidx np nf ty =>
            obtain ⟨vs, hvs, hv⟩ := bind_ok_inv hv
            have hpvs := ihStep (Step.ctorArgs hd) (hStep _ (Step.ctorArgs hd)) vs hvs
            have hvlen : vs.length = nf := by
              have hlen := (forceAll_ok_get _ hvs).1
              rw [hlen, List.length_drop, har]
              simp only [Program.headArity, hd]
              omega
            unfold ctorResult at hv
            split at hv
            · cases hv; exact ⟨.lit 0, sortWhole_lit⟩
            · split at hv
              · cases vs with
                | cons v1 r1 =>
                  cases v1 with
                  | lit n => cases r1 with
                    | nil => cases hv; exact ⟨.lit (n + 1), sortWhole_lit⟩
                    | cons _ _ => cases hv
                  | _ => cases hv
                | nil => cases hv
              · cases hv
                refine ⟨.con ⟨fun i w hi _ sf' lv' ind' cidx' np' nf' ty' hd' => ?_,
                    fun _ _ _ _ hiq => ?_⟩ (fun v hv' => (hpvs v hv').1) (fun v hv' => (hpvs v hv').2), sortWhole_con⟩
                · rw [hd] at hd'
                  simp only [Option.some.injEq, Decl.ctor.injEq] at hd'
                  obtain ⟨-, -, -, -, -, rfl, -⟩ := hd'
                  have := (List.getElem?_eq_some_iff.1 hi).1; omega
                · obtain ⟨lv', ty', hdq⟩ := decl_of_isQuotCtor hiq
                  rw [hd] at hdq; cases hdq
          | _ => cases hv
      | quotMk c0 =>
        have hStep : ∀ c', Step p (.fire k (.quotMk c0) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | mkArg => exact hargs _ (by simp)
        refine ⟨fun v hv => ?_, hStep⟩
        rw [fire_quotMk] at hv
        match args with
        | [α, r0, a0] =>
          obtain ⟨v0, hv0, hv⟩ := bind_ok_inv hv
          cases hv
          have hpv0 := ihStep Step.mkArg (hStep _ Step.mkArg) v0 hv0
          obtain ⟨hsp, q, -, hinst⟩ := hseen.1 c0 rfl
          have hreached : c0 ∈ ch.reached := hf.reached (c0, q) hinst
          obtain ⟨lv, ty, hdq⟩ := decl_of_quotMk hsp
          refine ⟨.con ⟨fun _ _ _ _ _ _ _ _ _ _ _ hdc => ?_, fun i w hi _ _ => ?_⟩
            (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hpv0.1)
            (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hpv0.2), sortWhole_con⟩
          · rw [hdq] at hdc; cases hdc
          · cases i with
            | zero => exact ⟨rfl, hreached⟩
            | succ _ => simp at hi
        | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => cases hv
      | quotLift c0 =>
        have hStep : ∀ c', Step p (.fire k (.quotLift c0) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | liftQuot => exact hargs _ (by simp)
          | liftFun _ _ => exact hargs _ (by simp)
          | liftApply hq hiq hf0 =>
            have hgvq := (ihStep Step.liftQuot (hargs _ (by simp)) _ hq).1
            have hgvf := ihStep (Step.liftFun hq hiq) (hargs _ (by simp)) _ hf0
            cases hgvq with
            | con _ hfs hws =>
              have hga1 := hfs _ (List.mem_singleton.2 rfl)
              have hga2 := hws _ (List.mem_singleton.2 rfl)
              refine ⟨hgvf.1, ?_⟩
              cases hgvf.1 with
              | pap => exact ⟨.val hga1 hga2, sortMinorsIgnore_of_sortWhole hgvf.2⟩
              | _ => exact .val hga1 hga2
        refine ⟨fun v hv => ?_, hStep⟩
        rw [fire_quotLift] at hv
        cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ] at hv
          match args with
          | [α, r0, β, f0, h0, q0] =>
            obtain ⟨qv, hqv, hv⟩ := bind_ok_inv hv
            cases qv with
            | con c' l' ps fs =>
              cases fs with
              | cons a0 rest =>
                cases rest with
                | nil =>
                  simp only at hv
                  split at hv
                  · rename_i hiq
                    obtain ⟨fv, hfv, hv⟩ := bind_ok_inv hv
                    have hp := ihStep (Step.liftApply hqv hiq hfv) (hStep _ (Step.liftApply hqv hiq hfv)) v hv
                    have hwf := (ihStep (Step.liftFun hqv hiq) (hargs _ (by simp)) fv hfv).2
                    exact ⟨hp.1, hp.2 hwf⟩
                  · cases hv
                | cons _ _ => cases hv
              | nil => cases hv
            | _ => cases hv
          | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
          | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => cases hv
      | recr r0 =>
        obtain ⟨hsp, q, hag, hinst⟩ := hseen.1 r0 rfl
        have hreached : r0 ∈ ch.reached := hf.reached (r0, q) hinst
        have hres := resolve_none_of_recr hsp
        obtain ⟨htermOk, -⟩ := hinstsAll (r0, q) hinst
        have hStep : ∀ c', Step p (.fire k (.recr r0) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | recMajor _ _ => exact good_getD hargs _
          | recRule hd hk hch hrule hpeel =>
            rename_i kind j fields rule body
            have hkey : TermKey.rule r0 j ∈ p.runtimeKeys r0 := by
              simp only [Program.runtimeKeys, hres, hd, List.mem_map, List.mem_range]
              exact ⟨j, (List.getElem?_eq_some_iff.1 hrule).1, rfl⟩
            have htm : p.termOf (.rule r0 j) = some rule.rhs := by simp [Program.termOf, hd, hrule]
            have hts := (hf.wa.insts (r0, q) hinst).terms _ hkey _ htm
            have hst_rhs := htermOk _ hkey _ htm
            have hst_body := sortTermOk_peel _ _ _ [] hpeel hts hst_rhs
            have hrefs_body : RefsHandled p ch q body := fun x hx =>
              refsHandled_runtime hf hinst hkey htm x (refs_peel _ _ _ [] hpeel hts x hx)
            have hu_body : univsOk p body = true :=
              univsOk_peel _ _ _ hpeel ((hf.canon.univs r0 hreached).1 _ hkey _ htm)
            have hfields : ∀ s ∈ fields, GoodSlot p ann ch s := by
              cases kind with
              | empty => simp [P1.recChosen] at hch
              | subsingleton w srcs =>
                simp only [P1.recChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
                rw [← hch.2]
                exact good_subsingleton_fields fun s hs' => hargs s (mem_of_mem_drop' (List.mem_of_mem_take hs'))
              | ordinary =>
                simp only [P1.recChosen] at hch
                cases hfm : force p _ (args.getD _ default) with
                | ok major =>
                  rw [hfm] at hch
                  simp only at hch
                  cases hsel : p.selectRule _ _ major with
                  | none => rw [hsel] at hch; cases hch
                  | some jf =>
                    rw [hsel] at hch
                    simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                    have hgm := (ihStep (Step.recMajor hd hk) (good_getD hargs _) major hfm).1
                    rw [hch] at hsel
                    exact good_selectRule hgm hsel
                | _ => rw [hfm] at hch; cases hch
            refine ⟨q, hag, .mk fun s hs' => ?_, hrefs_body, hu_body, Or.inl hst_body⟩
            rw [List.mem_reverse, List.mem_append] at hs'
            rcases hs' with hs' | hs'
            · exact hargs s (List.mem_of_mem_take hs')
            · exact hfields s hs'
        refine ⟨fun v hv => ?_, hStep⟩
        cases k with
        | zero => simp [fire] at hv
        | succ k' =>
          cases hd : p.decl? r0 with
          | none => simp [fire, hd] at hv
          | some d =>
            cases d with
            | recr sf kk lv np nmot nmin ni ind rules ty =>
              cases hk : (p.table.recKindOf r0).map (·.atLevels ls) with
              | none => simp only [fire, hd, hk] at hv; cases hv
              | some kind =>
                obtain ⟨j, fields, rule, body, hch, hrule, hpeel, heval⟩ := fire_recr_ok hd hk hv
                have hkey : TermKey.rule r0 j ∈ p.runtimeKeys r0 := by
                  simp only [Program.runtimeKeys, hres, hd, List.mem_map, List.mem_range]
                  exact ⟨j, (List.getElem?_eq_some_iff.1 hrule).1, rfl⟩
                have htm : p.termOf (.rule r0 j) = some rule.rhs := by simp [Program.termOf, hd, hrule]
                have hts := (hf.wa.insts (r0, q) hinst).terms _ hkey _ htm
                have hst_body := sortTermOk_peel _ _ _ [] hpeel hts (htermOk _ hkey _ htm)
                have hp := ihStep (Step.recRule hd hk hch hrule hpeel)
                  (hStep _ (Step.recRule hd hk hch hrule hpeel)) v heval
                exact ⟨hp.1, hp.2 (sortWholeTerm_of_sortTermOk hst_body)⟩
            | _ => simp [fire, hd] at hv
      | cases c0 =>
        have hgoodAllFit_whole : ∀ (k' : Nat) (ss : List Slot) (mv : Value),
            (∀ s ∈ ss, GoodSlot p ann ch s) → SortWhole p ann mv →
            (∀ d, CallLt d (.fire (k' + 1) (.cases c0) ls args) → GoodCall p ann ch d →
              GoodPost p ann ch d ∧ ∀ c', Step p d c' → GoodCall p ann ch c') →
            (∀ s ∈ ss, GoodVal p ann ch mv → CallLt (.apply k' mv s) (.fire (k' + 1) (.cases c0) ls args)) →
            GoodVal p ann ch mv →
            GoodAllFit p ann ch k' mv ss := by
          intro k' ss
          induction ss with
          | nil => intro _ _ _ _ _ _; trivial
          | cons s rest ihss =>
            intro mv hss hwmv ih' _ hgmv
            have hgs : GoodSlotFits p ann ch mv s := by
              have hs0 := hss s (List.mem_cons_self ..)
              cases mv with
              | pap => exact ⟨hs0, sortMinorsIgnore_of_sortWhole hwmv⟩
              | _ => exact hs0
            refine ⟨hgs, fun v hv => ?_⟩
            have hlt_app : CallLt (.apply k' mv s) (.fire (k' + 1) (.cases c0) ls args) := by
              simp only [CallLt, Call.measure]; exact Prod.Lex.left _ _ (Nat.lt_succ_self k')
            have hpv := (ih' _ hlt_app ⟨hgmv, hgs⟩).1 v hv
            exact ihss v (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) (hpv.2 hwmv) ih'
              (fun _ _ _ => by simp only [CallLt, Call.measure]; exact Prod.Lex.left _ _ (Nat.lt_succ_self k')) hpv.1
        have hStep : ∀ c', Step p (.fire k (.cases c0) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | caseMajor _ _ _ => exact good_getD hargs _
          | caseMinor _ _ _ _ => exact good_getD hargs _
          | caseApply hres hd hk hch hfm =>
            rename_i kind j fields mv
            have hpmv := ihStep (Step.caseMinor hres hd hk hch) (good_getD hargs _) mv hfm
            have hfields : ∀ s ∈ fields, GoodSlot p ann ch s := by
              cases kind with
              | empty => simp [caseChosen] at hch
              | subsingleton w srcs =>
                simp only [caseChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
                rw [← hch.2]
                intro s hs'
                obtain ⟨src, -, rfl⟩ := List.mem_map.1 hs'
                cases src with
                | proof => exact .val (.irr ..) sortWhole_irr
                | index i => exact good_getD_irr hargs _
              | ordinary =>
                simp only [caseChosen] at hch
                cases hfmaj : force p _ (args.getD _ default) with
                | ok major =>
                  rw [hfmaj] at hch
                  simp only at hch
                  cases hsel : p.selectRule _ _ major with
                  | none => rw [hsel] at hch; cases hch
                  | some jf =>
                    rw [hsel] at hch
                    simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                    have hgmaj := (ihStep (Step.caseMajor hres hd hk) (good_getD hargs _) major hfmaj).1
                    rw [hch] at hsel
                    exact good_selectRule hgmaj hsel
                | _ => rw [hfmaj] at hch; cases hch
            exact ⟨hpmv.1, hgoodAllFit_whole _ _ _ hfields hpmv.2 ih
              (fun _ _ _ => by simp only [CallLt, Call.measure]; exact Prod.Lex.left _ _ (Nat.lt_succ_self _)) hpmv.1⟩
        refine ⟨fun v hv => ?_, hStep⟩
        cases k with
        | zero => simp [fire] at hv
        | succ k' =>
          cases hres : p.table.resolveOf c0 with
          | none => rw [fire] at hv; simp [hres] at hv
          | some e =>
            cases e with
            | case r0 =>
              obtain ⟨sf, kk, lv, np, nmot, nmin, ni, ind, rules, ty, kind, hd, hk⟩ :=
                fire_cases_decl hres hv
              obtain ⟨j, fields, mv, hch, hfm, happ⟩ := fire_cases_ok hres hd hk hv
              have hpmv := ihStep (Step.caseMinor hres hd hk hch) (good_getD hargs _) mv hfm
              have hp := ihStep (Step.caseApply hres hd hk hch hfm)
                (hStep _ (Step.caseApply hres hd hk hch hfm)) v happ
              exact ⟨hp.1, hp.2 hpmv.2⟩
            | _ => rw [fire] at hv; simp [hres] at hv
      | prim op =>
        have hStep : ∀ c', Step p (.fire k (.prim op) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep; cases hstep; exact hargs
        refine ⟨fun v hv => ?_, hStep⟩
        rw [fire_prim] at hv
        obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
        unfold primValue at hv
        cases hlit : litArgs vs with
        | none => rw [hlit] at hv; cases hv
        | some ns =>
          rw [hlit] at hv; dsimp only at hv
          cases hop : op.evalLits ns with
          | none => rw [hop] at hv; cases hv
          | some res =>
            rw [hop] at hv
            cases res with
            | nat n => dsimp only at hv; cases hv; exact ⟨.lit n, sortWhole_lit⟩
            | bool b =>
              dsimp only at hv
              obtain ⟨c0, rfl⟩ := boolValue_ok hv
              exact ⟨.con ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩ (fun _ hm => by cases hm) (fun _ hm => by cases hm), sortWhole_con⟩
      | word w op =>
        obtain ⟨c0, hc0, thm, hres⟩ := hseen.2 w op rfl
        have hStep : ∀ c', Step p (.fire k (.word w op) ls args) c' → GoodCall p ann ch c' := by
          intro c' hstep; cases hstep; exact hargs
        refine ⟨fun v hv => ?_, hStep⟩
        rw [fire_word] at hv
        obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
        obtain ⟨r0, hr0⟩ := wordValue_ok hv
        cases r0 with
        | word w' n =>
          simp only [Program.wordResult] at hr0
          cases hm : p.mkWord? w' n with
          | none => rw [hm] at hr0; cases hr0
          | some t =>
            rw [hm] at hr0
            simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hr0
            subst hr0
            exact good_mkWord hf hc0 hres hm
        | nat n => simp only [Program.wordResult, Sem.Result.ok.injEq] at hr0; subst hr0; exact ⟨.lit n, sortWhole_lit⟩
        | dec b => simp [Program.wordResult] at hr0
    | force k s =>
      cases hgood with
      | val hgv hw =>
        refine ⟨fun v hv => ?_, fun _ hstep => by cases hstep⟩
        rw [force_val] at hv; cases hv; exact ⟨hgv, hw⟩
      | name q hag hrefs hu hok henv =>
        rename_i t ρ ls
        have hStep : ∀ c', Step p (.force k (.name t ρ ls)) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | forceName => exact ⟨q, hag, henv, hrefs, hu, Or.inl hok⟩
        refine ⟨fun v hv => ?_, hStep⟩
        rw [force_name] at hv
        cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ] at hv
          have hp := ihStep Step.forceName (hStep _ Step.forceName) v hv
          exact ⟨hp.1, hp.2 (sortWholeTerm_of_sortTermOk hok)⟩
    | forceAll k ss =>
      cases ss with
      | nil =>
        refine ⟨fun vs hvs => ?_, fun _ hstep => by cases hstep⟩
        rw [forceAll_nil] at hvs; cases hvs; intro _ hm; cases hm
      | cons s rest =>
        have hStep : ∀ c', Step p (.forceAll k (s :: rest)) c' → GoodCall p ann ch c' := by
          intro c' hstep
          cases hstep with
          | allForce => exact hgood s (List.mem_cons_self ..)
          | allForceRest _ => exact fun s' hs' => hgood s' (List.mem_cons_of_mem _ hs')
        refine ⟨fun vs hvs => ?_, hStep⟩
        rw [forceAll_cons] at hvs
        obtain ⟨v0, hv0, hvs⟩ := bind_ok_inv hvs
        obtain ⟨vs0, hvs0, hvs⟩ := bind_ok_inv hvs
        cases hvs
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ihStep Step.allForce (hStep _ Step.allForce) v hv0
        · exact ihStep (Step.allForceRest hv0) (hStep _ (Step.allForceRest hv0)) vs0 hvs0 v hv

private theorem good_reach {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hsc : SortClosed p ann ch = true) {top : Call}
    (htop : GoodCall p ann ch top) :
    ∀ c, Reach p top c → GoodCall p ann ch c ∧ GoodPost p ann ch c := by
  intro c hr
  induction hr with
  | refl => exact ⟨htop, (good_core hf hsc top htop).1⟩
  | step _ hst ih =>
    have hg' := (good_core hf hsc _ ih.1).2 _ hst
    exact ⟨hg', (good_core hf hsc _ hg').1⟩

private theorem markersIgnored_of_ignoresAt {p : Program} {ann : Relevance.Ann}
    {k : Nat} {exempt : Nat → Prop} :
    ∀ (fields : List Slot) (i : Nat) (mv : Value),
      (∀ m s, fields[m]? = some s → MarkerSlot s → ¬ exempt (i + m) → IgnoresAt p ann k mv m) →
      MarkersIgnored p ann k exempt i mv fields
  | [], _, _, _ => trivial
  | s :: ss, i, mv, h => by
    refine ⟨fun hms hne => h 0 s rfl hms (by simpa using hne), fun v hv => ?_⟩
    refine markersIgnored_of_ignoresAt ss (i + 1) v fun m s' hs' hms' hne' => ?_
    have h1 := h (m + 1) s' (by simpa using hs') hms' (by
      have : i + (m + 1) = i + 1 + m := by omega
      rwa [this])
    exact h1 s v hv

private theorem recKind_atLevels_eq_atProfile {ls : Levels} {q : Profile} (hag : Agree ls q)
    (rk : RecKind) : rk.atLevels ls = rk.atProfile q := by
  cases rk with
  | ordinary => rfl
  | empty => rfl
  | subsingleton w srcs =>
    simp only [RecKind.atLevels, RecKind.atProfile, hag.holds]

/-- Every call with `GoodCall`, `Pre`, and child `Post`s satisfies `SortCoherent` under `SortClosed`. -/
private theorem localSortCoherent_of_good {p : Program} {ann : Relevance.Ann} {ch : Relevance.Checked}
    (hf : Facts p ann ch) (hs : ShapeOk p) (hsc : SortClosed p ann ch = true) {top : Call}
    (htop : GoodCall p ann ch top) :
    LocalSortCoherent p ann ch top := by
  have hgoodAll := good_reach hf hsc htop
  have hquotOk : sortQuotOk p ann ch = true := by
    unfold SortClosed at hsc; simp only [Bool.and_eq_true] at hsc; exact hsc.1.1
  have hrecRulesAll : ∀ inst ∈ ch.instances,
      ∀ sf kk lv np nmot nmin ni ind rules ty,
        specialHead? p inst.1 = some (.recr inst.1) →
        p.decl? inst.1 = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        sortRecRuleOk p ann inst.1 inst.2 np nmot nmin ni rules = true := by
    unfold SortClosed at hsc; simp only [Bool.and_eq_true, List.all_eq_true] at hsc
    intro inst hin sf kk lv np nmot nmin ni ind rules ty hsp hd
    have hi := hsc.2 inst hin
    have hrec := hi.1.2
    rw [hsp, hd] at hrec; exact hrec
  have hcaseRulesAll : ∀ inst ∈ ch.instances,
      ∀ r sf kk lv np nmot nmin ni ind rules ty,
        p.table.resolveOf inst.1 = some (.case r) →
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        nmin ≤ rules.length := by
    unfold SortClosed at hsc; simp only [Bool.and_eq_true, List.all_eq_true] at hsc
    intro inst hin r sf kk lv np nmot nmin ni ind rules ty hres hd
    have hi := hsc.2 inst hin
    have hc := hi.2
    rw [hres] at hc; dsimp only at hc; rw [hd] at hc; exact of_decide_eq_true hc
  intro c hrc hpre hpost
  have hgc := (hgoodAll c hrc).1
  cases c with
  | eval k ls ρ t =>
    cases t with
    | app f a m r =>
      -- Clause (a)
      intro hirr _ fv hfv
      obtain ⟨q, hag, -, -, hu, -, happ, -, -⟩ := goodFrame_app_parts hgc
      have hrq : r.irrP q = true := by rw [hag.irr]; exact hirr
      have huf : univsOk p f = true := by simp only [univsOk, Bool.and_eq_true] at hu; exact hu.1
      exact eval_sort_prefix hag huf (happ hrq) hfv
    | proj s i e =>
      -- Clause (f)
      intro cv lsv ps fs v he hfs hvi
      obtain ⟨q, -, -, -, -, hok⟩ :=
        goodFrame_nonAppConst hgc (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
      simp only [sortTermOk, Bool.and_eq_true] at hok
      have hprojOk : sortProjOk p ann ch i = true := hok.1
      have hpe : Pre p ann ch (.eval k ls ρ e) := by
        obtain ⟨q', bs', hag', ⟨hlen, hlive⟩, hrefs', hu', hc'⟩ := hpre
        have hte : TermC p ann q' bs' e := by
          rcases hc' with ht | ⟨_, -, hsp, -⟩ | ⟨_, _, heq, -⟩
          · cases ht with | proj _ h2 => exact h2
          · cases hsp with | head _ _ ht => cases ht with | proj _ h2 => exact h2
          · cases heq
        refine ⟨q', bs', hag', .mk hlen (fun x sl r' hx hr' hirr hm _ =>
          hlive x sl r' hx hr' hirr hm ?_), hrefs', hu', Or.inl hte⟩
        rintro ⟨_, _, _, hh, -⟩; cases hh
      have hlv := (hpost _ Step.proj hpe _ he).1
      have hgv := ((hgoodAll _ (.step hrc Step.proj)).2 _ he).1
      cases hlv with
      | con hread _ _ =>
        cases hgv with
        | con hcmwf _ _ =>
          have hrf : ReadsField p ann ch cv lsv i = false := by
            cases hr : ReadsField p ann ch cv lsv i
            · rfl
            · have hlv' := hread i v hfs (Or.inl hr)
              rw [live_not_irr hlv'] at hvi; cases hvi
          unfold sortProjOk at hprojOk
          simp only [Bool.and_eq_true] at hprojOk
          cases hd : p.decl? cv with
          | some d =>
            cases d with
            | quot qk lv ty =>
              cases qk with
              | ctor =>
                have hiq : p.isQuotCtor cv = true := by simp [Program.isQuotCtor, hd]
                obtain ⟨rfl, hreach⟩ := hcmwf.2 i v hfs hvi hiq
                simp only [ReadsField, hd, Bool.not_eq_false'] at hrf
                cases hcr : ann.constRel? cv with
                | none => simp [hcr] at hrf
                | some cr =>
                  rw [hcr] at hrf
                  cases hrp : cr.params[2]? with
                  | none => simp [hrp] at hrf
                  | some rp =>
                    simp only [Option.bind_some, hrp, Option.map_some, Option.getD_some] at hrf
                    have hq := hprojOk.2
                    simp only [beq_self_eq_true, ↓reduceIte, List.all_eq_true] at hq
                    have hq' := hq cv hreach
                    simp only [hd, hcr, hrp, Bool.not_eq_true'] at hq'
                    rw [propWhenCanHold_of_holds hrf] at hq'; cases hq'
              | _ =>
                simp only [ReadsField, hd, Checked.keeps, Checked.keepsP] at hrf
                cases hkr : ch.ctorRel? cv with
                | none => simp [hkr] at hrf
                | some kr =>
                  rw [ch_ctorRel hf] at hkr
                  obtain ⟨sf, lv', ind, cidx, np, nf, ty', hdc, -⟩ := hf.canon.ctors cv kr hkr
                  rw [hd] at hdc; cases hdc
            | ctor sf lv ind cidx np nf ty =>
              simp only [ReadsField, hd, Checked.keeps, Checked.keepsP] at hrf
              cases hkr : ch.ctorRel? cv with
              | none => simp [hkr] at hrf
              | some kr =>
                have hkrAnn : ann.ctorRel? cv = some kr := by rwa [← ch_ctorRel hf]
                obtain ⟨sf', lv', ind', cidx', np', nf', ty', hdc', hlen, -⟩ := hf.canon.ctors cv kr hkrAnn
                rw [hd] at hdc'; cases hdc'
                have hilt : i < nf := hcmwf.1 i v hfs hvi sf lv ind cidx np nf ty hd
                have hget : kr.fields[i]? = some (kr.fields[i]'(by omega)) :=
                  List.getElem?_eq_getElem (by omega)
                simp only [hkr, hget, Bool.not_eq_false'] at hrf
                have hcan : propWhenCanHold (kr.fields[i]'(by omega)).dropWhen = true :=
                  propWhenCanHold_of_holdsP hrf
                have hmap := natMapAll_get? ch.ctors 0 1 cv hprojOk.1 hkr
                simp only [Nat.zero_add, Nat.one_mul, hget, hcan, ↓reduceIte] at hmap
                exact hmap
            | _ =>
              simp only [ReadsField, hd, Checked.keeps, Checked.keepsP] at hrf
              cases hkr : ch.ctorRel? cv with
              | none => simp [hkr] at hrf
              | some kr =>
                rw [ch_ctorRel hf] at hkr
                obtain ⟨sf, lv', ind, cidx, np, nf, ty', hdc, -⟩ := hf.canon.ctors cv kr hkr
                rw [hd] at hdc; cases hdc
          | none =>
            simp only [ReadsField, hd, Checked.keeps, Checked.keepsP] at hrf
            cases hkr : ch.ctorRel? cv with
            | none => simp [hkr] at hrf
            | some kr =>
              rw [ch_ctorRel hf] at hkr
              obtain ⟨sf, lv', ind, cidx, np, nf, ty', hdc, -⟩ := hf.canon.ctors cv kr hkr
              rw [hd] at hdc; cases hdc
    | _ => trivial
  | fire k h ls args =>
    cases k with
    | zero => trivial
    | succ k' =>
      cases h with
      | recr r =>
        -- Clause (d)
        intro sf kk lv np nmot nmin ni ind rules ty kind j fields rule hd hk hch hrule
        dsimp only
        intro n s hget hms hnotRSE
        have hfire : FireOk p ann ch (.recr r) ls args := hpre
        obtain ⟨hsp, q, hag, hinst⟩ := hfire.inst.1 r rfl
        have hrrOk := hrecRulesAll (r, q) hinst sf kk lv np nmot nmin ni ind rules ty hsp hd
        unfold sortRecRuleOk at hrrOk
        have hjlt : j < rules.length := (List.getElem?_eq_some_iff.1 hrule).1
        have hpair : (rule, j) ∈ rules.zipIdx := by
          rw [List.mem_iff_getElem?]
          refine ⟨j, ?_⟩
          simp [List.getElem?_zipIdx, hrule]
        have hrj := List.all_eq_true.1 hrrOk (rule, j) hpair
        simp only [Bool.and_eq_true] at hrj
        have harity : args.length = np + nmot + nmin + ni + 1 := by
          rw [hfire.arity]; exact headArity_recr hd
        have hpre_len : (args.take (np + nmot + nmin)).length = np + nmot + nmin := by
          simp only [List.length_take]; omega
        by_cases hn : n < np + nmot + nmin
        · -- Pre slot: must be `HeadIgnores` from `FireOk.live`
          have hsa : args[n]? = some s := by
            rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hn] at hget
            exact hget
          have hig : HeadIgnores ann (.recr r) ls n := by
            apply Classical.byContradiction
            intro hno
            have hls := hfire.live n s hsa (fun hh => hno hh.1)
            obtain ⟨t0, ρ0, ls0, rfl⟩ := hms
            cases hls with
            | val hlv _ => exact absurd (live_not_irr hlv) (by simp [Value.isIrr])
          obtain ⟨c', cr, rp, hc', hcr, hrp, hirrAt⟩ := hig
          simp only [headConst?, Option.some.injEq] at hc'; subst hc'
          have hpreOk := List.all_eq_true.1 hrj.1 n (List.mem_range.2 hn)
          have hirrP : rp.irrP q = true := by rw [hag.irr]; exact hirrAt
          simp only [hcr, hrp, hirrP, ↓reduceIte] at hpreOk
          cases hb : (lamRels rule.rhs)[n]? with
          | none => simp [hb] at hpreOk
          | some b =>
            simp only [hb] at hpreOk
            exact ⟨b, rfl, by rw [← hag.irr]; exact hpreOk⟩
        · -- Field slot `fi = n - (np + nmot + nmin)`
          have hfi : fields[n - (np + nmot + nmin)]? = some s := by
            rw [List.getElem?_append_right (by omega), hpre_len] at hget
            exact hget
          have hkrk : (p.table.recKindOf r).map (·.atProfile q) = some kind := by
            rw [← hk]
            cases hrk : p.table.recKindOf r with
            | none => rfl
            | some rk => simp [recKind_atLevels_eq_atProfile hag rk]
          have hfieldsOk := hrj.2
          rw [hkrk] at hfieldsOk
          cases kind with
          | empty => simp [P1.recChosen] at hch
          | ordinary =>
            simp only [P1.recChosen] at hch
            cases hfm : force p k' (args.getD (np + nmot + nmin + ni) default) with
            | ok major =>
              rw [hfm] at hch
              simp only at hch
              cases hsel : p.selectRule ind np major with
              | none => rw [hsel] at hch; cases hch
              | some jf =>
                rw [hsel] at hch
                simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                rw [hch] at hsel
                have hpm := hpost _ (Step.recMajor hd hk) (pre_force_getD hfire k' _) major hfm
                have hgm := ((hgoodAll _ (.step hrc (Step.recMajor hd hk))).2 major hfm).1
                cases major with
                | lit m =>
                  simp only [Program.selectRule] at hsel
                  split at hsel
                  · split at hsel
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                      rw [← hsel.2] at hfi; simp at hfi
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                      rw [← hsel.2] at hfi
                      have hmem := List.mem_iff_getElem?.2 ⟨_, hfi⟩
                      simp only [List.mem_singleton] at hmem; subst hmem
                      obtain ⟨_, _, _, hbot⟩ := hms; cases hbot
                  · cases hsel
                | con cv lsv ps fs =>
                  have hlv : Live p ann ch (.con cv lsv ps fs) := hpm.1 rfl
                  obtain ⟨sf', lv', np', nf', ty', hdc, rfl⟩ : ∃ sf' lv' np' nf' ty',
                      p.decl? cv = some (.ctor sf' lv' ind j np' nf' ty') ∧ fields = fs.map .val := by
                    simp only [Program.selectRule] at hsel
                    cases hdc : p.decl? cv with
                    | none => rw [hdc] at hsel; cases hsel
                    | some d =>
                      rw [hdc] at hsel
                      cases d with
                      | ctor sf' lv' ind' cidx np' nf' ty' =>
                        simp only at hsel
                        split at hsel
                        · rename_i hcond
                          simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                          obtain ⟨rfl, rfl⟩ := hsel; obtain ⟨rfl, -⟩ := hcond
                          exact ⟨sf', lv', np', nf', ty', rfl, rfl⟩
                        · cases hsel
                      | _ => simp at hsel
                  have hrc_eq : cv = rule.ctor := by
                    cases hshape : elimShape? p r with
                    | none => simp [elimShape?, resolve_none_of_recr hsp, hd] at hshape
                    | some shape =>
                      have hrecr : shape.recr = r := by
                        simp only [elimShape?, resolve_none_of_recr hsp, hd, Option.some.injEq] at hshape
                        rw [← hshape]
                      obtain ⟨sf0, lv0, np0, ty0, hd0⟩ :=
                        hf.canon.rules r (hf.reached (r, q) hinst) shape hshape
                          sf kk lv np nmot nmin ni ind rules ty (by rw [hrecr]; exact hd) j rule hrule
                      exact hs.ctorUnique cv rule.ctor sf' sf0 lv' lv0 ind j np' np0 nf' rule.fields ty' ty0 hdc hd0
                  subst hrc_eq
                  rw [List.getElem?_map] at hfi
                  cases hfs : fs[n - (np + nmot + nmin)]? with
                  | none => simp [hfs] at hfi
                  | some v =>
                    simp only [hfs, Option.map_some, Option.some.injEq] at hfi
                    subst hfi
                    obtain ⟨t0, ρ0, ls0, hv_eq⟩ := hms
                    cases hv_eq
                    cases hlv with
                    | con hread _ _ =>
                      cases hgm with
                      | con hcmwf _ _ =>
                        have hrf : ReadsField p ann ch rule.ctor lsv (n - (np + nmot + nmin)) = false := by
                          cases hr : ReadsField p ann ch rule.ctor lsv (n - (np + nmot + nmin))
                          · rfl
                          · exact absurd (live_not_irr (hread _ _ hfs (Or.inl hr))) (by simp [Value.isIrr])
                        simp only [ReadsField, hdc, Checked.keeps, Checked.keepsP] at hrf
                        cases hkr : ch.ctorRel? rule.ctor with
                        | none => simp [hkr] at hrf
                        | some kr =>
                          have hkrAnn : ann.ctorRel? rule.ctor = some kr := by rwa [← ch_ctorRel hf]
                          obtain ⟨sf0, lv0, ind0, cidx0, np0, nf0, ty0, hdc0, hlen, -⟩ :=
                            hf.canon.ctors rule.ctor kr hkrAnn
                          rw [hdc] at hdc0; cases hdc0
                          have hilt : n - (np + nmot + nmin) < nf' :=
                            hcmwf.1 _ _ hfs rfl sf' lv' ind j np' nf' ty' hdc
                          have hcls_get : kr.fields[n - (np + nmot + nmin)]? =
                              some (kr.fields[n - (np + nmot + nmin)]'(by omega)) :=
                            List.getElem?_eq_getElem (by omega)
                          simp only [hkr, hcls_get, Bool.not_eq_false'] at hrf
                          have hcan := propWhenCanHold_of_holdsP hrf
                          have hnwe : fieldWrittenErased p rule.ctor (n - (np + nmot + nmin)) = false := by
                            cases hwe : fieldWrittenErased p rule.ctor (n - (np + nmot + nmin))
                            · rfl
                            · exfalso; apply hnotRSE
                              exact Or.inr (Or.inl ⟨by omega, by simpa [hpre_len] using hwe⟩)
                          rw [hkrAnn] at hfieldsOk
                          have hpairF : (kr.fields[n - (np + nmot + nmin)]'(by omega), n - (np + nmot + nmin)) ∈
                              kr.fields.zipIdx := by
                            rw [List.mem_iff_getElem?]
                            refine ⟨n - (np + nmot + nmin), ?_⟩
                            simp [List.getElem?_zipIdx, hcls_get]
                          have hfok := List.all_eq_true.1 hfieldsOk _ hpairF
                          rw [hcan, hnwe] at hfok
                          simp only [Bool.not_false, and_self, ↓reduceIte] at hfok
                          have hne : np + nmot + nmin + (n - (np + nmot + nmin)) = n := by omega
                          rw [hne] at hfok
                          cases hb : (lamRels rule.rhs)[n]? with
                          | none => simp [hb] at hfok
                          | some b =>
                            simp only [hb] at hfok
                            exact ⟨b, rfl, by rw [← hag.irr]; exact hfok⟩
                | _ => simp [Program.selectRule] at hsel
            | _ => rw [hfm] at hch; cases hch
          | subsingleton w srcs =>
            simp only [P1.recChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
            obtain ⟨rfl, rfl⟩ := hch
            simp only [beq_self_eq_true, ↓reduceIte] at hfieldsOk
            rw [List.getElem?_map] at hfi
            cases hsrc : srcs[n - (np + nmot + nmin)]? with
            | none => simp [hsrc] at hfi
            | some src =>
              simp only [hsrc, Option.map_some, Option.some.injEq] at hfi
              have hpairS : (src, n - (np + nmot + nmin)) ∈ srcs.zipIdx := by
                rw [List.mem_iff_getElem?]
                exact ⟨n - (np + nmot + nmin), by simp [List.getElem?_zipIdx, hsrc]⟩
              have hsok := List.all_eq_true.1 hfieldsOk _ hpairS
              have hne : np + nmot + nmin + (n - (np + nmot + nmin)) = n := by omega
              cases src with
              | proof =>
                simp only [hne] at hsok
                cases hb : (lamRels rule.rhs)[n]? with
                | none => simp [hb] at hsok
                | some b =>
                  simp only [hb] at hsok
                  exact ⟨b, rfl, by rw [← hag.irr]; exact hsok⟩
              | index i =>
                by_cases hge : i ≥ ni
                · simp only [hge, ↓reduceIte, hne] at hsok
                  cases hb : (lamRels rule.rhs)[n]? with
                  | none => simp [hb] at hsok
                  | some b =>
                    simp only [hb] at hsok
                    exact ⟨b, rfl, by rw [← hag.irr]; exact hsok⟩
                · have hilt : i < ni := Nat.lt_of_not_le hge
                  have hgetArg : args[np + nmot + nmin + i]? = some s := by
                    dsimp only at hfi
                    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hilt, List.getElem?_drop] at hfi
                    have hlt2 : np + nmot + nmin + i < args.length := by omega
                    rw [List.getElem?_eq_getElem hlt2] at hfi ⊢
                    simpa using hfi
                  have hig : HeadIgnores ann (.recr r) ls (np + nmot + nmin + i) := by
                    apply Classical.byContradiction
                    intro hno
                    have hls := hfire.live _ s hgetArg (fun hh => hno hh.1)
                    obtain ⟨_, _, _, rfl⟩ := hms
                    cases hls with
                    | val hlv _ => exact absurd (live_not_irr hlv) (by simp [Value.isIrr])
                  obtain ⟨c', cr, rp, hc', hcr, hrp, hirrAt⟩ := hig
                  simp only [headConst?, Option.some.injEq] at hc'; subst hc'
                  have hirrP : rp.irrP q = true := by rw [hag.irr]; exact hirrAt
                  simp only [hge, ↓reduceIte, hcr, hrp, hirrP, hne] at hsok
                  cases hb : (lamRels rule.rhs)[n]? with
                  | none => simp [hb] at hsok
                  | some b =>
                    simp only [hb] at hsok
                    exact ⟨b, rfl, by rw [← hag.irr]; exact hsok⟩
      | cases c0 =>
        -- Clause (c)
        intro r sf kk lv np nmot nmin ni ind rules ty kind j fields mv hres hd hk hch hfm
        have hfire : FireOk p ann ch (.cases c0) ls args := hpre
        have hmin := hgc.2.2.2
        have harity : args.length = np + 1 + ni + 1 + nmin := by
          rw [hfire.arity]; exact headArity_cases hres hd
        by_cases hj : j < nmin
        · have hgetMin : args[np + 1 + ni + 1 + j]? = some (args.getD (np + 1 + ni + 1 + j) default) := by
            rw [List.getD_eq_getElem?_getD]
            have hlt : np + 1 + ni + 1 + j < args.length := by omega
            rw [List.getElem?_eq_getElem hlt]; rfl
          refine markersIgnored_of_ignoresAt fields 0 mv fun m s hs_m hms hnotEx => ?_
          simp only [Nat.zero_add] at hnotEx
          -- Show `caseRuleSortDrop p ann c0 j m = true`
          have hdrop : caseRuleSortDrop p ann c0 j m = true := by
            unfold caseRuleSortDrop
            rw [hres]; dsimp only; rw [hd]; dsimp only
            simp only [Bool.or_eq_true]
            cases kind with
            | empty => simp [caseChosen] at hch
            | ordinary =>
              left
              simp only [caseChosen] at hch
              cases hfmaj : force p k' (args.getD (np + 1 + ni) default) with
              | ok major =>
                rw [hfmaj] at hch
                simp only at hch
                cases hsel : p.selectRule ind np major with
                | none => rw [hsel] at hch; cases hch
                | some jf =>
                  rw [hsel] at hch
                  simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hch
                  rw [hch] at hsel
                  have hpmaj := hpost _ (Step.caseMajor hres hd hk) (pre_force_getD hfire k' _) major hfmaj
                  have hgmaj := ((hgoodAll _ (.step hrc (Step.caseMajor hres hd hk))).2 major hfmaj).1
                  cases major with
                  | lit mm =>
                    simp only [Program.selectRule] at hsel
                    split at hsel
                    · split at hsel
                      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                        rw [← hsel.2] at hs_m; simp at hs_m
                      · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                        rw [← hsel.2] at hs_m
                        have hmem := List.mem_iff_getElem?.2 ⟨_, hs_m⟩
                        simp only [List.mem_singleton] at hmem; subst hmem
                        obtain ⟨_, _, _, hbot⟩ := hms; cases hbot
                    · cases hsel
                  | con cv lsv ps fs =>
                    have hlv : Live p ann ch (.con cv lsv ps fs) := hpmaj.1 rfl
                    obtain ⟨sf', lv', np', nf', ty', hdc, rfl⟩ : ∃ sf' lv' np' nf' ty',
                        p.decl? cv = some (.ctor sf' lv' ind j np' nf' ty') ∧ fields = fs.map .val := by
                      simp only [Program.selectRule] at hsel
                      cases hdc : p.decl? cv with
                      | none => rw [hdc] at hsel; cases hsel
                      | some d =>
                        rw [hdc] at hsel
                        cases d with
                        | ctor sf' lv' ind' cidx np' nf' ty' =>
                          simp only at hsel
                          split at hsel
                          · rename_i hcond
                            simp only [Option.some.injEq, Prod.mk.injEq] at hsel
                            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                            obtain ⟨rfl, rfl⟩ := hsel; obtain ⟨rfl, -⟩ := hcond
                            exact ⟨sf', lv', np', nf', ty', rfl, rfl⟩
                          · cases hsel
                        | _ => simp at hsel
                    obtain ⟨hsp, q, -, hinst⟩ := hfire.inst.1 c0 rfl
                    -- `rules[j]?` exists and has `rule.ctor = cv`
                    cases hrule : rules[j]? with
                    | none =>
                      exfalso
                      have hle := hcaseRulesAll (c0, q) hinst r sf kk lv np nmot nmin ni ind rules ty hres hd
                      have hge := List.getElem?_eq_none_iff.1 hrule
                      omega
                    | some rule =>
                      have hrc_eq : cv = rule.ctor := by
                        obtain ⟨sf0, lv0, np0, ty0, hd0⟩ :=
                          hf.canon.rules c0 (hf.reached (c0, q) hinst) _ (elimShape_cases hres hd)
                            sf kk lv np nmot nmin ni ind rules ty hd j rule hrule
                        exact hs.ctorUnique cv rule.ctor sf' sf0 lv' lv0 ind j np' np0 nf' rule.fields ty' ty0 hdc hd0
                      subst hrc_eq
                      rw [List.getElem?_map] at hs_m
                      cases hfs : fs[m]? with
                      | none => simp [hfs] at hs_m
                      | some v =>
                        simp only [hfs, Option.map_some, Option.some.injEq] at hs_m
                        subst hs_m
                        obtain ⟨_, _, _, hv_eq⟩ := hms; cases hv_eq
                        cases hlv with
                        | con hread _ _ =>
                          cases hgmaj with
                          | con hcmwf _ _ =>
                            have hrf : ReadsField p ann ch rule.ctor lsv m = false := by
                              cases hr : ReadsField p ann ch rule.ctor lsv m
                              · rfl
                              · exact absurd (live_not_irr (hread _ _ hfs (Or.inl hr))) (by simp [Value.isIrr])
                            simp only [ReadsField, hdc, Checked.keeps, Checked.keepsP] at hrf
                            cases hkr : ch.ctorRel? rule.ctor with
                            | none => simp [hkr] at hrf
                            | some kr =>
                              have hkrAnn : ann.ctorRel? rule.ctor = some kr := by rwa [← ch_ctorRel hf]
                              obtain ⟨sf0, lv0, ind0, cidx0, np0, nf0, ty0, hdc0, hlen, -⟩ :=
                                hf.canon.ctors rule.ctor kr hkrAnn
                              rw [hdc] at hdc0; cases hdc0
                              have hmlt : m < nf' := hcmwf.1 _ _ hfs rfl sf' lv' ind j np' nf' ty' hdc
                              have hcls_get : kr.fields[m]? = some (kr.fields[m]'(by omega)) :=
                                List.getElem?_eq_getElem (by omega)
                              simp only [hkr, hcls_get, Bool.not_eq_false'] at hrf
                              have hcan := propWhenCanHold_of_holdsP hrf
                              have hnwe : fieldWrittenErased p rule.ctor m = false := by
                                cases hwe : fieldWrittenErased p rule.ctor m
                                · rfl
                                · exfalso; apply hnotEx; left; simp [hrule, hwe]
                              simp [hkrAnn, hcls_get, hcan, hnwe]
                  | _ => simp [Program.selectRule] at hsel
              | _ => rw [hfmaj] at hch; cases hch
            | subsingleton w srcs =>
              right
              simp only [caseChosen, Sem.Result.ok.injEq, Prod.mk.injEq] at hch
              obtain ⟨rfl, rfl⟩ := hch
              have hrk : p.table.recKindOf r = some (.subsingleton w srcs) := by
                cases h0 : p.table.recKindOf r with
                | none => simp [h0] at hk
                | some rk0 =>
                  rw [h0] at hk
                  cases rk0 with
                  | subsingleton w0 srcs0 =>
                    simp only [Option.map_some, RecKind.atLevels, Option.some.injEq] at hk
                    split at hk
                    · cases hk; rfl
                    · cases hk
                  | _ => simp [RecKind.atLevels] at hk
              rw [List.getElem?_map] at hs_m
              cases hsrc : srcs[m]? with
              | none => simp [hsrc] at hs_m
              | some src =>
                simp only [hsrc, Option.map_some, Option.some.injEq] at hs_m
                simp only [beq_self_eq_true, hrk, hsrc, Bool.true_and]
                cases src with
                | proof => rfl
                | index i' =>
                  by_cases hge : ni ≤ i'
                  · simp [hge]
                  · have hilt : i' < ni := Nat.lt_of_not_le hge
                    have hgetArg : args[np + 1 + i']? = some s := by
                      dsimp only at hs_m
                      rw [List.getD_eq_getElem?_getD] at hs_m
                      have hlt2 : np + 1 + i' < args.length := by omega
                      rw [List.getElem?_eq_getElem hlt2] at hs_m ⊢
                      simpa using hs_m
                    have hig : HeadIgnores ann (.cases c0) ls (np + 1 + i') := by
                      apply Classical.byContradiction
                      intro hno
                      have hls := hfire.live _ s hgetArg (fun hh => hno hh.1)
                      obtain ⟨_, _, _, rfl⟩ := hms
                      cases hls with
                      | val hlv _ => exact absurd (live_not_irr hlv) (by simp [Value.isIrr])
                    obtain ⟨c', cr, rp, hc', hcr, hrp, hirrAt⟩ := hig
                    simp only [headConst?, Option.some.injEq] at hc'; subst hc'
                    simp [hge, hcr, hrp, propWhenCanHold_of_holds hirrAt]
          have higSlot := hmin c0 r sf kk lv np nmot nmin ni ind rules ty rfl hres hd j _ hj hgetMin m hdrop
          exact ignoresAt_of_slot higSlot hfm
        · -- `nmin ≤ j`: minor slot is `default = .val (.lit 0)`, which is stuck on `apply`
          have hdef : args.getD (np + 1 + ni + 1 + j) default = .val (.lit 0) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          rw [hdef, force_val, Sem.Result.ok.injEq] at hfm
          subst hfm
          exact markersIgnored_of_ignoresAt fields 0 (.lit 0) fun m _ _ _ _ =>
            ignoresAt_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) m
      | quotLift c0 =>
        -- Clause (e)
        rcases args with _ | ⟨α, _ | ⟨r0, _ | ⟨β, _ | ⟨f0, _ | ⟨h0, _ | ⟨q0, _ | _⟩⟩⟩⟩⟩⟩ <;> try trivial
        intro c' l' ps a0 fv hfq hiq _ hairr hner
        have hfire : FireOk p ann ch (.quotLift c0) ls [α, r0, β, f0, h0, q0] := hpre
        obtain ⟨hsp0, q, -, hinst0⟩ := hfire.inst.1 c0 rfl
        have hreach0 : c0 ∈ ch.reached := hf.reached (c0, q) hinst0
        have hhasLift : (ch.reached.any fun c =>
            match specialHead? p c with | some (.quotLift _) => true | _ => false) = true := by
          rw [List.any_eq_true]
          exact ⟨c0, hreach0, by simp [hsp0]⟩
        unfold sortQuotOk at hquotOk
        simp only [hhasLift, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at hquotOk
        have hpreQ : Pre p ann ch (.force k' q0) := by
          have := pre_force_getD hfire k' 5; simpa using this
        have hlvq := (hpost _ Step.liftQuot hpreQ _ hfq).1 rfl
        have hgvq := ((hgoodAll _ (.step hrc Step.liftQuot)).2 _ hfq).1
        cases hlvq with
        | con hread _ _ =>
          cases hgvq with
          | con hcmwf _ _ =>
            obtain ⟨-, hreach'⟩ := hcmwf.2 0 a0 rfl hairr hiq
            obtain ⟨lv', ty', hdq⟩ := decl_of_isQuotCtor hiq
            have hrf : ReadsField p ann ch c' l' 0 = false := by
              cases hr : ReadsField p ann ch c' l' 0
              · rfl
              · exact absurd (live_not_irr (hread 0 a0 rfl (Or.inl hr))) (by simp [hairr])
            simp only [ReadsField, hdq, Bool.not_eq_false'] at hrf
            have hq' := hquotOk c' hreach'
            have hnotMem : 2 ∉ erasedParams ty' := fun hm => hner ⟨_, hdq, hm⟩
            simp only [hdq, hnotMem, ↓reduceIte] at hq'
            cases hcr : ann.constRel? c' with
            | none => simp [hcr] at hrf
            | some cr =>
              rw [hcr] at hrf hq'
              cases hrp : cr.params[2]? with
              | none => simp [hrp] at hrf
              | some rp =>
                simp only [Option.bind_some, hrp, Option.map_some, Option.getD_some] at hrf
                simp only [hrp, Bool.not_eq_true'] at hq'
                rw [propWhenCanHold_of_holds hrf] at hq'; cases hq'
      | _ => trivial
  | _ => trivial

end SortDischarge

/-! ## Public theorems for `SortClosed` -/

open SortDischarge in
/-- **`SortClosed` discharges `P1.RunSortAgree`** on any root with literal inputs. -/
theorem runSortAgree_of_sortClosed {p : Src.Program} {ann : Src.Relevance.Ann}
    {ch : Src.Relevance.Checked} (hf : Facts p ann ch) (hs : ShapeOk p)
    (hsc : SortClosed p ann ch = true) {k : Nat} {root : Src.CId} {ns : List Nat}
    (hroot : ∃ ar, (ar, root) ∈ p.roots) :
    Src.Relevance.Proof.P1.RunSortAgree p ann k root (ns.map .lit) := by
  obtain ⟨ar, ha⟩ := hroot
  have hgood1 : GoodCall p ann ch (.evalConst k [] root) := by
    rcases hf.wa.roots _ ha with hge | hin
    · exact Or.inl hge
    · exact Or.inr ⟨_, agree_nil_normalize (Agree.root _) _, hin⟩
  have hrootNoDrop : caseHasSortDrop p ann root = false := by
    unfold SortClosed at hsc
    simp only [Bool.and_eq_true, List.all_eq_true] at hsc
    have := hsc.1.2 (ar, root) ha
    simpa using this
  have hloc1 := localSortCoherent_of_good hf hs hsc hgood1
  refine runSortAgree_of_local hf hs ⟨ar, ha⟩ hloc1 fun f hf0 => ?_
  have hgf := (good_core hf hsc _ hgood1).1 f hf0
  have hwf : SortWhole p ann f := hgf.2 hrootNoDrop
  have hgoodAll : ∀ (ss : List Src.Slot) (g : Src.Value),
      (∀ s ∈ ss, ∃ n, s = .val (.lit n)) →
      GoodVal p ann ch g → SortWhole p ann g →
      GoodAllFit p ann ch k g ss := by
    intro ss
    induction ss with
    | nil => intro _ _ _ _; trivial
    | cons s rest ihss =>
      intro g hss hgg hwg
      obtain ⟨n, rfl⟩ := hss s (List.mem_cons_self ..)
      have hfit : GoodSlotFits p ann ch g (.val (.lit n)) := by
        cases g with
        | pap => exact ⟨.val (.lit n) sortWhole_lit, sortMinorsIgnore_of_sortWhole hwg⟩
        | _ => exact .val (.lit n) sortWhole_lit
      refine ⟨hfit, fun v hv => ?_⟩
      have hpv := (good_core hf hsc (.apply k g (.val (.lit n))) ⟨hgg, hfit⟩).1 v hv
      exact ihss v (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) hpv.1 (hpv.2 hwg)
  have hgood2 : GoodCall p ann ch (.applyAll k f ((ns.map .lit).map .val)) :=
    ⟨hgf.1, hgoodAll _ f (fun s hs' => by
      simp only [List.map_map, List.mem_map, Function.comp] at hs'
      obtain ⟨n, -, rfl⟩ := hs'
      exact ⟨n, rfl⟩) hgf.1 hwf⟩
  exact localSortCoherent_of_good hf hs hsc hgood2

/-- **`SortClosed` discharges `Front.RunSortAgree`** on any `Recheck.run`-accepted artifact. -/
theorem Front.runSortAgree_of_sortClosed (h : run cfg P c = .ok a)
    (hsc : SortDischarge.SortClosed a.src c.relevance a.checked = true) (i : Nat × List Nat) :
    a.front.RunSortAgree c.relevance i := by
  intro k root hr
  obtain ⟨hfr, -, -⟩ := runLir_spec (run_parts h).1
  obtain ⟨installed, hchk, hcan, hsrc⟩ := front_accepted hfr
  have hf : Facts a.src c.relevance a.checked := by
    have := facts_modeEq hchk hcan (Src.Lazify.run_modeEq installed a.checked.keys)
    rw [show a.src = a.front.src from rfl, hsrc]
    exact this
  have hroot : ∃ ar, (ar, root) ∈ a.src.roots := by
    simp only [Artifact.front, Option.map_eq_some_iff] at hr
    obtain ⟨⟨ar, r'⟩, hget, rfl⟩ := hr
    exact ⟨ar, List.mem_of_getElem? hget⟩
  exact _root_.IxCC.Recheck.runSortAgree_of_sortClosed hf (shapeOk_of_run h) hsc hroot

/-- **Discharged narrowing (`Front.RunSortAgree` & `ShapeOk` eliminated).** Under `Recheck.run`'s
acceptance and the kernel-evaluable static check `SortClosed`, the source goes wrong only by being
stuck, trapping, or returning a `Live` value the view rejects: never because of a marker. -/
theorem Front.goesWrong_live_discharged (h : run cfg P c = .ok a)
    (hsc : SortDischarge.SortClosed a.src c.relevance a.checked = true) {i : Nat × List Nat} :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i :=
  Front.goesWrong_live_closed h (Front.runSortAgree_of_sortClosed h hsc i)

/-- **`Recheck.sound` with the narrowed escape and `Front.RunSortAgree` discharged.** -/
theorem sound_live_discharged (h : run cfg P c = .ok a)
    (hsc : SortDischarge.SortClosed a.src c.relevance a.checked = true) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
        ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  sound_live_closed h D hD i hi (Front.runSortAgree_of_sortClosed h hsc i)

/-! ## Semantic `BinderMeta.pw` + `M.graded` bridge (`GradedSortBridge`) -/

/-- Semantic sort-agreement witness instantiated from Ixon v5 `BinderMeta.pw` and `M.graded` (in
`IxCCGrounding`, keeping `IxCC` isolated from `IxCK.Kernel.Denotes`). Each obligation is purely
local at a single call `c` whose precondition holds, given the `Post` of its child calls. -/
structure GradedSortBridge (p : Src.Program) (ann : Src.Relevance.Ann) (ch : Src.Relevance.Checked) :
    Prop where
  /-- (a) E7: an application argument irrelevant by sort (`BinderMeta.pw` from `M.graded`) meets a
  receiver whose value ignores it (`IgnoresNext`). -/
  appIgnores : ∀ k ls ρ f a m r,
    Pre p ann ch (.eval k ls ρ (.app f a m r)) →
    (∀ c', Step p (.eval k ls ρ (.app f a m r)) c' → Pre p ann ch c' → Post p ann ch c') →
    r.irrAt ls = true → ¬ WrittenErasedArg p (.app f a m r) →
    ∀ fv, Src.eval p k ls ρ f = .ok fv → IgnoresNext ann fv
  /-- (f) E6: a projection yields a marker only from a field written erased (`M.graded` prevents
  projecting a sort-dropped proof/type field). -/
  projKept : ∀ k ls ρ s i e,
    Pre p ann ch (.eval k ls ρ (.proj s i e)) →
    (∀ c', Step p (.eval k ls ρ (.proj s i e)) c' → Pre p ann ch c' → Post p ann ch c') →
    ∀ cv lsv ps fs v, Src.eval p k ls ρ e = .ok (.con cv lsv ps fs) →
      fs[i]? = some v → v.isIrr = true → Src.Relevance.Check.fieldWrittenErased p cv i = true
  /-- (d) F2/F3: recursor rule λ binders match sort-irrelevant parameters and sort-dropped fields
  (`BinderMeta.pw` agreement on recursor rules). -/
  recRuleBinder : ∀ k r ls args,
    Pre p ann ch (.fire (k + 1) (.recr r) ls args) →
    (∀ c', Step p (.fire (k + 1) (.recr r) ls args) c' → Pre p ann ch c' → Post p ann ch c') →
    SortCoherent p ann (.fire (k + 1) (.recr r) ls args)
  /-- (c) F5: a `case` key minor ignores every non-erased sort-dropped field (`M.graded` typing of
  eliminator minors, covering higher-order `dite` and mixed `Prod`+`Fin` programs). -/
  caseMinorIgnores : ∀ k c ls args,
    Pre p ann ch (.fire (k + 1) (.cases c) ls args) →
    (∀ c', Step p (.fire (k + 1) (.cases c) ls args) c' → Pre p ann ch c' → Post p ann ch c') →
    SortCoherent p ann (.fire (k + 1) (.cases c) ls args)
  /-- (e) F8: `Quot.lift` passes a sort-irrelevant element only to a function that ignores it. -/
  quotLiftIgnores : ∀ k c ls α r β f h q,
    Pre p ann ch (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q]) →
    (∀ c', Step p (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q]) c' → Pre p ann ch c' → Post p ann ch c') →
    SortCoherent p ann (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q])

private theorem localSortCoherent_of_graded {p : Src.Program} {ann : Src.Relevance.Ann}
    {ch : Src.Relevance.Checked} (hg : GradedSortBridge p ann ch) (top : Call) :
    SortDischarge.LocalSortCoherent p ann ch top := by
  intro c _ hpre hpost
  cases c with
  | eval k ls ρ t =>
    cases t with
    | app f a m r => exact hg.appIgnores k ls ρ f a m r hpre hpost
    | proj s i e => exact hg.projKept k ls ρ s i e hpre hpost
    | _ => trivial
  | fire k h ls args =>
    cases k with
    | zero => trivial
    | succ k' =>
      cases h with
      | recr r => exact hg.recRuleBinder k' r ls args hpre hpost
      | cases c => exact hg.caseMinorIgnores k' c ls args hpre hpost
      | quotLift c =>
        rcases args with _ | ⟨α, _ | ⟨r, _ | ⟨β, _ | ⟨f, _ | ⟨h, _ | ⟨q, _ | _⟩⟩⟩⟩⟩⟩ <;> try trivial
        exact hg.quotLiftIgnores k' c ls α r β f h q hpre hpost
      | _ => trivial
  | _ => trivial

/-- **`GradedSortBridge` discharges `P1.RunSortAgree`** on any root with literal inputs. -/
theorem runSortAgree_of_graded {p : Src.Program} {ann : Src.Relevance.Ann}
    {ch : Src.Relevance.Checked} (hf : Facts p ann ch) (hs : ShapeOk p)
    (hg : GradedSortBridge p ann ch) {k : Nat} {root : Src.CId} {ns : List Nat}
    (hroot : ∃ ar, (ar, root) ∈ p.roots) :
    Src.Relevance.Proof.P1.RunSortAgree p ann k root (ns.map .lit) :=
  SortDischarge.runSortAgree_of_local hf hs hroot (localSortCoherent_of_graded hg _)
    (fun _ _ => localSortCoherent_of_graded hg _)

/-- **`GradedSortBridge` discharges `Front.RunSortAgree`** on any `Recheck.run`-accepted artifact. -/
theorem Front.runSortAgree_of_graded (h : run cfg P c = .ok a)
    (hg : GradedSortBridge a.src c.relevance a.checked) (i : Nat × List Nat) :
    a.front.RunSortAgree c.relevance i := by
  intro k root hr
  obtain ⟨hfr, -, -⟩ := runLir_spec (run_parts h).1
  obtain ⟨installed, hchk, hcan, hsrc⟩ := front_accepted hfr
  have hf : Facts a.src c.relevance a.checked := by
    have := facts_modeEq hchk hcan (Src.Lazify.run_modeEq installed a.checked.keys)
    rw [show a.src = a.front.src from rfl, hsrc]
    exact this
  have hroot : ∃ ar, (ar, root) ∈ a.src.roots := by
    simp only [Artifact.front, Option.map_eq_some_iff] at hr
    obtain ⟨⟨ar, r'⟩, hget, rfl⟩ := hr
    exact ⟨ar, List.mem_of_getElem? hget⟩
  exact _root_.IxCC.Recheck.runSortAgree_of_graded hf (shapeOk_of_run h) hg hroot

/-- **Semantic narrowing (`GradedSortBridge` from `BinderMeta.pw` + `M.graded`).** -/
theorem Front.goesWrong_live_of_graded (h : run cfg P c = .ok a)
    (hg : GradedSortBridge a.src c.relevance a.checked) {i : Nat × List Nat} :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i :=
  Front.goesWrong_live_closed h (Front.runSortAgree_of_graded h hg i)

/-- **`Recheck.sound` with the narrowed escape via `GradedSortBridge`.** -/
theorem sound_live_of_graded (h : run cfg P c = .ok a)
    (hg : GradedSortBridge a.src c.relevance a.checked) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
        ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  sound_live_closed h D hD i hi (Front.runSortAgree_of_graded h hg i)

end IxCC.Recheck
