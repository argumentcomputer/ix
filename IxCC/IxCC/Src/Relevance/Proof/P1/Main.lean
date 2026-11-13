import IxCC.Src.Relevance.Proof.P1.App
import IxCC.Src.Relevance.Proof.P1.RunLive

/-! # P1, relevance preservation: the theorem

The 25 cases of the core (`IxCC.Src.Relevance.Proof.P1.Cases`) are proved: five in `Cases`, F2
and F3 in `Recr`, E6, F1, F7 and F8 in `Ctor`, E8, δ, `headValue`, F6 and F6w in `Delta`, E1, E4,
E5, A1–A3, `applyAll`, `force` and `forceAll` in `Plumbing`, F5 in `CaseKey`, E7 in `App`.
`cases_all` collects them, and P1's approved statements follow with no further hypothesis than
L1's facts (`Facts`), the structure (`ShapeOk`) and the run's sort events (`SortAgree`,
`RunSortAgree`), which nothing proves:

* `preserve`: every call a run makes whose precondition holds has its `Post`;
* `pre_step`: the precondition propagates along every step but the shielded variable's evaluation;
* `run_live`: `Src.run` on a root and literal inputs returns a `Live` value (`RunLiveStmt`, the
  statement the consumption takes): δ on the root has its precondition (`WellAnnotated.roots`: the
  root is reached at the empty profile), and the literal slots fit its value one by one. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-- The 25 cases of the core, proved. -/
theorem cases_all : Cases p ann ch where
  var := case_var
  sort := case_sort
  pi := case_pi
  natLit := case_natLit
  strLit := case_strLit
  lam := case_lam
  letE := case_letE
  proj := case_proj
  app := case_app
  const := case_const
  evalConst := case_evalConst
  headValue := case_headValue
  apply := case_apply
  applyAll := case_applyAll
  ctor := case_ctor
  quotMk := case_quotMk
  quotLift := case_quotLift
  f2 := case_F2
  f3 := case_F3
  f4 := case_F4
  cases := case_cases
  prim := case_prim
  word := case_word
  force := case_force
  forceAll := case_forceAll

/-- **P1, relevance preservation.** Under L1's facts, the structure, and coherent sort events,
every call a run makes whose precondition holds returns only `Live` values. -/
theorem preserve (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top) :
    ∀ c, Reach p top c → Pre p ann ch c → Post p ann ch c :=
  preserve_of_cases cases_all hf hs hsa

/-- The precondition propagates along every step but one: the evaluation of a variable its spine
shields (a dropped field passed to the minor that ignores it), which returns the marker. -/
theorem pre_step (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top)
    {c c' : Call} (hr : Reach p top c) (hc : Pre p ann ch c) (hst : Step p c c')
    (hsh : ¬ ∃ k ls ρ f m r x, c = .eval k ls ρ (.app f (.var x) m r) ∧ c' = .eval k ls ρ (.var x) ∧
      ShieldedIn x ρ (.app f (.var x) m r)) :
    Pre p ann ch c' :=
  pre_step_of_cases cases_all hf hs hsa hr hc hst hsh

/-! ## What a call reads -/

/-- A major a rule is selected by is no marker. -/
theorem isIrr_of_selectRule {ind np : CId} {major : Value} {jf : Nat × List Slot}
    (h : p.selectRule ind np major = some jf) : major.isIrr = false := by
  cases major with
  | irr _ _ _ => simp [Program.selectRule] at h
  | _ => rfl

/-- What a call with its precondition reads is `Live`: an applied function by `apply`'s
precondition; a projection's structure and field by the `Post`s of the structure's evaluation (a
step) and of the projection; a selected major (ordinary kind) and a lifted quotient by their
`force`'s `Post` (a step), being no marker. -/
theorem reads_live (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top) :
    ∀ c, Reach p top c → Pre p ann ch c → Reads p ann ch c := by
  intro c hr hpre
  unfold Reads
  split
  · intro _
    exact hpre.1
  · rename_i k ls ρ s i e
    intro v w hv hw
    have hst : Step p (.eval k ls ρ (.proj s i e)) (.eval k ls ρ e) := Step.proj
    have hpe := pre_step hf hs hsa hr hpre hst (by
      rintro ⟨_, _, _, _, _, _, _, h1, -, -⟩
      cases h1)
    have hlv := (preserve hf hs hsa _ (.step hr hst) hpe v hv).1
    have hw' : eval p k ls ρ (.proj s i e) = .ok w := by
      rw [eval_proj, hv]
      exact hw
    exact ⟨hlv, (preserve hf hs hsa _ hr hpre w hw').1⟩
  · rename_i k r ls args
    intro sf kk lv np nmot nmin ni ind rules ty major jf hd hk hfo hsel
    have hst : Step p (.fire (k + 1) (.recr r) ls args)
        (.force k (args.getD (np + nmot + nmin + ni) default)) := Step.recMajor hd hk
    have hpf := pre_step hf hs hsa hr hpre hst (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
    exact (preserve hf hs hsa _ (.step hr hst) hpf major hfo).1 (isIrr_of_selectRule hsel)
  · rename_i k c ls args
    intro r sf kk lv np nmot nmin ni ind rules ty major jf hres hd hk hfo hsel
    have hst : Step p (.fire (k + 1) (.cases c) ls args) (.force k (args.getD (np + 1 + ni) default)) :=
      Step.caseMajor hres hd hk
    have hpf := pre_step hf hs hsa hr hpre hst (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
    exact (preserve hf hs hsa _ (.step hr hst) hpf major hfo).1 (isIrr_of_selectRule hsel)
  · rename_i k c0 ls α r β f h q
    intro c' l' ps a hq _
    have hst : Step p (.fire (k + 1) (.quotLift c0) ls [α, r, β, f, h, q]) (.force k q) := Step.liftQuot
    have hpf := pre_step hf hs hsa hr hpre hst (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
    exact (preserve hf hs hsa _ (.step hr hst) hpf _ hq).1 rfl
  · trivial

/-! ## The root -/

/-- A profile agreeing with the empty levels still agrees once normalised. -/
theorem agree_nil_normalize {q : Profile} (hq : Agree [] q) (n : Nat) : Agree [] (q.normalize n) := by
  intro i
  have h0 : (([] : Levels).getD i 0 == 0) = true := by simp
  rw [h0]
  simp only [Profile.normalize, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : (List.range n)[i]? with
  | none => rfl
  | some j =>
    have hj := hq j
    rw [show (([] : Levels).getD j 0 == 0) = true by simp] at hj
    simpa [List.getD_eq_getElem?_getD] using hj

/-- Literal slots fit a `Live` value one by one, along the applications a reached `applyAll`
makes: a literal is `Live` and `Whole`, and ignores every position (so a minor position of a
partial application meets it). -/
theorem allFit_lits (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top)
    {k : Nat} : ∀ (ss : List Slot), (∀ s ∈ ss, ∃ n, s = .val (.lit n)) → ∀ (f : Value),
      Reach p top (.applyAll k f ss) → Live p ann ch f → AllFit p ann ch k f ss
  | [], _, _, _, _ => trivial
  | s :: ss, hss, f, hr, hl => by
    obtain ⟨n, rfl⟩ := hss s (List.mem_cons_self ..)
    have hfit : SlotFits p ann ch f (.val (.lit n)) := by
      have hls : LiveSlot p ann ch (.val (.lit n)) := .val (.lit n) whole_lit
      cases f with
      | clo _ _ _ _ _ => exact fun _ => hls
      | pap h ls args =>
        cases hl with
        | pap _ _ hmin _ =>
          exact ⟨fun _ => hls, minorsIgnore_snoc hmin (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)⟩
      | lit _ => trivial
      | str _ => trivial
      | con _ _ _ _ => trivial
      | irr _ _ _ => trivial
    refine ⟨hfit, fun v hv => ?_⟩
    have hra : Reach p top (.apply k f (.val (.lit n))) := .step hr Step.allHead
    have hlv := (preserve hf hs hsa _ hra ⟨hl, hfit⟩ v hv).1
    exact allFit_lits hf hs hsa ss (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) v
      (.step hr (Step.allRest hv)) hlv

/-- **The root.** `Src.run` on literal inputs returns a `Live` value (`RunLiveStmt`). -/
theorem run_live : RunLiveStmt := by
  intro p ann ch hf hs k root ns v hroot hsa hrun
  obtain ⟨hsa1, hsa2⟩ := hsa
  obtain ⟨a, ha⟩ := hroot
  have hpre : Pre p ann ch (.evalConst k [] root) := by
    rcases hf.wa.roots _ ha with hge | hin
    · exact Or.inl hge
    · exact Or.inr ⟨_, agree_nil_normalize (Agree.root _) _, hin⟩
  unfold Src.run at hrun
  cases hf0 : evalConst p k [] root with
  | ok f =>
    rw [hf0] at hrun
    have hfl := (preserve hf hs hsa1 _ .refl hpre f hf0).1
    have hsa' := hsa2 f hf0
    have hfit : AllFit p ann ch k f ((ns.map Value.lit).map Slot.val) :=
      allFit_lits hf hs hsa' _ (fun s hs' => by
        simp only [List.map_map, List.mem_map, Function.comp] at hs'
        obtain ⟨n, -, rfl⟩ := hs'
        exact ⟨n, rfl⟩) f .refl hfl
    exact (preserve hf hs hsa' _ .refl ⟨hfl, hfit⟩ v hrun).1
  | _ => simp [hf0] at hrun

end IxCC.Src.Relevance.Proof.P1
