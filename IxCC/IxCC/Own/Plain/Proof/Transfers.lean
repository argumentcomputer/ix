import IxCC.Own.Plain.Proof.Drops
import IxCC.Own.Plain.Proof.CaptureRoots
import IxCC.Own.Plain.Proof.Scope

/-! The actual canonical copies-then-drops schedule stutters at the source
clock and transfers owned arguments plus captured roots to its continuation. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

theorem evalActions_append (ρ : Own.Env) (H : Heap) (as bs : List Action) :
    evalActions ρ H (as ++ bs) =
      (evalActions ρ H as).bind fun H' => evalActions ρ H' bs := by
  induction as generalizing H with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, evalActions]
    cases ha : evalAction ρ H a <;> simp [Result.bind, ih]

def copiedArgs (seen : List Fir.Var) : List Fir.Arg → List Fir.Arg
  | [] => []
  | .var x :: as =>
    if seen.contains x then .var x :: copiedArgs seen as
    else copiedArgs (x :: seen) as
  | a :: as => a :: copiedArgs seen as

theorem moveCopies_eq_copies (seen : List Fir.Var) (args : List Fir.Arg) :
    moveCopies seen args = copies (copiedArgs seen args) := by
  induction args generalizing seen with
  | nil => rfl
  | cons a as ih =>
    cases a with
    | var x =>
      dsimp only [moveCopies, copiedArgs]
      cases h : seen.contains x
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ih]
      · rw [if_pos rfl, if_pos rfl, copies, ih]
    | lit _ => exact ih seen
    | erased => exact ih seen

theorem copiedArgs_sublist (seen : List Fir.Var) (args : List Fir.Arg) :
    (copiedArgs seen args).Sublist args := by
  induction args generalizing seen with
  | nil => exact .slnil
  | cons a as ih =>
    cases a with
    | var x =>
      dsimp only [copiedArgs]
      cases seen.contains x
      · rw [if_neg Bool.false_ne_true]; exact (ih (x :: seen)).cons _
      · rw [if_pos rfl]; exact (ih seen).cons_cons _
    | lit _ => exact (ih seen).cons_cons _
    | erased => exact (ih seen).cons_cons _

theorem copiedArgs_scope {live : List Fir.Var} (seen : List Fir.Var) {args : List Fir.Arg}
    (hs : args.all (argIn live) = true) :
    (copiedArgs seen args).all (argIn live) = true := by
  rw [List.all_eq_true] at hs ⊢
  intro a ha
  exact hs a ((copiedArgs_sublist seen args).subset ha)

theorem evalArgs_of_sublist {ρ : Own.Env} {as bs : List Fir.Arg} {vs : List RVal}
    (hsub : as.Sublist bs) (hb : Own.evalArgs ρ bs = some vs) :
    ∃ us, Own.evalArgs ρ as = some us := by
  induction hsub generalizing vs with
  | slnil => exact ⟨[], rfl⟩
  | cons _ _ ih =>
    obtain ⟨_, _, _, hbs, _⟩ := evalArgs_cons_inv hb
    exact ih hbs
  | cons_cons _ _ ih =>
    obtain ⟨v, _, ha, hbs, _⟩ := evalArgs_cons_inv hb
    obtain ⟨us, hus⟩ := ih hbs
    exact ⟨v :: us, by simp [Own.evalArgs, ha, hus]⟩

theorem EnvRoots.lookup {ρ : Own.Env} {live : List Fir.Var} {roots : List RVal}
    (hr : EnvRoots ρ live roots) {x : Fir.Var} (hx : x ∈ live) :
    ∃ v, ρ.get? x = some v ∧ v ∈ roots := by
  induction live generalizing roots with
  | nil => cases hx
  | cons y ys ih =>
    obtain ⟨v, vs, hy, ht, rfl⟩ := envRoots_cons hr
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨v, hy, List.mem_cons_self⟩
    · obtain ⟨w, hw, hm⟩ := ih ht hx
      exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩

theorem retained_sublist (seen live : List Fir.Var) :
    (retained seen live).Sublist live := by
  induction live with
  | nil => exact .slnil
  | cons x xs ih =>
    dsimp only [retained, List.filter]
    cases seen.contains x
    · exact ih.cons _
    · exact ih.cons_cons _

theorem retained_congr_on {cs₁ cs₂ live : List Fir.Var}
    (h : ∀ x ∈ live, cs₁.contains x = cs₂.contains x) :
    retained cs₁ live = retained cs₂ live := by
  induction live with
  | nil => rfl
  | cons x xs ih =>
    have htail := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    dsimp only [retained, List.filter] at htail ⊢
    rw [h x List.mem_cons_self, htail]

theorem contains_append_cons (seen rest : List Fir.Var) (x y : Fir.Var) :
    (seen ++ x :: rest).contains y = ((x :: seen) ++ rest).contains y := by
  induction seen with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.cons_append, List.contains_cons, ih]
    cases y == z <;> cases y == x <;> rfl

theorem contains_append_left {seen : List Fir.Var} {x : Fir.Var}
    (hx : seen.contains x = true) (rest : List Fir.Var) :
    (seen ++ rest).contains x = true := by
  induction seen with
  | nil => cases hx
  | cons z zs ih =>
    simp only [List.cons_append, List.contains_cons] at hx ⊢
    cases hxz : x == z with
    | true => rfl
    | false =>
      simp only [hxz, Bool.false_or] at hx
      exact ih hx

theorem contains_append_of_mem {seen : List Fir.Var} {x : Fir.Var}
    (hx : seen.contains x = true) (rest : List Fir.Var) (y : Fir.Var) :
    (seen ++ x :: rest).contains y = (seen ++ rest).contains y := by
  rw [contains_append_cons]
  simp only [List.cons_append, List.contains_cons]
  cases h : y == x with
  | false => rfl
  | true =>
    have heq : y = x := LawfulBEq.eq_of_beq h
    subst y
    exact (contains_append_left hx rest).symm

theorem retained_cons_of_not_mem {x : Fir.Var} {seen live : List Fir.Var}
    (hx : x ∉ live) :
    retained (x :: seen) live = retained seen live := by
  apply retained_congr_on
  intro y hy
  simp only [List.contains_cons]
  cases h : y == x with
  | false => rfl
  | true =>
    have heq : y = x := LawfulBEq.eq_of_beq h
    subst y
    exact False.elim (hx hy)

theorem retained_cons_step {ρ : Own.Env} {live seen : List Fir.Var}
    {roots keptSeen keptNext : List RVal} {x : Fir.Var} {v : RVal}
    (hr : EnvRoots ρ live roots) (hd : live.Nodup)
    (hx_mem : x ∈ live) (hx_val : ρ.get? x = some v)
    (hx_unseen : seen.contains x = false)
    (hk : EnvRoots ρ (retained seen live) keptSeen)
    (hk' : EnvRoots ρ (retained (x :: seen) live) keptNext) :
    (∀ location, refsIn location keptNext = refsIn location (v :: keptSeen)) ∧
    (∀ w, w ∈ v :: keptSeen → w ∈ keptNext) := by
  induction live generalizing roots keptSeen keptNext with
  | nil => cases hx_mem
  | cons y ys ih =>
    obtain ⟨u, us, hy, ht, rfl⟩ := envRoots_cons hr
    obtain ⟨hy_not_mem, hd_ys⟩ := List.nodup_cons.mp hd
    cases heq : y == x with
    | true =>
      have hyx : y = x := LawfulBEq.eq_of_beq heq
      subst y
      have huv : u = v := Option.some.inj (hy.symm.trans hx_val)
      subst u
      have hret_seen : retained seen (x :: ys) = retained seen ys := by
        dsimp only [retained, List.filter]
        rw [hx_unseen]
      have hk_ys : EnvRoots ρ (retained seen ys) keptSeen := hret_seen ▸ hk
      have hret_cons : retained (x :: seen) (x :: ys) = x :: retained seen ys := by
        have hcx : (x :: seen).contains x = true := by
          simp only [List.contains_cons, heq, Bool.true_or]
        have htail := retained_cons_of_not_mem (seen := seen) hy_not_mem
        dsimp only [retained, List.filter] at htail ⊢
        rw [hcx, htail]
      rw [hret_cons] at hk'
      obtain ⟨v', keptNext', hx', hk'_ys, rfl⟩ := envRoots_cons hk'
      have hvv' : v' = v := Option.some.inj (hx'.symm.trans hx_val)
      subst v'
      have hks : keptNext' = keptSeen := Option.some.inj (hk'_ys.symm.trans hk_ys)
      subst keptNext'
      exact ⟨fun _ => rfl, fun _ h => h⟩
    | false =>
      have hne : x ≠ y := fun h => by
        subst h
        have hrefl : (x == x) = true := decide_eq_true rfl
        rw [hrefl] at heq
        cases heq
      have hx_ys : x ∈ ys := by
        rcases List.mem_cons.mp hx_mem with rfl | hm
        · exact False.elim (hne rfl)
        · exact hm
      have hcy : (x :: seen).contains y = seen.contains y := by
        simp only [List.contains_cons, heq, Bool.false_or]
      cases hseen_y : seen.contains y with
      | true =>
        have hret_seen : retained seen (y :: ys) = y :: retained seen ys := by
          dsimp only [retained, List.filter]
          rw [hseen_y]
        have hret_cons : retained (x :: seen) (y :: ys) = y :: retained (x :: seen) ys := by
          dsimp only [retained, List.filter]
          rw [hcy, hseen_y]
        have hk_cons : EnvRoots ρ (y :: retained seen ys) keptSeen := hret_seen ▸ hk
        have hk'_cons : EnvRoots ρ (y :: retained (x :: seen) ys) keptNext := hret_cons ▸ hk'
        obtain ⟨u₁, ks, hy₁, hk_ys, rfl⟩ := envRoots_cons hk_cons
        obtain ⟨u₂, kn, hy₂, hk'_ys, rfl⟩ := envRoots_cons hk'_cons
        have hu₁ : u₁ = u := Option.some.inj (hy₁.symm.trans hy)
        have hu₂ : u₂ = u := Option.some.inj (hy₂.symm.trans hy)
        subst u₁ u₂
        obtain ⟨hrefs, hmem⟩ := ih ht hd_ys hx_ys hk_ys hk'_ys
        refine ⟨fun location => ?_, fun w hw => ?_⟩
        · have hl := hrefs location
          dsimp only [refsIn] at hl ⊢
          omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact List.mem_cons_of_mem _ (hmem _ List.mem_cons_self)
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmem w (List.mem_cons_of_mem _ hw))
      | false =>
        have hret_seen : retained seen (y :: ys) = retained seen ys := by
          dsimp only [retained, List.filter]
          rw [hseen_y]
        have hret_cons : retained (x :: seen) (y :: ys) = retained (x :: seen) ys := by
          dsimp only [retained, List.filter]
          rw [hcy, hseen_y]
        exact ih ht hd_ys hx_ys (hret_seen ▸ hk) (hret_cons ▸ hk')

theorem moveCopies_raw_balance {ρ : Own.Env} {live seen : List Fir.Var}
    {args : List Fir.Arg} {roots values incValues keptSeen keptAll : List RVal}
    (hr : EnvRoots ρ live roots) (hd : live.Nodup)
    (hs : args.all (argIn live) = true)
    (ha : Own.evalArgs ρ args = some values)
    (hc : Own.evalArgs ρ (copiedArgs seen args) = some incValues)
    (hk : EnvRoots ρ (retained seen live) keptSeen)
    (hkAll : EnvRoots ρ (retained (seen ++ argVars args) live) keptAll) :
    (∀ location, refsIn location (values ++ keptSeen) = refsIn location (incValues ++ keptAll)) ∧
    (∀ v, v ∈ values ++ keptSeen → v ∈ incValues ++ keptAll) := by
  induction args generalizing seen values incValues keptSeen with
  | nil =>
    have hv : values = [] := by simpa [Own.evalArgs] using ha.symm
    have hi : incValues = [] := by simpa [copiedArgs, Own.evalArgs] using hc.symm
    subst values incValues
    have hka : EnvRoots ρ (retained seen live) keptAll := by
      simpa [argVars] using hkAll
    have hkeq : keptAll = keptSeen := Option.some.inj (hka.symm.trans hk)
    subst keptAll
    exact ⟨fun _ => rfl, fun _ h => h⟩
  | cons a as ih =>
    have hparts : argIn live a = true ∧ as.all (argIn live) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hs
    obtain ⟨v, vs, hav, has, rfl⟩ := evalArgs_cons_inv ha
    cases a with
    | var x =>
      have hx_live : x ∈ live := by simpa [argIn] using hparts.1
      have hx_val : ρ.get? x = some v := hav
      cases hseen : seen.contains x with
      | true =>
        have hcopy_eq : copiedArgs seen (.var x :: as) = .var x :: copiedArgs seen as := by
          dsimp only [copiedArgs]
          rw [hseen, if_pos rfl]
        have hc' : Own.evalArgs ρ (.var x :: copiedArgs seen as) = some incValues :=
          hcopy_eq ▸ hc
        obtain ⟨v', incVs, hv', hcas, rfl⟩ := evalArgs_cons_inv hc'
        have hvv' : v' = v := Option.some.inj (hv'.symm.trans hx_val)
        subst v'
        have hret : retained (seen ++ x :: argVars as) live = retained (seen ++ argVars as) live :=
          retained_congr_on (fun y _ => contains_append_of_mem hseen (argVars as) y)
        have hkAll' : EnvRoots ρ (retained (seen ++ argVars as) live) keptAll := by
          simpa only [argVars, hret] using hkAll
        obtain ⟨hrefs, hmem⟩ := ih hparts.2 has hcas hk hkAll'
        refine ⟨fun location => ?_, fun w hw => ?_⟩
        · dsimp only [List.cons_append, refsIn]
          rw [hrefs location]
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hmem w hw)
      | false =>
        have hcopy_eq : copiedArgs seen (.var x :: as) = copiedArgs (x :: seen) as := by
          dsimp only [copiedArgs]
          rw [hseen, if_neg Bool.false_ne_true]
        have hcas : Own.evalArgs ρ (copiedArgs (x :: seen) as) = some incValues :=
          hcopy_eq ▸ hc
        obtain ⟨keptNext, hkNext, _⟩ :=
          hr.restrict (retained_sublist (x :: seen) live)
        obtain ⟨hstep_refs, hstep_mem⟩ :=
          retained_cons_step hr hd hx_live hx_val hseen hk hkNext
        have hret : retained (seen ++ x :: argVars as) live = retained ((x :: seen) ++ argVars as) live :=
          retained_congr_on (fun y _ => contains_append_cons seen (argVars as) x y)
        have hkAll' : EnvRoots ρ (retained ((x :: seen) ++ argVars as) live) keptAll := by
          simpa only [argVars, hret] using hkAll
        obtain ⟨hrefs, hmem⟩ := ih hparts.2 has hcas hkNext hkAll'
        refine ⟨fun location => ?_, fun w hw => ?_⟩
        · have h1 := hstep_refs location
          have h2 := hrefs location
          dsimp only [List.cons_append, refsIn] at h1 ⊢
          rw [refsIn_append] at h2 ⊢
          omega
        · apply hmem
          rcases List.mem_cons.mp hw with rfl | hw
          · exact List.mem_append_right _ (hstep_mem _ List.mem_cons_self)
          · rcases List.mem_append.mp hw with hw | hw
            · exact List.mem_append_left _ hw
            · exact List.mem_append_right _ (hstep_mem w (List.mem_cons_of_mem _ hw))
    | lit l =>
      obtain ⟨v', incVs, hv', hcas, rfl⟩ := evalArgs_cons_inv hc
      have hvv' : v' = v := Option.some.inj (hv'.symm.trans hav)
      subst v'
      obtain ⟨hrefs, hmem⟩ := ih hparts.2 has hcas hk hkAll
      refine ⟨fun location => ?_, fun w hw => ?_⟩
      · dsimp only [List.cons_append, refsIn]
        rw [hrefs location]
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmem w hw)
    | erased =>
      obtain ⟨v', incVs, hv', hcas, rfl⟩ := evalArgs_cons_inv hc
      have hvv' : v' = v := Option.some.inj (hv'.symm.trans hav)
      subst v'
      obtain ⟨hrefs, hmem⟩ := ih hparts.2 has hcas hk hkAll
      refine ⟨fun location => ?_, fun w hw => ?_⟩
      · dsimp only [List.cons_append, refsIn]
        rw [hrefs location]
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmem w hw)

theorem retained_imm_balance {ρ : Own.Env} {captured imm live : List Fir.Var}
    {kept keptImm : List RVal}
    (himm : ImmEnv ρ imm)
    (hk : EnvRoots ρ (retained captured live) kept)
    (hkImm : EnvRoots ρ (retained (captured ++ imm) live) keptImm) :
    (∀ location, refsIn location kept = refsIn location keptImm) ∧
    (∀ v, v ∈ kept → v ∈ keptImm) := by
  induction live generalizing kept keptImm with
  | nil =>
    have h1 : kept = [] := by simpa [EnvRoots, retained, Own.evalArgs] using hk.symm
    have h2 : keptImm = [] := by simpa [EnvRoots, retained, Own.evalArgs] using hkImm.symm
    subst kept keptImm
    exact ⟨fun _ => rfl, fun _ h => h⟩
  | cons y ys ih =>
    cases hcap : captured.contains y with
    | true =>
      have hcapImm : (captured ++ imm).contains y = true := contains_append_left hcap imm
      have hret1 : retained captured (y :: ys) = y :: retained captured ys := by
        dsimp only [retained, List.filter]
        rw [hcap]
      have hret2 : retained (captured ++ imm) (y :: ys) = y :: retained (captured ++ imm) ys := by
        dsimp only [retained, List.filter]
        rw [hcapImm]
      have hk1 : EnvRoots ρ (y :: retained captured ys) kept := hret1 ▸ hk
      have hk2 : EnvRoots ρ (y :: retained (captured ++ imm) ys) keptImm := hret2 ▸ hkImm
      obtain ⟨vy, kept', hy1, hkt1, rfl⟩ := envRoots_cons hk1
      obtain ⟨vy', keptImm', hy2, hkt2, rfl⟩ := envRoots_cons hk2
      have hvy : vy' = vy := Option.some.inj (hy2.symm.trans hy1)
      subst vy'
      obtain ⟨hrefs, hmem⟩ := ih hkt1 hkt2
      refine ⟨fun location => ?_, fun w hw => ?_⟩
      · dsimp only [refsIn]
        rw [hrefs location]
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmem w hw)
    | false =>
      have hret1 : retained captured (y :: ys) = retained captured ys := by
        dsimp only [retained, List.filter]
        rw [hcap]
      have hk1 : EnvRoots ρ (retained captured ys) kept := hret1 ▸ hk
      cases hcapImm : (captured ++ imm).contains y with
      | false =>
        have hret2 : retained (captured ++ imm) (y :: ys) = retained (captured ++ imm) ys := by
          dsimp only [retained, List.filter]
          rw [hcapImm]
        have hk2 : EnvRoots ρ (retained (captured ++ imm) ys) keptImm := hret2 ▸ hkImm
        exact ih hk1 hk2
      | true =>
        have hret2 : retained (captured ++ imm) (y :: ys) = y :: retained (captured ++ imm) ys := by
          dsimp only [retained, List.filter]
          rw [hcapImm]
        have hk2 : EnvRoots ρ (y :: retained (captured ++ imm) ys) keptImm := hret2 ▸ hkImm
        obtain ⟨vy, keptImm', hy, hkt2, rfl⟩ := envRoots_cons hk2
        have hy_mem : y ∈ imm := by
          rcases List.mem_append.mp (List.contains_iff_mem.mp hcapImm) with hmem | hmem
          · have htrue : captured.contains y = true := List.contains_iff_mem.mpr hmem
            exact False.elim (Bool.false_ne_true (hcap.symm.trans htrue))
          · exact hmem
        obtain ⟨vy', hy', himm_vy⟩ := himm y hy_mem
        have hvy : vy' = vy := Option.some.inj (hy'.symm.trans hy)
        subst vy'
        obtain ⟨hrefs, hmem⟩ := ih hk1 hkt2
        refine ⟨fun location => ?_, fun w hw => List.mem_cons_of_mem _ (hmem w hw)⟩
        rw [refsIn_cons_imm keptImm' himm_vy location, hrefs location]

theorem moveCopies_transfer_balance {ρ : Own.Env} {live imm captured : List Fir.Var}
    {args : List Fir.Arg} {roots values incValues kept keptAll : List RVal}
    (hr : EnvRoots ρ live roots) (hd : live.Nodup) (himm : ImmEnv ρ imm)
    (hs : args.all (argIn live) = true)
    (ha : Own.evalArgs ρ args = some values)
    (hc : Own.evalArgs ρ (copiedArgs (captured ++ imm) (heapArgs imm args)) = some incValues)
    (hk : EnvRoots ρ (retained captured live) kept)
    (hkAll : EnvRoots ρ (retained ((captured ++ imm) ++ argVars (heapArgs imm args)) live) keptAll) :
    (∀ location, refsIn location (values ++ kept) = refsIn location (incValues ++ keptAll)) ∧
    (∀ v, v ∈ values ++ kept → v ∈ incValues ++ keptAll ∨ ImmVal v) := by
  obtain ⟨heapValues, hheap, hrefs_heap, hmem_heap⟩ := evalArgs_heapArgs himm ha
  obtain ⟨keptImm, hkImm, _⟩ := hr.restrict (retained_sublist (captured ++ imm) live)
  obtain ⟨hrefs_imm, hmem_imm⟩ := retained_imm_balance himm hk hkImm
  obtain ⟨hrefs_raw, hmem_raw⟩ :=
    moveCopies_raw_balance hr hd (heapArgs_scope imm hs) hheap hc hkImm hkAll
  refine ⟨fun location => ?_, fun v hv => ?_⟩
  · have h1 := hrefs_heap location
    have h2 := hrefs_imm location
    have h3 := hrefs_raw location
    rw [refsIn_append, h1, h2, ← refsIn_append, h3]
  · rcases List.mem_append.mp hv with hv | hv
    · rcases hmem_heap v hv with hvh | himm_v
      · exact Or.inl (hmem_raw v (List.mem_append_left _ hvh))
      · exact Or.inr himm_v
    · exact Or.inl (hmem_raw v (List.mem_append_right _ (hmem_imm v hv)))

theorem transfer_sound (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (live imm captured : List Fir.Var) (args : List Fir.Arg) (c : Code)
    {external : Nat → Nat} {roots values : List RVal}
    (hr : EnvRoots ρ live roots) (hd : live.Nodup) (himm : ImmEnv ρ imm)
    (hb : Balance H external roots)
    (hs : args.all (argIn live) = true) (ha : Own.evalArgs ρ args = some values) :
    ∃ H' kept,
      eval P k ρ J H (transfer live imm captured args c) = eval P k ρ J H' c ∧
      EnvRoots ρ (retained captured live) kept ∧ Balance H' external (values ++ kept) ∧
      (∀ v, v ∈ kept → v ∈ roots) ∧
      (∀ v, v ∈ values ++ kept → H.value? v = H'.value? v) ∧
      (∀ v, ExternalRoot external v → H.value? v = H'.value? v) := by
  have hsub := (copiedArgs_sublist (captured ++ imm) (heapArgs imm args)).trans (heapArgs_sublist imm args)
  obtain ⟨incValues, hinc⟩ := evalArgs_of_sublist hsub ha
  have ho_inc : ArgsOwned ρ (copiedArgs (captured ++ imm) (heapArgs imm args)) roots := by
    intro x hx
    have hx_arg : Fir.Arg.var x ∈ args := hsub.subset hx
    have hx_live : x ∈ live := by
      simpa [argIn] using (List.all_eq_true.mp hs) (.var x) hx_arg
    exact hr.lookup hx_live
  obtain ⟨H₁, hcopy, hb₁, hv₁⟩ :=
    copies_sound ρ H (copiedArgs (captured ++ imm) (heapArgs imm args)) hb ho_inc hinc
  obtain ⟨H₂, keptAll, hdrop, hkAll, hb₂, _, hv₂, he₂⟩ :=
    drops_sound ρ H₁ ((captured ++ imm) ++ argVars (heapArgs imm args)) live hr hb₁
  obtain ⟨kept, hk, hk_sub⟩ :=
    hr.restrict (retained_sublist captured live)
  obtain ⟨hrefs, hmem⟩ :=
    moveCopies_transfer_balance hr hd himm hs ha hinc hk hkAll
  have hb' : Balance H₂ external (values ++ kept) := by
    intro l
    rw [hrefs l]
    exact hb₂ l
  refine ⟨H₂, kept, ?_, hk, hb', fun v hm => hk_sub.subset hm,
    fun v hm => (hv₁ v).trans (by
      rcases hmem v hm with hm_raw | himm_v
      · exact hv₂ v hm_raw
      · exact value?_eq_of_immVal H₁ H₂ himm_v),
    fun v he => (hv₁ v).trans (he₂ v he)⟩
  unfold transfer transferActions
  rw [eval_actionPrefix, evalActions_append, moveCopies_eq_copies, hcopy]
  simp only [Result.bind_ok, hdrop]


end IxCC.Own.Plain
