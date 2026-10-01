import Compilatrix.Anf.Proof.Walk.StepB

/-! # The rewriting walk: jumps

One fuel level of the walk's simulation for `walkJump`: a join point inlined
at its single jump, a small join point inlined at a jump, case-of-case (a
jump with a known constructor to a join point that scrutinises its
parameter takes the selected alternative), and an emitted jump (the join
entry's `JoinR`). Each inlining replaces the jump's charge (and the
skipped leading ticks) by ticks (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

/-! ## Alternatives selected by a known constructor -/

theorem evalAlts_find {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {c : Key.CtorKey}
    {fs : List Val} {d : Option Exp} : ∀ {alts : List Alt} {a : Alt},
    alts.find? (fun a => decide (a.key = c) && a.arity == fs.length) = some a →
    evalAlts P k ρ J c fs alts d = eval P k (fs.reverse ++ ρ) J a.body ∧ a ∈ alts ∧
      a.arity = fs.length
  | [], _, h => by simp at h
  | .mk key m body :: rest, a, h => by
    rw [evalAlts_cons]
    by_cases hc : key = c ∧ m = fs.length
    · rw [if_pos hc]
      have hp : (decide ((Alt.mk key m body).key = c) && (Alt.mk key m body).arity == fs.length) = true := by
        simp [Alt.key, Alt.arity, hc.1, hc.2]
      rw [List.find?_cons_of_pos (p := fun (a : Alt) => decide (a.key = c) && a.arity == fs.length) hp, Option.some.injEq] at h
      subst h
      exact ⟨rfl, List.mem_cons_self, hc.2⟩
    · rw [if_neg hc]
      have hp : ¬ (decide ((Alt.mk key m body).key = c) && (Alt.mk key m body).arity == fs.length) = true :=
        fun hp' => hc (by simp only [Alt.key, Alt.arity, Bool.and_eq_true, beq_iff_eq] at hp'; exact ⟨of_decide_eq_true hp'.1, hp'.2⟩)
      rw [List.find?_cons_of_neg (p := fun (a : Alt) => decide (a.key = c) && a.arity == fs.length) hp] at h
      obtain ⟨h1, h2, h3⟩ := evalAlts_find h
      exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩

theorem evalAlts_find_none {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {c : Key.CtorKey}
    {fs : List Val} {d : Option Exp} : ∀ {alts : List Alt},
    alts.find? (fun a => decide (a.key = c) && a.arity == fs.length) = none →
    evalAlts P k ρ J c fs alts d = (match d with | some e => eval P k ρ J e | none => .stuck)
  | [], _ => evalAlts_nil P k ρ J c fs d
  | .mk key m body :: rest, h => by
    rw [evalAlts_cons]
    by_cases hc : key = c ∧ m = fs.length
    · have hp : (decide ((Alt.mk key m body).key = c) && (Alt.mk key m body).arity == fs.length) = true := by
        simp [Alt.key, Alt.arity, hc.1, hc.2]
      rw [List.find?_cons_of_pos (p := fun (a : Alt) => decide (a.key = c) && a.arity == fs.length) hp] at h
      cases h
    · rw [if_neg hc]
      have hp : ¬ (decide ((Alt.mk key m body).key = c) && (Alt.mk key m body).arity == fs.length) = true :=
        fun hp' => hc (by simp only [Alt.key, Alt.arity, Bool.and_eq_true, beq_iff_eq] at hp'; exact ⟨of_decide_eq_true hp'.1, hp'.2⟩)
      rw [List.find?_cons_of_neg (p := fun (a : Alt) => decide (a.key = c) && a.arity == fs.length) hp] at h
      exact evalAlts_find_none h

/-- The alternative `select` picks is the one evaluation takes. -/
theorem select_spec {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {c : Key.CtorKey}
    {fs : List Val} {alts : List Alt} {d : Option Exp} {isAlt : Bool} {e : Exp}
    (h : Walk.select alts d c fs.length = some (isAlt, e)) :
    evalAlts P k ρ J c fs alts d = eval P k ((if isAlt then fs.reverse else []) ++ ρ) J e ∧
      (isAlt = true → ∃ a ∈ alts, a.body = e ∧ a.arity = fs.length) ∧ (isAlt = false → d = some e) := by
  simp only [Walk.select] at h
  split at h
  · next a ha =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := evalAlts_find (P := P) (k := k) (ρ := ρ) (J := J) (d := d) ha
    exact ⟨by simpa using h1, fun _ => ⟨a, h2, rfl, h3⟩, by simp⟩
  · next ha =>
    obtain ⟨e', he', hp⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [evalAlts_find_none ha, he']
    exact ⟨by simp, by simp, fun _ => rfl⟩

/-! ## Ticks on both sides -/

theorem repeat_later_mono {c : Nat → Result Val} (hc : ClockMono c) :
    ∀ m, ClockMono (Nat.repeat (fun f k => later k f) m c)
  | 0 => hc
  | m + 1 => ClockMono.later (repeat_later_mono hc m)

theorem sim_ticks {R : Val → Val → Prop} {n : Nat} {c : Nat → Result Val} {T : Nat → Result Val}
    {SK : Val → Nat → Result Val} (hc : ClockMono c) (hT : ClockMono T) :
    ∀ m : Nat, SimUpTo R n (fun k => (c k).bind (SK · k)) T →
      SimUpTo R n (fun k => (Nat.repeat (fun f k => later k f) m c k).bind (SK · k))
        (fun k => Nat.repeat (fun f k => later k f) m T k)
  | 0, h => h
  | m + 1, h =>
    SimUpTo.tick (repeat_later_mono hc m) (repeat_later_mono hT m) (sim_ticks hc hT m h)

theorem NoDead.ticks {live jlive : List Bool} : ∀ {m : Nat} {e : Exp},
    NoDead live jlive (Walk.ticks m e) → NoDead live jlive e
  | 0, _, h => h
  | _ + 1, _, h => NoDead.ticks h.tick

variable {P Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {n fuel : Nat}

/-- Case-of-case: the jump's charge and the join body's leading ticks
become ticks over the walk of the alternative a known constructor
selects. -/
theorem caseOfCase_sim (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {here : Here}
    {k : Kont} {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo}
    {SK : Val → Nat → Result Val} (hV : Valid C ρ') (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ') (hk : KontW Q Valid Xc n k SK ρ' J')
    {j m : Nat} {alts : List Alt} {dflt : Option Exp} {ρj : List Val} {Jj : List JClo}
    {livej jlj : List Bool} {σj : List Ent} {jσj : List JEnt}
    (hJj : J[j]? = some (.mk ρj Jj 1 (Walk.ticks m (.case (.var 0) alts dflt)) false))
    (henvj : WEnv Q Valid Xc livej σj ρj ρ') (hJjj : JEnv P Q Valid Xc n (KT Q k J') ρ' J' jlj jσj Jj)
    (hndj : NoDead (true :: livej) jlj (Walk.ticks m (.case (.var 0) alts dflt)))
    {as : List Atom} {v w : Val} {o : Opd} (hvs : evalAtoms ρ as = some [v]) (how : o.val ρ' = some w)
    (hvw : WV Q Valid Xc v w) {c : Key.CtorKey} {fs : List Opd} {isAlt : Bool} {alt0 o' : Exp}
    {s s2 : Fires} (hkn : Walk.known C.prog.known here o = some (c, fs))
    (hsel : Walk.select alts dflt c fs.length = some (isAlt, alt0))
    (h2 : (Walk.walk C fuel (Walk.Env.mk ((if isAlt then Walk.entsOf fs.reverse else []) ++ Ent.opd o :: σj)
      jσj) here alt0 k).run s = .ok (o', s2)) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.jump j as)).bind (SK · k))
      (fun k => eval Q k ρ' J' (Walk.ticks (m + 1) o')) := by
  have hK : Q.known = C.prog.known := by rw [hctx.known, hctx.cknown C ρ' hV]
  obtain ⟨wfs, hwfs, hwc⟩ := known_sound hK hf hkn how
  have hfl := mapM_length hwfs
  have hndc := hndj.ticks
  have hsrc : ∀ k, (eval P k ρ J (.jump j as)).bind (SK · k) =
      (Nat.repeat (fun f k => later k f) (m + 1)
        (fun k => eval P k (v :: ρj) Jj (.case (.var 0) alts dflt)) k).bind (SK · k) := by
    intro k
    rw [eval_jump, hJj]
    simp only [Result.ofOption, Result.bind_ok, hvs, jumpTo, List.length_singleton, if_true,
      Bool.false_eq_true, if_false, List.reverse_singleton, List.singleton_append, eval_ticks]
    rfl
  refine (sim_ticks (eval_mono P _ Jj _) (eval_mono Q ρ' J' o') (m + 1) ?_).congr hsrc
    (fun k => eval_ticks k ρ' J' (m + 1) o')
  rcases Rel.asCtor_rel structural.toBase P.known hvw with hnone | ⟨c', vfs, wfs', hvc, hwc', hfs⟩
  · refine (SimUpTo.stuck (fun k => eval Q k ρ' J' o')).congr (fun k => ?_) (fun _ => rfl)
    rw [eval_case]
    simp [Atom.eval, Result.ofOption, hnone]
    rfl
  · rw [← hctx.known, hwc] at hwc'
    simp only [Option.some.injEq, Prod.mk.injEq] at hwc'
    obtain ⟨rfl, rfl⟩ := hwc'
    have hvl : vfs.length = fs.length := by rw [← (of_pw hfs).length, hfl]
    rw [← hvl] at hsel
    have hcase : ∀ k, eval P k (v :: ρj) Jj (.case (.var 0) alts dflt) =
        eval P k ((if isAlt then vfs.reverse else []) ++ v :: ρj) Jj alt0 := by
      intro k
      rw [eval_case]
      simp only [Atom.eval, List.getElem?_cons_zero, Result.ofOption, Result.bind_ok, hvc]
      exact (select_spec (k := k) hsel).1
    obtain ⟨-, hmem, hdf⟩ := select_spec (P := P) (k := 0) (ρ := v :: ρj) (J := Jj) hsel
    have hbase : WEnv Q Valid Xc (true :: livej) (.opd o :: σj) (v :: ρj) ρ' := .live (.opd how hvw) henvj
    cases isAlt with
    | true =>
      obtain ⟨a, ha, hab, haa⟩ := hmem rfl
      have henvb := WEnv.pushOpds (mapM_reverse hwfs) (of_pw hfs).reverse hbase
      have hnda := NoDead.case_alts hndc a ha
      rw [haa, hab, hvl] at hnda
      rw [List.length_reverse] at henvb
      exact (hW.walk h2 _ Jj ρ' J' _ jlj SK hV (by simpa using henvb) hJjj hd hdj hf hnda hk).congr
        (fun k => by rw [hcase]; rfl) (fun _ => rfl)
    | false =>
      have hnda := NoDead.case_dflt (by rw [← hdf rfl]; exact hndc)
      exact (hW.walk h2 _ Jj ρ' J' _ jlj SK hV (by simpa using hbase) hJjj hd hdj hf hnda hk).congr
        (fun k => by rw [hcase]; rfl) (fun _ => rfl)

theorem walkJump_step (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg}
    {env : Walk.Env} {here : Here} {j : Nat} {as : List Atom} {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkJump C (fuel + 1) env here j as k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.jump j as) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkJump] at h
  obtain ⟨os, s1, h1, h2⟩ := Walk.run_bind_ok h
  clear h
  have h := h2
  clear h2
  dsimp only at h
  obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h1 fun i hi => by
    simpa [Exp.occ] using hnd.1 i hi
  clear h1
  have hlen := hJ.length
  have hlive : ∀ {je : JEnt}, env.jσ[j]? = some je → jlive[j]? = some true := fun hj =>
    jlive_of_occ (hlen.1.trans hlen.2.symm) hj fun j' hj' e => by
      subst e; have := hnd.2 j' hj'; simp [Exp.jocc] at this
  have hosl : os.length = vs.length := by rw [← mapM_length hws, hvws.length]
  split at h
  · -- inlined at its single jump
    next _ σj jσj ar r0 b hj =>
    split at h
    · next har =>
      have har' : os.length = ar := by simpa using har
      have h' := run_fire_then h
      obtain ⟨o, s2, h2, h3⟩ := Walk.run_bind_ok h'
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
      obtain ⟨rfl, ρj, Jj, livej, jlj, hJj, henvj, hJjj, hndj⟩ := hJ.get_once hj (hlive hj)
      have henvb := WEnv.pushOpds (mapM_reverse hws) hvws.reverse henvj
      rw [List.length_reverse, har'] at henvb
      have := hW.walk h2 (vs.reverse ++ ρj) Jj ρ' J' _ jlj SK hV henvb hJjj hd hdj hf hndj hk
      refine (SimUpTo.tick (eval_mono P _ Jj b) (eval_mono Q ρ' J' o) this).congr (fun k => ?_)
        (fun k => by rw [eval_tick])
      rw [eval_jump, hJj]
      simp only [Result.ofOption, Result.bind_ok, hvs, jumpTo, show vs.length = ar by omega, if_true,
        Bool.false_eq_true, if_false]
    · exact absurd h (fun h => Walk.run_throw_ok h)
  · -- an emitted join point
    next _ l σj jσj ar r0 b hj =>
    obtain ⟨ρj, Jj, livej, jlj, jc', Tk, hJj, hl, hjc', hT, hR, henvj, hJjj, hndj⟩ :=
      hJ.get_emitted hj (hlive hj)
    have hSK := hk.meaning hT
    split at h
    · -- a small join point, inlined
      next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨_, hr0⟩, har⟩, _⟩ := hc
      subst hr0
      have h' := run_fire_then h
      obtain ⟨o, s2, h2, h3⟩ := Walk.run_bind_ok h'
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
      have henvb := WEnv.pushOpds (mapM_reverse hws) hvws.reverse henvj
      rw [List.length_reverse, har] at henvb
      simp only [Bool.false_eq_true, if_false] at hndj
      have := hW.walk h2 (vs.reverse ++ ρj) Jj ρ' J' _ jlj SK hV henvb hJjj hd hdj hf hndj hk
      refine (SimUpTo.tick (eval_mono P _ Jj b) (eval_mono Q ρ' J' o) this).congr (fun k => ?_)
        (fun k => by rw [eval_tick])
      rw [eval_jump, hJj]
      simp only [Result.ofOption, Result.bind_ok, hvs, jumpTo, show vs.length = ar by omega, if_true,
        Bool.false_eq_true, if_false]
    · next hsmall =>
      split at h
      · -- case-of-case
        next σ' alt hhit =>
        have h' := run_fire_then h
        obtain ⟨o', s2, h2, h3⟩ := Walk.run_bind_ok h'
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
        obtain ⟨m, inner, hsb⟩ : ∃ m inner, Walk.stripTicks b = (m, inner) := ⟨_, _, rfl⟩
        have hb := stripTicks_eq hsb
        simp only [hsb] at hhit ⊢
        split at hhit
        · next hc =>
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
          obtain ⟨⟨_, hr0⟩, har⟩ := hc
          subst hr0 har
          split at hhit
          · rename_i _ _ alts dflt o
            subst hb
            split at hhit
            · next c fs hkn =>
              split at hhit
              · next isAlt alt0 hsel =>
                split at hhit
                · simp only [Option.some.injEq, Prod.mk.injEq] at hhit
                  obtain ⟨rfl, rfl⟩ := hhit
                  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
                    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
                      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hws
                    obtain ⟨w, _, _, rfl, rfl⟩ := hws
                    exact ⟨w, rfl⟩
                  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
                    cases hvws with
                    | cons hv hrest => cases hrest; exact ⟨_, rfl⟩
                  have hvw : WV Q Valid Xc v w := by cases hvws with | cons hv _ => exact hv
                  have how : o.val ρ' = some w := by
                    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
                      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hws
                    obtain ⟨w', hw', _, rfl, h''⟩ := hws
                    cases h''; exact hw'
                  simp only [Bool.false_eq_true, if_false, List.replicate_one, List.singleton_append]
                    at hndj
                  exact caseOfCase_sim hctx hW hV hd hdj hf hk hJj henvj hJjj hndj hvs how hvw hkn hsel h2
                · cases hhit
              · cases hhit
            · cases hhit
          · cases hhit
        · cases hhit
      · -- an emitted jump
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
        have hcall := hR n (Nat.le_refl n) SK hSK vs ws hvws
        refine hcall.congr (fun k => ?_) (fun k => ?_)
        · rw [eval_jump, hJj]; simp [Result.ofOption, hvs]
        · rw [eval_jump, hd, hdj, hjc']
          simp [Result.ofOption, Walk.atoms, opds_eval hws]
  · exact absurd h (fun h => Walk.run_throw_ok h)

end Compilatrix.Anf.WalkProof
