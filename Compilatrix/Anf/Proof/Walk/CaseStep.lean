import Compilatrix.Anf.Proof.Walk.Case

/-! # The rewriting walk: case

One fuel level of the walk's simulation for `walkCase`: case of a known
constructor (the selected alternative under its fields), case identity
(the arms rebuild the scrutinee, so the case returns it or jumps with it,
keeping the arms' leading ticks), equal field-free arms (the case's choice
is irrelevant), and the general case (alternatives and default walked, a
meta-continuation first made a join point when the case branches) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → Prop} {n fuel : Nat}

/-- The general case: the walked alternatives and default under the
scrutinee's operand. -/
theorem case_general (hctx : Ctx P Q Valid n) (hW : WalkAt P Q Valid n fuel) {C : Cfg}
    {env : Walk.Env} {here0 : Here} {x : Atom} {alts : List Alt} {d : Option Exp} {k0 : Kont}
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J'0 : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : Valid C ρ') (henv : WEnv Q Valid live env.σ ρ ρ')
    (hJ0 : JEnv P Q Valid n (KT Q k0 J'0) ρ' J'0 jlive env.jσ J) (hd0 : here0.d = ρ'.length)
    (hdj0 : here0.dj = J'0.length) (hf0 : FactsOk Q Valid here0.facts ρ')
    (hnd : NoDead live jlive (.case x alts d)) (hk0 : KontW Q Valid n k0 SK ρ' J'0)
    {xo : Opd} {v w : Val} (hv : x.eval ρ = some v) (hw : xo.val ρ' = some w) (hvw : WV Q Valid v w)
    {alts' : List Alt} {dflt' : Option Exp} {s0 s1 : Fires}
    (halts : (Walk.walkAlts C fuel env here0 xo alts k0).run s0 = .ok (alts', s1))
    (hdflt : (d = none ∧ dflt' = none) ∨ ∃ e e' s2 s3, d = some e ∧ dflt' = some e' ∧
      (Walk.walk C fuel env here0 e k0).run s2 = .ok (e', s3)) :
    SimUpTo (WV Q Valid) n (fun k => (eval P k ρ J (.case x alts d)).bind (SK · k))
      (fun k => eval Q k ρ' J'0 (.case (xo.atom here0.d) alts' dflt')) := by
  rcases Rel.asCtor_rel structural P.known hvw with hnone | ⟨c, vfs, wfs, hvc, hwc, hfs⟩
  · refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
    rw [eval_case, hv]
    simp [Result.ofOption, hnone]
    rfl
  · have hwc' : w.asCtor Q.known = some (c, wfs) := by rw [hctx.known]; exact hwc
    have hdsim : (d = none ∧ dflt' = none) ∨ ∃ e e', d = some e ∧ dflt' = some e' ∧
        SimUpTo (WV Q Valid) n (fun k => (eval P k ρ J e).bind (SK · k)) (fun k => eval Q k ρ' J'0 e') := by
      rcases hdflt with h0 | ⟨e, e', s2, s3, rfl, rfl, he⟩
      · exact .inl h0
      · exact .inr ⟨e, e', rfl, rfl, hW.walk he ρ J ρ' J'0 live jlive SK hV henv hJ0 hd0 hdj0 hf0
          hnd.case_dflt hk0⟩
    refine (hW.walkAlts halts ρ J ρ' J'0 live jlive SK hV henv hJ0 hd0 hdj0 hf0 hnd.case_alts hk0 c vfs
      wfs w d dflt' (of_pw hfs) hw hwc' hdsim).congr (fun k => ?_) (fun k => ?_)
    · rw [eval_case, hv]; simp [Result.ofOption, hvc]
    · rw [eval_case, hd0, Opd.val_atom hw]; simp [Result.ofOption, hwc']

theorem walkCase_step (hctx : Ctx P Q Valid n) (hW : WalkAt P Q Valid n fuel) {C : Cfg}
    {env : Walk.Env} {here : Here} {x : Atom} {alts : List Alt} {d : Option Exp} {k : Kont}
    {out : Exp} {s s' : Fires}
    (h : (Walk.walkCase C (fuel + 1) env here x alts d k).run s = .ok (out, s')) :
    ExpSim P Q Valid n C out env here k (.case x alts d) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkCase] at h
  obtain ⟨xo, s1, h1, h2⟩ := Walk.run_bind_ok h
  clear h
  have h := h2
  clear h2
  dsimp only at h
  obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel' henv h1 hnd.case_atom
  have hK : Q.known = C.prog.known := by rw [hctx.known, hctx.cknown C ρ' hV]
  have hsrc : ∀ k, eval P k ρ J (.case x alts d) = match v.asCtor P.known with
      | some (c, fs) => evalAlts P k ρ J c fs alts d
      | none => .stuck := by
    intro k; rw [eval_case, hv]; rfl
  split at h
  · -- a known constructor
    next fields e hsel =>
    have h' := run_fire_then h
    split at hsel
    · split at hsel
      · next c fs hkn =>
        obtain ⟨⟨isAlt, e'⟩, hs, he⟩ := Option.map_eq_some_iff.1 hsel
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨wfs, hwfs, hwc⟩ := known_sound hK hf hkn hw
        have hwc' : w.asCtor P.known = some (c, wfs) := by rw [← hctx.known]; exact hwc
        rcases Rel.asCtor_rel structural P.known hvw with hnone | ⟨c', vfs, wfs', hvc, hwc2, hfs⟩
        · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hnone]; rfl) (fun _ => rfl)
        · rw [hwc'] at hwc2
          simp only [Option.some.injEq, Prod.mk.injEq] at hwc2
          obtain ⟨rfl, rfl⟩ := hwc2
          have hvl : vfs.length = fs.length := by rw [← (of_pw hfs).length, mapM_length hwfs]
          rw [← hvl] at hs
          obtain ⟨-, hmem, hdf⟩ := select_spec (P := P) (k := 0) (ρ := ρ) (J := J) hs
          have hsrc' : ∀ k, (eval P k ρ J (.case x alts d)).bind (SK · k) =
              (eval P k ((if isAlt then vfs.reverse else []) ++ ρ) J e').bind (SK · k) := by
            intro k; rw [hsrc, hvc]; dsimp only; rw [(select_spec hs).1]
          cases isAlt with
          | true =>
            obtain ⟨a, ha, hab, haa⟩ := hmem rfl
            have henvb := WEnv.pushOpds (mapM_reverse hwfs) (of_pw hfs).reverse henv
            have hnda := hnd.case_alts a ha
            rw [haa, hab, hvl] at hnda
            rw [List.length_reverse] at henvb
            exact (hW.walk h' _ J ρ' J' _ jlive SK hV (by simpa using henvb) hJ hd hdj hf hnda hk).congr
              (fun k => by rw [hsrc']; rfl) (fun _ => rfl)
          | false =>
            have hnda := NoDead.case_dflt (by rw [← hdf rfl]; exact hnd)
            exact (hW.walk h' _ J ρ' J' _ jlive SK hV (by simpa using henv) hJ hd hdj hf hnda hk).congr
              (fun k => by rw [hsrc']; rfl) (fun _ => rfl)
      · cases hsel
    · cases hsel
  · next hsel =>
    split at h
    · -- a case identity
      next m tail hid =>
      have h' := run_fire_then h
      split at hid
      · next hc =>
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
        obtain ⟨_, rfl⟩ := hc
        obtain ⟨hne, harms⟩ := identityTail_spec hid
        rcases Rel.asCtor_rel structural P.known hvw with hnone | ⟨c, vfs, wfs, hvc, hwc, hfs⟩
        · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hnone]; rfl) (fun _ => rfl)
        rcases evalAlts_identity (P := P) (ρ := ρ) (J := J) (c := c) (fs := vfs) harms with
          hst | ⟨rfl, hz, c0, heq⟩
        · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hvc]; dsimp only; rw [hst]; rfl)
            (fun _ => rfl)
        have hz' : P.known.natZero ≠ some c := by rw [← hctx.cknown C ρ' hV]; exact hz
        have hv' : v = .con c [] := asCtor_nil hvc hz'
        subst hv'
        have hsrc' : ∀ k, (eval P k ρ J (.case x alts none)).bind (SK · k) =
            (Nat.repeat (fun f k => later k f) m
              (fun k => eval P k ρ J (.bind c0 (.con c []) (idTail tail))) k).bind (SK · k) := by
          intro k; rw [hsrc, hvc]; dsimp only; rw [heq, eval_ticks]
        cases tail with
        | none =>
          obtain ⟨o', s2, h2, h3⟩ := Walk.run_bind_ok h'
          obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
          refine (sim_ticks (eval_mono P ρ J _) (eval_mono Q ρ' J' o') m ?_).congr hsrc'
            (fun k => eval_ticks k ρ' J' m o')
          refine (pass_sim h2 hd hdj hf hk hw hvw).congr (fun k => ?_) (fun _ => rfl)
          simp [idTail, eval_bind, evalBind_con, evalAtoms_nil, Result.ofOption, eval_ret', Atom.eval]
        | some j =>
          obtain ⟨o', s2, h2, h3⟩ := Walk.run_bind_ok h'
          obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
          refine (sim_ticks (eval_mono P ρ J _) (eval_mono Q ρ' J' o') m ?_).congr hsrc'
            (fun k => eval_ticks k ρ' J' m o')
          have hndj : NoDead live jlive (.jump j [x]) := by
            refine ⟨fun i hi => by simpa [Exp.occ, Atom.occList] using hnd.case_atom i hi,
              fun j' hj' => ?_⟩
            simp only [Exp.jocc]
            split
            · next hjj =>
              exfalso
              have h0 := hnd.2 j' hj'
              obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
              obtain ⟨key, c1, rfl, -⟩ := harms a ha
              have := altsJocc_mem (by simp only [Exp.jocc, Exp.optJocc] at h0; omega) _ ha
              simp only [Alt.body] at this
              have ht : ∀ m', Exp.jocc j' (Walk.ticks m' (.bind c1 (.con key []) (idTail (some j)))) = 1 := by
                intro m'
                induction m' with
                | zero => simp [Walk.ticks, Exp.jocc, idTail, beq_iff_eq.1 hjj]
                | succ m' ih => simpa [Walk.ticks, Exp.jocc] using ih
              rw [ht] at this
              cases this
            · rfl
          refine (hW.walk h2 ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hndj hk).congr
            (fun k => ?_) (fun _ => rfl)
          simp only [idTail]
          rw [eval_bind, evalBind_con]
          simp only [evalAtoms_nil, Result.ofOption, Result.bind_ok]
          rw [eval_jump, eval_jump]
          have hx0 : (Atom.var 0).eval (Val.con c [] :: ρ) = some (Val.con c []) := rfl
          simp [evalAtoms, Result.ofOption, hv, hx0]
      · cases hid
    · next hid =>
      split at h
      · -- equal arms
        next e hsame =>
        have h' := run_fire_then h
        split at hsame
        · obtain ⟨hall, hdflt, hne⟩ := sameArms_spec hsame
          obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨ha0, hab⟩ := hall a ha
          have hnde := hnd.case_alts a ha
          rw [ha0, hab] at hnde
          simp only [List.replicate_zero, List.nil_append] at hnde
          rcases Rel.asCtor_rel structural P.known hvw with hnone | ⟨c, vfs, wfs, hvc, hwc, hfs⟩
          · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hnone]; rfl) (fun _ => rfl)
          rcases evalAlts_same (P := P) (ρ := ρ) (J := J) (c := c) (fs := vfs) hdflt hall with heq | hst
          · exact (hW.walk h' ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnde hk).congr
              (fun k => by rw [hsrc, hvc]; dsimp only; rw [heq]) (fun _ => rfl)
          · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hvc]; dsimp only; rw [hst]; rfl)
              (fun _ => rfl)
        · cases hsame
      · -- the general case
        have hgo : ∀ (here0 : Here) (k0 : Kont) (J'0 : List JClo) (alts' : List Alt) (dflt' : Option Exp)
            (s0 s0' : Fires), (Walk.walkAlts C fuel env here0 xo alts k0).run s0 = .ok (alts', s0') →
            ((d = none ∧ dflt' = none) ∨ ∃ e e' s2 s3, d = some e ∧ dflt' = some e' ∧
              (Walk.walk C fuel env here0 e k0).run s2 = .ok (e', s3)) →
            here0.d = here.d → here0.facts = here.facts → here0.dj = J'0.length →
            JEnv P Q Valid n (KT Q k0 J'0) ρ' J'0 jlive env.jσ J → KontW Q Valid n k0 SK ρ' J'0 →
            SimUpTo (WV Q Valid) n (fun k => (eval P k ρ J (.case x alts d)).bind (SK · k))
              (fun k => eval Q k ρ' J'0 (.case (xo.atom here0.d) alts' dflt')) :=
          fun here0 k0 J'0 alts' dflt' s0 s0' halts hdflt hd0 hf0 hdj0 hJ0 hk0 =>
            case_general hctx hW hV henv hJ0 (by rw [hd0, hd]) hdj0 (by rw [hf0]; exact hf) hnd hk0 hv hw
              hvw halts hdflt
        have hJK : ∀ (k0 : Kont) (J'0 : List JClo), J' <:+ J'0 →
            (KT Q k J' = none ∨ KT Q k0 J'0 = KT Q k J') →
            JEnv P Q Valid n (KT Q k0 J'0) ρ' J'0 jlive env.jσ J := by
          intro k0 J'0 hsuf hKT
          rcases hKT with hKT | hKT
          · rw [hKT] at hJ; exact JEnv.retarget hJ
          · rw [hKT]; exact hJ.suffix (List.suffix_refl _) hsuf
        cases d with
        | none =>
          dsimp only at h
          by_cases hb : (alts.length + if (none : Option Exp).isSome = true then 1 else 0) ≥ 2
          · simp only [hb, ↓reduceIte] at h
            refine branch_sim h hd hdj hf hk fun here0 k0 out0 s0 s0' J'0 hrun hd0 hf0 hdj0 hsuf _ hKT hk0 => ?_
            obtain ⟨alts', s2, h2, h3⟩ := Walk.run_bind_ok hrun
            obtain ⟨dflt', s4, h4, h5⟩ := Walk.run_bind_ok h3
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
            exact hgo here0 k0 J'0 alts' none s0 s2 h2 (.inl ⟨rfl, rfl⟩) hd0 hf0 hdj0
              (hJK k0 J'0 hsuf hKT) hk0
          · simp only [hb, ↓reduceIte] at h
            obtain ⟨alts', s2, h2, h3⟩ := Walk.run_bind_ok h
            obtain ⟨dflt', s4, h4, h5⟩ := Walk.run_bind_ok h3
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
            exact hgo here k J' alts' none s1 s2 h2 (.inl ⟨rfl, rfl⟩) rfl rfl hdj
              (hJK k J' (List.suffix_refl _) (.inr rfl)) hk
        | some e =>
          dsimp only at h
          by_cases hb : (alts.length + if (some e).isSome = true then 1 else 0) ≥ 2
          · simp only [hb, ↓reduceIte] at h
            refine branch_sim h hd hdj hf hk fun here0 k0 out0 s0 s0' J'0 hrun hd0 hf0 hdj0 hsuf _ hKT hk0 => ?_
            obtain ⟨alts', s2, h2, h3⟩ := Walk.run_bind_ok hrun
            obtain ⟨dflt', s4, h4, h5⟩ := Walk.run_bind_ok h3
            obtain ⟨e', he', rfl⟩ := Walk.run_map_ok h4
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
            exact hgo here0 k0 J'0 alts' (some e') s0 s2 h2 (.inr ⟨e, e', s2, s4, rfl, rfl, he'⟩) hd0 hf0
              hdj0 (hJK k0 J'0 hsuf hKT) hk0
          · simp only [hb, ↓reduceIte] at h
            obtain ⟨alts', s2, h2, h3⟩ := Walk.run_bind_ok h
            obtain ⟨dflt', s4, h4, h5⟩ := Walk.run_bind_ok h3
            obtain ⟨e', he', rfl⟩ := Walk.run_map_ok h4
            obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
            exact hgo here k J' alts' (some e') s1 s2 h2 (.inr ⟨e, e', s2, s4, rfl, rfl, he'⟩) rfl rfl hdj
              (hJK k J' (List.suffix_refl _) (.inr rfl)) hk

end Compilatrix.Anf.WalkProof
