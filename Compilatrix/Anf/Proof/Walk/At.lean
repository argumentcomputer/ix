import Compilatrix.Anf.Proof.Walk.Step

/-! # The rewriting walk: the simulation statement

`ExpSim n out env here k e`: from a source environment and join closures
related to the walk's (`WEnv`, `JEnv` with the target meaning of `k`), target
environments of the walk's depths satisfying its facts, no use of a dropped
binding, and a source continuation matched by `k`, the walked term `out`
simulates the source term `e` followed by the continuation (M2.3).
`WalkAt n fuel` is that statement for every walk function at `fuel`;
`pass_sim` is the case where the term is an operand. -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable (P Q : Program) (Valid : Cfg → List Val → List Val → Prop) (Xc : Nat → List Val → Exp → Exp → Prop)

/-- The walk's output (configuration `C`) simulates the source term followed
by the source continuation. -/
def ExpSim (n : Nat) (C : Cfg) (out : Exp) (env : Walk.Env) (here : Here) (k : Kont) (e : Exp) :
    Prop :=
  ∀ (ρ : List Val) (J : List JClo) (ρ' : List Val) (J' : List JClo) (live jlive : List Bool)
    (SK : Val → Nat → Result Val), Valid C ρ ρ' →
    WEnv Q Valid Xc C live env.σ ρ ρ' → JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J →
    here.d = ρ'.length → here.dj = J'.length → FactsOk Q Valid here.facts ρ' → NoDead live jlive e →
    KontW Q Valid Xc n k SK ρ' J' →
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J e).bind (SK · k)) (fun k => eval Q k ρ' J' out)

/-- The simulation of every walk function at fuel `fuel`, bound `n`. -/
structure WalkAt (n fuel : Nat) : Prop where
  walk : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃e : Exp⦄ ⦃k : Kont⦄ ⦃out : Exp⦄ ⦃s s' : Fires⦄,
    (Walk.walk C fuel env here e k).run s = .ok (out, s') →
    ExpSim P Q Valid Xc n C out env here k e
  after : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃body : Exp⦄ ⦃k k' : Kont⦄ ⦃s s' : Fires⦄,
    (Walk.after C fuel env body k).run s = .ok (k', s') →
    ∀ (ρ : List Val) (J : List JClo) (ρ' : List Val) (J' : List JClo) (live jlive : List Bool)
      (SK : Val → Nat → Result Val), Valid C ρ ρ' →
    WEnv Q Valid Xc C live env.σ ρ ρ' → JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J →
    NoDead (true :: live) jlive body → KontW Q Valid Xc n k SK ρ' J' →
    KontW Q Valid Xc n k' (fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) ρ' J'
  walkBind : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃c : Ixon.V3.LetContract⦄ ⦃b : Bind⦄
    ⦃body : Exp⦄ ⦃k : Kont⦄ ⦃out : Exp⦄ ⦃s s' : Fires⦄,
    (Walk.walkBind C fuel env here c b body k).run s = .ok (out, s') →
    ExpSim P Q Valid Xc n C out env here k (.bind c b body)
  walkJoin : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃ar : Nat⦄ ⦃r : Bool⦄ ⦃b body : Exp⦄
    ⦃k : Kont⦄ ⦃out : Exp⦄ ⦃s s' : Fires⦄,
    (Walk.walkJoin C fuel env here ar r b body k).run s = .ok (out, s') →
    ExpSim P Q Valid Xc n C out env here k (.join ar r b body)
  walkJump : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃j : Nat⦄ ⦃as : List Atom⦄ ⦃k : Kont⦄
    ⦃out : Exp⦄ ⦃s s' : Fires⦄,
    (Walk.walkJump C fuel env here j as k).run s = .ok (out, s') →
    ExpSim P Q Valid Xc n C out env here k (.jump j as)
  walkCase : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃x : Atom⦄ ⦃alts : List Alt⦄
    ⦃d : Option Exp⦄ ⦃k : Kont⦄ ⦃out : Exp⦄ ⦃s s' : Fires⦄,
    (Walk.walkCase C fuel env here x alts d k).run s = .ok (out, s') →
    ExpSim P Q Valid Xc n C out env here k (.case x alts d)
  walkAlts : ∀ ⦃C : Cfg⦄ ⦃env : Walk.Env⦄ ⦃here : Here⦄ ⦃xo : Opd⦄ ⦃alts : List Alt⦄ ⦃k : Kont⦄
    ⦃alts' : List Alt⦄ ⦃s s' : Fires⦄,
    (Walk.walkAlts C fuel env here xo alts k).run s = .ok (alts', s') →
    ∀ (ρ : List Val) (J : List JClo) (ρ' : List Val) (J' : List JClo) (live jlive : List Bool)
      (SK : Val → Nat → Result Val), Valid C ρ ρ' →
    WEnv Q Valid Xc C live env.σ ρ ρ' → JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J →
    here.d = ρ'.length → here.dj = J'.length → FactsOk Q Valid here.facts ρ' →
    (∀ a ∈ alts, NoDead (List.replicate a.arity true ++ live) jlive a.body) →
    KontW Q Valid Xc n k SK ρ' J' →
    ∀ (c : Key.CtorKey) (fs fs' : List Val) (w : Val) (dflt : Option Exp) (dflt' : Option Exp),
    WVs Q Valid Xc fs fs' → xo.val ρ' = some w → w.asCtor Q.known = some (c, fs') →
    ((dflt = none ∧ dflt' = none) ∨ ∃ e e', dflt = some e ∧ dflt' = some e' ∧
      SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J e).bind (SK · k)) (fun k => eval Q k ρ' J' e')) →
    SimUpTo (WV Q Valid Xc) n (fun k => (evalAlts P k ρ J c fs alts dflt).bind (SK · k))
      (fun k => evalAlts Q k ρ' J' c fs' alts' dflt')

variable {P Q Valid Xc}

/-- Passing an operand to the continuation. -/
theorem pass_sim {n : Nat} {here : Here} {o : Opd} {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.pass here o k).run s = .ok (out, s')) {ρ' : List Val} {J' : List JClo}
    (hd : here.d = ρ'.length) (hdj : here.dj = J'.length) (hfacts : FactsOk Q Valid here.facts ρ')
    {SK : Val → Nat → Result Val} (hk : KontW Q Valid Xc n k SK ρ' J') {x w : Val}
    (ho : o.val ρ' = some w) (hx : WV Q Valid Xc x w) :
    SimUpTo (WV Q Valid Xc) n (SK x) (fun k => eval Q k ρ' J' out) := by
  cases k with
  | ret =>
    simp only [Walk.pass] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    obtain ⟨T, hT, hs⟩ := hk
    simp only [KT, Option.some.injEq] at hT
    subst hT
    refine (hs x w hx).congr (fun _ => rfl) (fun k => ?_)
    rw [eval_ret', hd, Opd.val_atom ho]; rfl
  | jump l =>
    simp only [Walk.pass] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    obtain ⟨T, hT, hs⟩ := hk
    simp only [KT] at hT
    split at hT
    · next hl =>
      obtain ⟨jcl, hjcl, rfl⟩ := Option.map_eq_some_iff.1 hT
      refine (hs x w hx).congr (fun _ => rfl) (fun k => ?_)
      rw [hd, hdj]
      have hat : evalAtoms ρ' [o.atom ρ'.length] = some [w] := by simp [evalAtoms, Opd.val_atom ho]
      rw [eval_jump, hjcl, hat]; rfl
    · cases hT
  | cont f =>
    simp only [Walk.pass] at h
    exact hk here o out s s' ρ' J' h (List.suffix_refl _) (List.suffix_refl _) hd hdj hfacts x w ho hx

end Compilatrix.Anf.WalkProof
