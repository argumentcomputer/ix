import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarBasic
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarDiv
import IxCC.Rt.Proof.OpsWord

/-!
# The fixed-width word primitives on the plain-RC route (stage W1)

The word expansions are proved once against the heap-free core `Rt.Proof.PrimCore`
(`Rt.Proof.word_core`); this route's simulation relation follows from it by `rhsSim_of_core`, as
the immortal route's does by `Rt.Proof.rhsSim_of_core`. `div`, `mod`, `land`, `lor` and `xor`
emit the `Nat` primitives' code, so their simulations transfer from this route's `Nat` lemmas
(`rhsSim_of_nat`).
-/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap Width WordOp)

/-- The relation after an expansion: `x` bound to the word of the new value, every other register
below the supply as before. -/
theorem envRel_insert_frame {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env}
    {ρl ρl' : Lir.Env} (h : EnvRel T P D sup ρ ρl) {x : Nat} (hx : x < sup) {w : Word} {n : Nat}
    (hρx : ρl'[x]? = some w) (hw : natWord n = some w) (hρy : ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    EnvRel T P D sup (ρ.insert x (.lit (.nat n))) ρl' where
  dom := by
    intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact h.dom hy
  val := by
    intro y v' hy hD
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx
      subst hyx
      cases hy
      exact ⟨w, hρx, hw⟩
    · rename_i hyx
      obtain ⟨w', hw', hv'⟩ := h.val hy hD
      exact ⟨w', by rw [hρy y (h.dom hy) hyx]; exact hw', hv'⟩

/-- **This route's simulation from the heap-free core.** -/
theorem rhsSim_of_core {T : Tables} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup fn L p L' p' x : Nat}
    {f : Fir.FunId} {op : Lam.Prim} {las : List Lir.Arg} {as : List Fir.Arg}
    (hops : operands f as = .ok (some las)) (hlive : ∀ a ∈ as, LiveArg D a) (hx : x < sup)
    (hnb : ∀ ns b, op.sem ns ≠ some (.bool b)) (hc : Rt.Proof.PrimCore lp ctx sup fn L p L' p' x op las) :
    RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim op as)) := by
  intro P H ρ ρl mem rest v H' hρ hr
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Own.primResult] at hres
  cases hn : Own.natArgs vs with
  | none => simp [hn] at hres
  | some ns =>
    simp only [hn] at hres
    cases hs : op.sem ns with
    | none => simp [hs] at hres
    | some r =>
      cases r with
      | bool b => exact absurd hs (hnb ns b)
      | nat n =>
        simp only [hs, Sem.Result.ok.injEq] at hres
        subst hres
        rcases hc ρl mem rest ns ws n hws (Rt.Proof.natArgs_words (fun h => h) hrel hn) hreads hs with
          ⟨c, ρl', w, hstar, hw, hρx, hρy⟩ | hfail
        · exact .inl ⟨c, ρl', hstar, envRel_insert_frame hρ hx hρx hw hρy⟩
        · exact .inr hfail

/-- **The `Nat` code transfers** on this route, as `Rt.Proof.rhsSim_of_nat` on the immortal one. -/
theorem rhsSim_of_nat {T : Tables} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup fn L p L' p' x : Nat}
    {as : List Fir.Arg} {w : Width} {op : WordOp} {nop : Lam.Prim}
    (himp : ∀ (ns : List Nat) (n : Nat), Lam.wordSem w op ns = some (.nat n) → nop.sem ns = some (.nat n))
    (h : RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim nop as))) :
    RhsSim T lp ctx D sup fn L p L' p' x (.fir (.prim (.word w op) as)) := by
  intro P H ρ ρl mem rest v H' hρ hr
  apply h P H ρ ρl mem rest v H' hρ
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  have hres' : Own.primResult (ownTables T) nop vs = .ok v := by
    simp only [Own.primResult] at hres ⊢
    cases hn : Own.natArgs vs with
    | none => simp [hn] at hres
    | some ns =>
      simp only [hn] at hres ⊢
      cases hs : (Lam.Prim.word w op).sem ns with
      | none => simp [hs] at hres
      | some r =>
        cases r with
        | nat n =>
          simp only [hs] at hres
          rw [Lam.Prim.sem_word] at hs
          rw [himp ns n hs]
          exact hres
        | bool b => exact absurd hs (Rt.Proof.word_not_bool w op ns b)
  simp only [Own.evalRhs, hvs, hres', Sem.Result.map, Sem.Result.bind]

/-- **Every word primitive's expansion simulates Cfg's primitive on this route** (the case of
`primitive_sim` for `Lam.Prim.word`). -/
theorem prim_word {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st st' : St} {x : Nat} {w : Width}
    {o : WordOp} {las : List Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x (.word w o) las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some las))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim (.word w o) as)) := by
  cases o
  case div =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first
      | exact rhsSim_of_nat (nop := .natDiv) (Rt.Proof.wordSem_nat_of rfl fun p q => by
          rw [sem_nat2 .natDiv (by decide)]
          by_cases hq : q = 0 <;> simp [hq, WordOp.eval, Src.WordResult.val])
          (prim_natDiv hF hH hrun hC ho hsup hx hops hlive)
      | (exfalso; word_bad)
  case mod =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first
      | exact rhsSim_of_nat (nop := .natMod) (Rt.Proof.wordSem_nat_of rfl fun p q => by
          rw [sem_nat2 .natMod (by decide)]
          by_cases hq : q = 0 <;> simp [hq, WordOp.eval, Src.WordResult.val])
          (prim_natMod hF hH hrun hC ho hsup hx hops hlive)
      | (exfalso; word_bad)
  case land =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first
      | exact rhsSim_of_nat (nop := .natLand) (Rt.Proof.wordSem_nat_of rfl fun p q => by
          rw [sem_nat2 .natLand (by decide)]; rfl)
          (prim_natLand hF hH hrun hC ho hsup hx hops hlive)
      | (exfalso; word_bad)
  case lor =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first
      | exact rhsSim_of_nat (nop := .natLor) (Rt.Proof.wordSem_nat_of rfl fun p q => by
          rw [sem_nat2 .natLor (by decide)]; rfl)
          (prim_natLor hF hH hrun hC ho hsup hx hops hlive)
      | (exfalso; word_bad)
  case xor =>
    rcases las with _ | ⟨la, _ | ⟨lb, _ | ⟨lc, las⟩⟩⟩ <;>
      first
      | exact rhsSim_of_nat (nop := .natXor) (Rt.Proof.wordSem_nat_of rfl fun p q => by
          rw [sem_nat2 .natXor (by decide)]; rfl)
          (prim_natXor hF hH hrun hC ho hsup hx hops hlive)
      | (exfalso; word_bad)
  all_goals
    exact rhsSim_of_core hops hlive hx (Rt.Proof.word_not_bool _ _) (Rt.Proof.word_core hF hH hrun hC hl ho hsup rfl)

end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
