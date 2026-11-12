import IxCCGrounding.Apply
import IxCCGrounding.Lits

/-!
# Special heads (`IxCCGrounding.Heads`)

Model-side lemmas the fundamental lemma's cases reduce to.

* **The regime of the binder a graph-regime site fills** (`last_regime`): F5 reads the motive's
  universe off the site that saturated the `case` head.
* **E6 projection of a constructor** (`proj_con`): the value-form law `proj_ctor`.
* **F6 a binary `Nat` primitive** (`prim_fire_nat`): the law `nat_accel`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **The regime of the binder a graph-regime site fills is not `0`**: arguments that fit a
telescope up to `∀ D, Bk` (datum `m`), applied to a member of its denotation, give a member of a
graph-regime product only if `m` is not read in regime `0`. -/
theorem last_regime {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ σ : BVarIdx → V} {T D Bk : KExpr} {m : BinderMeta} {xs : List V} {H TT : V}
    (hfit : Fits cval env φ ρ T xs σ (.forallE D Bk m)) (hT : Denotes cval env φ ρ T TT)
    (hH : H ∈ˢ TT) {v : Nat} {A : V} {B : V → V} (hv : v ≠ 0)
    (hX : xs.foldl app H ∈ˢ piR v A B) : regime φ m.pw ≠ 0 := by
  obtain ⟨RR, hRR, hXm⟩ := fits_app_mem hfit hT hH
  obtain ⟨DD, BB, _, _, _, rfl⟩ := den_pi.mp hRR
  intro h0
  rw [h0] at hXm
  rw [eq_pt_of_mem_piR_zero hXm] at hX
  exact not_pt_mem_piR_pos hv hX

/-- **E6, the projection of a constructor value**: what the projection node denotes is the
field, by `proj_ctor`, when the structure's table entry names the constructor and the
constructor's parameters and fields fit its stored type, at a structure that is never a
proposition (`NeverProp`, checked by the `proj` conjunct). -/
theorem proj_con (M : Model V env) (hL : LawsCore M) {Ts : KKey} {i : Nat}
    {entry : ProjEntry .anon} (hent : env.findProj? Ts i = some entry)
    {cvC : ConstantVal .anon} {np nf : Nat} (hc : env.find? entry.ctor = some (.ctorInfo cvC np nf))
    (hTs : NeverProp env Ts)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {Ps Fs : List V}
    (hP : Ps.length = np) (hFl : Fs.length = nf) (hfit : Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R)
    {Y : V} (hY : Fs[i]? = some Y) {φ0 : LevelParam → Nat} {ρ0 : BVarIdx → V} {e : KExpr}
    (he : Denotes M.cval env φ0 ρ0 e ((Ps ++ Fs).foldl app (M.cval entry.ctor φ))) :
    Denotes M.cval env φ0 ρ0 (.proj Ts i e) Y := by
  obtain ⟨cvT, caps, s, hfT, hs, hnv⟩ := hTs
  have h := Denotes.proj_table hent he
  -- `proj_ctor` in a proof-irrelevant set model: the structure's sort is not zero at `φ`, so its
  -- constructor is read in the graph regime and its image is the field tuple (after `off` tag
  -- positions); at a proposition the image would be `pt`, whose components are all `pt`.
  rwa [hL.proj_ctor Ts i entry cvC np nf cvT caps s φ ρ σ R Ps Fs Y hent hc hfT hs
    (eval_ne_zero_of_never hnv φ) hP hFl hfit hY] at h

/-- **F6, a binary `Nat` primitive with a `Nat` result**, on literal arguments: the operation's
denotation applied to the literals' is the result literal's, by `nat_accel`. -/
theorem prim_fire_nat (M : Model V env) (hL : LawsCore M) (hS : NatBasis env)
    {op : IxCC.Src.PrimOp} (hop : op.arity = 2) {ci : ConstantInfo .anon}
    (hf : env.find? (primKey op) = some ci) (hl : ci.toConstantVal.levelParams = [])
    (φ : LevelParam → Nat) {a b n : Nat} (hev : op.eval2 a b = .nat n) :
    app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ n := by
  have hF := natFacts M hS φ
  have hden : Denotes M.cval env φ (fun _ => empty) (primApp op a b)
      (app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b)) := by
    have h1 : primApp (md := .anon) op a b =
        .app (.app (.const (primKey op) []) (litE a)) (litE b) := by
      simp [primApp, hop]
    rw [h1]
    exact .app (.app ((den_const0 hf hl).mpr rfl) ((lit_den M hF _ a _).mpr rfl))
      ((lit_den M hF _ b _).mpr rfl)
  have h2 := hL.nat_accel op a b φ _ _ (fun h => by rw [hop] at h; cases h) hden
  rw [hev] at h2
  exact (lit_den M hF _ n _).mp h2

end IxCC.Grounding
