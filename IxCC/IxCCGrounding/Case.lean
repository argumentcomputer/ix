import IxCCGrounding.Tele
import IxCCGrounding.Heads

/-!
# The generic `case` lemma, model side (`IxCCGrounding.Case`)

**`caseIota`**: at a `case` constant whose stored value, type, recursor and constructors have
the checked shape (`CaseStored`), `casesOn` applied to arguments that fit its type, the last
applied at a graph-regime site, with the major the image of constructor `j` at the `case`'s own
parameters and levels, is minor `j` applied to the constructor's fields, along a graph-regime
chain. In every model with δ and ι, at every level assignment, with no typing hypothesis.

The proof follows the stored terms:

1. δ on `casesOn` (`Laws.defn_value`), β through its λ-telescope at the arguments, which fit its
   type (`lamTele_app`): `casesOn ps mo t mins` is `rec ps mo W₀ … W_{n-1} t`, the `Wⱼ` being
   what the wrappers denote;
2. the recursor's arguments fit its stored type: the parameters and the motive are `casesOn`'s,
   and each wrapper lies in its minor premise (`wrapper_mem`, by `lamTele_mem`): the wrapper's
   domains are the minor premise's (fields: both are lifts of the constructor's field domains;
   induction hypotheses: both are the motive at a field), and the body, minor `j` applied to the
   fields, lies in the codomain since minor `j` lies in `casesOn`'s minor premise, whose codomain
   does not mention the earlier minors (`CaseWF.codom`);
3. ι (`Laws.iota_rule`) on the major, constructor `j` at the `case`'s parameters and levels, and
   β through the rule's right-hand side: `rec ps mo Ws t = Wⱼ fields ihs`, the induction
   hypotheses being the recursor at the recursive fields;
4. β through the wrapper, which drops the induction hypotheses (each lies in its domain, the
   motive at its field, by `mem` of the recursor): `Wⱼ fields ihs = minorⱼ fields`;
5. the chain: minor `j` lies in `casesOn`'s minor premise, whose field binders carry the last
   binder's zero-ness datum (`CaseWF.regime`), read in the graph regime at the saturating site
   (`last_regime`).

The major's fields must number the constructor's (`Fs.length = cs.nF`): with fewer, ι does not
apply, and the conclusion can fail (at `And.casesOn` the major proof point is also `And.intro`
applied to its two parameters alone).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-! ## Syntax -/

/-- A list of length `n + 2 + m` splits around two elements. -/
theorem split_ctx {α : Type _} (l : List α) (n m : Nat) (h : l.length = n + 2 + m) :
    ∃ a x y b, l = a ++ x :: y :: b ∧ a.length = n ∧ b.length = m := by
  have hd : (l.drop n).length = m + 2 := by simp; omega
  match hdl : l.drop n, hd with
  | x :: y :: b, hd =>
    exact ⟨l.take n, x, y, b, by rw [← hdl, List.take_append_drop], by simp; omega,
      by simpa using hd⟩
  | [], hd => simp at hd
  | [_], hd => simp at hd

theorem lift_zero (c : Nat) (e : KExpr) : e.liftLooseBVars 0 c = e := by
  induction e generalizing c with
  | bvar i => simp only [Expr.liftLooseBVars, Nat.add_zero]; split <;> rfl
  | fvar _ _ _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp [Expr.liftLooseBVars, ihf, iha]
  | lam t b m iht ihb => simp [Expr.liftLooseBVars, iht, ihb]
  | forallE t b m iht ihb => simp [Expr.liftLooseBVars, iht, ihb]
  | letE t v b l iht ihv ihb => simp [Expr.liftLooseBVars, iht, ihv, ihb]
  | lit _ => rfl
  | proj s i e ih => simp [Expr.liftLooseBVars, ih]

theorem liftTele_zero : ∀ (c : Nat) (bs : List (KExpr × BinderMeta)), liftTele 0 c bs = bs
  | _, [] => rfl
  | c, (A, m) :: bs => by simp [liftTele, lift_zero, liftTele_zero (c + 1) bs]

theorem map_fst_get {bs : List (KExpr × BinderMeta)} {n : Nat} {A : KExpr}
    (h : bs[n]?.map (·.1) = some A) (f : KExpr → KExpr) :
    bs[n]?.map (fun b => f b.1) = some (f A) := by
  cases hb : bs[n]? with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h ⊢; rw [h]

theorem get_of_map_fst {bs : List (KExpr × BinderMeta)} {n : Nat} {A : KExpr}
    (h : bs[n]?.map (·.1) = some A) : ∃ m, bs[n]? = some (A, m) := by
  cases hb : bs[n]? with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨b.2, by rw [← h]⟩

/-- A minor premise's field domain `n` is the constructor's, lifted past the motive and the minors
before it. -/
theorem field_lift {fbs fields : List (KExpr × BinderMeta)} {j n : Nat} {AP : KExpr}
    (hf : (liftTele (j + 1) 0 fbs).map (·.1) = fields.map (·.1))
    (hP : fbs[n]?.map (·.1) = some AP) :
    fields[n]?.map (·.1) = some (AP.liftLooseBVars (j + 1) n) := by
  have h1 := congrArg (·[n]?) hf
  simp only [List.getElem?_map] at h1
  rw [← h1, liftTele_get, Nat.zero_add]
  exact map_fst_get hP _

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}
  {φ : LevelParam → Nat}

/-- **A field domain, wherever the minor premise is read**: lifted by `k'` above `j` and read
under the parameters, a block of `j + 1 + k'` sets and the earlier fields, it denotes what the
constructor's field domain denotes under the parameters and the earlier fields. -/
theorem fieldDom_iff {fbs fields : List (KExpr × BinderMeta)} {j k' : Nat}
    (hf : (liftTele (j + 1) 0 fbs).map (·.1) = fields.map (·.1)) {ps junk ys : List V}
    {ρ : BVarIdx → V} (hj : junk.length = j + 1 + k') {AL AP : KExpr}
    (hL : (liftTele k' j fields)[ys.length]?.map (·.1) = some AL)
    (hP : fbs[ys.length]?.map (·.1) = some AP) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ junk) ρ)) AL X ↔
      Denotes M.cval env φ (pushAll ys (pushAll ps ρ)) AP X := by
  have hF := field_lift hf hP
  rw [liftTele_get] at hL
  have h2 := hL.symm.trans (map_fst_get hF fun A => A.liftLooseBVars k' (j + ys.length))
  obtain rfl := Option.some.inj h2
  rw [← pushAll_append, ← pushAll_append, den_lift2 hj]

theorem den_app_bvars {ρ : BVarIdx → V} {a b : Nat} {X : V} :
    Denotes M.cval env φ ρ (.app (.bvar a) (.bvar b)) X ↔ X = app (ρ a) (ρ b) := by
  rw [den_app]
  constructor
  · rintro ⟨F, A, hF, hA, rfl⟩; rw [den_bvar.mp hF, den_bvar.mp hA]
  · rintro rfl; exact ⟨_, _, .bvar, .bvar, rfl⟩

/-! ## The context of a `case` constant's arguments

`ps`, `mo`, `t`, `mins` are `casesOn`'s arguments (parameters, motive, major, minors); `Ws` what the
wrappers denote. The environments: `casesOn`'s body (`pushAll (ps ++ mo :: t :: mins) ρ`), the
recursor's type at minor premise `j` (`pushAll (ps ++ [mo] ++ Ws.take j) ρ`), `casesOn`'s type at
minor `j` (`pushAll (ps ++ [mo, t] ++ mins.take j) ρ`), the constructor's type after its parameters
(`pushAll ps ρ`). -/

section Wrapper

variable {sh : CaseShape} {j : Nat} {cs : CtorShape} {fbs : List (KExpr × BinderMeta)}
  {ps mins Ws : List V} {mo t : V} {ρ : BVarIdx → V}

/-- The induction hypothesis domain `r` of minor premise `j`, read under the recursor's
arguments up to the minor or under `casesOn`'s (lifted past the major and the later minors),
denotes the motive at the recursive field. -/
theorem ihDom_den {pre : List V} (hpre : pre.length = j) {ys : List V} {r rf : Nat}
    (hys : ys.length = cs.nF + r) (hrf : rf < cs.nF) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ [mo] ++ pre) ρ)) (cs.ihDom j r rf) X ↔
      X = app mo (pushAll ys ρ (r + cs.nF - 1 - rf)) := by
  rw [CtorShape.ihDom, den_app_bvars, show r + cs.nF + j = pre.length + ys.length by omega,
    pushAll_offset, show ps ++ [mo] ++ pre = ps ++ mo :: pre by simp, pushAll_at,
    pushAll_lt (E' := ρ) (by omega : r + cs.nF - 1 - rf < ys.length)]

theorem ihDomL_den (hj : j < mins.length) {ys : List V} {r rf : Nat} (hys : ys.length = cs.nF + r)
    (hrf : rf < cs.nF) {X : V} :
    Denotes M.cval env φ (pushAll ys (pushAll (ps ++ mo :: t :: mins) ρ))
        ((cs.ihDom j r rf).liftLooseBVars (mins.length + 1 - j) (j + cs.nF + r)) X ↔
      X = app mo (pushAll ys ρ (r + cs.nF - 1 - rf)) := by
  have h1 : r + cs.nF + j ≥ j + cs.nF + r := by omega
  have h2 : ¬ r + cs.nF - 1 - rf ≥ j + cs.nF + r := by omega
  simp only [CtorShape.ihDom, Expr.liftLooseBVars, h1, h2, ↓reduceIte]
  rw [den_app_bvars,
    show r + cs.nF + j + (mins.length + 1 - j) = (t :: mins).length + ys.length by simp; omega,
    pushAll_offset, pushAll_at, pushAll_lt (E' := ρ) (by omega : r + cs.nF - 1 - rf < ys.length)]

end Wrapper

end IxCC.Grounding
