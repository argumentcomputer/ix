import IxCCGrounding.Facts
import IxCCGrounding.Laws

/-!
# Level agreement at `ordinary` recursors (`IxCCGrounding.RecLevels`), W-c step 1

At an `ordinary` recursor (parameters, no index) ι (`paramsBlindIota`) reads the major premise as
the constructor's image **at the levels the major premise's domain names** (`ls0`, over the
recursor's level parameters, read at the recursor's assignment `φ`). A SrcEval constructor value is
the image at the assignment `ψ` it was built at (`RelV.con`). Parameters need no agreement
(`paramsBlindIota` takes the constructor's own parameters); levels do, and no law gives it
(`plans/GROUNDING.md` §23): it is a fact about the run.

**The agreement, over the abstract `Ok`** (`RecLevelAgree`): at every `Ok` instance of the recursor
and every `Ok` instance of a constructor of its inductive, the constructor's levels are `ls0` read
at the recursor's levels. The F2 site sees both instances: `HeadAt.recr` records `Ok r ls`, and
`RelV.con` records `Ok c lsc` wherever the constructor has level parameters.

**The hypothesis the fundamental lemma takes** (`OrdLevels`): an `Ok` instance of the recursor has
its level count (the rule body's recursive call reads the recursor at its own levels), and one of
three sources of the constructor's image at `ls0`: canonicity (`CtorCanon`, the legacy laws), no
level parameter on the rules' constructors (`RecNoLevels`, `cval_params` alone), or the agreement.

**Decided on a verified instance set** (`instRecB`, `instUniformRec_of_check`): at every instance
of `Inst` of an `ordinary` recursor, every instance of `Inst` of a constructor of its inductive is
at `ls0` read at the recursor's instance, where `ls0` names only the recursor's level parameters
(Lean's recursors: the inductive's levels are a suffix of the recursor's). `recLevelAgree_of_mem`
moves it to any `Ok` contained in `Inst` (`OkIn`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-- **Level agreement at the `ordinary` recursor `r`, over the abstract `Ok`**: with `ls0` the
levels the stored recursor's major premise's domain names, at every `Ok` instance `ls` of `r` (read
at any `φ` giving `r`'s parameters those values) and every `Ok` instance `lsc` of a constructor of
`r`'s inductive, `lsc` is `ls0` read at `φ`. -/
def RecLevelAgree (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (Ok : CId → Levels → Prop) (r : CId) : Prop :=
  ∀ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term), p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
  ∀ (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)) (dom body : KExpr)
    (m : BinderMeta) (D : KKey) (ls0 : List Level),
    env.find? (κ r) = some (.recInfo cvr mI rP krules) → piBody mI cvr.type = .forallE dom body m →
    dom.getAppFn = .const D ls0 →
  ∀ (ls : Levels) (φ : LevelParam → Nat), Ok r ls → LvAt φ (lpsOf r) ls →
  ∀ (c : CId) (lsc : Levels) (sf' : Bool) (lv cidx np' nf : Nat) (ty' : Term),
    p.decl? c = some (.ctor sf' lv ind cidx np' nf ty') → Ok c lsc →
    lsc.length = ls0.length ∧
      ∀ (k : Nat) (l : Level), ls0[k]? = some l → lsc[k]? = some (Level.eval φ l)

/-- **What the fundamental lemma takes at an `ordinary` recursor `r`**: every `Ok` instance of `r`
has `r`'s level count, and the constructor's image at the major domain's levels comes from
canonicity, from the rules' constructors having no level parameter, or from level agreement. -/
def OrdLevels {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} (M : Model V env) (p : Program)
    (κ : CId → KKey) (lpsOf : CId → List Nat) (Ok : CId → Levels → Prop) (r : CId) : Prop :=
  (∀ ls, Ok r ls → ls.length = (lpsOf r).length) ∧
    (CtorCanon M ∨ RecNoLevels env (κ r) ∨ RecLevelAgree p env κ lpsOf Ok r)

/-- **Level uniformity at the `ordinary` recursors of `Inst`**: `RecLevelAgree` with membership in
`Inst` for `Ok`. -/
def InstUniformRec (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (Inst : List (CId × Levels)) : Prop :=
  ∀ r ls, (r, ls) ∈ Inst → recClassB p env κ r = some .ordinary →
  ∀ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term), p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
  ∀ (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)) (dom body : KExpr)
    (m : BinderMeta) (D : KKey) (ls0 : List Level),
    env.find? (κ r) = some (.recInfo cvr mI rP krules) → piBody mI cvr.type = .forallE dom body m →
    dom.getAppFn = .const D ls0 →
  ∀ (φ : LevelParam → Nat), LvAt φ (lpsOf r) ls →
  ∀ (c : CId) (lsc : Levels) (sf' : Bool) (lv cidx np' nf : Nat) (ty' : Term),
    p.decl? c = some (.ctor sf' lv ind cidx np' nf ty') → (c, lsc) ∈ Inst →
    lsc.length = ls0.length ∧
      ∀ (k : Nat) (l : Level), ls0[k]? = some l → lsc[k]? = some (Level.eval φ l)

/-- **Uniformity gives agreement at any `Ok` contained in `Inst`** (`OkIn p ann Inst`). -/
theorem recLevelAgree_of_mem {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {Inst : List (CId × Levels)} {Ok : CId → Levels → Prop}
    (hU : InstUniformRec p env κ lpsOf Inst) (hm : ∀ c ls, Ok c ls → (c, ls) ∈ Inst) {r : CId}
    (hk : recClassB p env κ r = some .ordinary) : RecLevelAgree p env κ lpsOf Ok r :=
  fun sf kk lvls np nmot nmin ni ind rules ty hd cvr mI rP krules dom body m D ls0 hf hpb hdom ls
      φ hOk hlv c lsc sf' lv cidx np' nf ty' hdc hOkc =>
    hU r ls (hm r ls hOk) hk sf kk lvls np nmot nmin ni ind rules ty hd cvr mI rP krules dom body m
      D ls0 hf hpb hdom φ hlv c lsc sf' lv cidx np' nf ty' hdc (hm c lsc hOkc)

/-! ## Decided -/

/-- `lsc` is `ls0` read at the concrete levels `ls` of the parameters `lps`, where each level of
`ls0` is a parameter of `lps`. -/
def levelsAtB (lps : List Nat) (ls : Levels) (ls0 : List Level) (lsc : Levels) : Bool :=
  lsc.length == ls0.length &&
    (List.range ls0.length).all fun k =>
      match ls0[k]? with
      | some (.param q) =>
        (List.range lps.length).any fun j => lps[j]? == some q && lsc[k]? == ls[j]?
      | _ => false

theorem levelsAt_of_check {lps : List Nat} {ls : Levels} {ls0 : List Level} {lsc : Levels}
    (h : levelsAtB lps ls ls0 lsc = true) {φ : LevelParam → Nat} (hlv : LvAt φ lps ls) :
    lsc.length = ls0.length ∧
      ∀ (k : Nat) (l : Level), ls0[k]? = some l → lsc[k]? = some (Level.eval φ l) := by
  simp only [levelsAtB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun k l hl => ?_⟩
  have hk : k < ls0.length := (List.getElem?_eq_some_iff.mp hl).1
  have h1 := hall k hk
  simp only [hl] at h1
  cases l with
  | param q =>
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨j, -, hq, he⟩ := h1
    have hkc : k < lsc.length := by omega
    rw [List.getElem?_eq_getElem hkc] at he ⊢
    simp only [Level.eval, hlv j q hq, List.getD_eq_getElem?_getD, ← he, Option.getD_some]
  | zero => simp at h1
  | succ _ => simp at h1
  | max _ _ => simp at h1
  | imax _ _ => simp at h1

/-- **`InstUniformRec`, decided**: per instance of an `ordinary` recursor, every constructor
instance of its inductive against `ls0` at the recursor's instance (`levelsAtB`). Quadratic in
`|Inst|`, as `instCheckB`'s `case` uniformity. -/
def instRecB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (Inst : List (CId × Levels)) : Bool :=
  Inst.all fun x =>
    match recClassB p env κ x.1 with
    | some .ordinary =>
      match p.decl? x.1, env.find? (κ x.1) with
      | some (.recr _ _ _ _ _ _ _ ind _ _), some (.recInfo cvr mI _ _) =>
        match piBody mI cvr.type with
        | .forallE dom _ _ =>
          match dom.getAppFn with
          | .const _ ls0 =>
            Inst.all fun y =>
              match p.decl? y.1 with
              | some (.ctor _ _ ind' _ _ _ _) => ind' != ind || levelsAtB (lpsOf x.1) x.2 ls0 y.2
              | _ => true
          | _ => false
        | _ => false
      | _, _ => false
    | _ => true

/-- **`instRecB` is sound.** -/
theorem instUniformRec_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {Inst : List (CId × Levels)}
    (h : instRecB p env κ lpsOf Inst = true) : InstUniformRec p env κ lpsOf Inst := by
  intro r ls hm hk sf kk lvls np nmot nmin ni ind rules ty hd cvr mI rP krules dom body m D ls0 hf
    hpb hdom φ hlv c lsc sf' lv cidx np' nf ty' hdc hmc
  have h1 := List.all_eq_true.mp h (r, ls) hm
  simp only [hk, hd, hf, hpb, hdom] at h1
  have h2 := List.all_eq_true.mp h1 (c, lsc) hmc
  simp only [hdc, bne_self_eq_false, Bool.false_or] at h2
  exact levelsAt_of_check h2 hlv

end IxCC.Grounding
