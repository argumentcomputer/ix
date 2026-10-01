module

import ConLeche.Model.Inductives.StructCtorFrames
public import ConLeche.Model.Inductives.SumIntro
public import ConLeche.Model.Inductives.SumRecRead
public import ConLeche.Verify.Inductives.SumInv
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The direct sum's constructor data and frames (task #175 sum-types,
indexed)

`CtorDataI`: `CtorData` at an indexed family — the constructor's type
reads to the Π-tower over its field data ending in the family at the
parameter variables and the **index readings** `Es` (the readings of
the residual's index expressions at the constructor's own frame), and
the field **sources** `srcs` (per field: the index position the field
literally is, or none — the squash-regime recursor body applies its
minor to the sources; a field without a source at a large-eliminating
`Prop` family is propositional, `FieldsBoundSrc`).  `sumCtorData_of`
reads them off `checkSumCtor`'s run (the residual `T p⃗ e⃗` at
the opened frame, its spine inverted), and `sumCtorFrames` gives the
constructor's frames: the parameter frames identified, the field
chain graded, the index expressions graded and **fitting the former's
index telescope** — read off the residual's own grading
(`spineFit_of_wellDenoted_lams`: an application spine graded against a
λ-tower fits the tower's domains, since a graph determines its
domain).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- The arguments of a bounded spine are bounded. -/
theorem bvarsBelow_mkAppN_inv {k : Nat} :
    ∀ {as : List Term} {f : Term}, Term.bvarsBelow k (Term.mkAppN f as) →
      Term.bvarsBelow k f ∧ ∀ a ∈ as, Term.bvarsBelow k a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨hf, hall⟩ := bvarsBelow_mkAppN_inv (as := as) (f := .app f a) h
    exact ⟨hf.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hf.2
      · exact hall a' ha'⟩

/-- The head and the arguments of a graded spine are graded. -/
theorem WellDenoted.mkAppN_inv {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      WellDenoted V ρ f ∧ ∀ a ∈ args, WellDenoted V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := WellDenoted.mkAppN_inv h
    rw [WellDenoted_app] at hfa
    exact ⟨hfa.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hfa.2.1
      · exact hall a' ha'⟩

/-- Equal graphs have equal domains. -/
theorem graph_eq_dom {F G : V → V} {A D : V} (h : graph F A = graph G D) : A = D := by
  apply SetTheory.ext
  intro x
  constructor
  · intro hx
    have : kpair x (F x) ∈ˢ graph G D := h ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'
  · intro hx
    have : kpair x (G x) ∈ˢ graph F A := h.symm ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp this
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'

/-- A graph-regime abstraction in a product has the product's
domain. -/
theorem lamR_mem_piR_dom {u v : Nat} (hu : u ≠ 0) {A D : V} {F B : V → V}
    (h : lamR u D F ∈ˢ piR v A B) : A = D := by
  by_cases hv : v = 0
  · subst hv
    rw [piR_zero] at h
    exact absurd (eq_pt_of_mem_truthVal h) (lamR_ne_pt hu)
  · have h1 := (mem_piR_pos hv h).1
    rw [lamR_pos hu] at h1
    exact graph_eq_dom h1

/-- **A spine graded against a constant-bit λ-tower fits its
domains** (graph regime): each application node's product has the
abstraction's domain. -/
theorem spineFit_of_wellDenoted_lams {u : Nat} (hu : u ≠ 0) {b : AnnotTerm} :
    ∀ {args : List AnnotTerm} {ds : List (Nat × Nat × AnnotTerm)} {σ ρ : Nat → V} {f : AnnotTerm},
      args.length ≤ ds.length →
      WellDenoted V ρ (AnnotTerm.mkAppN f args) →
      interp V ρ f = interp V σ (mkLamsC u ds b) →
      SpineFit σ ((ds.take args.length).map (·.2.2)) (args.map (interp V ρ))
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | a :: args, d :: ds, σ, ρ, f, hlen, hok, hf => by
    rw [AnnotTerm.mkAppN_cons] at hok
    have hokfa : WellDenoted V ρ (.app f a) := (WellDenoted.mkAppN_inv hok).1
    rw [WellDenoted_app] at hokfa
    obtain ⟨-, -, v, A, B, hfm, ham, -⟩ := hokfa
    have hf' : interp V ρ f
        = lamR u (interp V σ d.2.2) fun x => interp V (cons x σ) (mkLamsC u ds b) := by
      rw [hf]; rfl
    rw [hf'] at hfm
    have hA : A = interp V σ d.2.2 := lamR_mem_piR_dom hu hfm
    rw [hA] at ham
    have happ : interp V ρ (.app f a) = interp V (cons (interp V ρ a) σ) (mkLamsC u ds b) := by
      rw [interp_app, hf', app_lamR_pos hu ham]
    have ih := spineFit_of_wellDenoted_lams hu (args := args) (ds := ds) (σ := cons (interp V ρ a) σ)
      (ρ := ρ) (f := .app f a) (by simpa using hlen) hok happ
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, SpineFit]
    exact ⟨ham, ih⟩

theorem DenoteMetaSpine.getElem? {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      ∀ {l : Nat} {a : Expr}, as[l]? = some a →
        ∃ v, vs[l]? = some v ∧ denoteMeta acval env φ d a = some v
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons ha htl, l, a, h => by
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, ha⟩
    | succ l =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact DenoteMetaSpine.getElem? htl h

/-- A read spine crosses a cons its terms do not mention. -/
theorem DenoteMetaSpine.cons_mono {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} (hfresh : env.find? c₀.name = none)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) {ψ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ a ∈ as, ConstsBound env a) →
      DenoteMetaSpine acval env ψ d as vs →
      DenoteMetaSpine (acvalWith acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hcb, .cons ha htl =>
    .cons (denoteMeta_cons_mono hfresh (hat a) ψ d (hcb a List.mem_cons_self) ha)
      (DenoteMetaSpine.cons_mono hfresh hat (fun a' ha' => hcb a' (List.mem_cons_of_mem _ ha')) htl)

omit [SetTheory V] in
/-- A valuation agreeing with the parameters below `nP`. -/
theorem consList_params_apply {nP : Nat} (ρ X : Nat → V) {i : Nat} (hi : i < nP) :
    consList ((List.range nP).reverse.map ρ) X i = ρ i := by
  have hlt : ((List.range nP).reverse.map ρ).length - 1 - i < ((List.range nP).reverse.map ρ).length := by
    simp; omega
  have h1 := consList_apply_lt ((List.range nP).reverse.map ρ) X i (by simpa using hi)
  have h2 := consList_apply_lt ((List.range nP).reverse.map ρ) (fun j => ρ (j + nP)) i
    (by simpa using hi)
  rw [consList_range_reverse] at h2
  rw [List.getElem?_eq_getElem hlt, Option.getD_some] at h1 h2
  rw [h1, h2]

/-! ## The field sources -/

/-- The first position of an expression in a list. -/
def firstIdx (x : Expr) : List Expr → Option Nat
  | [] => none
  | a :: as => if a = x then some 0 else (firstIdx x as).map (· + 1)

theorem firstIdx_some : ∀ {l : List Expr} {x : Expr} {i : Nat},
    firstIdx x l = some i → l[i]? = some x
  | [], _, _, h => by simp [firstIdx] at h
  | a :: as, x, i, h => by
    simp only [firstIdx] at h
    split at h
    · next hax =>
      obtain rfl := Option.some.inj h
      simp [hax]
    · obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using firstIdx_some hi'

theorem firstIdx_of_mem : ∀ {l : List Expr} {x : Expr}, x ∈ l → ∃ i, firstIdx x l = some i
  | [], _, h => nomatch h
  | a :: as, x, h => by
    simp only [firstIdx]
    by_cases hax : a = x
    · exact ⟨0, by rw [if_pos hax]⟩
    · rw [if_neg hax]
      obtain ⟨i, hi⟩ := firstIdx_of_mem (l := as) (x := x)
        (by rcases List.mem_cons.mp h with rfl | h'; exact absurd rfl hax; exact h')
      exact ⟨i + 1, by rw [hi]; rfl⟩

/-- The sources of the fields: a field whose sort is `Prop` is a proof
(`none`); otherwise the first index position the field variable
occupies. -/
def srcsOf (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map fun j =>
    if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
    else firstIdx (xFvs.getD j default) idxArgs

theorem srcsOf_length (xFvs idxArgs : List Expr) (sorts : List Level) (nF : Nat) :
    (srcsOf xFvs idxArgs sorts nF).length = nF := by simp [srcsOf]

theorem srcsOf_getElem? (xFvs idxArgs : List Expr) (sorts : List Level) (nF j : Nat) (hj : j < nF) :
    (srcsOf xFvs idxArgs sorts nF)[j]?
      = some (if (Level.isEquiv (sorts.getD j .zero) .zero == some true) = true then none
          else firstIdx (xFvs.getD j default) idxArgs) := by
  simp [srcsOf, hj]

/-- The fields not sourced by an index are propositions: each such
field's domain is a truth value, hereditarily. -/
@[expose] def FieldsBoundSrc (ρ : Nat → V) : List AnnotTerm → List (Option Nat) → Prop
  | [], _ => True
  | _ :: _, [] => True
  | F :: Fs, s :: ss => (s = none → interp V ρ F ∈ˢ (univ 0 : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBoundSrc (cons a ρ) Fs ss

/-- `fieldsBound_of_frame` at the sourced fields. -/
theorem fieldsBoundSrc_of_frame {Γ : List AnnotTerm} {k nP nF : Nat} {srcs : List (Option Nat)}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → srcs[j]? = some none → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ 0 : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBoundSrc ρ (fieldsFrom Γ k nP nF j) (srcs.drop j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    cases hs : srcs.drop j with
    | nil => trivial
    | cons s ss =>
      have hsj : srcs[j]? = some s := by
        have := congrArg (·[0]?) hs
        simpa [List.getElem?_drop] using this
      have hss : srcs.drop (j + 1) = ss := by
        rw [← List.drop_drop, hs]
        rfl
      refine ⟨fun hsn => hbnd j hlt (hsn ▸ hsj) ρ hρ, fun a ha => ?_⟩
      rw [← hss]
      refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
      rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
      have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
        rw [List.getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
      exact Sat_cons V hρ ha

/-! ## The constructor's data -/

/-- The family at the parameter variables and the index readings,
read at the constructor's full frame. -/
@[expose] def ctorBodyAVI {env : Env} (m : EnvModel V env) (T : Name) (nP nF : Nat)
    (ψ : Name → Nat) (Es : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)

/-- **A constructor's data at an indexed family**: its stored type
reads to the Π-tower over `ds ψ` ending in the family at the
parameters and the index readings `Es ψ`; the index readings read the
residual's index expressions `idxArgs` at the constructor's frame; the
sources `srcs` name, per field, the index it literally is, and at a
large-eliminating `Prop` family the other fields are
propositional. -/
structure CtorDataI {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name)
    (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) : Prop where
  resid : ∃ (cbs : List (Expr × BinderMeta)) (es : List Expr),
    cvC.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
    es.length = nIdx
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  lenE : ∀ ψ : Name → Nat, (Es ψ).length = nIdx
  idxLen : idxArgs.length = nIdx
  idxRead : ∀ ψ : Name → Nat, DenoteMetaSpine m.acval env ψ (nP + nF) idxArgs (Es ψ)
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ ds ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  belowE : ∀ ψ : Name → Nat, ∀ E ∈ Es ψ, Term.bvarsBelow (nP + nF) E.erase
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) →
    ds ψ₁ = ds ψ₂ ∧ Es ψ₁ = Es ψ₂
  srcLen : srcs.length = nF
  srcBnd : ∀ s ∈ srcs, ∀ l, s = some l → l < nIdx
  srcIdx : ∀ j l, srcs[j]? = some (some l) → ∀ ψ : Name → Nat,
    (Es ψ)[l]? = some (AnnotTerm.bvar (nF - 1 - j))
  srcProp : large = true → ∀ ψ : Name → Nat, resSort.eval ψ = 0 → ∀ ρ : Nat → V,
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    FieldsBoundSrc ρ (((ds ψ).drop nP).map (·.2.2)) srcs

/-- The data crosses a cons whose head is neither the former nor
mentioned. -/
theorem CtorDataI.cross {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env cvC.type)
    (hcbI : ∀ e ∈ idxArgs, ConstsBound env e)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  have hbody : ∀ ψ, ctorBodyAVI m₂ T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ
    unfold ctorBodyAVI
    rw [hac, acvalWith_ne hT]
  refine ⟨h.resid, fun ψ => ?_, h.len, h.lenE, h.idxLen, fun ψ => ?_, h.bits,
    fun ψ ρ => ?_, h.below, h.belowE, h.params, h.srcLen, h.srcBnd, h.srcIdx, h.srcProp⟩
  · rw [hac, hbody]
    exact denoteMeta_cons_mono hfresh (hat _) ψ 0 hcb (h.read ψ)
  · rw [hac]
    exact DenoteMetaSpine.cons_mono hfresh hat hcbI (h.idxRead ψ)
  · rw [hbody]; exact h.okTy ψ ρ

/-- A read spine of terms not mentioning a constant reads alike at
either valuation of it. -/
theorem DenoteMetaSpine.acvalWith_congr {acval : Name → (Name → Nat) → AnnotTerm} {T' : Name}
    {A₁ A₂ : (Name → Nat) → AnnotTerm} {env₀ : Env} (hfresh : env₀.find? T' = none)
    {ψ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ e ∈ as, e.constsResolve env₀ = true) →
      DenoteMetaSpine (acvalWith acval T' A₁) env ψ d as vs →
      DenoteMetaSpine (acvalWith acval T' A₂) env ψ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hres, .cons ha htl =>
    .cons (by
        rw [← denoteMeta_acvalWith_unmentioned₂ (A₁ := A₁) (A₂ := A₂) hfresh _ _
          (hres a List.mem_cons_self)]
        exact ha)
      (DenoteMetaSpine.acvalWith_congr hfresh (fun e he => hres e (List.mem_cons_of_mem _ he)) htl)

/-- The index readings of two data at the same residual agree across
carriers that differ only at an unmentioned constant. -/
theorem CtorDataI.Es_eq {env : Env} {acval : Name → (Name → Nat) → AnnotTerm} {T T' : Name}
    {A₁ A₂ : (Name → Nat) → AnnotTerm} {env₀ : Env}
    {m₁ m₂ : EnvModel V env} (hac₁ : m₁.acval = acvalWith acval T' A₁)
    (hac₂ : m₂.acval = acvalWith acval T' A₂) (hfresh : env₀.find? T' = none)
    {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds₁ ds₂ : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es₁ Es₂ : (Name → Nat) → List AnnotTerm}
    {srcs₁ srcs₂ : List (Option Nat)}
    (h₁ : CtorDataI m₁ T lps cvC nP nF nIdx resSort isProp large idxArgs ds₁ Es₁ srcs₁)
    (h₂ : CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds₂ Es₂ srcs₂)
    (hres : ∀ e ∈ idxArgs, e.constsResolve env₀ = true) (ψ : Name → Nat) :
    Es₁ ψ = Es₂ ψ := by
  have hsp₁ := h₁.idxRead ψ
  have hsp₂ := h₂.idxRead ψ
  rw [hac₁] at hsp₁
  rw [hac₂] at hsp₂
  exact DenoteMetaSpine.unique (DenoteMetaSpine.acvalWith_congr hfresh hres hsp₁) hsp₂

/-- The constructor's data, from its stage run at the environment
holding the former. -/
theorem sumCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {bs : List (Expr × ConLeche.BinderMeta)}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort)) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat)),
      (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        idxArgs = xrest.getAppArgs.drop nP) ∧
      CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  obtain ⟨⟨_, hccv⟩, hresid, fvsP, crest, tfvs, trest, xFvs, idxArgs, hopC, -, -, hopX, hlenI,
    -, hres, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', -, hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hopC hresid
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP type' 0 hopC
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ idxArgs) hib
  obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : ConLeche.inferTypeCore μ env F' (nP + nF)
      (.const T (lps.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ idxArgs) htfT
    (by rw [List.length_append, hlenP, hlenI]; exact hstripT) hib
  have hvb := ensureSortCore_sort_eq hensb
  rw [hvb] at hbits
  -- the per-assignment reading
  have hper : ∀ ψ : Name → Nat, ∃ (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type'
        = some (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es)) ∧
      ds.length = nP + nF ∧ Es.length = nIdx ∧
      DenoteMetaSpine mp.base2.acval env ψ (nP + nF) idxArgs Es ∧
      (∀ d ∈ ds, (resSort.eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es))) ∧
      DomsBelow 0 ds ∧ (∀ E ∈ Es, Term.bvarsBelow (nP + nF) E.erase) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hopAll htf' hbt' hTa hokT'
    -- the residual's spine, inverted
    obtain ⟨fa, vs, hfa, hsp, hR⟩ := denoteMeta_mkAppN_inv hop'.body
    have hfa' : fa = mp.base2.acval T ψ := by
      have hconst := denoteMeta_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := nP + nF) hfT
        (show (lps.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (lps.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (lps.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (lps.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hconst, hsubst] at hfa
      exact (Option.some.inj hfa).symm
    subst hfa'
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hvs₁ : vs₁ = paramBvars nP nF := by
      have := DenoteMetaSpine.unique hsp₁
        (denoteMetaSpine_indexed (acval := mp.base2.acval) (env := env) (φ := ψ) (d := nP + nF)
          fvsP 0 hidx)
      rw [this, hlenP]
      unfold paramBvars
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    subst hvs₁
    have hR' : R = ctorBodyAVI mp.base2 T nP nF ψ vs₂ := hR
    subst hR'
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    have hbelowAll := stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)
    refine ⟨ds, vs₂, hTa, hlen, by rw [← hsp₂.length, hlenI], hsp₂, ?_, hokT', hbelowAll.1, ?_⟩
    · intro d hd
      exact (stripPisAV_bits (nP + nF) (hbits ψ) hTa hst' d hd).symm
    · intro E hE
      have hb := hbelowAll.2
      rw [Nat.zero_add] at hb
      unfold ctorBodyAVI at hb
      rw [AnnotTerm.erase_mkAppN] at hb
      exact (bvarsBelow_mkAppN_inv hb).2 _
        (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
  -- the sources
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hspec : ∀ ψ, _ := fun ψ => Classical.choose_spec (Classical.choose_spec (hper ψ))
  refine ⟨idxArgs, fun ψ => Classical.choose (hper ψ),
    fun ψ => Classical.choose (Classical.choose_spec (hper ψ)),
    srcsOf xFvs idxArgs sorts nF, hres, ⟨fvsP, crest, xFvs, _, hopC, hopX, ?_⟩, ?_⟩
  · rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' hlenP]
  refine ⟨hresid, fun ψ => (hspec ψ).1, fun ψ => (hspec ψ).2.1, fun ψ => (hspec ψ).2.2.1,
    hlenI, fun ψ => (hspec ψ).2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.2.2, ?_,
    srcsOf_length _ _ _ _, ?_, ?_, ?_⟩
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have h2 := (hspec ψ₂).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAVI mp.base2 T nP nF ψ₁ (Classical.choose (Classical.choose_spec (hper ψ₁))))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 type' htp']
      exact (hspec ψ₁).1
    obtain ⟨hds, hbody⟩ := mkPisAV_inj
      (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1]) (Option.some.inj (h1.symm.trans h2))
    refine ⟨hds, ?_⟩
    obtain ⟨-, hargs⟩ := mkAppN_inj_args (f := mp.base2.acval T ψ₁) (g := mp.base2.acval T ψ₂) hbody
      (by rw [List.length_append, List.length_append, (hspec ψ₁).2.2.1, (hspec ψ₂).2.2.1])
    exact List.append_cancel_left hargs
  · -- the sources are index positions
    intro s hs l hsl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hj
    have hj' := Option.some.inj hj
    rw [hsl] at hj'
    split at hj'
    · exact nomatch hj'
    · have := firstIdx_some hj'
      rw [← hlenI]
      exact (List.getElem?_eq_some_iff.mp this).1
  · -- an index source reads to the field variable
    intro j l hjl ψ
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hjl).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hjl
    have hjl' := Option.some.inj hjl
    split at hjl'
    · exact nomatch hjl'
    · have hidxl := firstIdx_some hjl'
      obtain ⟨fv, hfv⟩ : ∃ fv, xFvs[j]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := hidxX j fv hfv
      rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some] at hidxl
      obtain ⟨v, hv, hread⟩ := DenoteMetaSpine.getElem? ((hspec ψ).2.2.2.1) hidxl
      rw [denoteMeta_fvar, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega] at hread
      rw [hv, Option.some.inj hread]
  · -- the unsourced fields are propositional at a large-eliminating
    -- family instantiated at `Prop`
    intro hl ψ hw0 ρ hρ
    have hc := claimsAt_of hμ mp ψ F
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs))
        (((Classical.choose (hper ψ)).map (·.2.2)).reverse)
        (ctorBodyAVI mp.base2 T nP nF ψ (Classical.choose (Classical.choose_spec (hper ψ)))) :=
      opened_of_peel hopAll htf' hbt' (hspec ψ).1 (hspec ψ).2.1 (hspec ψ).2.2.2.2.2.1
    have hlenDs : (Classical.choose (hper ψ)).length = nP + nF := (hspec ψ).2.1
    have hΓlen : ((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).length = nP + nF := by
      rw [List.length_reverse, List.length_map, hlenDs]
    have hρ' : Sat V (((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := Classical.choose (hper ψ)) (nP := nP) (nF := nF) hlenDs
    rw [← hFsEq]
    have h := fieldsBoundSrc_of_frame (Γ := ((Classical.choose (hper ψ)).map (·.2.2)).reverse)
      (srcs := srcsOf xFvs idxArgs sorts nF) rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
    · rw [List.drop_zero] at h; exact h
    intro j hj hsj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
    have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
    have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hC.doms (nP + j) fv hfvA
    have hmem := (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    -- the source is `none`: the sort evaluates to `0`
    have hu0 : u.eval ψ = 0 := by
      cases hp : isProp with
      | false =>
        have hle := Level.leq_sound (hleq hp) ψ
        omega
      | true =>
        rw [srcsOf_getElem? _ _ _ _ _ hj] at hsj
        have hsj' := Option.some.inj hsj
        have hsu : sorts.getD j .zero = u := by
          rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
        rw [hsu] at hsj'
        split at hsj'
        · next hequ => exact Level.isEquiv_sound (beq_iff_eq.mp hequ) ψ
        · rcases hz hp hl with h | h
          · exact Level.isEquiv_sound (beq_iff_eq.mp h) ψ
          · exfalso
            have hfvx : xFvs.getD j default = fv := by
              rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some]
            rw [hfvx] at hsj'
            obtain ⟨i, hi'⟩ := firstIdx_of_mem (List.contains_iff_mem.mp h)
            rw [hi'] at hsj'
            exact nomatch hsj'
    rw [hu0] at hmem
    exact hmem

/-! ## The constructor's frames -/

/-- **The constructor's frames**: the parameter frames identified, and
under the parameters the field chain graded (at the block's level),
bit-valid, bounded when the family is not `Prop`, and the index
expressions graded and fitting the former's index telescope at every
fitting field spine. -/
theorem ctorFramesGen (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
    -- the fields' sorts, as the stage read them (task #210 Part A: the
    -- projection table's guard levels at a structure-like block): one
    -- per field, each bounded by the result sort at a non-`Prop` family,
    -- and the field's reading along a fitting prefix a member of its
    -- sort's universe
    (sorts.length = nF ∧
      (∀ j, j < nF → isProp = false → Level.leq (sorts.getD j .zero) resSort = some true) ∧
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
  obtain ⟨⟨_, hccv⟩, -, fvsP, crest, tfvs, trest, xFvs, idxArgs', hopC, hopT, hdoms, hopX,
    -, -, -, hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopC hsorts
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hpins := ConLeche.checkStructDomsAt_inv hdoms
  have hlenX : xFvs.length = nF := openPisAtFvars_length _ hopX
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
          (∀ E ∈ Es ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))) ∧
      (∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    -- the former, opened at the parameters
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hopT hTf hTb (hFD.read ψ) (hFD.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take nP (ppsAll ψ) (AnnotTerm.sort (resSort.eval ψ))
      (by rw [hFD.len ψ]; omega)
    obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
    subst hΓt
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs'))
        ((ds ψ).map (·.2.2)).reverse (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
      opened_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hlenF : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
    have hiff : ∀ ρ : Nat → V, Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ := by
      intro ρ
      have := (hpf nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    have hrow : ∀ j, j < nF → ∃ u, sorts[j]? = some u ∧
        (isProp = false → Level.leq u resSort = some true) ∧
        ∀ ρ : Nat → V,
          Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + j))) ρ →
          interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD
            (nP + nF - 1 - (nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, -⟩ := hfields j hj
      refine ⟨u, hu, hleq, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
      have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
      have hread := hC.doms (nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hsortsPart : ∀ ρ : Nat → V, Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) := by
      intro ρ hρ j hj as hsp
      obtain ⟨u, hu, -, hmem⟩ := hrow j hj
      have hsat := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
      have hdropj : ((((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - (nP + j))
          = ((((ds ψ).drop nP).map (·.2.2)).take j).reverse ++
            (((ds ψ).take nP).map (·.2.2)).reverse := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - (nP + j) = nF - j from by omega,
          List.drop_append_of_le_length (by rw [List.length_reverse, hlenF]; exact Nat.sub_le _ _),
          List.drop_reverse, hlenF, show nF - (nF - j) = j from by omega]
      have hentj : ((((ds ψ).map (·.2.2)).reverse)).getD (nP + nF - 1 - (nP + j)) default
          = (((ds ψ).drop nP).map (·.2.2)).getD j default := by
        rw [reverse_map_take_drop (ds ψ) nP, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_reverse, hlenF]; omega),
          List.getElem?_reverse (by rw [hlenF]; omega), hlenF,
          show nF - 1 - (nF - 1 - j) = j from by omega, ← List.getD_eq_getElem?_getD]
      have := hmem (consList as ρ) (by rw [hdropj]; exact hsat)
      rw [hentj] at this
      rw [List.getD_eq_getElem?_getD (l := sorts), hu]
      exact this
    refine ⟨hiff, fun ρ hρ => ?_, hsortsPart⟩
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by
      simp [hlenDs]
    have hρ' : Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      by_cases hnp : isProp = true
      · exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · rw [← hFsEq]
      exact fieldsValid_of_frame rfl hΓlen hC.okΓ 0 (Nat.zero_le _) ρ hρ'
    · intro hnp
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, hleq, hmem⟩ := hrow j hj
      have hle := Level.leq_sound (hleq hnp) ψ
      exact univ_mono hle _ (hmem ρ hρ)
    · -- the index expressions at a fitting field spine
      intro bs hsp
      have hlenB : bs.length = nF := by rw [hsp.length_eq, hlenF]
      have hsat : Sat V (((ds ψ).map (·.2.2)).reverse) (consList bs ρ) := by
        have := sat_of_spineFit (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse) hρ hsp
        rwa [← reverse_map_take_drop] at this
      have hokRP := hC.okR _ hsat
      unfold ctorBodyAVI at hokRP
      have hokR := hokRP.1
      obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokR
      obtain ⟨-, hargsV⟩ := AnnotValid.mkAppN_inv hokRP.2
      refine ⟨fun E hE => ⟨hargs E (List.mem_append_right _ hE),
        hargsV E (List.mem_append_right _ hE)⟩, ?_⟩
      -- the spine fits the former's leaf
      obtain ⟨B, hB⟩ := hleafT ψ
      have hfit := spineFit_of_wellDenoted_lams (u := resSort.eval ψ + 1) (Nat.succ_ne_zero _)
        (b := B) (args := paramBvars nP nF ++ Es ψ)
        (ds := ppsAll ψ) (σ := consList bs ρ) (ρ := consList bs ρ) (f := mp.base2.acval T ψ)
        (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]) hokR (by rw [hB])
      rw [List.take_of_length_le (by simp [paramBvars, hCD.lenE ψ, hFD.len ψ]),
        ← List.take_append_drop nP (ppsAll ψ), List.map_append, List.map_append] at hfit
      obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
      have hlen₁ : as₁.length = nP := by
        rw [h1.length_eq, List.length_map, List.length_take, hFD.len ψ]; omega
      have hps : (paramBvars nP nF).map (interp V (consList bs ρ))
          = (List.range nP).reverse.map ρ := by
        rw [paramBvars_eq_paramBvarsAt]
        exact map_paramBvarsAt_interp (fun j => by rw [← hlenB]; exact consList_apply_add bs ρ j)
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvars])
      rw [hps] at h2
      show SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) ((Es ψ).map (interp V (consList bs ρ)))
      refine spineFit_congr_below (DomsBelow.drop nP (hFD.below ψ)) ?_ h2
      intro i hi
      rw [Nat.zero_add] at hi
      exact consList_params_apply ρ _ hi
  refine ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2.1, hlenS, ?_, fun ψ => (hframes ψ).2.2⟩
  intro j hj hnp
  obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hfields j hj
  rw [List.getD_eq_getElem?_getD, hu]
  exact hleq hnp

end ConLeche.Model
