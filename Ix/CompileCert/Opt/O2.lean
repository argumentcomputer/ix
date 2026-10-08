import Ix.CompileCert.Opt.AuxCore

/-!
# M7 L3-def: O2, the recursor of a split block (`Ix/Compile/Pass/Opt/O2.lean`)

The docstring's *Faithfulness (definitional, up to η)*: "By Def 3.4 the image's Ix minor for `c`
is `λ fs ihs. mⱼ fs h₁ … h_q` … The adapted minor is that term with (i) the relocated hypothesis
`img(r_T) ps ms mins idx (f ys)` in place of its development, which is the same term after δ (img)
and β, and which the engine rewrites by a pass that is itself definitional; (ii) the binder domains
as Lean's minor type gives them …, equal to the image's developed domains up to β; (iii) `mⱼ`
applied rather than substituted into, equal up to β. A reflexive wrapper `λ a. ih a` of the image
is `ih` by η."

The proof splits the argument where the code splits it:

* **the arrangement** (this module, over the compiler's `O2.apply`, unfolded): the occurrence
  δβ-reduces through the image (`RecLawI`: `r` denotes its image, whose minor terms are the ones
  the shape records) to `ρ ps (ms ∘ σ) M⃗[args] is t`; O2's output has the same parameters,
  motives (by `σ`), indices, major and extra arguments, and per Ix minor either the Lean minor
  variable's argument (as O6) or the adapted minor;
* **the engine's rewrite of the relocated calls** (this module, `adaptMinor_mono`): the adapted
  minor built with the engine (`recur`) converts to the one built with the relocated calls left as
  Lean recursor occurrences (`occRecur`: the call-site surgery's term), given that the engine's
  results convert to their occurrences (the induction hypothesis of `engineN_faithful`): the two
  runs read the same constructor, minor type, fields and targets, and differ only in the relocated
  calls, which `mkLambda` abstracts in the same way (`mkLambda_conv`, over the core copy of
  `batchAbstract`, design D-3);
* **(i)–(iii) and η at the surgery's term**: the named law `O2MinorLaw`: the image's wrapped Ix
  minor, at the occurrence's arguments, converts to the adapted minor with the relocated calls as
  Lean recursor occurrences (L2a-syn: Def 3.4 step 4 and the minor-type correspondence; the
  report's laws ledger).

**`O2_faithful_on`** proves conversion at an occurrence satisfying `O2Ready`, which includes
`PrefixFresh` and `RecurConvFrom`, from `RecLawI`, `O2MinorLaw`, the copies (`AuxGenCopies`)
and `BAbsClosed Γ`. It does not discharge the general `O2Faithful` engine hypothesis. That
discharge awaits capture-avoiding helpers; the engine, hook and rewrite keep their general domains.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## Lists related pointwise -/

/-- Two lists related position by position. -/
inductive Rel2 {α β : Type} (Q : α → β → Prop) : List α → List β → Prop
  | nil : Rel2 Q [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : Q a b → Rel2 Q as bs → Rel2 Q (a :: as) (b :: bs)

/-- **A loop that pushes one element per input element** (in `Option`): the result is the
initial array followed by elements related to the inputs position by position. -/
theorem forIn_option_push {α β : Type} (f : α → Array β → Option (ForInStep (Array β)))
    (Q : α → β → Prop) (hstep : ∀ x acc r, f x acc = some r → ∃ y, r = .yield (acc.push y) ∧ Q x y) :
    ∀ (l : List α) (acc res : Array β), forIn l acc f = some res →
      ∃ ys : List β, res = acc ++ ys.toArray ∧ Rel2 Q l ys
  | [], acc, res, h => by
    rw [List.forIn_nil] at h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨[], by simp, .nil⟩
  | x :: l, acc, res, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := obind.1 h
    obtain ⟨y, rfl, hq⟩ := hstep x acc r hr
    obtain ⟨ys, rfl, hp⟩ := forIn_option_push f Q hstep l (acc.push y) res h
    exact ⟨y :: ys, by simp, .cons hq hp⟩

/-- **Two runs of a loop** (in `Option`) whose steps keep a relation: the second succeeds where
the first does, with related results. -/
theorem forIn_option_sim {α σ τ : Type} (f : α → σ → Option (ForInStep σ))
    (g : α → τ → Option (ForInStep τ)) (R : σ → τ → Prop)
    (hstep : ∀ x a b r, R a b → f x a = some r →
      ∃ a' b', r = .yield a' ∧ g x b = some (.yield b') ∧ R a' b') :
    ∀ (l : List α) (a : σ) (b : τ) (res : σ), R a b → forIn l a f = some res →
      ∃ res', forIn l b g = some res' ∧ R res res'
  | [], a, b, res, hab, h => by
    rw [List.forIn_nil] at h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨b, by rw [List.forIn_nil]; rfl, hab⟩
  | x :: l, a, b, res, hab, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := obind.1 h
    obtain ⟨a', b', rfl, hg, hr'⟩ := hstep x a b r hab hr
    obtain ⟨res', h1, h2⟩ := forIn_option_sim f g R hstep l a' b' res hr' h
    refine ⟨res', ?_, h2⟩
    rw [List.forIn_cons, hg]
    exact h1

/-! ## `Option` runs side by side -/

theorem osim_bind {α β γ : Type} {x : Option α} {f : α → Option β} {g : α → Option γ}
    {R : β → γ → Prop} {b : β} (h : (x >>= f) = some b)
    (hf : ∀ a, x = some a → f a = some b → ∃ c, g a = some c ∧ R b c) :
    ∃ c, (x >>= g) = some c ∧ R b c := by
  obtain ⟨a, ha, h⟩ := obind.1 h
  obtain ⟨c, hc, hr⟩ := hf a ha h
  exact ⟨c, by rw [ha]; exact hc, hr⟩

theorem osim_ite {c : Prop} [Decidable c] {β γ : Type} {a1 b1 : Option β} {a2 b2 : Option γ}
    {R : β → γ → Prop} {b : β} (h : (if c then a1 else b1) = some b)
    (ht : c → a1 = some b → ∃ x, a2 = some x ∧ R b x) (he : ¬ c → b1 = some b → ∃ x, b2 = some x ∧ R b x) :
    ∃ x, (if c then a2 else b2) = some x ∧ R b x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h ⊢; exact ht hc h
  · simp only [hc, ↓reduceIte] at h ⊢; exact he hc h

/-- **A loop run side by side**, followed by the rest of a do-block. -/
theorem osim_forIn_arr {α σ τ β γ : Type} {l : Array α} {a : σ} {b : τ}
    {f : α → σ → Option (ForInStep σ)} {g : α → τ → Option (ForInStep τ)} {k1 : σ → Option β}
    {k2 : τ → Option γ} {R : σ → τ → Prop} {Q : β → γ → Prop} {x : β}
    (h : (forIn l a f >>= k1) = some x) (hab : R a b)
    (hstep : ∀ y a b r, R a b → f y a = some r → ∃ a' b', r = .yield a' ∧ g y b = some (.yield b') ∧ R a' b')
    (hk : ∀ r r', R r r' → k1 r = some x → ∃ c, k2 r' = some c ∧ Q x c) :
    ∃ c, (forIn l b g >>= k2) = some c ∧ Q x c := by
  obtain ⟨res, hloop, h⟩ := obind.1 h
  rw [← Array.forIn_toList] at hloop
  obtain ⟨res', h1, h2⟩ := forIn_option_sim f g R hstep l.toList a b res hab hloop
  obtain ⟨c, hc, hq⟩ := hk res res' h2 h
  exact ⟨c, by rw [← Array.forIn_toList, h1]; exact hc, hq⟩

/-! ## The relocated calls left as occurrences -/

/-- The relocated calls as Lean recursor occurrences: the call-site surgery's term. -/
def occRecur : Occ → Option Expr := fun o => some (occTerm o)

/-- The engine's results convert to their occurrences, at the occurrences O2 makes: the relocated
calls, whose arguments begin with the occurrence's parameters, motives and minors `pre`. -/
def RecurConvFrom (Γ : Env) (recur : Occ → Option Expr) (pre : Array Expr) : Prop :=
  ∀ o' e', o'.site = none → (∃ rest, o'.args = pre ++ rest) → recur o' = some e' →
    ExprConv Γ e' (occTerm o')

/-- The occurrence's parameters, motives and minors (what the split-minor helpers read) have no
free variable: the helpers open binders with fixed fresh names (`Ix.AuxGen.freshFVar`), which
must not occur in what they abstract. -/
def PrefixFresh (s : RecShape) (o : Occ) : Prop :=
  ∀ i a, i < s.np + s.nm + s.nmin → o.args[i]? = some a → fvarFree (er a) = true

/-- Two results of `adaptMinor`: both unadapted, or adapted to convertible terms. -/
def OptConv (Γ : Env) : Option Expr → Option Expr → Prop
  | none, none => True
  | some w, some w₀ => ExprConv Γ w w₀
  | _, _ => False

/-! ## The parts of an occurrence O2 reads -/

def psOf (s : RecShape) (o : Occ) : Array Expr := o.args.extract 0 s.np
def msOf (s : RecShape) (o : Occ) : Array Expr := o.args.extract s.np (s.np + s.nm)
def minsOf (s : RecShape) (o : Occ) : Array Expr := o.args.extract (s.np + s.nm) (s.np + s.nm + s.nmin)
def inBlockOf (s : RecShape) : Array Bool := (Array.range s.nm).map s.motiveSrc.contains

/-- What O2 put at an Ix minor `(src?, t)` of the shape: the Lean minor `j` it is built from
(`src? = some j`, or the head of the image's wrapped minor `t`), passed as it is or adapted. -/
def O2Minor (recur : Occ → Option Expr) (ienv : Ix.Environment) (rv : RecursorVal) (s : RecShape)
    (o : Occ) : Option Nat × Expr → Expr → Prop
  | (src?, t), y => ∃ j, (src? = some j ∨ (src? = none ∧ wrappedMinorSrc s.arity s.np s.nm s.nmin t = some j)) ∧
      ((adaptMinor recur ienv rv (inBlockOf s) o.us (psOf s o) (msOf s o) (minsOf s o) j = some none ∧
          (minsOf s o)[j]? = some y) ∨
       (src? = none ∧
          adaptMinor recur ienv rv (inBlockOf s) o.us (psOf s o) (msOf s o) (minsOf s o) j = some (some y)))

/-! ## The laws -/

/-- The image's minor terms at the occurrence's universe arguments. -/
def minorsAt (s : RecShape) (us : Array Level) : List Tm :=
  s.minorTerms.toList.map fun t => er (Ix.Compile.Canon.substLevels s.levelParams us t)

/-- **`RecLawI`** (decision 3, with the minors): a Lean recursor `h` of a changed block δ-reduces,
at every universe argument, to its image, whose shape is the one the block records and whose Ix
minors are the shape's recorded minor terms (what `readShape` reads off the image). -/
def RecLawI (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (h r : Name) (b : OptBlock) (s : RecShape) (us : Array Level),
    classify h = some (.kRec, r) → env.blockOf h = some b → b.shapes.get? r = some s →
    ∃ v, Γ.ax (.const h us) v ∧ ImageAt s (s.levelsAt us) (minorsAt s us) v

/-- The image's wrapped minor `t` at the occurrence: under the image's telescope, instantiated
with the occurrence's first `arity` arguments. -/
def imgMinor (s : RecShape) (o : Occ) (t : Expr) : Tm :=
  betaN ((o.args.toList.map er).take s.arity) (er (Ix.Compile.Canon.substLevels s.levelParams o.us t))

/-- **`O2MinorLaw`** (L2a-syn: Def 3.4 step 4 and the minor-type correspondence; the docstring's
(i)–(iii) and η): at an occurrence of O2's pattern, an Ix minor `t` of the image that is not a Lean
minor variable, built from Lean minor `j`, converts to the minor the call-site surgery builds
(`adaptMinor` with the relocated calls left as Lean recursor occurrences, `occRecur`): Lean's
minor itself when no field of its constructor is recursive into another component, the adapted
minor otherwise. -/
def O2MinorLaw (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (o : Occ) (r : Name) (b : OptBlock) (s : RecShape) (rv : RecursorVal) (k j : Nat) (t : Expr),
    classify o.head = some (.kRec, r) → env.blockOf o.head = some b → b.change.split = true →
    b.change.collapse = false → b.shapes.get? r = some s → env.const? r = some (.recInfo rv) →
    s.arity ≤ o.args.size → s.minorSrc[k]? = some none → s.minorTerms[k]? = some t →
    wrappedMinorSrc s.arity s.np s.nm s.nmin t = some j → PrefixFresh s o →
    (∀ m, adaptMinor occRecur env.ienv rv (inBlockOf s) o.us (psOf s o) (msOf s o) (minsOf s o) j =
        some none → (minsOf s o)[j]? = some m → Conv Γ (imgMinor s o t) (er m)) ∧
    (∀ w, adaptMinor occRecur env.ienv rv (inBlockOf s) o.us (psOf s o) (msOf s o) (minsOf s o) j =
        some (some w) → Conv Γ (imgMinor s o t) (er w))

/-! ## The decomposition -/

theorem kind_rec {k : AuxKind} (hk : ¬ (k != .kRec) = true) : k = .kRec := by
  cases k
  · rfl
  all_goals exact absurd rfl hk

theorem split_ok {a c : Bool} (h : ¬ (!a || c) = true) : a = true ∧ c = false := by
  cases a <;> cases c <;> simp_all

/-- What a firing of O2 established. -/
theorem O2_some {recur : Occ → Option Expr} {env : OptEnv} {o : Occ} {e : Expr}
    (h : O2.apply recur env o = some e) :
    ∃ r b s rv ls ms' mins', classify o.head = some (.kRec, r) ∧ env.blockOf o.head = some b ∧
      b.change.split = true ∧ b.change.collapse = false ∧ b.shapes.get? r = some s ∧
      env.const? r = some (.recInfo rv) ∧ s.arity ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
      pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms' ∧
      Rel2 (O2Minor recur env.ienv rv s o) (s.minorSrc.zip s.minorTerms).toList mins'.toList ∧
      e = mkAppN (Expr.mkConst s.ixRec ls) (o.args.extract 0 s.np ++ ms' ++ mins' ++
        o.args.extract (s.np + s.nm + s.nmin) s.arity ++ o.args.extract s.arity o.args.size) := by
  unfold O2.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsc, h⟩ := oguard h
  obtain ⟨s, hs, h⟩ := obind.1 h
  try dsimp only at h
  split at h
  · rename_i rv hrv
    obtain ⟨n, hn, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hsz, h⟩ := oguard h
    obtain ⟨ls, hls, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨ms', hms, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨mins', hloop, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    have he : e = _ := h.symm
    have hk' : k = .kRec := kind_rec hk
    subst hk'
    have hn' : n = s.arity := standardTelescope_eq hn
    subst hn'
    obtain ⟨hsp, hcol⟩ := split_ok hsc
    rw [← Array.forIn_toList] at hloop
    obtain ⟨ys, hres, hrel⟩ := forIn_option_push _ (O2Minor recur env.ienv rv s o) (by
      rintro ⟨src?, t⟩ acc res hb'
      dsimp only at hb'
      cases src? with
      | some j0 =>
        dsimp only at hb'
        obtain ⟨j, hj, hb'⟩ := obind.1 hb'
        simp only [pure, Option.some.injEq] at hj
        subst hj
        obtain ⟨am, ha, hb'⟩ := obind.1 hb'
        cases am with
        | none =>
          try dsimp only at hb'
          obtain ⟨m, hm, hb'⟩ := obind.1 hb'
          simp only [pure, Option.some.injEq] at hb'
          exact ⟨m, hb'.symm, j0, .inl rfl, .inl ⟨ha, hm⟩⟩
        | some w =>
          try dsimp only at hb'
          obtain ⟨hns, _⟩ := oguard hb'
          exact absurd rfl hns
      | none =>
        dsimp only at hb'
        obtain ⟨j, hj, hb'⟩ := obind.1 hb'
        obtain ⟨am, ha, hb'⟩ := obind.1 hb'
        cases am with
        | none =>
          try dsimp only at hb'
          obtain ⟨m, hm, hb'⟩ := obind.1 hb'
          simp only [pure, Option.some.injEq] at hb'
          exact ⟨m, hb'.symm, j, .inr ⟨rfl, hj⟩, .inl ⟨ha, hm⟩⟩
        | some w =>
          try dsimp only at hb'
          obtain ⟨_, hb'⟩ := oguard hb'
          simp only [pure, Option.some.injEq] at hb'
          exact ⟨w, hb'.symm, j, .inr ⟨rfl, hj⟩, .inr ⟨rfl, ha⟩⟩) _ _ _ hloop
    refine ⟨r, b, s, rv, ls, ms', mins', hc, hb, hsp, hcol, hs, hrv, by omega, hls, hms, ?_, he⟩
    rw [hres]
    simpa using hrel
  · oabsurd h

/-! ## The arrangement -/

theorem betaN_shapeTv {o : Occ} {s : RecShape} (hn : s.arity ≤ o.args.size) {p : Nat} (hp : p < s.arity) :
    betaN ((o.args.toList.map er).take s.arity) (shapeTv s p) = argT o.args p := by
  have hlen : ((o.args.toList.map er).take s.arity).length = s.arity := by
    simp only [List.length_take, List.length_map, Array.length_toList]; omega
  have e1 : shapeTv s p = .bvar (((o.args.toList.map er).take s.arity).length - 1 - p) := by
    rw [hlen]; rfl
  rw [e1, betaN_tv (by rw [hlen]; exact hp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take]
  simp only [hp, ↓reduceIte]
  rw [← List.getD_eq_getElem?_getD]
  exact gL_args o.args p

/-- A list related by `Q` to a list of expressions, with every related pair convertible. -/
theorem rel2_forall2 {Γ : Env} {α : Type} {Q : α → Expr → Prop} {F : α → Tm}
    {xs : List α} {ys : List Expr} (hr : Rel2 Q xs ys)
    (hk : ∀ (k : Nat) x y, xs[k]? = some x → ys[k]? = some y → Q x y → Conv Γ (er y) (F x)) :
    Forall2 (Conv Γ) (ys.map er) (xs.map F) := by
  induction hr with
  | nil => exact .nil
  | cons hq _ ih =>
    exact .cons (hk 0 _ _ rfl rfl hq) (ih (fun k x' y' h1 h2 h3 => hk (k + 1) x' y' h1 h2 h3))

/-! ## The engine's rewrite of the relocated calls -/

theorem idBind_conv {Γ : Env} {α : Type} (M : Id α) (F G : α → Id Expr)
    (h : ∀ a, Conv Γ (er (F a)) (er (G a))) : Conv Γ (er (M >>= F)) (er (M >>= G)) := h M

/-- A loop in `Id` that wraps its state in one binder per element converts its starting points. -/
theorem binderLoop_forIn_conv {Γ : Env} {α : Type} (step : α → Expr → Expr)
    (hstep : ∀ x a b, Conv Γ (er a) (er b) → Conv Γ (er (step x a)) (er (step x b))) :
    ∀ (l : List α) (a b : Expr), Conv Γ (er a) (er b) →
      Conv Γ (er (forIn (m := Id) l a (fun x r => pure (ForInStep.yield (step x r)))))
        (er (forIn (m := Id) l b (fun x r => pure (ForInStep.yield (step x r)))))
  | [], a, b, h => by simp only [List.forIn_nil]; exact h
  | x :: l, a, b, h => by
    rw [List.forIn_cons, List.forIn_cons]
    exact binderLoop_forIn_conv step hstep l _ _ (hstep x a b h)

/-- **`mkLambda` is a congruence** (over the core copy of `batchAbstract`). -/
theorem mkLambda_conv {Γ : Env} (hc : AuxGenCopies) (hΓ : BAbsClosed Γ) {b b' : Expr}
    (ds : Array Ix.AuxGen.LocalDecl) (h : ExprConv Γ b b') :
    ExprConv Γ (Ix.AuxGen.mkLambda b ds) (Ix.AuxGen.mkLambda b' ds) := by
  unfold ExprConv at h ⊢
  unfold Ix.AuxGen.mkLambda Ix.AuxGen.mkBinderChain
  simp only [Id.run]
  split
  · exact h
  · refine idBind_conv _ _ _ (fun M => ?_)
    simp only [bind_pure]
    rw [← Array.forIn_toList, ← Array.forIn_toList]
    refine binderLoop_forIn_conv _ ?_ _ _ _ ?_
    · intro x a c hac
      simp only [er_mkLam]
      exact .lam (.refl _) hac
    · rw [hc.batchAbstract, er_batchAbstractP, er_batchAbstractP]
      exact conv_babs hΓ _ _ h 0

theorem relocatedIh_mono {Γ : Env} (hc : AuxGenCopies) (hΓ : BAbsClosed Γ) {recur : Occ → Option Expr}
    {ps ms mins : Array Expr} (hr : RecurConvFrom Γ recur (ps ++ ms ++ mins))
    {target : Ix.AuxGen.SourceRecTarget} {field : Expr} {all : Array Name} {us : Array Level} {ih : Expr}
    (h : relocatedIh recur target field all us ps ms mins = some ih) :
    ∃ ih₀, relocatedIh occRecur target field all us ps ms mins = some ih₀ ∧ ExprConv Γ ih ih₀ := by
  unfold relocatedIh at h ⊢
  cases hall : all[0]? with
  | none => rw [hall] at h; cases h
  | some all0 =>
    rw [hall] at h
    try dsimp only at h ⊢
    obtain ⟨inner, hin, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, mkLambda_conv hc hΓ _ (hr _ _ rfl ⟨target.idxArgs ++ #[target.xsFvars.foldl Expr.mkApp field],
      by simp only [Array.append_assoc]⟩ hin)⟩

/-- **The adapted minor built with the engine converts to the surgery's** (the relocated calls
left as Lean recursor occurrences): the two runs read the same constructor, minor type, fields,
targets and hypotheses, and differ only in the relocated calls. -/
theorem adaptMinor_mono {Γ : Env} (hc : AuxGenCopies) (hΓ : BAbsClosed Γ) {recur : Occ → Option Expr}
    {ps ms mins : Array Expr} (hr : RecurConvFrom Γ recur (ps ++ ms ++ mins)) {ienv : Ix.Environment}
    {rv : RecursorVal} {inBlock : Array Bool} {us : Array Level} {j : Nat} {x : Option Expr}
    (h : adaptMinor recur ienv rv inBlock us ps ms mins j = some x) :
    ∃ x₀, adaptMinor occRecur ienv rv inBlock us ps ms mins j = some x₀ ∧ OptConv Γ x x₀ := by
  unfold adaptMinor at h ⊢
  try dsimp only at h ⊢
  refine osim_bind h ?_
  rintro ⟨_, ctor⟩ - h
  try dsimp only at h ⊢
  refine osim_bind h ?_
  rintro minorTy - h
  try dsimp only at h ⊢
  refine osim_bind h ?_
  rintro ⟨fieldDecls, fieldFVars, afterFields⟩ - h
  try dsimp only at h ⊢
  refine osim_bind h ?_
  rintro recFields - h
  try dsimp only at h ⊢
  refine osim_ite h ?_ ?_
  · intro _ h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨none, rfl, trivial⟩
  · intro _ h
    refine osim_bind h ?_
    rintro ⟨ihDecls, ihFVars, _⟩ - h
    try dsimp only at h ⊢
    refine osim_ite h ?_ ?_
    · intro _ h
      oabsurd h
    · intro _ h
      try dsimp only at h ⊢
      refine osim_bind h ?_
      rintro m - h
      try dsimp only at h ⊢
      refine osim_forIn_arr (R := fun (a b : Array Ix.AuxGen.LocalDecl × Expr) => a.1 = b.1 ∧ ExprConv Γ a.2 b.2)
        h ⟨rfl, .refl _⟩ ?_ ?_
      · rintro ⟨⟨fieldIdx, target⟩, ihIdx⟩ ⟨d1, b1⟩ ⟨d2, b2⟩ r ⟨hd, hb⟩ hf
        try dsimp only at hf hd hb ⊢
        subst hd
        by_cases hin : inBlock.getD target.sourcePos false = true
        · simp only [hin, ↓reduceIte, pure, Option.some.injEq] at hf ⊢
          subst hf
          refine ⟨_, _, rfl, rfl, rfl, ?_⟩
          unfold ExprConv at hb ⊢
          simp only [er_mkApp]
          exact .app hb (.refl _)
        · simp only [hin, Bool.false_eq_true, ↓reduceIte] at hf ⊢
          obtain ⟨ih, hih, hf⟩ := obind.1 hf
          simp only [pure, Option.some.injEq] at hf
          subst hf
          obtain ⟨ih₀, hih₀, hc'⟩ := relocatedIh_mono hc hΓ hr hih
          refine ⟨_, (d1, b2.mkApp ih₀), rfl, ?_, rfl, ?_⟩
          · rw [hih₀]; rfl
          · unfold ExprConv at hb hc' ⊢
            simp only [er_mkApp]
            exact .app hb hc'
      · rintro r r' ⟨h1, h2⟩ hk
        simp only [pure, Option.some.injEq] at hk
        subst hk
        refine ⟨_, rfl, ?_⟩
        show ExprConv Γ (Ix.AuxGen.mkLambda r.2 r.1) (Ix.AuxGen.mkLambda r'.2 r'.1)
        rw [h1]
        exact mkLambda_conv hc hΓ _ h2


theorem optConv_none {Γ : Env} {x : Option Expr} (h : OptConv Γ none x) : x = none := by
  cases x with
  | none => rfl
  | some _ => exact absurd h (by simp [OptConv])

theorem optConv_some {Γ : Env} {w : Expr} {x : Option Expr} (h : OptConv Γ (some w) x) :
    ∃ w₀, x = some w₀ ∧ ExprConv Γ w w₀ := by
  cases x with
  | none => exact absurd h (by simp [OptConv])
  | some w₀ => exact ⟨w₀, rfl, h⟩

theorem extract_get {a : Array Expr} {i j p : Nat} {y : Expr} (hj : j ≤ a.size)
    (h : (a.extract i j)[p]? = some y) : p < j - i ∧ argT a (i + p) = er y := by
  rw [Array.getElem?_extract] at h
  split at h
  · rename_i hp
    refine ⟨by omega, ?_⟩
    simp only [argT, h, Option.map_some, Option.getD_some]
  · cases h

/-- **O2's Ix minor converts to the image's**, at the occurrence's arguments. -/
theorem O2_minor_conv {Γ : Env} {env : OptEnv} (hc : AuxGenCopies) (hΓ : BAbsClosed Γ)
    (hlaw : O2MinorLaw Γ env) {recur : Occ → Option Expr} {o : Occ}
    {r : Name} {b : OptBlock} {s : RecShape} {rv : RecursorVal}
    (hr : RecurConvFrom Γ recur (psOf s o ++ msOf s o ++ minsOf s o)) (hfr : PrefixFresh s o)
    (hc0 : classify o.head = some (.kRec, r)) (hb : env.blockOf o.head = some b)
    (hsp : b.change.split = true) (hcol : b.change.collapse = false) (hs : b.shapes.get? r = some s)
    (hrv : env.const? r = some (.recInfo rv)) (hn : s.arity ≤ o.args.size)
    (hpt : ∀ (k j : Nat), s.minorSrc[k]? = some (some j) →
      (minorsAt s o.us)[k]? = some (shapeTv s (s.np + s.nm + j)))
    {k : Nat} {src? : Option Nat} {t y : Expr} (hk1 : s.minorSrc[k]? = some src?)
    (hk2 : s.minorTerms[k]? = some t) (hq : O2Minor recur env.ienv rv s o (src?, t) y) :
    Conv Γ (er y) (imgMinor s o t) := by
  obtain ⟨j, hsrc, hcase⟩ := hq
  rcases hsrc with rfl | ⟨rfl, hw⟩
  · rcases hcase with ⟨_, hy⟩ | ⟨h, _⟩
    · have hm := hpt k j hk1
      have hmk : (minorsAt s o.us)[k]? = some (er (Ix.Compile.Canon.substLevels s.levelParams o.us t)) := by
        simp only [minorsAt, List.getElem?_map, Array.getElem?_toList, hk2, Option.map_some]
      rw [hmk, Option.some.injEq] at hm
      have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
      obtain ⟨hjl, hy'⟩ := extract_get (by omega) (show (o.args.extract (s.np + s.nm)
        (s.np + s.nm + s.nmin))[j]? = some y from hy)
      unfold imgMinor
      rw [hm, betaN_shapeTv hn (by have : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl; omega), ← hy']
      exact .refl _
    · cases h
  · have law := hlaw o r b s rv k j t hc0 hb hsp hcol hs hrv hn hk1 hk2 hw hfr
    rcases hcase with ⟨ha, hy⟩ | ⟨_, ha⟩
    · obtain ⟨x₀, ha₀, hx⟩ := adaptMinor_mono hc hΓ hr ha
      rw [optConv_none hx] at ha₀
      exact .symm (law.1 y ha₀ hy)
    · obtain ⟨x₀, ha₀, hx⟩ := adaptMinor_mono hc hΓ hr ha
      obtain ⟨w₀, rfl, hw₀⟩ := optConv_some hx
      exact .trans hw₀ (.symm (law.2 w₀ ha₀))

/-- The hypotheses `O2_faithful_on` takes of the occurrence, at the shape O2 reads. -/
def O2Ready (Γ : Env) (env : OptEnv) (recur : Occ → Option Expr) (o : Occ) : Prop :=
  ∀ r b s, classify o.head = some (.kRec, r) → env.blockOf o.head = some b → b.shapes.get? r = some s →
    PrefixFresh s o ∧ RecurConvFrom Γ recur (psOf s o ++ msOf s o ++ minsOf s o)

/-- **O2 is definitional**: at an occurrence whose parameters, motives and minors have no free
variable, O2's output converts to the occurrence, given that the engine's results at the relocated
calls convert to them (`O2Ready`), the image with its minors (`RecLawI`), the image's wrapped
minors against the surgery's (`O2MinorLaw`), the core copies (`AuxGenCopies`) and rules closed
under abstraction (`BAbsClosed Γ`). -/
theorem O2_faithful_on {Γ : Env} {env : OptEnv} (hc : AuxGenCopies) (hΓ : BAbsClosed Γ)
    (hrec : RecLawI Γ env) (hlaw : O2MinorLaw Γ env) {recur : Occ → Option Expr} {o : Occ} {e : Expr}
    (hready : O2Ready Γ env recur o) (h : O2.apply recur env o = some e) :
    ExprConv Γ e (occTerm o) := by
  obtain ⟨r, b, s, rv, ls, ms', mins', hc0, hb, hsp, hcol, hs, hrv, hn, hls, hms, hrel, rfl⟩ :=
    O2_some h
  obtain ⟨hfr, hr⟩ := hready r b s hc0 hb hs
  have hls' := O5_levels_eq hls
  obtain ⟨v, hδ, ts, hts, hlen, hpt, -, rfl⟩ := hrec o.head r b s o.us hc0 hb hs
  rw [← hls'] at hδ
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have hL : s.arity ≤ (o.args.toList.map er).length := by simpa using hn
  have hconv := delta_beta hL hts hδ
  unfold ExprConv
  rw [er_occTerm, er_mkAppN, er_mkConst]
  refine .trans (Conv.appN_args _ ?_) (.symm hconv)
  simp only [Array.toList_append, List.map_append, shapeArgs]
  refine forall2_append (forall2_append (forall2_append (forall2_append ?_ ?_) ?_) ?_) ?_
  · -- the parameters
    apply forall2_of_eq
    rw [extract_map o.args (by omega), List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [List.mem_range] at hp
    simp only [Function.comp, Nat.zero_add]
    rw [betaN_shapeTv hn (by omega)]
  · -- the motives, by `σ`
    apply forall2_of_eq
    obtain ⟨hm1, hm2⟩ := pick_extract (show s.np + s.nm ≤ o.args.size by omega) hms
    rw [hm1, List.map_map]
    apply List.map_congr_left
    intro p hp
    have := hm2 p hp
    simp only [Function.comp]
    rw [betaN_shapeTv hn (by omega)]
  · -- the minors
    have hsz : s.minorTerms.size = s.minorSrc.size := by
      have : (minorsAt s o.us).length = s.minorSrc.size := hlen
      simpa [minorsAt] using this
    have e1 : (minorsAt s o.us).map (betaN ((o.args.toList.map er).take s.arity)) =
        (s.minorSrc.zip s.minorTerms).toList.map (fun x => imgMinor s o x.2) := by
      rw [Array.toList_zip]
      have e2 : (fun x : Option Nat × Expr => imgMinor s o x.2) = imgMinor s o ∘ Prod.snd := rfl
      rw [e2, ← List.map_map, List.map_snd_zip (by simp [hsz])]
      simp only [minorsAt, List.map_map]
      rfl
    rw [e1]
    refine rel2_forall2 hrel ?_
    intro k x y hx hy hq
    obtain ⟨src?, t⟩ := x
    rw [Array.toList_zip, List.getElem?_zip_eq_some] at hx
    obtain ⟨hx1, hx2⟩ := hx
    exact O2_minor_conv hc hΓ hlaw hr hfr hc0 hb hsp hcol hs hrv hn hpt
      (by rw [← Array.getElem?_toList]; exact hx1) (by rw [← Array.getElem?_toList]; exact hx2) hq
  · -- the indices and the major
    apply forall2_of_eq
    rw [extract_map o.args hn, List.map_map, show s.arity - (s.np + s.nm + s.nmin) = s.ni + 1 by omega]
    apply List.map_congr_left
    intro p hp
    simp only [List.mem_range] at hp
    simp only [Function.comp]
    rw [betaN_shapeTv hn (by omega)]
  · -- the extra arguments
    apply forall2_of_eq
    rw [extract_map o.args (Nat.le_refl _), args_drop o.args hn]

end Ix.CompileCert.Opt
