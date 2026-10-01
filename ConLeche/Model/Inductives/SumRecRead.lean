module

public import ConLeche.Model.Inductives.StructRecRead
import ConLeche.Model.Annot.BitInst
public section

/-!
# The generated sum recursor's readings (task #175 sum-types, indexed)

`ConLeche/Model/Inductives/StructRecRead.lean` at a constructor list over
an indexed family: the generated recursor type reads to the Π-tower
over `sumRecDataAV` (parameters, motive over the index telescope, one
minor per constructor, the index telescope again, major), with the
core `motive ı⃗ t`, and rule `j` reads to the λ-tower over
`sumRuleDataAV` at constructor `j`'s field data, with the core
`minor_j f⃗`.  The minor entries are read by one induction over the
constructor list (`denoteP_minorsPis` / `denoteP_minorsLams`), the
accumulated variables (the motive first, then the earlier minors)
threaded as `extras`.

The one genuinely new reading is the minor's conclusion
`motive e⃗ (C p⃗ f⃗)`: the constructor's index expressions, spelled at
the recursor frame (under the extras), read to the constructor's own
index readings lifted above the fields
(`denoteMetaSpine_idxArgs_lift`) — obtained by reading the whole opened
residual `T p⃗ e⃗` at that frame and inverting the application spine.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Syntactic bookkeeping -/

/-- A closed instantiation sequence commutes with a strip. -/
theorem stripPis_instSeq :
    ∀ (sp : List Expr) (t : Nat) {e : Expr} {n : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr},
      sp.length ≤ t + 1 →
      e.stripPis n = some (bs, body) →
      ∃ bs', (Expr.instSeq sp t e).stripPis n = some (bs', Expr.instSeq sp (t + n) body)
  | [], _, _, _, bs, _, _, h => ⟨bs, h⟩
  | a :: sp, t, e, n, bs, body, hlen, h => by
    obtain ⟨bs', h', -⟩ := ConLeche.stripPis_instantiate1_full (v := a) n t h
    obtain ⟨bs'', h''⟩ := stripPis_instSeq sp (t - 1) (by simp at hlen; omega) h'
    refine ⟨bs'', ?_⟩
    show (Expr.instSeq sp (t - 1) (e.instantiate1 a t)).stripPis n
      = some (bs'', Expr.instSeq sp (t + n - 1) (body.instantiate1 a (t + n)))
    rw [h'']
    congr 2
    rcases sp with _ | ⟨b, sp⟩
    · rfl
    · have : 1 ≤ t := by simp at hlen; omega
      congr 1
      omega

theorem structPsAt_zero (n : Nat) :
    ConLeche.structPsAt 0 n = (List.range n).map fun k => Expr.bvar (n - 1 - k) := by
  simp [ConLeche.structPsAt]

/-- The index variables' spine one under (the major), instantiated at
the index variables. -/
theorem map_instSeq_structPsAt_one (ifvs : List Expr) (nIdx : Nat)
    (hcl : ∀ a ∈ ifvs, a.looseBVarsBounded 0 = true) (hlen : ifvs.length = nIdx) :
    (ConLeche.structPsAt 1 nIdx).map (Expr.instSeq ifvs nIdx) = ifvs := by
  apply List.ext_getElem
  · simp [ConLeche.structPsAt, hlen]
  · intro k h1 h2
    have hk : k < nIdx := by simpa [ConLeche.structPsAt] using h1
    simp only [ConLeche.structPsAt, List.getElem_map, List.getElem_range]
    have := Expr.instSeq_bvar ifvs nIdx (1 + nIdx - 1 - k) hcl (by omega) (by omega)
    rw [show nIdx - (1 + nIdx - 1 - k) = k from by omega, List.getElem?_eq_getElem h2] at this
    exact (Option.some.inj this).symm

/-- A closed spine is fixed by an instantiation sequence. -/
theorem map_instSeq_closed (sp : List Expr) (t : Nat) {xs : List Expr}
    (hcl : ∀ a ∈ xs, a.looseBVarsBounded 0 = true) :
    xs.map (Expr.instSeq sp t) = xs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map]
  exact Expr.instSeq_eq_self _ _ (hcl _ (List.getElem_mem h2))

/-- A closed spine is fixed by an instantiation. -/
theorem map_instantiate1_closed {xs : List Expr} (hcl : ∀ a ∈ xs, a.looseBVarsBounded 0 = true)
    (v : Expr) (k : Nat) : xs.map (·.instantiate1 v k) = xs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map]
  exact Expr.instantiate1_eq_self
    (Expr.looseBVarsBounded_mono (Nat.zero_le k) (hcl _ (List.getElem_mem h2)))

/-! ## `AnnotTerm` bookkeeping -/

theorem liftN_mkAppN (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, liftN_mkAppN n k as, AnnotTerm.liftN_app]

theorem AnnotTerm.mkAppN_append_one : ∀ (as : List AnnotTerm) (f a : AnnotTerm),
    AnnotTerm.mkAppN f (as ++ [a]) = .app (AnnotTerm.mkAppN f as) a
  | [], _, _ => rfl
  | b :: as, f, a => by
    simp only [List.cons_append, AnnotTerm.mkAppN_cons]
    exact AnnotTerm.mkAppN_append_one as _ a

theorem mkAppN_inj_args :
    ∀ {as bs : List AnnotTerm} {f g : AnnotTerm},
      AnnotTerm.mkAppN f as = AnnotTerm.mkAppN g bs → as.length = bs.length → f = g ∧ as = bs
  | [], [], _, _, h, _ => ⟨h, rfl⟩
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: as, b :: bs, f, g, h, hl => by
    simp only [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfg, hab⟩ := mkAppN_inj_args h (by simpa using hl)
    obtain ⟨rfl, rfl⟩ := AnnotTerm.app.inj hfg
    exact ⟨rfl, by rw [hab]⟩

/-- A leaf fixed by every one-step lift is fixed by every lift. -/
theorem liftN_eq_self_of_one {e : AnnotTerm} (h : ∀ k, AnnotTerm.liftN 1 e k = e) :
    ∀ (n k : Nat), AnnotTerm.liftN n e k = e
  | 0, k => AnnotTerm.liftN_zero e k
  | n + 1, k => by
    rw [show n + 1 = 1 + n from by omega, ← AnnotTerm.liftN_liftN e 1 n k,
      liftN_eq_self_of_one h n k, h k]

theorem DenoteMetaSpine.append_inv {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as bs : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as ++ bs) vs →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧
        DenoteMetaSpine acval env φ d as vs₁ ∧ DenoteMetaSpine acval env φ d bs vs₂
  | [], bs, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | a :: as, bs, vs, h => by
    rw [List.cons_append] at h
    cases h with
    | cons ha htl =>
      obtain ⟨vs₁, vs₂, rfl, h1, h2⟩ := DenoteMetaSpine.append_inv htl
      exact ⟨_ :: vs₁, vs₂, rfl, .cons ha h1, h2⟩

theorem DenoteMetaSpine.unique {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → DenoteMetaSpine acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteMetaSpine.unique h h']

/-! ## The entries -/

/-- The motive's domain reading `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the
parameters' frame, over the former's index data `ips`. -/
@[expose] def motiveAVI {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat) (nP nIdx : Nat)
    (ℓ : Level) (ips : List (Nat × Nat × AnnotTerm)) : AnnotTerm :=
  mkPisAV (rebit (pwBit ψ PropWhen.never) ips)
    (.pi 0 (pwBit ψ PropWhen.never)
      (AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx))
      (.sort (ℓ.eval ψ)))

/-- The major premise's domain reading under the motive, `n` minors
and the index variables: the family at the parameters and the index
variables. -/
@[expose] def majorAVAt {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat) (nP nIdx n : Nat) :
    AnnotTerm :=
  AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + 1 + n + nIdx) ++ fieldBvars nIdx)

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm

/-! ## The per-constructor reading premise -/

/-! ## The cores -/

/-- A constant at the parameter variables and `nF` more variables
above `o` extras reads to its leaf at the parameter and field
variables. -/
theorem denoteMeta_famSpine_at {m : EnvModel V env} {ψ : Name → Nat} {C : Name}
    {lps : List Name} {ci : ConstantInfo} (hfC : env.find? C = some ci)
    (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF o : Nat} {tfvs xFvs : List Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty) :
    denoteMeta m.acval env ψ (nP + o + nF) (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs))
      = some (AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)) := by
  have hspP : DenoteMetaSpine m.acval env ψ (nP + o + nF) tfvs (paramBvarsAt nP (nP + o + nF)) := by
    have := denoteMetaSpine_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) tfvs 0
      (fun k x hx => by
        obtain ⟨ty, h⟩ := hidxT k x hx
        exact ⟨ty, by rw [h, Nat.zero_add]⟩)
    rw [hlenT] at this
    have he : ((List.range nP).map fun k => AnnotTerm.bvar (nP + o + nF - 1 - (0 + k)))
        = paramBvarsAt nP (nP + o + nF) := by
      unfold paramBvarsAt
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    rwa [he] at this
  have hspX : DenoteMetaSpine m.acval env ψ (nP + o + nF) xFvs (fieldBvars nF) := by
    have := denoteMetaSpine_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) xFvs
      (nP + o) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AnnotTerm.bvar (nP + o + nF - 1 - (nP + o + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  have hconst : denoteMeta m.acval env ψ (nP + o + nF) (.const C (lps.map .param))
      = some (m.acval C ψ) := by
    rw [denoteMeta_const hfC (by rw [hlpsC]; simp), hlpsC, Level.substFn_param_self]
  exact denoteMeta_mkAppN (hspP.append hspX) hconst

/-- **The constructor's index expressions at the recursor frame.**
Under `o` extras and the field variables, the residual's index
expressions read to the constructor's own index readings lifted `o`
above the fields: the opened residual `T p⃗ e⃗` reads to the lifted
constructor body, whose spine is inverted. -/
theorem denoteMetaSpine_idxArgs_lift {m : EnvModel V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nF nIdx o : Nat} {crest0 : Expr} {fbs : List (Expr × BinderMeta)} {es : List Expr}
    (hsF : crest0.stripPis nF
      = some (fbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)))
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {tfvs xFvs : List Expr} (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hcreadO : denoteMeta m.acval env ψ (nP + o) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms o 0 (ds.drop nP))
          ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF)))
    (hlenD : ds.length = nP + nF) (hlenE : Es.length = nIdx) (hlenes : es.length = nIdx) :
    DenoteMetaSpine m.acval env ψ (nP + o + nF)
      (es.map fun e => Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP + nF - 1) e))
      (Es.map fun E => E.liftN o nF) := by
  have hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxX q a hq
    rfl
  have hnil : tfvs = [] ∨ nP - 1 + nF = nP + nF - 1 := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the opened residual at the frame
  obtain ⟨fbs', hsF'⟩ := stripPis_instSeq tfvs (nP - 1) (by omega) hsF
  obtain ⟨ds', hci⟩ := ConLeche.instPisAt_of_stripPis xFvs (by rw [hlenX]; exact hsF')
  have hstX : stripPisAV nF (mkPisAV (liftDoms o 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF))
      = some (liftDoms o 0 (ds.drop nP),
          (AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF) := by
    have := stripPisAV_mkPisAV (liftDoms o 0 (ds.drop nP))
      ((AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have htele := piTeleAV_of_stripPisAV hstX
  have hread := instPisAt_openerRes xFvs hci (j := nP + o) hidxX hcreadO (by rw [hlenX]; exact htele)
  rw [hlenX] at hread
  -- the residual, instantiated: the family at the parameter variables and the instantiated
  -- index expressions
  have hres : Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP - 1 + nF)
      (Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)))
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ es.map fun e => Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP + nF - 1) e)) := by
    rw [instSeq_idx_congr (sp := tfvs) (t := nP - 1 + nF) (t' := nP + nF - 1) _ hnil,
      Expr.instSeq_mkAppN, Expr.instSeq_mkAppN, List.map_append, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + nF - 1 = nF + nP - 1 from by omega,
      ConLeche.map_instSeq_structPsAt tfvs nF nP hclT (by omega), List.take_of_length_le (by omega),
      map_instSeq_closed xFvs (nF - 1) hclT, List.map_map,
      show nF + nP - 1 = nP + nF - 1 from by omega]
    rfl
  rw [hres] at hread
  obtain ⟨fa, vs, hfa, hsp, heq⟩ := denoteMeta_mkAppN_inv hread
  have hfa' : fa = m.acval T ψ := by
    rw [denoteMeta_const hfT (by rw [hlpsT]; simp), hlpsT, Level.substFn_param_self] at hfa
    exact (Option.some.inj hfa).symm
  subst hfa'
  rw [liftN_mkAppN, liftN_eq_self_of_one (m.acval_closed T ψ), List.map_append] at heq
  have hlenV : vs.length = nP + nIdx := by
    have := hsp.length
    simp [hlenT, hlenes] at this
    omega
  obtain ⟨-, hvs⟩ := mkAppN_inj_args heq (by simp [paramBvars, hlenV, hlenE])
  obtain ⟨vs₁, vs₂, rfl, h1, h2⟩ := DenoteMetaSpine.append_inv hsp
  have hlen1 : vs₁.length = nP := by rw [← h1.length, hlenT]
  obtain ⟨-, rfl⟩ := List.append_inj hvs.symm (by simp [paramBvars, hlen1])
  exact h2

/-! ## The minor premise -/

/-! ## The minors' telescopes -/

/-! ## The motive -/

/-- **The motive's type**, instantiated at the parameters, reads to
`motiveAVI` over the former's index data. -/
theorem denoteMeta_motiveI {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {ℓ : Level} {tty itele motiveTy : Expr}
    {tbs : List (Expr × BinderMeta)}
    (hsT : tty.stripPis nP = some (tbs, itele))
    (hmot : ConLeche.structMotiveTyI T lps nP nIdx ℓ itele = some motiveTy)
    (hTf : tty.hasFvar = false) (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {ppsAll : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hTread : denoteMeta m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    denoteMeta m.acval env ψ nP (Expr.instSeq tfvs (nP - 1) motiveTy)
      = some (motiveAVI m T ψ nP nIdx ℓ (ppsAll.drop nP)) := by
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxT q a hq
    rfl
  have hnil : tfvs = [] ∨ nP - 1 + nIdx = nIdx + nP - 1 := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  unfold ConLeche.structMotiveTyI at hmot
  have hmot' := ConLeche.replacePisPw_instSeq tfvs (nP - 1) (by omega) hmot
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx nP htstrip
  have hstI : stripPisAV nIdx (mkPisAV (ppsAll.drop nP) (.sort w))
      = some (ppsAll.drop nP, .sort w) := by
    have := stripPisAV_mkPisAV (ppsAll.drop nP) (AnnotTerm.sort w)
    rwa [List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmotive := denoteMeta_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmot' hopI
    htread hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the body, instantiated at the parameters and the index variables
  have hdom1 : Expr.instSeq tfvs (nP - 1 + nIdx) (ConLeche.structFamI T lps nP nIdx 0 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold ConLeche.structFamI
    rw [instSeq_idx_congr (sp := tfvs) (t := nP - 1 + nIdx) (t' := nIdx + nP - 1) _ hnil,
      Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show 0 + 0 + nIdx = nIdx from by omega,
      ConLeche.map_instSeq_structPsAt tfvs nIdx nP hclT (by omega), List.take_of_length_le (by omega),
      structPsAt_zero, ConLeche.map_instSeq_fieldBvars_above tfvs (nIdx + nP - 1) nIdx
        (by rw [hlenT]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      ConLeche.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq tfvs (nP - 1 + nIdx)
      (.forallE (ConLeche.structFamI T lps nP nIdx 0 0) (.sort ℓ)
        ⟨.never⟩))
      = .forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
          (.sort ℓ) ⟨.never⟩ := by
    rw [Expr.instSeq_forallE tfvs (nP - 1 + nIdx) _ _ _ (by omega), hdom1,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ (by omega), hdom2,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl]
  rw [hbody] at hmotive
  have hspine := denoteMeta_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := 0) hlenT hlenI hidxT
    (fun k x hx => by rw [Nat.add_zero]; exact hidxI k x hx)
  rw [Nat.add_zero] at hspine
  have hpi : denoteMeta m.acval env ψ (nP + nIdx)
      (.forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
        (.sort ℓ) ⟨.never⟩)
      = some (.pi 0 (pwBit ψ PropWhen.never)
          (AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx))
          (.sort (ℓ.eval ψ))) := by
    rw [denoteMeta_forallE, hspine, Expr.instantiate1_sort, denoteMeta_sort]
    rfl
  rw [hpi, Option.map_some] at hmotive
  exact hmotive

/-! ## The generated type -/

/-! ## The generated rule -/

end ConLeche.Model
