module

public import IxC.Kernel.Verify.Rename.Native1

@[expose] public section

/-!
# The renaming walk through the fixpoint route: the install's re-checks (step 7.3, chunk (iii))

The kinds re-checked on the stored constructors (`nativeOpenedOk`,
`nativeFieldsOk`) and the stream's rules against the generated ones
(`nativeRulePrefixOk`, `nativeRulesOk`), at renamed arguments over related
environments: they answer alike.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-! ## Small tests at renamed terms -/

theorem getAppFn_beq_const_map (hf : InjOn f P) {T : Key md} (hT : T.Good P)
    (us : List Level) {e : Expr md} (he : e.Good P) :
    ((e.mapKeys f).getAppFn == Expr.const (T.map f) us) = (e.getAppFn == Expr.const T us) := by
  rw [← Expr.mapKeys_getAppFn]
  exact Expr.mapKeys_beq hf he.getAppFn (show Expr.Good P (Expr.const T us) from hT)

theorem take_beq_map (hf : InjOn f P) {e : Expr md} (he : e.Good P) (n : Nat)
    {l : List (Expr md)} (hl : Expr.GoodList P l) :
    ((e.mapKeys f).getAppArgs.take n == l.map (Expr.mapKeys f)) = (e.getAppArgs.take n == l) := by
  rw [Expr.getAppArgs_mapKeys, ← List.map_take]
  exact list_beq_mapKeys hf (he.getAppArgs.take n) hl

theorem take_map_beq_map (hf : InjOn f P) {args : List (Expr md)} (ha : Expr.GoodList P args)
    (n : Nat) {l : List (Expr md)} (hl : Expr.GoodList P l) :
    ((args.map (Expr.mapKeys f)).take n == l.map (Expr.mapKeys f)) = (args.take n == l) := by
  rw [← List.map_take]
  exact list_beq_mapKeys hf (ha.take n) hl

theorem all_constsResolve_map {env : Env md} {env' : Env md'} (hE : EnvRel P f env env')
    {l : List (Expr md)} (hl : Expr.GoodList P l) :
    (l.map (Expr.mapKeys f)).all (fun e => e.constsResolve env') =
      l.all (fun e => e.constsResolve env) := by
  rw [List.all_map]
  exact List.all_congr_mem' fun x hx => constsResolve_ren hE (hl x hx)

theorem all_fvarTypeD_constsResolve_map {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {l : List (Expr md)} (hl : Expr.GoodList P l) :
    (l.map (Expr.mapKeys f)).all (fun e => e.fvarTypeD.constsResolve env') =
      l.all (fun e => e.fvarTypeD.constsResolve env) := by
  rw [List.all_map]
  exact List.all_congr_mem' fun x hx => by
    simp only [Function.comp, ← Expr.mapKeys_fvarTypeD]
    exact constsResolve_ren hE (hl x hx).fvarTypeD

theorem any_mentionsFvar_map (l : List (Expr md)) (q : Nat) :
    (l.map (Expr.mapKeys f)).any (fun y => y.fvarTypeD.mentionsFvar q) =
      l.any (fun y => y.fvarTypeD.mentionsFvar q) := by
  rw [List.any_map]
  congr 1
  funext y
  simp only [Function.comp, ← Expr.mapKeys_fvarTypeD, Expr.mentionsFvar_mapKeys]

/-! ## The kinds, re-checked -/

/-- **The kinds' re-check at a renamed constructor** answers alike. -/
theorem nativeOpenedOk_map {env₀ : Env md} {env₀' : Env md'} (hE₀ : EnvRel P f env₀ env₀')
    {T : Key md} (hT : T.Good P) (lps : List LevelParam) (nP nIdx : Nat) {cty : Expr md}
    (hc : cty.Good P) (nF : Nat) (ks : List RecFieldKind) :
    nativeOpenedOk env₀' (T.map f) lps nP nIdx (cty.mapKeys f) nF ks =
      nativeOpenedOk env₀ T lps nP nIdx cty nF ks := by
  have hf := hE₀.inj
  unfold nativeOpenedOk
  rw [openPisAtFvars_mapKeys]
  cases h₁ : openPisAtFvars nP cty 0 with
  | none => rfl
  | some q₁ =>
    obtain ⟨fvsP, crest⟩ := q₁
    obtain ⟨hfvsP, hcrest⟩ := Expr.openPisAtFvars_good hc h₁
    simp only [Option.map_some, Expr.mapDoms]
    rw [openPisAtFvars_mapKeys]
    cases h₂ : openPisAtFvars nF crest nP with
    | none => rfl
    | some q₂ =>
      obtain ⟨xFvs, xrest⟩ := q₂
      obtain ⟨hx, hxrest⟩ := Expr.openPisAtFvars_good hcrest h₂
      simp only [Option.map_some, Expr.mapDoms, Expr.getAppArgs_mapKeys, ← List.map_drop,
        all_constsResolve_map hE₀ (hxrest.getAppArgs.drop nP), Expr.mentionsFvar_mapKeys]
      congr 1
      apply List.all_congr_mem'
      intro i _
      rw [List.getElem?_map]
      cases hxi : xFvs[i]? with
      | none => rfl
      | some x =>
        have hxg : x.Good P := hx x (List.mem_of_getElem? hxi)
        have hxt : x.fvarTypeD.Good P := hxg.fvarTypeD
        simp only [Option.map_some]
        cases ks.getD i .ordinary with
        | ordinary =>
          simp only [← Expr.mapKeys_fvarTypeD]
          exact constsResolve_ren hE₀ hxt
        | recursive =>
          simp only [← Expr.mapKeys_fvarTypeD, getAppFn_beq_const_map hf hT _ hxt,
            take_beq_map hf hxt nP hfvsP, Expr.getAppArgs_mapKeys, List.length_map,
            take_map_beq_map hf hxt.getAppArgs nP hfvsP,
            ← List.map_drop, all_constsResolve_map hE₀ (hxt.getAppArgs.drop nP),
            any_mentionsFvar_map, Expr.mentionsFvar_mapKeys]
        | reflexive =>
          simp only [← Expr.mapKeys_fvarTypeD, Expr.piBinders_mapKeys, Expr.mapTele,
            Expr.mapBinders_length]
          rw [openPisAtFvars_mapKeys]
          cases h₃ : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | none => rfl
          | some q₃ =>
            obtain ⟨afvs, body⟩ := q₃
            obtain ⟨ha, hbody⟩ := Expr.openPisAtFvars_good hxt h₃
            simp only [Option.map_some, Expr.mapDoms, List.length_map,
              all_fvarTypeD_constsResolve_map hE₀ ha, getAppFn_beq_const_map hf hT _ hbody,
              take_beq_map hf hbody nP hfvsP, Expr.getAppArgs_mapKeys,
              take_map_beq_map hf hbody.getAppArgs nP hfvsP,
              ← List.map_drop, all_constsResolve_map hE₀ (hbody.getAppArgs.drop nP),
              any_mentionsFvar_map, Expr.mentionsFvar_mapKeys]
        | negative => rfl
        | unsupported => rfl

theorem nativeFieldsOk_map {env₀ : Env md} {env₀' : Env md'} (hE₀ : EnvRel P f env₀ env₀')
    {T : Key md} (hT : T.Good P) (lps : List LevelParam) (nP nIdx : Nat)
    {ctorsA : List (ConstantVal md × Nat)} (hcs : ∀ c ∈ ctorsA, c.1.Good P)
    (kinds : List (List RecFieldKind)) :
    nativeFieldsOk env₀' (T.map f) lps nP nIdx (ctorsA.map fun c => (c.1.mapKeys f, c.2)) kinds =
      nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds := by
  unfold nativeFieldsOk
  simp only [List.length_map]
  congr 1
  apply List.all_congr_mem'
  intro j _
  rw [List.getElem?_map]
  cases hj : ctorsA[j]? with
  | none => rfl
  | some c =>
    have hc := hcs c (List.mem_of_getElem? hj)
    cases kinds[j]? with
    | none => rfl
    | some ks =>
      simp only [Option.map_some, ConstantVal.mapKeys_type,
        nativeOpenedOk_map hE₀ hT lps nP nIdx hc.2]

/-! ## The stream's rules against the generated ones -/

theorem mapBinders_getElem? (bs : List (Expr md × BinderMeta)) (i : Nat) :
    (Expr.mapBinders f bs)[i]? = bs[i]?.map fun b => (b.1.mapKeys f, b.2) := by
  simp [Expr.mapBinders, List.getElem?_map]

theorem resetMeta_beq_map (hf : InjOn f P) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    (Expr.resetMeta (a.mapKeys f) == Expr.resetMeta (b.mapKeys f)) =
      (Expr.resetMeta a == Expr.resetMeta b) := by
  rw [← Expr.mapKeys_resetMeta, ← Expr.mapKeys_resetMeta]
  exact Expr.mapKeys_beq hf ha.resetMeta hb.resetMeta

theorem nativeRulePrefixOk_map (hf : InjOn f P) {recTy rhs : Expr md} (hty : recTy.Good P)
    (hrhs : rhs.Good P) (nP n j nF : Nat) :
    nativeRulePrefixOk (recTy.mapKeys f) nP n j nF (rhs.mapKeys f) =
      nativeRulePrefixOk recTy nP n j nF rhs := by
  unfold nativeRulePrefixOk
  rw [Expr.stripLams_mapKeys, Expr.stripPis_mapKeys]
  cases h₁ : Expr.stripLams (nP + 1 + n + nF) rhs with
  | none => rfl
  | some q₁ =>
    cases h₂ : Expr.stripPis (nP + 1 + n) recTy with
    | none => rfl
    | some q₂ =>
      obtain ⟨rbs, _⟩ := q₁
      obtain ⟨tbs, _⟩ := q₂
      obtain ⟨hrbs, _⟩ := Expr.stripLams_good hrhs h₁
      obtain ⟨htbs, _⟩ := Expr.stripPis_good hty h₂
      simp only [Option.map_some, Expr.mapTele, mapBinders_getElem?]
      congr 1
      · apply List.all_congr_mem'
        intro i _
        cases hr : rbs[i]? with
        | none => rfl
        | some b =>
          cases ht : tbs[i]? with
          | none => rfl
          | some t =>
            simp only [Option.map_some]
            exact resetMeta_beq_map hf (hrbs b (List.mem_of_getElem? hr))
              (htbs t (List.mem_of_getElem? ht))
      · cases hm : tbs[nP + 1 + j]? with
        | none => rfl
        | some mty =>
          have hmty : mty.1.Good P := htbs mty (List.mem_of_getElem? hm)
          simp only [Option.map_some, ← Expr.mapKeys_liftLooseBVars, Expr.stripPis_mapKeys]
          cases h₃ : Expr.stripPis nF (mty.1.liftLooseBVars (n - j) 0) with
          | none => rfl
          | some q₃ =>
            obtain ⟨fbs, _⟩ := q₃
            obtain ⟨hfbs, _⟩ := Expr.stripPis_good (hmty.liftLooseBVars (n - j) 0) h₃
            simp only [Option.map_some, Expr.mapTele, mapBinders_getElem?]
            apply List.all_congr_mem'
            intro i _
            cases hr : rbs[nP + 1 + n + i]? with
            | none => rfl
            | some b =>
              cases hfb : fbs[i]? with
              | none => rfl
              | some fb =>
                simp only [Option.map_some]
                exact resetMeta_beq_map hf (hrbs b (List.mem_of_getElem? hr))
                  (hfbs fb (List.mem_of_getElem? hfb))

/-- **The stream's rules against the generated ones**, at a renamed block. -/
theorem nativeRulesOk_map (hf : InjOn f P) {recC : Key md} (hrc : recC.Good P)
    (rlvls : List Level) (pw : PropWhen) (nP n : Nat) {cs : List (ConstantVal md × Nat)}
    (hcs : ∀ c ∈ cs, c.1.Good P) (kinds : List (List RecFieldKind)) {rhss : List (Expr md)}
    (hrhss : Expr.GoodList P rhss) {recTy : Expr md} (hty : recTy.Good P) :
    nativeRulesOk (recC.map f) rlvls pw nP n (cs.map fun c => (c.1.mapKeys f, c.2)) kinds
        (rhss.map (Expr.mapKeys f)) (recTy.mapKeys f) =
      nativeRulesOk recC rlvls pw nP n cs kinds rhss recTy := by
  unfold nativeRulesOk
  simp only [List.length_map]
  congr 1
  apply List.all_congr_mem'
  intro j _
  rw [List.getElem?_map, List.getElem?_map]
  cases hr : rhss[j]? with
  | none => rfl
  | some rhs =>
    cases hc : cs[j]? with
    | none => cases kinds[j]? <;> rfl
    | some c =>
      obtain ⟨cA, nF⟩ := c
      have hrhs : rhs.Good P := hrhss rhs (List.mem_of_getElem? hr)
      have hcA : cA.Good P := hcs (cA, nF) (List.mem_of_getElem? hc)
      cases hk : kinds[j]? with
      | none => rfl
      | some ks =>
        simp only [Option.map_some, ConstantVal.mapKeys_type, Expr.stripLams_mapKeys,
          nativeRulePrefixOk_map hf hty hrhs, structFieldTeleOf_map', structFieldIdxOf_map',
          structRuleBodyR_map]
        cases h₁ : Expr.stripLams (nP + 1 + n + nF) rhs with
        | none => rfl
        | some q =>
          obtain ⟨_, rbody⟩ := q
          obtain ⟨_, hrbody⟩ := Expr.stripLams_good hrhs h₁
          have hgen := structRuleBodyR_good hrc (structFieldTeleOf_good hcA.2 nP nF)
            (structFieldIdxOf_good hcA.2 nP nF) rlvls pw nP n nF j (recIdxOf ks)
            (teleOf := structFieldTeleOf cA.type nP nF)
          simp only [Option.map_some, Expr.mapTele, ← Expr.mapKeys_resetMeta,
            Expr.mapKeys_beq hf hrbody hgen.resetMeta]

end Ix.Kernel
