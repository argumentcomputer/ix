module

public import IxC.Kernel.Rules.Rel
public import IxC.Kernel.Rules.TransportKit
public import IxC.Kernel.Rules.NatOffset

@[expose] public section

/-!
# Transport of derivations: weakening and renaming (lane l5)

The six relations of the rules tier move along a **transport**: an extension of
the environment (`EnvExt env env'`) together with a renaming of free variables
`ρ` that is strictly increasing, and a map of opening depths `δ` that agrees
with `ρ` at the depths the derivation opens binders (`ok`). A derivation at an
admissible depth `d` becomes one at `δ d` over `env'`, its terms renamed
(`Expr.renFV ρ`).

Two instances:

* **environment weakening** (`Transport.weaken`): `ρ` and `δ` the identity.
  Typing a theorem's value where it is unfolded (`Red.deltaThm`'s premises) reads
  the theorem's own check in a later environment.
* **top weakening, W2** (`Transport.lift`): the variables from `p` on move up by
  `g` (`ρ i = i` below `p`, `i + g` from `p`), at depths from `p`. IxVM's context
  lowering checks a subterm opened at depth `p = d - g` and uses the result at
  depth `d`. With `p = 0` it lifts a closed derivation to any depth. The stored
  terms must be closed (`StoreClosed`), as an installed environment's are.

**What a transport needs** (`Transport`): the depth bookkeeping, the extension,
and either the identity renaming or closed stored terms. Every rule's premises
are then transported premise by premise; the helpers they name commute with the
renaming and are monotone along the extension (`Rules/TransportKit.lean`).
-/

namespace Ix.Kernel.Rules

open Ix.Kernel.Expr (renFV renFV_instantiate1 getAppArgs_renFV getAppFn_renFV_const
  renFV_mkAppN getD_map_renFV lamPw_renFV looseBVarsBounded_renFV wscopedB_renFV
  fvarLeaves_sub_renFV fvarLeaves_all_renFV renFV_natLitToConstructor
  renFV_strLitToConstructor renFV_of_natOpResult renFV_abstract1 piResidual_renFV
  renFV_instantiateLevelParams_closed renFV_of_id renFV_instSpine renFV_instantiateList)

/-- **A transport of derivations** from `env` to `env'`, renaming free variables
by `ρ` and opening depths by `δ`, at the admissible depths `ok`. -/
structure Transport (ρ δ : Nat → Nat) (ok : Nat → Prop) (env env' : Env md) : Prop where
  mono : ∀ {i j : Nat}, i < j → ρ i < ρ j
  ok_succ : ∀ {D : Nat}, ok D → ok (D + 1)
  δ_succ : ∀ {D : Nat}, ok D → δ (D + 1) = δ D + 1
  open_eq : ∀ {D : Nat}, ok D → ρ D = δ D
  lt : ∀ {D i : Nat}, ok D → i < D → ρ i < δ D
  ext : EnvExt env env'
  store : (∀ i, ρ i = i) ∨ StoreClosed env

namespace Transport

variable {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}

theorem inj (hT : Transport ρ δ ok env env') {i j : Nat} (h : ρ i = ρ j) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (Nat.ne_of_lt (hT.mono hij))
  · exact hij
  · exact absurd h (Nat.ne_of_gt (hT.mono hij))

/-- Opening a binder at an admissible depth commutes with the transport. -/
theorem renFV_open (hT : Transport ρ δ ok env env') {d : Nat} (hd : ok d) (b ty : Expr md) :
    (b.instantiate1 (.fvar d ty)).renFV ρ =
      (b.renFV ρ).instantiate1 (.fvar (δ d) (ty.renFV ρ)) := by
  rw [renFV_instantiate1]
  show (b.renFV ρ).instantiate1 (.fvar (ρ d) (ty.renFV ρ)) 0 = _
  rw [hT.open_eq hd]

theorem renFV_fvar_open (hT : Transport ρ δ ok env env') {d : Nat} (hd : ok d) (ty : Expr md) :
    (Expr.fvar d ty).renFV ρ = .fvar (δ d) (ty.renFV ρ) := by
  show Expr.fvar (ρ d) (ty.renFV ρ) = _
  rw [hT.open_eq hd]

/-- A level instantiation of a closed (or unrenamed) stored term is fixed. -/
theorem fix_of (hT : Transport ρ δ ok env env') {e : Expr md}
    (hc : StoreClosed env → e.hasFvar = false)
    (lps : List LevelParam) (us : List Level) :
    (e.instantiateLevelParams lps us).renFV ρ = e.instantiateLevelParams lps us := by
  rcases hT.store with hid | hs
  · exact renFV_of_id hid _
  · exact renFV_instantiateLevelParams_closed lps us (hc hs)

theorem fixType (hT : Transport ρ δ ok env env') {k : Key md} {c : ConstantInfo md}
    {cv : ConstantVal md} (hf : env.find? k = some c) (hc : c.toConstantVal = cv)
    (lps : List LevelParam) (us : List Level) :
    (cv.type.instantiateLevelParams lps us).renFV ρ = cv.type.instantiateLevelParams lps us :=
  hT.fix_of (fun hs => hc ▸ hs.type hf) lps us

theorem fixRhs (hT : Transport ρ δ ok env env') {k : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (hf : env.find? k = some (.recInfo cv mI rP rules))
    {rl : RecRule md} (hrl : rl ∈ rules) (lps : List LevelParam) (us : List Level) :
    (rl.rhs.instantiateLevelParams lps us).renFV ρ = rl.rhs.instantiateLevelParams lps us :=
  hT.fix_of (fun hs => (hs.rhs hf rl hrl).1) lps us

theorem comparands_fst (rl : RecRule md) (lps : List LevelParam) (us : List Level)
    (cvjLps : List LevelParam) (args : List (Expr md)) (rP : Nat) :
    (recFireComparands rl lps us cvjLps (args.map (renFV ρ)) rP).1 =
      (recFireComparands rl lps us cvjLps args rP).1 := by
  unfold recFireComparands
  split <;> rfl

theorem comparands_snd (hT : Transport ρ δ ok env env') {k : Key md} {cv : ConstantVal md}
    {mI rP' : Nat} {rules : List (RecRule md)} (hf : env.find? k = some (.recInfo cv mI rP' rules))
    {rl : RecRule md} (hrl : rl ∈ rules) (lps : List LevelParam) (us : List Level)
    (cvjLps : List LevelParam) (args : List (Expr md)) (rP : Nat) :
    (recFireComparands rl lps us cvjLps (args.map (renFV ρ)) rP).2 =
      (recFireComparands rl lps us cvjLps args rP).2.map (renFV ρ) := by
  unfold recFireComparands
  split
  · next lvls pins hfire =>
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp]
    rw [renFV_instSpine, List.map_take,
      hT.fix_of (e := p) (fun hs => (hs.rhs hf rl hrl).2 lvls pins hfire p hp) lps us]
  · simp only [List.map_take]

theorem typeAt (hT : Transport ρ δ ok env env') {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hent : env.findProj? sn i = some entry) (us : List Level) (targs : List (Expr md))
    (pe : Expr md) :
    (entry.typeAt us targs pe).renFV ρ = entry.typeAt us (targs.map (renFV ρ)) (pe.renFV ρ) := by
  unfold ProjEntry.typeAt
  rw [renFV_instantiateList _ _ (Nat.le_refl _),
    hT.fix_of (e := entry.body) (fun hs => hs.proj hent) entry.levelParams us]
  simp [List.map_reverse]

theorem unfold (hT : Transport ρ δ ok env env') {e e' : Expr md}
    (hu : unfoldDefinition env e = some e') :
    unfoldDefinition env' (e.renFV ρ) = some (e'.renFV ρ) := by
  unfold unfoldDefinition at hu ⊢
  split at hu
  · rename_i n us hfn
    cases hf : env.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some c =>
      rw [hf] at hu
      cases c with
      | defnInfo cv value hint =>
        dsimp only at hu
        split at hu
        · next hlen =>
          obtain rfl := Option.some.inj hu
          rw [getAppFn_renFV_const hfn]
          dsimp only
          rw [hT.ext.find hf]
          dsimp only
          rw [if_pos hlen, renFV_mkAppN, hT.fix_of (e := value) (fun hs => hs.defn hf),
            getAppArgs_renFV]
        · exact nomatch hu
      | _ => exact nomatch hu
  · exact nomatch hu

theorem etaProjs_tr (hT : Transport ρ δ ok env env') {T : Key md} {cvT : ConstantVal md}
    {caps : IndCaps md} (hind : env.find? T = some (.indInfo cvT caps)) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    (etaProjs env T us targs b nF).map (renFV ρ) =
      etaProjs env' T us (targs.map (renFV ρ)) (b.renFV ρ) nF := by
  rw [hT.ext.etaProjs_eq hind, Ix.Kernel.etaProjs_renFV]

theorem etaFabArgsE_tr (hT : Transport ρ δ ok env env') {T : Key md} {cvT : ConstantVal md}
    {caps : IndCaps md} (hind : env.find? T = some (.indInfo cvT caps)) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    (etaFabArgsE env T us targs b nF).map (renFV ρ) =
      etaFabArgsE env' T us (targs.map (renFV ρ)) (b.renFV ρ) nF := by
  unfold etaFabArgsE
  rw [List.map_append, hT.etaProjs_tr hind]

theorem wscoped (hT : Transport ρ δ ok env env') {d : Nat} (hd : ok d) {e : Expr md}
    (h : e.wscopedB d = true) : (e.renFV ρ).wscopedB (δ d) = true :=
  wscopedB_renFV hT.mono e (fun _ hi => hT.lt hd hi) h

theorem lbb {e : Expr md} (h : e.looseBVarsBounded 0 = true) :
    (e.renFV ρ).looseBVarsBounded 0 = true := by
  rw [looseBVarsBounded_renFV]; exact h

end Transport

/-! ## The transport -/

mutual

/-- **A reduction, transported.** -/
theorem red_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → ok d →
      Red env' (δ d) (e.renFV ρ) (e'.renFV ρ)
  | _, _, _, .refl, _ => .refl
  | _, _, _, .trans h₁ h₂, hd => .trans (red_tr hT h₁ hd) (red_tr hT h₂ hd)
  | _, _, _, .appFn h, hd => .appFn (red_tr hT h hd)
  | _, _, _, .projArg h, hd => .projArg (red_tr hT h hd)
  | _, _, _, .appArg h, hd => .appArg (red_tr hT h hd)
  | _, _, _, .betaGate hnev, _ => by
    rw [renFV_instantiate1]
    exact .betaGate hnev
  | _, _, _, .beta hta hd', hd => by
    rw [renFV_instantiate1]
    exact .beta (infer_tr hT hta hd) (defEq_tr hT hd' hd)
  | _, _, _, .delta hu, _ => .delta (hT.unfold hu)
  | _, _, _, .deltaThm (us := us) (cv := cv) (value := value) hf hlen hvf hvb hinf hde hinfT
      hred hz, hd => by
    have hV := renFV_instantiateLevelParams_closed (ρ := ρ) cv.levelParams us hvf
    have i1 := infer_tr hT hinf hd
    have d1 := defEq_tr hT hde hd
    have i2 := infer_tr hT hinfT hd
    rw [hV] at i1
    rw [hT.fixType (cv := cv) hf rfl] at d1 i2
    rw [hV]
    exact .deltaThm (hT.ext.find hf) hlen hvf hvb i1 d1 i2 (red_tr hT hred hd) hz
  | _, _, _, .eqProof hhead hfE hp hwp hbp hlp ha hda hb hdb hTT hred hv, hd =>
    .eqProof (getAppFn_renFV_const hhead) (hT.ext.find hfE) (infer_tr hT hp hd)
      (hT.wscoped hd hwp) (Transport.lbb hbp) (fvarLeaves_sub_renFV hlp)
      (infer_tr hT ha hd) (defEq_tr hT hda hd) (infer_tr hT hb hd) (defEq_tr hT hdb hd)
      (infer_tr hT hTT hd) (red_tr hT hred hd) hv
  | _, _, _, .natLit h, _ => by
    rw [renFV_natLitToConstructor]
    exact .natLit (hT.ext.natLitSupported_mono h)
  | _, _, _, .strLit h, _ => by
    rw [renFV_strLitToConstructor]
    exact .strLit (hT.ext.strLitSupported_mono h)
  | _, _, _, .natSucc hsup hw hn, hd =>
    .natSucc (hT.ext.natLitSupported_mono hsup) (red_tr hT hw hd)
      (by rw [rawNatLit?_renFV]; exact hn)
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr, hd => by
    rw [renFV_of_natOpResult hr]
    exact .natOp hc (hT.ext.natOpStored_mono hst) (red_tr hT hwa hd)
      (by rw [rawNatLit?_renFV]; exact hn₁) (red_tr hT hwb hd)
      (by rw [rawNatLit?_renFV]; exact hn₂) hr
  | _, _, _, .natAddSucc (us := us) (b := b) (k := k) hs ht, _ => by
    show Red env' _ (.app (.app (.const natAddName us) (b.renFV ρ)) (.lit (.natVal (k + 1))))
      (.app (.const natSuccName []) ((natAddLit b k).renFV ρ))
    rw [natAddLit_renFV]
    exact .natAddSucc (hT.ext.natLitSupported_mono hs) (hT.ext.opt_mono (p := natAddTyOk) ht rfl)
  | _, _, _, .natAddZero hs ht hw hn, hd =>
    .natAddZero (hT.ext.natLitSupported_mono hs) (hT.ext.opt_mono (p := natAddTyOk) ht rfl)
      (red_tr hT hw hd) (by rw [rawNatLit?_renFV]; exact hn)
  | _, _, _, .proj (cvC := cvC) hent hhead hi hlen hus hfire hctor hcerts, hd => by
    have hc := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvC) hctor rfl, ← getAppArgs_renFV] at hc
    rw [← getD_map_renFV, ← getAppArgs_renFV]
    exact .proj (hT.ext.findProj? hent) (getAppFn_renFV_const hhead) hi
      (by rw [getAppArgs_renFV, List.length_map]; exact hlen) hus hfire (hT.ext.find hctor) hc
  | _, _, _, .iota (e := e) (us := us) (cv := cv) (rP := rP) (rules := rules)
      (major := major) (cvj := cvj) (rl := rl)
      hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv hparams hcertR hcertC hres
      hidx, hd => by
    have hrl : rl ∈ rules := List.mem_of_find?_eq_some hrule
    have hgoal : (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)).renFV ρ =
        Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          ((e.renFV ρ).getAppArgs.take rP ++ (major.renFV ρ).getAppArgs.drop rl.ctorParams) := by
      rw [renFV_mkAppN, hT.fixRhs hrec hrl, getAppArgs_renFV, getAppArgs_renFV, List.map_append,
        List.map_take, List.map_drop]
    rw [hgoal]
    have hmaj := red_tr hT hmajor hd
    rw [← getD_map_renFV, ← getAppArgs_renFV] at hmaj
    have hcR := certs_tr hT hcertR hd
    rw [hT.fixType (cv := cv) hrec rfl, List.map_append, List.map_take, ← getAppArgs_renFV] at hcR
    have hcC := certs_tr hT hcertC hd
    rw [hT.fixType (cv := cvj) hctor rfl, ← getAppArgs_renFV] at hcC
    exact .iota (getAppFn_renFV_const hhead) (hT.ext.find hrec)
      (by rw [getAppArgs_renFV, List.length_map]; exact hlen) hus hmaj
      (getAppFn_renFV_const hmhead) (hT.ext.find hctor) hrule
      (by rw [getAppArgs_renFV, List.length_map]; exact hmlen) hfire
      (by rw [getAppArgs_renFV, Transport.comparands_fst]; exact hlv)
      (fun hc => by
        have h := defEqList_tr hT (hparams hc) hd
        rw [List.map_take, ← getAppArgs_renFV,
          ← hT.comparands_snd hrec hrl, ← getAppArgs_renFV] at h
        exact h)
      hcR hcC
      (fun hne => by
        have h := piResidual_renFV (ρ := ρ) _ _ _ (hres hne)
        rw [hT.fixType (cv := cvj) hctor rfl, ← getAppArgs_renFV] at h
        exact h)
      (fun hne => by
        have h := defEqList_tr hT (hidx hne) hd
        rw [List.map_drop, List.map_drop, List.map_take, ← getAppArgs_renFV,
          ← getAppArgs_renFV] at h
        exact h)
  | _, _, _, .rescueK (cvj := cvj)
      hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws hb hlv' hcerts htf hdt hpi, hd => by
    have hcs := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvj) hctor rfl, List.map_take, ← getAppArgs_renFV] at hcs
    exact .rescueK (hT.ext.find hrec) hk (hT.ext.find hctor) hres (hT.ext.find hind)
      (infer_tr hT htm hd) (red_tr hT htmaj hd) (getAppFn_renFV_const hthead) hlv
      (by rw [getAppArgs_renFV, List.length_map]; exact hnP)
      (by rw [hfab, renFV_mkAppN, getAppArgs_renFV, List.map_take]; rfl)
      (hT.wscoped hd hws) (Transport.lbb hb) (fvarLeaves_all_renFV hlv') hcs
      (infer_tr hT htf hd) (defEq_tr hT hdt hd) (defEq_tr hT hpi hd)
  | _, _, _, .rescueEta (major := major) (tmaj := tmaj) (cvj := cvj)
      (ust := ust) (caps := caps) hrec heta hctor hres hind htm htmaj hthead hlen
      hlv hnz hfab hws hb hlv' hcerts hproj hpi, hd => by
    have hargs := hT.etaFabArgsE_tr hind ust tmaj.getAppArgs major caps.etaFields
    rw [← getAppArgs_renFV] at hargs
    have hcs := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvj) hctor rfl, hargs] at hcs
    exact .rescueEta (hT.ext.find hrec) heta (hT.ext.find hctor) hres (hT.ext.find hind)
      (infer_tr hT htm hd) (red_tr hT htmaj hd) (getAppFn_renFV_const hthead)
      (by rw [getAppArgs_renFV, List.length_map]; exact hlen) hlv hnz
      (by rw [hfab, renFV_mkAppN, hargs]; rfl)
      (hT.wscoped hd hws) (Transport.lbb hb) (fvarLeaves_all_renFV hlv') hcs
      (fun hno => by
        rw [hT.ext.towerSlotsAll_eq hind] at hno
        have h := etaProjCerts_tr hT (hproj hno) hd
        rw [← getAppArgs_renFV] at h
        exact h)
      (defEq_tr hT hpi hd)
  | _, _, _, .rescueAnd (major := major) (tmaj := tmaj) (cvj := cvj)
      hrec hctor hres hind htm htmaj hthead hlen hlv hslots hfab hws hb hlv' hcerts htf hdt hpi,
      hd => by
    have hargs :
        (tmaj.getAppArgs ++ [Expr.proj andName 0 major, Expr.proj andName 1 major]).map (renFV ρ)
        = (tmaj.renFV ρ).getAppArgs ++
          [Expr.proj andName 0 (major.renFV ρ), Expr.proj andName 1 (major.renFV ρ)] := by
      rw [List.map_append, getAppArgs_renFV]
      rfl
    have hcs := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvj) hctor rfl, hargs] at hcs
    exact .rescueAnd (hT.ext.find hrec) (hT.ext.find hctor) hres (hT.ext.find hind)
      (infer_tr hT htm hd) (red_tr hT htmaj hd) (getAppFn_renFV_const hthead)
      (by rw [getAppArgs_renFV, List.length_map]; exact hlen) hlv
      (fun j hj => by
        obtain ⟨e, hfe, hct, hnP, hnF, hfire⟩ := hslots j hj
        exact ⟨e, hT.ext.findProj? hfe, hct, hnP, hnF, hfire⟩)
      (by rw [hfab, renFV_mkAppN, hargs]; rfl)
      (hT.wscoped hd hws) (Transport.lbb hb) (fvarLeaves_all_renFV hlv') hcs
      (infer_tr hT htf hd) (defEq_tr hT hdt hd) (defEq_tr hT hpi hd)

/-- **A conversion, transported.** -/
theorem defEq_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → ok d →
      DefEq env' (δ d) (a.renFV ρ) (b.renFV ρ)
  | _, _, _, .refl, _ => .refl
  | _, _, _, .symm h, hd => .symm (defEq_tr hT h hd)
  | _, _, _, .redL hr h, hd => .redL (red_tr hT hr hd) (defEq_tr hT h hd)
  | _, _, _, .sort h, _ => .sort h
  | _, _, _, .fvar, _ => .fvar
  | _, _, _, .const h, _ => .const h
  | _, _, _, .natZero, _ => .natZero
  | _, _, _, .natSucc h, hd => .natSucc (defEq_tr hT h hd)
  | _, _, _, .natOffset (ba := ba) (bb := bb) (k := k) hs ht ha hb h, hd =>
    .natOffset (ba := ba.renFV ρ) (bb := bb.renFV ρ) (k := k) (hT.ext.natLitSupported_mono hs)
      (hT.ext.opt_mono (p := natAddTyOk) ht rfl) (by rw [natOffsetOf_renFV, ha]; rfl)
      (by rw [natOffsetOf_renFV, hb]; rfl) (defEq_tr hT h hd)
  | _, _, _, .forallE hty hbody hpw hc, hd => by
    have h2 := defEq_tr hT hbody (hT.ok_succ hd)
    simp only [hT.δ_succ hd, hT.renFV_open hd] at h2
    exact .forallE (defEq_tr hT hty hd) h2 hpw hc
  | _, _, _, .lam hty hbody hpw hc, hd => by
    have h2 := defEq_tr hT hbody (hT.ok_succ hd)
    simp only [hT.δ_succ hd, hT.renFV_open hd] at h2
    exact .lam (defEq_tr hT hty hd) h2 hpw hc
  | _, _, _, .app hf ha, hd => .app (defEq_tr hT hf hd) (defEq_tr hT ha hd)
  | _, _, _, .proj h, hd => .proj (defEq_tr hT h hd)
  | d, _, _, .eta (b := b) (ty₁ := ty₁) htb hwtb hty hbody hpw hc, hd => by
    have h2 := defEq_tr hT hbody (hT.ok_succ hd)
    have hap : (Expr.app b (.fvar d ty₁)).renFV ρ = .app (b.renFV ρ) ((Expr.fvar d ty₁).renFV ρ) :=
      rfl
    rw [hap, hT.renFV_fvar_open hd] at h2
    simp only [hT.δ_succ hd, hT.renFV_open hd] at h2
    exact .eta (infer_tr hT htb hd) (red_tr hT hwtb hd) (defEq_tr hT hty hd) h2 hpw hc
  | _, _, _, .proofFast h₁ h₂, _ =>
    .proofFast (by rw [isProofFast_renFV]; exact hT.ext.isProofFast_mono h₁)
      (by rw [isProofFast_renFV]; exact hT.ext.isProofFast_mono h₂)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0, hd =>
    .proofIrrel (infer_tr hT hta hd) (infer_tr hT htta hd) (red_tr hT hu hd) hu0
      (infer_tr hT htb hd) (infer_tr hT httb hd) (red_tr hT hv hd) hv0
  | _, _, _, .unitLike hta hwta hua htb hwtb hub, hd =>
    .unitLike (infer_tr hT hta hd) (red_tr hT hwta hd)
      (by rw [isUnitLikeTy_renFV]; exact hT.ext.isUnitLikeTy_mono hua)
      (infer_tr hT htb hd) (red_tr hT hwtb hd)
      (by rw [isUnitLikeTy_renFV]; exact hT.ext.isUnitLikeTy_mono hub)
  | _, _, _, .structEta (cvT := cvT) htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT
      hresc htlen hlv hlps hslots hus hcerts hproj hparams hfields, hd => by
    have hcs := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvT) hind rfl, ← getAppArgs_renFV] at hcs
    have hp := defEqList_tr hT hparams hd
    rw [List.map_take, ← getAppArgs_renFV, ← getAppArgs_renFV] at hp
    have hf := defEqList_tr hT hfields hd
    rw [List.map_drop, ← getAppArgs_renFV, hT.etaProjs_tr hind, ← getAppArgs_renFV] at hf
    refine .structEta (infer_tr hT htb hd) (red_tr hT hwtb hd) (getAppFn_renFV_const hhead)
      (hT.ext.find hctor) (by rw [getAppArgs_renFV, List.length_map]; exact hlen)
      (getAppFn_renFV_const hthead) (hT.ext.find hind) heta hetaCtor hresT hresc
      (by rw [getAppArgs_renFV, List.length_map]; exact htlen) hlv hlps ?_ hus hcs
      (fun hno => by
        rw [hT.ext.towerSlotsAll_eq hind] at hno
        have h := etaProjCerts_tr hT (hproj hno) hd
        rw [← getAppArgs_renFV] at h
        exact h) hp hf
    rw [hT.ext.towerSlotsAll_eq hind]
    rcases Bool.or_eq_true_iff.mp hslots with h | h
    · rw [h]; rfl
    · rw [hT.ext.recSlotsAll_mono h, Bool.or_true]
  | _, _, _, .structUnit (cvT := cvT) hta hwta hthead hind hunit hresT htlen hlv htb
      hwtb hd' hcerts, hd => by
    have hcs := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvT) hind rfl, ← getAppArgs_renFV] at hcs
    exact .structUnit (infer_tr hT hta hd) (red_tr hT hwta hd) (getAppFn_renFV_const hthead)
      (hT.ext.find hind) hunit hresT (by rw [getAppArgs_renFV, List.length_map]; exact htlen)
      hlv (infer_tr hT htb hd) (red_tr hT hwtb hd) (defEq_tr hT hd' hd) hcs

/-- **An inference, transported.** -/
theorem infer_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → ok d →
      Infer env' g (δ d) (e.renFV ρ) (t.renFV ρ)
  | _, _, _, _, .sort, _ => .sort
  | _, _, _, _, .fvar h, hd => .fvar (hT.lt hd h)
  | _, _, _, _, .const (ci := ci) hf htower hus, _ => by
    rw [hT.fixType (cv := ci.toConstantVal) hf rfl]
    exact .const (hT.ext.find hf) htower hus
  | _, _, _, _, .natLit h, _ => .natLit (hT.ext.natLitSupported_mono h)
  | _, _, _, _, .strLit h, _ => .strLit (hT.ext.strLitSupported_mono h)
  | _, _, _, _, .forallE hs hu hbs hv hz, hd => by
    have ibs := infer_tr hT hbs (hT.ok_succ hd)
    have rv := red_tr hT hv (hT.ok_succ hd)
    simp only [hT.δ_succ hd, hT.renFV_open hd] at ibs rv
    exact .forallE (infer_tr hT hs hd) (red_tr hT hu hd) ibs rv hz
  | _, d, _, _, .lam (ty := ty) (bt := bt) (mb := mb) hs hu hbt hchain hbtt hv hz,
      hd => by
    have ibt := infer_tr hT hbt (hT.ok_succ hd)
    simp only [hT.δ_succ hd, hT.renFV_open hd] at ibt
    have habs : (Expr.forallE ty (bt.abstract1 d) mb).renFV ρ =
        .forallE (ty.renFV ρ) ((bt.renFV ρ).abstract1 (δ d)) mb := by
      show Expr.forallE (ty.renFV ρ) ((bt.abstract1 d 0).renFV ρ) mb = _
      rw [renFV_abstract1 hT.inj d bt 0, hT.open_eq hd]
    rw [habs]
    exact .lam (fun hg => infer_tr hT (hs hg) hd) (fun hg => red_tr hT (hu hg) hd) ibt
      (fun pwI h => hchain pwI (by rwa [lamPw_renFV] at h))
      (fun h => by
        have := infer_tr hT (hbtt (by rwa [lamPw_renFV] at h)) (hT.ok_succ hd)
        rwa [hT.δ_succ hd] at this)
      (fun h => by
        have := red_tr hT (hv (by rwa [lamPw_renFV] at h)) (hT.ok_succ hd)
        rwa [hT.δ_succ hd] at this)
      (fun h => hz (by rwa [lamPw_renFV] at h))
  | _, _, _, _, .app htf hw hta hd', hd => by
    rw [renFV_instantiate1]
    exact .app (infer_tr hT htf hd) (red_tr hT hw hd) (infer_tr hT hta hd) (defEq_tr hT hd' hd)
  | _, _, _, _, .appSkip htf hw hnev, hd => by
    rw [renFV_instantiate1]
    exact .appSkip (infer_tr hT htf hd) (red_tr hT hw hd) hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop, hd => by
    rw [hT.typeAt hent, ← getAppArgs_renFV]
    exact .proj (infer_tr hT htpe hd) (red_tr hT hte hd) (getAppFn_renFV_const hhead)
      (hT.ext.findProj? hent) (by rw [getAppArgs_renFV, List.length_map]; exact hlen) hus hprop

/-- **A telescope certificate, transported.** -/
theorem certs_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → ok d →
        Certs env' (δ d) lic (ty.renFV ρ) (args.map (renFV ρ))
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .skip hlic hnev hrest, hd => by
    have h := certs_tr hT hrest hd
    rw [renFV_instantiate1] at h
    exact .skip hlic hnev h
  | _, _, _, _, .cert hta hd' hrest, hd => by
    have h := certs_tr hT hrest hd
    rw [renFV_instantiate1] at h
    exact .cert (infer_tr hT hta hd) (defEq_tr hT hd' hd) h

/-- **A pairwise conversion, transported.** -/
theorem defEqList_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → ok d →
      DefEqList env' (δ d) (as.map (renFV ρ)) (bs.map (renFV ρ))
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hd => .cons (defEq_tr hT h hd) (defEqList_tr hT hs hd)

/-- **The per-field certificates of a projection-function family, transported.** -/
theorem etaProjCerts_tr {ρ δ : Nat → Nat} {ok : Nat → Prop} {env env' : Env md}
    (hT : Transport ρ δ ok env env') :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → ok d →
        EtaProjCerts env' (δ d) T us' (targs.map (renFV ρ)) (b.renFV ρ) lpsT idxs
  | _, _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, _, .cons (cvp := cvp) hf hlps hstrip hcerts hrest, hd => by
    have hc := certs_tr hT hcerts hd
    rw [hT.fixType (cv := cvp) hf rfl, List.map_append] at hc
    exact .cons (hT.ext.find hf) hlps (by rw [List.length_map]; exact hstrip) hc
      (etaProjCerts_tr hT hrest hd)

end

/-! ## The two instances -/

namespace Transport

/-- **Environment weakening**: the identity renaming along an extension. -/
theorem weaken {env env' : Env md} (h : EnvExt env env') :
    Transport (fun i => i) (fun d => d) (fun _ => True) env env' where
  mono := id
  ok_succ := fun _ => trivial
  δ_succ := fun _ => rfl
  open_eq := fun _ => rfl
  lt := fun _ hi => hi
  ext := h
  store := .inl fun _ => rfl

/-- **Top weakening (W2)**: the variables from `p` on move up by `g`, at the depths
from `p`, along an extension of an environment whose stored terms are closed. -/
theorem lift {env env' : Env md} (hx : EnvExt env env') (hs : StoreClosed env) (p g : Nat) :
    Transport (fun i => if i < p then i else i + g) (fun d => d + g) (fun d => p ≤ d) env env'
    where
  mono := fun {i j} hij =>
    show (if i < p then i else i + g) < (if j < p then j else j + g) by
      by_cases hi : i < p <;> by_cases hj : j < p <;> simp [hi, hj] <;> omega
  ok_succ := fun {D} (h : p ≤ D) => show p ≤ D + 1 by omega
  δ_succ := fun {D} _ => show D + 1 + g = D + g + 1 by omega
  open_eq := fun {D} (h : p ≤ D) =>
    show (if D < p then D else D + g) = D + g by simp [Nat.not_lt.mpr h]
  lt := fun {D i} (h : p ≤ D) (hi : i < D) =>
    show (if i < p then i else i + g) < D + g by
      by_cases hip : i < p <;> simp [hip] <;> omega
  ext := hx
  store := .inr hs

end Transport

/-! ## Corollaries -/

theorem Infer.weaken {env env' : Env md} (h : EnvExt env env') {g : Grade} {d : Nat}
    {e t : Expr md} (hi : Infer env g d e t) : Infer env' g d e t := by
  have := infer_tr (Transport.weaken h) hi trivial
  simpa only [renFV_of_id (fun _ => rfl)] using this

theorem DefEq.weaken {env env' : Env md} (h : EnvExt env env') {d : Nat} {a b : Expr md}
    (hi : DefEq env d a b) : DefEq env' d a b := by
  have := defEq_tr (Transport.weaken h) hi trivial
  simpa only [renFV_of_id (fun _ => rfl)] using this

theorem Red.weaken {env env' : Env md} (h : EnvExt env env') {d : Nat} {e e' : Expr md}
    (hi : Red env d e e') : Red env' d e e' := by
  have := red_tr (Transport.weaken h) hi trivial
  simpa only [renFV_of_id (fun _ => rfl)] using this

/-- The renaming `lift` uses fixes a term whose free variables are below `p`. -/
theorem renFV_lift_of_wscoped {p g : Nat} :
    ∀ {e : Expr md} {D : Nat}, D ≤ p → e.wscopedB D = true →
      e.renFV (fun i => if i < p then i else i + g) = e := by
  intro e
  induction e with
  | fvar i ty ih =>
    intro D hD h
    simp only [Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hip : i < p := Nat.lt_of_lt_of_le h1 hD
    show Expr.fvar (if i < p then i else i + g) (ty.renFV _) = _
    rw [if_pos hip, ih (Nat.le_of_lt hip) h2]
  | app f a ihf iha =>
    intro D hD h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    simp only [renFV, ihf hD h.1, iha hD h.2]
  | lam ty b m iht ihb =>
    intro D hD h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    simp only [renFV, iht hD h.1, ihb hD h.2]
  | forallE ty b m iht ihb =>
    intro D hD h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    simp only [renFV, iht hD h.1, ihb hD h.2]
  | letE ty v b l iht ihv ihb =>
    intro D hD h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    simp only [renFV, iht hD h.1.1, ihv hD h.1.2, ihb hD h.2]
  | proj s i e ih =>
    intro D hD h
    simp only [Expr.wscopedB] at h
    simp only [renFV, ih hD h]
  | bvar | sort | const | lit => intro _ _ _; rfl

/-- **W2 for inference**: a derivation at depth `p` (IxVM's lowered context),
weakened along an extension, holds at depth `p + g` with the variables opened
from `p` on moved up by `g`. A subject scoped below `p` is unchanged
(`renFV_lift_of_wscoped`). -/
theorem Infer.lift {env env' : Env md} (hx : EnvExt env env') (hs : StoreClosed env)
    {g' : Grade} {p g : Nat} {e t : Expr md} (hi : Infer env g' p e t) :
    Infer env' g' (p + g) (e.renFV (fun i => if i < p then i else i + g))
      (t.renFV (fun i => if i < p then i else i + g)) :=
  infer_tr (Transport.lift hx hs p g) hi (Nat.le_refl p)

/-- **W2 for conversion.** -/
theorem DefEq.lift {env env' : Env md} (hx : EnvExt env env') (hs : StoreClosed env)
    {p g : Nat} {a b : Expr md} (hi : DefEq env p a b) :
    DefEq env' (p + g) (a.renFV (fun i => if i < p then i else i + g))
      (b.renFV (fun i => if i < p then i else i + g)) :=
  defEq_tr (Transport.lift hx hs p g) hi (Nat.le_refl p)

/-- **W2 for reduction.** -/
theorem Red.lift {env env' : Env md} (hx : EnvExt env env') (hs : StoreClosed env)
    {p g : Nat} {e e' : Expr md} (hi : Red env p e e') :
    Red env' (p + g) (e.renFV (fun i => if i < p then i else i + g))
      (e'.renFV (fun i => if i < p then i else i + g)) :=
  red_tr (Transport.lift hx hs p g) hi (Nat.le_refl p)

end Ix.Kernel.Rules
