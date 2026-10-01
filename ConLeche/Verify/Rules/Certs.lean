module

public import ConLeche.Verify.Rules.Defs
public import ConLeche.Verify.Knot
import ConLeche.Rules.Derived
import ConLeche.Verify.InferLemmas

public section

/-!
# The certificate bridges (task #305, lane B1)

The helpers of `Core.lean` that several bodies call — the telescope
certificate, the list walk, the two proof-irrelevance tests, the three
structure certificates, η, the stuck cascade, the same-head
short-circuit, the `Bool.true` shortcut — each bridged at `fuel` from
the entry-point bridges at `fuel` (the helpers run the record
`pureFns .verified env fuel`, whose fields ARE the entry points at
`fuel`: `whnf_def`, `defeq_def`, `inferTypeIO_def`).

Each theorem's proof is the site's `Verify` inversion lemma
(`iotaCerts_step_inv_gate`, `defEqList_step_inv`, `proofIrrel_inv`,
`propIrrel_inv`, `structEtaCertWith_inv`, `structEtaCert_inv`,
`structUnitCert_inv`, `etaCert_inv`, `structEtaProjCerts_inv`,
`defeqSpine_inv`; `stuckIrrel` and `boolTrueShortcut` have none yet
and are inverted by hand as `Model/Steps/Stuck.lean`'s
`stuckIrrelFueled_of_claims` does) followed by the one rule.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- `iotaCerts` ⇒ `Certs` (`iotaCerts_step_inv_gate`; a licensed
`.never` slot lands on `Certs.skip`, a certified one on `Certs.cert`
through `inferTypeIO_bridge` and `hd`). -/
theorem iotaCerts_bridge (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel) :
    ∀ {d : Nat} {lic : Bool} {ty : Expr} {args : List Expr},
      iotaCertsFueled .verified env fuel d lic ty args = .ok true →
      Certs env d lic ty args := by
  intro d lic ty args
  induction args generalizing ty with
  | nil => intro _; exact .nil
  | cons arg rest ih =>
    match ty with
    | .forallE ty₀ body mb =>
      intro h
      rcases iotaCerts_step_inv_gate h with ⟨hg, hrest⟩ | ⟨ta, hta, hde, hrest⟩
      · rw [Bool.and_eq_true] at hg
        exact .skip hg.1 hg.2 (ih hrest)
      · exact .cert (inferTypeIO_bridge hio hta) (hd hde) (ih hrest)
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
    | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      intro h
      simp [iotaCertsFueled, iotaCerts, pure, Except.pure] at h

/-- `defEqList` ⇒ `DefEqList` (`defEqList_step_inv`). -/
theorem defEqList_bridge (hd : DefEqBridge env fuel) :
    ∀ {d : Nat} {as bs : List Expr},
      defEqListFueled .verified env fuel d as bs = .ok true →
      DefEqList env d as bs := by
  intro d as
  induction as with
  | nil =>
    intro bs h
    match bs with
    | [] => exact .nil
    | _ :: _ =>
      simp [defEqListFueled, defEqList, pure, Except.pure] at h
  | cons a as ih =>
    intro bs h
    match bs with
    | [] =>
      simp [defEqListFueled, defEqList, pure, Except.pure] at h
    | b :: bs =>
      obtain ⟨hab, hrest⟩ := defEqList_step_inv h
      exact .cons (hd hab) (ih hrest)

/-- `structEtaProjCerts` ⇒ `EtaProjCerts` (`structEtaProjCerts_inv`,
one `iotaCerts_bridge` per field). -/
theorem structEtaProjCerts_bridge (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) :
    ∀ {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {idxs : List Nat},
      structEtaProjCertsFueled .verified env fuel d T us' targs b lpsT idxs
        = .ok true →
      EtaProjCerts env d T us' targs b lpsT idxs := by
  intro d T us' targs b lpsT idxs h
  have hall := structEtaProjCerts_inv (mode := .verified) idxs h
  clear h
  induction idxs with
  | nil => exact .nil
  | cons i rest ih =>
    obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlps, hstrp, hic⟩ :=
      hall i (List.mem_cons_self ..)
    exact .cons hfp hlps hstrp (iotaCerts_bridge hd hio hic)
      (ih (fun j hj => hall j (List.mem_cons_of_mem _ hj)))

/-- `proofIrrel` ⇒ `DefEq.unitLike` or `DefEq.proofIrrel`
(`proofIrrel_inv`). -/
theorem proofIrrel_bridge (hw : WhnfBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : proofIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨ta, wta, hta, hwta, harm⟩ := proofIrrel_inv h
  rcases harm with ⟨hua, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · exact .unitLike (inferTypeIO_bridge hio hta) (hw hwta) hua
      (inferTypeIO_bridge hio htb) (hw hwtb) hub
  · exact .proofIrrel (inferTypeIO_bridge hio hta)
      (inferTypeIO_bridge hio hsta) (hw hwsta) huT
      (inferTypeIO_bridge hio htb) (inferTypeIO_bridge hio hstb)
      (hw hwstb) hvT

/-- `propIrrel` ⇒ `DefEq.proofFast` or `DefEq.proofIrrel`
(`propIrrel_inv`). -/
theorem propIrrel_bridge (hw : WhnfBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : propIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  rcases propIrrel_inv h with ⟨hfa, hfb⟩ |
    ⟨ta, sta, uT, tb, stb, vT, hta, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · exact .proofFast hfa hfb
  · exact .proofIrrel (inferTypeIO_bridge hio hta)
      (inferTypeIO_bridge hio hsta) (hw hwsta) huT
      (inferTypeIO_bridge hio htb) (inferTypeIO_bridge hio hstb)
      (hw hwstb) hvT

/-- **The η certificate's per-field telescope certificates**, at a
projection-function family: the `towerSlotsAll = false →` conjunct of
`structEtaCertWith_inv`, bridged one field at a time.  Both consumers
of `structEtaCertWith` need it as a premise — `DefEq.structEta` here,
`Red.rescueEta` at the η rescue (`majorToCtor`'s η branch runs the
same certificate at `a := fab`, `b := major`, `wtb := tmaj`) — so it
is a lemma of its own rather than a step inside the next one.  The
family's identity is the caller's (`hwfn`, `hfT`); the inversion's own
is reconciled against it. -/
theorem structEtaCertWith_projCerts_bridge (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel)
    {d : Nat} {a b wtb : Expr} {T : Name} {us' : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (hwfn : wtb.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (h : structEtaCertWithFueled .verified env fuel d a b wtb = .ok true) :
    towerSlotsAll env T caps.etaFields = false →
      EtaProjCerts env d T us' wtb.getAppArgs b cvT.levelParams
        (List.range caps.etaFields) := by
  obtain ⟨-, -, -, -, -, T₂, us₂, cvT₂, caps₂,
    -, -, -, hwfn₂, hfT₂, -, -, -, -, -, -, -, -, -, -, hproj, -⟩ :=
    structEtaCertWith_inv h
  rw [hwfn] at hwfn₂
  obtain ⟨rfl, rfl⟩ := Expr.const.inj hwfn₂
  rw [hfT] at hfT₂
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT₂)
  exact fun htw => structEtaProjCerts_bridge hd hio (hproj htw)

/-- `structEtaCertWith` at a given head-normal type ⇒ `DefEq.structEta`
(`structEtaCertWith_inv`, with `structEtaCertWith_projCerts_bridge`
for the per-field premise).  The two runs that produced `wtb` are the
caller's (`structEtaCert`'s own, or the η rescue's `tm`/`tmaj`), so
they are hypotheses here. -/
theorem structEtaCertWith_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b tb wtb : Expr}
    (htb : inferTypeIO .verified env fuel d b = .ok tb)
    (hwtb : whnf .verified env fuel d tb = .ok wtb)
    (h : structEtaCertWithFueled .verified env fuel d a b wtb = .ok true) :
    DefEq env d a b := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
    hfn, hfc, hlen, hwfn, hfT, heta, hctor, hresT, hresc, hplen, hulen,
    hlps, hslots, hus, hcertT, -, hpar, -, hfields⟩ :=
    structEtaCertWith_inv h
  exact .structEta (inferTypeIO_bridge hio htb) (hw hwtb) hfn hfc hlen hwfn hfT
    heta hctor hresT hresc hplen hulen hlps hslots hus
    (iotaCerts_bridge hd hio hcertT)
    (structEtaCertWith_projCerts_bridge hd hio hwfn hfT h)
    (defEqList_bridge hd hpar) (defEqList_bridge hd hfields)

/-- `structEtaCert` ⇒ `DefEq.structEta` (`structEtaCert_inv`, then
`structEtaCertWith_bridge`). -/
theorem structEtaCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : structEtaCertFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨tb, wtb, htb, hwtb, h'⟩ := structEtaCert_inv h
  exact structEtaCertWith_bridge hw hd hio htb hwtb h'

/-- `structUnitCert` ⇒ `DefEq.structUnit` (`structUnitCert_inv`). -/
theorem structUnitCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : structUnitCertFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb,
    hta, hwta, hwfn, hfT, hunit, hres, hplen, hulen, htb, hwtb, hde, hic⟩ :=
    structUnitCert_inv h
  exact .structUnit (inferTypeIO_bridge hio hta) (hw hwta) hwfn hfT hunit
    hres hplen hulen (inferTypeIO_bridge hio htb) (hw hwtb) (hd hde)
    (iotaCerts_bridge hd hio hic)

/-- `etaCert` ⇒ `DefEq.eta` (`etaCert_inv`; the annotation agreement is
the inversion's `verifiedChecks = true →` conjunct at `rfl`). -/
theorem etaCert_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {ty body b : Expr} {mb : BinderMeta}
    (h : etaCertFueled .verified env fuel d ty body mb b = .ok true) :
    DefEq env d (.lam ty body mb) b := by
  obtain ⟨tb, ty₂, fb, m₂, htb, hwtb, hdty, hdbody, hpw⟩ := etaCert_inv h
  exact .eta (inferTypeIO_bridge hio htb) (hw hwtb) (hd hdty) (hd hdbody)
    (hpw rfl)

/-- `stuckIrrel` ⇒ one of its four arms (`structEtaCert_bridge` twice —
the second through `DefEq.structEtaR` —, `structUnitCert_bridge`,
`proofIrrel_bridge`).  No inversion lemma exists for `stuckIrrel`
today; it is four `exceptBind_ok`s. -/
theorem stuckIrrel_bridge (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : stuckIrrelFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  dsimp only [stuckIrrelFueled] at h
  simp only [stuckIrrel, Bind.bind, Except.bind, structEtaCert_fold,
    structUnitCert_fold, proofIrrel_fold] at h
  cases h3 : structEtaCertFueled .verified env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true => exact structEtaCert_bridge hw hd hio h3
  | false =>
  cases h4 : structEtaCertFueled .verified env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true => exact .structEtaR (structEtaCert_bridge hw hd hio h4)
  | false =>
  cases h5 : structUnitCertFueled .verified env fuel d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok r5 =>
  rw [h5] at h
  dsimp only at h
  cases r5 with
  | true => exact structUnitCert_bridge hw hd hio h5
  | false => exact proofIrrel_bridge hw hio h

/-- `defeqSpine` ⇒ `DefEq.constSpine` (`defeqSpine_inv`). -/
theorem defeqSpine_bridge (hd : DefEqBridge env fuel)
    {d : Nat} {a b : Expr}
    (h : defeqSpineFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  obtain ⟨n, us, us', ha, hb, -, hus, hl⟩ := defeqSpine_inv h
  exact .constSpine ha hb hus (defEqList_bridge hd hl)

/-- `boolTrueShortcut` ⇒ `DefEq.boolTrue`. -/
theorem boolTrueShortcut_bridge (hw : WhnfBridge env fuel)
    {d : Nat} {a : Expr}
    (h : boolTrueShortcutFueled .verified env fuel d a = .ok true) :
    DefEq env d a (.const boolTrueName []) := by
  dsimp only [boolTrueShortcutFueled] at h
  simp only [boolTrueShortcut, Bind.bind, Except.bind, whnf_def] at h
  cases hwh : whnf .verified env fuel d a with
  | error err => rw [hwh] at h; exact nomatch h
  | ok w =>
  rw [hwh] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact .boolTrue (hw hwh) h

end ConLeche.Rules
