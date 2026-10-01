module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSound
import ConLeche.Model.Rules.IotaSound
import ConLeche.Model.Rules.DefEqSound
import ConLeche.Model.Rules.InferSound
import ConLeche.Model.Rules.CertsSound
import ConLeche.Rules.Derived

public section

/-!
# The soundness of derivations (task #305)

**Derivation ⇒ P currency**, by one mutual structural recursion over
the six relations.  Every case is one per-rule lemma applied to the
recursive calls — nothing semantic happens here, which is the whole
point: the per-rule lemmas are the proof lanes' deliverables, this
file is fixed, and it is what the recomposition consumes.

The one non-mechanical move is the λ rule's `hshape`: the chain case
of the codomain validation reads the SHAPE of the body's inferred type
off the premise derivation (`Infer.lam_shape`), which the per-rule
lemma cannot see.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

mutual

theorem red_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {e e' : Expr}, Red env d e e' → RedSem m φ d e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ =>
    Red.trans_sound (red_sound hin h₁) (red_sound hin h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound hin h)
  | _, _, _, .projArg h => Red.projArg_sound (red_sound hin h)
  | _, _, _, .betaGate hnev => Red.betaGate_sound hnev
  | _, _, _, .beta hta hd =>
    Red.beta_sound (infer_sound hin hta) (defeq_sound hin hd)
  | _, _, _, .delta h => Red.delta_sound hin h
  | _, _, _, .natLit h => Red.natLit_sound h
  | _, _, _, .strLit h => Red.strLit_sound h
  | _, _, _, .natSucc hsup hw hn =>
    Red.natSucc_sound hin hsup (red_sound hin hw) hn
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr =>
    Red.natOp_sound hin hc hst (red_sound hin hwa) hn₁ (red_sound hin hwb) hn₂ hr
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    Red.proj_sound hin hent hhead hi hlen hus hfire hctor (certs_sound hin hcerts)
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv
      hparams hcertR hcertC hres hidx =>
    Red.iota_sound hin hhead hrec hlen hus (red_sound hin hmajor) hmhead hctor
      hrule hmlen hfire hlv (fun hc => defEqList_sound hin (hparams hc))
      (certs_sound hin hcertR) (certs_sound hin hcertC) hres
      (fun hne => defEqList_sound hin (hidx hne))
  | _, _, _, .rescueK hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws
      hb hlv' hcerts htf hdt hpi =>
    Red.rescueK_sound hin hrec hk hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlv hnP hfab hws hb hlv'
      (certs_sound hin hcerts) (infer_sound hin htf) (defeq_sound hin hdt)
      (defeq_sound hin hpi)
  | _, _, _, .rescueEta hrec heta hctor hres hind htm htmaj hthead hlen hlv hnz
      hfab hws hb hlv' hcerts hproj hpi =>
    Red.rescueEta_sound hin hrec heta hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlen hlv hnz hfab hws hb hlv'
      (certs_sound hin hcerts)
      (fun hno => etaProjCerts_sound hin (hproj hno)) (defeq_sound hin hpi)
  | _, _, _, .rescueAnd hrec hctor hres hind htm htmaj hthead hlen hlv hslots
      hfab hws hb hlv' hcerts htf hdt hpi =>
    Red.rescueAnd_sound hin hrec hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlen hlv hslots hfab hws hb hlv'
      (certs_sound hin hcerts) (infer_sound hin htf) (defeq_sound hin hdt)
      (defeq_sound hin hpi)

theorem defeq_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {a b : Expr}, DefEq env d a b → DefEqSem m φ d a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound hin h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hin hr) (defeq_sound hin h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .fvar => DefEq.fvar_sound
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .natZero => DefEq.natZero_sound
  | _, _, _, .natSucc h => DefEq.natSucc_sound (defeq_sound hin h)
  | _, _, _, .forallE hty hbody hpw =>
    DefEq.forallE_sound (defeq_sound hin hty) (defeq_sound hin hbody) hpw
  | _, _, _, .lam hty hbody hpw =>
    DefEq.lam_sound (defeq_sound hin hty) (defeq_sound hin hbody) hpw
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hin hf) (defeq_sound hin ha)
  | _, _, _, .proj h => DefEq.proj_sound (defeq_sound hin h)
  | _, _, _, .eta htb hwtb hty hbody hpw =>
    DefEq.eta_sound (infer_sound hin htb) (red_sound hin hwtb)
      (defeq_sound hin hty) (defeq_sound hin hbody) hpw
  | _, _, _, .proofFast ha hb => DefEq.proofFast_sound hin ha hb
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    DefEq.proofIrrel_sound (infer_sound hin hta) (infer_sound hin htta)
      (red_sound hin hu) hu0 (infer_sound hin htb) (infer_sound hin httb)
      (red_sound hin hv) hv0
  | _, _, _, .unitLike hta hwta hua htb hwtb hub =>
    DefEq.unitLike_sound (infer_sound hin hta) (red_sound hin hwta) hua
      (infer_sound hin htb) (red_sound hin hwtb) hub
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT
      hresc htlen hlv hlps hslots hus hcerts hproj hparams hfields =>
    DefEq.structEta_sound hin (infer_sound hin htb) (red_sound hin hwtb) hhead
      hctor hlen hthead hind heta hetaCtor hresT hresc htlen hlv hlps hslots hus
      (certs_sound hin hcerts) (fun hno => etaProjCerts_sound hin (hproj hno))
      (defEqList_sound hin hparams) (defEqList_sound hin hfields)
  | _, _, _, .structUnit hta hwta hthead hind hunit hresT htlen hlv htb hwtb hd
      hcerts =>
    DefEq.structUnit_sound hin (infer_sound hin hta) (red_sound hin hwta) hthead
      hind hunit hresT htlen hlv (infer_sound hin htb) (red_sound hin hwtb)
      (defeq_sound hin hd) (certs_sound hin hcerts)

theorem infer_sound (hin : RulesInputs V m φ) :
    ∀ {g : Grade} {d : Nat} {e t : Expr}, Infer env g d e t → InferSem m φ g d e t
  | _, _, _, _, .sort => Infer.sort_sound
  | _, _, _, _, .fvar h => Infer.fvar_sound h
  | _, _, _, _, .const hf htower hus => Infer.const_sound hin hf htower hus
  | _, _, _, _, .natLit h => Infer.natLit_sound hin h
  | _, _, _, _, .strLit h => Infer.strLit_sound hin h
  | _, _, _, _, .forallE hs hu hbs hv hz =>
    Infer.forallE_sound (infer_sound hin hs) (red_sound hin hu)
      (infer_sound hin hbs) (red_sound hin hv) hz
  | _, _, _, _, .lam hs hu hbt hchain hbtt hv hz =>
    Infer.lam_sound (fun hg => infer_sound hin (hs hg))
      (fun hg => red_sound hin (hu hg)) (infer_sound hin hbt)
      (fun _ _ _ hbody => by subst hbody; exact Infer.lam_shape hbt)
      hchain (fun hn => infer_sound hin (hbtt hn))
      (fun hn => red_sound hin (hv hn)) hz
  | _, _, _, _, .app htf hw hta hd =>
    Infer.app_sound (infer_sound hin htf) (red_sound hin hw)
      (infer_sound hin hta) (defeq_sound hin hd)
  | _, _, _, _, .appSkip htf hw hnev =>
    Infer.appSkip_sound (infer_sound hin htf) (red_sound hin hw) hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    Infer.proj_sound hin (infer_sound hin htpe) (red_sound hin hte) hhead hent
      hlen hus hprop

theorem certs_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {lic : Bool} {ty : Expr} {args : List Expr},
      Certs env d lic ty args → CertsSem m φ d lic ty args
  | _, _, _, _, .nil => Certs.nil_sound
  | _, _, _, _, .skip hlic hnev hrest =>
    Certs.skip_sound hlic hnev (certs_sound hin hrest)
  | _, _, _, _, .cert hta hd hrest =>
    Certs.cert_sound (infer_sound hin hta) (defeq_sound hin hd)
      (certs_sound hin hrest)

theorem defEqList_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {as bs : List Expr},
      DefEqList env d as bs → DefEqListSem m φ d as bs
  | _, _, _, .nil => DefEqList.nil_sound
  | _, _, _, .cons h hs =>
    DefEqList.cons_sound (defeq_sound hin h) (defEqList_sound hin hs)

theorem etaProjCerts_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs →
      EtaProjCertsSem m φ d T us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => EtaProjCerts.nil_sound
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest =>
    EtaProjCerts.cons_sound hf hlps hstrip (certs_sound hin hcerts)
      (etaProjCerts_sound hin hrest)

end

end ConLeche.Model.Rules
