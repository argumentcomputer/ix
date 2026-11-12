module

public import IxC.Kernel.Model.Open.Core
public import IxC.Kernel.Model.Open.Certs
public import IxC.Kernel.Model.Open.Lists
public import IxC.Kernel.Model.Open.Tables
import IxC.Kernel.Model.Open.Eta
import IxC.Kernel.Model.Open.Irrel
import IxC.Kernel.Model.Open.NatStep
import IxC.Kernel.Model.Open.Lam
import IxC.Kernel.Model.Open.Lit
import IxC.Kernel.Model.Open.Rescue
import IxC.Kernel.Model.Open.Iota
import IxC.Kernel.Model.Open.Proj
import IxC.Kernel.Model.Open.ProjType
import IxC.Kernel.Model.Open.StructEta
import IxC.Kernel.Model.Open.Unit
import IxC.Kernel.Model.Open.ProofFast
import IxC.Kernel.Rules.Derived

@[expose] public section

/-!
# The rules are sound over every `Model`

**Every derivation of the kernel's rules (`IxC/Kernel/Rules/Rel.lean`) satisfies its motive
in every model** of a stored environment: a reduct denotes what its subject does (`RedS`),
definitionally equal terms denote alike (`DefEqS`), and an inferred type holds the subject
(`InferS`), at every level assignment. One mutual structural recursion over the six
relations; each case is one rule's lemma (`Open/*.lean`) applied to the recursive calls.

The only fact about the environment read is `StoredEnv` (the stored terms closed, the
stored telescopes' arities, the projection tables, the η rules, the table bodies, the
recursor rules), which the kernel's fold establishes (`EnvModelM.storedEnv`). The laws
read are `Model`'s fields. A theorem's unfolding (`Red.deltaThm`) reads its premises at the
assignment the use's levels induce, so the recursion is at every assignment.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env}

mutual

theorem red_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → RedS M φ d e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ => Red.trans_sound (red_sound hse h₁) (red_sound hse h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound hse h)
  | _, _, _, .projArg h => Red.projArg_sound (red_sound hse h)
  | _, _, _, .appArg h => Red.appArg_sound (red_sound hse h)
  | _, _, _, .betaGate hnev => Red.betaGate_sound hnev
  | _, _, _, .beta hta hd => Red.beta_sound (infer_sound hse hta) (defeq_sound hse hd)
  | _, _, _, .delta h => Red.delta_sound hse.closed h
  | _, _, _, .deltaThm (us := us) (cv := cv) hf hlen hvf hvb hinf hde hinfT hred hz =>
    Red.deltaThm_sound hse.closed hf hlen hvf hvb
      (infer_sound hse (φ := Level.substFn φ cv.levelParams us) hinf)
      (defeq_sound hse (φ := Level.substFn φ cv.levelParams us) hde)
      (infer_sound hse (φ := Level.substFn φ cv.levelParams us) hinfT)
      (red_sound hse (φ := Level.substFn φ cv.levelParams us) hred) hz
  | _, _, _, .eqProof _ _ hp hwp hbp hlp ha hda hb hdb hT hred hv =>
    Red.eqProof_sound (infer_sound hse hp) hwp hbp hlp (infer_sound hse ha)
      (defeq_sound hse hda) (infer_sound hse hb) (defeq_sound hse hdb) (infer_sound hse hT)
      (red_sound hse hred) hv
  | _, _, _, .natLit h => Red.natLit_sound h
  | _, _, _, .natZeroLit _ => Red.natZeroLit_sound
  | _, _, _, .strLit h => Red.strLit_sound h
  | _, _, _, .natSucc _ hw hn => Red.natSucc_sound (red_sound hse hw) hn
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr =>
    Red.natOp_sound hc hst (red_sound hse hwa) hn₁ (red_sound hse hwb) hn₂ hr
  | _, _, _, .natAddSucc hs ht => Red.natAddSucc_sound hs ht
  | _, _, _, .natAddZero hs ht hw hn => Red.natAddZero_sound hs ht (red_sound hse hw) hn
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    Red.proj_sound hse hent hhead hi hlen hus hfire hctor (certs_sound hse hcerts)
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv
      hparams hcertR hcertC hres hidx =>
    Red.iota_sound hse hhead hrec hlen hus (red_sound hse hmajor) hmhead hctor hrule hmlen
      hfire hlv (fun hc => defEqList_sound hse (hparams hc)) (certs_sound hse hcertR)
      (certs_sound hse hcertC) hres (fun hne => defEqList_sound hse (hidx hne))
  | _, _, _, .rescueK _ _ hctor _ _ htm htmaj hthead hlv _ hfab hws hb hlv' hcerts _ _ hpi =>
    Red.rescueK_sound hse.closed hctor (infer_sound hse htm) (red_sound hse htmaj) hthead hlv
      hfab hws hb hlv' (certs_sound hse hcerts) (defeq_sound hse hpi)
  | _, _, _, .rescueEta hrec heta hctor hres hind htm htmaj hthead _ hlv _ hfab hws hb hlv'
      hcerts hproj hpi =>
    Red.rescueEta_sound hse hrec heta hctor hres hind (infer_sound hse htm)
      (red_sound hse htmaj) hthead hlv hfab hws hb hlv' (certs_sound hse hcerts)
      (fun hno => etaProjCerts_sound hse (hproj hno)) (defeq_sound hse hpi)
  | _, _, _, .rescueAnd _ hctor _ _ htm htmaj hthead _ hlv hslots hfab hws hb hlv' hcerts _ _
      hpi =>
    Red.rescueAnd_sound hse.closed hctor (infer_sound hse htm) (red_sound hse htmaj) hthead
      hlv hslots hfab hws hb hlv' (certs_sound hse hcerts) (defeq_sound hse hpi)

theorem defeq_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → DefEqS M φ d a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound hse h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hse hr) (defeq_sound hse h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .fvar => DefEq.fvar_sound
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .natZero => DefEq.natZero_sound
  | _, _, _, .natSucc h => DefEq.natSucc_sound (defeq_sound hse h)
  | _, _, _, .natOffset hs ht ha hb h =>
    DefEq.natOffset_sound hs ht ha hb (defeq_sound hse h)
  | _, _, _, .forallE hty hbody hpw _ =>
    DefEq.forallE_sound (defeq_sound hse hty) (defeq_sound hse hbody) hpw
  | _, _, _, .lam hty hbody hpw _ =>
    DefEq.lam_sound (defeq_sound hse hty) (defeq_sound hse hbody) hpw
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hse hf) (defeq_sound hse ha)
  | _, _, _, .proj h => DefEq.proj_sound (defeq_sound hse h)
  | _, _, _, .eta htb hwtb hty hbody hpw _ =>
    DefEq.eta_sound (infer_sound hse htb) (red_sound hse hwtb) (defeq_sound hse hty)
      (defeq_sound hse hbody) hpw
  | _, _, _, .proofFast ha hb => DefEq.proofFast_sound ha hb
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    DefEq.proofIrrel_sound (infer_sound hse hta) (infer_sound hse htta) (red_sound hse hu) hu0
      (infer_sound hse htb) (infer_sound hse httb) (red_sound hse hv) hv0
  | _, _, _, .unitLike hta hwta hua htb hwtb hub =>
    DefEq.unitLike_sound (infer_sound hse hta) (red_sound hse hwta) hua (infer_sound hse htb)
      (red_sound hse hwtb) hub
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT hresc htlen
      hlv hlps hslots hus hcerts hproj hparams hfields =>
    DefEq.structEta_sound hse (infer_sound hse htb) (red_sound hse hwtb) hhead hctor hlen
      hthead hind heta hetaCtor hresT hresc htlen hlv hlps hslots hus (certs_sound hse hcerts)
      (fun hno => etaProjCerts_sound hse (hproj hno)) (defEqList_sound hse hparams)
      (defEqList_sound hse hfields)
  | _, _, _, .structUnit hta hwta hthead hind hunit _ htlen _ htb hwtb hd hcerts =>
    DefEq.structUnit_sound hse.closed hse.arities (infer_sound hse hta) (red_sound hse hwta)
      hthead hind hunit htlen (infer_sound hse htb) (red_sound hse hwtb) (defeq_sound hse hd)
      (certs_sound hse hcerts)
  | _, _, _, .proofIrrelTy hta htta hu hu0 htb hd =>
    DefEq.proofIrrelTy_sound (infer_sound hse hta) (infer_sound hse htta) (red_sound hse hu)
      hu0 (infer_sound hse htb) (defeq_sound hse hd)
  | _, _, _, .unitLikeTy hta hwta hthead hind hunit htlen hcerts _ htb hd =>
    DefEq.unitLikeTy_sound hse.closed hse.arities (infer_sound hse hta) (red_sound hse hwta)
      hthead hind hunit htlen (certs_sound hse hcerts) (infer_sound hse htb)
      (defeq_sound hse hd)
  | _, _, _, .structEtaTy hhead hctor hlen hind heta hetaCtor hpos htow hta hwta hcerts htb hd
      hfields =>
    DefEq.structEtaTy_sound hse hhead hctor hlen hind heta hetaCtor hpos htow
      (infer_sound hse hta) (red_sound hse hwta) (certs_sound hse hcerts) (infer_sound hse htb)
      (defeq_sound hse hd) (defEqList_sound hse hfields)

theorem infer_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → InferS M φ g d e t
  | _, _, _, _, .sort => Infer.sort_sound
  | _, _, _, _, .fvar _ => Infer.fvar_sound
  | _, _, _, _, .const hf _ hus => Infer.const_sound hse.closed hf hus
  | _, _, _, _, .natLit h => Infer.natLit_sound h
  | _, _, _, _, .strLit h => Infer.strLit_sound h
  | _, _, _, _, .forallE hs hu hbs hv hz =>
    Infer.forallE_sound (infer_sound hse hs) (red_sound hse hu) (infer_sound hse hbs)
      (red_sound hse hv) hz
  | _, _, _, _, .lam hs _ hbt hchain hbtt hv hz =>
    Infer.lam_sound (fun hg => infer_sound hse (hs hg)) (infer_sound hse hbt)
      (fun _ _ _ hbody => by subst hbody; exact Infer.lam_shape hbt)
      hchain (fun hn => infer_sound hse (hbtt hn)) (fun hn => red_sound hse (hv hn)) hz
  | _, _, _, _, .app htf hw hta hd =>
    Infer.app_sound (infer_sound hse htf) (red_sound hse hw) (infer_sound hse hta)
      (defeq_sound hse hd)
  | _, _, _, _, .appSkip htf hw hnev =>
    Infer.appSkip_sound (infer_sound hse htf) (red_sound hse hw) hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hfire =>
    Infer.proj_sound hse (infer_sound hse htpe) (red_sound hse hte) hhead hent hlen hus hfire

theorem certs_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → CertsS M φ d lic ty args
  | _, _, _, _, .nil => Certs.nil_sound
  | _, _, _, _, .skip hlic hnev hrest => Certs.skip_sound hlic hnev (certs_sound hse hrest)
  | _, _, _, _, .cert hta hd hrest =>
    Certs.cert_sound (infer_sound hse hta) (defeq_sound hse hd) (certs_sound hse hrest)

theorem defEqList_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → DefEqListS M φ d as bs
  | _, _, _, .nil => DefEqList.nil_sound
  | _, _, _, .cons h hs => DefEqList.cons_sound (defeq_sound hse h) (defEqList_sound hse hs)

theorem etaProjCerts_sound (hse : StoredEnv env) {φ : LevelParam → Nat} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → EtaProjCertsS M φ d T us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => EtaProjCerts.nil_sound
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest =>
    EtaProjCerts.cons_sound hf hlps hstrip (certs_sound hse hcerts)
      (etaProjCerts_sound hse hrest)

end

/-- **The rules are sound over every model of a stored environment**: in every model `M` of
an environment the kernel's fold stored (`StoredEnv`), at every level assignment, a reduction
preserves the denotation and its grading, definitionally equal terms denote alike, and an
inferred type holds the subject. -/
theorem rules_sound (hse : StoredEnv env) (M : Model V env) (φ : LevelParam → Nat) :
    (∀ {d : Nat} {e e' : Expr md}, Red env d e e' → RedS M φ d e e') ∧
    (∀ {d : Nat} {a b : Expr md}, DefEq env d a b → DefEqS M φ d a b) ∧
    (∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → InferS M φ g d e t) :=
  ⟨red_sound hse, defeq_sound hse, infer_sound hse⟩

end Ix.Kernel.Open
