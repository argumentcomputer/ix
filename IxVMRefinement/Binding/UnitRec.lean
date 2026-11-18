import IxVMRefinement.Binding.UnitDefn
import IxVMRefinement.Assembly.TypingRecParentTie

/-! # The step of a late recursor record, in the binding fold

`bUnitStep_recLate` proves `BUnitStep` for a standalone recursor record of a native family, with
the registry clause `LateRegistry t E` as the extra clause at each store `E`. It mirrors
`unitStep_recLate_of_tied`; the difference is that the late step (`late_prefixInv_step`) is
taken at every store `E` for `R` and every limit, with the registry at `E`, so the circuit's
interface is asked at every store for `R` with one recursor constant (`BRecLateOut`): the
recursor `cn` is the circuit's output at the record and the environment, and for every family a
store for `R` matches at the parent, the late relation holds with `cn` and `cn` reloads there.
The parent read at the choice store `Ec` is a parent at every store for `R` when `R` holds its
record and the native route's answer stands at every store for `R` (`hnative`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (NativeFam DeclNativeRecLateRunJ)
open Ix.Kernel.Model (rulesJ)

/-- **What the circuit's check of a recursor record gives at every store for `R`**: one
constant `cn` at the record's key, storing a reading of the record over the run's records, such
that at every store for `R`, for every family matched at the parent `P`, the late relation
holds with `cn` in front and `cn` reloads. At one store it gives the typing skeleton's
`RecLateOut` (`BRecLateOut.recLateOut`). -/
def BRecLateOut (t : Ix.Kernel.RoleTable) (R E₀ : Ixon.Env) (A : _root_.Address)
    (env : Ix.Kernel.Env .anon) (P : _root_.Address) (ip : Ixon.InductiveProj) : Prop :=
  ∃ cn ci₀ : ConstantInfo .anon, cn.name = keyOf t A ∧ Reads t E₀ A ci₀ ∧ StoredAs cn ci₀ ∧
    ∀ E, RecordsFor R E → ∀ fam : NativeFam .anon, MatchedAt t E env P ip fam →
      (∃ (cvR : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
        DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩) ∧
      Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn

/-- At one store for `R`, the interface gives the typing skeleton's. -/
theorem BRecLateOut.recLateOut {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
    {A : _root_.Address} {env : Ix.Kernel.Env .anon} {P : _root_.Address}
    {ip : Ixon.InductiveProj} (h : BRecLateOut t R E₀ A env P ip) (hE : RecordsFor R E)
    {fam : NativeFam .anon} (hm : MatchedAt t E env P ip fam) : RecLateOut t E₀ E A env fam := by
  obtain ⟨cn, ci₀, hname, hreads, hstored, hall⟩ := h
  obtain ⟨⟨cvR, mI, rP, rules, hrun⟩, hreload⟩ := hall E hE fam hm
  exact ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩

/-- **`BUnitStep` for a standalone recursor record of a native family, with the registry.**
The parent the circuit read at the choice store `Ec` (with `Q`, e.g. `RecMajorTie`), the
circuit's output at every store for `R` (`hout`), `R` holding the parent's record, the native
route's answer at every store for `R`, and the record's key no operation's. -/
theorem bUnitStep_recLate {t : Ix.Kernel.RoleTable} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {n : Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop)
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc) (hRc : RecordsFor R Ec)
    (hop : keyOf t A ∉ RoleOps.opNames)
    (hparent : ∀ env, StepAt.{u} t envT E₀ Ec (some n) A c env →
      ∃ P ip, RecParent t Ec env P ip ∧ Q P)
    (hheld : ∀ env P ip, RecParent t Ec env P ip → (recordOf R P).isSome = true)
    (hnative : ∀ E, RecordsFor R E → ∀ b, NativeAt Ec b → NativeAt E b)
    (hout : ∀ env P ip, StepAt.{u} t envT E₀ Ec (some n) A c env → RecParent t Ec env P ip →
      Q P → BRecLateOut t R E₀ A env P ip) :
    BUnitStep.{u} (fun E => LateRegistry.{u} t E) t R envT E₀ n A c := by
  intro env hext hnd hinv hYe href hfresh
  have hstep : StepAt.{u} t envT E₀ Ec (some n) A c env := ⟨hext, hnd, hinv Ec hRc, href, hfresh⟩
  obtain ⟨P, ip, hpar, hQ⟩ := hparent env hstep
  obtain ⟨cmR, hcmR⟩ := Option.isSome_iff_exists.mp (hheld env P ip hpar)
  obtain ⟨cn, ci₀, hname, hreads, hstored, hall⟩ := hout env P ip hstep hpar hQ
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  -- The parent's record at every store for `R`.
  have hcmE : ∀ E, RecordsFor R E → Ix.Cert.recordAt E P = some cm := by
    intro E hE
    have h1 : Ix.Cert.recordAt E P = some cmR := hE.2.1 P cmR hcmR
    have h2 : Ix.Cert.recordAt Ec P = some cmR := hRc.2.1 P cmR hcmR
    have e : cmR = cm := Option.some.inj (h2.symm.trans hcm)
    rw [← e]
    exact h1
  -- The late step at every store for `R` and every limit.
  have hlate : ∀ E, RecordsFor R E → ∀ lim, Decl.PrefixInv.{u} E t lim env →
      LateRegistry.{u} t E env →
      Decl.PrefixInv.{u} E t lim ⟨cn :: env.consts⟩ ∧ LateRegistry.{u} t E ⟨cn :: env.consts⟩ := by
    intro E hE lim hinvE hYE
    obtain ⟨Reg, hR⟩ := hYE
    obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ :=
      hR.at_parent ht hfP hres (hcmE E hE) hcmi (hnative E hE _ hnat)
    obtain ⟨⟨cvR, mI, rP, rules, hrun⟩, hreload⟩ := hall E hE fam ⟨hat, hnameP, hmatch⟩
    have hcomp := late_companions ht hinvE.companions ⟨hat, hnameP, hmatch⟩ (hcmE E hE) hcmi hrun
    obtain ⟨hinv', hR'⟩ := late_prefixInv_step hinvE hR hReg hrun
      (hname.trans (LoadedReads.keyOf_eq t A).symm) hcomp hreload
    exact ⟨hinv', ⟨Reg, hR'⟩⟩
  -- The recursor is fresh and is a recursor (read at the choice store).
  obtain ⟨Regc, hRegc⟩ := hYe Ec hRc
  obtain ⟨famc, hfamc, hatc, hnamePc, hmatchc⟩ := hRegc.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨⟨cvRc, mIc, rPc, rulesc, hrunc⟩, -⟩ := hall Ec hRc famc ⟨hatc, hnamePc, hmatchc⟩
  obtain ⟨hfreshN, -, -, cvx, ax, bx, rsx, hcn⟩ := late_head hrunc
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  have hfreshL : ∀ ci ∈ [cn], env.find? ci.name = none := by
    intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  refine ⟨[cn], List.nodup_singleton _, hfreshL, ?_, ?_, ?_, ?_, ?_⟩
  · intro E hE lim hinvE
    exact (hlate E hE lim hinvE (hYe E hE)).1
  · intro E hE
    exact (hlate E hE (some n) (hinv E hE) (hYe E hE)).2
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hop
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

end IxVM.Refinement.Binding
