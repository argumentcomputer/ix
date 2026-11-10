module

public import IxC.Kernel.Model.Rules.Motive
import IxC.Kernel.Semantics.Frame

public section

/-!
# An accepted subject reads

`acceptedReads_of` (`Model/Tiers.lean`) over derivations: what inference at the
full grade derives, the reading reads. Used by the derivation package's
soundness (`Model/JudgeRules.lean`) and by the theorem-unfolding rule's
(`Model/Rules/ThmSound.lean`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key Level)
open Ix.Kernel.Rules (Infer DefEq Red Certs DefEqList EtaProjCerts Grade)

universe w

variable {V : Type w} [SetTheory V]

/-! ## An accepted subject reads

`acceptedReads_of`'s twin over derivations: what inference at the full grade
accepts, the reading reads. The recursion is on the derivation; the other five
relations of the mutual family need no statement and get a trivial one. -/

mutual

theorem infer_reads {env : Env md} (m : EnvModel V env) (φ : LevelParam → Nat) :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      ∃ ea, denoteMeta m.acval env φ d e = some ea
  | _, _, _, _, .sort, _, _, _, _ => ⟨_, denoteMeta_sort _ _ _⟩
  | _, _, _, _, .fvar _, _, _, _, _ => ⟨_, denoteMeta_fvar _ _ _ _⟩
  | _, _, _, _, .const hf _ hus, _, _, _, _ => ⟨_, denoteMeta_const hf hus⟩
  | _, _, _, _, .natLit h, _, _, _, _ => ⟨_, denoteMeta_natLit h⟩
  | _, d, _, _, .strLit (s := s) h, _, _, _, _ => by
    rcases hd : denoteMeta m.acval env φ d (.lit (.strVal s)) with _ | ea
    · rw [denoteMeta, if_pos h] at hd
      exact nomatch hd
    · exact ⟨ea, rfl⟩
  | _, _, _, _, .forallE (ty := ty) (body := body) hs _ hbs _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded body := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwo, hbo, hLo⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
    obtain ⟨ta, hta⟩ := infer_reads m φ hs hg hws.1 hb.1 hLty
    obtain ⟨ba, hba⟩ := infer_reads m φ hbs hg hwo hbo hLo
    exact ⟨_, by rw [denoteMeta_forallE, hta, hba]; rfl⟩
  | _, _, _, _, .lam (ty := ty) (body := body) hs _ hbt _ _ _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded body := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwo, hbo, hLo⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
    obtain ⟨ta, hta⟩ := infer_reads m φ (hs hg) rfl hws.1 hb.1 hLty
    obtain ⟨ba, hba⟩ := infer_reads m φ hbt hg hwo hbo hLo
    exact ⟨_, by rw [denoteMeta_lam, hta, hba]; rfl⟩
  | _, _, _, _, .app htf _ hta _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨fa, hfa⟩ := infer_reads m φ htf hg hws.1 hb.1 (fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl]))
    obtain ⟨aa, haa⟩ := infer_reads m φ hta hg hws.2 hb.2 (fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl]))
    exact ⟨_, by rw [denoteMeta_app, hfa, haa]; rfl⟩
  | _, _, _, _, .appSkip _ _ _, hg, _, _, _ => nomatch hg
  | _, _, _, _, .proj htpe _ _ hent _ _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded] at hb
    obtain ⟨pa, hpa⟩ := infer_reads m φ htpe hg hws hb (fun l hl =>
      hL l (by simpa [Expr.fvarLeaves] using hl))
    exact ⟨_, denoteMeta_proj_tower hent hpa⟩

theorem infer_reads_red {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → True
  | _, _, _, _ => trivial

theorem infer_reads_defeq {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

theorem infer_reads_certs {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem infer_reads_defEqList {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem infer_reads_etaProjCerts {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → True
  | _, _, _, _, _, _, _, _ => trivial

end

end Ix.Kernel.Model
