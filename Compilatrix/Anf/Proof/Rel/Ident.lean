import Compilatrix.Anf.Proof.Rel.Fund

/-! # The identity instance of the relation

`IdV`: values with the same code everywhere (literals, □, constructors of
related fields, closures of the same code over related environments). It is
structural, and for one program it satisfies the interface at every clock
bound (`Ident.level`, by strong induction: the fundamental lemma below the
bound gives application, calls and global values, which give the
fundamental lemma at the bound). So every expression simulates itself at
every clock (`Ident.fund`) and every program refines itself
(`Ident.refines`) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Rel

open Compilatrix.Sem (Result ClockMono SimUpTo Sim later later_succ later_zero)

mutual

/-- Values with the same code everywhere. -/
inductive IdV : Val → Val → Prop
  | lit {l : Lam.Lit} : IdV (.lit l) (.lit l)
  | box : IdV .box .box
  | con {c : Key.CtorKey} {vs ws : List Val} : IdVs vs ws → IdV (.con c vs) (.con c ws)
  | clos {ρ ρ' got got' : List Val} {n : Nat} {b : Exp} :
      IdVs ρ ρ' → IdVs got got' → IdV (.clos ρ n b got) (.clos ρ' n b got')

inductive IdVs : List Val → List Val → Prop
  | nil : IdVs [] []
  | cons {v w : Val} {vs ws : List Val} : IdV v w → IdVs vs ws → IdVs (v :: vs) (w :: ws)

end

namespace Ident

theorem pw_of : ∀ {vs ws : List Val}, IdVs vs ws → Pw IdV vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pw_of hs)

theorem of_pw : ∀ {vs ws : List Val}, Pw IdV vs ws → IdVs vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (of_pw hs)

theorem structural : Structural IdV where
  lit _ := .lit
  box := .box
  con _ _ _ h := .con (of_pw h)
  idc _ _ _ _ _ _ hρ hg := .clos (of_pw hρ) (of_pw hg)
  invLit l w h := by cases h; rfl
  invBox w h := by cases h; rfl
  invCon c vs w h := by cases h with | con h => exact ⟨_, rfl, pw_of h⟩
  invClos ρ n b got w h := by cases h; exact ⟨_, _, _, _, rfl⟩

mutual

theorem obs : ∀ {v w : Val}, IdV v w → obsV v = obsV w
  | _, _, .lit => rfl
  | _, _, .box => rfl
  | _, _, .con h => by
    rename_i c _ _
    cases c with
    | src c => simp only [obsV, obsList_eq h]
    | clo f j => rfl
  | _, _, .clos _ _ => rfl

theorem obsList_eq : ∀ {vs ws : List Val}, IdVs vs ws → obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [obsList, obs h, obsList_eq hs]

end

variable (P : Program)

/-- The interface and the fundamental lemma, at one clock bound. -/
structure Level (n : Nat) : Prop where
  fund : FundAt P P IdV n
  app : AppSim P P IdV n
  call : CallSim P P IdV n
  glob : GlobSim P P IdV n

theorem app_at {n : Nat} (hlow : ∀ m < n, FundAt P P IdV m) : AppSim P P IdV n := by
  suffices h : ∀ len, ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, vs.length ≤ len → IdV f g → Pw IdV vs ws →
      SimUpTo IdV n (fun k => applyN P k f vs) (fun k => applyN P k g ws) from
    fun f g vs ws hfg hvs => h vs.length (Nat.le_refl _) hfg hvs
  intro len
  induction len with
  | zero =>
    intro f g vs ws hl hfg hvs
    cases vs with
    | cons _ _ => simp at hl
    | nil =>
      cases hvs
      exact (SimUpTo.ok hfg).congr (fun k => applyN_nil' P k f) (fun k => applyN_nil' P k g)
  | succ len ih =>
    intro f g vs ws hl hfg hvs
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok hfg).congr (fun k => applyN_nil' P k f) (fun k => applyN_nil' P k g)
    | cons v vs' =>
      cases hfg with
      | clos hρ hgot =>
        exact app_idc structural hlow (pw_of hρ) (pw_of hgot) hvs
          fun f' g' us us' h hus hlt => ih (by simp at hl hlt; omega) h hus
      | _ =>
        exact (SimUpTo.stuck (fun k => applyN P k _ ws)).congr
          (fun k => applyN_not_clos P k _ v vs' (by intros; nofun)) (fun _ => rfl)

theorem call_at {n : Nat} (hlow : ∀ m < n, FundAt P P IdV m) : CallSim P P IdV n := by
  intro g vs ws hvs
  cases P.global? g with
  | none => exact SimUpTo.stuck _
  | some gd =>
    simp only [Result.ofOption, Result.bind_ok, callVal]
    have hl := hvs.length
    by_cases hm : vs.length = gd.ps.length
    · refine (SimUpTo.later fun i hi => hlow i (by omega) hvs.reverse .nil gd.body).congr
        (fun k => if_pos hm) (fun k => if_pos (by rw [hl]; exact hm))
    · exact (SimUpTo.stuck _).congr (fun k => if_neg hm) (fun k => if_neg (by rw [hl]; exact hm))

theorem glob_at {n : Nat} (hlow : ∀ m < n, FundAt P P IdV m) : GlobSim P P IdV n := by
  intro g
  cases P.global? g with
  | none => exact SimUpTo.stuck _
  | some gd =>
    simp only [Result.ofOption, Result.bind_ok]
    unfold globVal
    cases gd.ps with
    | nil => exact SimUpTo.later fun i hi => hlow i (by omega) .nil .nil gd.body
    | cons _ _ => exact SimUpTo.ok (.clos .nil .nil)

/-- The identity instance at every clock bound. -/
theorem level : ∀ n, Level P n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hlow : ∀ m < n, FundAt P P IdV m := fun m hm => (ih m hm).fund
  have ha := app_at P hlow
  have hc := call_at P hlow
  have hg := glob_at P hlow
  exact ⟨fund_step structural rfl hlow ha hc hg, ha, hc, hg⟩

/-- **Fundamental lemma**: every expression simulates itself, at every
clock, from environments and join closures with the same code. -/
theorem fund {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw IdV ρ ρ') (hJ : JR IdV J J') (e : Exp) :
    Sim IdV id (fun k => eval P k ρ J e) (fun k => eval P k ρ' J' e) :=
  SimUpTo.sim fun n => (level P n).fund hρ hJ e

/-- Every program refines itself. -/
theorem refines : Sem.Refines P P :=
  refines_of structural rfl (fun _ _ h => obs h) (fun n => (level P n).glob) (fun n => (level P n).app)

end Ident

end Compilatrix.Anf.Rel
