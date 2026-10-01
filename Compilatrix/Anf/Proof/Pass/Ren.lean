import Compilatrix.Anf.Proof.Pass.Reach

/-! # Pruning: renamed code simulates

A program `Q` whose global `m g` is source global `g` with every reference
renamed by `m`, for the globals `g` of a set `S` closed under references.
Values are related by `RV`: literals, □, constructors pointwise, and a
closure against the closure of its renamed code (whose references lie in
`S`). The fundamental lemma for renamed code (`fund_step`) is the Rel
compatibility lemmas with calls and global values going through `m`, and
renamed join closures; the program interface at each bound comes from the
lemma below it (`levels`) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Prune.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)

/-- Every global reference of `e` lies in `S`. -/
def RefsIn (S : Src.NatMap Unit) (e : Exp) : Prop := ∀ h ∈ e.refs, S.contains h = true

/-- A renaming setting: the globals of `S` (closed under references) are
`Q`'s globals at their new ids, with renamed bodies. -/
structure Setting where
  P : Program
  Q : Program
  S : Src.NatMap Unit
  m : Src.NatMap Nat
  known : Q.known = P.known
  closed : ∀ g gd, S.contains g = true → P.global? g = some gd → RefsIn S gd.body
  glob : ∀ g gd, S.contains g = true → P.global? g = some gd →
    Q.global? (m.getD g g) = some { gd with body := Exp.rename m gd.body }

variable (X : Setting)

mutual

/-- Source and target values. -/
inductive RV : Val → Val → Prop
  | lit {l : Lam.Lit} : RV (.lit l) (.lit l)
  | box : RV .box .box
  | con {c : Key.CtorKey} {vs ws : List Val} : RVs vs ws → RV (.con c vs) (.con c ws)
  | clos {ρ ρ' got got' : List Val} {n : Nat} {b : Exp} :
      RVs ρ ρ' → RVs got got' → RefsIn X.S b → RV (.clos ρ n b got) (.clos ρ' n (Exp.rename X.m b) got')

inductive RVs : List Val → List Val → Prop
  | nil : RVs [] []
  | cons {v w : Val} {vs ws : List Val} : RV v w → RVs vs ws → RVs (v :: vs) (w :: ws)

end

/-- Join closures with renamed code. -/
inductive JRV : List JClo → List JClo → Prop
  | nil : JRV [] []
  | cons {ρ ρ' : List Val} {J J' : List JClo} {n : Nat} {b : Exp} {r : Bool} {Js Js' : List JClo} :
      Pw (RV X) ρ ρ' → JRV J J' → RefsIn X.S b → JRV Js Js' →
      JRV (.mk ρ J n b r :: Js) (.mk ρ' J' n (Exp.rename X.m b) r :: Js')

variable {X}

theorem pw_of : ∀ {vs ws : List Val}, RVs X vs ws → Pw (RV X) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pw_of hs)

theorem of_pw : ∀ {vs ws : List Val}, Pw (RV X) vs ws → RVs X vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (of_pw hs)

theorem base : Rel.Base (RV X) where
  lit _ := .lit
  box := .box
  con _ _ _ h := .con (of_pw h)
  invLit l w h := by cases h; rfl
  invBox w h := by cases h; rfl
  invCon c vs w h := by cases h with | con h => exact ⟨_, rfl, pw_of h⟩
  invClos ρ n b got w h := by cases h with | clos _ _ _ => exact ⟨_, _, _, _, rfl⟩

mutual

theorem obs : ∀ {v w : Val}, RV X v w → obsV v = obsV w
  | _, _, .lit => rfl
  | _, _, .box => rfl
  | _, _, .con h => by
    rename_i c _ _
    cases c with
    | src c => simp only [obsV, obsList_eq h]
    | clo f j => rfl
  | _, _, .clos _ _ _ => rfl

theorem obsList_eq : ∀ {vs ws : List Val}, RVs X vs ws → obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [obsList, obs h, obsList_eq hs]

end

theorem JRV.get : ∀ {J J' : List JClo}, JRV X J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨ ∃ ρ ρ' J0 J0' n b r, J[j]? = some (.mk ρ J0 n b r) ∧
      J'[j]? = some (.mk ρ' J0' n (Exp.rename X.m b) r) ∧ Pw (RV X) ρ ρ' ∧ JRV X J0 J0' ∧ RefsIn X.S b
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hρ h0 hb _, 0 => .inr ⟨_, _, _, _, _, _, _, rfl, rfl, hρ, h0, hb⟩
  | _, _, .cons _ _ _ h, j + 1 => by simpa using h.get j

/-! ## References of subterms -/

theorem RefsIn.bind {S : Src.NatMap Unit} {c : Ixon.V3.LetContract} {b : Bind} {e : Exp}
    (h : RefsIn S (.bind c b e)) : (∀ x ∈ b.refs, S.contains x = true) ∧ RefsIn S e :=
  ⟨fun x hx => h x (by simp [Exp.refs, hx]), fun x hx => h x (by simp [Exp.refs, hx])⟩

theorem RefsIn.join {S : Src.NatMap Unit} {n : Nat} {r : Bool} {b e : Exp} (h : RefsIn S (.join n r b e)) :
    RefsIn S b ∧ RefsIn S e :=
  ⟨fun x hx => h x (by simp [Exp.refs, hx]), fun x hx => h x (by simp [Exp.refs, hx])⟩

theorem RefsIn.tick {S : Src.NatMap Unit} {e : Exp} (h : RefsIn S (.tick e)) : RefsIn S e :=
  fun x hx => h x (by simpa [Exp.refs] using hx)

theorem altsRefs_mem {x : GlobalId} : ∀ {alts : List Alt} {a : Alt}, a ∈ alts → x ∈ a.body.refs →
    x ∈ Exp.altsRefs alts
  | [], _, ha, _ => by simp at ha
  | .mk k n b :: rest, a, ha, hx => by
    simp only [Exp.altsRefs, List.mem_append]
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .inl hx
    · exact .inr (altsRefs_mem ha hx)

theorem RefsIn.case_alt {S : Src.NatMap Unit} {x : Atom} {alts : List Alt} {d : Option Exp}
    (h : RefsIn S (.case x alts d)) {a : Alt} (ha : a ∈ alts) : RefsIn S a.body :=
  fun y hy => h y (by simp only [Exp.refs, List.mem_append]; exact .inl (altsRefs_mem ha hy))

theorem RefsIn.case_dflt {S : Src.NatMap Unit} {x : Atom} {alts : List Alt} {e : Exp}
    (h : RefsIn S (.case x alts (some e))) : RefsIn S e :=
  fun y hy => h y (by simp only [Exp.refs, Exp.optRefs, List.mem_append]; exact .inr hy)

/-! ## The interface at a bound -/

variable (X)

/-- Calling a global of `S` and its renamed id. -/
def CallRen (n : Nat) : Prop :=
  ∀ g, X.S.contains g = true → ∀ ⦃vs ws : List Val⦄, Pw (RV X) vs ws →
    SimUpTo (RV X) n (fun k => (Result.ofOption (X.P.global? g)).bind (callVal X.P k · vs))
      (fun k => (Result.ofOption (X.Q.global? (X.m.getD g g))).bind (callVal X.Q k · ws))

/-- A global of `S` and its renamed id. -/
def GlobRen (n : Nat) : Prop :=
  ∀ g, X.S.contains g = true →
    SimUpTo (RV X) n (fun k => (Result.ofOption (X.P.global? g)).bind (globVal X.P k))
      (fun k => (Result.ofOption (X.Q.global? (X.m.getD g g))).bind (globVal X.Q k))

/-- Renamed code simulates its source at bound `n`. -/
def FundRen (n : Nat) : Prop :=
  ∀ ⦃ρ ρ' : List Val⦄ ⦃J J' : List JClo⦄, Pw (RV X) ρ ρ' → JRV X J J' →
    ∀ e : Exp, RefsIn X.S e →
      SimUpTo (RV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' (Exp.rename X.m e))

variable {X}

section

variable {n : Nat} (hlow : ∀ m < n, FundRen X m) (ha : Rel.AppSim X.P X.Q (RV X) n) (hc : CallRen X n)
  (hg : GlobRen X n)
include hlow ha hc hg

theorem fund_bind {ρ ρ' : List Val} (hρ : Pw (RV X) ρ ρ') :
    ∀ b : Bind, (∀ x ∈ b.refs, X.S.contains x = true) →
      SimUpTo (RV X) n (fun k => evalBind X.P k ρ b) (fun k => evalBind X.Q k ρ' (Bind.rename X.m b))
  | .atom a, _ => Rel.compat_atom base hρ a
  | .con c as, _ => Rel.compat_con base hρ c as
  | .proj c i x, _ => Rel.compat_proj base hρ c i x
  | .prim p as, _ => Rel.compat_prim base X.known hρ p as
  | .glob g, hr => (hg g (hr g (by simp [Bind.refs]))).congr (fun k => evalBind_glob X.P k ρ g)
      (fun k => evalBind_glob X.Q k ρ' _)
  | .call g as, hr => by
    refine SimUpTo.congr ?_ (fun k => evalBind_call X.P k ρ g as) (fun k => evalBind_call X.Q k ρ' _ as)
    rcases Rel.atoms_eval_rel base hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · refine (SimUpTo.stuck (fun _ => .stuck)).congr (fun k => ?_) (fun k => ?_)
      · rw [h1]; cases X.P.global? g <;> rfl
      · rw [h2]; cases X.Q.global? (X.m.getD g g) <;> rfl
    · refine (hc g (hr g (by simp [Bind.refs])) hvs).congr (fun k => ?_) (fun k => ?_)
      · rw [h1]; cases X.P.global? g <;> rfl
      · rw [h2]; cases X.Q.global? (X.m.getD g g) <;> rfl
  | .app f as, _ => Rel.compat_app base ha hρ f as
  | .fn ps b, hr => by
    cases ps with
    | nil => exact (SimUpTo.stuck _).congr (fun k => evalBind_fn_nil X.P k ρ b) (fun _ => rfl)
    | cons p ps =>
      exact (SimUpTo.ok (.clos (of_pw hρ) .nil fun x hx => hr x (by simpa [Bind.refs] using hx))).congr
        (fun k => evalBind_fn X.P k ρ _ b (List.cons_ne_nil _ _))
        (fun k => evalBind_fn X.Q k ρ' _ _ (List.cons_ne_nil _ _))

mutual

theorem fund_exp {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw (RV X) ρ ρ') (hJ : JRV X J J') :
    ∀ e : Exp, RefsIn X.S e →
      SimUpTo (RV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' (Exp.rename X.m e))
  | .bind c b e, hr =>
    Rel.compat_bind (fund_bind hlow ha hc hg hρ b hr.bind.1) fun _ _ hvw => fund_exp (.cons hvw hρ) hJ e hr.bind.2
  | .join m r b e, hr => Rel.compat_join (fund_exp hρ (.cons hρ hJ hr.join.1 hJ) e hr.join.2)
  | .jump j as, _ => by
    show SimUpTo (RV X) n _ fun k => eval X.Q k ρ' J' (.jump j as)
    refine SimUpTo.congr ?_ (fun k => eval_jump X.P k ρ J j as) (fun k => eval_jump X.Q k ρ' J' j as)
    rcases hJ.get j with ⟨h1, h2⟩ | ⟨ρj, ρj', J0, J0', m, b, r, h1, h2, hρj, hJ0, hb⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok]
      rcases Rel.atoms_eval_rel base hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        simp only [Result.bind_ok]
        refine Rel.compat_jumpTo hvs (fun _ _ _ _ _ _ _ _ _ e1 e2 => ?_) (fun _ _ _ _ _ _ _ _ _ _ e1 e2 => ?_)
        · cases e1; cases e2
          refine ⟨rfl, fun i hi _ => hlow i (by omega) (hvs.reverse.append hρj) ?_ b hb⟩
          cases r
          · exact hJ0
          · exact .cons hρj hJ0 hb hJ0
        · cases e1; cases e2; rfl
  | .case x alts d, hr => by
    show SimUpTo (RV X) n _ fun k => eval X.Q k ρ' J' (.case x (Exp.renameAlts X.m alts) (Exp.renameOpt X.m d))
    refine SimUpTo.congr ?_ (fun k => eval_case X.P k ρ J x alts d)
      (fun k => eval_case X.Q k ρ' J' x _ _)
    rcases Rel.atom_eval_rel base hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2, X.known]
      simp only [Result.ofOption, Result.bind_ok]
      rcases Rel.asCtor_rel base X.P.known hvw with h3 | ⟨c, fs, fs', h3, h4, hfs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        exact fund_alts hρ hJ c hfs d (fund_opt hρ hJ d hr) alts fun a ha => hr.case_alt ha
  | .ret a, _ => Rel.compat_ret base hρ a
  | .tick e, hr => Rel.compat_tick fun m hm => hlow m (by omega) hρ hJ e hr.tick
  | .trap, _ => Rel.compat_trap

theorem fund_opt {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw (RV X) ρ ρ') (hJ : JRV X J J') :
    ∀ (d : Option Exp) {x : Atom} {alts : List Alt}, RefsIn X.S (.case x alts d) →
      ((d = none ∧ Exp.renameOpt X.m d = none) ∨ ∃ e, d = some e ∧ Exp.renameOpt X.m d = some (Exp.rename X.m e) ∧
        SimUpTo (RV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' (Exp.rename X.m e)))
  | none, _, _, _ => .inl ⟨rfl, rfl⟩
  | some e, _, _, hr => .inr ⟨e, rfl, rfl, fund_exp hρ hJ e hr.case_dflt⟩

theorem fund_alts {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw (RV X) ρ ρ') (hJ : JRV X J J')
    (c : Key.CtorKey) {fs fs' : List Val} (hfs : Pw (RV X) fs fs') (d : Option Exp)
    (hd : (d = none ∧ Exp.renameOpt X.m d = none) ∨ ∃ e, d = some e ∧ Exp.renameOpt X.m d = some (Exp.rename X.m e) ∧
        SimUpTo (RV X) n (fun k => eval X.P k ρ J e) (fun k => eval X.Q k ρ' J' (Exp.rename X.m e))) :
    ∀ alts : List Alt, (∀ a ∈ alts, RefsIn X.S a.body) →
      SimUpTo (RV X) n (fun k => evalAlts X.P k ρ J c fs alts d)
        (fun k => evalAlts X.Q k ρ' J' c fs' (Exp.renameAlts X.m alts) (Exp.renameOpt X.m d))
  | [], _ => by
    show SimUpTo (RV X) n _ fun k => evalAlts X.Q k ρ' J' c fs' [] (Exp.renameOpt X.m d)
    refine SimUpTo.congr ?_ (fun k => evalAlts_nil X.P k ρ J c fs d)
      (fun k => evalAlts_nil X.Q k ρ' J' c fs' _)
    rcases hd with ⟨rfl, h⟩ | ⟨e, rfl, h, hs⟩
    · rw [h]; exact SimUpTo.stuck _
    · rw [h]; exact hs
  | .mk key m body :: rest, hr => by
    show SimUpTo (RV X) n _ fun k =>
      evalAlts X.Q k ρ' J' c fs' (.mk key m (Exp.rename X.m body) :: Exp.renameAlts X.m rest) (Exp.renameOpt X.m d)
    refine SimUpTo.congr ?_ (fun k => evalAlts_cons X.P k ρ J c fs key m body rest d)
      (fun k => evalAlts_cons X.Q k ρ' J' c fs' key m _ _ _)
    have hl := hfs.length
    by_cases hsel : key = c ∧ m = fs.length
    · have hsel' : key = c ∧ m = fs'.length := ⟨hsel.1, by rw [hl]; exact hsel.2⟩
      exact (fund_exp (hfs.reverse.append hρ) hJ body (hr _ List.mem_cons_self)).congr
        (fun _ => if_pos hsel) (fun _ => if_pos hsel')
    · have hsel' : ¬ (key = c ∧ m = fs'.length) := by rw [hl]; exact hsel
      exact (fund_alts hρ hJ c hfs d hd rest fun a ha => hr a (List.mem_cons_of_mem _ ha)).congr
        (fun _ => if_neg hsel) (fun _ => if_neg hsel')

end

theorem fund_step : FundRen X n := fun _ _ _ _ hρ hJ e hr => fund_exp hlow ha hc hg hρ hJ e hr

end

end Compilatrix.Anf.Prune.Proof
