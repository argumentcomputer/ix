import IxCC.Anf.Proof.Mono
import IxCC.Sem.Dominance

/-! # The Anf-to-Anf relation: interface and compatibility

The logical relation of design note 02 §7 for Anf-to-Anf passes, at the
granularity the depth clock allows (M2.3). Anf, like Lam, runs on a *depth*
clock: a value computed one clock down is used at the full clock, so a
step-indexed relation on values (02 §7.1's `ValRel k`) is circular. The
relation is therefore split:

* on **values** a relation `R` that is not clock-indexed. It is
  *structural* (literals and □ relate to themselves, constructors
  pointwise, and these are the only related values of their shapes) and
  relates every closure to the same code under related environments
  (`Structural`). A pass adds its own closures: those whose target code is
  a rewrite of the source code;
* on **computations** the clock-indexed `Sem.SimUpTo R n`: up to clock
  bound `n`, a source outcome is matched at some target clock (related
  value, same trap, or target resource failure), and a source timeout at
  `k` is a target timeout or resource failure at `k` (tick dominance: the
  target charges at least as deep). A stuck source imposes nothing.

What a pass must establish about its values at bound `n` is an interface:
applying related values (`AppSim`), calling a global (`CallSim`) and
reading a global's value (`GlobSim`). From these, the **compatibility
lemmas** below give each Anf construct's simulation from its parts' (one
lemma per construct, as chains of `Sem.Bind`/`SimUpTo` combinators over the
bind-form equations, decision D-1); `Rel/Fund` assembles them into the
fundamental lemma. -/

set_option autoImplicit false

namespace IxCC.Anf.Rel

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)

/-- Two lists related pointwise. -/
inductive Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Pw R as bs → Pw R (a :: as) (b :: bs)

namespace Pw

variable {α β : Type} {R : α → β → Prop}

theorem length : ∀ {as : List α} {bs : List β}, Pw R as bs → bs.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem get : ∀ {as : List α} {bs : List β}, Pw R as bs → ∀ (i : Nat),
    (as[i]? = none ∧ bs[i]? = none) ∨ ∃ a b, as[i]? = some a ∧ bs[i]? = some b ∧ R a b
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ h, i + 1 => by simpa using h.get i

theorem append : ∀ {as : List α} {bs : List β}, Pw R as bs → ∀ {as' : List α} {bs' : List β},
    Pw R as' bs' → Pw R (as ++ as') (bs ++ bs')
  | _, _, .nil, _, _, h' => h'
  | _, _, .cons h hs, _, _, h' => .cons h (hs.append h')

theorem reverse : ∀ {as : List α} {bs : List β}, Pw R as bs → Pw R as.reverse bs.reverse
  | _, _, .nil => .nil
  | _, _, .cons h hs => by simpa using hs.reverse.append (.cons h .nil)

theorem take : ∀ {as : List α} {bs : List β}, Pw R as bs → ∀ n, Pw R (as.take n) (bs.take n)
  | _, _, .nil, _ => by simpa using Pw.nil
  | _, _, .cons _ _, 0 => by simpa using Pw.nil
  | _, _, .cons h hs, n + 1 => by simpa using Pw.cons h (hs.take n)

theorem drop : ∀ {as : List α} {bs : List β}, Pw R as bs → ∀ n, Pw R (as.drop n) (bs.drop n)
  | _, _, .nil, _ => by simpa using Pw.nil
  | _, _, .cons h hs, 0 => by simpa using Pw.cons h hs
  | _, _, .cons _ hs, n + 1 => by simpa using hs.drop n

theorem imp {R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ {as : List α} {bs : List β}, Pw R as bs → Pw R' as bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hR _ _ h) (hs.imp hR)

end Pw

variable (P Q : Program) (R : Val → Val → Prop)

/-- The shape every Anf-to-Anf pass's value relation has: literals and □
relate to themselves, constructors pointwise; and a literal, □, constructor
or closure relates only to a value of the same shape (`inv`). -/
structure Base : Prop where
  lit : ∀ l, R (.lit l) (.lit l)
  box : R .box .box
  con : ∀ c vs ws, Pw R vs ws → R (.con c vs) (.con c ws)
  invLit : ∀ l w, R (.lit l) w → w = .lit l
  invBox : ∀ w, R .box w → w = .box
  invCon : ∀ c vs w, R (.con c vs) w → ∃ ws, w = .con c ws ∧ Pw R vs ws
  invClos : ∀ ρ n b got w, R (.clos ρ n b got) w → ∃ ρ' n' b' got', w = .clos ρ' n' b' got'

/-- `Base`, and closures of the same code under related environments are
related. -/
structure Structural : Prop extends Base R where
  idc : ∀ ρ ρ' n b got got', Pw R ρ ρ' → Pw R got got' → R (.clos ρ n b got) (.clos ρ' n b got')

instance {R : Val → Val → Prop} : CoeOut (Structural R) (Base R) := ⟨Structural.toBase⟩

/-- Join closures with the same code over related environments. -/
inductive JR : List JClo → List JClo → Prop
  | nil : JR [] []
  | cons {ρ ρ' : List Val} {J0 J0' J J' : List JClo} {n : Nat} {b : Exp} {r : Bool} :
      Pw R ρ ρ' → JR J0 J0' → JR J J' → JR (.mk ρ J0 n b r :: J) (.mk ρ' J0' n b r :: J')

/-- Applying related values to related arguments, at clock bound `n`. -/
def AppSim (n : Nat) : Prop :=
  ∀ ⦃f : Val⦄ ⦃g : Val⦄ ⦃vs ws : List Val⦄, R f g → Pw R vs ws →
    SimUpTo R n (fun k => applyN P k f vs) (fun k => applyN Q k g ws)

/-- Calling a global on related arguments, at clock bound `n`. -/
def CallSim (n : Nat) : Prop :=
  ∀ (g : GlobalId) ⦃vs ws : List Val⦄, Pw R vs ws →
    SimUpTo R n (fun k => (Result.ofOption (P.global? g)).bind (callVal P k · vs))
      (fun k => (Result.ofOption (Q.global? g)).bind (callVal Q k · ws))

/-- A global's value, at clock bound `n`. -/
def GlobSim (n : Nat) : Prop :=
  ∀ g : GlobalId, SimUpTo R n (fun k => (Result.ofOption (P.global? g)).bind (globVal P k))
    (fun k => (Result.ofOption (Q.global? g)).bind (globVal Q k))

variable {P Q R}

/-! ## Values -/

theorem atom_eval_rel (hS : Base R) {ρ : List Val} {ρ' : List Val} (hρ : Pw R ρ ρ') :
    ∀ a : Atom, (a.eval ρ = none ∧ a.eval ρ' = none) ∨
      ∃ v w, a.eval ρ = some v ∧ a.eval ρ' = some w ∧ R v w
  | .var i => by simpa [Atom.eval] using hρ.get i
  | .lit l => .inr ⟨_, _, rfl, rfl, hS.lit l⟩
  | .box => .inr ⟨_, _, rfl, rfl, hS.box⟩

theorem atoms_eval_rel (hS : Base R) {ρ : List Val} {ρ' : List Val} (hρ : Pw R ρ ρ') :
    ∀ as : List Atom, (evalAtoms ρ as = none ∧ evalAtoms ρ' as = none) ∨
      ∃ vs ws, evalAtoms ρ as = some vs ∧ evalAtoms ρ' as = some ws ∧ Pw R vs ws
  | [] => .inr ⟨[], [], rfl, rfl, .nil⟩
  | a :: as => by
    rw [evalAtoms_cons, evalAtoms_cons]
    rcases atom_eval_rel hS hρ a with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · left; simp [h1, h2]
    · rcases atoms_eval_rel hS hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · left; simp [h1, h2, h3, h4]
      · right; exact ⟨v :: vs, w :: ws, by simp [h1, h3], by simp [h2, h4], .cons hvw hvs⟩

/-- `ofOption` of related options. -/
theorem sim_ofOption {n : Nat} {o : Option Val} {o' : Option Val}
    (h : (o = none ∧ o' = none) ∨ ∃ v w, o = some v ∧ o' = some w ∧ R v w) :
    SimUpTo R n (fun _ => Result.ofOption o) (fun _ => Result.ofOption o') := by
  rcases h with ⟨rfl, rfl⟩ | ⟨v, w, rfl, rfl, hvw⟩
  · exact SimUpTo.stuck _
  · exact SimUpTo.ok hvw

theorem natArgs_rel (hS : Base R) : ∀ {vs ws : List Val}, Pw R vs ws → natArgs ws = natArgs vs
  | [], [], .nil => rfl
  | v :: vs, w :: ws, .cons hvw hvs => by
    cases v with
    | lit l =>
      rw [hS.invLit l w hvw]
      cases l with
      | nat m => simp [natArgs, natArgs_rel hS hvs]
      | str s => simp [natArgs]
    | box => rw [hS.invBox w hvw]; simp [natArgs]
    | con c fs => obtain ⟨ws', rfl, _⟩ := hS.invCon c fs w hvw; simp [natArgs]
    | clos ρ n b got => obtain ⟨_, _, _, _, rfl⟩ := hS.invClos ρ n b got w hvw; simp [natArgs]

theorem prim_rel (hS : Base R) {n : Nat} (K : Lam.Known) (p : Lam.Prim) {vs ws : List Val}
    (h : Pw R vs ws) : SimUpTo R n (fun _ => primResult K p vs) (fun _ => primResult K p ws) := by
  unfold primResult
  rw [natArgs_rel hS h]
  cases natArgs vs with
  | none => exact SimUpTo.stuck _
  | some ns =>
    simp only
    cases p.sem ns with
    | none => exact SimUpTo.stuck _
    | some r =>
      cases r with
      | nat m => exact SimUpTo.ok (hS.lit _)
      | bool b =>
        simp only
        cases (if b then K.boolTrue else K.boolFalse) with
        | none => exact SimUpTo.stuck _
        | some c => exact SimUpTo.ok (hS.con c [] [] .nil)

theorem proj_rel (hS : Base R) {n : Nat} (c : Key.CtorKey) (i : Nat) {v w : Val} (h : R v w) :
    SimUpTo R n (fun _ => projVal c i v) (fun _ => projVal c i w) := by
  cases v with
  | con c' vs =>
    obtain ⟨ws, rfl, hvs⟩ := hS.invCon c' vs w h
    simp only [projVal]
    split
    · exact sim_ofOption (hvs.get i)
    · exact SimUpTo.stuck _
  | lit l => exact SimUpTo.stuck _
  | box => exact SimUpTo.stuck _
  | clos ρ n b got => exact SimUpTo.stuck _

theorem asCtor_rel (hS : Base R) (K : Lam.Known) {v w : Val} (h : R v w) :
    (v.asCtor K = none) ∨ ∃ c fs fs', v.asCtor K = some (c, fs) ∧ w.asCtor K = some (c, fs') ∧ Pw R fs fs' := by
  cases v with
  | lit l =>
    rw [hS.invLit l w h]
    cases l with
    | nat m =>
      cases m with
      | zero =>
        cases hz : K.natZero with
        | none => left; simp [Val.asCtor, hz]
        | some z => right; exact ⟨z, [], [], by simp [Val.asCtor, hz], by simp [Val.asCtor, hz], .nil⟩
      | succ m =>
        cases hs : K.natSucc with
        | none => left; simp [Val.asCtor, hs]
        | some s =>
          right
          exact ⟨s, [.lit (.nat m)], [.lit (.nat m)], by simp [Val.asCtor, hs],
            by simp [Val.asCtor, hs], .cons (hS.lit _) .nil⟩
    | str _ => left; rfl
  | box => left; rfl
  | con c fs =>
    obtain ⟨ws, rfl, hfs⟩ := hS.invCon c fs w h
    right; exact ⟨c, fs, ws, rfl, rfl, hfs⟩
  | clos ρ n b got => left; rfl

/-! ## Compatibility: right-hand sides -/

section

variable {n : Nat} (hS : Base R)
include hS

theorem compat_atom {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (a : Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.atom a)) (fun k => evalBind Q k ρ' (.atom a)) :=
  (sim_ofOption (atom_eval_rel hS hρ a)).congr (fun k => evalBind_atom P k ρ a)
    (fun k => evalBind_atom Q k ρ' a)

theorem compat_con {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (c : Key.CtorKey) (as : List Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.con c as)) (fun k => evalBind Q k ρ' (.con c as)) := by
  refine SimUpTo.congr ?_ (fun k => evalBind_con P k ρ c as) (fun k => evalBind_con Q k ρ' c as)
  rcases atoms_eval_rel hS hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
  · rw [h1, h2]; exact SimUpTo.stuck _
  · rw [h1, h2]; exact SimUpTo.ok (hS.con c vs ws hvs)

theorem compat_proj {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (c : Key.CtorKey) (i : Nat) (x : Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.proj c i x)) (fun k => evalBind Q k ρ' (.proj c i x)) := by
  refine SimUpTo.congr ?_ (fun k => evalBind_proj P k ρ c i x) (fun k => evalBind_proj Q k ρ' c i x)
  rcases atom_eval_rel hS hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
  · rw [h1, h2]; exact SimUpTo.stuck _
  · rw [h1, h2]; exact proj_rel hS c i hvw

theorem compat_prim (hK : Q.known = P.known) {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (p : Lam.Prim)
    (as : List Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.prim p as)) (fun k => evalBind Q k ρ' (.prim p as)) := by
  refine SimUpTo.congr ?_ (fun k => evalBind_prim P k ρ p as) (fun k => evalBind_prim Q k ρ' p as)
  rcases atoms_eval_rel hS hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
  · rw [h1, h2]; exact SimUpTo.stuck _
  · rw [h1, h2, hK]; exact prim_rel hS P.known p hvs

theorem compat_glob (hg : GlobSim P Q R n) (ρ ρ' : List Val) (g : GlobalId) :
    SimUpTo R n (fun k => evalBind P k ρ (.glob g)) (fun k => evalBind Q k ρ' (.glob g)) :=
  (hg g).congr (fun k => evalBind_glob P k ρ g) (fun k => evalBind_glob Q k ρ' g)

theorem compat_call (hc : CallSim P Q R n) {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (g : GlobalId)
    (as : List Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.call g as)) (fun k => evalBind Q k ρ' (.call g as)) := by
  refine SimUpTo.congr ?_ (fun k => evalBind_call P k ρ g as) (fun k => evalBind_call Q k ρ' g as)
  rcases atoms_eval_rel hS hρ as with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
  · refine (SimUpTo.stuck (fun _ => .stuck)).congr (fun k => ?_) (fun k => ?_)
    · rw [h1]; cases P.global? g <;> rfl
    · rw [h2]; cases Q.global? g <;> rfl
  · refine (hc g hvs).congr (fun k => ?_) (fun k => ?_)
    · rw [h1]; cases P.global? g <;> rfl
    · rw [h2]; cases Q.global? g <;> rfl

theorem compat_app (ha : AppSim P Q R n) {ρ ρ' : List Val} (hρ : Pw R ρ ρ') (f : Atom)
    (as : List Atom) :
    SimUpTo R n (fun k => evalBind P k ρ (.app f as)) (fun k => evalBind Q k ρ' (.app f as)) := by
  refine SimUpTo.congr ?_ (fun k => evalBind_app P k ρ f as) (fun k => evalBind_app Q k ρ' f as)
  rcases atom_eval_rel hS hρ f with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
  · rw [h1]; exact SimUpTo.stuck _
  · rw [h1, h2]
    rcases atoms_eval_rel hS hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
    · rw [h3]; exact SimUpTo.stuck _
    · rw [h3, h4]; exact ha hvw hvs

end

theorem compat_fn {n : Nat} (hS : Structural R) {ρ ρ' : List Val} (hρ : Pw R ρ ρ')
    (ps : List Ixon.V3.BinderContract) (b : Exp) :
    SimUpTo R n (fun k => evalBind P k ρ (.fn ps b)) (fun k => evalBind Q k ρ' (.fn ps b)) := by
  cases ps with
  | nil => exact (SimUpTo.stuck _).congr (fun k => evalBind_fn_nil P k ρ b) (fun _ => rfl)
  | cons p ps =>
    exact (SimUpTo.ok (hS.idc ρ ρ' _ b [] [] hρ .nil)).congr
      (fun k => evalBind_fn P k ρ _ b (List.cons_ne_nil _ _))
      (fun k => evalBind_fn Q k ρ' _ b (List.cons_ne_nil _ _))


/-! ## Compatibility: expressions -/

section

variable {n : Nat}

theorem compat_bind {ρ ρ' : List Val} {J J' : List JClo} {c c' : Ixon.V3.LetContract} {b b' : Bind}
    {e e' : Exp} (hb : SimUpTo R n (fun k => evalBind P k ρ b) (fun k => evalBind Q k ρ' b'))
    (he : ∀ v w, R v w → SimUpTo R n (fun k => eval P k (v :: ρ) J e) (fun k => eval Q k (w :: ρ') J' e')) :
    SimUpTo R n (fun k => eval P k ρ J (.bind c b e)) (fun k => eval Q k ρ' J' (.bind c' b' e')) :=
  (SimUpTo.bind (evalBind_mono Q ρ' b') (fun w => eval_mono Q (w :: ρ') J' e') hb he).congr
    (fun k => eval_bind P k ρ J c b e) (fun k => eval_bind Q k ρ' J' c' b' e')

theorem compat_join {ρ ρ' : List Val} {J J' : List JClo} {m : Nat} {r : Bool} {b b' e e' : Exp}
    (he : SimUpTo R n (fun k => eval P k ρ (.mk ρ J m b r :: J) e)
      (fun k => eval Q k ρ' (.mk ρ' J' m b' r :: J') e')) :
    SimUpTo R n (fun k => eval P k ρ J (.join m r b e)) (fun k => eval Q k ρ' J' (.join m r b' e')) :=
  he.congr (fun k => eval_join' P k ρ J m r b e) (fun k => eval_join' Q k ρ' J' m r b' e')

theorem compat_tick {ρ ρ' : List Val} {J J' : List JClo} {e e' : Exp}
    (he : ∀ m, m + 1 ≤ n → SimUpTo R m (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e')) :
    SimUpTo R n (fun k => eval P k ρ J (.tick e)) (fun k => eval Q k ρ' J' (.tick e')) :=
  (SimUpTo.later he).congr (fun k => eval_tick P k ρ J e) (fun k => eval_tick Q k ρ' J' e')

theorem compat_trap {ρ ρ' : List Val} {J J' : List JClo} :
    SimUpTo R n (fun k => eval P k ρ J .trap) (fun k => eval Q k ρ' J' .trap) :=
  SimUpTo.trap.congr (fun k => eval_trap' P k ρ J) (fun k => eval_trap' Q k ρ' J')

theorem compat_ret (hS : Base R) {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw R ρ ρ')
    (a : Atom) :
    SimUpTo R n (fun k => eval P k ρ J (.ret a)) (fun k => eval Q k ρ' J' (.ret a)) :=
  (sim_ofOption (atom_eval_rel hS hρ a)).congr (fun k => eval_ret' P k ρ J a)
    (fun k => eval_ret' Q k ρ' J' a)

/-- A jump: both sides charge, then run the join bodies one clock down. -/
theorem compat_jumpTo {jc jc' : JClo} {vs ws : List Val} (hvs : Pw R vs ws)
    (hjc : ∀ ρj ρj' Jj Jj' m b b' r r', jc = .mk ρj Jj m b r → jc' = .mk ρj' Jj' m b' r' →
      r = r' ∧ ∀ i, i + 1 ≤ n → vs.length = m →
        SimUpTo R i (fun k => eval P k (vs.reverse ++ ρj) (if r then jc :: Jj else Jj) b)
          (fun k => eval Q k (ws.reverse ++ ρj') (if r' then jc' :: Jj' else Jj') b'))
    (harity : ∀ ρj ρj' Jj Jj' m m' b b' r r', jc = .mk ρj Jj m b r → jc' = .mk ρj' Jj' m' b' r' → m = m') :
    SimUpTo R n (fun k => jumpTo P k jc vs) (fun k => jumpTo Q k jc' ws) := by
  obtain ⟨ρj, Jj, m, b, r⟩ := jc
  obtain ⟨ρj', Jj', m', b', r'⟩ := jc'
  obtain rfl := harity _ _ _ _ _ _ _ _ _ _ rfl rfl
  obtain ⟨rfl, hb⟩ := hjc _ _ _ _ _ _ _ _ _ rfl rfl
  have hl := hvs.length
  by_cases hm : vs.length = m
  · have hm' : ws.length = m := by rw [hl, hm]
    exact (SimUpTo.later fun i hi => hb i hi hm).congr (fun k => by simp only [jumpTo, if_pos hm])
      (fun k => by simp only [jumpTo, if_pos hm'])
  · exact (SimUpTo.stuck _).congr (fun k => by simp only [jumpTo, if_neg hm]) (fun _ => rfl)

end

end IxCC.Anf.Rel
