import IxVMRefinement.Core.Rep
import IxVMRefinement.Core.Ctx
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Ixon.RoleTableInj

/-! # The term relation under substitution, opening, and scope

The facts about the term relation `Tm` that every layer reading it needs:

* **A `let`'s image on a closed value** (`instShift_eq_instantiate1`): the capture-avoiding
  instantiation (`Expr.instantiate1Lift`) is the kernel's plain `instantiate1` when the value has
  no loose bound variable.
* **The loose bound variables of an image** (`Tm.looseBVarsBounded`): a term represented at
  local depth `k` has its loose bound variables below `k`.
* **Opening a binder** (`Tm.open`): a body represented one local binder deeper is represented,
  one opening depth deeper, by its instantiation at the fresh variable `.fvar d T`, under a ghost
  context that gives the new variable `T` and agrees with the old one below `d`.
* **Scope** (`Tm.wscopedB`): a term represented at opening depth `d` over a scoped ghost context
  (`GhostScoped`) is scoped at `d`.
* **The table's keys** (`keyOf_*`): under a well-formed table, the key of an address the table
  binds to a role is that role, and an address keyed by a role is the one the table binds it to. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel (Expr)

/-! ## Substitution on closed values -/

/-- **A `let`'s image on a closed value** is the plain instantiation. -/
theorem instShift_eq_instantiate1 {V : KExpr} (hV : V.looseBVarsBounded 0 = true) (j : Nat)
    (B : KExpr) : instShift V j B = B.instantiate1 V j :=
  Expr.instantiate1Lift_eq_instantiate1 hV B j

/-! ## Loose bound variables -/

/-- Lifting the loose bound variables at or above the cutoff by `n` raises their bound by `n`. -/
theorem looseBVarsBounded_liftLooseBVars {n : Nat} :
    ∀ {e : KExpr} {c b : Nat}, e.looseBVarsBounded b = true →
      (e.liftLooseBVars n c).looseBVarsBounded (b + n) = true := by
  intro e
  induction e with
  | bvar i =>
    intro c b hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.liftLooseBVars]
    split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | app f a ihf iha =>
    intro c b hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf hb.1, iha hb.2⟩
  | lam ty body m iht ihb =>
    intro c b hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨iht hb.1, ?_⟩
    have := ihb (c := c + 1) hb.2
    rwa [show b + 1 + n = b + n + 1 by omega] at this
  | forallE ty body m iht ihb =>
    intro c b hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨iht hb.1, ?_⟩
    have := ihb (c := c + 1) hb.2
    rwa [show b + 1 + n = b + n + 1 by omega] at this
  | letE ty v body m iht ihv ihb =>
    intro c b hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨⟨iht hb.1.1, ihv hb.1.2⟩, ?_⟩
    have := ihb (c := c + 1) hb.2
    rwa [show b + 1 + n = b + n + 1 by omega] at this
  | proj s i e ih =>
    intro c b hb
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded]
    exact ih hb
  | _ => intro c b _; simp [Expr.liftLooseBVars, Expr.looseBVarsBounded]

/-- **The capture-avoiding instantiation keeps a bound**: substituting at `j` a value bounded at
`m - j` into a term bounded at `m + 1` (with `j ≤ m`) gives a term bounded at `m`. -/
theorem looseBVarsBounded_instantiate1Lift {v : KExpr} :
    ∀ {e : KExpr} {j m : Nat}, j ≤ m → e.looseBVarsBounded (m + 1) = true →
      v.looseBVarsBounded (m - j) = true → (e.instantiate1Lift v j).looseBVarsBounded m = true := by
  intro e
  induction e with
  | bvar i =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at he
    simp only [Expr.instantiate1Lift]
    split
    · have := looseBVarsBounded_liftLooseBVars (n := j) (c := 0) hv
      rwa [show m - j + j = m by omega] at this
    · split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | app f a ihf iha =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf hjm he.1 hv, iha hjm he.2 hv⟩
  | lam ty body m' iht ihb =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hjm he.1 hv, ihb (by omega) he.2 (by rwa [show m + 1 - (j + 1) = m - j by omega])⟩
  | forallE ty body m' iht ihb =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hjm he.1 hv, ihb (by omega) he.2 (by rwa [show m + 1 - (j + 1) = m - j by omega])⟩
  | letE ty val body m' iht ihv ihb =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht hjm he.1.1 hv, ihv hjm he.1.2 hv⟩,
      ihb (by omega) he.2 (by rwa [show m + 1 - (j + 1) = m - j by omega])⟩
  | proj s i e ih =>
    intro j m hjm he hv
    simp only [Expr.looseBVarsBounded] at he
    simp only [Expr.instantiate1Lift, Expr.looseBVarsBounded]
    exact ih hjm he hv
  | _ => intro j m _ _ _; simp [Expr.instantiate1Lift, Expr.looseBVarsBounded]

/-- **An image at local depth `k` has its loose bound variables below `k`.** -/
theorem Tm.looseBVarsBounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    E.looseBVarsBounded k = true := by
  induction rep with
  | bvarLocal _ _ hi => simpa [Expr.looseBVarsBounded] using hi
  | bvarFree => simp [Expr.looseBVarsBounded]
  | sort => simp [Expr.looseBVarsBounded]
  | const => simp [Expr.looseBVarsBounded]
  | app _ _ _ ihf iha => simp [Expr.looseBVarsBounded, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Expr.looseBVarsBounded, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Expr.looseBVarsBounded, iht, ihb]
  | @letE k _ _ _ _ _ _ _ _ _ _ _ _ ihv ihb =>
    exact looseBVarsBounded_instantiate1Lift (Nat.zero_le k) ihb (by simpa using ihv)
  | litNat => simp [Expr.looseBVarsBounded]
  | litStr => simp [Expr.looseBVarsBounded]
  | proj _ _ _ ihe => simpa [Expr.looseBVarsBounded] using ihe

/-! ## Opening a binder -/

/-- **Opening a binder**: a term represented at local depth `k + 1` is represented, at opening
depth `d + 1` and local depth `k`, by its instantiation at `k` with the fresh variable
`.fvar d T`, under a ghost context giving the new variable the type `T` and agreeing with `Γ`
below `d`. At `k = 0` this is a binder body read under one more opened variable. -/
theorem Tm.open {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {T : KExpr} (hT : Γ' d = T) (hΓ : ∀ j, j < d → Γ' j = Γ j) {k' : Nat} {E : KExpr}
    {p : SourceValue F} (rep : Tm κ d Γ h k' E p) :
    ∀ k, k' = k + 1 → Tm κ (d + 1) Γ' h k (E.instantiate1 (.fvar d T) k) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi =>
    intro k hk
    subst hk
    simp only [Expr.instantiate1]
    by_cases hik : ZMod.val i = k
    · rw [ite_eq_left hik]
      have hf := Tm.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') cell hs (k := k) (by omega) (by omega)
      have e : fvIdx (d + 1) k (ZMod.val i) = d := by unfold fvIdx; omega
      rw [e, hT] at hf
      exact hf
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    intro k hk'
    subst hk'
    simp only [Expr.instantiate1]
    have hf := Tm.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') cell hs (k := k) (by omega) (by omega)
    have e : fvIdx (d + 1) k (ZMod.val i) = fvIdx d (k + 1) (ZMod.val i) := by
      unfold fvIdx; omega
    rw [e, hΓ _ (by unfold fvIdx; omega)] at hf
    exact hf
  | sort cell rl hu => intro k _; exact .sort cell rl hu
  | const cell ra rls hus => intro k _; exact .const cell ra rls hus
  | app cell _ _ ihf iha =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .app cell (ihf k hk) (iha k hk)
  | lam cell _ _ rl iht ihb =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .lam cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | forallE cell _ _ rl iht ihb =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .forallE cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | @letE k₁ addr tp vp bp T₀ V B cell _ _ _ iht ihv ihb =>
    intro k hk
    have hcomm := Expr.instantiate1Lift_instantiate1 (a := V) (s := (.fvar d T : KExpr))
      (by simp [Expr.looseBVarsBounded]) B 0 k
    simp only [Nat.zero_add] at hcomm
    rw [show (instShift V 0 B).instantiate1 (.fvar d T) k =
        (B.instantiate1Lift V 0).instantiate1 (.fvar d T) k from rfl, hcomm,
      Nat.add_comm 1 k]
    exact .letE cell (iht k hk) (ihv k hk) (ihb (k + 1) (by omega))
  | litNat cell rl hc => intro k _; exact .litNat cell rl hc
  | litStr cell rb hs => intro k _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro k hk
    simp only [Expr.instantiate1]
    exact .proj cell ra (ihe k hk)

/-- **A binder body read under one more opened variable** (`Tm.open` at local depth `0`). -/
theorem Tm.open_body {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {T B : KExpr} {p : SourceValue F} (hT : Γ' d = T) (hΓ : ∀ j, j < d → Γ' j = Γ j)
    (rep : Tm κ d Γ h 1 B p) : Tm κ (d + 1) Γ' h 0 (B.instantiate1 (.fvar d T)) p :=
  rep.open hT hΓ 0 rfl

/-- The ghost context extended by the type of the variable opened at `d`. -/
def Ghost.extend (Γ : Nat → KExpr) (d : Nat) (T : KExpr) : Nat → KExpr :=
  fun j => if j = d then T else Γ j

theorem Ghost.extend_at (Γ : Nat → KExpr) (d : Nat) (T : KExpr) : Ghost.extend Γ d T d = T := by
  simp [Ghost.extend]

theorem Ghost.extend_below (Γ : Nat → KExpr) (d : Nat) (T : KExpr) :
    ∀ j, j < d → Ghost.extend Γ d T j = Γ j := by
  intro j hj
  simp [Ghost.extend, Nat.ne_of_lt hj]

/-- **Opening keeps the ghost context scoped** when the new variable's type is scoped at `d`. -/
theorem GhostScoped.extend {Γ : Nat → KExpr} {d : Nat} {T : KExpr} (hs : GhostScoped Γ d)
    (hT : T.wscopedB d = true) : GhostScoped (Ghost.extend Γ d T) (d + 1) := by
  intro j hj
  by_cases e : j = d
  · subst e; simpa [Ghost.extend] using hT
  · simpa [Ghost.extend, e] using hs j (by omega)

/-! ## Scope -/

/-- Lifting loose bound variables keeps the opened variables. -/
theorem wscopedB_liftLooseBVars {n : Nat} {d : Nat} :
    ∀ {e : KExpr} {c : Nat}, e.wscopedB d = true → (e.liftLooseBVars n c).wscopedB d = true := by
  intro e
  induction e with
  | bvar i => intro c _; simp only [Expr.liftLooseBVars]; split <;> simp [Expr.wscopedB]
  | fvar idx ty => intro c he; simpa [Expr.liftLooseBVars] using he
  | app f a ihf iha =>
    intro c he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.liftLooseBVars, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihf he.1, iha he.2⟩
  | lam ty body m iht ihb =>
    intro c he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.liftLooseBVars, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht he.1, ihb he.2⟩
  | forallE ty body m iht ihb =>
    intro c he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.liftLooseBVars, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht he.1, ihb he.2⟩
  | letE ty v body m iht ihv ihb =>
    intro c he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.liftLooseBVars, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨⟨iht he.1.1, ihv he.1.2⟩, ihb he.2⟩
  | proj s i e ih =>
    intro c he
    simp only [Expr.wscopedB] at he
    simp only [Expr.liftLooseBVars, Expr.wscopedB]
    exact ih he
  | _ => intro c _; simp [Expr.liftLooseBVars, Expr.wscopedB]

/-- The capture-avoiding instantiation keeps the opened variables. -/
theorem wscopedB_instantiate1Lift {d : Nat} {v : KExpr} (hv : v.wscopedB d = true) :
    ∀ {e : KExpr} {j : Nat}, e.wscopedB d = true → (e.instantiate1Lift v j).wscopedB d = true := by
  intro e
  induction e with
  | bvar i =>
    intro j _
    simp only [Expr.instantiate1Lift]
    split
    · exact wscopedB_liftLooseBVars hv
    · split <;> simp [Expr.wscopedB]
  | fvar idx ty => intro j he; simpa [Expr.instantiate1Lift] using he
  | app f a ihf iha =>
    intro j he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihf he.1, iha he.2⟩
  | lam ty body m iht ihb =>
    intro j he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht he.1, ihb he.2⟩
  | forallE ty body m iht ihb =>
    intro j he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht he.1, ihb he.2⟩
  | letE ty val body m iht ihv ihb =>
    intro j he
    simp only [Expr.wscopedB, Bool.and_eq_true] at he
    simp only [Expr.instantiate1Lift, Expr.wscopedB, Bool.and_eq_true]
    exact ⟨⟨iht he.1.1, ihv he.1.2⟩, ihb he.2⟩
  | proj s i e ih =>
    intro j he
    simp only [Expr.wscopedB] at he
    simp only [Expr.instantiate1Lift, Expr.wscopedB]
    exact ih he
  | _ => intro j _; simp [Expr.instantiate1Lift, Expr.wscopedB]

/-- **A represented term is scoped** at its opening depth, over a scoped ghost context. -/
theorem Tm.wscopedB {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (hs : GhostScoped Γ d) (rep : Tm κ d Γ h k E p) :
    E.wscopedB d = true := by
  induction rep with
  | bvarLocal => simp [Expr.wscopedB]
  | @bvarFree k addr i cell _ hk hd =>
    simp only [Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by unfold fvIdx; omega, hs _ (by unfold fvIdx; omega)⟩
  | sort => simp [Expr.wscopedB]
  | const => simp [Expr.wscopedB]
  | app _ _ _ ihf iha => simp [Expr.wscopedB, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Expr.wscopedB, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Expr.wscopedB, iht, ihb]
  | letE _ _ _ _ _ ihv ihb => exact wscopedB_instantiate1Lift ihv ihb
  | litNat => simp [Expr.wscopedB]
  | litStr => simp [Expr.wscopedB]
  | proj _ _ _ ihe => simpa [Expr.wscopedB] using ihe

/-! ## The table's keys -/

/-- A well-formed table passes its check. -/
theorem RoleTable.check_of_wf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) : t.check = .ok () := by
  unfold Ix.Kernel.RoleTable.wf at hwf
  cases hc : t.check with
  | ok u => rfl
  | error e => rw [hc] at hwf; simp [Except.isOk, Except.toBool] at hwf

/-- Pairs of a list whose first components are distinct are determined by them. -/
theorem eq_of_nodup_map_fst {α β : Type} :
    ∀ {l : List (α × β)} {p q : α × β}, (l.map (·.1)).Nodup → p ∈ l → q ∈ l → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => nomatch hp
  | x :: l, p, q, hn, hp, hq, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hp with hpx | hpl <;> rcases List.mem_cons.mp hq with hqx | hql
    · rw [hpx, hqx]
    · subst hpx; exact absurd ⟨q, hql, he.symm⟩ hn.1
    · subst hqx; exact absurd ⟨p, hpl, he⟩ hn.1
    · exact eq_of_nodup_map_fst hn.2 hpl hql he

/-- **The key of an address the table binds to a role is the role**, under a well-formed table
(no address bound to two roles). -/
theorem keyOf_of_addressOf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {r : Ix.Kernel.Role}
    {a : _root_.Address} (h : t.addressOf? r = some a) : keyOf t a = .role r := by
  have hc := RoleTable.check_of_wf hwf
  unfold Ix.Kernel.RoleTable.addressOf? at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp1 : p.1 = r := by simpa using Array.find?_some hp
  have hmp := Array.mem_of_find?_eq_some hp
  unfold keyOf
  cases hq : t.bound.find? (·.2 == p.2) with
  | none =>
    exfalso
    have := Array.find?_eq_none.mp hq p hmp
    simp at this
  | some q =>
    have hq2 : q.2 = p.2 := by simpa using Array.find?_some hq
    have hmq := Array.mem_of_find?_eq_some hq
    have heq := Ix.Kernel.RoleTable.eq_of_nodup_map_snd (Ix.Kernel.RoleTable.check_nodup hc).2
      (Array.mem_toList_iff.mpr hmq) (Array.mem_toList_iff.mpr hmp) hq2
    subst heq
    rw [← hp1]

/-- **An address keyed by a role is the one the table binds the role to**, under a well-formed
table. -/
theorem addressOf_of_keyOf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {r : Ix.Kernel.Role}
    {a : _root_.Address} (h : keyOf t a = .role r) : t.addressOf? r = some a := by
  have hc := RoleTable.check_of_wf hwf
  unfold keyOf at h
  cases hq : t.bound.find? (·.2 == a) with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    have hq1 : q.1 = r := by cases h; rfl
    have hq2 : q.2 = a := by simpa using Array.find?_some hq
    have hmq := Array.mem_of_find?_eq_some hq
    unfold Ix.Kernel.RoleTable.addressOf?
    cases hp : t.bound.find? (·.1 == r) with
    | none =>
      exfalso
      have := Array.find?_eq_none.mp hp q hmq
      simp [hq1] at this
    | some p =>
      have hp1 : p.1 = r := by simpa using Array.find?_some hp
      have hmp := Array.mem_of_find?_eq_some hp
      have heq := eq_of_nodup_map_fst (Ix.Kernel.RoleTable.check_nodup hc).1
        (Array.mem_toList_iff.mpr hmp) (Array.mem_toList_iff.mpr hmq) (hp1.trans hq1.symm)
      simp [heq, hq2]

/-- **A key is a role exactly at the address the table binds it to**, under a well-formed
table. -/
theorem keyOf_eq_role_iff {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {r : Ix.Kernel.Role}
    {a : _root_.Address} : keyOf t a = .role r ↔ t.addressOf? r = some a :=
  ⟨addressOf_of_keyOf hwf, keyOf_of_addressOf hwf⟩

/-- **An address the table binds to no role is keyed by itself.** -/
theorem keyOf_of_unbound {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {a : _root_.Address}
    (h : ∀ r, t.addressOf? r ≠ some a) : keyOf t a = .id a := by
  unfold keyOf
  cases hq : t.bound.find? (·.2 == a) with
  | none => rfl
  | some q =>
    exfalso
    obtain ⟨qr, qa⟩ := q
    apply h qr
    apply addressOf_of_keyOf hwf
    unfold keyOf
    rw [hq]


/-! ## The context list as a list -/

/-- **The entries of a segment of `Γ` ending at `d` with `n` entries**, innermost first: the
opened variable `d - 1 - i` and its type, for `i < n`. -/
def segEntries (Γ : Nat → KExpr) (d n : Nat) : List (Nat × KExpr) :=
  (List.range n).map fun i => (d - 1 - i, Γ (d - 1 - i))

/-- An entry of the context list: the type of the opened variable `e.1`, represented at that
depth. -/
def SegEntryRep (κ : _root_.Address → KKey) (Γ : Nat → KExpr) (h : Heap F) (e : Nat × KExpr)
    (v : SourceValue F) : Prop :=
  Tm κ e.1 Γ h 0 e.2 v

theorem segEntryRep_heapMono₂ (κ : _root_.Address → KKey) (Γ : Nat → KExpr) :
    HeapMono₂ (SegEntryRep κ Γ) := by
  intro h₁ h₂ e v ext r
  exact Tm.mono ext r

theorem segEntries_succ (Γ : Nat → KExpr) (d n : Nat) :
    segEntries Γ (d + 1) (n + 1) = (d, Γ d) :: segEntries Γ d n := by
  unfold segEntries
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp
  intro a _
  have e : d - (a + 1) = d - 1 - a := by omega
  exact ⟨e, by rw [e]⟩

/-- **A context list is a list of segment entries**: of some `n ≤ d` entries ending at `d`. -/
theorem TypesRep.toRepList {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {d : Nat}
    {p : SourceValue F} (r : TypesRep κ Γ h d p) :
    ∃ n, n ≤ d ∧ RepList kexprListEnum (SegEntryRep κ Γ) h (segEntries Γ d n) p := by
  induction r with
  | nil cell => exact ⟨0, Nat.zero_le _, by simpa [segEntries] using RepLinkedList.nil cell⟩
  | @cons d addr tp rest cell rt _ ih =>
    obtain ⟨n, hn, hl⟩ := ih
    refine ⟨n + 1, by omega, ?_⟩
    rw [segEntries_succ]
    exact .cons cell rt hl

/-- **A list of segment entries is a context list.** -/
theorem TypesRep.ofRepList {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {n d : Nat} {p : SourceValue F}, n ≤ d →
      RepList kexprListEnum (SegEntryRep κ Γ) h (segEntries Γ d n) p → TypesRep κ Γ h d p := by
  intro n
  induction n with
  | zero =>
    intro d p _ hl
    simp only [segEntries, List.range_zero, List.map_nil] at hl
    cases hl with
    | nil cell => exact .nil cell
  | succ n ih =>
    intro d p hn hl
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [segEntries_succ] at hl
    cases hl with
    | cons cell headRep tailRep => exact .cons cell headRep (ih (by omega) tailRep)

/-- The innermost `m` entries of a segment are a segment ending at the same depth. -/
theorem segEntries_take (Γ : Nat → KExpr) (d n m : Nat) :
    (segEntries Γ d n).take m = segEntries Γ d (min m n) := by
  unfold segEntries
  rw [← List.map_take, List.take_range]

/-- **Keeping the innermost entries of a context list keeps it a context list at the same
depth** (`Lists::take` on `types`, as `ctx_trim` does): the ghost context and the depth are
unchanged, so every judgement read at the trimmed list is read at the same `d` and `Γ`. -/
theorem TypesRep.take {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h h' : Heap F} {d : Nat}
    {p q : SourceValue F} (r : TypesRep κ Γ h d p)
    (htake : ∀ (xs : List (Nat × KExpr)), RepList kexprListEnum (SegEntryRep κ Γ) h xs p →
      ∃ m, RepList kexprListEnum (SegEntryRep κ Γ) h' (xs.take m) q) :
    TypesRep κ Γ h' d q := by
  obtain ⟨n, hn, hl⟩ := r.toRepList
  obtain ⟨m, hq⟩ := htake _ hl
  rw [segEntries_take] at hq
  exact TypesRep.ofRepList (by omega) hq

end IxVM.Refinement.Core
