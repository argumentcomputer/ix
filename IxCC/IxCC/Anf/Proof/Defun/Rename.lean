import IxCC.Anf.Proof.Defun.Scope
import IxCC.Anf.Proof.Unfold

/-! # Renaming free variables is exact on code without local functions

`Exp.renameVars f d e` renames the variables of `e` free under `d` binders by
`f`. On code with no `fn` (and no `app`), evaluating the renamed code in an
environment `ρ'` is evaluating `e` in `ρ` whenever `ρ'` holds at each
renamed free variable what `ρ` holds at the variable (`eval_rename`), with
join closures related the same way (`JRen`); a closure built by an `fn` would
capture the renamed code, which is why local functions are excluded. P8's
lifted bodies are such code: the walk's image of a local function's body,
renamed onto its captures (`capRen`). Over the lifted global's parameters,
the captures' values then the arguments, the renamed body reads what the
image reads over the arguments and the environment the captures came from
(`capRen_env`). By induction on the clock, and on the term at each clock. -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Result later later_succ later_zero)

/-- Where `Exp.renameVars f d` sends the variable at index `x`. -/
def ren (f : Nat → Nat) (d x : Nat) : Nat := if x < d then x else d + f (x - d)

theorem ren_zero_base (f : Nat → Nat) (x : Nat) : ren f 0 x = f x := by
  unfold ren
  rw [ite_eq_right (Nat.not_lt_zero x), Nat.zero_add, Nat.sub_zero]

theorem ren_lt {f : Nat → Nat} {d n x : Nat} (h : x < n) : ren f (d + n) x = x := by
  unfold ren
  rw [ite_eq_left (by omega)]

theorem ren_ge {f : Nat → Nat} {d n x : Nat} (h : n ≤ x) : ren f (d + n) x = ren f d (x - n) + n := by
  unfold ren
  by_cases h1 : x < d + n
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right h1, ite_eq_right (by omega)]
    have : x - (d + n) = x - n - d := by omega
    rw [this]
    omega

/-- Pushing `n` values under the renaming: a free variable of `b` below `n`
reads a pushed value on both sides, one at or above `n` reads through the
renaming. -/
theorem ren_push {f : Nat → Nat} {d n : Nat} {ρ ρ' vs : List Val} {b : Exp} (hn : vs.length = n)
    (h : ∀ x ∈ b.free n, ρ'[ren f d x]? = ρ[x]?) :
    ∀ x ∈ b.free 0, (vs ++ ρ')[ren f (d + n) x]? = (vs ++ ρ)[x]? := by
  intro x hx
  by_cases hxn : x < n
  · rw [ren_lt hxn, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · have hge : n ≤ x := by omega
    rw [ren_ge hge, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hn,
      Nat.add_sub_cancel]
    apply h
    have := free_shift (d := 0) (k := n) (x := x - n) (e := b) (by rw [Nat.sub_add_cancel hge]; exact hx)
    rwa [Nat.zero_add] at this

/-! ## Atoms -/

theorem atom_rename_eval {f : Nat → Nat} {d : Nat} {ρ ρ' : List Val} :
    ∀ {a : Atom}, (∀ x ∈ a.free 0, ρ'[ren f d x]? = ρ[x]?) → (Atom.renameVars f d a).eval ρ' = a.eval ρ
  | .var i, h => by
    have := h i (by simp [Atom.free])
    unfold ren at this
    simp only [Atom.renameVars]
    by_cases hi : i < d
    · rw [ite_eq_left hi] at this ⊢
      exact this
    · rw [ite_eq_right hi] at this ⊢
      exact this
  | .lit _, _ => rfl
  | .box, _ => rfl

theorem atoms_rename_eval {f : Nat → Nat} {d : Nat} {ρ ρ' : List Val} :
    ∀ {as : List Atom}, (∀ x ∈ Atom.freeList 0 as, ρ'[ren f d x]? = ρ[x]?) →
      evalAtoms ρ' (Atom.renameList f d as) = evalAtoms ρ as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Atom.renameList]
    rw [evalAtoms_cons, evalAtoms_cons,
      atom_rename_eval fun x hx => h x (by simp only [Atom.freeList, List.mem_append]; exact .inl hx),
      atoms_rename_eval fun x hx => h x (by simp only [Atom.freeList, List.mem_append]; exact .inr hx)]

/-! ## Join closures -/

/-- Join closures related by a renaming: the target's body is the source's
renamed under the `d` binders it was made under and its own parameters, and
the source body's free variables read through the renaming. -/
inductive JRen (f : Nat → Nat) : List JClo → List JClo → Prop
  | nil : JRen f [] []
  | cons {ρ ρ' : List Val} {J0 J0' J J' : List JClo} {d n : Nat} {b : Exp} {r : Bool} :
      Exp.firstOrder (fun _ => false) b = true → (∀ x ∈ b.free n, ρ'[ren f d x]? = ρ[x]?) →
      JRen f J0 J0' → JRen f J J' →
      JRen f (.mk ρ J0 n b r :: J) (.mk ρ' J0' n (Exp.renameVars f (d + n) b) r :: J')

theorem JRen.get {f : Nat → Nat} : ∀ {J J' : List JClo}, JRen f J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨ ∃ ρ ρ' J0 J0' d n b r, J[j]? = some (.mk ρ J0 n b r) ∧
      J'[j]? = some (.mk ρ' J0' n (Exp.renameVars f (d + n) b) r) ∧ Exp.firstOrder (fun _ => false) b = true ∧
      (∀ x ∈ b.free n, ρ'[ren f d x]? = ρ[x]?) ∧ JRen f J0 J0'
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hb hρ h0 _, 0 => .inr ⟨_, _, _, _, _, _, _, _, rfl, rfl, hb, hρ, h0⟩
  | _, _, .cons _ _ _ h, j + 1 => by simpa using h.get j

/-! ## Evaluation -/

/-- Renamed code evaluates as its source, at clock `k`. -/
def RenAt (Q : Program) (f : Nat → Nat) (k : Nat) : Prop :=
  ∀ ⦃d : Nat⦄ ⦃e : Exp⦄ ⦃ρ ρ' : List Val⦄ ⦃J J' : List JClo⦄, Exp.firstOrder (fun _ => false) e = true →
    (∀ x ∈ e.free 0, ρ'[ren f d x]? = ρ[x]?) → JRen f J J' →
    eval Q k ρ' J' (Exp.renameVars f d e) = eval Q k ρ J e

theorem later_congr {α : Type} {k : Nat} {F G : Nat → Result α} (h : ∀ m, m + 1 ≤ k → F m = G m) :
    later k F = later k G := by
  cases k with
  | zero => rfl
  | succ k => rw [later_succ, later_succ]; exact h k (Nat.le_refl _)

theorem ren_bind {Q : Program} {f : Nat → Nat} {k d : Nat} {ρ ρ' : List Val} :
    ∀ (b : Bind), Bind.firstOrder (fun _ => false) b = true → (∀ x ∈ b.free 0, ρ'[ren f d x]? = ρ[x]?) →
      evalBind Q k ρ' (Bind.renameVars f d b) = evalBind Q k ρ b
  | .atom a, _, h => by
    simp only [Bind.renameVars]
    rw [evalBind_atom, evalBind_atom, atom_rename_eval h]
  | .con c as, _, h => by
    simp only [Bind.renameVars]
    rw [evalBind_con, evalBind_con, atoms_rename_eval h]
  | .proj c i x, _, h => by
    simp only [Bind.renameVars]
    rw [evalBind_proj, evalBind_proj, atom_rename_eval h]
  | .prim p as, _, h => by
    simp only [Bind.renameVars]
    rw [evalBind_prim, evalBind_prim, atoms_rename_eval h]
  | .glob g, _, _ => by
    simp only [Bind.renameVars]
    rw [evalBind_glob, evalBind_glob]
  | .call g as, _, h => by
    simp only [Bind.renameVars]
    rw [evalBind_call, evalBind_call, atoms_rename_eval h]
  | .app _ _, hfo, _ => by simp [Bind.firstOrder] at hfo
  | .fn _ _, hfo, _ => by simp [Bind.firstOrder] at hfo

section

variable {Q : Program} {f : Nat → Nat} {k : Nat}

mutual

theorem ren_exp (hlow : ∀ m < k, RenAt Q f m) : ∀ (e : Exp) {d : Nat} {ρ ρ' : List Val} {J J' : List JClo},
    Exp.firstOrder (fun _ => false) e = true → (∀ x ∈ e.free 0, ρ'[ren f d x]? = ρ[x]?) → JRen f J J' →
    eval Q k ρ' J' (Exp.renameVars f d e) = eval Q k ρ J e
  | .bind c b e, d, ρ, ρ', J, J', hfo, h, hJ => by
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo
    simp only [Exp.free, List.mem_append] at h
    simp only [Exp.renameVars]
    rw [eval_bind, eval_bind, ren_bind b hfo.1 fun x hx => h x (.inl hx)]
    congr 1
    funext v
    exact ren_exp hlow e hfo.2 (ren_push (vs := [v]) rfl fun x hx => h x (.inr hx)) hJ
  | .join n r b e, d, ρ, ρ', J, J', hfo, h, hJ => by
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo
    simp only [Exp.free, List.mem_append, Nat.zero_add] at h
    simp only [Exp.renameVars]
    rw [eval_join', eval_join']
    exact ren_exp hlow e hfo.2 (fun x hx => h x (.inr hx)) (.cons hfo.1 (fun x hx => h x (.inl hx)) hJ hJ)
  | .jump j as, d, ρ, ρ', J, J', _, h, hJ => by
    simp only [Exp.free] at h
    simp only [Exp.renameVars]
    rw [eval_jump, eval_jump, atoms_rename_eval h]
    rcases hJ.get j with ⟨h1, h2⟩ | ⟨ρj, ρj', J0, J0', dj, n, b, r, h1, h2, hb, hρ, h0⟩
    · rw [h1, h2]
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok]
      cases evalAtoms ρ as with
      | none => rfl
      | some vs =>
        simp only [Result.bind_ok, jumpTo]
        split
        · rename_i hn
          apply later_congr
          intro m hm
          refine hlow m (by omega) hb (ren_push (by rw [List.length_reverse]; exact hn) hρ) ?_
          cases r
          · exact h0
          · exact .cons hb hρ h0 h0
        · rfl
  | .case x alts dft, d, ρ, ρ', J, J', hfo, h, hJ => by
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo
    simp only [Exp.free, List.mem_append] at h
    simp only [Exp.renameVars]
    rw [eval_case, eval_case, atom_rename_eval fun y hy => h y (.inl (.inl hy))]
    cases x.eval ρ with
    | none => rfl
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      cases v.asCtor Q.known with
      | none => rfl
      | some cf =>
        obtain ⟨c, fs⟩ := cf
        exact ren_alts hlow alts hfo.1 (fun y hy => h y (.inl (.inr hy))) hJ
          (ren_opt hlow dft hfo.2 (fun y hy => h y (.inr hy)) hJ)
  | .ret a, d, ρ, ρ', J, J', _, h, _ => by
    simp only [Exp.free] at h
    simp only [Exp.renameVars]
    rw [eval_ret', eval_ret', atom_rename_eval h]
  | .tick e, d, ρ, ρ', J, J', hfo, h, hJ => by
    simp only [Exp.firstOrder] at hfo
    simp only [Exp.free] at h
    simp only [Exp.renameVars]
    rw [eval_tick, eval_tick]
    exact later_congr fun m hm => hlow m (by omega) hfo h hJ
  | .trap, _, _, _, _, _, _, _, _ => by
    simp only [Exp.renameVars]
    rw [eval_trap', eval_trap']

theorem ren_opt (hlow : ∀ m < k, RenAt Q f m) : ∀ (o : Option Exp) {d : Nat} {ρ ρ' : List Val}
    {J J' : List JClo}, Exp.optFirstOrder (fun _ => false) o = true →
    (∀ x ∈ Exp.optFree 0 o, ρ'[ren f d x]? = ρ[x]?) → JRen f J J' →
    ∀ e, o = some e → eval Q k ρ' J' (Exp.renameVars f d e) = eval Q k ρ J e
  | none, _, _, _, _, _, _, _, _, _, he => nomatch he
  | some e, _, _, _, _, _, hfo, h, hJ, _, he => by
    cases he
    simp only [Exp.optFirstOrder] at hfo
    simp only [Exp.optFree] at h
    exact ren_exp hlow e hfo h hJ

theorem ren_alts (hlow : ∀ m < k, RenAt Q f m) : ∀ (alts : List Alt) {d : Nat} {ρ ρ' : List Val}
    {J J' : List JClo} {c : Key.CtorKey} {fs : List Val} {dft : Option Exp},
    Exp.altsFirstOrder (fun _ => false) alts = true →
    (∀ x ∈ Exp.altsFree 0 alts, ρ'[ren f d x]? = ρ[x]?) → JRen f J J' →
    (∀ e, dft = some e → eval Q k ρ' J' (Exp.renameVars f d e) = eval Q k ρ J e) →
    evalAlts Q k ρ' J' c fs (Exp.renameAlts f d alts) (Exp.renameOpt f d dft) = evalAlts Q k ρ J c fs alts dft
  | [], d, ρ, ρ', J, J', c, fs, dft, _, _, _, hd => by
    simp only [Exp.renameAlts]
    cases dft with
    | none =>
      simp only [Exp.renameOpt]
      rw [evalAlts_nil, evalAlts_nil]
    | some e =>
      simp only [Exp.renameOpt]
      rw [evalAlts_nil, evalAlts_nil]
      exact hd e rfl
  | .mk key n b :: rest, d, ρ, ρ', J, J', c, fs, dft, hfa, ha, hJ, hd => by
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at hfa
    simp only [Exp.altsFree, List.mem_append, Nat.zero_add] at ha
    simp only [Exp.renameAlts]
    rw [evalAlts_cons, evalAlts_cons]
    split
    · rename_i hsel
      exact ren_exp hlow b hfa.1 (ren_push (by rw [List.length_reverse]; exact hsel.2.symm)
        fun x hx => ha x (.inl hx)) hJ
    · exact ren_alts hlow rest hfa.2 (fun x hx => ha x (.inr hx)) hJ hd

end

end

/-- **Renaming is exact on code without local functions**, at every clock. -/
theorem eval_rename (Q : Program) (f : Nat → Nat) : ∀ k, RenAt Q f k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro d e ρ ρ' J J' hfo h hJ
  exact ren_exp (fun m hm => ih m hm) e hfo h hJ

/-! ## The captures' renaming -/

theorem captures_lt {Γ x : Nat} {free : List Nat} (h : x ∈ captures Γ free) : x < Γ := by
  unfold captures at h
  simp only [List.mem_reverse, List.mem_filter, List.mem_range] at h
  exact h.1

theorem captures_nodup (Γ : Nat) (free : List Nat) : (captures Γ free).Nodup := by
  unfold captures
  exact (List.reverse_perm _).nodup_iff.2 (List.nodup_range.filter _)

theorem capMap_get {caps : List Nat} (hnd : caps.Nodup) {p y : Nat} (hp : caps[p]? = some y) :
    (capMap caps).getD y 0 = caps.length - 1 - p := by
  unfold capMap Src.NatMap.getD
  have hkeys : ((caps.zipIdx.map fun (x, p) => (x, caps.length - 1 - p)).map (·.1)).Nodup := by
    rw [List.map_map]
    have : (caps.zipIdx.map ((·.1) ∘ fun (x, p) => (x, caps.length - 1 - p))) = caps := by
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
      cases caps[j]? <;> rfl
    rw [this]
    exact hnd
  rw [Src.NatMap.get?_ofList hkeys (List.mem_map.2 ⟨(y, p), List.mem_zipIdx_iff_getElem?.2 hp, rfl⟩)]
  rfl

/-- **The captures' renaming**: over the captures' values (from a target
environment `ρ'` of at least the depth `Γ` they come from) pushed below `n`
values `A`, the lifted body's renamed variable `x` reads what `x` reads over
`A` and `ρ'`, for each `x` below `n` or capturing. -/
theorem capRen_env {Γ : Nat} {free : List Nat} {n : Nat} {A ρ' : List Val} (hA : A.length = n)
    (hlen : Γ ≤ ρ'.length) :
    ∀ x, (x < n ∨ x - n ∈ captures Γ free) →
      (A ++ ((captures Γ free).map fun y => ρ'.getD y .box).reverse)[capRen (captures Γ free) n x]? =
        (A ++ ρ')[x]? := by
  intro x hx
  unfold capRen
  by_cases hxn : x < n
  · rw [ite_eq_left hxn, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · rw [ite_eq_right hxn]
    have hy : x - n ∈ captures Γ free := hx.resolve_left hxn
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hy
    have hplt : p < (captures Γ free).length := (List.getElem?_eq_some_iff.1 hp).1
    rw [capMap_get (captures_nodup Γ free) hp, List.getElem?_append_right (by omega), hA,
      Nat.add_sub_cancel_left, List.getElem?_append_right (by omega), hA,
      List.getElem?_reverse (by rw [List.length_map]; omega), List.length_map]
    have e : (captures Γ free).length - 1 - ((captures Γ free).length - 1 - p) = p := by omega
    rw [e, List.getElem?_map, hp]
    have hlt : x - n < ρ'.length := Nat.lt_of_lt_of_le (captures_lt hy) hlen
    rw [List.getElem?_eq_getElem hlt, Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl

end IxCC.Anf.Defun.Proof
