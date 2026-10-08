import Ix.CompileCert.Pj.Tele

/-! Typed argument tuples for dependent telescopes. Binder metadata is kept in
the installed telescope; this relation records precisely the domain denotations
and argument memberships, with the valuation extended after every argument. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (InstalledTelescope pushArguments ValuationLift DenotesSpine)

universe u

inductive TeleTyped {V : Type u} [Kernel.SetTheory V]
    (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (φ : Kernel.Name → Nat) : (Nat → V) → List Kernel.Expr → List V → Prop
  | nil {ρ} : TeleTyped cval env φ ρ [] []
  | cons {ρ t ts x xs A}
      (domain : Kernel.Denotes cval env φ ρ t A)
      (member : x ∈ˢ A)
      (rest : TeleTyped cval env φ (Kernel.push x ρ) ts xs) :
      TeleTyped cval env φ ρ (t :: ts) (x :: xs)

section Tuples

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
  {φ : Kernel.Name → Nat}

theorem TeleTyped.length {ρ : Nat → V} {ts : List Kernel.Expr} {xs : List V}
    (typed : TeleTyped cval env φ ρ ts xs) : xs.length = ts.length := by
  induction typed with
  | nil => rfl
  | cons _ _ _ ih => simp only [List.length_cons, ih]

theorem TeleTyped.cons_iff {ρ : Nat → V} {t : Kernel.Expr} {ts : List Kernel.Expr}
    {x : V} {xs : List V} :
    TeleTyped cval env φ ρ (t :: ts) (x :: xs) ↔
      ∃ A, Kernel.Denotes cval env φ ρ t A ∧ x ∈ˢ A ∧
        TeleTyped cval env φ (Kernel.push x ρ) ts xs := by
  constructor
  · intro typed
    cases typed with
    | cons domain member rest => exact ⟨_, domain, member, rest⟩
  · rintro ⟨A, domain, member, rest⟩
    exact .cons domain member rest

theorem TeleTyped.append {ρ : Nat → V} {ts us : List Kernel.Expr} {xs ys : List V}
    (first : TeleTyped cval env φ ρ ts xs)
    (second : TeleTyped cval env φ (pushArguments ρ xs) us ys) :
    TeleTyped cval env φ ρ (ts ++ us) (xs ++ ys) := by
  induction first with
  | nil => exact second
  | cons domain member rest ih => exact .cons domain member (ih second)

theorem TeleTyped.installed {bs : List (Kernel.Expr × Kernel.BinderMeta)} {b : Kernel.Expr}
    {ρ : Nat → V} {xs : List V} (typed : TeleTyped cval env φ ρ (bs.map Prod.fst) xs) :
    InstalledTelescope cval env φ ρ (piJoin bs b) xs (pushArguments ρ xs) b := by
  induction bs generalizing ρ xs with
  | nil => cases typed; exact .nil
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    cases typed with
    | cons domain member rest => exact .cons domain member (ih rest)

theorem TeleTyped.of_installed {bs : List (Kernel.Expr × Kernel.BinderMeta)}
    {b result : Kernel.Expr} {ρ finalρ : Nat → V} {xs : List V}
    (tuple : InstalledTelescope cval env φ ρ (piJoin bs b) xs finalρ result)
    (length : xs.length = bs.length) : TeleTyped cval env φ ρ (bs.map Prod.fst) xs := by
  induction bs generalizing ρ xs with
  | nil =>
    cases xs with
    | nil => exact .nil
    | cons x xs => simp at length
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    cases xs with
    | nil => simp at length
    | cons x xs =>
      cases tuple with
      | cons domain member rest =>
        exact .cons domain member (ih rest (by simpa using length))

/-- Exact agreement with the installed telescope, including its final valuation
and residual. The argument count prevents a partial prefix from being confused
with a complete tuple. -/
theorem installed_piJoin_iff {bs : List (Kernel.Expr × Kernel.BinderMeta)}
    {b result : Kernel.Expr} {ρ finalρ : Nat → V} {xs : List V} :
    (InstalledTelescope cval env φ ρ (piJoin bs b) xs finalρ result ∧
      xs.length = bs.length) ↔
    (TeleTyped cval env φ ρ (bs.map Prod.fst) xs ∧
      finalρ = pushArguments ρ xs ∧ result = b) := by
  constructor
  · rintro ⟨tuple, length⟩
    refine ⟨TeleTyped.of_installed tuple length, tuple.final_valuation, ?_⟩
    apply tuple.result_of_stripPis
    rw [length]
    exact stripPis_piJoin bs b
  · rintro ⟨typed, rfl, rfl⟩
    exact ⟨typed.installed, by simpa only [List.length_map] using typed.length⟩

theorem teleTyped_apply {bs : List (Kernel.Expr × Kernel.BinderMeta)} {b : Kernel.Expr}
    {ρ : Nat → V} {xs : List V} {T f : V}
    (typeRead : Kernel.Denotes cval env φ ρ (piJoin bs b) T) (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ ρ (bs.map Prod.fst) xs) :
    ∃ B, Kernel.Denotes cval env φ (pushArguments ρ xs) b B ∧ xs.foldl app f ∈ˢ B :=
  typed.installed.apply typeRead member

/-- Lifting a list of dependent domains advances the cutoff at every binder. -/
def liftTypes (amount : Nat) : Nat → List Kernel.Expr → List Kernel.Expr
  | _, [] => []
  | cutoff, t :: ts => t.liftLooseBVars amount cutoff :: liftTypes amount (cutoff + 1) ts

theorem TeleTyped.lift {ts : List Kernel.Expr} {xs : List V} {ρ target : Nat → V}
    {amount cutoff : Nat} (typed : TeleTyped cval env φ ρ ts xs)
    (related : ValuationLift amount cutoff ρ target) :
    TeleTyped cval env φ target (liftTypes amount cutoff ts) xs := by
  induction typed generalizing cutoff target with
  | nil => exact .nil
  | cons domain member rest ih =>
    exact .cons (Ix.CompileCert.denotes_lift domain related) member (ih (related.push _))

theorem TeleTyped.unlift {ts : List Kernel.Expr} {xs : List V} {ρ target : Nat → V}
    {amount cutoff : Nat} (related : ValuationLift amount cutoff ρ target)
    (typed : TeleTyped cval env φ target (liftTypes amount cutoff ts) xs) :
    TeleTyped cval env φ ρ ts xs := by
  induction ts generalizing ρ target cutoff xs with
  | nil => cases typed; exact .nil
  | cons t ts ih =>
    cases xs with
    | nil => cases typed
    | cons x xs =>
      obtain ⟨A, domain, member, rest⟩ := TeleTyped.cons_iff.mp typed
      exact .cons (denotes_unlift amount t related domain) member
        (ih (related.push x) rest)

/-- Grading of the body at every complete typed argument tuple. -/
theorem graded_piJoin {bs : List (Kernel.Expr × Kernel.BinderMeta)} {b : Kernel.Expr}
    {ρ : Nat → V} {xs : List V}
    (graded : Bridge.Graded cval env φ ρ (piJoin bs b))
    (typed : TeleTyped cval env φ ρ (bs.map Prod.fst) xs) :
    Bridge.Graded cval env φ (pushArguments ρ xs) b := by
  induction bs generalizing ρ xs with
  | nil => cases typed; exact graded
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    cases xs with
    | nil => cases typed
    | cons x xs =>
      obtain ⟨A, domain, member, rest⟩ := TeleTyped.cons_iff.mp typed
      obtain ⟨_, B, readB, body, _⟩ := graded
      have equal : A = B := Kernel.Denotes_functional domain readB
      exact ih (ρ := Kernel.push x ρ) (xs := xs) (body x (equal ▸ member)) rest


/-- Inserting arguments at the bottom of the de Bruijn valuation. -/
omit [Kernel.SetTheory V] in
theorem valuationLift_prefix (ρ : Nat → V) (xs : List V) :
    ValuationLift xs.length 0 ρ (pushArguments ρ xs) := by
  intro i
  simpa only [Nat.zero_le, ↓reduceIte, Nat.add_comm i] using
    Ix.CompileCert.pushArguments_above xs ρ i

/-- A common suffix of arguments advances an existing insertion cutoff. -/
omit [Kernel.SetTheory V] in
theorem valuationLift_pushArguments {ρ target : Nat → V} {amount cutoff : Nat}
    (related : ValuationLift amount cutoff ρ target) (xs : List V) :
    ValuationLift amount (cutoff + xs.length)
      (pushArguments ρ xs) (pushArguments target xs) := by
  induction xs generalizing ρ target cutoff with
  | nil => simpa only [List.length_nil, Nat.add_zero, pushArguments] using related
  | cons x xs ih =>
    have next := ih (related.push x)
    simpa only [pushArguments, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using next

/-- Motives inserted between parameters and fields do not change the readings
of the appropriately lifted parameter/field terms. -/
omit [Kernel.SetTheory V] in
theorem valuationLift_middle (ρ : Nat → V) (ps ms fs : List V) :
    ValuationLift ms.length fs.length
      (pushArguments ρ (ps ++ fs)) (pushArguments ρ (ps ++ ms ++ fs)) := by
  have inserted := valuationLift_prefix (pushArguments ρ ps) ms
  have extended := valuationLift_pushArguments inserted fs
  simpa only [Ix.CompileCert.pushArguments_append, Nat.zero_add] using extended

/-- Choose one member of each dependent binder domain, with a property that
may depend on the complete prefix already chosen. The whole telescope's
reading supplies each next domain; no denotation is postulated for an
unreachable prefix. -/
theorem tele_pick (bs : List (Kernel.Expr × Kernel.BinderMeta))
    {b : Kernel.Expr} {ρ : Nat → V} {T : V}
    (typeRead : Kernel.Denotes cval env φ ρ (piJoin bs b) T)
    (Q : List V → V → Prop)
    (choose : ∀ before after t m, bs = before ++ (t, m) :: after →
      ∀ xs, TeleTyped cval env φ ρ (before.map Prod.fst) xs →
      ∀ A, Kernel.Denotes cval env φ (pushArguments ρ xs) t A →
      ∃ x, x ∈ˢ A ∧ Q xs x) :
    ∃ xs, TeleTyped cval env φ ρ (bs.map Prod.fst) xs ∧
      ∀ i (bound : i < xs.length), Q (xs.take i) xs[i] := by
  induction bs generalizing ρ T Q with
  | nil =>
    refine ⟨[], .nil, ?_⟩
    intro i bound
    simp at bound
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    obtain ⟨A, B, domain, body, _, _⟩ := Bridge.denotes_pi_inv typeRead
    obtain ⟨x, member, property⟩ := choose [] bs t m rfl [] .nil A domain
    have chooseTail : ∀ before after u n, bs = before ++ (u, n) :: after →
        ∀ xs, TeleTyped cval env φ (Kernel.push x ρ) (before.map Prod.fst) xs →
        ∀ C, Kernel.Denotes cval env φ (pushArguments (Kernel.push x ρ) xs) u C →
        ∃ y, y ∈ˢ C ∧ Q (x :: xs) y := by
      intro before after u n split xs typed C readC
      apply choose ((t, m) :: before) after u n
      · simp only [List.cons_append, split]
      · exact TeleTyped.cons domain member typed
      · exact readC
    obtain ⟨xs, typed, properties⟩ := ih (body x member)
      (fun prior y => Q (x :: prior) y) chooseTail
    refine ⟨x :: xs, .cons domain member typed, ?_⟩
    intro i bound
    cases i with
    | zero => simpa using property
    | succ i =>
      have inside : i < xs.length := by simpa using bound
      simpa only [List.take_succ_cons, List.getElem_cons_succ] using properties i inside

/-- Grading of a complete application spine includes grading of its head. -/
theorem graded_spine_head (args : List Kernel.Expr) {f : Kernel.Expr} {ρ : Nat → V}
    (graded : Bridge.Graded cval env φ ρ (Kernel.Expr.mkAppN f args)) :
    Bridge.Graded cval env φ ρ f := by
  induction args generalizing f with
  | nil => simpa only [Kernel.Expr.mkAppN, List.foldl_nil] using graded
  | cons a args ih =>
    have first : Bridge.Graded cval env φ ρ (.app f a) :=
      ih (by simpa only [Kernel.Expr.mkAppN, List.foldl_cons] using graded)
    exact first.1

/-- A graded application to a member of a graph-regime telescope has arguments
in the telescope's actual dependent domains. The term valuation and the type
valuation may differ; they are connected through the denoted function and the
supplied argument readings, not identified by assumption. -/
theorem typed_of_graded_spine (bs : List (Kernel.Expr × Kernel.BinderMeta))
    {b f : Kernel.Expr} {args : List Kernel.Expr} {xs : List V}
    {termρ typeρ : Nat → V} {F T : V}
    (graphBinders : ∀ p ∈ bs, Kernel.regime φ p.2.pw ≠ 0)
    (graded : Bridge.Graded cval env φ termρ (Kernel.Expr.mkAppN f args))
    (headRead : Kernel.Denotes cval env φ termρ f F)
    (typeRead : Kernel.Denotes cval env φ typeρ (piJoin bs b) T)
    (member : F ∈ˢ T)
    (spine : DenotesSpine cval env φ termρ args xs)
    (length : args.length = bs.length) :
    TeleTyped cval env φ typeρ (bs.map Prod.fst) xs := by
  induction bs generalizing b f args xs termρ typeρ F T with
  | nil =>
    have argsNil : args = [] := List.length_eq_zero_iff.mp length
    subst args
    cases spine
    exact .nil
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    cases args with
    | nil => simp at length
    | cons a args =>
      cases spine with
      | @cons _ x _ xs readArg readRest =>
        have first : Bridge.Graded cval env φ termρ (.app f a) :=
          graded_spine_head args
            (by simpa only [Kernel.Expr.mkAppN, List.foldl_cons] using graded)
        obtain ⟨_, _, G, X, r, A', B', readG, readX, memberG, memberX, _⟩ := first
        have functionEq : G = F := Kernel.Denotes_functional readG headRead
        have argumentEq : X = x := Kernel.Denotes_functional readX readArg
        have gradedMember : F ∈ˢ piR r A' B' := by simpa only [functionEq] using memberG
        have gradedArgument : x ∈ˢ A' := by simpa only [argumentEq] using memberX
        obtain ⟨A, B, domain, body, _, typeEq⟩ := Bridge.denotes_pi_inv typeRead
        have actualMember : F ∈ˢ piR (Kernel.regime φ m.pw) A B := by
          simpa only [typeEq] using member
        have actualPositive : Kernel.regime φ m.pw ≠ 0 :=
          graphBinders (t, m) (List.mem_cons_self ..)
        have gradedPositive : r ≠ 0 := by
          intro zero
          rw [zero] at gradedMember
          exact (mem_piR_pos actualPositive actualMember).2.2.2
            (eq_pt_of_mem_piR_zero gradedMember)
        have domainEq : A = A' :=
          piR_dom_unique actualPositive gradedPositive actualMember gradedMember
        have typedArgument : x ∈ˢ A := by rw [domainEq]; exact gradedArgument
        refine .cons domain typedArgument ?_
        apply ih
          (fun p hp => graphBinders p (List.mem_cons_of_mem _ hp))
          (by simpa only [Kernel.Expr.mkAppN, List.foldl_cons] using graded)
          (Kernel.Denotes.app headRead readArg) (body x typedArgument)
          ((mem_piR_pos actualPositive actualMember).2.1 x typedArgument) readRest
        simpa using length


/-- Universe substitution transports the domains of a typed tuple. The needed
locality law is already a theorem for every strong installed model. -/
theorem TeleTyped.levels (locality : Bridge.CvalLocal cval env)
    (ks : List Kernel.Name) (us : List Kernel.Level)
    {ρ : Nat → V} {ts : List Kernel.Expr} {xs : List V}
    (typed : TeleTyped cval env (Kernel.Level.substFn φ ks us) ρ ts xs) :
    TeleTyped cval env φ ρ (ts.map (fun t => t.instantiateLevelParams ks us)) xs := by
  induction typed with
  | nil => exact .nil
  | cons domain member rest ih =>
    exact .cons (Bridge.denotes_levels locality ks us domain) member ih

/-- When a substitution leaves all binder domains unchanged, the very same
argument tuple is typed at the original assignment. The syntactic independence
premise is explicit; this lemma does not infer it from a recursor read. -/
theorem TeleTyped.fixedLevels (locality : Bridge.CvalLocal cval env)
    (ks : List Kernel.Name) (us : List Kernel.Level)
    {ρ : Nat → V} {ts : List Kernel.Expr} {xs : List V}
    (typed : TeleTyped cval env (Kernel.Level.substFn φ ks us) ρ ts xs)
    (fixed : ∀ t ∈ ts, t.instantiateLevelParams ks us = t) :
    TeleTyped cval env φ ρ ts xs := by
  have same : ts.map (fun t => t.instantiateLevelParams ks us) = ts := by
    calc
      ts.map (fun t => t.instantiateLevelParams ks us) = ts.map id := List.map_congr_left fixed
      _ = ts := List.map_id ts
  rw [← same]
  exact typed.levels locality ks us

end Tuples

end Ix.CompileCert.Pj
