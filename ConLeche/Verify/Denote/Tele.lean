module

public import ConLeche.Verify.Denote.Inst

public section

/-!
# Denoted application spines

`DenoteSpine` — each expression of a spine denotes to the corresponding
term — and the two `mkAppN` transport lemmas built on it.

**What this file used to also hold.**  `TeleTyped`/`VTeleTyped`, the
telescope walk with *typing* where `TeleFitI` had membership, lived
here as the hypothesis of the declarative lane's fired modeled-iota
contract.  That lane was retired (task #148 T7b) and the set route
states its own fit as `TeleFitV` over memberships, so the typed walk
had no consumer left and went with it.  The spine half stayed: it is
denotation-only, judgment-free, and both the bridge's `majorToCtor`
rescues and the iota clause's redex reassembly run on it.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-! ## Spines

`Expr.mkAppN` and `Term.mkAppN` have the same shape, so a denoted
spine transports through an application chain.  Needed wherever a
clause matches on `getAppFn`/`getAppArgs` and the bridge has to
reassemble the denotation — `majorToCtor`'s rescues, and the iota
clause's redex. -/

/-- Each expression of a spine denotes to the corresponding term. -/
inductive DenoteSpine (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) : List Expr → List Term → Prop
  | nil : DenoteSpine cval env φ d [] []
  | cons {a : Expr} {v : Term} {as : List Expr} {vs : List Term} :
      denote cval env φ d a = some v →
      DenoteSpine cval env φ d as vs →
      DenoteSpine cval env φ d (a :: as) (v :: vs)

/-- Denotation commutes with application spines. -/
theorem denote_mkAppN {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {vs : List Term}
    (h : DenoteSpine cval env φ d as vs) :
    ∀ {f : Expr} {vf : Term}, denote cval env φ d f = some vf →
      denote cval env φ d (Expr.mkAppN f as) = some (Term.mkAppN vf vs) := by
  induction h with
  | nil => intro f vf hf; exact hf
  | cons ha _ ih =>
    intro f vf hf
    refine ih ?_
    rw [denote_app, hf, ha]

/-- Denoted spines append. -/
theorem DenoteSpine.append {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as bs : List Expr} {xs ys : List Term}
    (h1 : DenoteSpine cval env φ d as xs)
    (h2 : DenoteSpine cval env φ d bs ys) :
    DenoteSpine cval env φ d (as ++ bs) (xs ++ ys) := by
  induction h1 with
  | nil => exact h2
  | cons ha _ ih => exact .cons ha ih

/-- A denoted spine's prefix. -/
theorem DenoteSpine.take {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List Term}
    (h : DenoteSpine cval env φ d as xs) :
    ∀ k, DenoteSpine cval env φ d (as.take k) (xs.take k) := by
  induction h with
  | nil => intro k; simp [List.take_nil]; exact .nil
  | @cons a v as vs ha _ ih =>
    intro k
    cases k with
    | zero => exact .nil
    | succ k => exact .cons ha (ih k)

/-- A denoted spine's suffix. -/
theorem DenoteSpine.drop {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List Term}
    (h : DenoteSpine cval env φ d as xs) :
    ∀ k, DenoteSpine cval env φ d (as.drop k) (xs.drop k) := by
  induction h with
  | nil => intro k; simp [List.drop_nil]; exact .nil
  | @cons a v as vs ha h ih =>
    intro k
    cases k with
    | zero => exact .cons ha h
    | succ k => exact ih k

/-- A denoted spine has the same length as its source. -/
theorem DenoteSpine.length {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {xs : List Term}
    (h : DenoteSpine cval env φ d as xs) : xs.length = as.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A mapped spine denotes pointwise — the shape the eta fabrication
has, where the fields are a `List.range` map. -/
theorem DenoteSpine.map {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {α : Type} {as : List α} {f : α → Expr} {g : α → Term}
    (h : ∀ a ∈ as, denote cval env φ d (f a) = some (g a)) :
    DenoteSpine cval env φ d (as.map f) (as.map g) := by
  induction as with
  | nil => exact .nil
  | cons a as ih =>
    exact .cons (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A denoted spine's entries, indexed.  (Relocated from
`ConLeche/TTVerify/DefEqStep.lean`: `Iota.lean` needs it too, and
`Tele.lean` is where `DenoteSpine` is declared.) -/
theorem DenoteSpine.get {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {as : List Expr} {vs : List Term}
    (h : DenoteSpine cval env φ d as vs) :
    ∀ i : Fin as.length,
      denote cval env φ d as[i] = some (vs.getD i default) := by
  induction h with
  | nil => intro i; exact nomatch i.2
  | @cons a v as vs ha _ ih =>
    intro i
    match i with
    | ⟨0, _⟩ => simpa using ha
    | ⟨j + 1, hj⟩ =>
      have := ih ⟨j, by simpa using hj⟩
      simpa using this

/-- Denotation of an application spine, inverted: the head and every
argument denote, and the value is their `Term` application.  The
converse of `denote_mkAppN`, and what the delta step needs to read a
redex apart. -/
theorem denote_mkAppN_inv {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {v : Term},
    denote cval env φ d (Expr.mkAppN f as) = some v →
    ∃ vf vs, denote cval env φ d f = some vf ∧
      DenoteSpine cval env φ d as vs ∧ v = Term.mkAppN vf vs := by
  intro as
  induction as with
  | nil => intro f v h; exact ⟨v, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f v h
    obtain ⟨vfa, vs, hfa, hsp, rfl⟩ := ih h
    rw [denote_app] at hfa
    split at hfa
    · next vf va hf ha =>
      exact ⟨vf, va :: vs, hf, .cons ha hsp, by
        rw [← Option.some.inj hfa]; rfl⟩
    · exact nomatch hfa

end ConLeche.Verify
