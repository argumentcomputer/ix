import Ix.IxVM.Consistency.Statement

/-! # Checking `Annotates` and `StoredAs` by evaluation

`annotatesCheck`, `storedAsCheck` and `storedListCheck` search for a proof of `Annotates`,
`StoredAs` and a pointwise `StoredAs` of two lists, and return the proof they find. They are
sound by construction: what they return is a proof (`annotates_of_check`,
`storedAs_of_check`, `storedList_of_check`). A closed instance is then proved by evaluating
the check, `storedAs_of_check (by decide +kernel)`.

They are not complete: `fuel` bounds the depth of the terms and the number of declared
`let`s expanded.

`pins_storedAs_raw`: each of the kernel's stored basis constants (`BasisKind.declsA`), the
quotient package included, stores the raw basis constant (`BasisKind.decls`) that a stream's
record is compared with (`Ix.Kernel.basisPinHit`, `Ix.Kernel.quotPinHit`).
-/

namespace IxVM.Consistency

open Ix.Kernel (Expr ConstantInfo ConstantVal RecRule)

/-- **A proof that `e'` annotates `e`**, if the search finds one within `fuel`. -/
def annotatesCheck : (fuel : Nat) → (e' e : Expr .anon) → Option (PLift (Annotates e' e))
  | 0, _, _ => none
  | n + 1, e', .letE _ v b _ =>
    (annotatesCheck n e' (b.instantiate1Lift v)).map fun p => ⟨.letE p.down⟩
  | _ + 1, .bvar i, .bvar j =>
    if h : i = j then some ⟨by subst h; exact .bvar⟩ else none
  | n + 1, .fvar i ty', .fvar j ty =>
    if h : i = j then
      (annotatesCheck n ty' ty).map fun p => ⟨by subst h; exact .fvar p.down⟩
    else none
  | _ + 1, .sort l, .sort l' =>
    if h : l = l' then some ⟨by subst h; exact .sort⟩ else none
  | _ + 1, .const k us, .const k' us' =>
    if h : k = k' ∧ us = us' then
      some ⟨by obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact .const⟩
    else none
  | _ + 1, .lit l, .lit l' =>
    if h : l = l' then some ⟨by subst h; exact .lit⟩ else none
  | n + 1, .app f' a', .app f a =>
    match annotatesCheck n f' f, annotatesCheck n a' a with
    | some p, some q => some ⟨.app p.down q.down⟩
    | _, _ => none
  | n + 1, .lam ty' b' _, .lam ty b _ =>
    match annotatesCheck n ty' ty, annotatesCheck n b' b with
    | some p, some q => some ⟨.lam p.down q.down⟩
    | _, _ => none
  | n + 1, .forallE ty' b' _, .forallE ty b _ =>
    match annotatesCheck n ty' ty, annotatesCheck n b' b with
    | some p, some q => some ⟨.forallE p.down q.down⟩
    | _, _ => none
  | n + 1, .proj s i e', .proj s' i' e =>
    if h : s = s' ∧ i = i' then
      (annotatesCheck n e' e).map fun p =>
        ⟨by obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact .proj p.down⟩
    else none
  | _ + 1, _, _ => none

/-- **A successful check is a proof.** -/
theorem annotates_of_check {n : Nat} {e' e : Expr .anon}
    (h : (annotatesCheck n e' e).isSome = true) : Annotates e' e := by
  cases hc : annotatesCheck n e' e with
  | none =>
    rw [hc] at h
    have h' : false = true := h
    cases h'
  | some p => exact p.down

/-- A proof that `cv` stores `cv₀`, if the search finds one. -/
def valStoredCheck (n : Nat) (cv cv₀ : ConstantVal .anon) : Option (PLift (ValStored cv cv₀)) :=
  if h : cv.name = cv₀.name ∧ cv.levelParams = cv₀.levelParams then
    (annotatesCheck n cv.type cv₀.type).map fun p =>
      PLift.up (And.intro h.1 (And.intro h.2 p.down))
  else none

/-- A proof that the rules `rs` store the rules `rs₀`, one for one, if the search finds one. -/
def rulesStoredCheck (n : Nat) :
    (rs rs₀ : List (RecRule .anon)) → Option (PLift (List.Forall₂ RuleStored rs rs₀))
  | [], [] => some ⟨.nil⟩
  | r :: rs, r₀ :: rs₀ =>
    if h : r.ctor = r₀.ctor ∧ r.nfields = r₀.nfields then
      match annotatesCheck n r.rhs r₀.rhs, rulesStoredCheck n rs rs₀ with
      | some p, some q =>
        some ⟨.cons (And.intro h.1 (And.intro h.2 p.down)) q.down⟩
      | _, _ => none
    else none
  | _, _ => none

/-- **A proof that `ci` is the declared constant `ci₀`, stored**, if the search finds one. -/
def storedAsCheck (n : Nat) :
    (ci ci₀ : ConstantInfo .anon) → Option (PLift (StoredAs ci ci₀))
  | .axiomInfo cv, .axiomInfo cv₀ =>
    (valStoredCheck n cv cv₀).map fun p => PLift.up (And.intro p.down trivial)
  | .defnInfo cv v h, .defnInfo cv₀ v₀ h₀ =>
    if hh : h = h₀ then
      match valStoredCheck n cv cv₀, annotatesCheck n v v₀ with
      | some p, some q => some (PLift.up (And.intro p.down (And.intro q.down hh)))
      | _, _ => none
    else none
  | .thmInfo cv v, .thmInfo cv₀ v₀ =>
    match valStoredCheck n cv cv₀, annotatesCheck n v v₀ with
    | some p, some q => some (PLift.up (And.intro p.down q.down))
    | _, _ => none
  | .indInfo cv _, .indInfo cv₀ _ =>
    (valStoredCheck n cv cv₀).map fun p => PLift.up (And.intro p.down trivial)
  | .ctorInfo cv nP nF, .ctorInfo cv₀ nP₀ nF₀ =>
    if hh : nP = nP₀ ∧ nF = nF₀ then
      (valStoredCheck n cv cv₀).map fun p => PLift.up (And.intro p.down hh)
    else none
  | .recInfo cv mI rP rules, .recInfo cv₀ mI₀ rP₀ rules₀ =>
    if hh : mI = mI₀ ∧ rP = rP₀ then
      match valStoredCheck n cv cv₀, rulesStoredCheck n rules rules₀ with
      | some p, some q =>
        some (PLift.up (And.intro p.down (And.intro hh.1 (And.intro hh.2 q.down))))
      | _, _ => none
    else none
  | _, _ => none

/-- **A successful check is a proof.** -/
theorem storedAs_of_check {n : Nat} {ci ci₀ : ConstantInfo .anon}
    (h : (storedAsCheck n ci ci₀).isSome = true) : StoredAs ci ci₀ := by
  cases hc : storedAsCheck n ci ci₀ with
  | none =>
    rw [hc] at h
    have h' : false = true := h
    cases h'
  | some p => exact p.down

/-- A proof that the constants `cs` store the constants `cs₀`, one for one, if the search
finds one. -/
def storedListCheck (n : Nat) :
    (cs cs₀ : List (ConstantInfo .anon)) → Option (PLift (List.Forall₂ StoredAs cs cs₀))
  | [], [] => some ⟨.nil⟩
  | c :: cs, c₀ :: cs₀ =>
    match storedAsCheck n c c₀, storedListCheck n cs cs₀ with
    | some p, some q => some ⟨.cons p.down q.down⟩
    | _, _ => none
  | _, _ => none

/-- **A successful check is a proof.** -/
theorem storedList_of_check {n : Nat} {cs cs₀ : List (ConstantInfo .anon)}
    (h : (storedListCheck n cs cs₀).isSome = true) : List.Forall₂ StoredAs cs cs₀ := by
  cases hc : storedListCheck n cs cs₀ with
  | none =>
    rw [hc] at h
    have h' : false = true := h
    cases h'
  | some p => exact p.down

/-- **Each stored basis constant stores the raw basis constant**: the kernel's annotated
pins (`declsA`, what the environment holds) against the raw pins (`decls`, what a stream's
block is compared with), block by block, constant by constant, recursors and their rules
included. -/
theorem pins_storedAs_raw (kind : Ix.Kernel.BasisKind) :
    List.Forall₂ StoredAs (kind.declsA : List (ConstantInfo .anon))
      (kind.decls : List (ConstantInfo .anon)) := by
  cases kind <;> exact storedList_of_check (n := 256) (by decide +kernel)

end IxVM.Consistency
