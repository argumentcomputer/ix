import IxCC.Src.Table.Shape
import IxCC.Src.Resource.Check

/-! # Unfolding-table checks

Each check decides one untrusted proposal on the resolved declarations.
Equality is `Term.eqv`: syntactic, ignoring
contracts, modes and annotations. A check returns the entry it justifies or
a reason; `Table.Build` drops refused proposals with a `hint` diagnostic. -/

namespace IxCC.Src.Table

open IxCC.Ixon

structure Config where
  /-- The primitive operations with native lowering; others resolve
  through their `eqn` entry or kernel body. -/
  prims : List PrimOp := PrimOp.all
  /-- Node cap for `inline` entries. -/
  inlineCap : Nat := 256
  deriving Inhabited

/-- Maximum expanded tree nodes inspected in table check types and small bodies
(guards against exponential `share` DAG blowup). -/
def maxTermNodes : Nat := 100000

/-- Maximum expanded tree nodes for definition/proof bodies in `checkEqn` and
`checkAxiomWalk` (`sum-loop`'s unshared tree has 1.68M nodes). -/
def maxBodyNodes : Nat := 5000000

/-- A standard Lean axiom (`propext`, `Quot.sound`, `Classical.choice`): a safe
axiom at one of the program's standard-axiom pins (`Pins.stdAxioms`, 256-bit
big-endian addresses, `Pinned.addrNat`). -/
def isStandardAxiom (p : Program) (c : CId) : Bool :=
  match p.decl? c with
  | some (.axio true _ _) => p.known.pins.stdAxioms.contains (Pinned.addrNat (p.addr c))
  | _ => false

def declTerms : Decl → List Term
  | .defn _ _ _ t v => [t, v]
  | .induct _ _ _ _ t _ => [t]
  | .ctor _ _ _ _ _ _ t => [t]
  | .recr _ _ _ _ _ _ _ _ rules t => t :: rules.map (·.rhs)
  | .quot _ _ t => [t]
  | .axio _ _ t => [t]

def declExtraConsts : Decl → List CId
  | .induct _ _ _ _ _ ctors => ctors
  | .ctor _ _ ind _ _ _ _ => [ind]
  | .recr _ _ _ _ _ _ _ ind rules _ => ind :: rules.map (·.ctor)
  | _ => []

def collectTermsConsts : List Term → Nat → List CId → Option (Nat × List CId)
  | [], b, acc => some (b, acc)
  | t :: ts, b, acc => do
    let (b1, acc1) ← t.constsBudget b acc
    collectTermsConsts ts b1 acc1

def declAxiomOk (p : Program) (c : CId) (d : Decl) : Bool :=
  decide (c < p.size) && match d with
    | .axio .. => isStandardAxiom p c
    | _ => true

def checkAxiomWalk (p : Program) : Nat → List CId → List CId → Bool
  | 0, _ :: _, _ => false
  | _, [], _ => true
  | fuel + 1, c :: todo, seen =>
    if seen.contains c then
      checkAxiomWalk p fuel todo seen
    else
      match p.decl? c with
      | none => false
      | some d =>
        if !declAxiomOk p c d then false
        else
          match collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
          | none => false
          | some (_, refs) =>
            let newRefs := refs.filter (fun r => !seen.contains r && !todo.contains r)
            checkAxiomWalk p fuel (newRefs ++ todo) (c :: seen)

/-- Verify that the transitive constant closure of `thm` in `p` contains no
`Decl.axio` outside the standard Lean axioms (`propext`, `Quot.sound`,
`Classical.choice`). The closure is the one `AxiomReach` defines;
`checkAxiomClosure_sound` proves the property for it. -/
def checkAxiomClosure (p : Program) (thm : CId) : Except String Unit :=
  let allStandard := decide (thm < p.size) && (List.range p.size).all fun c =>
    match p.decl? c with
    | some (.axio ..) => isStandardAxiom p c
    | _ => true
  if allStandard || checkAxiomWalk p (p.size * 2 + 16) [thm] [] then
    .ok ()
  else
    throw "theorem depends on a non-standard axiom or exceeds closure budget"

/-- A constant in `p` is within bounds and, if an axiom, is a standard Lean axiom. -/
def AxiomDeclOk (p : Program) (c : CId) : Prop :=
  c < p.size ∧ (match p.decl? c with | some (.axio ..) => isStandardAxiom p c = true | _ => True)

theorem checkAxiomWalk_todo_sound {p : Program} :
    ∀ (fuel : Nat) (todo seen : List CId),
      checkAxiomWalk p fuel todo seen = true →
      (∀ s ∈ seen, AxiomDeclOk p s) →
      ∀ c ∈ todo, AxiomDeclOk p c
  | 0, [], _, _, _, _, hmem => by cases hmem
  | 0, _ :: _, _, h, _, _, _ => by simp [checkAxiomWalk] at h
  | fuel + 1, [], _, _, _, _, hmem => by cases hmem
  | fuel + 1, x :: rest, seen, h, hseen, c, hmem => by
    simp only [checkAxiomWalk] at h
    by_cases hxs : seen.contains x = true
    · simp only [hxs, ↓reduceIte] at h
      rcases List.mem_cons.1 hmem with rfl | hrest
      · exact hseen c (List.contains_iff_mem.1 hxs)
      · exact checkAxiomWalk_todo_sound fuel rest seen h hseen c hrest
    · simp only [hxs, Bool.false_eq_true, ↓reduceIte] at h
      cases hd : p.decl? x with
      | none => rw [hd] at h; cases h
      | some d =>
        rw [hd] at h
        dsimp only at h
        cases hok : declAxiomOk p x d with
        | false =>
          rw [hok] at h
          cases h
        | true =>
          rw [hok] at h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hcol : collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
          | none => rw [hcol] at h; cases h
          | some pair =>
            rcases pair with ⟨_, refs⟩
            rw [hcol] at h
            dsimp only at h
            unfold declAxiomOk at hok
            obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
            have hxok : AxiomDeclOk p x := by
              refine ⟨of_decide_eq_true h1, ?_⟩
              rw [hd]
              cases d <;> simp_all
            have hseen' : ∀ s ∈ x :: seen, AxiomDeclOk p s := by
              intro s hs
              rcases List.mem_cons.1 hs with rfl | hs
              · exact hxok
              · exact hseen s hs
            rcases List.mem_cons.1 hmem with rfl | hrest
            · exact hxok
            · exact checkAxiomWalk_todo_sound fuel _ (x :: seen) h hseen' c
                (List.mem_append_right _ hrest)

theorem checkAxiomWalk_head_sound {p : Program} {fuel : Nat} {c : CId} {rest : List CId}
    (h : checkAxiomWalk p fuel (c :: rest) [] = true) :
    c < p.size ∧ (match p.decl? c with | some (.axio ..) => isStandardAxiom p c = true | _ => True) :=
  checkAxiomWalk_todo_sound fuel (c :: rest) [] h (fun _ hs => by cases hs) c List.mem_cons_self

/-! ### The closure `checkAxiomWalk` follows -/

/-- Every constant `t` mentions (`Term.mentions`: a `.const` head or a `.proj`
structure) is in the list `constsBudget` returns, which extends `acc`. -/
theorem _root_.IxCC.Src.Term.constsBudget_sound :
    ∀ (t : Term) (b : Nat) (acc : List CId) (b' : Nat) (acc' : List CId),
      t.constsBudget b acc = some (b', acc') →
      (∀ x ∈ acc, x ∈ acc') ∧ ∀ c, t.mentions c = true → c ∈ acc'
  | t, 0, _, _, _, h => by cases t <;> simp [Term.constsBudget] at h
  | .const d us, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨fun x hx => ?_, fun c hc => ?_⟩
    · split
      · exact hx
      · exact List.mem_cons_of_mem _ hx
    · have hcd : c = d := by simpa [Term.mentions] using hc
      subst hcd
      split
      · next hin => exact List.contains_iff_mem.1 hin
      · exact List.mem_cons_self
  | .app f a m r, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.bind_eq_bind] at h
    cases h1 : f.constsBudget b acc with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨b1, acc1⟩ := p1
      simp only [h1, Option.bind_some] at h
      obtain ⟨hf1, hf2⟩ := Term.constsBudget_sound f b acc b1 acc1 h1
      obtain ⟨ha1, ha2⟩ := Term.constsBudget_sound a b1 acc1 b' acc' h
      refine ⟨fun x hx => ha1 x (hf1 x hx), fun c hc => ?_⟩
      simp only [Term.mentions, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · exact ha1 c (hf2 c hc)
      · exact ha2 c hc
  | .lam bd d t, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.bind_eq_bind] at h
    cases h1 : d.constsBudget b acc with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨b1, acc1⟩ := p1
      simp only [h1, Option.bind_some] at h
      obtain ⟨hd1, hd2⟩ := Term.constsBudget_sound d b acc b1 acc1 h1
      obtain ⟨ht1, ht2⟩ := Term.constsBudget_sound t b1 acc1 b' acc' h
      refine ⟨fun x hx => ht1 x (hd1 x hx), fun c hc => ?_⟩
      simp only [Term.mentions, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · exact ht1 c (hd2 c hc)
      · exact ht2 c hc
  | .pi bd res d t, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.bind_eq_bind] at h
    cases h1 : d.constsBudget b acc with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨b1, acc1⟩ := p1
      simp only [h1, Option.bind_some] at h
      obtain ⟨hd1, hd2⟩ := Term.constsBudget_sound d b acc b1 acc1 h1
      obtain ⟨ht1, ht2⟩ := Term.constsBudget_sound t b1 acc1 b' acc' h
      refine ⟨fun x hx => ht1 x (hd1 x hx), fun c hc => ?_⟩
      simp only [Term.mentions, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · exact ht1 c (hd2 c hc)
      · exact ht2 c hc
  | .letE lc r ty v body, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.bind_eq_bind] at h
    cases h1 : ty.constsBudget b acc with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨b1, acc1⟩ := p1
      simp only [h1, Option.bind_some] at h
      cases h2 : v.constsBudget b1 acc1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨b2, acc2⟩ := p2
        simp only [h2, Option.bind_some] at h
        obtain ⟨hy1, hy2⟩ := Term.constsBudget_sound ty b acc b1 acc1 h1
        obtain ⟨hv1, hv2⟩ := Term.constsBudget_sound v b1 acc1 b2 acc2 h2
        obtain ⟨hb1, hb2⟩ := Term.constsBudget_sound body b2 acc2 b' acc' h
        refine ⟨fun x hx => hb1 x (hv1 x (hy1 x hx)), fun c hc => ?_⟩
        simp only [Term.mentions, Bool.or_eq_true] at hc
        rcases hc with (hc | hc) | hc
        · exact hb1 c (hv1 c (hy2 c hc))
        · exact hb1 c (hv2 c hc)
        · exact hb2 c hc
  | .proj s i e, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget] at h
    obtain ⟨he1, he2⟩ := Term.constsBudget_sound e b _ b' acc' h
    have hs : s ∈ acc' := by
      apply he1
      split
      · next hin => exact List.contains_iff_mem.1 hin
      · exact List.mem_cons_self
    refine ⟨fun x hx => he1 x ?_, fun c hc => ?_⟩
    · split
      · exact hx
      · exact List.mem_cons_of_mem _ hx
    · simp only [Term.mentions, Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with rfl | hc
      · exact hs
      · exact he2 c hc
  | .var i, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun x hx => hx, fun c hc => by simp [Term.mentions] at hc⟩
  | .sort u, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun x hx => hx, fun c hc => by simp [Term.mentions] at hc⟩
  | .natLit n, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun x hx => hx, fun c hc => by simp [Term.mentions] at hc⟩
  | .strLit s, b + 1, acc, b', acc', h => by
    simp only [Term.constsBudget, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun x hx => hx, fun c hc => by simp [Term.mentions] at hc⟩

/-- `collectTermsConsts` lists every constant its terms mention, extending `acc`. -/
theorem collectTermsConsts_sound :
    ∀ (ts : List Term) (b : Nat) (acc : List CId) (b' : Nat) (acc' : List CId),
      collectTermsConsts ts b acc = some (b', acc') →
      (∀ x ∈ acc, x ∈ acc') ∧ ∀ t ∈ ts, ∀ c, t.mentions c = true → c ∈ acc'
  | [], b, acc, b', acc', h => by
    simp only [collectTermsConsts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun x hx => hx, fun t ht => by cases ht⟩
  | t :: ts, b, acc, b', acc', h => by
    simp only [collectTermsConsts, Option.bind_eq_bind] at h
    cases h1 : t.constsBudget b acc with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨b1, acc1⟩ := p1
      simp only [h1, Option.bind_some] at h
      obtain ⟨ht1, ht2⟩ := Term.constsBudget_sound t b acc b1 acc1 h1
      obtain ⟨hs1, hs2⟩ := collectTermsConsts_sound ts b1 acc1 b' acc' h
      refine ⟨fun x hx => hs1 x (ht1 x hx), fun u hu c hc => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hs1 c (ht2 c hc)
      · exact hs2 u hu c hc

/-- One edge of the dependency graph `checkAxiomWalk` explores: `c` is a direct
dependency of the declaration `d` when

- `c` occurs in one of `declTerms d` (a definition's or theorem's type and
  value; the type of an inductive, constructor, quotient or axiom; a
  recursor's type and every rule's right-hand side) as a `.const c _` head or
  as the structure of a `.proj c _ _` (`Term.mentions`); or
- `c` is in `declExtraConsts d` (an inductive's constructors, a constructor's
  inductive, a recursor's major inductive and its rules' constructors).

These are exactly the references `collectTermsConsts (declTerms d) _
(declExtraConsts d)` collects. -/
def AxiomEdge (d : Decl) (c : CId) : Prop :=
  (∃ t ∈ declTerms d, t.mentions c = true) ∨ c ∈ declExtraConsts d

/-- `AxiomReach p root c`: `c` is reachable from `root` in `p` along
`AxiomEdge`, leaving only constants `p` declares (`p.decl? a = some d`).

This is the reference graph of the ingested `Src.Program`, as ingress keeps
each Ixon constant (shares expanded). It does not follow the unfolding table
(`p.table`), the pinned identities (`p.known`) or the types of literals, and it
says nothing about how the kernel checked these declarations. -/
inductive AxiomReach (p : Program) (root : CId) : CId → Prop
  | refl : AxiomReach p root root
  | step {a c : CId} {d : Decl} :
      AxiomReach p root a → p.decl? a = some d → AxiomEdge d c → AxiomReach p root c

/-- The invariant of `checkAxiomWalk p fuel todo seen`: every constant in
`seen` is `AxiomDeclOk`, and each of its `AxiomEdge` dependencies is in `seen`
or still in `todo`. -/
def AxiomWalkClosed (p : Program) (todo seen : List CId) : Prop :=
  ∀ s ∈ seen, AxiomDeclOk p s ∧
    ∀ d c, p.decl? s = some d → AxiomEdge d c → c ∈ seen ∨ c ∈ todo

/-- An accepting walk ends with a visited set that contains its `todo` and
`seen`, is closed under `AxiomEdge`, and holds only `AxiomDeclOk` constants. -/
theorem checkAxiomWalk_closed {p : Program} :
    ∀ (fuel : Nat) (todo seen : List CId),
      checkAxiomWalk p fuel todo seen = true → AxiomWalkClosed p todo seen →
      ∃ S : List CId, (∀ c ∈ todo, c ∈ S) ∧ (∀ c ∈ seen, c ∈ S) ∧ AxiomWalkClosed p [] S
  | 0, [], seen, _, hinv => ⟨seen, fun _ h => (by simp at h), fun _ h => h, hinv⟩
  | 0, _ :: _, _, h, _ => by simp [checkAxiomWalk] at h
  | fuel + 1, [], seen, _, hinv => ⟨seen, fun _ h => (by simp at h), fun _ h => h, hinv⟩
  | fuel + 1, x :: rest, seen, h, hinv => by
    simp only [checkAxiomWalk] at h
    by_cases hxs : seen.contains x = true
    · simp only [hxs, ↓reduceIte] at h
      have hxs' : x ∈ seen := List.contains_iff_mem.1 hxs
      have hinv' : AxiomWalkClosed p rest seen := by
        intro s hs
        refine ⟨(hinv s hs).1, fun d c hd hr => ?_⟩
        rcases (hinv s hs).2 d c hd hr with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact Or.inl hxs'
          · exact Or.inr h1
      obtain ⟨S, hS1, hS2, hS3⟩ := checkAxiomWalk_closed fuel rest seen h hinv'
      refine ⟨S, fun c hc => ?_, hS2, hS3⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hS2 _ hxs'
      · exact hS1 c hc
    · simp only [hxs, Bool.false_eq_true, ↓reduceIte] at h
      cases hd : p.decl? x with
      | none => rw [hd] at h; cases h
      | some d =>
        rw [hd] at h
        dsimp only at h
        cases hok : declAxiomOk p x d with
        | false =>
          rw [hok] at h
          cases h
        | true =>
          rw [hok] at h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hcol : collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
          | none => rw [hcol] at h; cases h
          | some pair =>
            rcases pair with ⟨bud, refs⟩
            rw [hcol] at h
            dsimp only at h
            obtain ⟨hcol1, hcol2⟩ :=
              collectTermsConsts_sound _ _ _ bud refs hcol
            unfold declAxiomOk at hok
            obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
            have hxok : AxiomDeclOk p x := by
              refine ⟨of_decide_eq_true h1, ?_⟩
              rw [hd]
              cases d <;> simp_all
            let newRefs := refs.filter (fun r => !seen.contains r && !rest.contains r)
            have hinv' : AxiomWalkClosed p (newRefs ++ rest) (x :: seen) := by
              intro s hs
              rcases List.mem_cons.1 hs with rfl | hs
              · refine ⟨hxok, fun d' c hd' hr => ?_⟩
                rw [hd] at hd'
                cases hd'
                have hc : c ∈ refs := by
                  rcases hr with ⟨t, ht, hm⟩ | hm
                  · exact hcol2 t ht c hm
                  · exact hcol1 c hm
                by_cases hcs : c ∈ seen
                · exact Or.inl (List.mem_cons_of_mem _ hcs)
                · by_cases hcr : c ∈ rest
                  · exact Or.inr (List.mem_append_right _ hcr)
                  · refine Or.inr (List.mem_append_left _ ?_)
                    refine List.mem_filter.2 ⟨hc, ?_⟩
                    simp [hcs, hcr]
              · refine ⟨(hinv s hs).1, fun d' c hd' hr => ?_⟩
                rcases (hinv s hs).2 d' c hd' hr with h1 | h1
                · exact Or.inl (List.mem_cons_of_mem _ h1)
                · rcases List.mem_cons.1 h1 with rfl | h1
                  · exact Or.inl List.mem_cons_self
                  · exact Or.inr (List.mem_append_right _ h1)
            obtain ⟨S, hS1, hS2, hS3⟩ := checkAxiomWalk_closed fuel _ (x :: seen) h hinv'
            refine ⟨S, fun c hc => ?_, fun c hc => hS2 c (List.mem_cons_of_mem _ hc), hS3⟩
            rcases List.mem_cons.1 hc with rfl | hc
            · exact hS2 _ List.mem_cons_self
            · exact hS1 c (List.mem_append_right _ hc)

theorem axiomReach_mem_of_closed {p : Program} {root : CId} {S : List CId}
    (hS : AxiomWalkClosed p [] S) (hroot : root ∈ S) :
    ∀ {c : CId}, AxiomReach p root c → c ∈ S
  | _, .refl => hroot
  | _, .step hr hd href => by
    have ha := axiomReach_mem_of_closed hS hroot hr
    rcases (hS _ ha).2 _ _ hd href with h | h
    · exact h
    · cases h

/-- **Soundness of `checkAxiomClosure`.** If `checkAxiomClosure p thm` accepts,
then `thm` is a constant of `p`, and no constant of `p` reachable from `thm`
(`AxiomReach`: through the types, values and rule right-hand sides of the
declarations on the way, and an inductive's constructors, a constructor's
inductive and a recursor's inductive and rule constructors) is an axiom other
than `propext`, `Quot.sound` and `Classical.choice` (`AxiomDeclOk`).

A `CId` at or above `p.size` names no constant of `p` (`Program`: `consts`
holds exactly the keys below `size`, which ingress guarantees and the type does
not), so the conclusion is stated for the reachable `c < p.size`. Both
branches of the check are covered: the shortcut when every axiom of `p` is
standard, and the walk, which fails closed on an unknown constant, a body over
`maxBodyNodes` and exhausted fuel. -/
theorem checkAxiomClosure_sound {p : Program} {thm : CId}
    (h : checkAxiomClosure p thm = .ok ()) :
    thm < p.size ∧ ∀ c, AxiomReach p thm c → c < p.size → AxiomDeclOk p c := by
  unfold checkAxiomClosure at h
  dsimp only at h
  split at h
  · next hcond =>
    rcases Bool.or_eq_true_iff.1 hcond with hall | hwalk
    · obtain ⟨hlt, hrng⟩ := Bool.and_eq_true_iff.1 hall
      refine ⟨of_decide_eq_true hlt, fun c _ hc => ⟨hc, ?_⟩⟩
      have hstd := List.all_eq_true.1 hrng c (List.mem_range.2 hc)
      cases hd : p.decl? c with
      | none => trivial
      | some d =>
        rw [hd] at hstd
        cases d <;> simp_all
    · have hinit : AxiomWalkClosed p [thm] [] := fun _ hs => by cases hs
      obtain ⟨S, hS1, _, hS3⟩ := checkAxiomWalk_closed _ [thm] [] hwalk hinit
      have hthm := hS1 thm List.mem_cons_self
      refine ⟨(hS3 thm hthm).1.1, fun c hr _ => ?_⟩
      exact (hS3 c (axiomReach_mem_of_closed hS3 hthm hr)).1
  · cases h

/-- `checkAxiomClosure` on every root (not called on the recheck path). -/
def checkAxiomClosureRoots (p : Program) : Bool :=
  p.roots.all fun (_, c) => (checkAxiomClosure p c).isOk

theorem checkAxiomClosure_roots {p : Program} (h : checkAxiomClosureRoots p = true)
    {a : Ixon.Address} {c : CId} (hroot : (a, c) ∈ p.roots) :
    c < p.size ∧ ∀ c', AxiomReach p c c' → c' < p.size → AxiomDeclOk p c' := by
  have hc := List.all_eq_true.1 h (a, c) hroot
  dsimp only [Except.isOk, Except.toBool] at hc
  cases hcl : checkAxiomClosure p c with
  | error _ => rw [hcl] at hc; cases hc
  | ok u =>
    cases u
    exact checkAxiomClosure_sound hcl

/-! ## `eqn` -/

/-- Peel exactly the equation header; remaining lambdas are internal syntax. -/
def peelLams : Nat → Term → Option (List (Binder × Term) × Term)
  | 0, t => some ([], t)
  | k + 1, .lam b d t => do
    let (bs, body) ← peelLams k t
    return ((b, d) :: bs, body)
  | _ + 1, _ => none

/-- The current lowering observes the final result contract. Intermediate
curried-result promises need a separate transport design. -/
def supportedHeaderResults : Term → Bool
  | .pi _ r _ body =>
    match body with
    | .pi .. => r == .shared && supportedHeaderResults body
    | _ => body.leanFragment
  | body => body.leanFragment

/-- Transport only matching written header contracts. Refuse every body or
domain annotation whose location cannot be preserved in the selected RHS. -/
def equationBody (p : Program) (f thm : CId) (tf vf rhs : Term)
    (fBinders binders : List (Binder × Term)) : Except String Term := do
  if vf.leanFragment && tf.leanFragment then
    return binders.foldr (fun (b, d) acc => .lam { b with contract := {} } d acc) rhs
  Resource.requirePair p f thm
  unless fBinders.length == tf.pis.1.length && supportedHeaderResults tf do
    throw "eqn-drops-contracts: partial or curried-result header is unsupported"
  let some (bodyBinders, rest) := peelLams binders.length vf
    | throw "eqn-drops-contracts: subject body has too few header lambdas"
  unless rest.leanFragment && rhs.leanFragment do
    throw "eqn-drops-contracts: body-internal contracts cannot be transported"
  unless (fBinders.zip (bodyBinders.zip binders)).all (fun ((b, d), ((vb, vd), (tb, td))) =>
      b.contract == vb.contract && b.contract == tb.contract &&
      d.leanFragment && vd.leanFragment && td.leanFragment &&
      domainEqv p d vd && domainEqv p d td) do
    throw "eqn-drops-contracts: header contracts or domains disagree"
  return (fBinders.zip binders).foldr (fun ((b, d), (tb, _)) acc =>
    .lam { tb with contract := b.contract } d acc) rhs

/-- Check `eqn f thm` and build the entry body `λ xs. rhs` (checks 1–5). -/
def checkEqn (p : Program) (f thm : CId) : Except String Resolve := do
  let some (n, tf, vf) := safeDefn? p f
    | throw "eqn: the subject is not a safe definition"
  let some (.defn .thm .safe n' tθ _vθ) := p.decl? thm
    | throw "eqn: the equation is not a safe theorem"
  unless tf.nodesLe maxTermNodes && vf.nodesLe maxBodyNodes &&
      tθ.nodesLe maxTermNodes do
    throw "eqn: term exceeds node budget"
  checkAxiomClosure p thm
  unless n == n' do throw "eqn: universe parameter counts differ"
  let (binders, body) := tθ.pis
  let some (b, lhs, rhs) := eqApp? p body
    | throw "eqn: the theorem is not a Π-telescope over Eq"
  let k := binders.length
  let expectedLhs := Term.mkApps (.const f (paramUnivs n))
    ((boundVars k).map (·, Mode.strict, Rel.rel))
  unless lhs.eqv expectedLhs do
    throw "eqn: the left-hand side is not f applied to the bound variables in order"
  let some (fBinders, fBody) := peelPis k tf
    | throw "eqn: the subject's type has fewer binders than the equation"
  unless (fBinders.zip binders).all (fun ((_, a), (_, a')) => domainEqv p a a') do
    throw "eqn: binder domains differ from the subject's type"
  unless domainEqv p fBody b do throw "eqn: the equation's type differs from the subject's result"
  let body ← equationBody p f thm tf vf rhs fBinders binders
  return .eqn thm body

/-! ## `csimp` -/

/-- Check `csimp f g thm`: `thm : @f = @g` exactly. The target's own
admissibility and acyclicity are checked by `Table.Build`. -/
def checkCsimp (p : Program) (f g thm : CId) : Except String Resolve := do
  unless p.resource.isNone do throw "csimp: resource-bound replacement is unsupported"
  let some (n, tf, _vf) := safeDefn? p f
    | throw "csimp: the subject is not a safe definition"
  let some (.defn .thm .safe n' tθ _vθ) := p.decl? thm
    | throw "csimp: the theorem is not a safe theorem"
  unless tf.nodesLe maxTermNodes && tθ.nodesLe maxTermNodes do
    throw "csimp: term exceeds node budget"
  checkAxiomClosure p thm
  unless n == n' do throw "csimp: universe parameter counts differ"
  unless g != f do throw "csimp: the target is the subject"
  let some (ty, lhs, rhs) := eqApp? p tθ
    | throw "csimp: the theorem is not an equation between constants"
  unless ty.eqv tf do throw "csimp: the equation's type is not the subject's type"
  unless lhs.eqv (.const f (paramUnivs n)) do throw "csimp: the left side is not @f"
  match rhs with
  | .const g' vs =>
    if g' == g then return .csimp g vs thm
    else throw "csimp: the right side is not @g"
  | _ => throw "csimp: the right side is not a constant"

/-- Follow `csimp` redirects from `cur` for at most `fuel` steps; `false` if
the chain revisits `start` or runs out (structural on the fuel). -/
def csimpChainF (resolve : NatMap Resolve) (start : CId) : Nat → CId → Bool
  | 0, _ => false
  | fuel + 1, cur =>
    match resolve.get? cur with
    | some (.csimp g _ _) => if g == start then false else csimpChainF resolve start fuel g
    | _ => true

/-- Follow `csimp` redirects; `false` if a chain revisits a constant (`n`:
the program size, a bound on any acyclic chain). -/
def csimpAcyclic (resolve : NatMap Resolve) (n : Nat) (start : CId) : Bool :=
  csimpChainF resolve start (n + 1) start

/-! ## `case` -/

/-- IH count of a recursor rule: its `rhs` is `λ ps motives minors fields.
app* #minor (fields ++ ihs)`. -/
def ruleIhs (np nmot nmin j : Nat) (rule : Rule) : Option Nat :=
  let (binders, body) := rule.rhs.lams
  let total := np + nmot + nmin + rule.fields
  if binders.length != total then none else
  let (head, args) := body.spine
  -- The minor for rule `j` is binder `np + nmot + j`.
  match head with
  | .var i =>
    if i == total - 1 - (np + nmot + j) && args.length ≥ rule.fields then
      some (args.length - rule.fields)
    else none
  | _ => none

/-- The first position in `is` whose check fails. -/
def firstFailing (is : List Nat) (ok : Nat → Bool) : Option Nat := is.find? (!ok ·)

/-- One minor wrapper of `case` (rule `j`): `λ fields ihs. #minor fields`. -/
def checkCaseMinor (np ni m total : Nat) (argAt : Nat → Term) (j : Nat) (rule : Rule) :
    Except String Unit := do
  let some ihs := ruleIhs np 1 m j rule | throw s!"case: rule {j} has no minor-application shape"
  let f := rule.fields
  let (wBinders, wBody) := (argAt (np + 1 + j)).lams
  unless wBinders.length == f + ihs do throw s!"case: minor wrapper {j} has the wrong arity"
  let minorIdx := (total - 1 - (np + 1 + ni + 1 + j)) + f + ihs
  let expected := Term.mkApps (.var minorIdx)
    ((List.range f).map fun i => (Term.var (f + ihs - 1 - i), Mode.strict, Rel.rel))
  unless wBody.eqv expected do throw s!"case: minor wrapper {j} is not the minor on its fields"

/-- The minor wrappers of rules `j, j+1, …` in order (structural on the rules). -/
def checkCaseMinors (np ni m total : Nat) (argAt : Nat → Term) :
    Nat → List Rule → Except String Unit
  | _, [] => pure ()
  | j, rule :: rules => do
    checkCaseMinor np ni m total argAt j rule
    checkCaseMinors np ni m total argAt (j + 1) rules

/-- Check `case T` with key `T.casesOn`. Returns the recursor. -/
def checkCase (p : Program) (key : CId) : Except String Resolve := do
  let some (n, ty, value) := safeDefn? p key
    | throw "case: the key is not a safe definition"
  unless ty.nodesLe maxTermNodes && value.nodesLe maxTermNodes do
    throw "case: term exceeds node budget"
  let (binders, body) := value.lams
  let (head, args) := body.spine
  let .const r us := head | throw "case: the body is not a recursor spine"
  let some (.recr _ _ rl np nmot nmin ni _ rules rty) := p.decl? r
    | throw "case: the head is not a recursor"
  unless rty.nodesLe maxTermNodes && rules.all (fun rule => rule.rhs.nodesLe maxTermNodes) do
    throw "case: recursor exceeds node budget"
  unless nmot == 1 do throw "case: mutual casesOn stays on δ"
  unless rl == n && us == paramUnivs n do throw "case: recursor levels are not the key's"
  unless rules.length == nmin do throw "case: rules and minors differ"
  let m := nmin
  let total := np + 1 + ni + 1 + m
  unless binders.length == total do throw "case: wrong binder count"
  unless args.length == total do throw "case: wrong argument count"
  let bvar := fun (q : Nat) => Term.var (total - 1 - q)
  let argAt := fun (i : Nat) => (args[i]?.map (·.1)).getD (.natLit 0)
  if let some i := firstFailing (List.range np) fun i => (argAt i).eqv (bvar i) then
    throw s!"case: parameter {i} out of place"
  unless (argAt np).eqv (bvar np) do throw "case: motive out of place"
  if let some i := firstFailing (List.range ni) fun i =>
      (argAt (np + 1 + m + i)).eqv (bvar (np + 1 + i)) then
    throw s!"case: index {i} out of place"
  unless (argAt (np + 1 + m + ni)).eqv (bvar (np + 1 + ni)) do
    throw "case: major out of place"
  checkCaseMinors np ni m total argAt 0 rules
  return .case r

/-! ## Sparse `casesOn`

Lean elaborates a `match` that names some constructors and ends in a catch-all
through a definition it generates per program, `T…._sparseCasesOn_N`
(`Lean.Meta.mkSparseCasesOn`): one argument per named constructor (an *arm*),
then the catch-all's continuation. Lean's code generator compiles it as a
`cases`, so an arm runs only when its constructor is chosen; read as an
ordinary definition, its arms are arguments SrcEval evaluates first. A `lazy`
row passes them by name. The closure is anonymous, so the definition is
recognised by its shape, as a `case` entry is. -/

/-- The occurrences of the variable `i` in the value positions of `t`: all but
a binder's domain, a Π and a `let`'s type, which are types and never evaluated
(structural). -/
def valueUses : Term → Nat → Nat
  | .var j, i => if j == i then 1 else 0
  | .app f a _ _, i => valueUses f i + valueUses a i
  | .lam _ _ t, i => valueUses t (i + 1)
  | .letE _ _ _ v b, i => valueUses v i + valueUses b (i + 1)
  | .proj _ _ e, i => valueUses e i
  | _, _ => 0

/-- Every variable of `t` is bound inside it, `d` binders in (structural). -/
def closedUnder : Term → Nat → Bool
  | .var j, d => j < d
  | .app f a _ _, d => closedUnder f d && closedUnder a d
  | .lam _ dom t, d | .pi _ _ dom t, d => closedUnder dom d && closedUnder t (d + 1)
  | .letE _ _ ty v b, d => closedUnder ty d && closedUnder v d && closedUnder b (d + 1)
  | .proj _ _ e, d => closedUnder e d
  | _, _ => true

/-- One minor of a sparse casesOn, for a constructor of `f` fields and `ihs`
IHs, under the definition's `B` binders, the arms being those from `arms` on:
`some (some q)` for `λ fields ihs else. arm fields` (the arm binder `q` applied
to the fields in order), `some none` for `λ fields ihs else. else h` with `h`
closed (the catch-all applied to Lean's proof that the constructor is not a
named one), `none` for anything else. -/
def sparseMinor (B arms f ihs : Nat) (minor : Term) : Option (Option Nat) :=
  let (ws, body) := minor.lams
  let m := f + ihs + 1
  if ws.length != m then none else
  match body.spine with
  | (.var 0, [(h, _, _)]) => if closedUnder h 0 then some none else none
  | (.var v, args) =>
    if m ≤ v && v - m < B - arms && args.length == f &&
        args.zipIdx.all (fun ((a, _, _), i) => a.eqv (.var (f + ihs - i))) then
      some (some (B - 1 - (v - m)))
    else none
  | _ => none

/-- The minors of rules `j, j+1, …` (structural on the rules): the arm binder
each named constructor's minor applies, in rule order. -/
def sparseMinors (np nmin B arms : Nat) (argAt : Nat → Term) :
    Nat → List Rule → Except String (List Nat)
  | _, [] => pure []
  | j, rule :: rules => do
    let some ihs := ruleIhs np 1 nmin j rule
      | throw s!"sparse: rule {j} has no minor-application shape"
    let here ← match sparseMinor B arms rule.fields ihs (argAt (np + 1 + j)) with
      | some q => pure q
      | none => throw s!"sparse: minor {j} is neither an arm on its fields nor the catch-all on a proof"
    let rest ← sparseMinors np nmin B arms argAt (j + 1) rules
    pure (match here with | some q => q :: rest | none => rest)

/-- Check that `f` is a sparse casesOn as `Lean.Meta.mkSparseCasesOn` writes
it, and return its binder count, the arity of its `lazy` row:

    λ params motive indices major arm₁ … armₖ.            (k ≥ 1)
      T.rec params motive' minor₀ … minorₙ₋₁ indices major

`T.rec` a single-motive recursor at the definition's levels; the parameters,
indices and major the definition's own binders, in place; every minor of one of
`sparseMinor`'s two forms, the named constructors' minors applying each arm
binder once. And every binder but the motive occurs at most once in a value
position of the body (`valueUses`; in this shape, exactly once), so a by-name
argument is evaluated at most once, and an arm whose constructor is not chosen
not at all. Recomputed from the definition wherever a `lazy` row is checked. -/
def checkSparseCases (p : Program) (f : CId) : Except String Nat := do
  let some (n, ty, value) := safeDefn? p f | throw "sparse: not a safe definition"
  unless ty.nodesLe maxTermNodes && value.nodesLe maxTermNodes do
    throw "sparse: term exceeds node budget"
  let (binders, body) := value.lams
  let (head, args) := body.spine
  let .const r us := head | throw "sparse: the body is not a recursor spine"
  let some (.recr _ _ rl np nmot nmin ni _ rules rty) := p.decl? r
    | throw "sparse: the head is not a recursor"
  unless rty.nodesLe maxTermNodes && rules.all (fun rule => rule.rhs.nodesLe maxTermNodes) do
    throw "sparse: recursor exceeds node budget"
  unless nmot == 1 do throw "sparse: not a single-motive recursor"
  unless rl == n && us == paramUnivs n do throw "sparse: recursor levels are not the definition's"
  unless rules.length == nmin do throw "sparse: rules and minors differ"
  let B := binders.length
  let arms := np + 1 + ni + 1
  unless arms < B do throw "sparse: no arm binder after the major"
  unless args.length == np + 1 + nmin + ni + 1 do throw "sparse: wrong argument count"
  let bvar := fun (q : Nat) => Term.var (B - 1 - q)
  let argAt := fun (i : Nat) => (args[i]?.map (·.1)).getD (.natLit 0)
  if let some i := firstFailing (List.range np) fun i => (argAt i).eqv (bvar i) then
    throw s!"sparse: parameter {i} out of place"
  if let some i := firstFailing (List.range ni) fun i =>
      (argAt (np + 1 + nmin + i)).eqv (bvar (np + 1 + i)) then
    throw s!"sparse: index {i} out of place"
  unless (argAt (np + 1 + nmin + ni)).eqv (bvar (np + 1 + ni)) do
    throw "sparse: major out of place"
  let used ← sparseMinors np nmin B arms argAt 0 rules
  unless used.length == B - arms &&
      (List.range (B - arms)).all (fun i => used.contains (arms + i)) do
    throw "sparse: the named constructors' minors do not apply each arm once"
  if let some q := firstFailing (List.range B) fun q =>
      q == np || decide (valueUses body (B - 1 - q) ≤ 1) then
    throw s!"sparse: binder {q} is used more than once"
  return B

/-! ## `lazy`, `inline`, `prim` -/

/-- A pinned `lazy` row (`Pinned.lazyPins`): the constant's address with this
arity. Addresses are content hashes, checked when the closure is read. -/
def pinnedLazy (p : Program) (f : CId) (arity : Nat) : Bool :=
  Pinned.lazyPins.contains (Pinned.addrNat (p.addr f), arity)

/-- A `lazy` entry: a safe definition with at least `arity` leading λs that is
a pinned row (`pinnedLazy`) or a sparse casesOn of `arity` binders
(`checkSparseCases`), and nothing else. `Table.build`, `Table.validate` and
`Table.ofCert` all check a `lazy` row with this function, so no proposal or
certificate passes another definition's arguments by name. -/
def checkLazy (p : Program) (f : CId) (arity : Nat) : Except String Unit := do
  let some (_, ty, value) := safeDefn? p f | throw "lazy: not a safe definition"
  unless ty.nodesLe maxTermNodes && value.nodesLe maxTermNodes do
    throw "lazy: term exceeds node budget"
  unless arity ≥ 1 && value.lamCount ≥ arity do throw "lazy: too few leading λs"
  unless pinnedLazy p f arity do
    match checkSparseCases p f with
    | .ok b =>
      unless b == arity do
        throw s!"lazy: not a pinned row, and a sparse casesOn of {b} binders, not {arity}"
    | .error msg => throw s!"lazy: not a pinned row, and not a sparse casesOn ({msg})"

def checkInline (p : Program) (f : CId) (cap : Nat) : Except String Unit := do
  let some (_, ty, value) := safeDefn? p f | throw "inline: not a safe definition"
  unless ty.nodesLe maxTermNodes do throw "inline: type exceeds node budget"
  unless cap ≤ maxTermNodes && value.nodesLe cap do throw "inline: over the size cap"
  if value.mentions f then throw "inline: self-referential"

/-- `Nat → Nat → Nat`, `Nat → Nat → Bool` or `Nat → Nat` over the pinned
types, by the operation's arity and result. -/
def checkPrim (p : Program) (f : CId) (op : PrimOp) (enabled : List PrimOp) :
    Except String Unit := do
  unless enabled.contains op do throw s!"prim: {op.name} is not in the configured set"
  unless some (Pinned.addrNat (p.addr f)) == p.known.pins.prim? op do
    throw "prim: the address is not the pinned one"
  let some natId := p.known.nat | throw "prim: Nat is absent"
  let nat := Term.const natId []
  let result ← if op.isPredicate then
      match p.known.bool with
      | some b => pure (Term.const b [])
      | none => throw "prim: Bool is absent"
    else pure nat
  let expected := if op.arity == 1 then Term.pi {} {} nat result
    else Term.pi {} {} nat (Term.pi {} {} nat result)
  let some d := p.decl? f | throw "prim: missing declaration"
  unless d.type.nodesLe maxTermNodes do throw "prim: type exceeds node budget"
  unless d.type.eqv expected do throw s!"prim: {op.name} does not have the primitive type"

/-! ## Derived `RecKind` -/

/-- Derive a recursor's kind (per profile as D18 asks): `empty` with no
rules; for a single-rule recursor of a family whose type ends in `sort u`,
`subsingleton when` with `when` the zero condition of `u` over the
recursor's own universe parameters (read through the major's universe
arguments), each field read from the constructor index that is exactly that
field, or a proof; `ordinary` otherwise (and where `when` fails). Lean's
large-elimination criterion makes the non-index fields propositions whenever
the recursor can eliminate into a relevant motive. -/
def deriveRecKind (p : Program) (r : CId) : Option RecKind := do
  let .recr _ _ _ _ _ _ _ ind rules recTy ← p.decl? r | none
  unless recTy.nodesLe maxTermNodes && rules.all (fun rule => rule.rhs.nodesLe maxTermNodes) do none
  if rules.isEmpty then return .empty
  let .induct _ _ _ _ indTy _ ← p.decl? ind | none
  unless indTy.nodesLe maxTermNodes do none
  let .sort u := indTy.pis.2 | return .ordinary
  let some us := p.majorUnivs r | return .ordinary
  let when := ((zeroCond u).inst us).dedup
  if when == .never || rules.length != 1 then return .ordinary
  let rule ← rules.head?
  let .ctor _ _ _ _ np nf ctorTy ← p.decl? rule.ctor | none
  unless ctorTy.nodesLe maxTermNodes do none
  let (_, result) := ctorTy.pis
  let indices := (result.spine.2.map (·.1)).drop np
  let fields := (List.range nf).map fun j =>
    match indices.findIdx? (·.eqv (.var (nf - 1 - j))) with
    | some i => FieldSrc.index i
    | none => FieldSrc.proof
  return .subsingleton when fields

end IxCC.Src.Table
