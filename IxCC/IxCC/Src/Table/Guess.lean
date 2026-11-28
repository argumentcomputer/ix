import IxCC.Src.Table.Check

/-! # Phase 2 Tier-2 `guess f c θ [θc]` table check (`IxCC.Src.Table.Guess`)

Zero-TCB kernel-evaluable verification for guess-and-verify ("nondeterministic hint + verified
checker") entries:

* Subject `f` and checker `c` are safe definitions with the same universe parameter count `n`
  (`n < UInt64.size`), with types
  `f : Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁), B` and
  `c : Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁) (y : B), Bool`.
* Soundness/uniqueness theorem `thm` (`θ`) is a safe theorem with `n` universe parameters, read
  with its proof (`!Program.byStatement.contains thm`), depending only on standard Lean axioms
  (`checkAxiomClosure`), with exact syntactic shape (`Term.eqv` / `domainEqv`):
  ```
  Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁) (y : B) (_ : @Eq.{1} Bool (c.{u} x₀…xₖ₋₁ y) Bool.true),
    @Eq.{u_B} B y (f.{u} x₀…xₖ₋₁)
  ```
* Optional completeness theorem `comp` (`θc`) passes the same safety/proof/axiom/node-count
  checks and has exact syntactic shape:
  ```
  Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁),
    @Eq.{1} Bool (c.{u} x₀…xₖ₋₁ (f.{u} x₀…xₖ₋₁)) Bool.true
  ```
* **Non-circularity guard (`FE-3`)**: `c` does NOT transitively reference `f` in `p.decl?`
  (`checkDoesNotReach`, proved sound against `AxiomReach`), preventing vacuous circular
  self-checking (`c x y := (y == f x)`).

Uses only existing pinned constants (`p.known.eq`, `p.known.bool`, `p.known.boolTrue`) and is
kernel-evaluable (`D17`). -/

namespace IxCC.Src.Table.Guess

open IxCC.Ixon
open IxCC.Src
open IxCC.Src.Table

/-- A checked guess-and-verify entry for a subject function `f`: re-export of `IxCC.Src.GuessEntry`. -/
abbrev GuessEntry := IxCC.Src.GuessEntry

theorem guessEntry_beq_eq_true_iff (a b : GuessEntry) : (a == b) = true ↔ a = b := by
  cases a with
  | mk c1 a1 t1 o1 =>
    cases b with
    | mk c2 a2 t2 o2 =>
      cases o1 <;> cases o2 <;> simp [BEq.beq, IxCC.Src.instBEqGuessEntry.beq, Option.instBEq.beq]

/-! ## Term helpers -/

/-- Lift loose de Bruijn variables `≥ cutoff` up by `byN` (structural, kernel-evaluable). -/
def liftTerm (byN : Nat) : Nat → Term → Term
  | _, .sort u => .sort u
  | _, .const c us => .const c us
  | _, .natLit n => .natLit n
  | _, .strLit s => .strLit s
  | cutoff, .var i => if i ≥ cutoff then .var (i + byN) else .var i
  | cutoff, .app f a m r => .app (liftTerm byN cutoff f) (liftTerm byN cutoff a) m r
  | cutoff, .lam b d t => .lam b (liftTerm byN cutoff d) (liftTerm byN (cutoff + 1) t)
  | cutoff, .pi b d t => .pi b (liftTerm byN cutoff d) (liftTerm byN (cutoff + 1) t)
  | cutoff, .letE nd m r t v b =>
      .letE nd m r (liftTerm byN cutoff t) (liftTerm byN cutoff v) (liftTerm byN (cutoff + 1) b)
  | cutoff, .proj s i e => .proj s i (liftTerm byN cutoff e)

/-- `k` consecutive bound variables starting at `offset`, outermost first:
`#(offset + k - 1) … #offset`. -/
def boundVarsFrom (offset k : Nat) : List Term :=
  (List.range k).reverse.map fun i => Term.var (offset + i)

/-- Apply constant `d` at its `n` universe parameters to `#(offset + k - 1) … #offset`. -/
def mkAppVars (d : CId) (n offset k : Nat) : Term :=
  Term.mkApps (.const d (paramUnivs n))
    ((boundVarsFrom offset k).map fun t => (t, Mode.strict, Rel.rel))

/-- `@Eq.{1} ty lhs rhs` using the pinned `Eq` constant `eqC`. -/
def mkEq1 (eqC : CId) (ty lhs rhs : Term) : Term :=
  .app (.app (.app (.const eqC [.succ .zero]) ty .strict .rel) lhs .strict .rel) rhs .strict .rel

/-- `c.{u} #(k-1) … #0 (f.{u} #(k-1) … #0)` under `k` argument binders. -/
def mkCompCApp (c f : CId) (n k : Nat) : Term :=
  .app (mkAppVars c n 0 k) (mkAppVars f n 0 k) .strict .rel

/-- Match `app* (const Eq [u]) [ty, lhs, rhs]` over the pinned `Eq`, returning `(u, ty, lhs, rhs)`. -/
def eqAppUniv? (p : Program) (t : Term) : Option (Univ × Term × Term × Term) :=
  match t.spine with
  | (.const c [u], [(ty, _), (lhs, _), (rhs, _)]) =>
    if some c == p.known.eq then some (u, ty, lhs, rhs) else none
  | _ => none

/-! ## Non-circularity guard (`FE-3`) -/

/-- Bounded DFS checking that `target` is NOT transitively reachable from `todo` in `p.decl?`
(within `maxBodyNodes` per declaration and `fuel` steps). Fails closed on missing declarations,
node-budget overflow, or fuel exhaustion (`D17` kernel-evaluable). -/
def checkDoesNotReachWalk (p : Program) (target : CId) : Nat → List CId → List CId → Bool
  | 0, _ :: _, _ => false
  | _, [], _ => true
  | fuel + 1, cur :: todo, seen =>
    if cur == target then
      false
    else if seen.contains cur then
      checkDoesNotReachWalk p target fuel todo seen
    else
      match p.decl? cur with
      | none => false
      | some d =>
        match collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
        | none => false
        | some (_, refs) =>
          let newRefs := refs.filter (fun r => !seen.contains r && !todo.contains r)
          checkDoesNotReachWalk p target fuel (newRefs ++ todo) (cur :: seen)

/-- Non-circularity guard (`FE-3`): verify that `src` does NOT transitively reference `target`
in `p.decl?`. Prevents vacuous circular self-checking (`c x y := (y == f x)`). -/
def checkDoesNotReach (p : Program) (src target : CId) : Except String Unit :=
  if checkDoesNotReachWalk p target (p.size * 2 + 16) [src] [] then
    .ok ()
  else
    throw "guess: checker transitively references subject or exceeds dependency budget"

/-- Invariant of `checkDoesNotReachWalk p target fuel todo seen`: no visited constant is `target`,
and every direct `AxiomEdge` dependency of a visited constant lies in `seen` or `todo`. -/
def NotReachClosed (p : Program) (target : CId) (todo seen : List CId) : Prop :=
  ∀ s ∈ seen, s ≠ target ∧
    ∀ d r, p.decl? s = some d → AxiomEdge d r → r ∈ seen ∨ r ∈ todo

theorem checkDoesNotReachWalk_closed {p : Program} {target : CId} :
    ∀ (fuel : Nat) (todo seen : List CId),
      checkDoesNotReachWalk p target fuel todo seen = true →
      NotReachClosed p target todo seen →
      ∃ S : List CId, (∀ x ∈ todo, x ∈ S) ∧ (∀ x ∈ seen, x ∈ S) ∧ NotReachClosed p target [] S := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo seen h hinv
    cases todo with
    | nil => exact ⟨seen, (fun _ hx => by cases hx), (fun _ hx => hx), hinv⟩
    | cons _ _ => simp [checkDoesNotReachWalk] at h
  | succ fuel ih =>
    intro todo seen h hinv
    cases todo with
    | nil => exact ⟨seen, (fun _ hx => by cases hx), (fun _ hx => hx), hinv⟩
    | cons cur rest =>
      simp only [checkDoesNotReachWalk] at h
      cases hct : (cur == target) with
      | true => simp [hct] at h
      | false =>
        simp only [hct, Bool.false_eq_true, ↓reduceIte] at h
        have hne : cur ≠ target := by
          intro heq
          subst heq
          have hr : (cur == cur) = true := decide_eq_true rfl
          rw [hr] at hct
          cases hct
        cases hcs : seen.contains cur with
        | true =>
          simp only [hcs, ↓reduceIte] at h
          have hcs' : cur ∈ seen := List.contains_iff_mem.1 hcs
          have hinv' : NotReachClosed p target rest seen := by
            intro s hs
            refine ⟨(hinv s hs).1, fun d r hd hedge => ?_⟩
            rcases (hinv s hs).2 d r hd hedge with h1 | h1
            · exact Or.inl h1
            · rcases List.mem_cons.1 h1 with rfl | h1
              · exact Or.inl hcs'
              · exact Or.inr h1
          obtain ⟨S, hS1, hS2, hS3⟩ := ih rest seen h hinv'
          refine ⟨S, fun x hx => ?_, hS2, hS3⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hS2 _ hcs'
          · exact hS1 x hx
        | false =>
          simp only [hcs, Bool.false_eq_true, ↓reduceIte] at h
          cases hd : p.decl? cur with
          | none => rw [hd] at h; cases h
          | some d =>
            rw [hd] at h
            dsimp only at h
            cases hcol : collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
            | none => rw [hcol] at h; cases h
            | some pair =>
              rcases pair with ⟨bud, refs⟩
              rw [hcol] at h
              dsimp only at h
              obtain ⟨hcol1, hcol2⟩ := collectTermsConsts_sound _ _ _ bud refs hcol
              let newRefs := refs.filter (fun r => !seen.contains r && !rest.contains r)
              have hinv' : NotReachClosed p target (newRefs ++ rest) (cur :: seen) := by
                intro s hs
                rcases List.mem_cons.1 hs with rfl | hs
                · refine ⟨hne, fun d' r hd' hedge => ?_⟩
                  rw [hd] at hd'
                  cases hd'
                  have hr : r ∈ refs := by
                    rcases hedge with ⟨t, ht, hm⟩ | hm
                    · exact hcol2 t ht r hm
                    · exact hcol1 r hm
                  cases hrs : seen.contains r with
                  | true => exact Or.inl (List.mem_cons_of_mem _ (List.contains_iff_mem.1 hrs))
                  | false =>
                    cases hrr : rest.contains r with
                    | true => exact Or.inr (List.mem_append_right _ (List.contains_iff_mem.1 hrr))
                    | false =>
                      refine Or.inr (List.mem_append_left _ ?_)
                      refine List.mem_filter.2 ⟨hr, ?_⟩
                      simp only [hrs, hrr]
                      rfl
                · refine ⟨(hinv s hs).1, fun d' r hd' hedge => ?_⟩
                  rcases (hinv s hs).2 d' r hd' hedge with h1 | h1
                  · exact Or.inl (List.mem_cons_of_mem _ h1)
                  · rcases List.mem_cons.1 h1 with rfl | h1
                    · exact Or.inl List.mem_cons_self
                    · exact Or.inr (List.mem_append_right _ h1)
              obtain ⟨S, hS1, hS2, hS3⟩ := ih (newRefs ++ rest) (cur :: seen) h hinv'
              refine ⟨S, fun x hx => ?_, fun x hx => hS2 x (List.mem_cons_of_mem _ hx), hS3⟩
              rcases List.mem_cons.1 hx with rfl | hx
              · exact hS2 _ List.mem_cons_self
              · exact hS1 x (List.mem_append_right _ hx)

theorem axiomReach_mem_of_notReachClosed {p : Program} {target root : CId} {S : List CId}
    (hS : NotReachClosed p target [] S) (hroot : root ∈ S) :
    ∀ {c : CId}, AxiomReach p root c → c ∈ S
  | _, .refl => hroot
  | _, .step hr hd hedge => by
    have ha := axiomReach_mem_of_notReachClosed hS hroot hr
    rcases (hS _ ha).2 _ _ hd hedge with h | h
    · exact h
    · cases h

/-- **Soundness of `checkDoesNotReach`.** If `checkDoesNotReach p src target` accepts, then
`target` is not transitively reachable from `src` along `AxiomEdge` in `p`. -/
theorem checkDoesNotReach_sound {p : Program} {src target : CId}
    (h : checkDoesNotReach p src target = .ok ()) :
    ¬ AxiomReach p src target := by
  unfold checkDoesNotReach at h
  cases hwalk : checkDoesNotReachWalk p target (p.size * 2 + 16) [src] [] with
  | false => simp [hwalk] at h
  | true =>
    have hinit : NotReachClosed p target [src] [] := fun _ hs => by cases hs
    obtain ⟨S, hS1, _, hS3⟩ := checkDoesNotReachWalk_closed _ [src] [] hwalk hinit
    have hsrc : src ∈ S := hS1 src List.mem_cons_self
    intro hreach
    have htgt : target ∈ S := axiomReach_mem_of_notReachClosed hS3 hsrc hreach
    exact (hS3 target htgt).1 rfl

theorem checkDoesNotReach_ne {p : Program} {src target : CId}
    (h : checkDoesNotReach p src target = .ok ()) :
    src ≠ target := by
  intro heq
  subst heq
  exact checkDoesNotReach_sound h .refl

/-! ## Modular check stages: declarations, soundness shape, completeness shape -/

/-- Checked declaration metadata for `(f, c, thm)` (steps 1–2 of `checkGuess`). -/
structure GuessDecls where
  lvls : Nat
  tf : Term
  vf : Term
  tc : Term
  vc : Term
  tθ : Term
  vθ : Term

/-- Steps 1–2: verify `f` and `c` are safe definitions with matching universe counts
(`< UInt64.size`), `thm` is a safe theorem with the same universe count, not `byStatement`,
within `maxTermNodes`, and standard-axiom closed. -/
def checkGuessDecls (p : Program) (f c thm : CId) : Except String GuessDecls :=
  match safeDefn? p f with
  | none => .error "guess: subject is not a safe definition"
  | some (n, tf, vf) =>
    match safeDefn? p c with
    | none => .error "guess: checker is not a safe definition"
    | some (n', tc, vc) =>
      if n' != n then
        .error "guess: checker universe parameter count differs from subject"
      else if !(decide (n < UInt64.size)) then
        .error "guess: universe parameter count exceeds UInt64"
      else
        match p.decl? thm with
        | some (.defn .thm .safe n'' tθ vθ) =>
          if n'' != n then
            .error "guess: soundness theorem universe parameter count differs from subject"
          else if p.byStatement.contains thm then
            .error "guess: soundness theorem was read by its statement; its proof is not in the program"
          else if !(tf.nodesLe maxTermNodes && tc.nodesLe maxTermNodes &&
              tθ.nodesLe maxTermNodes) then
            .error "guess: term exceeds node budget"
          else
            match checkAxiomClosure p thm with
            | .error e => .error e
            | .ok () => .ok { lvls := n, tf, vf, tc, vc, tθ, vθ }
        | _ => .error "guess: soundness theorem is not a safe theorem"

/-- Checked syntactic-shape metadata from step 3 of `checkGuess`. -/
structure GuessShapeMeta where
  arity : Nat
  fBinders : List (Binder × Term)
  eqC : CId
  boolC : CId
  boolTrueC : CId

/-- Step 3a: check binder structure and domains of `tf`, `tc`, `tθ`. -/
def checkGuessBinders (p : Program) (tf tc tθ : Term) (boolC : CId) :
    Except String (Nat × List (Binder × Term) × Term × Term × Term) :=
  let totalPis := tθ.piCount
  if !(decide (totalPis ≥ 2)) then
    .error "guess: soundness theorem must have at least 2 binders (witness and check hypothesis)"
  else
    let k := totalPis - 2
    match peelPis k tθ with
    | some (θArgs, .pi _ yDom (.pi _ hDom θBody)) =>
      match peelPis k tf with
      | none => .error "guess: subject's type has fewer binders than soundness theorem"
      | some (fBinders, fBody) =>
        match peelPis k tc with
        | some (cArgs, .pi _ cYDom cBody) =>
          if !(fBinders.zip θArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') then
            .error "guess: soundness theorem argument domains differ from subject"
          else if !domainEqv p fBody yDom then
            .error "guess: soundness theorem witness domain differs from subject result type"
          else if !(fBinders.zip cArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') then
            .error "guess: checker argument domains differ from subject"
          else if !domainEqv p fBody cYDom then
            .error "guess: checker witness domain differs from subject result type"
          else if !cBody.eqv (.const boolC []) then
            .error "guess: checker result type is not Bool"
          else
            .ok (k, fBinders, fBody, hDom, θBody)
        | _ => .error "guess: checker's type has fewer binders or no witness binder"
    | _ => .error "guess: soundness theorem has too few binders"

/-- Step 3b: check the hypothesis `hDom` (`@Eq.{1} Bool (c xs y) Bool.true`) and conclusion
`θBody` (`@Eq.{u_B} (liftTerm 2 0 B) y (f xs)`) of `θ`. -/
def checkGuessBody (p : Program) (f c : CId) (n k : Nat) (fBody hDom θBody : Term)
    (eqC boolC boolTrueC : CId) : Except String Unit :=
  let expectedHDom :=
    mkEq1 eqC (.const boolC []) (mkAppVars c n 0 (k + 1)) (.const boolTrueC [])
  if !hDom.eqv expectedHDom then
    .error "guess: soundness theorem hypothesis is not `@Eq.{1} Bool (c xs y) Bool.true`"
  else
    match eqAppUniv? p θBody with
    | none => .error "guess: soundness theorem conclusion is not Eq"
    | some (_uB, eqTy, lhs, rhs) =>
      if !domainEqv p (liftTerm 2 0 fBody) eqTy then
        .error "guess: soundness theorem equality type differs from subject result type"
      else if !lhs.eqv (.var 1) then
        .error "guess: soundness theorem conclusion left-hand side is not witness variable y"
      else if !rhs.eqv (mkAppVars f n 2 k) then
        .error "guess: soundness theorem conclusion right-hand side is not `f xs`"
      else
        .ok ()

/-- Step 4: check optional completeness theorem `comp`:
`Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁), @Eq.{1} Bool (c.{u} x₀…xₖ₋₁ (f.{u} x₀…xₖ₋₁)) Bool.true`. -/
def checkComp (p : Program) (f c comp : CId) (n k : Nat) (fBinders : List (Binder × Term))
    (eqC boolC boolTrueC : CId) : Except String Unit :=
  match p.decl? comp with
  | some (.defn .thm .safe nComp tComp _vComp) =>
    if nComp != n then
      .error "guess: completeness theorem universe parameter count differs from subject"
    else if p.byStatement.contains comp then
      .error "guess: completeness theorem was read by its statement; its proof is not in the program"
    else if !tComp.nodesLe maxTermNodes then
      .error "guess: completeness theorem exceeds node budget"
    else
      match checkAxiomClosure p comp with
      | .error e => .error e
      | .ok () =>
        match peelPis k tComp with
        | none => .error "guess: completeness theorem has too few binders"
        | some (compBinders, compBody) =>
          if !(fBinders.zip compBinders).all (fun ((_, a), (_, a')) => domainEqv p a a') then
            .error "guess: completeness theorem binder domains differ from subject"
          else
            let expectedCompBody :=
              mkEq1 eqC (.const boolC []) (mkCompCApp c f n k) (.const boolTrueC [])
            if !compBody.eqv expectedCompBody then
              .error "guess: completeness theorem conclusion is not `@Eq.{1} Bool (c xs (f xs)) Bool.true`"
            else
              .ok ()
  | _ => .error "guess: completeness theorem is not a safe theorem"

/-- Check a Phase 2 Tier-2 guess-and-verify proposal `guess f c thm [comp?]`. -/
def checkGuess (p : Program) (f c thm : CId) (comp? : Option CId) : Except String GuessEntry :=
  match checkGuessDecls p f c thm with
  | .error e => .error e
  | .ok d =>
    match p.known.eq, p.known.bool, p.known.boolTrue with
    | some eqC, some boolC, some boolTrueC =>
      match checkGuessBinders p d.tf d.tc d.tθ boolC with
      | .error e => .error e
      | .ok (k, fBinders, fBody, hDom, θBody) =>
        match checkGuessBody p f c d.lvls k fBody hDom θBody eqC boolC boolTrueC with
        | .error e => .error e
        | .ok () =>
          let compRes : Except String Unit := match comp? with
            | none => .ok ()
            | some comp => checkComp p f c comp d.lvls k fBinders eqC boolC boolTrueC
          match compRes with
          | .error e => .error e
          | .ok () =>
            if c == f then
              .error "guess: checker cannot be the subject itself"
            else
              match checkDoesNotReach p c f with
              | .error e => .error e
              | .ok () => .ok { checker := c, arity := k, thm, comp? }
    | _, _, _ => .error "guess: pinned Eq, Bool, or Bool.true is absent"

/-- Revalidate a stored `GuessEntry` for subject `f` on the recheck path (`style V`). -/
def validateGuess (p : Program) (f : CId) (g : GuessEntry) : Except String Unit :=
  match checkGuess p f g.checker g.thm g.comp? with
  | .error e => .error e
  | .ok checked =>
    if checked == g then .ok ()
    else .error "guess: entry does not match checked guess entry"

/-! ## Structural helper lemmas -/

theorem peelPis_length : ∀ (k : Nat) (t : Term) (bs : List (Binder × Term)) (body : Term),
    peelPis k t = some (bs, body) → bs.length = k
  | 0, t, bs, body, h => by
    simp only [peelPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | k + 1, .pi b d t, bs, body, h => by
    simp only [peelPis, Option.bind_eq_bind] at h
    cases h' : peelPis k t with
    | none => simp [h'] at h
    | some pair =>
      rcases pair with ⟨bs', body'⟩
      simp only [h', Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [peelPis_length k t bs' body' h']
  | _ + 1, .var _, _, _, h | _ + 1, .sort _, _, _, h | _ + 1, .const _ _, _, _, h
  | _ + 1, .app _ _ _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h | _ + 1, .letE _ _ _ _ _ _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h | _ + 1, .natLit _, _, _, h | _ + 1, .strLit _, _, _, h => by
    simp [peelPis] at h

private theorem eq_of_bne_false {a b : Nat} (h : ¬ (a != b) = true) : a = b := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
  exact h

private theorem eq_true_of_not_bang {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b <;> simp_all

private theorem eq_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- Structural properties established by `checkComp p f c comp n k fBinders eqC boolC boolTrueC = .ok ()`. -/
def CompOkProps (p : Program) (f c comp : CId) (n k : Nat)
    (fBinders : List (Binder × Term)) (eqC boolC boolTrueC : CId) : Prop :=
  ∃ (tComp vComp : Term) (compBinders : List (Binder × Term)) (compBody : Term),
    p.decl? comp = some (.defn .thm .safe n tComp vComp) ∧
    p.byStatement.contains comp = false ∧
    tComp.nodesLe maxTermNodes = true ∧
    checkAxiomClosure p comp = .ok () ∧
    peelPis k tComp = some (compBinders, compBody) ∧
    (fBinders.zip compBinders).all (fun ((_, a), (_, a')) => domainEqv p a a') = true ∧
    compBody.eqv (mkEq1 eqC (.const boolC []) (mkCompCApp c f n k) (.const boolTrueC [])) = true

theorem checkComp_ok_props {p : Program} {f c comp : CId} {n k : Nat}
    {fBinders : List (Binder × Term)} {eqC boolC boolTrueC : CId}
    (h : checkComp p f c comp n k fBinders eqC boolC boolTrueC = .ok ()) :
    CompOkProps p f c comp n k fBinders eqC boolC boolTrueC := by
  unfold checkComp at h
  split at h
  · rename_i nComp tComp vComp hdecl
    split at h; · cases h
    rename_i hn
    have hnEq : nComp = n := eq_of_bne_false hn
    subst hnEq
    split at h; · cases h
    rename_i hbs
    split at h; · cases h
    rename_i hnd
    split at h; · cases h
    rename_i hax
    split at h; · cases h
    rename_i compBinders compBody hpeel
    split at h; · cases h
    rename_i hdom
    dsimp only at h
    split at h; · cases h
    rename_i hbody
    exact ⟨tComp, vComp, compBinders, compBody, hdecl, eq_false_of_not_true hbs,
      eq_true_of_not_bang hnd, hax, hpeel, eq_true_of_not_bang hdom, eq_true_of_not_bang hbody⟩
  · cases h

private theorem checkGuessDecls_ok {p : Program} {f c thm : CId} {d : GuessDecls}
    (h : checkGuessDecls p f c thm = .ok d) :
    d.lvls < UInt64.size ∧
    safeDefn? p f = some (d.lvls, d.tf, d.vf) ∧
    safeDefn? p c = some (d.lvls, d.tc, d.vc) ∧
    p.decl? thm = some (.defn .thm .safe d.lvls d.tθ d.vθ) ∧
    p.byStatement.contains thm = false ∧
    d.tf.nodesLe maxTermNodes = true ∧
    d.tc.nodesLe maxTermNodes = true ∧
    d.tθ.nodesLe maxTermNodes = true ∧
    checkAxiomClosure p thm = .ok () := by
  unfold checkGuessDecls at h
  split at h; · cases h
  rename_i n tf vf hsf
  split at h; · cases h
  rename_i n' tc vc hsc
  split at h; · cases h
  rename_i hn'
  have hn'Eq : n' = n := eq_of_bne_false hn'
  subst hn'Eq
  split at h; · cases h
  rename_i hltB
  have hlt : n' < UInt64.size := of_decide_eq_true (eq_true_of_not_bang hltB)
  split at h
  · rename_i n'' tθ vθ hthm
    split at h; · cases h
    rename_i hn''
    have hn''Eq : n'' = n' := eq_of_bne_false hn''
    subst hn''Eq
    split at h; · cases h
    rename_i hbs
    split at h; · cases h
    rename_i hndB
    have hnd : (tf.nodesLe maxTermNodes && tc.nodesLe maxTermNodes && tθ.nodesLe maxTermNodes) = true :=
      eq_true_of_not_bang hndB
    obtain ⟨⟨htfN, htcN⟩, htθN⟩ := by simpa [Bool.and_eq_true] using hnd
    split at h; · cases h
    rename_i hax
    cases h
    exact ⟨hlt, hsf, hsc, hthm, eq_false_of_not_true hbs, htfN, htcN, htθN, hax⟩
  · cases h

private theorem checkGuessBinders_ok {p : Program} {tf tc tθ : Term} {boolC : CId}
    {k : Nat} {fBinders : List (Binder × Term)} {fBody hDom θBody : Term}
    (h : checkGuessBinders p tf tc tθ boolC = .ok (k, fBinders, fBody, hDom, θBody)) :
    ∃ (cArgs : List (Binder × Term)) (bCY : Binder) (cYDom cBody : Term)
      (θArgs : List (Binder × Term)) (bY : Binder) (yDom : Term) (bH : Binder),
      peelPis k tf = some (fBinders, fBody) ∧
      peelPis k tc = some (cArgs, .pi bCY cYDom cBody) ∧
      (fBinders.zip cArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') = true ∧
      domainEqv p fBody cYDom = true ∧
      cBody.eqv (.const boolC []) = true ∧
      peelPis k tθ = some (θArgs, .pi bY yDom (.pi bH hDom θBody)) ∧
      (fBinders.zip θArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') = true ∧
      domainEqv p fBody yDom = true := by
  unfold checkGuessBinders at h
  dsimp only at h
  split at h; · cases h
  split at h
  · rename_i θArgs bY yDom bH hDom' θBody' hpeelθ
    split at h; · cases h
    rename_i fBinders' fBody' hpeelF
    split at h
    · rename_i cArgs bCY cYDom cBody hpeelC
      split at h; · cases h
      rename_i hθD
      split at h; · cases h
      rename_i hyD
      split at h; · cases h
      rename_i hcD
      split at h; · cases h
      rename_i hcYD
      split at h; · cases h
      rename_i hcB
      cases h
      exact ⟨cArgs, bCY, cYDom, cBody, θArgs, bY, yDom, bH,
        hpeelF, hpeelC, eq_true_of_not_bang hcD, eq_true_of_not_bang hcYD,
        eq_true_of_not_bang hcB, hpeelθ, eq_true_of_not_bang hθD, eq_true_of_not_bang hyD⟩
    · cases h
  · cases h

private theorem checkGuessBody_ok {p : Program} {f c : CId} {n k : Nat} {fBody hDom θBody : Term}
    {eqC boolC boolTrueC : CId}
    (h : checkGuessBody p f c n k fBody hDom θBody eqC boolC boolTrueC = .ok ()) :
    hDom.eqv
      (mkEq1 eqC (.const boolC []) (mkAppVars c n 0 (k + 1)) (.const boolTrueC [])) = true ∧
    ∃ (uB : Univ) (eqTy lhs rhs : Term),
      eqAppUniv? p θBody = some (uB, eqTy, lhs, rhs) ∧
      domainEqv p (liftTerm 2 0 fBody) eqTy = true ∧
      lhs.eqv (.var 1) = true ∧
      rhs.eqv (mkAppVars f n 2 k) = true := by
  unfold checkGuessBody at h
  dsimp only at h
  split at h; · cases h
  rename_i hhD
  split at h; · cases h
  rename_i uB eqTy lhs rhs hθEq
  split at h; · cases h
  rename_i heqTy
  split at h; · cases h
  rename_i hlhs
  split at h; · cases h
  rename_i hrhs
  exact ⟨eq_true_of_not_bang hhD, uB, eqTy, lhs, rhs, hθEq,
    eq_true_of_not_bang heqTy, eq_true_of_not_bang hlhs, eq_true_of_not_bang hrhs⟩

/-- Structural properties established by `checkGuess p f c thm comp? = .ok g`. -/
def GuessOkProps (p : Program) (f c thm : CId) (comp? : Option CId) (g : GuessEntry) : Prop :=
  g.checker = c ∧ g.thm = thm ∧ g.comp? = comp? ∧
  ∃ (n : Nat) (tf vf tc vc tθ vθ : Term) (eqC boolC boolTrueC : CId)
    (fBinders : List (Binder × Term)) (fBody : Term)
    (cArgs : List (Binder × Term)) (bCY : Binder) (cYDom cBody : Term)
    (θArgs : List (Binder × Term)) (bY : Binder) (yDom : Term) (bH : Binder) (hDom θBody : Term)
    (uB : Univ) (eqTy lhs rhs : Term),
    n < UInt64.size ∧
    safeDefn? p f = some (n, tf, vf) ∧
    safeDefn? p c = some (n, tc, vc) ∧
    p.decl? thm = some (.defn .thm .safe n tθ vθ) ∧
    p.byStatement.contains thm = false ∧
    tf.nodesLe maxTermNodes = true ∧
    tc.nodesLe maxTermNodes = true ∧
    tθ.nodesLe maxTermNodes = true ∧
    checkAxiomClosure p thm = .ok () ∧
    ¬ AxiomReach p c f ∧
    c ≠ f ∧
    p.known.eq = some eqC ∧
    p.known.bool = some boolC ∧
    p.known.boolTrue = some boolTrueC ∧
    peelPis g.arity tf = some (fBinders, fBody) ∧
    peelPis g.arity tc = some (cArgs, .pi bCY cYDom cBody) ∧
    (fBinders.zip cArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') = true ∧
    domainEqv p fBody cYDom = true ∧
    cBody.eqv (.const boolC []) = true ∧
    peelPis g.arity tθ = some (θArgs, .pi bY yDom (.pi bH hDom θBody)) ∧
    (fBinders.zip θArgs).all (fun ((_, a), (_, a')) => domainEqv p a a') = true ∧
    domainEqv p fBody yDom = true ∧
    hDom.eqv
      (mkEq1 eqC (.const boolC []) (mkAppVars c n 0 (g.arity + 1)) (.const boolTrueC [])) = true ∧
    eqAppUniv? p θBody = some (uB, eqTy, lhs, rhs) ∧
    domainEqv p (liftTerm 2 0 fBody) eqTy = true ∧
    lhs.eqv (.var 1) = true ∧
    rhs.eqv (mkAppVars f n 2 g.arity) = true ∧
    ∀ comp, comp? = some comp →
      CompOkProps p f c comp n g.arity fBinders eqC boolC boolTrueC

/-- **Soundness of `checkGuess`**: returning `.ok g` establishes every structural, safety,
axiom-closure, non-circularity, and syntactic-shape invariant in `GuessOkProps`. -/
theorem checkGuess_ok_props {p : Program} {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (h : checkGuess p f c thm comp? = .ok g) :
    GuessOkProps p f c thm comp? g := by
  unfold checkGuess at h
  split at h; · cases h
  rename_i d hd
  obtain ⟨hlt, hsf, hsc, hthm, hbs, htfN, htcN, htθN, hax⟩ := checkGuessDecls_ok hd
  split at h
  · rename_i eqC boolC boolTrueC heqC hboolC hbtC
    split at h; · cases h
    rename_i k fBinders fBody hDom θBody hbind
    obtain ⟨cArgs, bCY, cYDom, cBody, θArgs, bY, yDom, bH,
      hpeelF, hpeelC, hcD, hcYD, hcB, hpeelθ, hθD, hyD⟩ := checkGuessBinders_ok hbind
    split at h; · cases h
    rename_i hbody
    obtain ⟨hhD, uB, eqTy, lhs, rhs, hθEq, heqTy, hlhs, hrhs⟩ := checkGuessBody_ok hbody
    dsimp only at h
    split at h; · cases h
    rename_i hcompRes
    split at h; · cases h
    rename_i hcfB
    split at h; · cases h
    rename_i hnr
    cases h
    have hcf : c ≠ f := fun heq => by
      subst heq
      exact hcfB (decide_eq_true rfl)
    have hcompP : ∀ comp, comp? = some comp →
        CompOkProps p f c comp d.lvls k fBinders eqC boolC boolTrueC := by
      intro comp hcomp
      subst hcomp
      exact checkComp_ok_props hcompRes
    exact ⟨rfl, rfl, rfl,
      d.lvls, d.tf, d.vf, d.tc, d.vc, d.tθ, d.vθ, eqC, boolC, boolTrueC,
      fBinders, fBody, cArgs, bCY, cYDom, cBody, θArgs, bY, yDom, bH, hDom, θBody,
      uB, eqTy, lhs, rhs,
      hlt, hsf, hsc, hthm, hbs, htfN, htcN, htθN, hax, checkDoesNotReach_sound hnr, hcf,
      heqC, hboolC, hbtC,
      hpeelF, hpeelC, hcD, hcYD, hcB, hpeelθ, hθD, hyD, hhD, hθEq, heqTy, hlhs, hrhs, hcompP⟩
  · cases h

theorem checkGuess_ok_fields {p : Program} {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (h : checkGuess p f c thm comp? = .ok g) :
    g.checker = c ∧ g.thm = thm ∧ g.comp? = comp? := by
  obtain ⟨h1, h2, h3, _⟩ := checkGuess_ok_props h
  exact ⟨h1, h2, h3⟩

theorem checkGuess_ok_notReach {p : Program} {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (h : checkGuess p f c thm comp? = .ok g) :
    ¬ AxiomReach p c f := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, hnr, _⟩ := checkGuess_ok_props h
  exact hnr

theorem checkGuess_ok_axiomClosure {p : Program} {f c thm : CId} {comp? : Option CId}
    {g : GuessEntry} (h : checkGuess p f c thm comp? = .ok g) :
    checkAxiomClosure p thm = .ok () := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hax, _⟩ := checkGuess_ok_props h
  exact hax

theorem validateGuess_iff {p : Program} {f : CId} {g : GuessEntry} :
    validateGuess p f g = .ok () ↔ checkGuess p f g.checker g.thm g.comp? = .ok g := by
  unfold validateGuess
  cases h : checkGuess p f g.checker g.thm g.comp? with
  | error e => simp
  | ok checked =>
    simp only [Except.ok.injEq]
    split
    · rename_i heq
      have h' := (guessEntry_beq_eq_true_iff checked g).mp heq
      simp [h']
    · rename_i hne
      have h' : checked ≠ g := fun hc => hne ((guessEntry_beq_eq_true_iff checked g).mpr hc)
      simp [h']

theorem validateGuess_ok_props {p : Program} {f : CId} {g : GuessEntry}
    (h : validateGuess p f g = .ok ()) :
    GuessOkProps p f g.checker g.thm g.comp? g :=
  checkGuess_ok_props (validateGuess_iff.mp h)

/-! ## Table-independence of `checkGuess` / `validateGuess` -/

private theorem stripWrappers_with_table (p : Program) (t0 : Table) :
    ∀ (t : Term), stripWrappers { p with table := t0 } t = stripWrappers p t
  | .var _ | .sort _ | .const _ _ | .natLit _ | .strLit _ => rfl
  | .app f a m r => by
    simp only [stripWrappers, stripWrappers_with_table p t0 f, stripWrappers_with_table p t0 a]
    rfl
  | .lam b d body => by
    simp only [stripWrappers, stripWrappers_with_table p t0 d, stripWrappers_with_table p t0 body]
  | .pi b d cod => by
    simp only [stripWrappers, stripWrappers_with_table p t0 d, stripWrappers_with_table p t0 cod]
  | .letE nd m r ty v body => by
    simp only [stripWrappers, stripWrappers_with_table p t0 ty, stripWrappers_with_table p t0 v,
      stripWrappers_with_table p t0 body]
  | .proj s i e => by
    simp only [stripWrappers, stripWrappers_with_table p t0 e]

private theorem domainEqv_with_table (p : Program) (t0 : Table) (a b : Term) :
    domainEqv { p with table := t0 } a b = domainEqv p a b := by
  simp only [domainEqv, stripWrappers_with_table]

private theorem checkAxiomWalk_with_table (p : Program) (t0 : Table) :
    ∀ (fuel : Nat) (todo seen : List CId),
      checkAxiomWalk { p with table := t0 } fuel todo seen = checkAxiomWalk p fuel todo seen
  | 0, [], _ => rfl
  | 0, _ :: _, _ => rfl
  | _ + 1, [], _ => rfl
  | fuel + 1, c :: todo, seen => by
    unfold checkAxiomWalk
    by_cases hs : seen.contains c
    · simp only [hs, ↓reduceIte]
      exact checkAxiomWalk_with_table p t0 fuel todo seen
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      change (match p.decl? c with
        | none => false
        | some d =>
          if !declAxiomOk { p with table := t0 } c d then false
          else
            match collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
            | none => false
            | some (_, refs) =>
              let newRefs := refs.filter (fun r => !seen.contains r && !todo.contains r)
              checkAxiomWalk { p with table := t0 } fuel (newRefs ++ todo) (c :: seen)) = _
      cases hd : p.decl? c with
      | none => rfl
      | some d =>
        have hok : declAxiomOk { p with table := t0 } c d = declAxiomOk p c d := by
          cases d <;> rfl
        simp only [hok]
        by_cases hdo : (!declAxiomOk p c d) = true
        · simp [hdo]
        · simp only [hdo, Bool.false_eq_true, ↓reduceIte]
          cases hcol : collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
          | none => rfl
          | some pair =>
            exact checkAxiomWalk_with_table p t0 fuel _ (c :: seen)

private theorem checkAxiomClosure_with_table (p : Program) (t0 : Table) (thm : CId) :
    checkAxiomClosure { p with table := t0 } thm = checkAxiomClosure p thm := by
  unfold checkAxiomClosure
  rw [checkAxiomWalk_with_table]
  rfl

private theorem checkDoesNotReachWalk_with_table (p : Program) (t0 : Table) (target : CId) :
    ∀ (fuel : Nat) (todo seen : List CId),
      checkDoesNotReachWalk { p with table := t0 } target fuel todo seen =
        checkDoesNotReachWalk p target fuel todo seen
  | 0, [], _ => rfl
  | 0, _ :: _, _ => rfl
  | _ + 1, [], _ => rfl
  | fuel + 1, cur :: todo, seen => by
    unfold checkDoesNotReachWalk
    by_cases ht : (cur == target) = true
    · simp [ht]
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      by_cases hs : seen.contains cur
      · simp only [hs, ↓reduceIte]
        exact checkDoesNotReachWalk_with_table p t0 target fuel todo seen
      · simp only [hs, Bool.false_eq_true, ↓reduceIte]
        change (match p.decl? cur with
          | none => false
          | some d =>
            match collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
            | none => false
            | some (_, refs) =>
              let newRefs := refs.filter (fun r => !seen.contains r && !todo.contains r)
              checkDoesNotReachWalk { p with table := t0 } target fuel (newRefs ++ todo) (cur :: seen)) = _
        cases hd : p.decl? cur with
        | none => rfl
        | some d =>
          dsimp only
          cases hcol : collectTermsConsts (declTerms d) maxBodyNodes (declExtraConsts d) with
          | none => rfl
          | some pair =>
            dsimp only
            exact checkDoesNotReachWalk_with_table p t0 target fuel _ (cur :: seen)

private theorem checkDoesNotReach_with_table (p : Program) (t0 : Table) (src target : CId) :
    checkDoesNotReach { p with table := t0 } src target = checkDoesNotReach p src target := by
  unfold checkDoesNotReach
  have h : checkDoesNotReachWalk { p with table := t0 } target ({ p with table := t0 }.size * 2 + 16)
      [src] [] = checkDoesNotReachWalk p target (p.size * 2 + 16) [src] [] :=
    checkDoesNotReachWalk_with_table p t0 target (p.size * 2 + 16) [src] []
  rw [h]

private theorem checkGuessDecls_with_table (p : Program) (t0 : Table) (f c thm : CId) :
    checkGuessDecls { p with table := t0 } f c thm = checkGuessDecls p f c thm := by
  unfold checkGuessDecls
  simp only [checkAxiomClosure_with_table]
  rfl

private theorem checkGuessBinders_with_table (p : Program) (t0 : Table) (tf tc tθ : Term)
    (boolC : CId) :
    checkGuessBinders { p with table := t0 } tf tc tθ boolC =
      checkGuessBinders p tf tc tθ boolC := by
  unfold checkGuessBinders
  simp only [domainEqv_with_table]

private theorem checkGuessBody_with_table (p : Program) (t0 : Table) (f c : CId) (n k : Nat)
    (fBody hDom θBody : Term) (eqC boolC boolTrueC : CId) :
    checkGuessBody { p with table := t0 } f c n k fBody hDom θBody eqC boolC boolTrueC =
      checkGuessBody p f c n k fBody hDom θBody eqC boolC boolTrueC := by
  unfold checkGuessBody
  simp only [domainEqv_with_table]
  rfl

private theorem checkComp_with_table (p : Program) (t0 : Table) (f c comp : CId) (n k : Nat)
    (fBinders : List (Binder × Term)) (eqC boolC boolTrueC : CId) :
    checkComp { p with table := t0 } f c comp n k fBinders eqC boolC boolTrueC =
      checkComp p f c comp n k fBinders eqC boolC boolTrueC := by
  unfold checkComp
  simp only [checkAxiomClosure_with_table, domainEqv_with_table]
  rfl

/-- `checkGuess` depends only on declarations, pins, and `byStatement` — never on `p.table`. -/
theorem checkGuess_with_table (p : Program) (t0 : Table) (f c thm : CId) (comp? : Option CId) :
    checkGuess { p with table := t0 } f c thm comp? = checkGuess p f c thm comp? := by
  unfold checkGuess
  simp only [checkGuessDecls_with_table, checkGuessBinders_with_table, checkGuessBody_with_table,
    checkComp_with_table, checkDoesNotReach_with_table]

/-- `validateGuess` depends only on declarations, pins, and `byStatement` — never on `p.table`. -/
theorem validateGuess_with_table (p : Program) (t0 : Table) (f : CId) (g : GuessEntry) :
    validateGuess { p with table := t0 } f g = validateGuess p f g := by
  unfold validateGuess
  rw [checkGuess_with_table]

end IxCC.Src.Table.Guess
