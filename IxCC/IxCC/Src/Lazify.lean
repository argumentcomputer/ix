import IxCC.Src.Runtime

/-! # Src.Lazify

Sets `byName` on the arguments of saturated `lazy` spines (the first
`arity` arguments), on the minors of saturated recursor and `case` spines,
and on every IH argument of every rule `rhs`. A mode
matters only where its argument is relevant, so a level-conditional argument
(D18) gets its mode like any other; arguments irrelevant at every instance
are not entered. It never changes a class or a major, and it touches only
modes: `Lazify.run_modeEq` (`IxCC.Src.Proof.Lazify`) proves that `run`
changes nothing in a program but the modes of application nodes in the runtime
terms it visits. That is a syntactic fact; no theorem states that lazification
preserves the program's meaning under SrcEval (part of the open item S6 in
`IxCC/docs/certification-design.md`). It runs after the relevance check, on the checked runtime
terms.

Kernel-evaluable (D17, on the recheck path as a re-run pass): the term walk
is a mutual structural recursion over `Term`, a spine's by-name positions are
a list of intervals, and the program is read through its `NatMap`s. -/

namespace IxCC.Src.Lazify

/-- Argument positions of a spine of `n` arguments that become `byName`, as
half-open intervals `[lo, hi)`. -/
def byNameRanges (p : Program) (head : Term) (n : Nat) : List (Nat × Nat) :=
  match head with
  | .const c _ =>
    let lazy := match p.table.lazyOf c with
      | some a => if n ≥ a then [(0, a)] else []
      | none => []
    let elim := match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r with
        | some (.recr _ _ _ np _ nmin ni _ _ _) =>
          if n ≥ np + 1 + ni + 1 + nmin then [(np + 1 + ni + 1, np + 1 + ni + 1 + nmin)] else []
        | _ => []
      | none =>
        match p.decl? c with
        | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
          if n ≥ np + nmot + nmin + ni + 1 then [(np + nmot, np + nmot + nmin)] else []
        | _ => []
      | _ => []
    lazy ++ elim
  | _ => []

/-- Whether position `i` is in one of the intervals. -/
def inRanges (ranges : List (Nat × Nat)) (i : Nat) : Bool :=
  ranges.any fun (lo, hi) => lo ≤ i && i < hi

def newMode (ranges : List (Nat × Nat)) (i : Nat) (m : Mode) (r : Rel) : Mode :=
  if !r.alwaysIrr && inRanges ranges i then .byName else m

/-- The number of arguments of an application spine. -/
def spineLength : Term → Nat
  | .app f _ _ _ => spineLength f + 1
  | _ => 0

/-- The head of an application spine. -/
def spineHead : Term → Term
  | .app f _ _ _ => spineHead f
  | t => t

mutual

/-- Lazify the relevant positions of a term. -/
def term (p : Program) : Term → Term
  | .app f a m r =>
    let n := spineLength f + 1
    let ranges := byNameRanges p (spineHead f) n
    let i := n - 1
    .app (spine p ranges (i - 1) f) (if r.alwaysIrr then a else term p a) (newMode ranges i m r) r
  | .lam b d t => .lam b d (term p t)
  | .letE c r ty v b => .letE c r ty (if r.alwaysIrr then v else term p v) (term p b)
  | .proj s i e => .proj s i (term p e)
  | t => t
termination_by structural t => t

/-- Rebuild the rest of a spine whose outermost remaining argument has
index `i`; its head is lazified as `term` does it. -/
def spine (p : Program) (ranges : List (Nat × Nat)) (i : Nat) : Term → Term
  | .app f a m r =>
    .app (spine p ranges (i - 1) f) (if r.alwaysIrr then a else term p a)
      (newMode ranges i m r) r
  | .lam b d t => .lam b d (term p t)
  | .letE c r ty v b => .letE c r ty (if r.alwaysIrr then v else term p v) (term p b)
  | .proj s i e => .proj s i (term p e)
  | t => t
termination_by structural t => t

end

/-- Mark the IH arguments of a rule's minor application `byName`. -/
def ihs (np nmot nmin : Nat) (rule : Rule) : Rule :=
  let total := np + nmot + nmin + rule.fields
  let (binders, body) := rule.rhs.lams
  if binders.length != total then rule else
  let (head, args) := body.spine
  let args := args.mapIdx fun i (a, m, r) =>
    (a, (if i ≥ rule.fields && !r.alwaysIrr then Mode.byName else m), r)
  let body := Term.mkApps head args
  { rule with rhs := binders.foldr (fun (b, d) acc => .lam b d acc) body }

/-- Lazify one runtime term. -/
def step (p : Program) (key : TermKey) : Program :=
  match key with
  | .rule r j =>
    match p.decl? r with
    | some (.recr _ _ _ np nmot nmin _ _ rules _) =>
      match rules[j]? with
      | some rule => p.setTerm key (term p (ihs np nmot nmin rule).rhs)
      | none => p
    | _ => p
  | _ =>
    match p.termOf key with
    | some t => p.setTerm key (term p t)
    | none => p

/-- Lazify the given runtime terms, in order (structural on the list). -/
def run (p : Program) : List TermKey → Program
  | [] => p
  | key :: keys => run (step p key) keys

/-! ## Preservation properties -/

theorem univ_beq_refl : ∀ u : Ixon.Univ, (u == u) = true
  | .zero => rfl
  | .succ u => univ_beq_refl u
  | .max a b => by show (a == a && b == b) = true; rw [univ_beq_refl a, univ_beq_refl b]; rfl
  | .imax a b => by show (a == a && b == b) = true; rw [univ_beq_refl a, univ_beq_refl b]; rfl
  | .var i => show (i == i) = true from BEq.rfl

instance : ReflBEq Ixon.Univ := ⟨fun {u} => univ_beq_refl u⟩

theorem _root_.IxCC.Src.Term.eqv_refl : ∀ t : Term, t.eqv t = true
  | .var _ => BEq.rfl
  | .sort u => univ_beq_refl u
  | .const _ us => by simp [Term.eqv]
  | .app f a _ _ => by simp [Term.eqv, Term.eqv_refl f, Term.eqv_refl a]
  | .lam _ d t => by simp [Term.eqv, Term.eqv_refl d, Term.eqv_refl t]
  | .pi _ _ d t => by simp [Term.eqv, Term.eqv_refl d, Term.eqv_refl t]
  | .letE _ _ t v b => by simp [Term.eqv, Term.eqv_refl t, Term.eqv_refl v, Term.eqv_refl b]
  | .proj _ _ e => by simp [Term.eqv, Term.eqv_refl e]
  | .natLit _ => BEq.rfl
  | .strLit _ => BEq.rfl

mutual

theorem term_eqv (p : Program) : ∀ t : Term, (term p t).eqv t = true
  | .app f a m r => by
    unfold term
    dsimp only [Term.eqv]
    rw [spine_eqv p _ f _]
    cases r.alwaysIrr <;> simp [Term.eqv_refl a, term_eqv p a]
  | .lam b d t => by
    unfold term
    simp [Term.eqv, Term.eqv_refl d, term_eqv p t]
  | .letE c r ty v b => by
    unfold term
    dsimp only [Term.eqv]
    rw [Term.eqv_refl ty, term_eqv p b]
    cases r.alwaysIrr <;> simp [Term.eqv_refl v, term_eqv p v]
  | .proj s i e => by
    unfold term
    simp [Term.eqv, term_eqv p e]
  | .var i => Term.eqv_refl (.var i)
  | .sort u => Term.eqv_refl (.sort u)
  | .const c us => Term.eqv_refl (.const c us)
  | .pi b r d t => Term.eqv_refl (.pi b r d t)
  | .natLit n => Term.eqv_refl (.natLit n)
  | .strLit s => Term.eqv_refl (.strLit s)
termination_by structural t => t

theorem spine_eqv (p : Program) (ranges : List (Nat × Nat)) :
    ∀ (t : Term) (i : Nat), (spine p ranges i t).eqv t = true
  | .app f a m r, i => by
    unfold spine
    dsimp only [Term.eqv]
    rw [spine_eqv p ranges f (i - 1)]
    cases r.alwaysIrr <;> simp [Term.eqv_refl a, term_eqv p a]
  | .lam b d t, _ => by
    unfold spine
    simp [Term.eqv, Term.eqv_refl d, term_eqv p t]
  | .letE c r ty v b, _ => by
    unfold spine
    dsimp only [Term.eqv]
    rw [Term.eqv_refl ty, term_eqv p b]
    cases r.alwaysIrr <;> simp [Term.eqv_refl v, term_eqv p v]
  | .proj s j e, _ => by
    unfold spine
    simp [Term.eqv, term_eqv p e]
  | .var j, _ => Term.eqv_refl (.var j)
  | .sort u, _ => Term.eqv_refl (.sort u)
  | .const c us, _ => Term.eqv_refl (.const c us)
  | .pi b r d t, _ => Term.eqv_refl (.pi b r d t)
  | .natLit n, _ => Term.eqv_refl (.natLit n)
  | .strLit s, _ => Term.eqv_refl (.strLit s)
termination_by structural t => t

end

/-- One lazified term is `Term.eqv` (the table checks' equality, which ignores
modes, relevance tags, binders and contracts) to the original. The exact
statement, that only application modes change, and its lift to `Lazify.run`
are `term_modeEq` and `run_modeEq` in `IxCC.Src.Proof.Lazify`. -/
theorem lazifyTerm_eqv (p : Program) (t : Term) : (term p t).eqv t = true :=
  term_eqv p t

theorem _root_.IxCC.Src.Program.setTerm_size (p : Program) (key : TermKey) (t : Term) :
    (p.setTerm key t).size = p.size := by
  unfold Program.setTerm
  split <;> try split
  all_goals try split
  all_goals try split
  all_goals rfl

theorem _root_.IxCC.Src.Program.setTerm_roots (p : Program) (key : TermKey) (t : Term) :
    (p.setTerm key t).roots = p.roots := by
  unfold Program.setTerm
  split <;> try split
  all_goals try split
  all_goals try split
  all_goals rfl

theorem _root_.IxCC.Src.Program.setTerm_table_recKind (p : Program) (key : TermKey) (t : Term) :
    (p.setTerm key t).table.recKind = p.table.recKind := by
  unfold Program.setTerm
  split <;> try split
  all_goals try split
  all_goals try split
  all_goals rfl

theorem step_size (p : Program) (key : TermKey) : (step p key).size = p.size := by
  unfold step
  split <;> try split
  all_goals try split
  all_goals first | rfl | exact p.setTerm_size _ _

theorem step_roots (p : Program) (key : TermKey) : (step p key).roots = p.roots := by
  unfold step
  split <;> try split
  all_goals try split
  all_goals first | rfl | exact p.setTerm_roots _ _

theorem step_table_recKind (p : Program) (key : TermKey) :
    (step p key).table.recKind = p.table.recKind := by
  unfold step
  split <;> try split
  all_goals try split
  all_goals first | rfl | exact p.setTerm_table_recKind _ _

theorem run_size (p : Program) : ∀ keys : List TermKey, (run p keys).size = p.size
  | [] => rfl
  | key :: keys => (run_size (step p key) keys).trans (step_size p key)

theorem run_roots (p : Program) : ∀ keys : List TermKey, (run p keys).roots = p.roots
  | [] => rfl
  | key :: keys => (run_roots (step p key) keys).trans (step_roots p key)

theorem run_table_recKind (p : Program) :
    ∀ keys : List TermKey, (run p keys).table.recKind = p.table.recKind
  | [] => rfl
  | key :: keys => (run_table_recKind (step p key) keys).trans (step_table_recKind p key)

end IxCC.Src.Lazify
