import IxCC.Lam.Syntax

/-! # Lam well-formedness

`Lam.WellFormed P`, decided by `wellFormed` with an
iff lemma: every global `0 … size - 1` is present and closed; variables are
in scope; `glob` ids are in range; `con` arities, `case` alternative
arities and `proj` indices come from the constructor table (the pinned `Nat`
keys included, so `Nat` peeling meets alternatives of arity 0 and 1);
primitives are saturated; the keys of a `case` are distinct; global keys and
constructor-table keys are pairwise distinct (D19); roots are in range. -/

namespace IxCC.Lam

/-- What well-formedness reads from a program: the global count and the
constructor table's arities. -/
structure Sig where
  size : Nat
  arity? : Key.CtorKey → Option Nat

def Program.sig (P : Program) : Sig :=
  { size := P.size, arity? := fun c => (P.ctor? c).map (·.arity) }

namespace Term

mutual

/-- Scope and shape of a term under `d` binders. -/
def wf (S : Sig) (d : Nat) : Term → Bool
  | .var i => decide (i < d)
  | .glob g => decide (g < S.size)
  | .lam _ _ b => wf S (d + 1) b
  | .app f a _ => wf S d f && wf S d a
  | .letE _ v b => wf S d v && wf S (d + 1) b
  | .con c fs => decide (S.arity? c = some fs.length) && wfList S d fs
  | .case s alts dflt =>
    wf S d s && wfAlts S d alts && decide (altKeys alts).Nodup && wfOpt S d dflt
  | .proj c i s => decide (∃ n, S.arity? c = some n ∧ i < n) && wf S d s
  | .lit _ | .box | .trap => true
  | .prim p args => decide (args.length = p.arity) && wfList S d args
  | .tick t => wf S d t

def wfList (S : Sig) (d : Nat) : List Term → Bool
  | [] => true
  | t :: ts => wf S d t && wfList S d ts

def wfAlts (S : Sig) (d : Nat) : List Alt → Bool
  | [] => true
  | .mk key n b :: as => decide (S.arity? key = some n) && wf S (d + n) b && wfAlts S d as

def wfOpt (S : Sig) (d : Nat) : Option Term → Bool
  | none => true
  | some t => wf S d t

/-- The keys of a list of alternatives. -/
def altKeys : List Alt → List Key.CtorKey
  | [] => []
  | .mk key _ _ :: as => key :: altKeys as

end

mutual

/-- The same, as a proposition. -/
def WF (S : Sig) (d : Nat) : Term → Prop
  | .var i => i < d
  | .glob g => g < S.size
  | .lam _ _ b => WF S (d + 1) b
  | .app f a _ => WF S d f ∧ WF S d a
  | .letE _ v b => WF S d v ∧ WF S (d + 1) b
  | .con c fs => S.arity? c = some fs.length ∧ WFList S d fs
  | .case s alts dflt => WF S d s ∧ WFAlts S d alts ∧ (altKeys alts).Nodup ∧ WFOpt S d dflt
  | .proj c i s => (∃ n, S.arity? c = some n ∧ i < n) ∧ WF S d s
  | .lit _ | .box | .trap => True
  | .prim p args => args.length = p.arity ∧ WFList S d args
  | .tick t => WF S d t

def WFList (S : Sig) (d : Nat) : List Term → Prop
  | [] => True
  | t :: ts => WF S d t ∧ WFList S d ts

def WFAlts (S : Sig) (d : Nat) : List Alt → Prop
  | [] => True
  | .mk key n b :: as => S.arity? key = some n ∧ WF S (d + n) b ∧ WFAlts S d as

def WFOpt (S : Sig) (d : Nat) : Option Term → Prop
  | none => True
  | some t => WF S d t

end

mutual

theorem wf_iff (S : Sig) : ∀ (d : Nat) (t : Term), wf S d t = true ↔ WF S d t
  | d, .var i => by simp [wf, WF]
  | d, .glob g => by simp [wf, WF]
  | d, .lam _ _ b => by simp only [wf, WF]; exact wf_iff S (d + 1) b
  | d, .app f a _ => by simp [wf, WF, wf_iff S d f, wf_iff S d a]
  | d, .letE _ v b => by simp [wf, WF, wf_iff S d v, wf_iff S (d + 1) b]
  | d, .con c fs => by simp [wf, WF, wfList_iff S d fs]
  | d, .case s alts dflt => by
    simp [wf, WF, wf_iff S d s, wfAlts_iff S d alts, wfOpt_iff S d dflt, and_assoc]
  | d, .proj c i s => by simp [wf, WF, wf_iff S d s]
  | d, .lit _ => by simp [wf, WF]
  | d, .box => by simp [wf, WF]
  | d, .trap => by simp [wf, WF]
  | d, .prim p args => by simp [wf, WF, wfList_iff S d args]
  | d, .tick t => by simp only [wf, WF]; exact wf_iff S d t

theorem wfList_iff (S : Sig) : ∀ (d : Nat) (ts : List Term), wfList S d ts = true ↔ WFList S d ts
  | _, [] => by simp [wfList, WFList]
  | d, t :: ts => by simp [wfList, WFList, wf_iff S d t, wfList_iff S d ts]

theorem wfAlts_iff (S : Sig) : ∀ (d : Nat) (as : List Alt), wfAlts S d as = true ↔ WFAlts S d as
  | _, [] => by simp [wfAlts, WFAlts]
  | d, .mk key n b :: as => by
    simp [wfAlts, WFAlts, wf_iff S (d + n) b, wfAlts_iff S d as, and_assoc]

theorem wfOpt_iff (S : Sig) : ∀ (d : Nat) (t : Option Term), wfOpt S d t = true ↔ WFOpt S d t
  | _, none => by simp [wfOpt, WFOpt]
  | d, some t => by simp only [wfOpt, WFOpt]; exact wf_iff S d t

end

end Term

/-- The pinned keys have the arities `Nat` peeling and Boolean primitives
produce, wherever the table lists them. -/
def Known.consistent (K : Known) (S : Sig) : Bool :=
  let ok := fun (c : Option Key.CtorKey) (n : Nat) => match c with
    | some c => (S.arity? c).all (· == n)
    | none => true
  ok K.natZero 0 && ok K.natSucc 1 && ok K.boolFalse 0 && ok K.boolTrue 0

/-- Decide well-formedness. -/
def wellFormed (P : Program) : Bool :=
  (List.range P.size).all (fun g => match P.global? g with
    | some gl => gl.body.wf P.sig 0
    | none => false) &&
  decide ((P.globalList.map (·.2.key)).Nodup) &&
  decide ((P.ctors.map (·.key)).Nodup) &&
  P.roots.all (· < P.size) &&
  P.known.consistent P.sig

structure WellFormed (P : Program) : Prop where
  globals : ∀ g, g < P.size → ∃ gl, P.global? g = some gl ∧ gl.body.WF P.sig 0
  keys : (P.globalList.map (·.2.key)).Nodup
  ctorKeys : (P.ctors.map (·.key)).Nodup
  roots : ∀ r ∈ P.roots, r < P.size
  known : P.known.consistent P.sig = true

theorem wellFormed_iff (P : Program) : wellFormed P = true ↔ WellFormed P := by
  constructor
  · intro h
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hg, hk⟩, hc⟩, hr⟩, hkn⟩ := h
    refine ⟨fun g hlt => ?_, hk, hc, fun r hr' => by simpa using hr r hr', hkn⟩
    have := hg g hlt
    split at this
    · next gl hgl => exact ⟨gl, hgl, (Term.wf_iff _ _ _).mp this⟩
    · cases this
  · intro ⟨hg, hk, hc, hr, hkn⟩
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨fun g hlt => ?_, hk⟩, hc⟩, fun r hr' => by simpa using hr r hr'⟩, hkn⟩
    obtain ⟨gl, hgl, hwf⟩ := hg g hlt
    simp [hgl, (Term.wf_iff _ _ _).mpr hwf]

instance (P : Program) : Decidable (WellFormed P) :=
  decidable_of_iff _ (wellFormed_iff P)

/-- The first global that is missing or not closed, for diagnostics. -/
def firstIllFormed (P : Program) : Option GlobalId :=
  (List.range P.size).find? fun g => match P.global? g with
    | some gl => !gl.body.wf P.sig 0
    | none => true

end IxCC.Lam
