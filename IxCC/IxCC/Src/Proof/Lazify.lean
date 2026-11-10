import IxCC.Src.Lazify
import IxCC.Src.Proof.NatMap

/-! # What `Src.Lazify` changes: only application modes

`Lazify.run` rewrites the runtime terms it is given: a definition's value or
an `eqn` body through `Lazify.term`, and a recursor rule's right-hand side
through `Lazify.ihs` and then `Lazify.term`. This module proves that it
changes nothing but the `Mode` of application nodes:

- `Term.ModeEq t u`: `t` and `u` are the same term except, possibly, for the
  `Mode` of their application nodes;
- `Program.ModeEq p q`: `p` and `q` have the same size, roots, pins, resource
  bindings, `recKind`, `lazy`, `inline` and opaque tables, the same constants
  (identity, address and declaration), except that a definition's value, a
  recursor rule's right-hand side and an `eqn` body may differ by
  `Term.ModeEq`;
- `Lazify.run_modeEq`: `Program.ModeEq p (Lazify.run p keys)` for every `p`
  and every key list, through `term_modeEq`, `spine_modeEq`, `ihs_modeEq` and
  `step_modeEq`; `Lazify.run_termOf` restates it per runtime term.

This is a syntactic fact. That lazification preserves the meaning of the
program under SrcEval is not proved here or anywhere else: it is part of the
open item S6 (the front end's stages are outside the proof chain). -/

set_option autoImplicit false

namespace IxCC.Src

open IxCC.Ixon

namespace Term

/-- `ModeEq t u`: `t` and `u` are the same term except, possibly, for the
evaluation `Mode` of their application nodes. Everything else must be equal:
variables, sorts, constants with their universe arguments, binders (written
contract, relevance tag and `propWhen`), Π result contracts, `let` contracts
and relevance tags, the relevance tag of every argument, projections and
literals. Unlike `Term.eqv` (the table checks' equality), it compares tags,
binders and contracts. -/
inductive ModeEq : Term → Term → Prop
  | var (i : Nat) : ModeEq (.var i) (.var i)
  | sort (u : Univ) : ModeEq (.sort u) (.sort u)
  | const (c : CId) (us : List Univ) : ModeEq (.const c us) (.const c us)
  | app {f g a b : Term} (m m' : Mode) (r : Rel) :
      ModeEq f g → ModeEq a b → ModeEq (.app f a m r) (.app g b m' r)
  | lam (bd : Binder) {d d' t t' : Term} :
      ModeEq d d' → ModeEq t t' → ModeEq (.lam bd d t) (.lam bd d' t')
  | pi (bd : Binder) (res : V3.ValueContract) {d d' t t' : Term} :
      ModeEq d d' → ModeEq t t' → ModeEq (.pi bd res d t) (.pi bd res d' t')
  | letE (c : V3.LetContract) (r : Rel) {ty ty' v v' b b' : Term} :
      ModeEq ty ty' → ModeEq v v' → ModeEq b b' →
      ModeEq (.letE c r ty v b) (.letE c r ty' v' b')
  | proj (s : CId) (i : Nat) {e e' : Term} : ModeEq e e' → ModeEq (.proj s i e) (.proj s i e')
  | natLit (n : Nat) : ModeEq (.natLit n) (.natLit n)
  | strLit (s : String) : ModeEq (.strLit s) (.strLit s)

theorem ModeEq.refl : ∀ t : Term, ModeEq t t
  | .var i => .var i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a m r => .app m m r (ModeEq.refl f) (ModeEq.refl a)
  | .lam b d t => .lam b (ModeEq.refl d) (ModeEq.refl t)
  | .pi b r d t => .pi b r (ModeEq.refl d) (ModeEq.refl t)
  | .letE c r t v b => .letE c r (ModeEq.refl t) (ModeEq.refl v) (ModeEq.refl b)
  | .proj s i e => .proj s i (ModeEq.refl e)
  | .natLit n => .natLit n
  | .strLit s => .strLit s

theorem ModeEq.trans {t u v : Term} (h₁ : ModeEq t u) (h₂ : ModeEq u v) : ModeEq t v := by
  induction h₁ generalizing v with
  | var => exact h₂
  | sort => exact h₂
  | const => exact h₂
  | app m m' r _ _ ihf iha =>
    cases h₂ with
    | app _ m'' _ hf ha => exact .app m m'' r (ihf hf) (iha ha)
  | lam bd _ _ ihd iht =>
    cases h₂ with
    | lam _ hd ht => exact .lam bd (ihd hd) (iht ht)
  | pi bd res _ _ ihd iht =>
    cases h₂ with
    | pi _ _ hd ht => exact .pi bd res (ihd hd) (iht ht)
  | letE c r _ _ _ ihty ihv ihb =>
    cases h₂ with
    | letE _ _ hty hv hb => exact .letE c r (ihty hty) (ihv hv) (ihb hb)
  | proj s i _ ihe =>
    cases h₂ with
    | proj _ _ he => exact .proj s i (ihe he)
  | natLit => exact h₂
  | strLit => exact h₂

/-- `mkApps` of `ModeEq` heads over argument lists with the same terms and
relevance tags (modes may differ). -/
theorem mkApps_modeEq :
    ∀ (args args' : List Arg) {h h' : Term}, ModeEq h h' →
      args.map (fun x => (x.1, x.2.2)) = args'.map (fun x => (x.1, x.2.2)) →
      ModeEq (mkApps h args) (mkApps h' args')
  | [], [], _, _, hh, _ => hh
  | [], _ :: _, _, _, _, he => by simp at he
  | _ :: _, [], _, _, _, he => by simp at he
  | (a, m, r) :: as, (a', m', r') :: as', h, h', hh, he => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, hrest⟩ := he
    exact mkApps_modeEq as as' (.app m m' r hh (ModeEq.refl a)) hrest

/-- Re-wrapping a λ-telescope over `ModeEq` bodies. -/
theorem foldrLam_modeEq :
    ∀ (bs : List (Binder × Term)) {b b' : Term}, ModeEq b b' →
      ModeEq (bs.foldr (fun (bd, d) acc => .lam bd d acc) b)
        (bs.foldr (fun (bd, d) acc => .lam bd d acc) b')
  | [], _, _, h => h
  | (bd, d) :: bs, _, _, h => .lam bd (ModeEq.refl d) (foldrLam_modeEq bs h)

theorem lams_foldr : ∀ t : Term, t.lams.1.foldr (fun (bd, d) acc => .lam bd d acc) t.lams.2 = t
  | .lam b d t => by simp only [lams, List.foldr_cons]; rw [lams_foldr t]
  | .var _ | .sort _ | .const .. | .app .. | .pi .. | .letE .. | .proj .. | .natLit _
  | .strLit _ => rfl

theorem spine_go_mkApps : ∀ (t : Term) (acc : List Arg),
    mkApps (spine.go t acc).1 (spine.go t acc).2 = mkApps t acc
  | .app f a m r, acc => by
    simp only [spine.go]
    rw [spine_go_mkApps f _]
    rfl
  | .var _, _ | .sort _, _ | .const .., _ | .lam .., _ | .pi .., _ | .letE .., _ | .proj .., _
  | .natLit _, _ | .strLit _, _ => rfl

theorem spine_mkApps (t : Term) : mkApps t.spine.1 t.spine.2 = t :=
  spine_go_mkApps t []

end Term

/-! ## Declarations and programs up to modes -/

/-- Two recursor rule lists that differ at most in the modes of their
right-hand sides. -/
def RulesModeEq (rs rs' : List Rule) : Prop :=
  rs.length = rs'.length ∧
    ∀ (j : Nat) (r r' : Rule), rs[j]? = some r → rs'[j]? = some r' →
      r.ctor = r'.ctor ∧ r.fields = r'.fields ∧ Term.ModeEq r.rhs r'.rhs

/-- Two declarations that differ at most in the modes of their runtime terms
(a definition's value, a recursor's rule right-hand sides). -/
inductive Decl.ModeEq : Decl → Decl → Prop
  | refl (d : Decl) : Decl.ModeEq d d
  | defn (kind : DefKind) (safety : DefinitionSafety) (lvls : Nat) (type : Term) {v v' : Term} :
      Term.ModeEq v v' → Decl.ModeEq (.defn kind safety lvls type v) (.defn kind safety lvls type v')
  | recr (safe k : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (type : Term)
      {rules rules' : List Rule} : RulesModeEq rules rules' →
      Decl.ModeEq (.recr safe k lvls np nmot nmin ni ind rules type)
        (.recr safe k lvls np nmot nmin ni ind rules' type)

/-- Two optional constant entries with the same identity and address whose
declarations differ at most in modes. -/
def EntryModeEq : Option ConstEntry → Option ConstEntry → Prop
  | some e, some e' => e.ref = e'.ref ∧ e.addr = e'.addr ∧ Decl.ModeEq e.decl e'.decl
  | none, none => True
  | _, _ => False

/-- Two optional table resolutions that are equal, or are `eqn` entries of
the same theorem whose bodies differ at most in modes. -/
inductive ResolveModeEq : Option Resolve → Option Resolve → Prop
  | refl (r : Option Resolve) : ResolveModeEq r r
  | eqn (thm : CId) {b b' : Term} :
      Term.ModeEq b b' → ResolveModeEq (some (.eqn thm b)) (some (.eqn thm b'))

/-- `p` and `q` are the same program except, possibly, for the modes of
application nodes inside definition values, recursor rule right-hand sides
and `eqn` bodies. -/
structure Program.ModeEq (p q : Program) : Prop where
  size : p.size = q.size
  roots : p.roots = q.roots
  known : p.known = q.known
  resource : p.resource = q.resource
  recKind : p.table.recKind = q.table.recKind
  lazy : p.table.lazy = q.table.lazy
  inline : p.table.inline = q.table.inline
  opaqueByValue : p.table.opaqueByValue = q.table.opaqueByValue
  resolve : ∀ c, ResolveModeEq (p.table.resolveOf c) (q.table.resolveOf c)
  entry : ∀ c, EntryModeEq (p.entry? c) (q.entry? c)

theorem RulesModeEq.refl (rs : List Rule) : RulesModeEq rs rs :=
  ⟨rfl, fun _ r r' h h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl, Term.ModeEq.refl _⟩⟩

theorem RulesModeEq.trans {rs rs' rs'' : List Rule} (h₁ : RulesModeEq rs rs')
    (h₂ : RulesModeEq rs' rs'') : RulesModeEq rs rs'' := by
  refine ⟨h₁.1.trans h₂.1, fun j r r'' hr hr'' => ?_⟩
  have hlen := h₁.1
  have hj : j < rs'.length := by
    have := (List.getElem?_eq_some_iff.1 hr).1
    omega
  obtain ⟨c₁, f₁, m₁⟩ := h₁.2 j r rs'[j] hr (List.getElem?_eq_getElem hj)
  obtain ⟨c₂, f₂, m₂⟩ := h₂.2 j rs'[j] r'' (List.getElem?_eq_getElem hj) hr''
  exact ⟨c₁.trans c₂, f₁.trans f₂, m₁.trans m₂⟩

theorem Decl.ModeEq.trans {d d' d'' : Decl} (h₁ : Decl.ModeEq d d') (h₂ : Decl.ModeEq d' d'') :
    Decl.ModeEq d d'' := by
  cases h₁ with
  | refl => exact h₂
  | defn kind safety lvls type hv =>
    cases h₂ with
    | refl => exact .defn kind safety lvls type hv
    | defn _ _ _ _ hv' => exact .defn kind safety lvls type (hv.trans hv')
  | recr safe k lvls np nmot nmin ni ind type hr =>
    cases h₂ with
    | refl => exact .recr safe k lvls np nmot nmin ni ind type hr
    | recr _ _ _ _ _ _ _ _ _ hr' => exact .recr safe k lvls np nmot nmin ni ind type (hr.trans hr')

theorem EntryModeEq.refl : ∀ e : Option ConstEntry, EntryModeEq e e
  | some _ => ⟨rfl, rfl, .refl _⟩
  | none => trivial

theorem EntryModeEq.trans : ∀ {e e' e'' : Option ConstEntry},
    EntryModeEq e e' → EntryModeEq e' e'' → EntryModeEq e e''
  | some _, some _, some _, ⟨r₁, a₁, d₁⟩, ⟨r₂, a₂, d₂⟩ => ⟨r₁.trans r₂, a₁.trans a₂, d₁.trans d₂⟩
  | none, none, none, _, _ => trivial
  | some _, none, _, h, _ => h.elim
  | none, some _, _, h, _ => h.elim
  | some _, some _, none, _, h => h.elim
  | none, none, some _, _, h => h.elim

theorem ResolveModeEq.trans {r r' r'' : Option Resolve} (h₁ : ResolveModeEq r r')
    (h₂ : ResolveModeEq r' r'') : ResolveModeEq r r'' := by
  cases h₁ with
  | refl => exact h₂
  | eqn thm hb =>
    cases h₂ with
    | refl => exact .eqn thm hb
    | eqn _ hb' => exact .eqn thm (hb.trans hb')

theorem Program.ModeEq.refl (p : Program) : Program.ModeEq p p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => .refl _, fun _ => EntryModeEq.refl _⟩

theorem Program.ModeEq.trans {p q r : Program} (h₁ : Program.ModeEq p q)
    (h₂ : Program.ModeEq q r) : Program.ModeEq p r :=
  ⟨h₁.size.trans h₂.size, h₁.roots.trans h₂.roots, h₁.known.trans h₂.known,
    h₁.resource.trans h₂.resource, h₁.recKind.trans h₂.recKind, h₁.lazy.trans h₂.lazy,
    h₁.inline.trans h₂.inline, h₁.opaqueByValue.trans h₂.opaqueByValue,
    fun c => (h₁.resolve c).trans (h₂.resolve c), fun c => (h₁.entry c).trans (h₂.entry c)⟩

/-- Every runtime term of `p` has a counterpart in `q` that differs at most in
modes. -/
theorem Program.ModeEq.termOf {p q : Program} (h : Program.ModeEq p q) {key : TermKey} {t : Term}
    (ht : p.termOf key = some t) : ∃ t', q.termOf key = some t' ∧ Term.ModeEq t t' := by
  cases key with
  | value c =>
    have he := h.entry c
    simp only [Program.termOf, Program.decl?] at ht ⊢
    cases hp : p.entry? c with
    | none => rw [hp] at ht; cases ht
    | some e =>
      rw [hp] at he ht
      cases hq : q.entry? c with
      | none => rw [hq] at he; exact he.elim
      | some e' =>
        rw [hq] at he
        obtain ⟨_, _, hd⟩ := he
        simp only [Option.map_some] at ht ⊢
        generalize e.decl = d at hd ht
        generalize e'.decl = d' at hd ⊢
        cases hd with
        | refl => exact ⟨t, ht, Term.ModeEq.refl t⟩
        | defn kind safety lvls type hv =>
          rename_i v v'
          simp only [Option.some.injEq] at ht
          subst ht
          exact ⟨v', rfl, hv⟩
        | recr => simp at ht
  | eqn c =>
    have hr := h.resolve c
    simp only [Program.termOf] at ht ⊢
    generalize p.table.resolveOf c = rp at hr ht
    generalize q.table.resolveOf c = rq at hr ⊢
    cases hr with
    | refl r => exact ⟨t, ht, Term.ModeEq.refl t⟩
    | eqn thm hb =>
      rename_i b b'
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨b', rfl, hb⟩
  | rule r j =>
    have he := h.entry r
    simp only [Program.termOf, Program.decl?] at ht ⊢
    cases hp : p.entry? r with
    | none => rw [hp] at ht; cases ht
    | some e =>
      rw [hp] at he ht
      cases hq : q.entry? r with
      | none => rw [hq] at he; exact he.elim
      | some e' =>
        rw [hq] at he
        obtain ⟨_, _, hd⟩ := he
        simp only [Option.map_some] at ht ⊢
        generalize e.decl = d at hd ht
        generalize e'.decl = d' at hd ⊢
        cases hd with
        | refl => exact ⟨t, ht, Term.ModeEq.refl t⟩
        | defn => simp at ht
        | recr safe k lvls np nmot nmin ni ind type hrs =>
          rename_i rules rules'
          simp only at ht ⊢
          cases hj : rules[j]? with
          | none => rw [hj] at ht; cases ht
          | some rule =>
            rw [hj, Option.map_some, Option.some.injEq] at ht
            subst ht
            have hlt : j < rules'.length := by
              have := (List.getElem?_eq_some_iff.1 hj).1
              have := hrs.1
              omega
            obtain ⟨_, _, hm⟩ := hrs.2 j rule rules'[j] hj (List.getElem?_eq_getElem hlt)
            exact ⟨rules'[j].rhs, by rw [List.getElem?_eq_getElem hlt]; rfl, hm⟩

theorem rulesSet_modeEq {rules : List Rule} {j : Nat} {rule : Rule} (hj : rules[j]? = some rule)
    {t : Term} (hm : Term.ModeEq rule.rhs t) :
    RulesModeEq rules (rules.set j { rule with rhs := t }) := by
  refine ⟨(List.length_set ..).symm, fun i r r' hr hr' => ?_⟩
  by_cases hij : j = i
  · subst hij
    rw [hj, Option.some.injEq] at hr
    subst hr
    have hlt : j < rules.length := (List.getElem?_eq_some_iff.1 hj).1
    rw [List.getElem?_set_self hlt, Option.some.injEq] at hr'
    subst hr'
    exact ⟨rfl, rfl, hm⟩
  · rw [List.getElem?_set_ne hij, hr, Option.some.injEq] at hr'
    subst hr'
    exact ⟨rfl, rfl, Term.ModeEq.refl _⟩

namespace Lazify

mutual

theorem term_modeEq (p : Program) : ∀ t : Term, Term.ModeEq t (term p t)
  | .app f a m r => by
    unfold term
    dsimp only
    refine .app _ _ r (spine_modeEq p _ f _) ?_
    split
    · exact Term.ModeEq.refl a
    · exact term_modeEq p a
  | .lam b d t => by
    unfold term
    exact .lam b (Term.ModeEq.refl d) (term_modeEq p t)
  | .letE c r ty v b => by
    unfold term
    refine .letE c r (Term.ModeEq.refl ty) ?_ (term_modeEq p b)
    split
    · exact Term.ModeEq.refl v
    · exact term_modeEq p v
  | .proj s i e => by
    unfold term
    exact .proj s i (term_modeEq p e)
  | .var i => Term.ModeEq.refl (.var i)
  | .sort u => Term.ModeEq.refl (.sort u)
  | .const c us => Term.ModeEq.refl (.const c us)
  | .pi b r d t => Term.ModeEq.refl (.pi b r d t)
  | .natLit n => Term.ModeEq.refl (.natLit n)
  | .strLit s => Term.ModeEq.refl (.strLit s)
termination_by structural t => t

theorem spine_modeEq (p : Program) (ranges : List (Nat × Nat)) :
    ∀ (t : Term) (i : Nat), Term.ModeEq t (spine p ranges i t)
  | .app f a m r, i => by
    unfold spine
    refine .app _ _ r (spine_modeEq p ranges f (i - 1)) ?_
    split
    · exact Term.ModeEq.refl a
    · exact term_modeEq p a
  | .lam b d t, _ => by
    unfold spine
    exact .lam b (Term.ModeEq.refl d) (term_modeEq p t)
  | .letE c r ty v b, _ => by
    unfold spine
    refine .letE c r (Term.ModeEq.refl ty) ?_ (term_modeEq p b)
    split
    · exact Term.ModeEq.refl v
    · exact term_modeEq p v
  | .proj s j e, _ => by
    unfold spine
    exact .proj s j (term_modeEq p e)
  | .var j, _ => Term.ModeEq.refl (.var j)
  | .sort u, _ => Term.ModeEq.refl (.sort u)
  | .const c us, _ => Term.ModeEq.refl (.const c us)
  | .pi b r d t, _ => Term.ModeEq.refl (.pi b r d t)
  | .natLit n, _ => Term.ModeEq.refl (.natLit n)
  | .strLit s, _ => Term.ModeEq.refl (.strLit s)
termination_by structural t => t

end

theorem map_mapIdx_proj {args : List Term.Arg} {g : Nat → Term.Arg → Term.Arg}
    (hg₁ : ∀ i x, (g i x).1 = x.1) (hg₂ : ∀ i x, (g i x).2.2 = x.2.2) :
    (args.mapIdx g).map (fun x => (x.1, x.2.2)) = args.map (fun x => (x.1, x.2.2)) := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp [List.getElem_mapIdx, hg₁, hg₂]

/-- `ihs` keeps a rule's constructor and field count and changes only modes
in its right-hand side. -/
theorem ihs_modeEq (np nmot nmin : Nat) (rule : Rule) :
    (ihs np nmot nmin rule).ctor = rule.ctor ∧ (ihs np nmot nmin rule).fields = rule.fields ∧
      Term.ModeEq rule.rhs (ihs np nmot nmin rule).rhs := by
  unfold ihs
  have hl := Term.lams_foldr rule.rhs
  generalize rule.rhs.lams = pr at hl ⊢
  obtain ⟨binders, body⟩ := pr
  dsimp only at hl ⊢
  split
  · exact ⟨rfl, rfl, Term.ModeEq.refl _⟩
  · have hs := Term.spine_mkApps body
    generalize body.spine = q at hs ⊢
    obtain ⟨head, args⟩ := q
    dsimp only at hs ⊢
    refine ⟨rfl, rfl, ?_⟩
    rw [← hl, ← hs]
    apply Term.foldrLam_modeEq
    apply Term.mkApps_modeEq _ _ (Term.ModeEq.refl head)
    exact (map_mapIdx_proj (fun _ ⟨_, _, _⟩ => rfl) (fun _ ⟨_, _, _⟩ => rfl)).symm

/-- Replacing a runtime term by one that differs at most in modes. -/
theorem setTerm_modeEq (p : Program) (key : TermKey) (t : Term)
    (h : ∀ t₀, p.termOf key = some t₀ → Term.ModeEq t₀ t) :
    Program.ModeEq p (p.setTerm key t) := by
  cases key with
  | value c =>
    simp only [Program.setTerm]
    split
    · next e he =>
      split
      · next kind safety lvls type v hd =>
        have hv : Term.ModeEq v t :=
          h v (by simp [Program.termOf, Program.decl?, he, hd])
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => .refl _, fun c' => ?_⟩
        show EntryModeEq (p.consts.get? c') ((p.consts.insert c _).get? c')
        rw [NatMap.get?_insert]
        split
        · next hcc =>
          subst hcc
          have he' : p.consts.get? c' = some e := he
          rw [he']
          refine ⟨rfl, rfl, ?_⟩
          show Decl.ModeEq e.decl _
          rw [hd]
          exact .defn kind safety lvls type hv
        · exact EntryModeEq.refl _
      · exact .refl p
    · exact .refl p
  | eqn c =>
    simp only [Program.setTerm]
    split
    · next thm b hr =>
      have hb : Term.ModeEq b t := h b (by simp [Program.termOf, hr])
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun c' => ?_, fun _ => EntryModeEq.refl _⟩
      show ResolveModeEq (p.table.resolve.get? c') ((p.table.resolve.insert c (.eqn thm t)).get? c')
      rw [NatMap.get?_insert]
      split
      · next hcc =>
        subst hcc
        have hr' : p.table.resolve.get? c' = some (.eqn thm b) := hr
        rw [hr']
        exact .eqn thm hb
      · exact .refl _
    · exact .refl p
  | rule r j =>
    simp only [Program.setTerm]
    split
    · next e he =>
      split
      · next safe k lvls np nmot nmin ni ind rules type hd =>
        split
        · next rule hj =>
          have hm : Term.ModeEq rule.rhs t :=
            h rule.rhs (by simp [Program.termOf, Program.decl?, he, hd, hj])
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => .refl _, fun c' => ?_⟩
          show EntryModeEq (p.consts.get? c') ((p.consts.insert r _).get? c')
          rw [NatMap.get?_insert]
          split
          · next hcc =>
            subst hcc
            have he' : p.consts.get? c' = some e := he
            rw [he']
            refine ⟨rfl, rfl, ?_⟩
            show Decl.ModeEq e.decl _
            rw [hd]
            exact .recr safe k lvls np nmot nmin ni ind type (rulesSet_modeEq hj hm)
          · exact EntryModeEq.refl _
        · exact .refl p
      · exact .refl p
    · exact .refl p

/-- One `Lazify.step` changes only modes. -/
theorem step_modeEq (p : Program) (key : TermKey) : Program.ModeEq p (step p key) := by
  unfold step
  split
  · next r j =>
    split
    · next safe k lvls np nmot nmin ni ind rules type hd =>
      split
      · next rule hj =>
        apply setTerm_modeEq
        intro t₀ ht₀
        simp only [Program.termOf, hd, hj, Option.map_some, Option.some.injEq] at ht₀
        subst ht₀
        exact (ihs_modeEq np nmot nmin rule).2.2.trans (term_modeEq p _)
      · exact .refl p
    · exact .refl p
  · split
    · next t ht =>
      apply setTerm_modeEq
      intro t₀ ht₀
      rw [ht, Option.some.injEq] at ht₀
      subst ht₀
      exact term_modeEq p t
    · exact .refl p

/-- **`Lazify.run` changes only application modes.** For every program `p` and
key list, `Lazify.run p keys` is `p` up to the modes of application nodes in
definition values, recursor rule right-hand sides and `eqn` bodies
(`Program.ModeEq`). A syntactic fact: SrcEval preservation is not proved
(open item S6). -/
theorem run_modeEq (p : Program) : ∀ keys : List TermKey, Program.ModeEq p (run p keys)
  | [] => .refl p
  | key :: keys => (step_modeEq p key).trans (run_modeEq (step p key) keys)

/-- Per runtime term: every runtime term of `p` has a counterpart in
`Lazify.run p keys` that differs from it at most in application modes. -/
theorem run_termOf (p : Program) (keys : List TermKey) {key : TermKey} {t : Term}
    (ht : p.termOf key = some t) :
    ∃ t', (run p keys).termOf key = some t' ∧ Term.ModeEq t t' :=
  (run_modeEq p keys).termOf ht

end Lazify

end IxCC.Src
