module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Concretize

/-!
Progress proofs for `Concretize`: predicates characterizing the inputs on
which `typToConcrete` / `termToConcrete` succeed, plus the supporting
progress lemmas. Paired with `Proofs/ConcretizeSound.lean` which proves
semantic preservation.

Companion to `Ix/Aiur/Compiler/Concretize.lean`. Kept out of the
implementation file so the compiler passes can evolve without churn in
the proof layer.
-/

public section

namespace Aiur

open Source

/-- Structural predicate: `t` contains no `.mvar` anywhere. The only failure
mode of `typToConcrete` is hitting an `.mvar`, so under `MvarFree t` the
conversion succeeds. -/
inductive Typ.MvarFree : Typ → Prop
  | unit                       : Typ.MvarFree .unit
  | field                      : Typ.MvarFree .field
  | ref (g)                    : Typ.MvarFree (.ref g)
  | pointer {t}  (h : Typ.MvarFree t) : Typ.MvarFree (.pointer t)
  | array {t n}  (h : Typ.MvarFree t) : Typ.MvarFree (.array t n)
  | tuple {ts}   (h : ∀ t ∈ ts, Typ.MvarFree t) : Typ.MvarFree (.tuple ts)
  | app   {g as} (h : ∀ t ∈ as, Typ.MvarFree t) : Typ.MvarFree (.app g as)
  | function {ins out}
      (hi : ∀ t ∈ ins, Typ.MvarFree t)
      (ho : Typ.MvarFree out) : Typ.MvarFree (.function ins out)

/-- `typToConcrete` succeeds on every `MvarFree` type. The only failure
arm of `typToConcrete` is `.mvar`, which `MvarFree` excludes. -/
theorem typToConcrete_ok_of_mvarFree
    (mono : Std.HashMap (Global × Array Typ) Global)
    {t : Typ} (h : Typ.MvarFree t) :
    ∃ ct, typToConcrete mono t = .ok ct := by
  induction h with
  | unit => exact ⟨_, by unfold typToConcrete; rfl⟩
  | field => exact ⟨_, by unfold typToConcrete; rfl⟩
  | ref _ => exact ⟨_, by unfold typToConcrete; rfl⟩
  | pointer _ ih =>
      obtain ⟨_, hct⟩ := ih
      exact ⟨_, by unfold typToConcrete; rw [hct]; rfl⟩
  | array _ ih =>
      obtain ⟨_, hct⟩ := ih
      exact ⟨_, by unfold typToConcrete; rw [hct]; rfl⟩
  | @tuple ts _ ih =>
      have hlist : ∀ t ∈ ts.toList, ∃ ct, typToConcrete mono t = .ok ct :=
        fun t ht => ih t (Array.mem_toList_iff.mp ht)
      obtain ⟨ls, hls⟩ := List.mapM_except_ok hlist
      have hmap :
          ts.attach.mapM (m := Except ConcretizeError)
              (fun ⟨t, _⟩ => typToConcrete mono t) = .ok ls.toArray := by
        rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)]
        rw [Array.unattach_attach]
        rw [Array.mapM_eq_mapM_toList]
        rw [hls]
        rfl
      refine ⟨Concrete.Typ.tuple ls.toArray, ?_⟩
      unfold typToConcrete
      simp only [hmap, bind, Except.bind, pure, Except.pure]
  | @app g as _ =>
      unfold typToConcrete
      cases mono[(g, as)]? with
      | none =>
          exact ⟨Concrete.Typ.ref g, by simp only [pure, Except.pure]⟩
      | some concName =>
          exact ⟨Concrete.Typ.ref concName, by simp only [pure, Except.pure]⟩
  | @function ins out _ _ ihi iho =>
      obtain ⟨ls, hls⟩ := List.mapM_except_ok ihi
      obtain ⟨ct_out, hout⟩ := iho
      have hmap :
          ins.attach.mapM (m := Except ConcretizeError)
              (fun ⟨t, _⟩ => typToConcrete mono t) = .ok ls := by
        rw [List.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)]
        rw [List.unattach_attach]
        rw [hls]
      refine ⟨Concrete.Typ.function ls ct_out, ?_⟩
      unfold typToConcrete
      simp only [hmap, hout, bind, Except.bind, pure, Except.pure]

/-! ## Typed.Term.MvarFree — reusable predicate

Structural predicate that every `Typ` annotation appearing anywhere in a
`Typed.Term` is `Typ.MvarFree`. Pure; says nothing about pattern shapes or
match forms. -/
inductive Typed.Term.MvarFree : Typed.Term → Prop
  | unit {τ e} (hτ : Typ.MvarFree τ) : MvarFree (.unit τ e)
  | var {τ e x} (hτ : Typ.MvarFree τ) : MvarFree (.var τ e x)
  | ref {τ e g ta} (hτ : Typ.MvarFree τ)
      (hta : ∀ t ∈ ta, Typ.MvarFree t) : MvarFree (.ref τ e g ta)
  | field {τ e g} (hτ : Typ.MvarFree τ) : MvarFree (.field τ e g)
  | tuple {τ e ts} (hτ : Typ.MvarFree τ)
      (hts : ∀ t ∈ ts, MvarFree t) : MvarFree (.tuple τ e ts)
  | array {τ e ts} (hτ : Typ.MvarFree τ)
      (hts : ∀ t ∈ ts, MvarFree t) : MvarFree (.array τ e ts)
  | ret {τ e r} (hτ : Typ.MvarFree τ) (hr : MvarFree r) : MvarFree (.ret τ e r)
  | letT {τ e p v b} (hτ : Typ.MvarFree τ)
      (hv : MvarFree v) (hb : MvarFree b) : MvarFree (.let τ e p v b)
  | matchT {τ e scrut bs} (hτ : Typ.MvarFree τ) (hs : MvarFree scrut)
      (hbs : ∀ pb ∈ bs, MvarFree pb.snd) : MvarFree (.match τ e scrut bs)
  | app {τ e g ta args u} (hτ : Typ.MvarFree τ)
      (hta : ∀ t ∈ ta, Typ.MvarFree t)
      (hargs : ∀ a ∈ args, MvarFree a) : MvarFree (.app τ e g ta args u)
  | add {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.add τ e a b)
  | sub {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.sub τ e a b)
  | mul {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.mul τ e a b)
  | eqZero {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.eqZero τ e a)
  | proj {τ e a n} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.proj τ e a n)
  | get {τ e a n} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.get τ e a n)
  | slice {τ e a i j} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.slice τ e a i j)
  | set {τ e a n v} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hv : MvarFree v) :
      MvarFree (.set τ e a n v)
  | store {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.store τ e a)
  | load {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.load τ e a)
  | ptrVal {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.ptrVal τ e a)
  | assertEq {τ e a b r} (hτ : Typ.MvarFree τ)
      (ha : MvarFree a) (hb : MvarFree b) (hr : MvarFree r) :
      MvarFree (.assertEq τ e a b r)
  | ioGetInfo {τ e k} (hτ : Typ.MvarFree τ) (hk : MvarFree k) :
      MvarFree (.ioGetInfo τ e k)
  | ioSetInfo {τ e k i l r} (hτ : Typ.MvarFree τ)
      (hk : MvarFree k) (hi : MvarFree i) (hl : MvarFree l) (hr : MvarFree r) :
      MvarFree (.ioSetInfo τ e k i l r)
  | ioRead {τ e i n} (hτ : Typ.MvarFree τ) (hi : MvarFree i) :
      MvarFree (.ioRead τ e i n)
  | ioWrite {τ e d r} (hτ : Typ.MvarFree τ) (hd : MvarFree d) (hr : MvarFree r) :
      MvarFree (.ioWrite τ e d r)
  | u8BitDecomposition {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8BitDecomposition τ e a)
  | u8ShiftLeft {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8ShiftLeft τ e a)
  | u8ShiftRight {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8ShiftRight τ e a)
  | u8Xor {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Xor τ e a b)
  | u8Add {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Add τ e a b)
  | u8Sub {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Sub τ e a b)
  | u8And {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8And τ e a b)
  | u8Or {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Or τ e a b)
  | u8LessThan {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8LessThan τ e a b)
  | u32LessThan {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u32LessThan τ e a b)
  | debug {τ e l t r} (hτ : Typ.MvarFree τ)
      (ht : ∀ sub, t = some sub → MvarFree sub) (hr : MvarFree r) :
      MvarFree (.debug τ e l t r)

/-- A `Source.Pattern` is *simple* iff `subPatternsToLocals` / `expandPattern`
accept it: only `.var`/`.wildcard` at any leaf, `.ref/.tuple/.array` with
such leaves, and `.or` of simples. No `.pointer` sub-patterns (must have been
eliminated by the match compiler). -/
inductive Pattern.Simple : Pattern → Prop
  | var (x) : Simple (.var x)
  | wildcard : Simple .wildcard
  | field (g) : Simple (.field g)
  | refCtor {g ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.ref g ps)
  | tup {ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.tuple ps)
  | arr {ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.array ps)
  | orP {a b} (ha : Simple a) (hb : Simple b) : Simple (.or a b)

/-- Compound predicate used by `termToConcrete_ok_of_concretizeReady`:
`MvarFree` + structural shape constraints that match what `termToConcrete`
currently requires (simplify-pass output). -/
inductive Typed.Term.ConcretizeReady : Typed.Term → Prop
  | unit {τ e} : ConcretizeReady (.unit τ e)
  | var {τ e x} : ConcretizeReady (.var τ e x)
  | ref {τ e g ta} : ConcretizeReady (.ref τ e g ta)
  | field {τ e g} : ConcretizeReady (.field τ e g)
  | tuple {τ e ts} (hts : ∀ t ∈ ts, ConcretizeReady t) :
      ConcretizeReady (.tuple τ e ts)
  | array {τ e ts} (hts : ∀ t ∈ ts, ConcretizeReady t) :
      ConcretizeReady (.array τ e ts)
  | ret {τ e r} (hr : ConcretizeReady r) : ConcretizeReady (.ret τ e r)
  | letT {τ e p v b} (hv : ConcretizeReady v) (hb : ConcretizeReady b) :
      ConcretizeReady (.let τ e p v b)
  | matchT {τ e sx st se bs}
      (hps : ∀ pb ∈ bs, Pattern.Simple pb.fst)
      (hbs : ∀ pb ∈ bs, ConcretizeReady pb.snd) :
      ConcretizeReady (.match τ e (.var st se sx) bs)
  | app {τ e g ta args u} (hargs : ∀ a ∈ args, ConcretizeReady a) :
      ConcretizeReady (.app τ e g ta args u)
  | add {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.add τ e a b)
  | sub {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.sub τ e a b)
  | mul {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.mul τ e a b)
  | eqZero {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.eqZero τ e a)
  | proj {τ e a n} (ha : ConcretizeReady a) : ConcretizeReady (.proj τ e a n)
  | get {τ e a n} (ha : ConcretizeReady a) : ConcretizeReady (.get τ e a n)
  | slice {τ e a i j} (ha : ConcretizeReady a) : ConcretizeReady (.slice τ e a i j)
  | set {τ e a n v} (ha : ConcretizeReady a) (hv : ConcretizeReady v) :
      ConcretizeReady (.set τ e a n v)
  | store {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.store τ e a)
  | load {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.load τ e a)
  | ptrVal {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.ptrVal τ e a)
  | assertEq {τ e a b r} (ha : ConcretizeReady a) (hb : ConcretizeReady b)
      (hr : ConcretizeReady r) : ConcretizeReady (.assertEq τ e a b r)
  | ioGetInfo {τ e k} (hk : ConcretizeReady k) : ConcretizeReady (.ioGetInfo τ e k)
  | ioSetInfo {τ e k i l r} (hk : ConcretizeReady k) (hi : ConcretizeReady i)
      (hl : ConcretizeReady l) (hr : ConcretizeReady r) :
      ConcretizeReady (.ioSetInfo τ e k i l r)
  | ioRead {τ e i n} (hi : ConcretizeReady i) : ConcretizeReady (.ioRead τ e i n)
  | ioWrite {τ e d r} (hd : ConcretizeReady d) (hr : ConcretizeReady r) :
      ConcretizeReady (.ioWrite τ e d r)
  | u8BitDecomposition {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8BitDecomposition τ e a)
  | u8ShiftLeft {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8ShiftLeft τ e a)
  | u8ShiftRight {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8ShiftRight τ e a)
  | u8Xor {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Xor τ e a b)
  | u8Add {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Add τ e a b)
  | u8Sub {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Sub τ e a b)
  | u8And {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8And τ e a b)
  | u8Or {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Or τ e a b)
  | u8LessThan {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8LessThan τ e a b)
  | u32LessThan {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u32LessThan τ e a b)
  | debug {τ e l t r} (ht : ∀ sub, t = some sub → ConcretizeReady sub)
      (hr : ConcretizeReady r) : ConcretizeReady (.debug τ e l t r)

/-! ## Progress lemma: `termToConcrete` succeeds on `ConcretizeReady` terms. -/

/-- A `do`-block that destructures an `Except`-return and extracts a component
reduces to `.ok` of that component when the inner computation succeeds.
Sidesteps the `simp`/`rw` normalization mismatch on `Except.bind` + pair-match. -/
private theorem except_bind_fst_ok {α β ε : Type}
    (x : Except ε (α × β)) (a : α) (b : β) (h : x = .ok (a, b)) :
    (do let (y, _) ← x; pure y : Except ε α) = .ok a := by
  rw [h]; rfl

/-- Helper for single-level pattern sub-patterns: `subPatternsToLocals`
succeeds when every sub-pattern is `.var` or `.wildcard`. -/
private theorem subPatternsToLocals_ok_of_simple {pats : List Pattern}
    (h : ∀ p ∈ pats, p = .wildcard ∨ ∃ x, p = .var x) :
    ∃ locals, subPatternsToLocals pats = .ok locals := by
  suffices hfold :
      ∀ (l : List Pattern) (acc : Array Local × Nat),
        (∀ p ∈ l, p = .wildcard ∨ ∃ x, p = .var x) →
        ∃ acc', l.foldlM (m := Except ConcretizeError) (init := acc)
          (fun (acc, tag) p => do
            match p with
            | .var x => pure (acc.push x, tag)
            | .wildcard => pure (acc.push (.idx tag), tag + 1)
            | _ => throw .unsupportedPattern) = .ok acc' by
    obtain ⟨⟨locals, tag⟩, hfinal⟩ := hfold pats (#[], concretizeWildcardBase) h
    refine ⟨locals, ?_⟩
    exact except_bind_fst_ok _ locals tag hfinal
  intro l
  induction l with
  | nil => intros acc _; exact ⟨acc, rfl⟩
  | cons p rest ih =>
    intros acc hcons
    have hrest : ∀ p ∈ rest, p = .wildcard ∨ ∃ x, p = .var x :=
      fun q hq => hcons q (List.mem_cons_of_mem _ hq)
    rcases hcons p List.mem_cons_self with hw | ⟨x, hv⟩
    · subst hw
      obtain ⟨acc', hacc'⟩ := ih (acc.1.push (.idx acc.2), acc.2 + 1) hrest
      exact ⟨acc', hacc'⟩
    · subst hv
      obtain ⟨acc', hacc'⟩ := ih (acc.1.push x, acc.2) hrest
      exact ⟨acc', hacc'⟩

private theorem subPatternsToLocalsArr_ok_of_simple {pats : Array Pattern}
    (h : ∀ p ∈ pats, p = .wildcard ∨ ∃ x, p = .var x) :
    ∃ locals, subPatternsToLocalsArr pats = .ok locals := by
  have hlist : ∀ p ∈ pats.toList, p = .wildcard ∨ ∃ x, p = .var x :=
    fun p hp => h p (Array.mem_toList_iff.mp hp)
  obtain ⟨locals, hlocals⟩ := subPatternsToLocals_ok_of_simple hlist
  refine ⟨locals, ?_⟩
  unfold subPatternsToLocalsArr
  exact hlocals

/-- Progress for `expandPattern`: every `Pattern.Simple` expands successfully. -/
theorem expandPattern_ok_of_simple
    {scrutTyp : Concrete.Typ} {scrutLocal : Local}
    {p : Pattern} (hp : Pattern.Simple p) (cb : Concrete.Term) :
    ∃ cases, expandPattern scrutTyp scrutLocal p cb = .ok cases := by
  induction hp generalizing cb with
  | var x => exact ⟨_, rfl⟩
  | wildcard => exact ⟨_, rfl⟩
  | field g => exact ⟨_, rfl⟩
  | @refCtor g pats hsub =>
    obtain ⟨locals, hlocals⟩ := subPatternsToLocals_ok_of_simple hsub
    refine ⟨#[(.ref g locals, cb)], ?_⟩
    simp [expandPattern, hlocals, bind, Except.bind, pure, Except.pure]
  | @tup pats hsub =>
    obtain ⟨locals, hlocals⟩ := subPatternsToLocalsArr_ok_of_simple hsub
    refine ⟨#[(.tuple locals, cb)], ?_⟩
    simp [expandPattern, hlocals, bind, Except.bind, pure, Except.pure]
  | @arr pats hsub =>
    obtain ⟨locals, hlocals⟩ := subPatternsToLocalsArr_ok_of_simple hsub
    refine ⟨#[(.array locals, cb)], ?_⟩
    simp [expandPattern, hlocals, bind, Except.bind, pure, Except.pure]
  | orP _ _ iha ihb =>
    obtain ⟨casesA, haA⟩ := iha cb
    obtain ⟨casesB, hbB⟩ := ihb cb
    refine ⟨casesA ++ casesB, ?_⟩
    simp [expandPattern, haA, hbB, bind, Except.bind, pure, Except.pure]


/-- The `foldlM` sweep in the general `.match` path succeeds under
per-branch hypotheses: every branch pattern is `Simple` and every branch
body concretizes. -/
theorem concretize_match_foldlM_ok
    (mono : Std.HashMap (Global × Array Typ) Global)
    (scrutTyp : Concrete.Typ) (scrutLocal : Local) :
    ∀ (bs : List (Pattern × Typed.Term))
      (init : Array (Concrete.Pattern × Concrete.Term)),
      (∀ pb ∈ bs, Pattern.Simple pb.fst) →
      (∀ pb ∈ bs, ∃ c, termToConcrete mono pb.snd = .ok c) →
      ∃ cases, bs.foldlM
        (fun acc (pb : Pattern × Typed.Term) => do
          let cb ← termToConcrete mono pb.snd
          pure (acc ++ (← expandPattern scrutTyp scrutLocal pb.fst cb))) init = .ok cases
  | [], init, _, _ => ⟨init, rfl⟩
  | (p, b) :: rest, init, hps, hbs => by
    obtain ⟨cb, hcb⟩ := hbs (p, b) List.mem_cons_self
    have hpSimple : Pattern.Simple p := hps (p, b) List.mem_cons_self
    obtain ⟨exp, hexp⟩ :=
      @expandPattern_ok_of_simple scrutTyp scrutLocal p hpSimple cb
    have hps' : ∀ pb ∈ rest, Pattern.Simple pb.fst :=
      fun pb hpb => hps pb (List.mem_cons_of_mem _ hpb)
    have hbs' : ∀ pb ∈ rest, ∃ c, termToConcrete mono pb.snd = .ok c :=
      fun pb hpb => hbs pb (List.mem_cons_of_mem _ hpb)
    obtain ⟨cases, hcases⟩ :=
      concretize_match_foldlM_ok mono scrutTyp scrutLocal rest (init ++ exp) hps' hbs'
    refine ⟨cases, ?_⟩
    simp only [List.foldlM_cons, bind, Except.bind, hcb, hexp, pure, Except.pure]
    exact hcases



/-- Tailored `foldlM` sweep lemma matching the exact
`Array.foldlM (fun x y => match ... y.1.snd ... y.1.fst ... ) #[] bs.toArray.attach`
shape generated by `fun_induction` on `termToConcrete`'s `.match` arm.

Rather than rewriting between `Array.foldlM`/`List.foldlM` (which fails
syntactically — `fun y => step acc y.1` vs `fun ⟨x, _⟩ => step acc x` are
not kernel-defeq for non-constructor `y`), we normalize the
`Array.foldlM`/`.attach` into a `List.foldlM` over `bs.toArray.toList.attachWith`
via `Array.foldlM_toList` + `Array.toList_attach`, then do the induction
directly on the attached list. -/
theorem concretize_match_attach_foldlM_ok
    (mono : Std.HashMap (Global × Array Typ) Global)
    (scrutTyp : Concrete.Typ) (scrutLocal : Local)
    (bs : List (Pattern × Typed.Term))
    (hps : ∀ pb ∈ bs, Pattern.Simple pb.fst)
    (hbs : ∀ pb ∈ bs, ∃ c, termToConcrete mono pb.snd = .ok c) :
    ∃ cases,
      bs.toArray.attach.foldlM
        (fun (x : Array (Concrete.Pattern × Concrete.Term))
             (y : {pb : Pattern × Typed.Term // pb ∈ bs.toArray}) => do
          let cb ← termToConcrete mono y.1.snd
          pure (x ++ (← expandPattern scrutTyp scrutLocal y.1.fst cb)))
        (init := #[]) = .ok cases := by
  -- Unfold `Array.foldlM` on `.attach` via the `Array.foldlM_toList` +
  -- `Array.toList_attach` pipeline (same one used in goals 2 and 3).
  conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
  simp only [Array.toList_attach]
  -- After `simp only [Array.toList_attach]`, the list is `bs.attachWith (· ∈ bs.toArray) _`.
  -- Prove this by structural induction on `bs`, with a generalized
  -- `attachWith`-membership predicate.
  suffices h : ∀ (bs' : List (Pattern × Typed.Term))
               (init : Array (Concrete.Pattern × Concrete.Term))
               (Hmem : ∀ pb ∈ bs', pb ∈ bs.toArray),
               (∀ pb ∈ bs', Pattern.Simple pb.fst) →
               (∀ pb ∈ bs', ∃ c, termToConcrete mono pb.snd = .ok c) →
               ∃ cases,
                 List.foldlM
                   (fun (x : Array (Concrete.Pattern × Concrete.Term))
                        (y : {pb : Pattern × Typed.Term // pb ∈ bs.toArray}) => do
                     let cb ← termToConcrete mono y.val.snd
                     pure (x ++ (← expandPattern scrutTyp scrutLocal y.val.fst cb)))
                   init (bs'.attachWith (· ∈ bs.toArray) Hmem) = .ok cases from
    h bs #[] (fun _ h => List.mem_toArray.mpr h) hps hbs
  intro bs'
  induction bs' with
  | nil => intros; exact ⟨_, rfl⟩
  | cons pb rest ih =>
    intro init Hmem hps' hbs'
    obtain ⟨p, b⟩ := pb
    obtain ⟨cb, hcb⟩ := hbs' (p, b) List.mem_cons_self
    have hpSimple : Pattern.Simple p := hps' (p, b) List.mem_cons_self
    obtain ⟨exp, hexp⟩ :=
      @expandPattern_ok_of_simple scrutTyp scrutLocal p hpSimple cb
    have hps'' : ∀ pb ∈ rest, Pattern.Simple pb.fst :=
      fun pb hpb => hps' pb (List.mem_cons_of_mem _ hpb)
    have hbs'' : ∀ pb ∈ rest, ∃ c, termToConcrete mono pb.snd = .ok c :=
      fun pb hpb => hbs' pb (List.mem_cons_of_mem _ hpb)
    have Hmem' : ∀ pb ∈ rest, pb ∈ bs.toArray :=
      fun pb hpb => Hmem pb (List.mem_cons_of_mem _ hpb)
    obtain ⟨cases, hcases⟩ := ih (init ++ exp) Hmem' hps'' hbs''
    refine ⟨cases, ?_⟩
    simp only [List.attachWith_cons, List.foldlM_cons, hcb, hexp, bind,
               Except.bind, pure, Except.pure]
    exact hcases

/-- When a term is both `Typed.Term.MvarFree` and `Typed.Term.ConcretizeReady`,
`termToConcrete` succeeds. The proof uses `fun_induction` on the recursion
structure of `termToConcrete` to sidestep the nested-inductive limitation
of plain `induction`; each arm is dispatched via the corresponding
constructor in `MvarFree`/`ConcretizeReady` and the IHs. -/
theorem termToConcrete_ok_of_concretizeReady
    (mono : Std.HashMap (Global × Array Typ) Global) :
    ∀ {t : Typed.Term}, Typed.Term.MvarFree t → Typed.Term.ConcretizeReady t →
    ∃ ct, termToConcrete mono t = .ok ct := by
  intro t
  fun_induction termToConcrete mono t <;> intro hmf hcr
  case case1 τ e =>
    cases hmf with
    | unit hτ =>
      obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
      refine ⟨Concrete.Term.unit cτ e, ?_⟩
      simp only [hcτ, bind, Except.bind, pure, Except.pure]
  case case2 τ e x =>
    cases hmf with
    | var hτ =>
      obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
      refine ⟨Concrete.Term.var cτ e x, ?_⟩
      simp only [hcτ, bind, Except.bind, pure, Except.pure]
  case case3 τ e g ta =>
    cases hmf with
    | ref hτ _hta =>
      obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
      refine ⟨Concrete.Term.ref cτ e g, ?_⟩
      simp only [hcτ, bind, Except.bind, pure, Except.pure]
  case case4 τ e g =>
    cases hmf with
    | field hτ =>
      obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
      refine ⟨Concrete.Term.field cτ e g, ?_⟩
      simp only [hcτ, bind, Except.bind, pure, Except.pure]
  case case5 τ e ts ih =>
    cases hmf with
    | tuple hτ hts =>
      cases hcr with
      | tuple hrts =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        have hmap : ∀ a ∈ ts, ∃ b, termToConcrete mono a = .ok b := by
          intro a ha; exact ih a ha (hts a ha) (hrts a ha)
        obtain ⟨cts, hcts⟩ := Array.mapM_except_ok hmap
        refine ⟨Concrete.Term.tuple cτ e cts.toArray, ?_⟩
        simp only [hcτ, hcts, bind, Except.bind, pure, Except.pure]
  case case6 τ e ts ih =>
    cases hmf with
    | array hτ hts =>
      cases hcr with
      | array hrts =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        have hmap : ∀ a ∈ ts, ∃ b, termToConcrete mono a = .ok b := by
          intro a ha; exact ih a ha (hts a ha) (hrts a ha)
        obtain ⟨cts, hcts⟩ := Array.mapM_except_ok hmap
        refine ⟨Concrete.Term.array cτ e cts.toArray, ?_⟩
        simp only [hcτ, hcts, bind, Except.bind, pure, Except.pure]
  case case7 τ e r ih =>
    cases hmf with
    | ret hτ hr =>
      cases hcr with
      | ret hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨cr, hcr'⟩ := ih hr hrr
        refine ⟨Concrete.Term.ret cτ e cr, ?_⟩
        simp only [hcτ, hcr', bind, Except.bind, pure, Except.pure]
  case case8 τ e pat v b ihv ihb =>
    cases hmf with
    | letT hτ hmv hmb =>
      cases hcr with
      | letT hrv hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨cv, hcv⟩ := ihv hmv hrv
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        cases pat with
        | var x =>
          refine ⟨Concrete.Term.letVar cτ e x cv cb, ?_⟩
          simp only [hcτ, hcv, hcb, bind, Except.bind, pure, Except.pure]
        | _ =>
          all_goals {
            refine ⟨Concrete.Term.letWild cτ e cv cb, ?_⟩
            simp only [hcτ, hcv, hcb, bind, Except.bind, pure, Except.pure]
          }
  case case9 τ e scrut bs ihScrut ihBranches _ihArrBody _ihTupBody =>
    cases hcr with
    | @matchT _ _ sx st se _ hps hrbs =>
      cases hmf with
      | matchT hτ hmscrut hmbs =>
        cases hmscrut with
        | var hst =>
          obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
          obtain ⟨cst, hcst⟩ := typToConcrete_ok_of_mvarFree mono hst
          have hbr : ∀ pb ∈ bs, ∃ c, termToConcrete mono pb.snd = .ok c := by
            intro pb hpb
            obtain ⟨p, b⟩ := pb
            have hpbArr : (p, b) ∈ bs.toArray := List.mem_toArray.mpr hpb
            exact ihBranches p b hpbArr (hmbs (p, b) hpb) (hrbs (p, b) hpb)
          -- After `fun_induction`, the goal is a continuation encoding
          -- `termToConcrete`'s `.match` arm, partially applied with the
          -- scrutinee result. Need to show existence for all `bs` shapes.
          -- Use `simp only [termToConcrete, ...]` to unfold, then case-split.
          have hscrut : termToConcrete mono (Typed.Term.var st se sx) =
              .ok (Concrete.Term.var cst se sx) := by
            simp only [termToConcrete, hcst, bind, Except.bind, pure, Except.pure]
          simp only [hcτ, hscrut, bind, Except.bind, pure, Except.pure]
          -- The goal is a nested match on `bs` shape with `__do_jp` joins.
          -- The outermost match checks for single-arm tuple.
          -- Split on that first.
          -- The goal after simp has nested match-on-`bs` for the single-arm
          -- tuple/array shortcuts, with `__do_jp` join points. `split` on
          -- each match, then close each branch.
          -- The goal has nested `match bs` with `__do_jp` join points.
          -- `split <;> split` handles: (1) tuple+tupleType, (2) tuple+otherType,
          -- (3,4) notTuple+array check. Each path reduces to a `match` on
          -- `termToConcrete` results that we can rewrite.
          split <;> split
          -- Case 1: bs = [(tuple pats, body)] ∧ cst = .tuple ts
          · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
            simp only [] at hcb
            exact ⟨_, by rw [hcb]⟩
          -- Case 2: bs = [(tuple pats, body)] ∧ cst not .tuple
          --   The inner array match on the tuple-shaped bs falls to the else branch.
          --   Then foldlM over the single branch succeeds.
          -- Remaining cases 2,3,4: each reaches the general foldlM path.
          -- In each case, the Array.foldlM result wraps into a match
          -- that produces .ok on success. Show existence by processing
          -- each branch body and pattern.
          -- Case 2: bs = [(tuple .., body)], cst not tuple → foldlM
          · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
            simp only [] at hcb
            have hpSimple := hps _ List.mem_cons_self
            simp only [] at hpSimple
            obtain ⟨exp, hexp⟩ :=
              @expandPattern_ok_of_simple cst sx _ hpSimple cb
            -- The goal has a match on the foldlM result.
            -- Show the foldlM on the singleton succeeds by computing it:
            -- The foldlM processes one element: termToConcrete body = .ok cb,
            -- expandPattern pat cb = .ok exp, result = #[] ++ exp.
            -- Then the outer match gives .ok (.match cτ e sx exp none).
            -- Use `rw` with the hypothesis to simplify.
            -- The foldlM function in the goal is alpha-equivalent to:
            --   fun acc ⟨(p, b), _⟩ => match termToConcrete ... with ...
            -- After one step: match (.ok cb) => match (.ok exp) => .ok (#[] ++ exp)
            -- Then match (.ok (#[] ++ exp)) => .ok (.match ...)
            -- But we also need to handle the second `if let` guard.
            -- The second `if let` checks for [(Pattern.array .., body)].
            -- Since bs = [(Pattern.tuple .., body)], this fails (tuple /= array).
            -- So the goal should already be at the foldlM case.
            split
            · -- Unreachable: bs = [(tuple ..)] can't match [(array ..)]
              simp_all
            · -- foldlM path: singleton array foldlM reduces to one step.
              conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
              simp only [Array.toList_attach,
                         List.attachWith, List.foldlM,
                         List.pmap, List.foldlM_cons,
                         hcb, hexp]
              exact ⟨_, rfl⟩
          -- Case 3: bs = [(array .., body)] → split on cst for array shortcut
          · split
            · -- cst = .array: destructureArray path
              obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
              simp only [] at hcb
              exact ⟨_, by rw [hcb]⟩
            · -- cst not array: foldlM path (singleton)
              obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
              simp only [] at hcb
              have hpSimple := hps _ List.mem_cons_self
              simp only [] at hpSimple
              obtain ⟨exp, hexp⟩ :=
                @expandPattern_ok_of_simple cst sx _ hpSimple cb
              conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
              simp only [Array.toList_attach,
                         List.attachWith, List.foldlM,
                         List.pmap, List.foldlM_cons,
                         hcb, hexp]
              exact ⟨_, rfl⟩
          -- Case 4: bs not singleton tuple/array → foldlM (general).
          -- `fun_induction` produces an `Array.foldlM` over `bs.toArray.attach`
          -- whose step function projects via `y.1` (so a destructuring lambda
          -- cannot match syntactically). The tailored sweep lemma
          -- `concretize_match_attach_foldlM_ok` is stated with the matching
          -- `y.1`/`do` shape; after unfolding `bind`/`Except.bind` the two
          -- sides share the same `match`-on-`Except` core and `rw` closes.
          · obtain ⟨cases, hcases⟩ :=
              concretize_match_attach_foldlM_ok mono cst sx bs hps hbr
            simp only [bind, Except.bind, pure, Except.pure] at hcases
            refine ⟨Concrete.Term.match cτ e sx cases none, ?_⟩
            rw [hcases]
  case case10 τ e g ta args u ih =>
    cases hmf with
    | app hτ _hta hargs =>
      cases hcr with
      | app hrargs =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        have hmap : ∀ a ∈ args, ∃ b, termToConcrete mono a = .ok b := by
          intro a ha; exact ih a ha (hargs a ha) (hrargs a ha)
        obtain ⟨cargs, hcargs⟩ := List.mapM_except_ok hmap
        refine ⟨Concrete.Term.app cτ e g cargs u, ?_⟩
        simp only [hcτ, hcargs, bind, Except.bind, pure, Except.pure]
  case case11 τ e a b iha ihb =>
    cases hmf with
    | add hτ hma hmb =>
      cases hcr with
      | add hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.add cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case12 τ e a b iha ihb =>
    cases hmf with
    | sub hτ hma hmb =>
      cases hcr with
      | sub hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.sub cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case13 τ e a b iha ihb =>
    cases hmf with
    | mul hτ hma hmb =>
      cases hcr with
      | mul hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.mul cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case14 τ e a iha =>
    cases hmf with
    | eqZero hτ hma =>
      cases hcr with
      | eqZero hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.eqZero cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case15 τ e a n iha =>
    cases hmf with
    | proj hτ hma =>
      cases hcr with
      | proj hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.proj cτ e ca n, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case16 τ e a n iha =>
    cases hmf with
    | get hτ hma =>
      cases hcr with
      | get hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.get cτ e ca n, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case17 τ e a i j iha =>
    cases hmf with
    | slice hτ hma =>
      cases hcr with
      | slice hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.slice cτ e ca i j, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case18 τ e a n v iha ihv =>
    cases hmf with
    | set hτ hma hmv =>
      cases hcr with
      | set hra hrv =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cv, hcv⟩ := ihv hmv hrv
        refine ⟨Concrete.Term.set cτ e ca n cv, ?_⟩
        simp only [hcτ, hca, hcv, bind, Except.bind, pure, Except.pure]
  case case19 τ e a iha =>
    cases hmf with
    | store hτ hma =>
      cases hcr with
      | store hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.store cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case20 τ e a iha =>
    cases hmf with
    | load hτ hma =>
      cases hcr with
      | load hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.load cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case21 τ e a iha =>
    cases hmf with
    | ptrVal hτ hma =>
      cases hcr with
      | ptrVal hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.ptrVal cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case22 τ e a b r iha ihb ihr =>
    cases hmf with
    | assertEq hτ hma hmb hmr =>
      cases hcr with
      | assertEq hra hrb hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        obtain ⟨cr, hcr'⟩ := ihr hmr hrr
        refine ⟨Concrete.Term.assertEq cτ e ca cb cr, ?_⟩
        simp only [hcτ, hca, hcb, hcr', bind, Except.bind, pure, Except.pure]
  case case23 τ e k ihk =>
    cases hmf with
    | ioGetInfo hτ hmk =>
      cases hcr with
      | ioGetInfo hrk =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ck, hck⟩ := ihk hmk hrk
        refine ⟨Concrete.Term.ioGetInfo cτ e ck, ?_⟩
        simp only [hcτ, hck, bind, Except.bind, pure, Except.pure]
  case case24 τ e k i l r ihk ihi ihl ihr =>
    cases hmf with
    | ioSetInfo hτ hmk hmi hml hmr =>
      cases hcr with
      | ioSetInfo hrk hri hrl hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ck, hck⟩ := ihk hmk hrk
        obtain ⟨ci, hci⟩ := ihi hmi hri
        obtain ⟨cl, hcl⟩ := ihl hml hrl
        obtain ⟨cr, hcr'⟩ := ihr hmr hrr
        refine ⟨Concrete.Term.ioSetInfo cτ e ck ci cl cr, ?_⟩
        simp only [ hcτ, hck, hci, hcl, hcr',
                   bind, Except.bind, pure, Except.pure]
  case case25 τ e i n ihi =>
    cases hmf with
    | ioRead hτ hmi =>
      cases hcr with
      | ioRead hri =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ci, hci⟩ := ihi hmi hri
        refine ⟨Concrete.Term.ioRead cτ e ci n, ?_⟩
        simp only [hcτ, hci, bind, Except.bind, pure, Except.pure]
  case case26 τ e d r ihd ihr =>
    cases hmf with
    | ioWrite hτ hmd hmr =>
      cases hcr with
      | ioWrite hrd hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨cd, hcd⟩ := ihd hmd hrd
        obtain ⟨cr, hcr'⟩ := ihr hmr hrr
        refine ⟨Concrete.Term.ioWrite cτ e cd cr, ?_⟩
        simp only [hcτ, hcd, hcr', bind, Except.bind, pure, Except.pure]
  case case27 τ e a iha =>
    cases hmf with
    | u8BitDecomposition hτ hma =>
      cases hcr with
      | u8BitDecomposition hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.u8BitDecomposition cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case28 τ e a iha =>
    cases hmf with
    | u8ShiftLeft hτ hma =>
      cases hcr with
      | u8ShiftLeft hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.u8ShiftLeft cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case29 τ e a iha =>
    cases hmf with
    | u8ShiftRight hτ hma =>
      cases hcr with
      | u8ShiftRight hra =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        refine ⟨Concrete.Term.u8ShiftRight cτ e ca, ?_⟩
        simp only [hcτ, hca, bind, Except.bind, pure, Except.pure]
  case case30 τ e a b iha ihb =>
    cases hmf with
    | u8Xor hτ hma hmb =>
      cases hcr with
      | u8Xor hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8Xor cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case31 τ e a b iha ihb =>
    cases hmf with
    | u8Add hτ hma hmb =>
      cases hcr with
      | u8Add hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8Add cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case32 τ e a b iha ihb =>
    cases hmf with
    | u8Sub hτ hma hmb =>
      cases hcr with
      | u8Sub hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8Sub cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case33 τ e a b iha ihb =>
    cases hmf with
    | u8And hτ hma hmb =>
      cases hcr with
      | u8And hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8And cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case34 τ e a b iha ihb =>
    cases hmf with
    | u8Or hτ hma hmb =>
      cases hcr with
      | u8Or hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8Or cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case35 τ e a b iha ihb =>
    cases hmf with
    | u8LessThan hτ hma hmb =>
      cases hcr with
      | u8LessThan hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u8LessThan cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case36 τ e a b iha ihb =>
    cases hmf with
    | u32LessThan hτ hma hmb =>
      cases hcr with
      | u32LessThan hra hrb =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨ca, hca⟩ := iha hma hra
        obtain ⟨cb, hcb⟩ := ihb hmb hrb
        refine ⟨Concrete.Term.u32LessThan cτ e ca cb, ?_⟩
        simp only [hcτ, hca, hcb, bind, Except.bind, pure, Except.pure]
  case case37 τ e l r cont ihr =>
    cases hmf with
    | debug hτ hmt hmr =>
      cases hcr with
      | debug hrt hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        obtain ⟨cr, hcr'⟩ := ihr hmr hrr
        refine ⟨Concrete.Term.debug cτ e l none cr, ?_⟩
        show cont none = _
        simp only [cont, hcτ, hcr', bind, Except.bind, pure, Except.pure]
  case case38 τ e l sub cont cont2 ih1 ih2 =>
    cases hmf with
    | debug hτ hmt hmr =>
      cases hcr with
      | debug hrt hrr =>
        obtain ⟨cτ, hcτ⟩ := typToConcrete_ok_of_mvarFree mono hτ
        have hmcont2 : cont2.MvarFree := hmt cont2 rfl
        have hrcont2 : cont2.ConcretizeReady := hrt cont2 rfl
        obtain ⟨ccont2, hccont2⟩ := ih2 hmcont2 hrcont2
        obtain ⟨cr, hcr'⟩ := ih1 hmr hrr
        refine ⟨Concrete.Term.debug cτ e l (some ccont2) cr, ?_⟩
        simp only [cont, hcτ, hccont2, hcr', bind, Except.bind, pure, Except.pure]

end Aiur

end
