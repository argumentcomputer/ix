module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.FirstOrder

/-!
`Typed.Term.RefsDt` / `Concrete.Term.RefsDt` bridge infrastructure:
substInTypedTerm/rewriteTypedTerm/termToConcrete preservation, drain
chain, `concretizeBuild_preserves_TermRefsDt`, and the `step4Lower` fold.
Extracted from `ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### `TermRefsDt` bridge infrastructure.

Mirrors the FO chain above. The two structural 37-arm lemmas are the heart
(`rewriteTypedTerm_preserves_RefsDt` on typed→typed rewrite,
`termToConcrete_preserves_RefsDt` on typed→concrete lowering); the
composition layers (`concretizeBuild`, `step4Lower` fold) assemble them. -/

-- `list_mem_of_attach_map` and `List.mem_mapM_ok_forall` are defined earlier
-- (moved before `substInTypedTerm_preserves_RefsDt`).

/-- `rewriteTypedTerm` preserves `Typed.Term.RefsDt` structurally.
Given a unified bridge from `decls`-keyed dt/ctor entries to the target `tds'`
under `rewriteGlobal`, each arm rebuilds `RefsDt tds'` on the rewritten term.

The unified bridge subsumes the prior triple `hdt_bridge` / `hctor_bridge` /
`hrewriteGlobal_preserve` into a single `g`-resolving statement:
`g` dt/ctor in `decls` ⟹ `rewriteGlobal decls mono g tArgs` dt/ctor in `tds'`.
This is essential for `concretizeBuild_preserves_TermRefsDt`, where the
constructor-`mono`-hit case yields a fresh name `concDTName.pushNamespace
ctorName` not present in `decls`. The merged bridge requires the bridge
proof to be performed once for each `(g, tArgs)` pair, threading dt/ctor
witnesses through `rewriteGlobal`'s case analysis directly into `tds'`. -/
theorem rewriteTypedTerm_preserves_RefsDt
    {decls : Typed.Decls} {subst : Global → Option Typ} {mono : MonoMap}
    {tds' : Typed.Decls} {body : Typed.Term}
    (hbody : Typed.Term.RefsDt decls body)
    (hbridge : ∀ g tArgs,
      (∃ dt c, decls.getByKey g = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) →
      ∃ dt c, tds'.getByKey (rewriteGlobal decls mono g tArgs) =
        some (.constructor dt c) ∧
        (dt.params.isEmpty ∨
          ¬ (tArgs.map (rewriteTyp subst mono)).isEmpty)) :
    Typed.Term.RefsDt tds' (rewriteTypedTerm decls subst mono body) := by
  induction hbody with
  | unit => unfold rewriteTypedTerm; exact .unit
  | var => unfold rewriteTypedTerm; exact .var
  | @ref typ e g tArgs hdt =>
    unfold rewriteTypedTerm
    -- Sig amendment 2026-05-04 (RefsDt-defect): the bridge premise now
    -- threads the structural disjunct `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`
    -- through to the rewritten target. The hypothesis input (`hdt`) and the
    -- bridge output both bundle the disjunct alongside the `getByKey`
    -- witness; we pass through verbatim.
    exact .ref (hbridge g tArgs hdt)
  | field => unfold rewriteTypedTerm; exact .field
  | @tuple typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .tuple ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .array ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | ret _ ihr =>
    unfold rewriteTypedTerm; exact .ret ihr
  | «let» _ _ ihv ihb =>
    unfold rewriteTypedTerm; exact .let ihv ihb
  | @«match» typ e scrut cases _ _ ihscrut ihcases =>
    unfold rewriteTypedTerm
    refine .match ihscrut ?_
    intro pc hpc
    obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
    subst hp0eq
    exact ihcases p0 hp0mem
  | @app typ e g tArgs args u _ ih =>
    unfold rewriteTypedTerm
    refine .app ?_
    intro a ha
    obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
    subst ha0eq
    exact ih a0 ha0mem
  | add _ _ iha ihb => unfold rewriteTypedTerm; exact .add iha ihb
  | sub _ _ iha ihb => unfold rewriteTypedTerm; exact .sub iha ihb
  | mul _ _ iha ihb => unfold rewriteTypedTerm; exact .mul iha ihb
  | eqZero _ iha => unfold rewriteTypedTerm; exact .eqZero iha
  | proj _ iha => unfold rewriteTypedTerm; exact .proj iha
  | get _ iha => unfold rewriteTypedTerm; exact .get iha
  | slice _ iha => unfold rewriteTypedTerm; exact .slice iha
  | «set» _ _ iha ihv => unfold rewriteTypedTerm; exact .set iha ihv
  | store _ iha => unfold rewriteTypedTerm; exact .store iha
  | load _ iha => unfold rewriteTypedTerm; exact .load iha
  | ptrVal _ iha => unfold rewriteTypedTerm; exact .ptrVal iha
  | assertEq _ _ _ iha ihb ihr =>
    unfold rewriteTypedTerm; exact .assertEq iha ihb ihr
  | ioGetInfo _ ihk => unfold rewriteTypedTerm; exact .ioGetInfo ihk
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr =>
    unfold rewriteTypedTerm; exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ihi => unfold rewriteTypedTerm; exact .ioRead ihi
  | ioWrite _ _ ihd ihr => unfold rewriteTypedTerm; exact .ioWrite ihd ihr
  | u8BitDecomposition _ iha => unfold rewriteTypedTerm; exact .u8BitDecomposition iha
  | u8ShiftLeft _ iha => unfold rewriteTypedTerm; exact .u8ShiftLeft iha
  | u8ShiftRight _ iha => unfold rewriteTypedTerm; exact .u8ShiftRight iha
  | u8Xor _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Sub iha ihb
  | u8And _ _ iha ihb => unfold rewriteTypedTerm; exact .u8And iha ihb
  | u8Or  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Or iha ihb
  | u8LessThan  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => unfold rewriteTypedTerm; exact .u32LessThan iha ihb
  | @debug typ e label t r ht hr iht ihr =>
    unfold rewriteTypedTerm
    refine .debug ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl


/-! #### `Concrete.Term.RefsDt` monotonicity.

Under an "all-keys-preserving" hypothesis on the underlying `Concrete.Decls`,
`RefsDt cd₁ t → RefsDt cd₂ t`. The pipeline only ever inserts new entries
into the accumulator (no key deletion or function-key injection over a
prior dt/ctor-keyed entry), so the witness for each `.ref` subterm survives
through every step. -/
theorem Concrete.Term.RefsDt.mono
    {cd₁ cd₂ : Concrete.Decls} {t : Concrete.Term}
    (hwit : ∀ g,
      ((∃ dt, cd₁.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd₁.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd₂.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd₂.getByKey g = some (.constructor dt c))))
    (hr : Concrete.Term.RefsDt cd₁ t) :
    Concrete.Term.RefsDt cd₂ t := by
  induction hr with
  | unit => exact .unit
  | var => exact .var
  | ref hdt => exact .ref (hwit _ hdt)
  | field => exact .field
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | ret _ ih => exact .ret ih
  | letVar _ _ ihv ihb => exact .letVar ihv ihb
  | letWild _ _ ihv ihb => exact .letWild ihv ihb
  | letLoad _ ihb => exact .letLoad ihb
  | «match» _ _ ihcases ihdef => exact .match ihcases ihdef
  | app _ ih => exact .app ih
  | add _ _ iha ihb => exact .add iha ihb
  | sub _ _ iha ihb => exact .sub iha ihb
  | mul _ _ iha ihb => exact .mul iha ihb
  | eqZero _ ih => exact .eqZero ih
  | proj _ ih => exact .proj ih
  | get _ ih => exact .get ih
  | slice _ ih => exact .slice ih
  | «set» _ _ iha ihv => exact .set iha ihv
  | store _ ih => exact .store ih
  | load _ ih => exact .load ih
  | ptrVal _ ih => exact .ptrVal ih
  | assertEq _ _ _ iha ihb ihr => exact .assertEq iha ihb ihr
  | ioGetInfo _ ih => exact .ioGetInfo ih
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr => exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ih => exact .ioRead ih
  | ioWrite _ _ ihd ihr => exact .ioWrite ihd ihr
  | u8BitDecomposition _ ih => exact .u8BitDecomposition ih
  | u8ShiftLeft _ ih => exact .u8ShiftLeft ih
  | u8ShiftRight _ ih => exact .u8ShiftRight ih
  | u8Xor _ _ iha ihb => exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => exact .u8Sub iha ihb
  | u8And _ _ iha ihb => exact .u8And iha ihb
  | u8Or _ _ iha ihb => exact .u8Or iha ihb
  | u8LessThan _ _ iha ihb => exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => exact .u32LessThan iha ihb
  | debug _ _ iht ihr => exact .debug iht ihr

/-- `destructureTuple` preserves `RefsDt cb` on its output. The output is a
foldl over `List.range pats.size`, each step wrapping the accumulator in
`.letVar`/`.letWild` over a `.proj` on `scrutTerm`. Both wrappers are
constructors of `Concrete.Term.RefsDt` whose only inductive premise is
`RefsDt acc`, plus the trivially-`RefsDt` `.proj` on the (RefsDt) scrutinee. -/
theorem destructureTuple_preserves_RefsDt
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (ts : Array Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.RefsDt cd scrutTerm)
    (hcb : Concrete.Term.RefsDt cd cb) :
    Concrete.Term.RefsDt cd (destructureTuple scrutTerm pats ts cb) := by
  unfold destructureTuple
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    -- The single-step body wraps cb in either .letVar or .letWild over .proj scrutTerm.
    have hproj : Concrete.Term.RefsDt cd
        (.proj (ts[pats.size - 1 - hd]?.getD .unit) false scrutTerm
          (pats.size - 1 - hd)) := .proj hscrut
    split <;> first
      | exact .letVar hproj hcb
      | exact .letWild hproj hcb

/-- `destructureArray` preserves `RefsDt cb` on its output. Same shape as
`destructureTuple_preserves_RefsDt`, with `.get` in place of `.proj`. -/
theorem destructureArray_preserves_RefsDt
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (eltTyp : Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.RefsDt cd scrutTerm)
    (hcb : Concrete.Term.RefsDt cd cb) :
    Concrete.Term.RefsDt cd (destructureArray scrutTerm pats eltTyp cb) := by
  unfold destructureArray
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    have hget : Concrete.Term.RefsDt cd
        (.get eltTyp false scrutTerm (pats.size - 1 - hd)) := .get hscrut
    split <;> first
      | exact .letVar hget hcb
      | exact .letWild hget hcb

/-- Sub-lemma for the general `.match` path: `expandPattern` produces a
list of cases each of whose body is either `cb` itself, or `cb` wrapped in
a `.letVar _ _ x (.var scrutTyp false scrutLocal) cb`. In both cases, if
`Concrete.Term.RefsDt cd cb`, then every produced body satisfies
`Concrete.Term.RefsDt cd`. Recurses on Pattern for the `.or` case. -/
theorem expandPattern_preserves_RefsDt
    {cd : Concrete.Decls} {scrutTyp : Concrete.Typ} {scrutLocal : Local} :
    ∀ {p : Pattern} {cb : Concrete.Term}
      {result : Array (Concrete.Pattern × Concrete.Term)},
      Concrete.Term.RefsDt cd cb →
      expandPattern scrutTyp scrutLocal p cb = .ok result →
      ∀ pc ∈ result, Concrete.Term.RefsDt cd pc.2
  | .wildcard, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .var x, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard,
        .letVar cb.typ cb.escapes x (.var scrutTyp false scrutLocal) cb) := by
      simpa using hpc
    subst hpc'
    exact .letVar .var hcb
  | .field g, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.field g, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .ref g pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.ref g locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .tuple pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.tuple locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .array pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.array locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .or p1 p2, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i r1 hr1
    split at hexp
    · cases hexp
    rename_i r2 hr2
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    rw [Array.mem_append] at hpc
    rcases hpc with h1 | h2
    · exact expandPattern_preserves_RefsDt hcb hr1 pc h1
    · exact expandPattern_preserves_RefsDt hcb hr2 pc h2
  | .pointer p, cb, result, _hcb, hexp => by
    -- Throws .unsupportedPattern; hexp is unreachable.
    unfold expandPattern at hexp
    cases hexp

/-- Generic `foldlM` invariant for the `attach`-folded `expandPattern` builder.
Given a list `xs : List _` (with each element memorized in `bs` via `hsub`),
folding `expandPattern scrutTyp scrutLocal x.val.1 cb_x` (where
`cb_x = (termToConcrete mono x.val.2).ok`) over `xs_attach` produces an array
where every case body satisfies `RefsDt cd`. -/
theorem expandPattern_foldlM_preserves_RefsDt
    {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {scrutTyp : Concrete.Typ} {scrutLocal : Local}
    (bs : List (Pattern × Typed.Term))
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.RefsDt cd cb) :
    ∀ (xs_attach : List (Pattern × Typed.Term))
      (init final : Array (Concrete.Pattern × Concrete.Term)),
      (∀ x ∈ xs_attach, x ∈ bs) →
      (∀ pc' ∈ init, Concrete.Term.RefsDt cd pc'.2) →
      List.foldlM
        (fun acc (x : Pattern × Typed.Term) => do
          let cb ← termToConcrete mono x.2
          pure (acc ++ (← expandPattern scrutTyp scrutLocal x.1 cb)))
        init xs_attach = .ok final →
      ∀ pc' ∈ final, Concrete.Term.RefsDt cd pc'.2
  | [], init, final, _hsub, hinit, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    exact hinit
  | hd :: tl, init, final, hsub, hinit, hfold => by
    rw [List.foldlM_cons] at hfold
    simp only [bind, Except.bind] at hfold
    -- Now hfold has the shape `(termToConcrete mono hd.2 >>= fun cb => ...)`.
    cases hcb_hd : termToConcrete mono hd.2 with
    | error _ => rw [hcb_hd] at hfold; cases hfold
    | ok cb_hd =>
      rw [hcb_hd] at hfold
      simp only at hfold
      cases hexp_hd : expandPattern scrutTyp scrutLocal hd.1 cb_hd with
      | error _ => rw [hexp_hd] at hfold; cases hfold
      | ok exp_hd =>
        rw [hexp_hd] at hfold
        simp only [pure, Except.pure] at hfold
        have hd_in_bs : hd ∈ bs := hsub hd List.mem_cons_self
        have hcb_ref : Concrete.Term.RefsDt cd cb_hd :=
          ihcases hd hd_in_bs hcb_hd
        have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.RefsDt cd pc'.2 :=
          expandPattern_preserves_RefsDt hcb_ref hexp_hd
        have hnew_init : ∀ pc' ∈ init ++ exp_hd, Concrete.Term.RefsDt cd pc'.2 := by
          intro pc' hpc'
          rw [Array.mem_append] at hpc'
          rcases hpc' with h | h
          · exact hinit pc' h
          · exact hexp_good pc' h
        have hsub_tl : ∀ x ∈ tl, x ∈ bs :=
          fun x hx => hsub x (List.mem_cons_of_mem _ hx)
        exact expandPattern_foldlM_preserves_RefsDt bs ihcases tl
          (init ++ exp_hd) final hsub_tl hnew_init hfold

/-- Helper for the `.match` arm of `termToConcrete_preserves_RefsDt`. The
arm takes 3 paths (single-tuple irrefutable / single-array irrefutable /
general expandPattern fold). All produce concrete terms whose RefsDt
reduces to the body's RefsDt; the IHs `ihscrut` and `ihcases` provide
RefsDt for the recursively-lowered scrut/branch bodies.

Sub-paths (a) `destructureTuple` and (b) `destructureArray` are F=0 via
`destructureTuple_preserves_RefsDt` / `destructureArray_preserves_RefsDt`
helpers above. Sub-path (c) (general fold) is F=0 via
`expandPattern_preserves_RefsDt` + `expandPattern_foldlM_preserves_RefsDt`.
The `match`-arm dispatch composing them is F=1 below. -/
theorem termToConcrete_match_arm_preserves_RefsDt
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {cbody : Concrete.Term}
    (typ : Typ) (e : Bool) (scrut : Typed.Term) (bs : List (Pattern × Typed.Term))
    (_hwit : ∀ g,
      ((∃ dt, tds.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, tds.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd.getByKey g = some (.constructor dt c))))
    (ihscrut : ∀ {cs}, termToConcrete mono scrut = .ok cs → Concrete.Term.RefsDt cd cs)
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.RefsDt cd cb)
    (hrun : termToConcrete mono (.match typ e scrut bs) = .ok cbody) :
    Concrete.Term.RefsDt cd cbody := by
  -- Unfold the .match arm of termToConcrete and reduce the do-bind cascade.
  unfold termToConcrete at hrun
  simp only [bind, Except.bind, pure, Except.pure] at hrun
  split at hrun
  · cases hrun
  rename_i τ' _hτ
  split at hrun
  · cases hrun
  rename_i scrut' hscrut'
  -- scrut' must be a `.var ...` else `unsupportedMatchScrutinee` is thrown.
  split at hrun
  rotate_left
  · cases hrun
  rename_i _scrutTerm sty esc sl
  -- After this rename:
  --  sty : Concrete.Typ (typ of `.var`); esc : Bool (escape); sl : Local
  --  hscrut' : termToConcrete mono scrut = Except.ok (.var sty esc sl).
  -- The first split corresponds to:
  --   `match bs with | [(.tuple body_t, hbs_eq)] => <inner: match sty with | .tuple ts => ...> | _ => ...`
  split at hrun
  · -- bs = [(.tuple body_t, hbs_eq)].
    rename_i _orphan body_t hbs_eq
    -- Inner split: match sty with | .tuple ts => ... | _ => fallthrough.
    split at hrun
    · -- sty = .tuple ts.  hrun has `match termToConcrete mono hbs_eq with ...`
      rename_i ts
      split at hrun
      · cases hrun
      rename_i cb hcb
      simp only [Except.ok.injEq] at hrun
      subst hrun
      have hbs_mem : ((Pattern.tuple body_t, hbs_eq) : Pattern × Typed.Term)
          ∈ [(Pattern.tuple body_t, hbs_eq)] := List.mem_singleton.mpr rfl
      have hcbR : Concrete.Term.RefsDt cd cb := ihcases _ hbs_mem hcb
      have hscrutTermR : Concrete.Term.RefsDt cd
          (.var (Concrete.Typ.tuple ts) false sl) := .var
      exact destructureTuple_preserves_RefsDt _ body_t ts cb hscrutTermR hcbR
    · -- sty ≠ .tuple. Fallthrough.
      -- The inner match `[(P.tuple body_t, hbs_eq)] vs [(P.array ...)] is the wildcard.
      split at hrun
      · -- The "fired" array-singleton arm — contradiction:
        -- [(P.tuple body_t, hbs_eq)] = [(P.array pats, body)] forces tuple = array.
        rename_i _ _ _ _ habs
        simp only [List.cons.injEq, Prod.mk.injEq] at habs
        obtain ⟨⟨hp, _⟩, _⟩ := habs
        cases hp
      · -- Wildcard arm matched: hrun has the general foldlM path.
        split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_RefsDt
          [(Pattern.tuple body_t, hbs_eq)] ihcases
          [(Pattern.tuple body_t, hbs_eq)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
  · -- bs is NOT single-tuple-with-tuple-sty arm. Try array-singleton arm.
    split at hrun
    · -- bs = [(.array pats_a, body_a)]. 4 anonymous vars introduced.
      -- Trace state shows: bs✝ (orphan), _o1 (orphan), pats✝ (Array Pattern),
      -- body✝ (Typed.Term), then the negation hypothesis.
      rename_i _o1 _o2 pats_a body_a _hneg_tup
      split at hrun
      · -- sty = .array eltTyp n.
        rename_i eltTyp n
        split at hrun
        · cases hrun
        rename_i cb hcb
        simp only [Except.ok.injEq] at hrun
        subst hrun
        have hbs_mem : ((Pattern.array pats_a, body_a) : Pattern × Typed.Term)
            ∈ [(Pattern.array pats_a, body_a)] := List.mem_singleton.mpr rfl
        have hcbR : Concrete.Term.RefsDt cd cb := ihcases _ hbs_mem hcb
        have hscrutTermR : Concrete.Term.RefsDt cd
            (.var (Concrete.Typ.array eltTyp n) false sl) := .var
        exact destructureArray_preserves_RefsDt _ pats_a eltTyp cb hscrutTermR hcbR
      · -- sty ≠ .array. Fallthrough to general fold.
        split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_RefsDt
          [(Pattern.array pats_a, body_a)] ihcases
          [(Pattern.array pats_a, body_a)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
    · -- bs is NOT single-tuple AND NOT single-array. General path.
      split at hrun
      · cases hrun
      rename_i cases' hcases'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .match ?_ (fun d hd => by cases hd)
      rw [← Array.foldlM_toList] at hcases'
      intro pc hpc
      -- The fold uses an `attachWith` over bs.toArray; bridge via a foldlM equation
      -- that drops the subtype to the plain (Pattern × Typed.Term) shape.
      -- Build an `ihcases` for `bs.toArray.toList` (= bs), then apply the helper
      -- specialised to the attachWith subtype.
      let f_attach : Array (Concrete.Pattern × Concrete.Term) →
          { x // x ∈ bs.toArray } → Except ConcretizeError (Array (Concrete.Pattern × Concrete.Term)) :=
        fun acc y => do
          let cb ← termToConcrete mono y.1.snd
          let exp ← expandPattern sty sl y.1.fst cb
          pure (acc ++ exp)
      -- Recurse over the attachWith list.
      have key : ∀ (xs : List { x // x ∈ bs.toArray })
            (init final : Array (Concrete.Pattern × Concrete.Term)),
          (∀ pc' ∈ init, Concrete.Term.RefsDt cd pc'.2) →
          List.foldlM f_attach init xs = .ok final →
          ∀ pc' ∈ final, Concrete.Term.RefsDt cd pc'.2 := by
        intro xs
        induction xs with
        | nil =>
          intro init final hinit hfold
          simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
          subst hfold; exact hinit
        | cons hd tl ih =>
          intro init final hinit hfold
          rw [List.foldlM_cons] at hfold
          simp only [bind, Except.bind, f_attach] at hfold
          cases hcb_hd : termToConcrete mono hd.1.2 with
          | error _ => rw [hcb_hd] at hfold; cases hfold
          | ok cb_hd =>
            rw [hcb_hd] at hfold
            simp only at hfold
            cases hexp_hd : expandPattern sty sl hd.1.1 cb_hd with
            | error _ => rw [hexp_hd] at hfold; cases hfold
            | ok exp_hd =>
              rw [hexp_hd] at hfold
              simp only [pure, Except.pure] at hfold
              have hd_in_bs : hd.1 ∈ bs := by
                have := hd.2
                simpa using this
              have hcb_ref : Concrete.Term.RefsDt cd cb_hd :=
                ihcases _ hd_in_bs hcb_hd
              have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.RefsDt cd pc'.2 :=
                expandPattern_preserves_RefsDt hcb_ref hexp_hd
              have hnew_init : ∀ pc' ∈ init ++ exp_hd, Concrete.Term.RefsDt cd pc'.2 := by
                intro pc' hpc'
                rw [Array.mem_append] at hpc'
                rcases hpc' with h | h
                · exact hinit pc' h
                · exact hexp_good pc' h
              exact ih _ _ hnew_init hfold
      exact key _ #[] cases' (by intro pc' hpc'; simp at hpc') hcases' pc hpc

/-! #### `termToConcrete` preserves `RefsDt`.

Structural pass: every typed `Typed.Term.RefsDt tds body` whose
`.ref g` witnesses survive into `cd` (via `hwit`) lifts to
`Concrete.Term.RefsDt cd (termToConcrete mono body)`. The `mono` argument
only affects `typToConcrete` (type lowering), which doesn't influence
`RefsDt` — only term-level `.ref g` arms matter. -/
theorem termToConcrete_preserves_RefsDt
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {body : Typed.Term} {cbody : Concrete.Term}
    (hbody : Typed.Term.RefsDt tds body)
    (hwit : ∀ g,
      ((∃ dt, tds.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, tds.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd.getByKey g = some (.constructor dt c))))
    (hrun : termToConcrete mono body = .ok cbody) :
    Concrete.Term.RefsDt cd cbody := by
  induction hbody generalizing cbody with
  | unit =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .unit
  | var =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .var
  | @ref typ e g tArgs hdt =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    -- Sig amendment 2026-05-04: typed `.ref` only carries ctor witness; inject
    -- via `Or.inr` for the concrete-side `Concrete.Term.RefsDt.ref` premise.
    -- The new RefsDt-defect disjunct (`dt.params.isEmpty ∨ ¬ tArgs.isEmpty`)
    -- is bundled inside `hdt` — the concrete-side bridge `hwit` only consumes
    -- the `getByKey` witness, so we strip the disjunct here.
    obtain ⟨dt, c, hget, _hdisj⟩ := hdt
    exact .ref (hwit g (Or.inr ⟨dt, c, hget⟩))
  | field =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .field
  | @tuple typ e ts _hts ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .tuple ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @array typ e ts _hts ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .array ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @ret typ e r _ ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ret (ihr hr')
  | @«let» typ e pat v b _hv _hb ihv ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i v' hv'
    split at hrun
    · cases hrun
    rename_i b' hb'
    -- The pattern match decides letVar vs letWild.
    cases pat with
    | var x =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letVar (ihv hv') (ihb hb')
    | wildcard =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | field _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | ref _ _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | tuple _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | array _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | or _ _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | pointer _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
  | @«match» typ e scrut bs _hscrut _hcases ihscrut ihcases =>
    -- Delegated to the helper; passes the structural IHs for scrut and per-case bodies.
    exact termToConcrete_match_arm_preserves_RefsDt typ e scrut bs hwit
      (fun {cs} hcs => ihscrut hcs)
      (fun pc hpc {cb} hcb => ihcases pc hpc hcb)
      hrun
  | @app typ e g tArgs args u _hargs ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i args' hargs'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .app ?_
    intro a ha
    exact List.mem_mapM_ok_forall
      (P := fun x => x ∈ args) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) args args' (fun x hx => hx) hargs' a ha
  | @add typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .add (iha ha') (ihb hb')
  | @sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .sub (iha ha') (ihb hb')
  | @mul typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .mul (iha ha') (ihb hb')
  | @eqZero typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .eqZero (iha ha')
  | @proj typ e a n _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .proj (iha ha')
  | @get typ e a n _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .get (iha ha')
  | @slice typ e a i j _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .slice (iha ha')
  | @«set» typ e a n v _ _ iha ihv =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i v' hv'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .set (iha ha') (ihv hv')
  | @store typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .store (iha ha')
  | @load typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .load (iha ha')
  | @ptrVal typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ptrVal (iha ha')
  | @assertEq typ e a b r _ _ _ iha ihb ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .assertEq (iha ha') (ihb hb') (ihr hr')
  | @ioGetInfo typ e k _ ihk =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i k' hk'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioGetInfo (ihk hk')
  | @ioSetInfo typ e k i l r _ _ _ _ ihk ihi ihl ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i k' hk'
    split at hrun
    · cases hrun
    rename_i i' hi'
    split at hrun
    · cases hrun
    rename_i l' hl'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioSetInfo (ihk hk') (ihi hi') (ihl hl') (ihr hr')
  | @ioRead typ e i n _ ihi =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i i' hi'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioRead (ihi hi')
  | @ioWrite typ e d r _ _ ihd ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i d' hd'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioWrite (ihd hd') (ihr hr')
  | @u8BitDecomposition typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8BitDecomposition (iha ha')
  | @u8ShiftLeft typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8ShiftLeft (iha ha')
  | @u8ShiftRight typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8ShiftRight (iha ha')
  | @u8Xor typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Xor (iha ha') (ihb hb')
  | @u8Add typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Add (iha ha') (ihb hb')
  | @u8Sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Sub (iha ha') (ihb hb')
  | @u8And typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8And (iha ha') (ihb hb')
  | @u8Or typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Or (iha ha') (ihb hb')
  | @u8LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8LessThan (iha ha') (ihb hb')
  | @u32LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u32LessThan (iha ha') (ihb hb')
  | @debug typ e label tOpt r ht hr iht ihr =>
    -- Case-split tOpt UP FRONT so termToConcrete unfolds cleanly.
    cases htmatch : tOpt with
    | none =>
      rw [htmatch] at hrun
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      -- t' = none branch (no inner match needed since we go directly to pure none)
      split at hrun
      · cases hrun
      rename_i τ' _hτ
      split at hrun
      · cases hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .debug ?_ (ihr hr')
      intro tval htval; cases htval
    | some sub =>
      rw [htmatch] at hrun
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      split at hrun
      · cases hrun
      rename_i sub' hsub'
      split at hrun
      · cases hrun
      rename_i τ' _hτ
      split at hrun
      · cases hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .debug ?_ (ihr hr')
      intro tval htval
      -- htval : some sub' = some tval (after simp), htmatch : tOpt = some sub
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub htmatch hsub'

/-- Drain-state invariant: every newly-emitted function body satisfies
`Typed.Term.RefsDt tds`. Mirrors `NewFunctionsFO`. -/
@[expose] def DrainState.NewFunctionsTermRefsDt
    (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typed.Term.RefsDt tds f.body

theorem DrainState.NewFunctionsTermRefsDt.init
    {tds : Typed.Decls}
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFunctionsTermRefsDt tds
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

/-- Step preservation: `concretizeDrainEntry` keeps `NewFunctionsTermRefsDt`.
For the function-arm case, it pushes a new function whose body is
`substInTypedTerm subst f.body`. The `Typed.Term.RefsDt tds` predicate
transports across `substInTypedTerm` directly via
`substInTypedTerm_preserves_RefsDt` — substitution rewrites only `Typ`-level
annotations and leaves every `Typed.Term`-level global unchanged, so
the predicate's witnesses survive without needing `f.params = []`. -/
theorem concretizeDrainEntry_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTermRefsDt decls state) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          -- Body is `substInTypedTerm subst f.body`. `substInTypedTerm` rewrites
          -- only `Typ`-level annotations, leaving `Typed.Term`-level globals
          -- (`.ref _ _ g _`, `.app _ _ g _ _ _`) verbatim. So `RefsDt decls`
          -- transports across `substInTypedTerm` regardless of `f.params`.
          exact substInTypedTerm_preserves_RefsDt (hP entry.1 f hf_get)
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f hf; exact hinv f hf
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewFunctionsTermRefsDt decls state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : DrainState.NewFunctionsTermRefsDt decls s'' :=
        concretizeDrainEntry_preserves_NewFunctionsTermRefsDt hP hinv0 hd hs''
      exact ih s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTermRefsDt decls state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewFunctionsTermRefsDt decls state0 := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTermRefsDt hP
    state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewFunctionsTermRefsDt decls init)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    DrainState.NewFunctionsTermRefsDt decls drained := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : DrainState.NewFunctionsTermRefsDt decls state' :=
          concretizeDrainIter_preserves_NewFunctionsTermRefsDt hP hinv hstate'
        exact ih state' hinv' hdrain

-- `concretizeBuild_preserves_TermRefsDt` relocated to
-- `ConcretizeSound/TermRefsDtBridge.lean` 2026-05-04 (downstream of `Phase4`
-- so its body has access to `concretizeBuild_function_origin_with_body` from
-- `TypesNotFunction.lean`, which lives downstream of this file in the import
-- order via Shapes → Layout → StageExtract → RefsDt).

/-! #### `step4Lower` fold: typed-side → concrete-side `TermRefsDt`.

Each typed function body becomes its `termToConcrete` lowering. We need
`Concrete.Term.RefsDt cd (termToConcrete _ body)` from
`Typed.Term.RefsDt monoDecls body`, using bridges between dt/ctor keys
across the lowering step. Crucially, `step4Lower`'s function/dataType/
constructor arms preserve dt/ctor key-witnesses bijectively. -/

/-- Function-key inversion for the `step4Lower` fold: every `.function cf`
entry in the post-fold `concDecls` originates from a `.function f` entry in
`monoDecls` at the same key, with `cf.body = (termToConcrete emptyMono f.body)`.

Replay of `step4Lower_fold_kind_at_key`'s split strategy specialised to the
function arm. -/
theorem step4Lower_fold_function_origin
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cf : Concrete.Function}
    (hcf_get : concDecls.getByKey g = some (.function cf))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ f : Typed.Function,
      monoDecls.getByKey g = some (.function f) ∧
      termToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) f.body = .ok cf.body := by
  -- Define a fold-level invariant on Concrete.Decls states:
  -- `P acc := every .function entry in acc has body = termToConcrete _ f.body
  --   for some f keyed identically in monoDecls`.
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ g' cf', acc.getByKey g' = some (.function cf') →
      ∃ f' : Typed.Function,
        monoDecls.getByKey g' = some (.function f') ∧
        termToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) f'.body = .ok cf'.body
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hPdefault : P (default : Concrete.Decls) := by
    intro g' cf' hget
    exfalso
    have hne : (default : Concrete.Decls).getByKey g' = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[g']?).bind _ = none
      have : (default : Concrete.Decls).indices[g']? = none := by
        show ((default : Std.HashMap Global Nat))[g']? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  have hfinal : P concDecls := by
    apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
    · exact hPdefault
    intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    intro g' cf' hget
    cases d with
    | function f =>
      -- step4Lower on .function f: inserts `.function cf_step` at name where
      -- cf_step.body = termToConcrete _ f.body.
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      rename_i cInputs hInputs
      split at hstep
      · cases hstep
      rename_i cOutput hOutput
      split at hstep
      · cases hstep
      rename_i cBody hBody
      simp only [Except.ok.injEq] at hstep
      subst hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
        subst hget
        refine ⟨f, ?_, ?_⟩
        · exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
        · exact hBody
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
    | dataType dt =>
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
    | constructor dt c =>
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      split at hstep
      · cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
  exact hfinal g cf hcf_get

-- `step4Lower_fold_preserves_TermRefsDt` and `concretize_preserves_TermRefsDt`
-- are defined further below, AFTER the dt/ctor bridges, which themselves are
-- defined AFTER `indexMap_pairs_key_unique` (so they can use it directly).


end Aiur

end -- public section
