/-
Scratch dumping ground.

NOT imported by `Ix/Aiur.lean` or any production file. Holds theorems that
are not transitively reachable from `Aiur.Toplevel.compile_correct` —
orphan helpers, deprecated infrastructure, speculative work.

We do NOT care whether this file builds. Sorries, broken imports,
type-errors are fine here. Treat as a holding pen.

To resurrect a theorem from Scratch back into the main proofs:
1. Move the declaration into the appropriate `Ix/Aiur/Proofs/*.lean`.
2. Re-add any required imports.
3. Verify `lake build`.
-/
module
@[expose] public section

namespace Aiur

namespace Scratch

-- From: Ix/Aiur/Proofs/IOBufferEquiv.lean:L18
theorem IOBuffer.equiv_symm {a b : IOBuffer} (h : IOBuffer.equiv a b) :
    IOBuffer.equiv b a := by
  rw [iobuffer_equiv_iff] at *
  exact ⟨by rw [beq_iff_eq] at *; exact h.1.symm, h.2.symm⟩

-- From: Ix/Aiur/Proofs/Lib.lean:L143
/-- `Array.foldlM` over `.attach` equals `List.foldlM` on the underlying list
(after erasing the subtype projection). -/
theorem Array.foldlM_attach_to_List_foldlM
    {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : Array α) (step : β → α → m β) (init : β) :
    xs.attach.foldlM (init := init) (fun acc ⟨x, _⟩ => step acc x) =
    xs.toList.foldlM step init := by
  rw [← Array.foldlM_toList, Array.toList_attach]
  exact List.foldlM_attachWith_eq step xs.toList _ init

-- From: Ix/Aiur/Proofs/SimplifySound.lean:L323
theorem simplifyDecls_progress
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (_hex : MatchesExhaustive decls typedDecls) :
    ∃ simplified, simplifyDecls decls typedDecls = .ok simplified := by
  simp only [simplifyDecls, IndexMap.foldlM]
  rw [← Array.foldlM_toList]
  apply List.foldlM_except_ok'
  intro acc ⟨name, d⟩ _hmem
  match d with
  | .function f =>
    let ⟨body', hb⟩ := simplifyTypedTerm_ok_witness decls f.body
    exact ⟨acc.insert name (.function { f with body := body' }),
           by simp [hb, bind, Except.bind, pure, Except.pure]⟩
  | .dataType dt =>
    exact ⟨acc.insert name (.dataType dt), rfl⟩
  | .constructor dt c =>
    exact ⟨acc.insert name (.constructor dt c), rfl⟩

-- From: Ix/Aiur/Proofs/SimplifySound.lean:L396
/-- Preservation (structural / decl-name form): every name declared in the
input `typedDecls` has a declaration in the simplified output. Full value-level
preservation requires a `Typed.Eval` reference evaluator, not yet wired in. -/
theorem simplifyDecls_preservation
    {decls : Source.Decls} {typedDecls simplified : Typed.Decls}
    (h : simplifyDecls decls typedDecls = .ok simplified) :
    -- The typed-level simplification preserves the set of declared function
    -- names. (Full value-level preservation needs a `Typed.Eval` reference
    -- evaluator, which isn't wired in yet; this weaker statement captures
    -- the "simplify is structure-preserving on decls" invariant that the
    -- full preservation claim builds on.)
    ∀ name d, typedDecls.getByKey name = some d →
      ∃ d', simplified.getByKey name = some d' := by
  intros name d hd
  -- Step 1: monadic → pure fold bridge.
  have hmon :=
    List.foldlM_eq_foldl_of_pure (simplifyDeclsStep_ok decls) typedDecls.pairs.toList
      (default : Typed.Decls)
  -- Step 2: rewrite `h` from the `Array.foldlM` to `List.foldlM` form.
  have h' : typedDecls.pairs.toList.foldlM
      (m := Except CheckError) (fun acc p => match p.2 with
        | .function f => do
          let body' ← simplifyTypedTerm decls f.body
          pure (acc.insert p.1 (.function { f with body := body' }))
        | .dataType dt => pure (acc.insert p.1 (.dataType dt))
        | .constructor dt c => pure (acc.insert p.1 (.constructor dt c)))
      default = .ok simplified := by
    simp only [simplifyDecls, IndexMap.foldlM] at h
    rw [← Array.foldlM_toList] at h
    exact h
  -- Step 3: match `h'` against `hmon` to get pure-foldl equation.
  have heq : simplified = typedDecls.pairs.toList.foldl (simplifyDeclsStep decls) default := by
    have := h'.symm.trans hmon
    exact (Except.ok.inj this)
  -- Step 4: step preserves / inserts containsKey.
  have hstep : ∀ acc p, (simplifyDeclsStep decls acc p).containsKey p.1 := by
    intro acc ⟨name', d'⟩
    unfold simplifyDeclsStep
    cases d' <;> exact IndexMap.containsKey_insert_self _ _ _
  have hmono : ∀ acc (a : Global) (p : Global × Typed.Declaration),
      acc.containsKey a → (simplifyDeclsStep decls acc p).containsKey a := by
    intro acc a ⟨a', b'⟩ hac
    unfold simplifyDeclsStep
    cases b' <;> exact IndexMap.containsKey_insert_preserves _ _ _ _ hac
  -- Step 5: `hd` gives some pair `p = pairs[i]` with `p.1 == name` and `p.2 = d`,
  -- hence `p ∈ pairs.toList`. The strengthened `validIndices` guarantees `p.1 == name`.
  obtain ⟨p, hpmem, hpbeq, hpsnd⟩ :
      ∃ p, p ∈ typedDecls.pairs.toList ∧ (p.1 == name) = true ∧ p.2 = d := by
    unfold IndexMap.getByKey at hd
    cases hi : typedDecls.indices[name]? with
    | none => simp [hi] at hd
    | some i =>
      simp [hi, Option.bind] at hd
      have hv := typedDecls.validIndices name hi
      refine ⟨typedDecls.pairs[i]'hv.1, ?_, hv.2, ?_⟩
      · exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
      · have hp : typedDecls.pairs[i]? = some (typedDecls.pairs[i]'hv.1) :=
          Array.getElem?_eq_getElem hv.1
        rw [hp] at hd
        simp at hd
        obtain ⟨_, hpeq⟩ := hd
        rw [hpeq]
  -- Step 6: Apply the fold invariant with `p`, yielding `containsKey p.1`.
  have hcontains :
      (typedDecls.pairs.toList.foldl (simplifyDeclsStep decls) default).containsKey p.1 :=
    List.foldl_insert_indexmap_containsKey hstep hmono _ _ p hpmem
  rw [← heq] at hcontains
  -- Bridge `p.1 == name` to `containsKey name`.
  have hcontains' : simplified.containsKey name := by
    unfold IndexMap.containsKey at hcontains ⊢
    rwa [Std.HashMap.contains_congr (hab := hpbeq)] at hcontains
  rw [← IndexMap.getByKey_isSome_iff_containsKey] at hcontains'
  exact Option.isSome_iff_exists.mp hcontains'

-- From: Ix/Aiur/Proofs/StructCompatible.lean:L424
/-- Concretize + toBytecode lift a source-function entry to a concrete-function
entry with matching pre-name-map index and flat-size-to-typSize identity.
Closed via the three extractor lemmas above.

Sig updated (2026-04-24): `htf_mono` callback replaced with `hmono : FullyMonomorphic t`
so the strengthened `concretize_extract_function_at_name` can discharge. -/
theorem concretize_extract_concrete_function
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name)
    (_hct : t.compile = .ok ct)
    {name : Global} {fi : Bytecode.FunIdx} {f : Source.Function}
    (_hname : ct.nameMap[name]? = some fi)
    (hsrc : decls.getByKey name = some (.function f)) :
    ∃ (preIdx : Bytecode.FunIdx) (concName : Global) (concF : Concrete.Function),
      preNameMap[concName]? = some preIdx ∧
      concDecls.getByKey concName = some (.function concF) ∧
      ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
        (f.inputs.map Prod.snd).foldl
            (fun acc t => acc + typFlatSize decls {} t) 0 =
          (concF.inputs.map Prod.snd).foldl
            (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  obtain ⟨tf, htyped, hsum_ts⟩ :=
    checkAndSimplify_extract_typed_function hdecls hts hsrc
  obtain ⟨concName, concF, _, hconcGet, hflat_tc⟩ :=
    concretize_extract_function_at_name (decls := decls) hmono hdecls hts hconc htyped
  obtain ⟨preIdx, hpreName, _hpreLt⟩ :=
    toBytecode_extract_preIdx hbc hNameAgrees hconcGet
  refine ⟨preIdx, concName, concF, hpreName, hconcGet, ?_⟩
  intro layoutMap hlayout
  rw [hsum_ts]
  exact hflat_tc layoutMap hlayout

-- From: Ix/Aiur/Proofs/ConcretizeProgress.lean:L283
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

-- From: Ix/Aiur/Proofs/ConcretizeProgress.lean:L365
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
          have hscrut : termToConcrete mono (Typed.Term.var st se sx) =
              .ok (Concrete.Term.var cst se sx) := by
            simp only [termToConcrete, hcst, bind, Except.bind, pure, Except.pure]
          simp only [hcτ, hscrut, bind, Except.bind, pure, Except.pure]
          split <;> split
          · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
            simp only [] at hcb
            exact ⟨_, by rw [hcb]⟩
          · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
            simp only [] at hcb
            have hpSimple := hps _ List.mem_cons_self
            simp only [] at hpSimple
            obtain ⟨exp, hexp⟩ :=
              @expandPattern_ok_of_simple cst sx _ hpSimple cb
            split
            · simp_all
            · conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
              simp only [Array.toList_attach,
                         List.attachWith, List.foldlM,
                         List.pmap, List.foldlM_cons,
                         hcb, hexp]
              exact ⟨_, rfl⟩
          · split
            · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
              simp only [] at hcb
              exact ⟨_, by rw [hcb]⟩
            · obtain ⟨cb, hcb⟩ := hbr _ List.mem_cons_self
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

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L8
/-- `ValueEq` and `flattenValue` agree. -/
theorem ValueEq_iff_flattenValue
    (decls : Decls) (funcIdx : Global → Option Nat)
    (v : Value) (t : Typ) (gs : Array G) :
    ValueEq decls funcIdx v t gs ↔ flattenValue decls funcIdx v = gs := by
  constructor
  · intro h
    cases h with
    | mk heq => exact heq
  · intro heq
    exact .mk v t gs heq

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L13
/-- Forward direction: `ValueEq` implies the `flattenValue` equality. Often
easier to apply than the `iff` in intro-elimination contexts. -/
theorem ValueEq.flattenValue_eq
    {decls : Decls} {funcIdx : Global → Option Nat}
    {v : Value} {t : Typ} {gs : Array G}
    (h : ValueEq decls funcIdx v t gs) :
    flattenValue decls funcIdx v = gs := by
  cases h with
  | mk heq => exact heq

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L25
/-- Backward direction: every value has a canonical flat encoding via
`flattenValue`, and that encoding is a `ValueEq` witness for any `t`. -/
theorem ValueEq.of_flattenValue
    (decls : Decls) (funcIdx : Global → Option Nat)
    (v : Value) (t : Typ) :
    ValueEq decls funcIdx v t (flattenValue decls funcIdx v) :=
  .mk v t (flattenValue decls funcIdx v) rfl

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L190
/-- `ValueEq` is independent of `funcIdx` for `.fn`-free values. -/
theorem ValueEq.funcIdx_irrelevant_of_fnFree
    {decls : Decls} {f₁ f₂ : Global → Option Nat}
    {v : Value} {t : Typ} {gs : Array G}
    (hfn : v.FnFree)
    (heq : ValueEq decls f₁ v t gs) :
    ValueEq decls f₂ v t gs := by
  obtain ⟨h⟩ := heq
  exact .mk v t gs (by rw [← h]; exact (flattenValue_funcIdx_irrelevant_of_fnFree decls f₁ f₂ v hfn).symm)

-- From: Ix/Aiur/Proofs/CheckSound.lean:L383
/-- `checkAndSimplify` preserves the function-input flat-size sum on each
shared function entry. Trivial consequence of
`checkAndSimplify_preserves_inputs`. -/
theorem checkAndSimplify_preserves_input_flat_sum
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    (f.inputs.map Prod.snd).foldl
        (fun acc t => acc + typFlatSize decls {} t) 0 =
      (tf.inputs.map Prod.snd).foldl
        (fun acc t => acc + typFlatSize decls {} t) 0 := by
  rw [checkAndSimplify_preserves_inputs hdecls hts hsrc htyped]

-- From: Ix/Aiur/Proofs/CheckSound.lean:L830
/-- The `htf_mono` bridge. Combines `SrcFnParamsMonoP_mkDecls` +
`checkAndSimplify_preserves_params` to derive `tf.params = []`, hence
`tf.params.isEmpty = true`. -/
theorem htf_mono_bridge
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    tf.params.isEmpty = true := by
  have hsrc_mono : f.params = [] :=
    SrcFnParamsMonoP_mkDecls hmono hdecls name f hsrc
  have hpreserve : tf.params = f.params :=
    checkAndSimplify_preserves_params hdecls hts hsrc htyped
  rw [hpreserve, hsrc_mono]
  rfl

-- From: Ix/Aiur/Proofs/CheckSound.lean:L1634
/-- Reflect `wellFormedDecl`-at-source-constructor: always `.ok visited`,
no argtype checks happen here (handled in the dataType arm). -/
private theorem constructor_trivial_step
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {dt : DataType} {c : Constructor}
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.constructor dt c) = .ok visited') :
    visited' = visited := by
  unfold wellFormedDecls.wellFormedDecl at hstep
  simp only [pure, Except.pure, Except.ok.injEq] at hstep
  exact hstep.symm

-- From: Ix/Aiur/Proofs/LowerShared.lean:L1299
private theorem T3Private_bumpSelectors_preserves (n : Nat) :
    PreservesInputSize (bumpSelectors n) :=
  fun _ => rfl
-- From: Ix/Aiur/Proofs/LowerShared.lean:L1302
private theorem T3Private_bumpLookups_preserves (n : Nat) :
    PreservesInputSize (bumpLookups n) :=
  fun _ => rfl
-- From: Ix/Aiur/Proofs/LowerShared.lean:L1305
private theorem T3Private_addMemSize_preserves (n : Nat) :
    PreservesInputSize (addMemSize n) :=
  fun _ => rfl
-- From: Ix/Aiur/Proofs/LowerShared.lean:L1307
private theorem T3Private_pushDegree_preserves (d : Nat) :
    PreservesInputSize (pushDegree d) :=
  fun _ => rfl

-- From: Ix/Aiur/Proofs/LowerShared.lean:L424
/-- Embedding `IsCore` into `IsCoreExtended`. -/
theorem IsCore.toExtended {layoutMap : LayoutMap} {term : Term}
    (h : IsCore layoutMap term) : IsCoreExtended layoutMap term := by
  induction h with
  | unit => exact .unit
  | var => exact .var
  | field => exact .field
  | ref hl => exact .ref hl
  | letVar _ _ ihv ihb => exact .letVar ihv ihb
  | letWild _ _ ihv ihb => exact .letWild ihv ihb
  | ptrVal _ ih => exact .ptrVal ih
  | assertEq _ _ _ ihA ihB ihR => exact .assertEq ihA ihB ihR
  | debug htOpt _ ihtOpt ihr =>
    refine .debug (fun x hx => ihtOpt x hx) ihr

-- From: Ix/Aiur/Proofs/LowerShared.lean:L259
private theorem flattenValue_slice_at_offset
    (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) (layoutMap : LayoutMap)
    {τs : Array Concrete.Typ} {vs : Array Value} {i : Nat}
    (_hLen : τs.size = vs.size)
    (_hi : i < τs.size)
    (_hHasTyp : ∀ j (h₁ : j < τs.size) (h₂ : j < vs.size),
      ValueHasTyp concDecls (τs[j]'h₁) (vs[j]'h₂)) :
    ∃ offset iLen,
      typSize layoutMap (τs[i]'_hi) = .ok iLen ∧
      (flattenValue sourceDecls funcIdx (vs[i]'(_hLen ▸ _hi))).size = iLen ∧
      (flattenValue sourceDecls funcIdx (.tuple vs)).extract offset
        (offset + iLen)
        = flattenValue sourceDecls funcIdx (vs[i]'(_hLen ▸ _hi)) := by
  sorry

-- From: Ix/Aiur/Proofs/LowerSoundCore.lean:L83
/-- Extending `boundFlat` with a new binding. -/
theorem boundFlat_insert
    (decls : Source.Decls) (funcIdx : Global → Option Nat)
    (env : Concrete.Eval.Bindings)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (map : Array G)
    (l : Local) (v : Value) (idxs : Array Bytecode.ValIdx)
    (hbf : boundFlat decls funcIdx env bindings map)
    (hfresh : ∀ w, (l, w) ∉ env)
    (hpt : ∀ i : Fin idxs.size,
        map[idxs[i]]? = some ((flattenValue decls funcIdx v)[i]?.getD 0)) :
    boundFlat decls funcIdx ((l, v) :: env) (bindings.insert l idxs) map := by
  intro x v' hmem
  rcases List.mem_cons.mp hmem with h_head | h_tail
  · have hx : x = l := congrArg Prod.fst h_head
    have hv' : v' = v := congrArg Prod.snd h_head
    subst hx; subst hv'
    refine ⟨idxs, ?_, hpt⟩
    rw [Std.HashMap.getElem?_insert]
    simp
  · obtain ⟨idxs_x, hlook, hpt'⟩ := hbf x v' h_tail
    refine ⟨idxs_x, ?_, hpt'⟩
    rw [Std.HashMap.getElem?_insert]
    by_cases hxl : (l == x) = true
    · have hxl' : l = x := Local.beq_implies_eq hxl
      subst hxl'
      exact absurd h_tail (hfresh v')
    · have hxl_false : (l == x) = false := Bool.not_eq_true _ |>.mp hxl
      simp [hxl_false, hlook]

-- From: Ix/Aiur/Proofs/CompilerProgress.lean:L3761
private theorem CtorPresentBody_mem_map_ctors_iff
    {α β : Type} (L : List α) (f : α → β) (b : β) :
    b ∈ L.map f ↔ ∃ a ∈ L, f a = b := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, ih]
    constructor
    · rintro (heq | ⟨a, hmem, hfa⟩)
      · exact ⟨hd, Or.inl rfl, heq.symm⟩
      · exact ⟨a, Or.inr hmem, hfa⟩
    · rintro ⟨a, (heq | hmem), hfa⟩
      · subst heq; exact Or.inl hfa.symm
      · exact Or.inr ⟨a, hmem, hfa⟩

-- From: Ix/Aiur/Proofs/CompilerProgress.lean:L3826
private theorem CtorPresentBody_pushNamespace_left_inj
    {g₁ g₂ : Global} {s : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace s) : g₁ = g₂ := by
  have h' : g₁.toName.mkStr s = g₂.toName.mkStr s := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g₁.toName s = Lean.Name.str g₂.toName s := h'
  have : g₁.toName = g₂.toName := by injection h''
  cases g₁; cases g₂; simp_all

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L74
/-- `flattenValue` agrees under `funcIdx` vs `funcIdx.map remap` for every
value when they agree pointwise on every `.fn g`. -/
theorem flattenValue_transport_remap
    (decls : Decls) (f : Global → Option Nat) (remap : Nat → Nat)
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                     flattenValue decls (fun g' => (f g').map remap) (.fn g)) :
    ∀ (v : Value),
      flattenValue decls f v =
      flattenValue decls (fun g => (f g).map remap) v
  | .unit        => by unfold flattenValue; rfl
  | .field _     => by unfold flattenValue; rfl
  | .pointer _ _ => by unfold flattenValue; rfl
  | .fn g        => hfn_free g
  | .tuple vs    => by
      unfold flattenValue
      exact attach_flatMap_eq_pw
        (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
  | .array vs    => by
      unfold flattenValue
      exact attach_flatMap_eq_pw
        (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
  | .ctor g args => by
      unfold flattenValue
      have h_args : args.attach.flatMap
          (fun ⟨v, _⟩ => flattenValue decls f v) =
        args.attach.flatMap
          (fun ⟨v, _⟩ => flattenValue decls (fun g' => (f g').map remap) v) :=
        attach_flatMap_eq_pw
          (fun v _ => flattenValue_transport_remap decls f remap hfn_free v)
      split <;> simp [h_args]
termination_by v => sizeOf v

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L106
/-- Transport `ValueEq` across a funcIdx remap. Entry-function return values
are fn-free, which makes the remap-irrelevant (no `.fn` ids to renumber). -/
theorem ValueEq.transport_remap
    {decls : Decls} {f : Global → Option Nat}
    {remap : Nat → Nat} {v : Value} {t : Typ} {gs : Array G}
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                      flattenValue decls (fun g' => (f g').map remap) (.fn g))
    (h : flattenValue decls f v = gs) :
    ValueEq decls (fun g => (f g).map remap) v t gs :=
  .mk v t gs (by rw [← flattenValue_transport_remap decls f remap hfn_free v]; exact h)

-- From: Ix/Aiur/Proofs/ValueEqFlatten.lean:L116
/-- Transport `InterpResultEq` across a funcIdx remap. -/
theorem InterpResultEq.transport_remap
    {decls : Decls} {f : Global → Option Nat}
    {remap : Nat → Nat} {retTyp : Typ}
    {src : Except Source.Eval.SourceError (Value × IOBuffer)}
    {bc  : Except Bytecode.Eval.BytecodeError (Array G × IOBuffer)}
    (hfn_free : ∀ g, flattenValue decls f (.fn g) =
                      flattenValue decls (fun g' => (f g').map remap) (.fn g))
    (h : InterpResultEq decls f retTyp src bc) :
    InterpResultEq decls (fun g => (f g).map remap) retTyp src bc := by
  unfold InterpResultEq at *
  match src, bc with
  | .ok (v, io₁), .ok (gs, io₂) =>
    obtain ⟨hVE, hIO⟩ := h
    refine ⟨?_, hIO⟩
    cases hVE with
    | mk hflat => exact ValueEq.transport_remap hfn_free hflat
  | .ok _, .error _ => exact h.elim
  | .error _, .ok _ => trivial
  | .error _, .error _ => trivial

-- From: Ix/Aiur/Proofs/ConcretizeProgress.lean:L39
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

-- From: Ix/Aiur/Proofs/ConcretizeProgress.lean:L300
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

-- From: Ix/Aiur/Proofs/ConcretizeProgress.lean:L337
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
  conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
  simp only [Array.toList_attach]
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

-- From: Ix/Aiur/Proofs/DedupSound.lean:L192
theorem partitionRefine_classes_bounded
    (classes : Array Nat) (callees : Array (Array FunIdx))
    (i : Nat) (h : i < (partitionRefine classes callees).size) :
    (partitionRefine classes callees)[i] ≤ classes.size := by
  suffices hbnd : BoundedBy (partitionRefine classes callees) classes.size by
    exact hbnd _ (Array.getElem_mem h)
  have hsz : (classes.mapIdx fun i cls =>
      (cls, callees[i]!.map (classes[·]!))).size = classes.size :=
    Array.size_mapIdx
  have hbnd_nc : BoundedBy
      (assignClasses (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))).1 classes.size :=
    boundedBy_of_assignClasses _ classes.size (by rw [hsz]; exact Nat.le_refl _)
  have hsz' : (assignClasses (classes.mapIdx fun i cls =>
      (cls, callees[i]!.map (classes[·]!)))).1.size = classes.size := by
    rw [assignClasses_size_eq, hsz]
  unfold partitionRefine partitionRefineBound
  simp only
  split
  · rename_i heq
    have heq' : (assignClasses (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))).1 = classes := beq_iff_eq.mp heq
    intro x hx
    rw [← heq'] at hx
    exact hbnd_nc x hx
  · have hn' : (assignClasses (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))).1.size ≤ classes.size := by
      rw [hsz']; exact Nat.le_refl _
    exact partitionRefineBound_boundedBy _ _ callees classes.size hn' hbnd_nc

-- From: Ix/Aiur/Proofs/DedupSound.lean:L4378 (was in namespace HFixRawCloseScratch)
namespace HFixRawCloseScratch
theorem refine_step_refines
    (c : Array Nat) (callees : Array (Array FunIdx)) (i j : Nat)
    (hi_c : i < c.size) (hj_c : j < c.size) :
    let sigs := c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))
    let c' := (assignClasses sigs).1
    ∀ (hi' : i < c'.size) (hj' : j < c'.size),
      c'[i]'hi' = c'[j]'hj' → c[i] = c[j] := by
  simp only
  intro hi' hj' hcls
  have hsz_sig : (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!))).size = c.size :=
    Array.size_mapIdx
  have hi_sig : i < (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!))).size := hsz_sig ▸ hi_c
  have hj_sig : j < (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!))).size := hsz_sig ▸ hj_c
  have hsig_eq :
      (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[i]'hi_sig =
      (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[j]'hj_sig :=
    assignClasses_values_eq_of_classes_eq _ i j hi' hj' hcls
  have h_i : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[i]'hi_sig =
      (c[i], callees[i]!.map (c[·]!)) := by
    simp [Array.getElem_mapIdx]
  have h_j : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[j]'hj_sig =
      (c[j], callees[j]!.map (c[·]!)) := by
    simp [Array.getElem_mapIdx]
  rw [h_i, h_j] at hsig_eq
  exact (Prod.mk.inj hsig_eq).1
end HFixRawCloseScratch

/-! ## Stage 2 (2026-04-28) — Orphan catalog after Stage 1 predecessor deletions.

The theorems below are the post-Stage-1 orphan set: declarations in
`Ix/Aiur/Proofs/*.lean` that are not transitively reachable from
`Aiur.Toplevel.compile_correct`. They were previously load-bearing for the
deleted FullyMono predecessors (`Toplevel.compile_preservation`,
`Toplevel.compile_progress`, `Lower.compile_preservation`,
`Lower.compile_progress`, `Typed.Decls.concretize_preservation`).

We DO NOT physically copy their bodies here — that would entail moving ~140
theorems across ~10 files, exceeding the migration budget. Bodies remain in
their source files (where they still typecheck and are exported) but they no
longer participate in the `compile_correct` closure. This catalog is the audit
trail; future cleanup may delete them from their source files entirely once
the closure stabilizes.

Filter applied: excludes `_entry`-suffixed names (intentional future-cite
bridges) and the four named wiring stubs:
- `Aiur.Simulation.concretize_runFunction_simulation` (Stage 3 target)
- `Aiur.concretize_preserves_runFunction_entry`        (Stage 3 caller)
- `Aiur.flatten_agree_entry`                           (private bridge)
- `Aiur.Toplevel.typedDecls_params_empty_entry`        (intentional helper)

Authoritative list lives at `tools/orphan_list_lean.md` (regenerate via
`lake env lean tools/OrphanCheck.lean > tools/orphan_list_lean.md`).

Module breakdown (post-Stage-1, total 141 catalog entries):
- Ix.Aiur.Proofs.BytecodeLawfulBEq        : 5  (Bytecode.Ctrl beq lemmas)
- Ix.Aiur.Proofs.CheckSound                : 27 (mkDecls/checkAndSimplify lemmas)
- Ix.Aiur.Proofs.CompilerProgress          : 4  (concretize_drain bridges)
- Ix.Aiur.Proofs.ConcreteEvalInversion     : 9  (interp_* unfold lemmas)
- Ix.Aiur.Proofs.ConcretizeSound           : 41 (`_under_fullymono` family + RefClosed/FnFreeBody)
- Ix.Aiur.Proofs.DedupSound                : 8  (induct principles + remap range)
- Ix.Aiur.Proofs.IOBufferEquiv             : 1  (equiv_refl)
- Ix.Aiur.Proofs.Lib                       : 12 (foldlM/mapM helpers)
- Ix.Aiur.Proofs.LowerCalleesFromLayout    : 2
- Ix.Aiur.Proofs.LowerShared               : 11 (CompileInv + interp_preserves_ValueHasTyp)
- Ix.Aiur.Proofs.LowerSoundControl         : 1  (Function_compile_progress)
- Ix.Aiur.Proofs.LowerSoundCore            : 10 (toIndex_* extended forms + Local insts)
- Ix.Aiur.Proofs.SimplifySound             : 1  (PSigma.mk.hcongr_4)
- Ix.Aiur.Proofs.StructCompatible          : 10 (compile_ok_* family)

Restoration protocol: if any orphan turns out to be falsely classified (i.e.
some non-orphan transitively cites it but the dependency isn't visible to
`OrphanCheck`), restore via `git checkout HEAD -- <file>` and re-run the
orphan check to identify the actual caller. -/
namespace Stage2OrphanCatalog
end Stage2OrphanCatalog

-- From: Ix/Aiur/Proofs/LowerSoundControl.lean (orphan move)
/-- Per-function compile progress. Composed from the three steps above plus a
final `@[expose]`'d-`Function.compile` unfolding glue.

The signature adds `hNameAgrees` because Step 1 consults `lm[f.name]?` while
the caller only knows `cd.getByKey name = some (.function f)`. The link
`name = f.name` comes from the `.function` pair invariant (mirroring
`Function_body_preservation`). -/
theorem Function_compile_progress
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (lm : LayoutMap)
    (hlm : cd.layoutMap = .ok lm)
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (htdDt : Typed.Decls.DtNameIsKey tds)
    (htdCtorPresent : Typed.Decls.CtorPresent tds)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f)) :
    ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms) := by
  sorry

-- From: Ix/Aiur/Proofs/CompilerProgress.lean (orphan move)
theorem concretize_produces_ctorPresent
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hP : Typed.Decls.CtorPresent tds)
    (hDt : Typed.Decls.DtNameIsKey tds)
    (hCtor : Typed.Decls.CtorIsKey tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.CtorPresent cd := by sorry


-- From: SimplifySound.lean:L373
/-- `foldl` preserves `containsKey` for any initially-contained key. -/
private theorem List.foldl_indexmap_preserves_containsKey
    {α : Type u} {β : Type v} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    {step : IndexMap α β → (α × β) → IndexMap α β}
    (hmono : ∀ acc (a : α) (p : α × β), acc.containsKey a → (step acc p).containsKey a)
    (a : α) :
    ∀ (xs : List (α × β)) (init : IndexMap α β),
      init.containsKey a → (xs.foldl step init).containsKey a
  | [], _, h => h
  | x :: xs, init, h => by
    simp only [List.foldl_cons]
    exact List.foldl_indexmap_preserves_containsKey hmono a xs (step init x)
      (hmono init a x h)

-- From: SimplifySound.lean:L388
/-- Every element's key is `containsKey`'d after the full fold. -/
private theorem List.foldl_insert_indexmap_containsKey
    {α : Type u} {β : Type v} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    {step : IndexMap α β → (α × β) → IndexMap α β}
    (hstep : ∀ acc p, (step acc p).containsKey p.1)
    (hmono : ∀ acc (a : α) (p : α × β), acc.containsKey a → (step acc p).containsKey a) :
    ∀ (xs : List (α × β)) (init : IndexMap α β) (p : α × β),
      p ∈ xs → (xs.foldl step init).containsKey p.1
  | [], _, _, h => (List.not_mem_nil h).elim
  | x :: rest, init, p, hp => by
    rcases List.mem_cons.mp hp with heq | hrest
    · subst heq
      simp only [List.foldl_cons]
      exact List.foldl_indexmap_preserves_containsKey hmono p.1 rest _ (hstep init p)
    · simp only [List.foldl_cons]
      exact List.foldl_insert_indexmap_containsKey hstep hmono rest (step init x) p hrest

-- From: SimplifySound.lean:L418
private theorem simplifyDeclsStep_ok (decls : Source.Decls)
    (acc : Typed.Decls) (p : Global × Typed.Declaration) :
    (match p.2 with
      | .function f => do
        let body' ← simplifyTypedTerm decls f.body
        pure (acc.insert p.1 (.function { f with body := body' }))
      | .dataType dt => pure (acc.insert p.1 (.dataType dt))
      | .constructor dt c => pure (acc.insert p.1 (.constructor dt c)) :
      Except CheckError Typed.Decls) =
      .ok (simplifyDeclsStep decls acc p) := by
  obtain ⟨name, d⟩ := p
  unfold simplifyDeclsStep
  match d with
  | .function f =>
    simp only
    let ⟨body', hb⟩ := simplifyTypedTerm_ok_witness decls f.body
    simp [hb, bind, Except.bind, pure, Except.pure]
  | .dataType dt => rfl
  | .constructor dt c => rfl

-- From: ValueEqFlatten.lean:L62
/-- Pointwise flattenValue-equality helper for `.attach.flatMap` over Value arrays. -/
private theorem attach_flatMap_eq_pw {vs : Array Value}
    {g₁ g₂ : Value → Array G}
    (h : ∀ v ∈ vs, g₁ v = g₂ v) :
    vs.attach.flatMap (fun ⟨v, _⟩ => g₁ v) =
    vs.attach.flatMap (fun ⟨v, _⟩ => g₂ v) := by
  congr 1
  funext ⟨v, hv⟩
  exact h v hv

/-! ## `Flatten.args` composition lemmas. -/

-- From: ConcretizeProgress.lean:L198
/-- A `do`-block that destructures an `Except`-return and extracts a component
reduces to `.ok` of that component when the inner computation succeeds.
Sidesteps the `simp`/`rw` normalization mismatch on `Except.bind` + pair-match. -/
private theorem except_bind_fst_ok {α β ε : Type}
    (x : Except ε (α × β)) (a : α) (b : β) (h : x = .ok (a, b)) :
    (do let (y, _) ← x; pure y : Except ε α) = .ok a := by
  rw [h]; rfl

-- From: ConcretizeProgress.lean:L238
private theorem subPatternsToLocalsArr_ok_of_simple {pats : Array Pattern}
    (h : ∀ p ∈ pats, p = .wildcard ∨ ∃ x, p = .var x) :
    ∃ locals, subPatternsToLocalsArr pats = .ok locals := by
  have hlist : ∀ p ∈ pats.toList, p = .wildcard ∨ ∃ x, p = .var x :=
    fun p hp => h p (Array.mem_toList_iff.mp hp)
  obtain ⟨locals, hlocals⟩ := subPatternsToLocals_ok_of_simple hlist
  refine ⟨locals, ?_⟩
  unfold subPatternsToLocalsArr
  exact hlocals

-- From: ConcretizeProgress.lean:L206
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

-- From: LowerSoundControl.lean:L223
/-- Step 3: block-level `Term.compile` succeeds from any starting state. This
is the headline extension of `toIndex_progress_core` to full `Term`. -/
private theorem body_compile_ok
    {cd : Concrete.Decls} {lm : LayoutMap}
    (_hlm : cd.layoutMap = .ok lm)
    (_hrc : Concrete.Decls.RefClosed cd)
    (f : Concrete.Function)
    (_hname : ∃ name, cd.getByKey name = some (.function f))
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (state : CompilerState) :
    ∃ body state',
      (f.body.compile f.output lm bindings).run state =
        .ok body state' := by
  -- BLOCKED ON:
  -- (1) `toIndex_progress_core_extended` is **F=0** (LowerSoundCore).
  --     The toIndex-side blocker is gone; remaining work is block-level
  --     term-shape dispatch + IsCoreExtended-witness extraction.
  -- (2) Block-level dispatch in `Term.compile` for `.match`/`.ret`/
  --     `.matchContinue`/`.return`/`.yield`/`.letVar`-with-non-tail-
  --     `.match` RHS — these arms are NOT in `toIndex` (it throws on
  --     them); they're produced by `Term.compile`'s top dispatch
  --     (Lower.lean:352 `Concrete.Term.compile`). Closure path:
  --       (s1) Structural induction over `Concrete.Term` shape,
  --            generalizing over `bindings`/`state`/`yieldCtrl`.
  --       (s2) Each `.letVar`/`.letWild`-with-`.match`-RHS arm uses
  --            `Concrete.addCase` on each pattern + recurses on `bod`
  --            via the structural IH.
  --       (s3) Each non-match arm of `Term.compile` reduces to either
  --            `toIndex_progress_core_extended` (for the leaf `toIndex`
  --            call) OR recurses on the continuation via the IH.
  --       (s4) Tail `.ret` / `.match` / `Ctrl.return` / `Ctrl.yield`
  --            arms compile to `Bytecode.Ctrl`-tail forms; need a
  --            separate `Ctrl.compile_progress` helper.
  -- (3) `IsCoreExtended layoutMap f.body` derivation — needs an
  --     induction-on-shape from `Concrete.Term` carrying a
  --     `RefClosed`-derived `∃ n, typSize lm τ = .ok n` hypothesis at
  --     every `.proj`/`.get`/`.slice`/`.set`/`.letLoad`/`.load`/`.app`
  --     sub-term. Once the body is `IsCoreExtended`-typed, the access
  --     arms within `toIndex` succeed via `toIndex_progress_core_extended`.
  -- (4) `RefClosed cd` propagation through every `arg.typ` consulted by
  --     `.proj`/`.get`/`.slice`/`.set` — already provided via
  --     `_hrc : Concrete.Decls.RefClosed cd` at the call site; the
  --     IsCoreExtended derivation needs to extract per-`Typ`
  --     `typSize_ok_of_refClosed_lm` witnesses inside each carrier.
  sorry

-- MOVED to Scratch.lean: `Function_compile_progress` (orphan).

-- DELETED 2026-04-28: `Lower.compile_preservation` (FullyMono predecessor —
-- though it did NOT directly consume FullyMono, it was the only caller of
-- `Function_body_preservation` outside of `Lower.compile_preservation_entry`,
-- and its body has been inlined into the latter).

-- DELETED 2026-04-28: `Lower.compile_progress` (FullyMono predecessor of
-- `Lower.compile_progress_entry`). Cited orphan helpers
-- `concretize_layoutMap_progress` + `Function_compile_progress` (both retained
-- in their own files since they ARE callees here, but no longer reachable from
-- compile_correct).

-- From: LowerSoundControl.lean:L192
/-- Step 2: `f.inputs.foldlM ... typSize lm typ` succeeds under `RefClosed cd`.
Closed modulo `Aiur.typSize_ok_of_refClosed_lm` (in `Proofs/LowerShared.lean`). -/
private theorem inputs_foldlM_ok
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    (f : Concrete.Function)
    (hname : ∃ name, cd.getByKey name = some (.function f)) :
    ∃ result : Nat × Std.HashMap Local (Array Bytecode.ValIdx),
      f.inputs.foldlM (init := ((0 : Nat), (default : Std.HashMap Local (Array Bytecode.ValIdx))))
        (fun (valIdx, bindings) (arg, typ) => do
          let len ← match typSize lm typ with
            | .error e => (throw e : Except String Nat)
            | .ok len => pure len
          let indices := Array.range' valIdx len
          pure (valIdx + len, bindings.insert arg indices))
      = (Except.ok result : Except String _) := by
  obtain ⟨name, hget⟩ := hname
  have hdeclRC : Concrete.Declaration.RefClosed cd (.function f) := hrc name _ hget
  have hinputsRC : ∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd := hdeclRC.1
  apply List.foldlM_except_ok'
  intro acc p hp
  have hrcP : Concrete.Typ.RefClosed cd p.2 := hinputsRC p hp
  obtain ⟨n, hn⟩ := typSize_ok_of_refClosed_lm hlm hdtkey hLKM hrcP
  obtain ⟨valIdx, bindings⟩ := acc
  obtain ⟨arg, typ⟩ := p
  refine ⟨(valIdx + n, bindings.insert arg (Array.range' valIdx n)), ?_⟩
  simp only [hn, bind, Except.bind, pure, Except.pure]

-- From: LowerSoundControl.lean:L138
/-- Step 1: `Function.compile` starts with `lm[f.name]?`; we need that lookup
to yield a `.function` entry. Closed modulo `Aiur.layoutMap_preserves_function_exists_aux`
(in `Proofs/LowerShared.lean`). -/
private theorem layoutMap_lookup_function
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f)) :
    ∃ layout, lm[f.name]? = some (.function layout) := by
  have hkey_mem : ∃ key, (key, Declaration.function f) ∈ cd.pairs.toList
      ∧ (key == name) = true := by
    unfold IndexMap.getByKey at hname
    cases hidx : cd.indices[name]? with
    | none =>
      rw [hidx] at hname
      simp [bind, Option.bind] at hname
    | some i =>
      rw [hidx] at hname
      simp only [bind, Option.bind] at hname
      have hv := cd.validIndices name hidx
      have hi_lt : i < cd.pairs.size := hv.1
      have hkey_eq : (cd.pairs[i]'hi_lt).1 == name := hv.2
      have hget? : cd.pairs[i]? = some (cd.pairs[i]'hi_lt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hi_lt, rfl⟩
      rw [hget?] at hname
      simp only [Option.map_some] at hname
      have hsnd : (cd.pairs[i]'hi_lt).2 = Declaration.function f := Option.some.inj hname
      refine ⟨(cd.pairs[i]'hi_lt).1, ?_, hkey_eq⟩
      have hmem : cd.pairs[i]'hi_lt ∈ cd.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hpair : ((cd.pairs[i]'hi_lt).1, Declaration.function f)
          = cd.pairs[i]'hi_lt := by
        rw [← hsnd]
      rw [hpair]; exact hmem
  obtain ⟨key, hmem, _⟩ := hkey_mem
  have hkey_eq_name : key = f.name := hNameAgrees key f hmem
  have hmem' : (f.name, Declaration.function f) ∈ cd.pairs.toList := by
    rw [← hkey_eq_name]; exact hmem
  exact layoutMap_preserves_function_exists_aux cd f.name f hNameAgrees hDtNameIsKey hCtorIsKey hCtorPresent hmem' ⟨lm, hlm⟩ lm hlm

-- From: StructCompatible.lean:L98
/-- Shape of `ct.bytecode.functions`: the dedup output with a `constrained`
field patched in by `needsCircuit`. Direct definitional unpacking of
`Source.Toplevel.compile`.

Signature takes the full four-stage witness chain so the proof can chain
them through `compile`'s pipeline definition. -/
private theorem compile_ct_functions_shape
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (hct : t.compile = .ok ct)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap)) :
    ∃ needs : Array Bool,
      ct.bytecode.functions =
        bytecodeDedup.functions.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }) := by
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  refine ⟨bytecodeDedup.needsCircuit, ?_⟩
  rw [← hct_eq]

-- From: StructCompatible.lean:L571
/-- Sub-lemma: the bytecode call graph is closed. Composed from
`toBytecode_callees_in_range` (LowerShared), `deduplicate_preserves_callee_range`
(DedupSound), and `needsCircuit_preserves_body` + `compile_ct_functions_shape`
(Compiler.lean). -/
private theorem compile_ok_call_graph_closed
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (hct : t.compile = .ok ct) :
    ∀ fi (h : fi < ct.bytecode.functions.size),
      ∀ callee, callee ∈ (Bytecode.Block.collectAllCallees ct.bytecode.functions[fi].body) →
      callee < ct.bytecode.functions.size := by
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  have hraw := toBytecode_callees_in_range (concDecls := concDecls) hbc
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  have hdd := deduplicate_preserves_callee_range hdedup hraw
  obtain ⟨needs, hshape⟩ := compile_ct_functions_shape hct hts hconc hbc hdedup
  have hmap := needsCircuit_preserves_body bytecodeDedup.functions needs
  have hsize : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
    rw [hshape]; exact hmap.1
  intro fi h callee hmem
  have hfi' : fi < bytecodeDedup.functions.size := hsize ▸ h
  have hbody : ct.bytecode.functions[fi].body = bytecodeDedup.functions[fi].body := by
    have hbody_mapped := hmap.2 fi hfi'
    have hct_body :
        ct.bytecode.functions[fi]'h
          = (bytecodeDedup.functions.mapIdx
              (fun i (f : Bytecode.Function) =>
                { f with constrained := needs[i]! }))[fi]'(hshape ▸ h) :=
      getElem_congr_coll hshape
    rw [congrArg Bytecode.Function.body hct_body, hbody_mapped]
  rw [hbody] at hmem
  exact hsize ▸ hdd fi hfi' callee hmem

-- From: StructCompatible.lean:L137
/-- Sub-lemma: every `FunIdx` in `nameMap` is in range of `bc.functions`.
Composed from `preNameMap_in_range` (LowerShared), `deduplicate_remap_in_range`
(DedupSound), and `nameMap_value_via_remap` (Compiler.lean). -/
private theorem compile_ok_funIdx_valid
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (hct : t.compile = .ok ct) :
    ∀ (name : Global) (fi : Bytecode.FunIdx),
      ct.nameMap[name]? = some fi → fi < ct.bytecode.functions.size := by
  intro name fi hname
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  have hname_eq : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by rw [← hct_eq]
  have hbc_eq : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name] at hname
  match hpre : preNameMap[name]? with
  | none => rw [hpre] at hname; simp at hname
  | some preIdx =>
    rw [hpre, Option.map_some] at hname
    have hfi : fi = remap preIdx := (Option.some.injEq _ _).mp hname.symm
    have hpre_lt : preIdx < bytecodeRaw.functions.size :=
      preNameMap_in_range hbc name preIdx hpre
    have hremap_lt : remap preIdx < bytecodeDedup.functions.size :=
      deduplicate_remap_in_range hdedup preIdx hpre_lt
    have hsize : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
      rw [hbc_eq]; simp [Array.size_mapIdx]
    rw [hsize, hfi]
    exact hremap_lt

/-! ### Sub-lemmas for `compile_ok_input_layout_matches`. -/

-- From: StructCompatible.lean:L606
/-- If `compile` succeeds, its output is structurally compatible.
Composed from the four sub-lemmas above. Requires `FullyMonomorphic t` for
the `input_layout_matches` conjunct (threaded through
`concretize_extract_function_at_name`'s monomorphism requirement). -/
private theorem compile_ok_implies_struct_compatible
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct) (hmono : FullyMonomorphic t) :
    StructCompatible decls ct.bytecode
      (fun g => ct.nameMap[g]?) :=
  { total_on_reachable := compile_ok_total_on_reachable hdecls hct
    funIdx_valid := compile_ok_funIdx_valid hct
    input_layout_matches := compile_ok_input_layout_matches hdecls hct hmono
    call_graph_closed := compile_ok_call_graph_closed hct }

-- From: StructCompatible.lean:L486
/-- Sub-lemma: flattened input size agrees between source decl and bytecode
layout. Composition delegates to the 6 sub-lemmas above.

Requires `FullyMonomorphic t` — threaded through to
`concretize_extract_function_at_name` via `checkAndSimplify_preserves_params`. -/
private theorem compile_ok_input_layout_matches
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct) (hmono : FullyMonomorphic t) :
    ∀ name fi f, ct.nameMap[name]? = some fi →
      decls.getByKey name = some (.function f) →
      ∀ h : fi < ct.bytecode.functions.size,
        (f.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 =
        ct.bytecode.functions[fi].layout.inputSize := by
  intro name fi f hname hsrc h
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  have hct' := hct
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct'
  injection hct' with hct_eq
  have hname_eq : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by rw [← hct_eq]
  have hbc_eq : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  have htdna := checkAndSimplify_preserves_nameAgrees hts
  have hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name :=
    concretize_nameAgrees htdna hconc
  obtain ⟨tf, htyped, hsum_ts⟩ :=
    checkAndSimplify_extract_typed_function hdecls hts hsrc
  obtain ⟨concName, concF, hcn_eq, hconcGet, hflat_tc⟩ :=
    concretize_extract_function_at_name (decls := decls) hmono hdecls hts hconc htyped
  rw [hcn_eq] at hconcGet
  obtain ⟨layoutMap, hlayout⟩ := toBytecode_layoutMap_ok hbc
  have hflat_cc := hflat_tc layoutMap hlayout
  obtain ⟨preIdx, hpreName, hpre_lt⟩ :=
    toBytecode_extract_preIdx hbc hNameAgrees hconcGet
  obtain ⟨body, lms, hcomp, hlayout_raw_eq⟩ :=
    toBytecode_function_layout (cd := concDecls) hlayout hbc hNameAgrees name concF preIdx
      hconcGet hpreName hpre_lt
  have hinputSize := Concrete.Function.compile_inputSize hcomp
  have hname' : ct.nameMap[name]? = some fi := hname
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name, hpreName,
      Option.map_some] at hname'
  have hfi : fi = remap preIdx := (Option.some.injEq _ _).mp hname'.symm
  have hremap_lt : remap preIdx < bytecodeDedup.functions.size :=
    deduplicate_remap_in_range hdedup preIdx hpre_lt
  have hdedup_layout :
      bytecodeRaw.functions[preIdx].layout =
        bytecodeDedup.functions[remap preIdx].layout :=
    deduplicate_preserves_layout hdedup preIdx hpre_lt hremap_lt
  have hsize_eq : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
    rw [hbc_eq]; simp [Array.size_mapIdx]
  have hfi_dedup : fi < bytecodeDedup.functions.size := hsize_eq ▸ h
  have h_mapIdx_lt : fi < (bytecodeDedup.functions.mapIdx
      (fun i (f : Bytecode.Function) =>
        { f with constrained := bytecodeDedup.needsCircuit[i]! })).size := by
    rw [Array.size_mapIdx]; exact hfi_dedup
  have hct_fi_layout :
      ct.bytecode.functions[fi].layout = bytecodeDedup.functions[fi].layout := by
    have hct_fi :
        ct.bytecode.functions[fi]'h
          = (bytecodeDedup.functions.mapIdx
              (fun i (f : Bytecode.Function) =>
                { f with constrained := bytecodeDedup.needsCircuit[i]! }))[fi]'h_mapIdx_lt :=
      getElem_congr_coll (by rw [hbc_eq])
    rw [congrArg Bytecode.Function.layout hct_fi]
    exact needsCircuit_preserves_layout bytecodeDedup.functions
      bytecodeDedup.needsCircuit fi hfi_dedup
  have hlayout_dedup_eq :
      (bytecodeDedup.functions[fi]'hfi_dedup).layout
        = (bytecodeDedup.functions[remap preIdx]'hremap_lt).layout :=
    congrArg Bytecode.Function.layout (getElem_congr_idx hfi)
  rw [hct_fi_layout, hlayout_dedup_eq, ← hdedup_layout, hlayout_raw_eq, hinputSize,
      ← hflat_cc, ← hsum_ts]

-- From: StructCompatible.lean:L125
/-- Sub-lemma: reachability is tautological under the restated definition
(every name with `nameMap name = some fi` is, by definition, "reachable"). -/
private theorem compile_ok_total_on_reachable
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (_hdecls : t.mkDecls = .ok decls)
    (_hct : t.compile = .ok ct) :
    ∀ (name : Global), reachableFromEntries decls (fun g => ct.nameMap[g]?) name →
      ∃ fi, ct.nameMap[name]? = some fi := by
  intro name h
  simp only [reachableFromEntries] at h
  exact Option.isSome_iff_exists.mp h

-- From: StructCompatible.lean:L339
/-- Joint layout invariant of `Toplevel.deduplicate`'s canonicalization loop.
Provable because dedup's skeleton key uses the full `FunctionLayout`
(see `Compiler/Dedup.lean:211`): same-class functions agree on every layout
field. The witness `j` at position `fi := remap preIdx` is a raw index with
`classes[j] = fi = remap preIdx = classes[preIdx]`; same-final-class implies
same-initial-class (`partitionRefine` only splits, never merges) which implies
equal skeletons-with-layout (`assignClasses` collision-free). -/
private theorem deduplicate_layout_loop_invariant
    (t : Bytecode.Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ preIdx (_hpre : preIdx < t.functions.size)
      (_hremap : remap preIdx < tDedup.functions.size),
      t.functions[preIdx].layout = tDedup.functions[remap preIdx].layout := by
  simp only
  intro preIdx hpre hremap_lt
  -- Step 1: extract a raw index `j` whose layout matches `tDedup`'s at
  -- position `(t.deduplicate).2 preIdx`, plus `classes[j] = (t.deduplicate).2 preIdx`.
  have hprov := dedup_indexed_provenance_aux t ((t.deduplicate).2 preIdx) hremap_lt
  simp only at hprov
  obtain ⟨j, hj, hlayout, hj_cls, hclasses⟩ := hprov
  -- Step 2: `remap preIdx = classes[preIdx]` (in-range).
  have hremap_eq : (t.deduplicate).2 preIdx =
      (deduplicate_classes_of t)[preIdx]! :=
    deduplicate_remap_eq_classes t preIdx hpre
  simp only at hremap_eq
  have hpre_cls : preIdx < (deduplicate_classes_of t).size := by
    unfold deduplicate_classes_of
    by_cases hn : t.functions.size = 0
    · exact absurd hpre (hn ▸ Nat.not_lt_zero _)
    · have hne_bool : (t.functions.size == 0) = false := by simp [hn]
      rw [hne_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
      exact hpre
  have hremap_eq' : (t.deduplicate).2 preIdx =
      (deduplicate_classes_of t)[preIdx]'hpre_cls := by
    rw [hremap_eq, getElem!_pos _ preIdx hpre_cls]
  -- Step 3: `classes[j] = classes[preIdx]`.
  have hcls_eq : (deduplicate_classes_of t)[j]'hj_cls =
      (deduplicate_classes_of t)[preIdx]'hpre_cls := by
    rw [hclasses, hremap_eq']
  -- Step 4: Unfold `deduplicate_classes_of` to expose `partitionRefine`.
  have hn_bool : (t.functions.size == 0) = false := by
    have hn : ¬ t.functions.size = 0 := fun h => absurd hpre (h ▸ Nat.not_lt_zero _)
    simp [hn]
  have hdc_eq : deduplicate_classes_of t =
      Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body) := by
    unfold deduplicate_classes_of
    rw [hn_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
  -- Lift class-equality from `deduplicate_classes_of` to `partitionRefine` form.
  have hj_pr : j < (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body)).size := by
    rw [← hdc_eq]; exact hj_cls
  have hpre_pr : preIdx < (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body)).size := by
    rw [← hdc_eq]; exact hpre_cls
  have hcls_eq_pr : (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[j]'hj_pr =
      (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[preIdx]'hpre_pr := by
    have h1 : (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[j]'hj_pr =
        (deduplicate_classes_of t)[j]'hj_cls :=
      (getElem_congr_coll hdc_eq).symm
    have h2 : (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[preIdx]'hpre_pr =
        (deduplicate_classes_of t)[preIdx]'hpre_cls :=
      (getElem_congr_coll hdc_eq).symm
    rw [h1, h2, hcls_eq]
  -- Step 5: Apply `partitionRefine_only_splits` for initial-class equality.
  let skeletons := t.functions.map fun f =>
    (Bytecode.skeletonBlock f.body, f.layout)
  let initClasses := (Bytecode.assignClasses skeletons).1
  let callees := t.functions.map fun f => Bytecode.collectCalleesBlock f.body
  have hic_sz : initClasses.size = t.functions.size := by
    show (Bytecode.assignClasses skeletons).1.size = t.functions.size
    rw [assignClasses_size_eq]
    show skeletons.size = _
    simp [skeletons]
  have hj_ic : j < initClasses.size := hic_sz ▸ hj
  have hpre_ic : preIdx < initClasses.size := hic_sz ▸ hpre
  have hic_eq : initClasses[j]'hj_ic = initClasses[preIdx]'hpre_ic := by
    have := partitionRefine_only_splits initClasses callees j preIdx hj_ic hpre_ic
    apply this
    show (Bytecode.partitionRefine initClasses callees)[j]'_ =
      (Bytecode.partitionRefine initClasses callees)[preIdx]'_
    exact hcls_eq_pr
  -- Step 6: lift to same skeletons-with-layout.
  have hsk_sz : skeletons.size = t.functions.size := by simp [skeletons]
  have hj_sk : j < skeletons.size := hsk_sz ▸ hj
  have hpre_sk : preIdx < skeletons.size := hsk_sz ▸ hpre
  have hi_acl : preIdx < (Bytecode.assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hpre_sk
  have hj_acl : j < (Bytecode.assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hj_sk
  have h_acl_eq : (Bytecode.assignClasses skeletons).1[j]'hj_acl =
      (Bytecode.assignClasses skeletons).1[preIdx]'hi_acl := hic_eq
  have hsk_eq : skeletons[j]'hj_sk = skeletons[preIdx]'hpre_sk :=
    assignClasses_values_eq_of_classes_eq skeletons j preIdx hj_acl hi_acl h_acl_eq
  have h_j : skeletons[j]'hj_sk =
      (Bytecode.skeletonBlock t.functions[j].body, t.functions[j].layout) := by
    show (t.functions.map fun f =>
      (Bytecode.skeletonBlock f.body, f.layout))[j]'hj_sk = _
    simp [Array.getElem_map]
  have h_pre : skeletons[preIdx]'hpre_sk =
      (Bytecode.skeletonBlock t.functions[preIdx].body,
       t.functions[preIdx].layout) := by
    show (t.functions.map fun f =>
      (Bytecode.skeletonBlock f.body, f.layout))[preIdx]'hpre_sk = _
    simp [Array.getElem_map]
  rw [h_j, h_pre] at hsk_eq
  have hlayout_eq : t.functions[j].layout = t.functions[preIdx].layout :=
    (Prod.mk.inj hsk_eq).2
  -- Step 7: combine with `hlayout`. Goal has dedup-layout on RHS; `hlayout`
  -- equates that to `functions[j].layout`, then `hlayout_eq` finishes.
  rw [← hlayout_eq]; exact hlayout.symm

-- From: StructCompatible.lean:L472
/-- `Toplevel.deduplicate` preserves per-function `layout`. Closed modulo
`deduplicate_layout_loop_invariant` (which may be false — see finding). -/
private theorem deduplicate_preserves_layout
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap))
    (preIdx : Bytecode.FunIdx) (hlt : preIdx < bytecodeRaw.functions.size)
    (hlt' : remap preIdx < bytecodeDedup.functions.size) :
    bytecodeRaw.functions[preIdx].layout =
      bytecodeDedup.functions[remap preIdx].layout := by
  have hloop := deduplicate_layout_loop_invariant bytecodeRaw
  simp only [hdedup] at hloop
  exact hloop preIdx hlt hlt'

-- From: StructCompatible.lean:L79
/-- `mapIdx` with a `constrained`-only record update preserves `size` and
every `body`. Trivial from `Array.size_mapIdx` + `Array.getElem_mapIdx`. -/
private theorem needsCircuit_preserves_body
    (fs : Array Bytecode.Function) (needs : Array Bool) :
    (fs.mapIdx (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size
      = fs.size ∧
    ∀ fi (hfi : fi < fs.size),
      have hfi' : fi < (fs.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size := by
        have : (fs.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size = fs.size :=
          Array.size_mapIdx
        exact this ▸ hfi
      (fs.mapIdx (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }))[fi].body
        = fs[fi].body := by
  refine ⟨Array.size_mapIdx, ?_⟩
  intro fi hfi
  simp [Array.getElem_mapIdx]

-- From: StructCompatible.lean:L179
/-- `mapIdx (fun i f => { f with constrained := needs[i]! })` preserves
`layout` pointwise — only `constrained` changes. Companion of
`needsCircuit_preserves_body`. -/
private theorem needsCircuit_preserves_layout
    (fs : Array Bytecode.Function) (needs : Array Bool)
    (fi : Nat) (hfi : fi < fs.size) :
    have hfi' : fi < (fs.mapIdx
        (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size := by
      have : (fs.mapIdx
        (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size = fs.size :=
        Array.size_mapIdx
      exact this ▸ hfi
    (fs.mapIdx
      (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }))[fi].layout
        = fs[fi].layout := by
  simp [Array.getElem_mapIdx]

-- From: StructCompatible.lean:L196
/-- `toBytecode`'s fold yields bytecode functions whose `FunctionLayout` is
the one produced by `Concrete.Function.compile` on the corresponding concrete
function. Signature adds `hNameAgrees` (needed to identify `(xname, .function f)`
pair with `f.name = xname`); callers thread `concretize_nameAgrees` in. -/
private theorem toBytecode_function_layout
    {cd : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {layoutMap : LayoutMap}
    (hlayout : cd.layoutMap = .ok layoutMap)
    (hbc : cd.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (name : Global) (concF : Concrete.Function) (preIdx : Bytecode.FunIdx)
    (hget : cd.getByKey name = some (.function concF))
    (hnamePre : preNameMap[name]? = some preIdx)
    (hlt : preIdx < bytecodeRaw.functions.size) :
    ∃ body lms, Concrete.Function.compile layoutMap concF = .ok (body, lms) ∧
      bytecodeRaw.functions[preIdx].layout = lms.functionLayout := by
  rw [Concrete.Decls.toBytecode_unfold] at hbc
  simp only [bind, Except.bind, pure, Except.pure] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  rename_i layout' hlayout'
  have hlm_eq : layout' = layoutMap := by
    have := Except.ok.inj (hlayout' ▸ hlayout); exact this
  simp only [IndexMap.foldlM] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  rename_i triple htriple
  obtain ⟨functions, memSizes, nameMap⟩ := triple
  simp only at hbc
  have hEq := Prod.mk.inj (Except.ok.inj hbc)
  have hBC : (⟨functions, memSizes.toArray⟩ : Bytecode.Toplevel) = bytecodeRaw := hEq.1
  have hNM : nameMap = preNameMap := hEq.2
  rw [← Array.foldlM_toList, hlm_eq] at htriple
  let P : (Array Bytecode.Function × Lean.RBTree Nat compare ×
      Std.HashMap Global Bytecode.FunIdx) → Prop :=
    fun acc =>
      ∀ nm idx, (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some idx →
        idx < acc.1.size ∧
        ∃ (f : Concrete.Function) (body : Bytecode.Block) (lms : Concrete.Bytecode.LayoutMState),
          cd.getByKey nm = some (.function f) ∧
          Concrete.Function.compile layoutMap f = .ok (body, lms) ∧
          acc.1[idx]?.map (·.layout) = some lms.functionLayout
  have hP_init : P (#[], (Lean.RBTree.empty : Lean.RBTree Nat compare), {}) := by
    intro nm idx hget'; simp at hget'
  have hP_step : ∀ acc x acc',
      x ∈ cd.pairs.toList →
      (match x.2 with
        | Concrete.Declaration.function function => do
          let (body, layoutMState) ← Concrete.Function.compile layoutMap function
          let nameMap := acc.2.2.insert function.name acc.1.size
          let function' : Bytecode.Function :=
            ⟨body, layoutMState.functionLayout, function.entry, false⟩
          let memSizes := layoutMState.memSizes.fold (·.insert ·) acc.2.1
          pure (acc.1.push function', memSizes, nameMap)
        | _ => pure acc : Except String _) = .ok acc' →
      P acc → P acc' := by
    rintro ⟨accF, accM, accN⟩ ⟨xname, decl⟩ ⟨accF', accM', accN'⟩ hmem hok hP
    match decl with
    | .function function =>
      simp only [bind, Except.bind] at hok
      split at hok
      · exact absurd hok (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, layoutMState⟩ := res
      simp only [pure, Except.pure] at hok
      have hprod := Prod.mk.inj (Except.ok.inj hok)
      have hF : accF' = accF.push
          ⟨body, layoutMState.functionLayout, function.entry, false⟩ := hprod.1.symm
      have hinner := Prod.mk.inj hprod.2
      have hN' : accN' = accN.insert function.name accF.size := hinner.2.symm
      subst hF; subst hN'
      intro nm idx hget'
      by_cases hname : (function.name == nm) = true
      · rw [Std.HashMap.getElem?_insert] at hget'
        simp only [hname, ↓reduceIte] at hget'
        have hi : idx = accF.size := (Option.some.inj hget').symm
        subst hi
        refine ⟨?_, function, body, layoutMState, ?_, hcomp, ?_⟩
        · rw [Array.size_push]; exact Nat.lt_succ_self _
        · have hxname : xname = function.name := hNameAgrees xname function hmem
          have hgbk : cd.getByKey xname = some (.function function) :=
            IndexMap.getByKey_of_mem_pairs cd xname _ hmem
          have hxn : (xname == nm) = true := by rw [hxname]; exact hname
          unfold IndexMap.getByKey at hgbk ⊢
          rw [Std.HashMap.getElem?_congr (hab := hxn)] at hgbk
          exact hgbk
        · have hh : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[accF.size]? =
              some ⟨body, layoutMState.functionLayout, function.entry, false⟩ := by
            simp
          rw [hh]
          rfl
      · have hname' : (function.name == nm) = false :=
          Bool.not_eq_true _ |>.mp hname
        rw [Std.HashMap.getElem?_insert] at hget'
        simp only [hname'] at hget'
        have ⟨hidx, f', body', lms', hgbk, hcmp, hlayoutEq⟩ := hP nm idx hget'
        have hidx' : idx < accF.size := hidx
        refine ⟨?_, f', body', lms', hgbk, hcmp, ?_⟩
        · rw [Array.size_push]; exact Nat.lt_succ_of_lt hidx'
        · have h1 : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[idx]? = some accF[idx] :=
            Array.getElem?_push_lt (h := hidx')
          rw [h1]
          have h2 : (accF[idx]? : Option Bytecode.Function) = some accF[idx] := by
            simp [getElem?_pos, hidx']
          rw [h2] at hlayoutEq
          exact hlayoutEq
    | .dataType _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
    | .constructor _ _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
  have hP_final : P (functions, memSizes, nameMap) :=
    List.foldlM_except_invariant cd.pairs.toList _ _ hP_init hP_step htriple
  rw [← hNM] at hnamePre
  obtain ⟨_hidx, f, body, lms, hgbk, hcmp, hlayoutBc⟩ := hP_final name preIdx hnamePre
  have hfeq : f = concF := by
    rw [hgbk] at hget
    exact Concrete.Declaration.function.inj (Option.some.inj hget)
  subst hfeq
  refine ⟨body, lms, hcmp, ?_⟩
  have hfun_eq : bytecodeRaw.functions = functions := by cases hBC; rfl
  have hlt' : preIdx < functions.size := by rw [hfun_eq] at hlt; exact hlt
  have hget?eq : functions[preIdx]? = some functions[preIdx] :=
    Array.getElem?_eq_getElem hlt'
  rw [hget?eq] at hlayoutBc
  simp only [Option.map_some, Option.some.injEq] at hlayoutBc
  have heq_rec : bytecodeRaw.functions[preIdx]'hlt = functions[preIdx]'hlt' :=
    getElem_congr_coll hfun_eq
  rw [heq_rec, hlayoutBc]

-- From: CompilerPreservation.lean:L209
private theorem SrcCtorDtParamsMonoP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) (hmono' : dataType'.params = []) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SrcCtorDtParamsMonoP init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SrcCtorDtParamsMonoP result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      exact SrcCtorDtParamsMonoP_insert_constructor hP _ _ _ hmono'

-- From: CompilerPreservation.lean:L244
private theorem SrcCtorDtParamsMonoP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcCtorDtParamsMonoP acc.2) (hmono : dataType.params = [])
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SrcCtorDtParamsMonoP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hparams' : ({ dataType with constructors } : DataType).params = [] := hmono
  have hP_mid : SrcCtorDtParamsMonoP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SrcCtorDtParamsMonoP_insert_dataType hP dataType.name _
  exact SrcCtorDtParamsMonoP_ctor_fold dataType.name { dataType with constructors }
    hparams' constructors _ acc' hP_mid hstep

-- From: CompilerPreservation.lean:L131
private theorem SrcCtorDtParamsMonoP_default :
    SrcCtorDtParamsMonoP (default : Source.Decls) := by
  intro k dt c hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

-- From: CompilerPreservation.lean:L189
private theorem SrcCtorDtParamsMonoP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Source.Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcCtorDtParamsMonoP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SrcCtorDtParamsMonoP acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  simp only
  exact SrcCtorDtParamsMonoP_insert_function hP _ _

-- From: CompilerPreservation.lean:L172
private theorem SrcCtorDtParamsMonoP_insert_constructor
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (dt : DataType) (c : Constructor) (hmono : dt.params = []) :
    SrcCtorDtParamsMonoP (d.insert name (.constructor dt c)) := by
  intro k dt' c' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
    obtain ⟨heq, _⟩ := hget
    rw [← heq]
    exact hmono
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c' hget

-- From: CompilerPreservation.lean:L158
private theorem SrcCtorDtParamsMonoP_insert_dataType
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (dt : DataType) :
    SrcCtorDtParamsMonoP (d.insert name (.dataType dt)) := by
  intro k dt' c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c hget

-- From: CompilerPreservation.lean:L144
private theorem SrcCtorDtParamsMonoP_insert_function
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (f : Source.Function) :
    SrcCtorDtParamsMonoP (d.insert name (.function f)) := by
  intro k dt c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt c hget

-- From: CompilerPreservation.lean:L265
private theorem SrcCtorDtParamsMonoP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic toplevel)
    (h : toplevel.mkDecls = .ok decls) :
    SrcCtorDtParamsMonoP decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : SrcCtorDtParamsMonoP afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · show SrcCtorDtParamsMonoP (aliasNames, (default : Source.Decls)).2
      exact SrcCtorDtParamsMonoP_default
    · intro a x a' _hmem hstep hP
      exact SrcCtorDtParamsMonoP_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' hmem hstep hP
    have hxmono : x.params = [] :=
      hmono.2 x (Array.mem_toList_iff.mp hmem)
    exact SrcCtorDtParamsMonoP_dataTypeStep hP hxmono hstep

-- From: CompilerPreservation.lean:L456
private theorem TdCtorDtParamsMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    TdCtorDtParamsMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := TdCtorDtParamsMatchP_of_checkFold hfold
  exact TdCtorDtParamsMatchP_of_simplifyDecls hMid hts

-- From: CompilerPreservation.lean:L321
private theorem TdCtorDtParamsMatchP_default (d : Source.Decls) :
    TdCtorDtParamsMatchP d (default : Typed.Decls) := by
  intro k dt c hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

-- From: CompilerPreservation.lean:L334
private theorem TdCtorDtParamsMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TdCtorDtParamsMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TdCtorDtParamsMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨heq1, heq2⟩ := hget
        subst heq1; subst heq2
        exact hname_src
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c' hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' _hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget

-- From: CompilerPreservation.lean:L396
private theorem TdCtorDtParamsMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TdCtorDtParamsMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TdCtorDtParamsMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TdCtorDtParamsMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt' c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' c hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hcmatch : decls.getByKey name = some (.constructor dt c) :=
        hP name dt c hname_td
      intro k dt' c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨heq1, heq2⟩ := hget
        subst heq1; subst heq2
        exact hcmatch
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' c' hget

-- From: CompilerPreservation.lean:L499
private theorem concretizeBuild_containsAll_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (g : Global) (hcontains : typedDecls.containsKey g) :
    (concretizeBuild typedDecls mono newFunctions newDataTypes).containsKey g := by
  rw [IndexMap.containsKey_iff_exists_pair] at hcontains
  obtain ⟨⟨g', d⟩, hmem, hgeq⟩ := hcontains
  have hgeq' : g' = g := LawfulBEq.eq_of_beq hgeq
  rw [← hgeq']
  have hFnParams := typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hDtParams := typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hCtorDtParams :=
    typedDecls_ctor_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      let (key, dd) := p
      match dd with
      | .function f =>
        if f.params.isEmpty then
          acc.insert key (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm typedDecls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert key (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert key (.constructor newDt newCtor)
        else acc
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm typedDecls emptySubst mono f.body })
  have hsrcMono : ∀ acc a p,
      acc.containsKey a → (srcStep acc p).containsKey a := by
    intro acc a ⟨k, dd⟩ h
    show (srcStep acc (k, dd)).containsKey a
    simp only [srcStep]
    cases dd with
    | function f =>
      by_cases hp : f.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
    | dataType dt =>
      by_cases hp : dt.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
    | constructor dt c =>
      by_cases hp : dt.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
  have hdtMono : ∀ acc a dt,
      acc.containsKey a → (dtStep acc dt).containsKey a := by
    intro acc a dt h
    show (dtStep acc dt).containsKey a
    simp only [dtStep]
    exact list_foldl_containsKey_preserves _
      (fun acc' a' c' h' => IndexMap.containsKey_insert_preserves _ _ _ _ h')
      _ _ a (IndexMap.containsKey_insert_preserves _ _ _ _ h)
  have hfnMono : ∀ acc a f,
      acc.containsKey a → (fnStep acc f).containsKey a := by
    intro acc a f h
    exact IndexMap.containsKey_insert_preserves _ _ _ _ h
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem hmem
  let L : List (Global × Typed.Declaration) := typedDecls.pairs.toList
  have hsplit : ∃ pre post, L = pre ++ (g', d) :: post := by
    refine ⟨L.take i, L.drop (i + 1), ?_⟩
    have hi' : i < L.length := hi
    calc L = L.take i ++ L.drop i := (List.take_append_drop i L).symm
      _ = L.take i ++ (L[i] :: L.drop (i + 1)) := by rw [List.drop_eq_getElem_cons hi']
      _ = L.take i ++ (g', d) :: L.drop (i + 1) := by rw [hi_eq]
  obtain ⟨pre, post, hsplit_eq⟩ := hsplit
  have hfrom_eq :
      L.foldl srcStep default =
        post.foldl srcStep (srcStep (pre.foldl srcStep default) (g', d)) := by
    rw [hsplit_eq]
    rw [List.foldl_append, List.foldl_cons]
  have hget : typedDecls.getByKey g' = some d :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  have hstepInserts : ∀ acc : Typed.Decls, (srcStep acc (g', d)).containsKey g' := by
    intro acc
    show (srcStep acc (g', d)).containsKey g'
    simp only [srcStep]
    cases d with
    | function f =>
      have hparams : f.params = [] := hFnParams g' f hget
      have hpe : f.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
    | dataType dt =>
      have hparams : dt.params = [] := hDtParams g' dt hget
      have hpe : dt.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
    | constructor dt c =>
      have hparams : dt.params = [] := hCtorDtParams g' dt c hget
      have hpe : dt.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
  have hfromSource_g :
      (L.foldl srcStep default).containsKey g' := by
    rw [hfrom_eq]
    exact list_foldl_containsKey_preserves srcStep hsrcMono post _ g'
      (hstepInserts _)
  have hconc_eq :
      concretizeBuild typedDecls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep
          (newDataTypes.toList.foldl dtStep (L.foldl srcStep default)) := by
    show concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep (newDataTypes.toList.foldl dtStep
        (typedDecls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq]
  exact list_foldl_containsKey_preserves fnStep hfnMono _ _ g'
    (list_foldl_containsKey_preserves dtStep hdtMono _ _ g' hfromSource_g)

-- From: CompilerPreservation.lean:L649
private theorem exists_mkDecls_of_checkAndSimplify
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∃ decls, t.mkDecls = .ok decls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  cases h : t.mkDecls with
  | error e => rw [h] at hts; simp [bind, Except.bind] at hts
  | ok decls => exact ⟨decls, rfl⟩

-- From: CompilerPreservation.lean:L487
private theorem list_foldl_containsKey_preserves
    {γ : Type}
    (step : Typed.Decls → γ → Typed.Decls)
    (hmono : ∀ acc a c, acc.containsKey a → (step acc c).containsKey a) :
    ∀ (L : List γ) (init : Typed.Decls) a,
      init.containsKey a → (L.foldl step init).containsKey a
  | [], _, _, h => h
  | hd :: tl, init, a, h => by
    simp only [List.foldl_cons]
    exact list_foldl_containsKey_preserves step hmono tl (step init hd) a
      (hmono init a hd h)

-- From: CompilerPreservation.lean:L472
/-- Under `FullyMono`, every typed `.constructor dt c` entry has
`dt.params = []`. Ported from `CtorDtParamsScratch` 2026-04-24. -/
private theorem typedDecls_ctor_dt_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g dt c, typedDecls.getByKey g = some (.constructor dt c) → dt.params = [] := by
  intro g dt c htyped
  have hP := TdCtorDtParamsMatchP_checkAndSimplify hdecls hts
  have hsrc : decls.getByKey g = some (.constructor dt c) := hP g dt c htyped
  have hmonoP := SrcCtorDtParamsMonoP_mkDecls hmono hdecls
  exact hmonoP g dt c hsrc

-- From: CompilerPreservation.lean:L54
/-- Key-set preservation through checkAndSimplify. Unfolds `checkAndSimplify`
into `wellFormedDecls` + typecheck fold + `simplifyDecls`, then chains three
key-set equivalences via `indexMap_foldlM_insertKey_default_iff`. -/
private theorem checkAndSimplify_keys
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (_hdecls : t.mkDecls = .ok decls) (_hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g, decls.getByKey g ≠ none ↔ typedDecls.getByKey g ≠ none := by
  intro g
  rw [IndexMap.getByKey_ne_none_iff_containsKey, IndexMap.getByKey_ne_none_iff_containsKey]
  unfold Source.Toplevel.checkAndSimplify at _hts
  simp only [_hdecls, bind, Except.bind] at _hts
  rcases hwell : wellFormedDecls decls with _ | u
  · rw [hwell] at _hts; simp at _hts
  rw [hwell] at _hts
  simp only [pure, Except.pure] at _hts
  split at _hts
  · simp at _hts
  rename_i _ td htc_gen
  unfold simplifyDecls at _hts
  simp only [bind, Except.bind, pure, Except.pure] at _hts
  have hsp_gen := _hts
  have hfold_ck : td.containsKey g ↔
      ∃ p ∈ decls.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff decls _ ?_ g td htc_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | constructor d c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType d =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | function f =>
      simp only [hd] at hr
      rcases hf : ((checkFunction f) (getFunctionContext f decls)).run' {} with err | tf
      · rw [hf] at hr; simp at hr
      · rw [hf] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  have hsimp_ck : typedDecls.containsKey g ↔
      ∃ p ∈ td.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff td _ ?_ g typedDecls hsp_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | function f =>
      simp only [hd] at hr
      rcases hb : simplifyTypedTerm decls f.body with err | v
      · rw [hb] at hr; simp at hr
      · rw [hb] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType dt =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | constructor dt c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  rw [IndexMap.containsKey_iff_exists_pair decls g, ← hfold_ck,
      IndexMap.containsKey_iff_exists_pair td g, ← hsimp_ck]

/-! ### Step1_3Body — helpers for `step1_3_fully_mono_is_identity`.

Ported from `Step1_3BodyScratch` (2026-04-24). Axiom `typedDecls_ctor_dt_params_empty`
is the sole remaining sorry — mechanical ~60 LoC mirror of `SrcDtParamsMonoP`
for `.constructor` entries in `CheckSound.lean`. -/

-- From: CompilerPreservation.lean:L832
/-- Key-set preservation through concretize under FullyMonomorphic. -/
private theorem concretize_keys_of_mono
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t) (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls) :
    ∀ g, typedDecls.getByKey g ≠ none ↔ concDecls.getByKey g ≠ none := by
  intro g
  rw [IndexMap.getByKey_ne_none_iff_containsKey, IndexMap.getByKey_ne_none_iff_containsKey]
  obtain ⟨monoDecls, lower, hmonoKeys, hlower_insert, hfold⟩ :=
    concretize_steps_1_4_extract _hmono _hts _hconc
  exact Iff.trans (hmonoKeys g) (concretize_step_4_keys_of_fold lower hlower_insert hfold g)

-- From: CompilerPreservation.lean:L919
/-- Bridge: under FullyMonomorphic, mono entry-function input lists are
preserved through concretize (no rewrite needed since `f.params = []`). -/
private theorem concretize_preserves_entry_inputs
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {name : Global} {f_src : Source.Function} {f_conc : Concrete.Function}
    (_hsrc : decls.getByKey name = some (.function f_src))
    (_hconcF : concDecls.getByKey name = some (.function f_conc))
    (_hentry : f_src.entry = true) :
    f_src.inputs.map (·.1) = f_conc.inputs.map (·.1) := by
  -- BLOCKED ON: input-list preservation under concretize. Sketch:
  --   `Source.Function.notPolyEntry` + `_hentry` ⟹ `f_src.params = []`.
  --   `concretize` Step 4 (`step4Lower` for `.function`) calls
  --   `rewriteFunctionInputs` which is a no-op when the type-args list
  --   is empty (entries are unparameterized). So input shapes match
  --   pointwise; the `.1` projection (input names) is identical.
  -- This is a structural bridge over `step4Lower`'s function arm.
  sorry

-- From: CompilerPreservation.lean:L893
/-- Bridge: concretize preserves declaration kind for source `.function`
keys under `FullyMonomorphic`. -/
private theorem concretize_preserves_function_kind_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {name : Global} {f_src : Source.Function}
    (_hsrc : decls.getByKey name = some (.function f_src)) :
    ∃ f_conc : Concrete.Function,
      concDecls.getByKey name = some (.function f_conc) := by
  -- BLOCKED ON: shape preservation through concretize. Under FullyMono,
  -- source `.function` keys stay as `.function` (kind never flips to
  -- `.dataType` or `.constructor`). Proof sketch:
  --   1. `checkAndSimplify_preserves_function_kind_fwd` (analogous to the
  --      existing `_ctor_kind_fwd`) gives `typedDecls.getByKey name =
  --      some (.function tf)`.
  --   2. `concretize`'s Step 4 fold inserts `.function` from `.function`
  --      (`step4Lower` matches kind to kind for functions).
  --   3. Under `FullyMonomorphic`, no rename occurs at top-level entry
  --      keys (`concretizeName g #[] = g`).
  -- Each step is a NAMED leaf bridge; the composition is structural.
  sorry

-- From: CompilerPreservation.lean:L811
/-- Under `FullyMonomorphic`, Step 1–3 of `Typed.Decls.concretize` produce a
`monoDecls : Typed.Decls` whose key set matches `typedDecls`, and whose Step 4
`foldlM` produces the given `concDecls`. Composed from
`step1_3_fully_mono_is_identity` + `step4Lower_inserts`. -/
private theorem concretize_steps_1_4_extract
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls)
      (lower : Concrete.Decls → Global × Typed.Declaration →
               Except ConcretizeError Concrete.Decls),
      (∀ g, typedDecls.containsKey g ↔ monoDecls.containsKey g) ∧
      (∀ acc x r, lower acc x = .ok r →
        ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true) ∧
      monoDecls.foldlM (init := default) lower = .ok concDecls := by
  obtain ⟨monoDecls, hkeys, hfold⟩ := step1_3_fully_mono_is_identity hmono hts hconc
  exact ⟨monoDecls, step4Lower, hkeys, step4Lower_inserts, hfold⟩

/- `concretize_step_4_keys_of_fold` moved to `ConcretizeSound.lean`
(generic over `lower` step; doesn't depend on CompilerPreservation context). -/

-- From: CompilerPreservation.lean:L844
private theorem namespace_preservation
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) (hmono : FullyMonomorphic t) :
    ∀ g, decls.getByKey g ≠ none ↔ concDecls.getByKey g ≠ none := by
  intro g
  exact Iff.trans (checkAndSimplify_keys hdecls hts g) (concretize_keys_of_mono hmono hts hconc g)

-- From: CompilerPreservation.lean:L672
/-- Under `FullyMonomorphic`, Steps 1-3 of `Typed.Decls.concretize` are an
identity (up to an inert `rewriteTyp`/`rewriteTypedTerm` pass with an empty
mono-map), so `monoDecls` has the same keys as `typedDecls` and the Step-4
`foldlM` via `step4Lower` produces the given `concDecls`.

BLOCKED ON structured decomposition:

(S1) `FullyMonomorphic`-params-preservation through `checkAndSimplify`:
    every function/dataType/constructor-carried-dt in `typedDecls` has empty
    `params`. Traces through `mkDecls_functionStep` (preserves `params`
    field), `checkFunction` (copies `function.params` into `Typed.Function`),
    `simplifyDecls` (only rewrites `.body`). Three nested folds; each is an
    insert-only `foldlM` whose step preserves a "all `.function` have empty
    params / all `.dataType` have empty params" invariant. ~300 LoC across
    (S1a), (S1b), (S1c) once the params-preservation invariant is stated as
    a List-level `foldlM`-invariant.

(S2) `concretizeBuild` forward key-inclusion: every key of `typedDecls` is in
    `concretizeBuild typedDecls drained.mono drained.newFunctions
    drained.newDataTypes`. Under (S1), `fromSource` fold's `else` branches are
    never taken, so every source pair inserts at its key. Need a generic
    `Array.foldl`/`List.foldl` key-insertion-closure lemma. ~150 LoC.

(S3) `concretizeBuild` backward key-inclusion: every output key is either a
    `typedDecls` key or the name of an entry in `drained.newFunctions` /
    `drained.newDataTypes`. `concretize_build_excludes_polymorphic` (CLOSED
    in `ConcretizeSound.lean`) handles the main decomposition.

(S4) `drained.newFunctions` / `drained.newDataTypes` names are `typedDecls`
    keys: under `FullyMonomorphic`, every worklist entry `(g, args)` has
    `args = #[]` (because well-formed typed terms have no nonempty `.app
    g args` under mono-only decls). Combined with `concretizeName_empty_args`
    (CLOSED: `concretizeName g #[] = g`) and `MonoHasDecl`-style
    reachability (CLOSED: `concretize_drain_mono_has_decl`), each new-array
    entry's name equals a worklist-seed name, which is a `typedDecls` key
    (seeds come from `decls.pairs`). ~300 LoC, dominated by the
    `collectInTyp`/`collectInTypedTerm`-only-emits-empty-args lemma.

(S5) Constructor-key case in backward-inclusion: for
    `dt.name.pushNamespace c.nameHead = g` with `dt ∈ drained.newDataTypes`
    and `c ∈ dt.constructors`, `g` is a `typedDecls` key because
    `mkDecls_dataTypeStep` inserts every ctor at
    `dt.name.pushNamespace ctor.nameHead` — plus (S4) ensures `dt.name` maps
    to a `typedDecls` datatype whose constructors have matching nameHeads.
    ~100 LoC.

Total effort: ~1000 LoC across (S1)-(S5). Main-theorem composition
(below comment) is ~50 LoC once all sub-lemmas are discharged:

```
  unfold Typed.Decls.concretize at _hconc
  simp only [bind, Except.bind] at _hconc
  split at _hconc
  · contradiction
  rename_i drained hdrain
  refine ⟨concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes,
          ?_, _hconc⟩
  intro g
  constructor
  · intro hcontains  -- forward via (S2)
    exact S2_containsAll _hmono _hts g hcontains
  · intro hcontains  -- backward via (S3) + (S4) + (S5)
    rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hcontains
    cases hgd : (concretizeBuild typedDecls drained.mono drained.newFunctions
                   drained.newDataTypes).getByKey g with ...
```

(Body ported from `Step1_3BodyScratch` 2026-04-24: closes via
FullyMono-threaded `containsKey` induction + backward case-split with
`NewDtBridge` / `NewFnBridge` + `ctor_pushed_name` dispatch.) -/


private theorem step1_3_fully_mono_is_identity
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls),
      (∀ g, typedDecls.containsKey g ↔ monoDecls.containsKey g) ∧
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls := by
  obtain ⟨decls, hdecls⟩ := Step1_3Body.exists_mkDecls_of_checkAndSimplify hts
  have hconc_orig : typedDecls.concretize = .ok concDecls := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  rename_i drained hdrain
  refine ⟨concretizeBuild typedDecls drained.mono drained.newFunctions
            drained.newDataTypes, ?_, hconc⟩
  intro g
  constructor
  · intro hc
    exact Step1_3Body.concretizeBuild_containsAll_of_fullyMonomorphic
      hmono hdecls hts _ _ _ g hc
  · intro hc
    rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hc
    cases hget : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).getByKey g with
    | none => exact absurd hget hc
    | some d =>
      rcases concretize_build_excludes_polymorphic _ _ _ _ _ _ hget with
        ⟨srcD, hsrc, _⟩ | ⟨f, hfmem, hfname⟩ | ⟨dt, hdtmem, hcond⟩
      · rw [← IndexMap.getByKey_ne_none_iff_containsKey]
        rw [hsrc]; exact Option.some_ne_none _
      · obtain ⟨g', orig, horig, hfneq⟩ :=
          newFnBridge_derive hmono hdecls hts hdrain f hfmem
        have hg_eq : g = g' := by rw [← hfname, hfneq]
        rw [hg_eq]
        rw [← IndexMap.getByKey_ne_none_iff_containsKey]
        rw [horig]; exact Option.some_ne_none _
      · rcases hcond with hdtname | ⟨c, hcmem, hceq⟩
        · obtain ⟨g', orig, horig, hdtname_eq, _⟩ :=
            newDtBridge_derive hmono hdecls hts hdrain dt hdtmem
          have hg_eq : g = g' := by rw [← hdtname, hdtname_eq]
          rw [hg_eq]
          rw [← IndexMap.getByKey_ne_none_iff_containsKey]
          rw [horig]; exact Option.some_ne_none _
        · -- (c-ctor): g = dt.name.pushNamespace c.nameHead
          obtain ⟨g', orig, horig, hdtname_eq, hctors_map⟩ :=
            newDtBridge_derive hmono hdecls hts hdrain dt hdtmem
          have hc_head_mem :
              c.nameHead ∈ orig.constructors.map (·.nameHead) := by
            rw [← hctors_map]; exact List.mem_map_of_mem hcmem
          obtain ⟨c_orig, hc_orig_mem, hc_heads_eq⟩ := List.mem_map.mp hc_head_mem
          have hDt : Typed.Decls.DtNameIsKey typedDecls :=
            checkAndSimplify_preserves_dtNameIsKey hts
          have horig_mem :
              (g', Typed.Declaration.dataType orig) ∈ typedDecls.pairs.toList :=
            IndexMap.mem_pairs_of_getByKey typedDecls g' _ horig
          have horig_name : g' = orig.name := hDt g' orig horig_mem
          have hCtorPresent : Typed.Decls.CtorPresent typedDecls :=
            checkAndSimplify_preserves_ctorPresent hts
          obtain ⟨cc, hcc_mem⟩ := hCtorPresent g' orig c_orig horig_mem hc_orig_mem
          have hcc_get := IndexMap.getByKey_of_mem_pairs typedDecls _ _ hcc_mem
          have hkey_eq : g = orig.name.pushNamespace c_orig.nameHead := by
            rw [← hceq, hdtname_eq, horig_name, hc_heads_eq]
          rw [hkey_eq]
          rw [← IndexMap.getByKey_ne_none_iff_containsKey]
          rw [hcc_get]; exact Option.some_ne_none _

-- From: CompilerProgress.lean:L5917
theorem newDtBridge_derive
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    NewDtBridge tds drained.newDataTypes := by
  intro dt hdt_mem
  have hinit : DrainState.StrongNewNameShape tds _ :=
    DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  obtain ⟨g, args, dt_orig, hname, hget, hargs_sz, hctors⟩ := hfinal.2 dt hdt_mem
  have hdt_orig_params :=
    typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts g dt_orig hget
  have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
  have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
  have hname_eq : dt.name = g := by
    rw [hname, hargs_empty]; exact concretizeName_empty_args g
  exact ⟨g, dt_orig, hget, hname_eq, hctors⟩

-- From: CompilerProgress.lean:L5940
theorem newFnBridge_derive
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    NewFnBridge tds drained.newFunctions := by
  intro f hf_mem
  have hinit : DrainState.StrongNewNameShape tds _ :=
    DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  obtain ⟨g, args, f_orig, hname, hget, hargs_sz⟩ := hfinal.1 f hf_mem
  have hf_orig_params :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts g f_orig hget
  have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
  have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
  have hname_eq : f.name = g := by
    rw [hname, hargs_empty]; exact concretizeName_empty_args g
  exact ⟨g, f_orig, hget, hname_eq⟩

-- MOVED to Scratch.lean: `concretize_produces_ctorPresent` (orphan).


-- DELETED 2026-04-28: `Toplevel.compile_progress` (FullyMono predecessor of
-- `compile_progress_entry`). Superseded by the entry-restricted variant whose
-- body composes through `concretize_produces_ctorPresent_entry` and
-- `Lower.compile_progress_entry`. The deleted theorem cited the orphan
-- `concretize_produces_ctorPresent` + `Lower.compile_progress` chain.

/-! ### Wire B — entry-restricted bridge variants for `compile_progress_entry`.

Each bridge below is the entry-restricted parallel of an `_under_fullymono`-
shaped progress lemma. They take `WellFormed t` instead of
`FullyMonomorphic t`. Their bodies are stub `sorry`s with documented closure
paths; `compile_progress_entry` composes through them. -/

-- From: CompilerProgress.lean:L990
private theorem ConcreteCtorPresentP_default :
    ConcreteCtorPresentP (default : Concrete.Decls) := by
  intro k dt c hget _hc
  exfalso
  have hne : (default : Concrete.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[k]?).bind _ = none
    have : (default : Concrete.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget



/-! ### Bridges back to pairs-form -/

-- From: CompilerProgress.lean:L4139
/-- `Name.str n s ≠ n`: a name is never equal to its own string-extension.
Proof by structural induction on n. -/
private theorem Name_str_ne_self : ∀ (n : Lean.Name) (s : String),
    Lean.Name.str n s ≠ n
  | .anonymous, _, h => by cases h
  | .str n' s', s, h => by
    -- h : str (str n' s') s = str n' s'
    injection h with hn hs
    -- hn : str n' s' = n'.   hs : s = s'.
    exact Name_str_ne_self n' s' hn
  | .num _ _, _, h => by cases h

-- From: CompilerProgress.lean:L4908
/-- Body of `concretizeBuild_ctorPresent`. Strengthened signature:
FullyMono + hdecls + hts hidden in bridges. Pass through to phase lemmas. -/
private theorem concretizeBuild_ctorPresent_body
    {typedDecls : Typed.Decls}
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead)
    (hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    (_hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (_hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    TypedCtorPresentP
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  let emptySubst : Global → Option Typ := fun _ => none
  -- Phase 1: `fromSource`.
  have hP1 := fromSource_preserves_ctorPresent typedDecls mono hP hDt hCtor
  -- Phase 2: `withNewDts`.
  have hFresh2 := phase2_freshness_discharge typedDecls mono hP hDt hCtor
    newDataTypes hFreshDt
  -- `hInitDt` derivation: fromSource preserves DtNameIsKey.
  have hInitDt : TypedDtNameIsKeyP (fromSource typedDecls mono) := by
    intro k dt hget
    obtain ⟨dtSrc, _, _, hdt_eq⟩ := fromSource_dt_trace typedDecls mono k dt hget
    rw [hdt_eq, rewriteDt_name]
    exact hDt k dtSrc (IndexMap.getByKey_of_mem_pairs _ _ _ (by assumption))
  -- `hMutualFresh` derivation: uses NewDtBridge + source key uniqueness.
  have hMutualFresh : ∀ dt ∈ newDataTypes, ∀ dt' ∈ newDataTypes,
      ∀ ch ∈ dt'.constructors.map (·.nameHead),
      dt.name ≠ dt'.name.pushNamespace ch := by
    intro dt hdt_mem dt' hdt'_mem ch hch
    -- dt = corresponds to source g_dt; dt' = source g_dt' with same ctor heads.
    obtain ⟨g_dt, orig_dt, hget_dt, hname_dt, _⟩ := _hNewDtBridge dt hdt_mem
    obtain ⟨g_dt', orig_dt', hget_dt', hname_dt', hheads_dt'⟩ :=
      _hNewDtBridge dt' hdt'_mem
    -- ch is a nameHead in dt'.constructors, so also in orig_dt'.constructors (via hheads_dt').
    rw [hheads_dt'] at hch
    -- There's a c_orig ∈ orig_dt'.constructors with c_orig.nameHead = ch.
    rw [List.mem_map] at hch
    obtain ⟨c_orig, hc_orig_mem, hc_orig_head⟩ := hch
    -- source has .constructor orig_dt' cc at orig_dt'.name.pushNamespace c_orig.nameHead.
    obtain ⟨cc, hcc_get⟩ := hP g_dt' orig_dt' c_orig hget_dt' hc_orig_mem
    have hg_dt'_name : g_dt' = orig_dt'.name := hDt g_dt' orig_dt' hget_dt'
    -- Goal: dt.name ≠ dt'.name.pushNamespace ch.
    -- hname_dt' : dt'.name = g_dt'. hc_orig_head : c_orig.nameHead = ch. hg_dt'_name : g_dt' = orig_dt'.name.
    intro hkeq
    -- hkeq : dt.name = dt'.name.pushNamespace ch
    -- Transform to: g_dt = orig_dt'.name.pushNamespace c_orig.nameHead (source key of .constructor).
    rw [hname_dt'] at hkeq  -- dt.name = g_dt'.pushNamespace ch
    rw [← hc_orig_head] at hkeq  -- dt.name = g_dt'.pushNamespace c_orig.nameHead
    rw [hname_dt] at hkeq  -- g_dt = g_dt'.pushNamespace c_orig.nameHead
    -- Substitute in hget_dt to get typedDecls at the ctor-key.
    rw [hkeq] at hget_dt
    -- hget_dt : typedDecls.getByKey (g_dt'.pushNamespace c_orig.nameHead) = some (.dataType orig_dt)
    -- Rewrite hcc_get's key: orig_dt'.name.pushNamespace c_orig.nameHead = g_dt'.pushNamespace c_orig.nameHead.
    rw [← hg_dt'_name] at hcc_get
    -- hcc_get : typedDecls.getByKey (g_dt'.pushNamespace c_orig.nameHead) = some (.constructor orig_dt' cc)
    rw [hcc_get] at hget_dt
    cases hget_dt
  have hP2 := withNewDts_preserves_ctorPresent _ mono newDataTypes hP1 hInitDt hFresh2 hMutualFresh
  -- Phase 3: `newFunctions`.
  -- Rewrite `concretizeBuild` as the composed folds.
  have hEq : concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        (newDataTypes.foldl
          (fun acc dt =>
            let rewrittenCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            let acc' := acc.insert dt.name (.dataType newDt)
            rewrittenCtors.foldl
              (fun acc'' c =>
                let cName := dt.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt c))
              acc')
          (typedDecls.pairs.foldl
            (fun acc p =>
              let (key, d) := p
              match d with
              | .function f =>
                if f.params.isEmpty then
                  let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
                  let newOutput := rewriteTyp emptySubst mono f.output
                  let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
                  acc.insert key (.function
                    { f with inputs := newInputs, output := newOutput, body := newBody })
                else acc
              | .dataType dt =>
                if dt.params.isEmpty then
                  let newCtors := dt.constructors.map fun c =>
                    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
                  acc.insert key (.dataType { dt with constructors := newCtors })
                else acc
              | .constructor dt c =>
                if dt.params.isEmpty then
                  let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
                  let newCtor : Constructor := { c with argTypes := newArgTypes }
                  let rewrittenCtors := dt.constructors.map fun c' =>
                    { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
                  let newDt : DataType := { dt with constructors := rewrittenCtors }
                  acc.insert key (.constructor newDt newCtor)
                else acc)
            default)) := by
    unfold concretizeBuild
    rfl
  rw [hEq]
  -- Phase 3 preservation via `newFunctions_preserves_ctorPresent`.
  -- The freshness hypothesis is discharged by `phase3_freshness_discharge`.
  have hFreshPost := phase3_freshness_discharge typedDecls mono hP hDt hCtor
    newFunctions newDataTypes hFreshFn _hNewDtBridge _hNewFnBridge
  exact newFunctions_preserves_ctorPresent _ mono typedDecls newFunctions hP2 hFreshPost

-- From: CompilerProgress.lean:L3804
/-- Forward lemma: every source `.constructor dtSrc cSrc` with empty params
has its rewrite present in `fromSource` at the same key. -/
private theorem fromSource_ctor_forward (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dtSrc : DataType) (cSrc : Constructor)
    (hmem : (k, Typed.Declaration.constructor dtSrc cSrc) ∈
      typedDecls.pairs.toList)
    (hparams : dtSrc.params.isEmpty = true) :
    (fromSource typedDecls mono).getByKey k =
      some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := by
  have hex : (fromSource typedDecls mono).getByKey k =
      some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := by
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
    rw [Array.length_toList] at hidx_lt
    have hpair_idx : typedDecls.pairs[idx]'hidx_lt =
        (k, Typed.Declaration.constructor dtSrc cSrc) := by
      rw [← hidx_eq, Array.getElem_toList]
    let Q : Nat → Typed.Decls → Prop := fun i acc =>
      idx < i → acc.getByKey k =
        some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc))
    suffices h : Q typedDecls.pairs.size (fromSource typedDecls mono) by
      apply h
      exact hidx_lt
    apply Array.foldl_induction
      (motive := fun (i : Nat) (acc : Typed.Decls) => Q i acc)
    · intro hlt
      exact absurd hlt (Nat.not_lt_zero _)
    · intro i acc hQ hlt
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt_i | heq
      · have hacc : acc.getByKey k =
            some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := hQ hlt_i
        unfold fromSourceStep
        generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p
        obtain ⟨key', d'⟩ := p
        simp only
        have hkey_ne : key' ≠ k := by
          intro hEq
          subst hEq
          have h1 : typedDecls.indices[(typedDecls.pairs[i.val]'i.isLt).1]? = some i.val :=
            typedDecls.pairsIndexed i.val i.isLt
          have h2 : typedDecls.indices[(typedDecls.pairs[idx]'hidx_lt).1]? = some idx :=
            typedDecls.pairsIndexed idx hidx_lt
          rw [hpsh] at h1
          rw [hpair_idx] at h2
          simp only at h1 h2
          rw [h1] at h2
          exact absurd (Option.some.inj h2).symm (Nat.ne_of_lt hlt_i)
        have hne : (key' == k) = false := by
          by_cases h : (key' == k) = true
          · exact absurd (LawfulBEq.eq_of_beq h) hkey_ne
          · exact Bool.not_eq_true _ |>.mp h
        cases d' with
        | function f =>
          by_cases hf : f.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
        | dataType dt' =>
          by_cases hf : dt'.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
        | constructor dt' c' =>
          by_cases hf : dt'.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
      · subst heq
        have hpair_idx' : typedDecls.pairs[i] =
            (k, Typed.Declaration.constructor dtSrc cSrc) := hpair_idx
        show (fromSourceStep typedDecls mono acc (typedDecls.pairs[i])).getByKey k = _
        rw [hpair_idx']
        unfold fromSourceStep
        simp only [hparams, if_true]
        exact IndexMap.getByKey_insert_self _ k _
  exact hex

-- From: CompilerProgress.lean:L3720
/-- ctor-trace: every `.constructor dt_new c_new` at `k` in fromSource
originated from a source `.constructor dtSrc cSrc` at `k` with empty
params, and `dt_new = rewriteDt dtSrc`, `c_new = rewriteC cSrc`. -/
private theorem fromSource_ctor_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dt_new : DataType) (c_new : Constructor)
    (hget : (fromSource typedDecls mono).getByKey k =
      some (.constructor dt_new c_new)) :
    ∃ dtSrc cSrc,
      (k, Typed.Declaration.constructor dtSrc cSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧
        dt_new = rewriteDt mono dtSrc ∧ c_new = rewriteC mono cSrc := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_new c_new, acc.getByKey k = some (.constructor dt_new c_new) →
      ∃ dtSrc cSrc,
        (k, Typed.Declaration.constructor dtSrc cSrc) ∈ typedDecls.pairs.toList ∧
          dtSrc.params.isEmpty = true ∧
          dt_new = rewriteDt mono dtSrc ∧ c_new = rewriteC mono cSrc
  suffices h : P (fromSource typedDecls mono) from h k dt_new c_new hget
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_new c_new hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  · intro i acc hP k dt_new c_new hget
    have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    unfold fromSourceStep at hget
    generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p at hget hp_mem
    obtain ⟨key, d⟩ := p
    simp only at hget
    cases d with
    | function f =>
      by_cases hparams : f.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new c_new hget
      · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget
    | dataType dtSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new c_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget
    | constructor dtSrc cSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
          refine ⟨dtSrc, cSrc, hp_mem, hparams, ?_, ?_⟩
          · rw [← hget.1]
          · rw [← hget.2]
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new c_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget

-- From: CompilerProgress.lean:L3889
/-- Forward dt lemma: every source `.dataType dtSrc` with empty params has
its rewrite at the same key in `fromSource`. -/
private theorem fromSource_dt_forward (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dtSrc : DataType)
    (hmem : (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList)
    (hparams : dtSrc.params.isEmpty = true) :
    (fromSource typedDecls mono).getByKey k =
      some (.dataType (rewriteDt mono dtSrc)) := by
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
  rw [Array.length_toList] at hidx_lt
  have hpair_idx : typedDecls.pairs[idx]'hidx_lt =
      (k, Typed.Declaration.dataType dtSrc) := by
    rw [← hidx_eq, Array.getElem_toList]
  let Q : Nat → Typed.Decls → Prop := fun i acc =>
    idx < i → acc.getByKey k = some (.dataType (rewriteDt mono dtSrc))
  suffices h : Q typedDecls.pairs.size (fromSource typedDecls mono) by
    apply h; exact hidx_lt
  apply Array.foldl_induction
    (motive := fun (i : Nat) (acc : Typed.Decls) => Q i acc)
  · intro hlt
    exact absurd hlt (Nat.not_lt_zero _)
  · intro i acc hQ hlt
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt_i | heq
    · have hacc : acc.getByKey k = some (.dataType (rewriteDt mono dtSrc)) := hQ hlt_i
      unfold fromSourceStep
      generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p
      obtain ⟨key', d'⟩ := p
      simp only
      have hkey_ne : key' ≠ k := by
        intro hEq
        subst hEq
        have h1 : typedDecls.indices[(typedDecls.pairs[i.val]'i.isLt).1]? = some i.val :=
          typedDecls.pairsIndexed i.val i.isLt
        have h2 : typedDecls.indices[(typedDecls.pairs[idx]'hidx_lt).1]? = some idx :=
          typedDecls.pairsIndexed idx hidx_lt
        rw [hpsh] at h1
        rw [hpair_idx] at h2
        simp only at h1 h2
        rw [h1] at h2
        exact absurd (Option.some.inj h2).symm (Nat.ne_of_lt hlt_i)
      have hne : (key' == k) = false := by
        by_cases h : (key' == k) = true
        · exact absurd (LawfulBEq.eq_of_beq h) hkey_ne
        · exact Bool.not_eq_true _ |>.mp h
      cases d' with
      | function f =>
        by_cases hf : f.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
      | dataType dt' =>
        by_cases hf : dt'.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
      | constructor dt' c' =>
        by_cases hf : dt'.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
    · subst heq
      have hpair_idx' : typedDecls.pairs[i] =
          (k, Typed.Declaration.dataType dtSrc) := hpair_idx
      show (fromSourceStep typedDecls mono acc (typedDecls.pairs[i])).getByKey k = _
      rw [hpair_idx']
      unfold fromSourceStep
      simp only [hparams, if_true]
      exact IndexMap.getByKey_insert_self _ k _

-- From: CompilerProgress.lean:L3643
/-- dt-trace: every `.dataType dt_new` at `k` in fromSource originated from a
source `.dataType dtSrc` at `k` with empty params, and `dt_new = rewriteDt dtSrc`. -/
private theorem fromSource_dt_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dt_new : DataType)
    (hget : (fromSource typedDecls mono).getByKey k = some (.dataType dt_new)) :
    ∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
      dtSrc.params.isEmpty = true ∧ dt_new = rewriteDt mono dtSrc := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_new, acc.getByKey k = some (.dataType dt_new) →
      ∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧ dt_new = rewriteDt mono dtSrc
  suffices h : P (fromSource typedDecls mono) from h k dt_new hget
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_new hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  · intro i acc hP k dt_new hget
    have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    unfold fromSourceStep at hget
    generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p at hget hp_mem
    obtain ⟨key, d⟩ := p
    simp only at hget
    cases d with
    | function f =>
      by_cases hparams : f.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new hget
      · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget
    | dataType dtSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          refine ⟨dtSrc, hp_mem, hparams, ?_⟩
          rw [← hget]
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget
    | constructor dtSrc cSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget

-- From: CompilerProgress.lean:L4055
private theorem fromSource_preserves_ctorPresent
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := typedDecls.pairs.foldl
      (fun acc p =>
        let (key, d) := p
        match d with
        | .function f =>
          if f.params.isEmpty then
            let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
            let newOutput := rewriteTyp emptySubst mono f.output
            let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
            acc.insert key (.function
              { f with inputs := newInputs, output := newOutput, body := newBody })
          else acc
        | .dataType dt =>
          if dt.params.isEmpty then
            let newCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            acc.insert key (.dataType { dt with constructors := newCtors })
          else acc
        | .constructor dt c =>
          if dt.params.isEmpty then
            let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
            let newCtor : Constructor := { c with argTypes := newArgTypes }
            let rewrittenCtors := dt.constructors.map fun c' =>
              { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            acc.insert key (.constructor newDt newCtor)
          else acc)
      default
    TypedCtorPresentP fromSource := by
  intro emptySubst fS
  -- The inline `fS` is definitionally equal to `fromSource typedDecls mono`.
  show TypedCtorPresentP (fromSource typedDecls mono)
  intro k dt_new c hget hc
  -- Trace `dt_new` back to a source dt.
  obtain ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ :=
    fromSource_dt_trace typedDecls mono k dt_new hget
  have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
  have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
  have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
  rw [rewriteDt_constructors] at hc_new
  rw [List.mem_map] at hc_new
  obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
  have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
  obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
  have hcc_mem : (dtSrc.name.pushNamespace c'.nameHead,
      Typed.Declaration.constructor dtSrc cc) ∈ typedDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hcc_get
  have hfwd := fromSource_ctor_forward typedDecls mono
    (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_mem hparams
  refine ⟨rewriteC mono cc, ?_⟩
  rw [hdt_eq, rewriteDt_name, hhead]
  exact hfwd

/-! ### Phase-2 lemma: `withNewDts` preserves CtorPresent.

For each `dt ∈ newDataTypes`:
* inserts `.dataType rewrittenDt` at `dt.name`
* for each `c ∈ rewrittenDt.constructors`, inserts `.constructor rewrittenDt c`
  at `dt.name.pushNamespace c.nameHead`.

The inner ctor-fold inserts all witnesses for the dt-name key's dt. The
outer fold threads through. Discharge via `phase2_freshness_discharge` below.
-/

-- From: CompilerProgress.lean:L4187
/-- Inner ctor-fold helper.

Given `acc₀` satisfying:
- Partial CtorPresent: all `.dataType d'' at k''` entries with `d''.name ≠ dt_name` already
  have their witnesses (the newDt entry at `dt_name` does NOT need witnesses yet).
- DtNameIsKey.
- newDt is pinned at `dt_name`.

Freshness: `dt_name.pushNamespace ch` (for `ch ∈ ctors.map (·.nameHead)`) distinct from
witness keys of all OTHER dts in acc₀.

After folding inserts of `.constructor newDt c` at `dt_name.pushNamespace c.nameHead`, we get:
- (a') every `ch ∈ ctors.map (·.nameHead)` has a ctor-entry at `dt_name.pushNamespace ch`.
- (b) non-newDt dt's witnesses still present.
- (c) DtNameIsKey preserved.
- (d) newDt still at `dt_name`.
- (e) Data-type trace: every `.dataType` entry in result was in `acc₀`.
-/
private theorem innerCtorFold_preserves
    (dt_name : Global) (newDt : DataType)
    (ctors : List Constructor)
    (acc₀ : Typed.Decls)
    (hAcc₀_partial : ∀ k'' d'' c'',
      acc₀.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
      d''.name ≠ dt_name →
      ∃ cc, acc₀.getByKey (d''.name.pushNamespace c''.nameHead) =
        some (.constructor d'' cc))
    (hAcc₀Dt : TypedDtNameIsKeyP acc₀)
    (hAcc₀_newDt : acc₀.getByKey dt_name = some (.dataType newDt))
    (hfreshPush : ∀ k d'' c'' ch,
      acc₀.getByKey k = some (.dataType d'') → c'' ∈ d''.constructors →
      ch ∈ ctors.map (·.nameHead) →
      d''.name ≠ dt_name → d''.name.pushNamespace c''.nameHead ≠
        dt_name.pushNamespace ch) :
    (∀ ch ∈ ctors.map (·.nameHead), ∃ cc,
      (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey (dt_name.pushNamespace ch) =
        some (.constructor newDt cc)) ∧
    (∀ k'' d'' c'',
      (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
      d''.name ≠ dt_name →
      ∃ cc, (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey (d''.name.pushNamespace c''.nameHead) =
        some (.constructor d'' cc)) ∧
    TypedDtNameIsKeyP (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀) ∧
    (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀).getByKey dt_name = some (.dataType newDt) ∧
    (∀ k d'', (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀).getByKey k = some (.dataType d'') →
      acc₀.getByKey k = some (.dataType d'')) := by
  induction ctors generalizing acc₀ with
  | nil =>
    refine ⟨?_, hAcc₀_partial, hAcc₀Dt, hAcc₀_newDt, fun _ _ hget => hget⟩
    intro ch hch
    simp only [List.map_nil] at hch
    cases hch
  | cons c rest ih =>
    simp only [List.foldl_cons]
    let acc₁ : Typed.Decls :=
      acc₀.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c)
    have hne_dt_name : (dt_name.pushNamespace c.nameHead == dt_name) = false := by
      cases hbeq : (dt_name.pushNamespace c.nameHead == dt_name) with
      | false => rfl
      | true =>
        exact absurd (LawfulBEq.eq_of_beq hbeq).symm (ne_pushNamespace_self dt_name c.nameHead)
    -- newDt still at dt_name in acc₁.
    have hAcc₁_newDt : acc₁.getByKey dt_name = some (.dataType newDt) := by
      simp only [acc₁]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_dt_name]
      exact hAcc₀_newDt
    -- DtNameIsKey on acc₁.
    have hAcc₁Dt : TypedDtNameIsKeyP acc₁ := by
      intro k d'' hget
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hAcc₀Dt k d'' hget
    -- Partial CtorPresent on acc₁ (non-newDt witnesses).
    have hAcc₁_partial : ∀ k'' d'' c'',
        acc₁.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
        d''.name ≠ dt_name →
        ∃ cc, acc₁.getByKey (d''.name.pushNamespace c''.nameHead) =
          some (.constructor d'' cc) := by
      intro k'' d'' c'' hget hc'' hd_ne
      have hcName : dt_name.pushNamespace c.nameHead ≠ k'' := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne_k : (dt_name.pushNamespace c.nameHead == k'') = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k'') with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_k] at hget
      obtain ⟨cc, hcc⟩ := hAcc₀_partial k'' d'' c'' hget hc'' hd_ne
      have hch_mem : c.nameHead ∈ (c :: rest).map (·.nameHead) := List.mem_cons_self
      have hwit_ne := hfreshPush k'' d'' c'' c.nameHead hget hc'' hch_mem hd_ne
      have hne_wit : (dt_name.pushNamespace c.nameHead ==
          d''.name.pushNamespace c''.nameHead) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead ==
            d''.name.pushNamespace c''.nameHead) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq).symm hwit_ne
      refine ⟨cc, ?_⟩
      simp only [acc₁]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_wit]
      exact hcc
    -- Freshness on rest for acc₁.
    have hfreshPush₁ : ∀ k d'' c'' ch,
        acc₁.getByKey k = some (.dataType d'') → c'' ∈ d''.constructors →
        ch ∈ rest.map (·.nameHead) →
        d''.name ≠ dt_name →
        d''.name.pushNamespace c''.nameHead ≠ dt_name.pushNamespace ch := by
      intro k d'' c'' ch hget hc'' hch hd_ne
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      have hch' : ch ∈ (c :: rest).map (·.nameHead) := by
        simp only [List.map_cons, List.mem_cons]; exact Or.inr hch
      exact hfreshPush k d'' c'' ch hget hc'' hch' hd_ne
    -- Apply IH.
    have hfinal := ih acc₁ hAcc₁_partial hAcc₁Dt hAcc₁_newDt hfreshPush₁
    -- Massage to get result-level (a').
    refine ⟨?_, hfinal.2.1, hfinal.2.2.1, hfinal.2.2.2.1, ?_⟩
    · -- (a'): for ch ∈ (c :: rest).map (·.nameHead), witness in result.
      intro ch hch
      simp only [List.map_cons, List.mem_cons] at hch
      rcases hch with heq | hin
      · -- ch = c.nameHead: witness is the entry inserted at acc₁, which survives
        -- rest's inserts only if c.nameHead ∉ rest.map (·.nameHead). Otherwise it's
        -- overwritten by later insert (still a valid witness .constructor newDt _).
        subst heq
        -- Split: is c.nameHead in rest.map (·.nameHead)?
        by_cases hin_rest : c.nameHead ∈ rest.map (·.nameHead)
        · -- Yes: rest's later insert at the same pushed key provides a witness.
          -- That witness is `.constructor newDt c_later` for some c_later in rest.
          -- Use hfinal.1 applied to hin_rest.
          exact hfinal.1 c.nameHead hin_rest
        · -- No: acc₁'s witness is preserved by rest-fold.
          -- Prove via a side lemma: rest-fold preserves entries at keys NOT in its pushed set.
          refine ⟨c, ?_⟩
          -- Goal: rest-fold's result has `.constructor newDt c` at `dt_name.pushNamespace c.nameHead`.
          -- We know acc₁.getByKey (dt_name.pushNamespace c.nameHead) = some (.constructor newDt c)
          -- and rest-fold only inserts at `dt_name.pushNamespace c'.nameHead` for c' ∈ rest.
          -- Those keys differ from c.nameHead's pushed key (by pushNamespace_inj_both).
          have hacc₁_ce : acc₁.getByKey (dt_name.pushNamespace c.nameHead) =
              some (.constructor newDt c) := by
            simp only [acc₁]; rw [IndexMap.getByKey_insert_self]
          -- Use a local lemma proved by induction on rest.
          exact restFold_preserves_unvisited dt_name newDt rest c.nameHead hin_rest acc₁ c hacc₁_ce
      · -- ch ∈ rest.map (·.nameHead): use hfinal.1.
        exact hfinal.1 ch hin
    · -- (e): trace through the rest-fold and then the c-insert.
      intro k d'' hget
      have h_acc₁ := hfinal.2.2.2.2 k d'' hget
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at h_acc₁
        rw [← hkeq] at h_acc₁
        rw [IndexMap.getByKey_insert_self] at h_acc₁
        cases h_acc₁
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at h_acc₁
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at h_acc₁
      exact h_acc₁

-- From: CompilerProgress.lean:L4668
/-- Inserting `.function newF` at `fName` preserves CtorPresent when
`fName` doesn't collide with any existing dt key or pushed ctor key. -/
private theorem insert_fn_preserves_ctorPresent
    (acc : Typed.Decls) (fName : Global) (newF : Typed.Function)
    (hAcc : TypedCtorPresentP acc)
    (hFresh : ∀ k dt c, acc.getByKey k = some (.dataType dt) →
      c ∈ dt.constructors →
      fName ≠ k ∧ fName ≠ dt.name.pushNamespace c.nameHead) :
    TypedCtorPresentP
      (acc.insert fName (.function newF)) := by
  intro k dt c hget hc
  by_cases hkn : (fName == k) = true
  · have hkEq : fName = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (fName == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    obtain ⟨cc, hccget⟩ := hAcc k dt c hget hc
    have ⟨_hne1, hne2_prop⟩ := hFresh k dt c hget hc
    have hne2 : (fName == dt.name.pushNamespace c.nameHead) = false := by
      by_cases h' : (fName == dt.name.pushNamespace c.nameHead) = true
      · exact absurd (LawfulBEq.eq_of_beq h') hne2_prop
      · exact Bool.not_eq_true _ |>.mp h'
    refine ⟨cc, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
    exact hccget

-- From: CompilerProgress.lean:L4151
/-- `pushNamespace` is never a prefix of itself: `g ≠ g.pushNamespace s`. -/
private theorem ne_pushNamespace_self (g : Global) (s : String) :
    g ≠ g.pushNamespace s := by
  intro h
  have h' : g.toName = g.toName.mkStr s := Global.mk.inj h
  have h'' : Lean.Name.str g.toName s = g.toName := h'.symm
  exact Name_str_ne_self g.toName s h''

-- From: CompilerProgress.lean:L4696
/-- Phase-3 preservation: the full `newFunctions` fold preserves
CtorPresent given a freshness hypothesis at each step. -/
private theorem newFunctions_preserves_ctorPresent
    (init : Typed.Decls) (mono : MonoMap) (typedDecls : Typed.Decls)
    (newFunctions : Array Typed.Function)
    (hInit : TypedCtorPresentP init)
    (hFresh : ∀ f ∈ newFunctions, ∀ k dt c,
      init.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
      f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead) :
    let emptySubst : Global → Option Typ := fun _ => none
    TypedCtorPresentP (newFunctions.foldl
      (fun acc f =>
        let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
        let newOutput := rewriteTyp emptySubst mono f.output
        let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
        let newF : Typed.Function :=
          { f with inputs := newInputs, output := newOutput, body := newBody }
        acc.insert f.name (.function newF))
      init) := by
  -- Strengthened invariant: acc satisfies CtorPresent AND every (k, .dataType dt)
  -- in acc is already present in init. This lets us apply `hFresh` (which is
  -- stated relative to `init`) at each step.
  let emptySubst : Global → Option Typ := fun _ => none
  let step : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
    let newOutput := rewriteTyp emptySubst mono f.output
    let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
    let newF : Typed.Function :=
      { f with inputs := newInputs, output := newOutput, body := newBody }
    acc.insert f.name (.function newF)
  let Q : Typed.Decls → Prop := fun acc =>
    TypedCtorPresentP acc ∧
    ∀ k dt, acc.getByKey k = some (.dataType dt) →
      init.getByKey k = some (.dataType dt)
  suffices h : Q (newFunctions.foldl step init) from h.1
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => Q acc)
  · exact ⟨hInit, fun _ _ h => h⟩
  · intro i acc hQ
    have hfmem : newFunctions[i.val]'i.isLt ∈ newFunctions := Array.getElem_mem _
    have hFreshAt : ∀ k dt c,
        acc.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
        (newFunctions[i.val]'i.isLt).name ≠ k ∧
        (newFunctions[i.val]'i.isLt).name ≠ dt.name.pushNamespace c.nameHead := by
      intro k dt c hget hc
      have hget_init : init.getByKey k = some (.dataType dt) := hQ.2 k dt hget
      exact hFresh (newFunctions[i.val]'i.isLt) hfmem k dt c hget_init hc
    refine ⟨?_, ?_⟩
    · -- CtorPresent preserved via `insert_fn_preserves_ctorPresent`.
      exact insert_fn_preserves_ctorPresent acc
        (newFunctions[i.val]'i.isLt).name _ hQ.1 hFreshAt
    · -- dataType-in-init preserved: insert only adds a .function entry.
      intro k dt hget
      simp only [step] at hget
      by_cases hkn : (newFunctions[i].name == k) = true
      · have hkEq : newFunctions[i].name = k := LawfulBEq.eq_of_beq hkn
        rw [← hkEq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (newFunctions[i].name == k) = false :=
          Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hQ.2 k dt hget

/-! ### Phase-3 freshness discharge: from `hFreshFn` + `NewFnBridge` +
`NewDtBridge` + `hFreshDt`, derive the per-step freshness condition
needed by `newFunctions_preserves_ctorPresent`.

For `.dataType dt` at `k` in the post-Phase-2 acc:
* Origin A: `dt` came from Phase 1 (source `.dataType`). Then `k = dt.name`
  by `hDt`. Need `f.name ≠ dt.name` and `f.name ≠ dt.name.pushNamespace c.nameHead`.
  - `f.name ≠ dt.name.pushNamespace c.nameHead`: via `hFreshFn` + `hP`+`hCtor`
    on source (source `.constructor dt c'` at `dt.name.pushNamespace c'.nameHead`;
    `f.name ≠` this key).
  - `f.name ≠ dt.name = k`: source IndexMap-key uniqueness + `NewFnBridge`
    (f origin is source `.function`; can't equal source `.dataType` key).
* Origin B: `dt` came from Phase 2 (`newDataTypes`). Then `dt.name = g` for
  some source dt `g`. Need:
  - `f.name ≠ dt.name = g`: `NewFnBridge` says `f.name = g'` for source fn `g'`;
    source key uniqueness gives `g' ≠ g`.
  - `f.name ≠ dt.name.pushNamespace c.nameHead`: `c.nameHead ∈ orig.constructors.map
    (·.nameHead)` (via `NewDtBridge`); source has `.constructor orig cc` at
    `g.pushNamespace c.nameHead` (via `hP` + `hCtor`). Apply `hFreshFn`.
-/

-- From: CompilerProgress.lean:L3981
/-- Phase-2 trace: a `.dataType dt_mid` at `k` in `phase2Acc` either came from
fromSource (traces back via `fromSource_dt_trace`) or from `newDataTypes`. -/
private theorem phase2Acc_dt_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (newDataTypes : Array DataType)
    (k : Global) (dt_mid : DataType)
    (hget : (phase2Acc typedDecls mono newDataTypes).getByKey k =
      some (.dataType dt_mid)) :
    (∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧ dt_mid = rewriteDt mono dtSrc) ∨
    (∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧
        dt_mid = rewriteDt mono dt_orig) := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_mid, acc.getByKey k = some (.dataType dt_mid) →
      (∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
          dtSrc.params.isEmpty = true ∧ dt_mid = rewriteDt mono dtSrc) ∨
      (∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧
          dt_mid = rewriteDt mono dt_orig)
  suffices h : P (phase2Acc typedDecls mono newDataTypes) from h k dt_mid hget
  unfold phase2Acc
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_mid hget
    exact Or.inl (fromSource_dt_trace typedDecls mono k dt_mid hget)
  · intro i acc hP k dt_mid hget
    have hdt_mem : newDataTypes[i.val]'i.isLt ∈ newDataTypes := Array.getElem_mem _
    have hCtorFold : ∀ (ctors : List Constructor) (newDt : DataType)
        (dt_name : Global) (init : Typed.Decls),
        P init →
        P (ctors.foldl
          (fun acc'' c =>
            acc''.insert (dt_name.pushNamespace c.nameHead)
              (.constructor newDt c))
          init) := by
      intro ctors newDt dt_name
      induction ctors with
      | nil => intro init hP'; exact hP'
      | cons hd tl ih =>
        intro init hPinit
        simp only [List.foldl_cons]
        apply ih
        intro k dt_mid hget
        by_cases hkn : (dt_name.pushNamespace hd.nameHead == k) = true
        · have hkEq : dt_name.pushNamespace hd.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dt_name.pushNamespace hd.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPinit k dt_mid hget
    have hPouter : P (acc.insert (newDataTypes[i.val]'i.isLt).name
        (.dataType (rewriteDt mono (newDataTypes[i.val]'i.isLt)))) := by
      intro k' dt_mid' hget'
      by_cases hkn : ((newDataTypes[i.val]'i.isLt).name == k') = true
      · have hkEq : (newDataTypes[i.val]'i.isLt).name = k' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget'
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget'
        refine Or.inr ⟨newDataTypes[i.val]'i.isLt, hdt_mem, rfl, ?_⟩
        rw [← hget']
      · have hne : ((newDataTypes[i.val]'i.isLt).name == k') = false :=
          Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget'
        exact hP k' dt_mid' hget'
    exact hCtorFold _ _ _ _ hPouter k dt_mid hget

/-! ### Phase-1 axiom (pass-through).

Discharge path: processed/remaining split on `typedDecls.pairs.toList`,
parallel to `concretizeBuild_ctorIsKey` in this file. Key fact: every
source entry rewrites to an entry at the same key with structurally-matching
`dt` payload.
-/

-- From: CompilerProgress.lean:L4582
/-- Phase-2 freshness discharge: from `hFreshDt` + structure of fromSource,
derive the freshness hypothesis needed by `withNewDts_preserves_ctorPresent`.

After Phase 1 (`fromSource`), a `.dataType dt_new` at key `k` corresponds
to a source `.dataType dt_orig` at `k`, where `dt_new = {dt_orig with
ctors := rewrittenCtors}`. So `dt_new.name = dt_orig.name` and
`dt_new.constructors.map (·.nameHead) = dt_orig.constructors.map
(·.nameHead)` (actual rewriting preserves nameHead).

The freshness obligation at Phase 2 becomes: `dt.name ≠ dt_new.name.pushNamespace
c'.nameHead` for `c' ∈ dt_new.constructors`. Since `dt_new.name = dt_orig.name`
and `c'.nameHead = c_src.nameHead` for some `c_src ∈ dt_orig.constructors`
(via the rewriting map), and source has `.constructor dt_orig c_src_wit`
at `dt_orig.name.pushNamespace c_src.nameHead` (by hP), the freshness
follows from `hFreshDt` (which rules out `dt.name = dt_orig.name.pushNamespace
c_src.nameHead`). -/
private theorem phase2_freshness_discharge
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (newDataTypes : Array DataType)
    (hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := typedDecls.pairs.foldl
      (fun acc p =>
        let (key, d) := p
        match d with
        | .function f =>
          if f.params.isEmpty then
            let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
            let newOutput := rewriteTyp emptySubst mono f.output
            let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
            acc.insert key (.function
              { f with inputs := newInputs, output := newOutput, body := newBody })
          else acc
        | .dataType dt =>
          if dt.params.isEmpty then
            let newCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            acc.insert key (.dataType { dt with constructors := newCtors })
          else acc
        | .constructor dt c =>
          if dt.params.isEmpty then
            let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
            let newCtor : Constructor := { c with argTypes := newArgTypes }
            let rewrittenCtors := dt.constructors.map fun c' =>
              { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            acc.insert key (.constructor newDt newCtor)
          else acc)
      default
    ∀ dt ∈ newDataTypes, ∀ k dt' c,
      fromSource.getByKey k = some (.dataType dt') → c ∈ dt'.constructors →
      dt.name ≠ dt'.name.pushNamespace c.nameHead := by
  intro emptySubst fS
  show ∀ dt ∈ newDataTypes, ∀ k dt' c,
    (fromSource typedDecls mono).getByKey k = some (.dataType dt') →
    c ∈ dt'.constructors →
    dt.name ≠ dt'.name.pushNamespace c.nameHead
  intro dt hdt_mem k dt_new c hget hc
  obtain ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ :=
    fromSource_dt_trace typedDecls mono k dt_new hget
  have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
  have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
  have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
  rw [rewriteDt_constructors] at hc_new
  rw [List.mem_map] at hc_new
  obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
  have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
  obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
  have hfresh_src := hFreshDt dt hdt_mem
    (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
  have hcc_is_key := hCtor (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
  have hcc_head : cc.nameHead = c'.nameHead := by
    have := pushNamespace_right_inj hcc_is_key
    exact this.symm
  have hname_new : dt_new.name = dtSrc.name := by rw [hdt_eq]
  rw [hname_new, hhead, ← hcc_head]
  exact hfresh_src

/-! ### Phase-3 lemma: `newFunctions` fold preserves CtorPresent. -/

-- From: CompilerProgress.lean:L4781
private theorem phase3_freshness_discharge
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    (hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    let emptySubst : Global → Option Typ := fun _ => none
    let postPhase2 : Typed.Decls := newDataTypes.foldl
      (fun acc dt =>
        let rewrittenCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        let acc' := acc.insert dt.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
              let newOutput := rewriteTyp emptySubst mono f.output
              let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
            else acc
          | .dataType dt =>
            if dt.params.isEmpty then
              let newCtors := dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
              acc.insert key (.dataType { dt with constructors := newCtors })
            else acc
          | .constructor dt c =>
            if dt.params.isEmpty then
              let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
              let newCtor : Constructor := { c with argTypes := newArgTypes }
              let rewrittenCtors := dt.constructors.map fun c' =>
                { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
              let newDt : DataType := { dt with constructors := rewrittenCtors }
              acc.insert key (.constructor newDt newCtor)
            else acc)
        default)
    ∀ f ∈ newFunctions, ∀ k dt c,
      postPhase2.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
      f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead := by
  intro emptySubst postPhase2
  show ∀ f ∈ newFunctions, ∀ k dt c,
    (phase2Acc typedDecls mono newDataTypes).getByKey k = some (.dataType dt) →
    c ∈ dt.constructors →
    f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead
  intro f hf_mem k dt_mid c hget hc
  rcases phase2Acc_dt_trace typedDecls mono newDataTypes k dt_mid hget with
    ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ | ⟨dt_orig, hdt_orig_mem, hk_eq, hdt_eq⟩
  · -- Origin A: Phase-1 source.
    have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
    have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
    have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
    rw [rewriteDt_constructors] at hc_new
    rw [List.mem_map] at hc_new
    obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
    have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
    obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
    have hcc_is_key := hCtor (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
    have hcc_head : cc.nameHead = c'.nameHead := by
      have := pushNamespace_right_inj hcc_is_key
      exact this.symm
    obtain ⟨g', orig_f, hget_g', hf_name⟩ := hNewFnBridge f hf_mem
    refine ⟨?_, ?_⟩
    · rw [hf_name]
      intro hgk
      have : typedDecls.getByKey g' = some (.dataType dtSrc) := by rw [hgk]; exact hget_src
      rw [hget_g'] at this
      cases this
    · rw [hdt_eq, rewriteDt_name, hhead]
      have := hFreshFn f hf_mem (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
      rw [← hcc_head]
      exact this
  · -- Origin B: Phase-2 new dt.
    obtain ⟨g, orig, hget_g_src, hname_eq, hhead_eq⟩ := hNewDtBridge dt_orig hdt_orig_mem
    have hc_new : c ∈ (rewriteDt mono dt_orig).constructors := by rw [← hdt_eq]; exact hc
    rw [rewriteDt_constructors] at hc_new
    rw [List.mem_map] at hc_new
    obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
    have hhead_c : c.nameHead = c'.nameHead := by rw [← hc'_eq]
    have hc'_head_in : c'.nameHead ∈ orig.constructors.map (·.nameHead) := by
      rw [← hhead_eq]
      rw [List.mem_map]
      exact ⟨c', hc'_mem, rfl⟩
    rw [List.mem_map] at hc'_head_in
    obtain ⟨c_orig, hc_orig_mem, hc_orig_head⟩ := hc'_head_in
    obtain ⟨cc, hcc_get⟩ := hP g orig c_orig hget_g_src hc_orig_mem
    have hcc_is_key := hCtor (orig.name.pushNamespace c_orig.nameHead) orig cc hcc_get
    have hcc_head : cc.nameHead = c_orig.nameHead := by
      have := pushNamespace_right_inj hcc_is_key
      exact this.symm
    have hg_name : g = orig.name := hDt g orig hget_g_src
    obtain ⟨g', orig_f, hget_g'_src, hf_name⟩ := hNewFnBridge f hf_mem
    refine ⟨?_, ?_⟩
    · rw [hk_eq, hname_eq, hf_name]
      intro hgeq
      have : typedDecls.getByKey g' = some (.dataType orig) := by rw [hgeq]; exact hget_g_src
      rw [hget_g'_src] at this
      cases this
    · rw [hdt_eq, rewriteDt_name, hname_eq, hhead_c]
      rw [← hc_orig_head]
      have hfresh := hFreshFn f hf_mem (orig.name.pushNamespace c_orig.nameHead) orig cc hcc_get
      rw [← hg_name] at hfresh
      rw [← hcc_head]
      exact hfresh

/-! ### Final body theorem.

Closes the body of `concretizeBuild_ctorPresent` (below) using the four
phase lemmas + direct `IndexMap.insert` analysis in
`insert_fn_preserves_ctorPresent`.
-/

-- From: CompilerProgress.lean:L4126
/-- If pushed keys are equal, both prefix globals and the suffix strings match. -/
private theorem pushNamespace_inj_both {g₁ g₂ : Global} {s t : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace t) : g₁ = g₂ ∧ s = t := by
  have h' : g₁.toName.mkStr s = g₂.toName.mkStr t := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g₁.toName s = Lean.Name.str g₂.toName t := h'
  refine ⟨?_, ?_⟩
  · have hn : g₁.toName = g₂.toName := by injection h''
    cases g₁; cases g₂; simp_all
  · injection h''

-- From: CompilerProgress.lean:L3605
/-- `Global.pushNamespace` is injective in its string argument (for any fixed
prefix). -/
private theorem pushNamespace_right_inj {g : Global} {s t : String}
    (h : g.pushNamespace s = g.pushNamespace t) : s = t := by
  have h' : g.toName.mkStr s = g.toName.mkStr t := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g.toName s = Lean.Name.str g.toName t := h'
  injection h''

-- From: CompilerProgress.lean:L4159
/-- Rest-fold preserves an entry at `dt_name.pushNamespace ch` when `ch` isn't in
`rest.map (·.nameHead)`. -/
private theorem restFold_preserves_unvisited
    (dt_name : Global) (newDt : DataType) (rest : List Constructor)
    (ch : String) (hch_nin : ch ∉ rest.map (·.nameHead))
    (acc : Typed.Decls) (c₀ : Constructor)
    (hc₀ : acc.getByKey (dt_name.pushNamespace ch) = some (.constructor newDt c₀)) :
    (rest.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc).getByKey (dt_name.pushNamespace ch) = some (.constructor newDt c₀) := by
  induction rest generalizing acc with
  | nil => simp [hc₀]
  | cons c' rest' ih =>
    simp only [List.foldl_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at hch_nin
    have ⟨hne_head, hch_nin_rest⟩ := hch_nin
    apply ih hch_nin_rest
    have hne : (dt_name.pushNamespace c'.nameHead == dt_name.pushNamespace ch) = false := by
      cases hbeq : (dt_name.pushNamespace c'.nameHead == dt_name.pushNamespace ch) with
      | false => rfl
      | true =>
        have heq := LawfulBEq.eq_of_beq hbeq
        have hs_eq := (pushNamespace_inj_both heq).2
        exact absurd hs_eq.symm hne_head
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    exact hc₀

-- From: CompilerProgress.lean:L3595
private theorem rewriteC_nameHead (mono : MonoMap) (c : Constructor) :
    (rewriteC mono c).nameHead = c.nameHead := rfl

-- From: CompilerProgress.lean:L3601
private theorem rewriteDt_constructors (mono : MonoMap) (dt : DataType) :
    (rewriteDt mono dt).constructors =
      dt.constructors.map (rewriteC mono) := rfl

-- From: CompilerProgress.lean:L3598
private theorem rewriteDt_name (mono : MonoMap) (dt : DataType) :
    (rewriteDt mono dt).name = dt.name := rfl

-- From: CompilerProgress.lean:L4395
private theorem withNewDts_preserves_ctorPresent
    (init : Typed.Decls) (mono : MonoMap) (newDataTypes : Array DataType)
    (hInit : TypedCtorPresentP init)
    (hInitDt : TypedDtNameIsKeyP init)
    (hFresh : ∀ dt ∈ newDataTypes, ∀ k dt' c,
      init.getByKey k = some (.dataType dt') → c ∈ dt'.constructors →
      -- The new dt's name is distinct from existing ctor witness keys.
      dt.name ≠ dt'.name.pushNamespace c.nameHead)
    (hMutualFresh : ∀ dt ∈ newDataTypes, ∀ dt' ∈ newDataTypes,
      ∀ ch ∈ dt'.constructors.map (·.nameHead),
      dt.name ≠ dt'.name.pushNamespace ch) :
    let emptySubst : Global → Option Typ := fun _ => none
    TypedCtorPresentP (newDataTypes.foldl
      (fun acc dt =>
        let rewrittenCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        let acc' := acc.insert dt.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      init) := by
  intro emptySubst
  -- Invariant Q: CtorPresent + DtNameIsKey + every .dataType entry either
  -- traces to `init` (same key+payload) or to some `dt_orig ∈ newDataTypes`
  -- with payload `rewriteDt mono dt_orig` at key `dt_orig.name`.
  let Q : Typed.Decls → Prop := fun acc =>
    TypedCtorPresentP acc ∧ TypedDtNameIsKeyP acc ∧
    ∀ k d, acc.getByKey k = some (.dataType d) →
      init.getByKey k = some (.dataType d) ∨
      ∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧ d = rewriteDt mono dt_orig
  suffices h : Q (newDataTypes.foldl
      (fun acc dt =>
        let rewrittenCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        let acc' := acc.insert dt.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      init) from h.1
  apply Array.foldl_induction (motive := fun (_ : Nat) (acc : Typed.Decls) => Q acc)
  · exact ⟨hInit, hInitDt, fun k d hget => Or.inl hget⟩
  · intro i acc hQ
    -- Setup.
    generalize hdt_eq : newDataTypes[i.val]'i.isLt = dt_i
    have hdt_mem : dt_i ∈ newDataTypes := by rw [← hdt_eq]; exact Array.getElem_mem _
    let rewrittenCtors := dt_i.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt_i with constructors := rewrittenCtors }
    have hnewDt_name : newDt.name = dt_i.name := rfl
    have hrewrittenHeads : rewrittenCtors.map (·.nameHead) =
        dt_i.constructors.map (·.nameHead) := by
      simp only [rewrittenCtors, List.map_map]
      apply List.map_congr_left
      intros; rfl
    -- Outer insert: acc₀ := acc.insert dt_i.name (.dataType newDt).
    let acc₀ : Typed.Decls := acc.insert dt_i.name (.dataType newDt)
    have hacc₀_newDt : acc₀.getByKey dt_i.name = some (.dataType newDt) := by
      simp only [acc₀]; rw [IndexMap.getByKey_insert_self]
    -- Partial CtorPresent on acc₀ (skip newDt at dt_i.name).
    -- For any .dataType d' at k' in acc₀ with d'.name ≠ dt_i.name: witness exists in acc₀.
    have hAcc₀_partial : ∀ k' d' c',
        acc₀.getByKey k' = some (.dataType d') → c' ∈ d'.constructors →
        d'.name ≠ dt_i.name →
        ∃ cc, acc₀.getByKey (d'.name.pushNamespace c'.nameHead) =
          some (.constructor d' cc) := by
      intro k' d' c' hget hc' hd_ne
      -- If k' = dt_i.name, would have d' = newDt with d'.name = dt_i.name, contradicting hd_ne.
      have hk_ne : (dt_i.name == k') = false := by
        cases hbeq : (dt_i.name == k') with
        | false => rfl
        | true =>
          have hkeq := LawfulBEq.eq_of_beq hbeq
          rw [← hkeq] at hget
          simp only [acc₀] at hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          exact absurd (hget.symm ▸ hnewDt_name) hd_ne
      simp only [acc₀] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hk_ne] at hget
      obtain ⟨cc, hccget⟩ := hQ.1 k' d' c' hget hc'
      -- Witness key ≠ dt_i.name (via freshness).
      have hwit_ne : dt_i.name ≠ d'.name.pushNamespace c'.nameHead := by
        intro h'
        rcases hQ.2.2 k' d' hget with horig_init | ⟨dt_orig, hdt_orig_mem, hk_eq, hd_eq⟩
        · exact hFresh dt_i hdt_mem k' d' c' horig_init hc' h'
        · have hd_name : d'.name = dt_orig.name := by rw [hd_eq, rewriteDt_name]
          have hc_mem_orig : c'.nameHead ∈ dt_orig.constructors.map (·.nameHead) := by
            rw [hd_eq, rewriteDt_constructors] at hc'
            -- hc' : c' ∈ dt_orig.constructors.map (rewriteC mono)
            simp only [List.mem_map] at hc'
            obtain ⟨co, hco_mem, hco_eq⟩ := hc'
            simp only [List.mem_map]
            exact ⟨co, hco_mem, by rw [← hco_eq]⟩
          have := hMutualFresh dt_i hdt_mem dt_orig hdt_orig_mem c'.nameHead hc_mem_orig
          rw [← hd_name] at this
          exact absurd h' this
      have hne_wit : (dt_i.name == d'.name.pushNamespace c'.nameHead) = false := by
        cases hbeq : (dt_i.name == d'.name.pushNamespace c'.nameHead) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hwit_ne
      refine ⟨cc, ?_⟩
      simp only [acc₀]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_wit]
      exact hccget
    -- DtNameIsKey on acc₀.
    have hAcc₀Dt : TypedDtNameIsKeyP acc₀ := by
      intro k' d' hget
      by_cases hk : (dt_i.name == k') = true
      · have hkeq := LawfulBEq.eq_of_beq hk
        rw [← hkeq] at hget
        simp only [acc₀] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        rw [← hkeq, ← hget]
      · have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk
        simp only [acc₀] at hget
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hQ.2.1 k' d' hget
    -- Freshness for inner fold.
    have hfreshPush : ∀ k'' d'' c'' ch,
        acc₀.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
        ch ∈ rewrittenCtors.map (·.nameHead) →
        d''.name ≠ dt_i.name → d''.name.pushNamespace c''.nameHead ≠
          dt_i.name.pushNamespace ch := by
      intro k'' d'' c'' ch _ _ _ hd_ne heq_push
      exact hd_ne (pushNamespace_inj_both heq_push).1
    -- Call innerCtorFold_preserves.
    have hinner := innerCtorFold_preserves dt_i.name newDt rewrittenCtors
      acc₀ hAcc₀_partial hAcc₀Dt hacc₀_newDt hfreshPush
    -- Goal: Q of full step.
    refine ⟨?_, ?_, ?_⟩
    · -- TypedCtorPresentP
      intro k' d' c' hget hc'
      by_cases hk_eq : (dt_i.name == k') = true
      · -- k' = dt_i.name: d' = newDt, witness via hinner.1 on c'.nameHead.
        have hkeq := LawfulBEq.eq_of_beq hk_eq
        have hacc₀_k := hinner.2.2.2.2 k' d' hget
        rw [← hkeq] at hacc₀_k
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_self] at hacc₀_k
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hacc₀_k
        -- d' = newDt.
        subst hacc₀_k
        -- c' ∈ newDt.constructors = rewrittenCtors. Need c'.nameHead in rewrittenCtors.map (·.nameHead).
        have hch_mem : c'.nameHead ∈ rewrittenCtors.map (·.nameHead) :=
          List.mem_map_of_mem hc'
        obtain ⟨cc, hcc⟩ := hinner.1 c'.nameHead hch_mem
        refine ⟨cc, ?_⟩
        -- Unfold acc₀ in hcc. Goal has newDt.name (= dt_i.name, rfl).
        simp only [acc₀] at hcc
        exact hcc
      · -- k' ≠ dt_i.name: d' traces via hinner.2.1 (non-newDt witnesses preserved).
        have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk_eq
        have hd_key := hinner.2.2.1 k' d' hget
        -- d'.name ≠ dt_i.name?
        have hd_ne : d'.name ≠ dt_i.name := by
          intro heq_name
          rw [heq_name] at hd_key
          rw [hd_key] at hne
          simp at hne
        exact hinner.2.1 k' d' c' hget hc' hd_ne
    · -- TypedDtNameIsKeyP
      exact hinner.2.2.1
    · -- Trace: init or newDataTypes.
      intro k' d' hget
      have hacc₀_k := hinner.2.2.2.2 k' d' hget
      by_cases hk : (dt_i.name == k') = true
      · have hkeq := LawfulBEq.eq_of_beq hk
        rw [← hkeq] at hacc₀_k
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_self] at hacc₀_k
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hacc₀_k
        refine Or.inr ⟨dt_i, hdt_mem, ?_, ?_⟩
        · exact hkeq.symm
        · exact hacc₀_k.symm
      · have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hacc₀_k
        exact hQ.2.2 k' d' hacc₀_k

-- From: CompilerProgress.lean:L1495
/-- The inner ctor fold in `mkDecls_dataTypeStep`. Inserts each ctor at
its pushed key. Preserves `SourceCtorPresentAux` and adds the new keys. -/
private theorem SourceCtorPresentAux_ctor_fold
    (dataType' : DataType) (fullCtors : List Constructor)
    (hFullCtors : fullCtors = dataType'.constructors) :
    ∀ (ctors : List Constructor) (init result : MkDeclsAcc),
      SourceCtorPresentAux init →
      init.2.getByKey dataType'.name = some (.dataType dataType') →
      (∀ c ∈ ctors, c ∈ fullCtors) →
      (∀ c ∈ fullCtors, c ∉ ctors →
        ∃ cc, init.2.getByKey (dataType'.name.pushNamespace c.nameHead) =
          some (.constructor dataType' cc)) →
      ctors.foldlM
        (fun (acc : MkDeclsAcc) ctor =>
          let ctorName := dataType'.name.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError MkDeclsAcc)
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SourceCtorPresentAux result ∧
      result.2.getByKey dataType'.name = some (.dataType dataType') ∧
      (∀ c ∈ fullCtors,
        ∃ cc, result.2.getByKey (dataType'.name.pushNamespace c.nameHead) =
          some (.constructor dataType' cc)) := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hAux hDt _hSubset hPre hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    refine ⟨hAux, hDt, ?_⟩
    intro c hc
    exact hPre c hc (by intro h; cases h)
  | cons c rest ih =>
    intro init result hAux hDt hSubset hPre hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hstep
    split at hstep
    · exact absurd hstep (by intro h; cases h)
    rename_i hNotIn
    simp only [Except.ok.injEq] at hstep
    subst hstep
    have hcFull : c ∈ fullCtors := hSubset c (List.Mem.head _)
    have hAuxNew : SourceCtorPresentAux
        (init.1.insert (dataType'.name.pushNamespace c.nameHead),
         init.2.insert (dataType'.name.pushNamespace c.nameHead)
           (.constructor dataType' c)) := by
      refine ⟨?_, ?_⟩
      · intro k dt cc' hget hcc'
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead == k) = true
        · have hkEq : dataType'.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dataType'.name.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          obtain ⟨cc, hccget⟩ := hAux.1 k dt cc' hget hcc'
          by_cases hkn2 : (dataType'.name.pushNamespace c.nameHead ==
                            dt.name.pushNamespace cc'.nameHead) = true
          · -- Collision impossible: if pushed keys match, the witness
            -- `hccget` was in init, so `init.1` contains that pushed key,
            -- but `hNotIn` says the new pushed key is not in `init.1`.
            exfalso
            have hkEq2 : dataType'.name.pushNamespace c.nameHead =
                          dt.name.pushNamespace cc'.nameHead :=
              LawfulBEq.eq_of_beq hkn2
            have hccKey : init.1.contains (dt.name.pushNamespace cc'.nameHead) = true :=
              hAux.2 _ _ hccget
            rw [← hkEq2] at hccKey
            rw [hccKey] at hNotIn
            exact absurd hNotIn (by simp)
          · have hne2 : (dataType'.name.pushNamespace c.nameHead ==
                          dt.name.pushNamespace cc'.nameHead) = false :=
              Bool.not_eq_true _ |>.mp hkn2
            refine ⟨cc, ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
            exact hccget
      · intro k v hget
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead == k) = true
        · have hkEq : dataType'.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [Std.HashSet.contains_insert]; simp
        · have hne : (dataType'.name.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          rw [Std.HashSet.contains_insert]
          have := hAux.2 k v hget; rw [this]; simp
    have hDtNew : (init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c)).getByKey dataType'.name =
        some (Source.Declaration.dataType dataType') := by
      have hkNe : (dataType'.name.pushNamespace c.nameHead == dataType'.name) = false := by
        cases hh : (dataType'.name.pushNamespace c.nameHead == dataType'.name) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hh
          have hInInit : init.1.contains dataType'.name = true := hAux.2 _ _ hDt
          have : init.1.contains (dataType'.name.pushNamespace c.nameHead) = true := by
            rw [heq]; exact hInInit
          rw [this] at hNotIn
          exact absurd hNotIn (by simp)
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hkNe]
      exact hDt
    have hSubsetNew : ∀ c' ∈ rest, c' ∈ fullCtors := by
      intro c' hc'mem
      exact hSubset c' (List.Mem.tail _ hc'mem)
    have hPreNew : ∀ c' ∈ fullCtors, c' ∉ rest →
        ∃ cc, (init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c)).getByKey
              (dataType'.name.pushNamespace c'.nameHead) =
            some (.constructor dataType' cc) := by
      intro c' hc'full hc'notrest
      by_cases hcc' : c' = c
      · refine ⟨c, ?_⟩
        rw [hcc']
        exact IndexMap.getByKey_insert_self _ _ _
      · have hc'notall : c' ∉ (c :: rest) := by
          intro hmem
          rcases List.mem_cons.mp hmem with heq | htail
          · exact hcc' heq
          · exact hc'notrest htail
        obtain ⟨cc, hccget⟩ := hPre c' hc'full hc'notall
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead ==
                         dataType'.name.pushNamespace c'.nameHead) = true
        · refine ⟨c, ?_⟩
          have hkEq := LawfulBEq.eq_of_beq hkn
          rw [← hkEq]
          exact IndexMap.getByKey_insert_self _ _ _
        · have hne : (dataType'.name.pushNamespace c.nameHead ==
                        dataType'.name.pushNamespace c'.nameHead) = false :=
            Bool.not_eq_true _ |>.mp hkn
          refine ⟨cc, ?_⟩
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hccget
    exact ih _ _ hAuxNew hDtNew hSubsetNew hPreNew hfold

-- From: CompilerProgress.lean:L1410
private theorem SourceCtorPresentAux_default :
    SourceCtorPresentAux (({}, default) : MkDeclsAcc) := by
  refine ⟨SourceCtorPresentP_default, ?_⟩
  intro k v hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

-- From: CompilerProgress.lean:L5415
private theorem TypedCtorIsKeyP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.CtorIsKey d) : TypedCtorIsKeyP d := by
  intro k dt c hget
  exact hP k dt c (IndexMap.mem_pairs_of_getByKey _ _ _ hget)

/-! ### `hFresh_bridge` infrastructure

Ported from `HFreshBridgeScratch.lean`. Derives newDataTypes/newFunctions
names disjoint from pushed-ctor-keys in typedDecls via `DrainState.NewNameShape`. -/

-- From: CompilerProgress.lean:L977
private theorem TypedCtorPresentP_default :
    TypedCtorPresentP (default : Typed.Decls) := by
  intro k dt c hget _hc
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

-- From: CompilerProgress.lean:L5400
/-- Bridge: get `TypedCtorPresentP` from `Typed.Decls.CtorPresent`. -/
private theorem TypedCtorPresentP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.CtorPresent d) : TypedCtorPresentP d := by
  intro k dt c hget hc
  have hmem : (k, Typed.Declaration.dataType dt) ∈ d.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  obtain ⟨cc, hcmem⟩ := hP k dt c hmem hc
  exact ⟨cc, IndexMap.getByKey_of_mem_pairs _ _ _ hcmem⟩

-- From: CompilerProgress.lean:L2695
private theorem TypedDecls_DtNameIsKey_pairs_of_gen
    {d : Typed.Decls}
    (hP : ∀ k dt, d.getByKey k = some (.dataType dt) → k = dt.name) :
    TypedDecls_DtNameIsKey_pairs d := by
  intro key dt hmem
  exact hP key dt (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)

-- From: CompilerProgress.lean:L5409
/-- Bridge: `TypedDtNameIsKey` (pairs form) ⇒ getByKey form. -/
private theorem TypedDtNameIsKeyP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.DtNameIsKey d) : TypedDtNameIsKeyP d := by
  intro k dt hget
  exact hP k dt (IndexMap.mem_pairs_of_getByKey _ _ _ hget)

-- From: CompilerProgress.lean:L5590
/-- Helper for Arrays. -/
private theorem array_foldl_insert_fn_containsKey
    (step : Typed.Decls → Typed.Function → Typed.Decls)
    (hstep_self : ∀ acc f, (step acc f).containsKey f.name)
    (hstep_mono : ∀ acc a f, acc.containsKey a → (step acc f).containsKey a)
    (xs : Array Typed.Function) (init : Typed.Decls) :
    ∀ f ∈ xs, (xs.foldl step init).containsKey f.name := by
  intro f hfmem
  rw [← Array.foldl_toList]
  have hfmem_list : f ∈ xs.toList := Array.mem_toList_iff.mpr hfmem
  exact list_foldl_insert_fn_containsKey step hstep_self hstep_mono xs.toList init f hfmem_list

-- From: CompilerProgress.lean:L5034
private theorem concretizeBuild_ctorPresent
    {typedDecls : Typed.Decls}
    (hP : TypedCtorPresentP typedDecls)
    (_hDt : TypedDtNameIsKeyP typedDecls)
    (_hCtor : TypedCtorIsKeyP typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    -- Freshness: new datatypes don't shadow an existing ctor witness' key.
    (_hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead)
    -- Freshness: new functions don't shadow an existing ctor witness' key.
    (_hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    -- FullyMono-implied structural correspondence of drained `newDataTypes`/
    -- `newFunctions` to source decls.
    (_hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (_hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    TypedCtorPresentP
      (concretizeBuild typedDecls mono newFunctions newDataTypes) :=
  CtorPresentBody.concretizeBuild_ctorPresent_body hP _hDt _hCtor mono
    newFunctions newDataTypes _hFreshDt _hFreshFn _hNewDtBridge _hNewFnBridge

-- From: CompilerProgress.lean:L5471
/-- Folding `concretizeDrainEntry` over a list preserves `NewNameShape`. -/
private theorem concretizeDrainEntry_list_foldlM_preserves_NewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.NewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.NewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.NewNameShape decls :=
        concretizeDrainEntry_preserves_NewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

-- From: CompilerProgress.lean:L5858
private theorem concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.StrongNewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.StrongNewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.StrongNewNameShape decls :=
        concretizeDrainEntry_preserves_StrongNewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

-- From: CompilerProgress.lean:L5425
/-- `concretizeDrainEntry` preserves `NewNameShape`. -/
private theorem concretizeDrainEntry_preserves_NewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.NewNameShape decls := by
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
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · obtain ⟨g, args, f_orig, hname, hget⟩ := hinv.1 f' hin
            exact ⟨g, args, f_orig, hname, hget⟩
          · subst heq
            refine ⟨entry.1, entry.2, f, ?_, ?_⟩
            · show concretizeName entry.1 entry.2 = concretizeName entry.1 entry.2; rfl
            · exact hf_get
        · intro dt hdt
          exact hinv.2 dt hdt
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, ?_, ?_⟩
            · show concretizeName entry.1 entry.2 = concretizeName entry.1 entry.2; rfl
            · exact hdt_get
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

-- From: CompilerProgress.lean:L5814
private theorem concretizeDrainEntry_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · exact hinv.1 f' hin
          · subst heq
            exact ⟨entry.1, entry.2, f, rfl, hf_get, hsz.symm⟩
        · intro dt hdt
          exact hinv.2 dt hdt
      · simp [hsz] at hstep
    · rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, rfl, hdt_get, hsz.symm, ?_⟩
            rw [List.map_map]
            apply List.map_congr_left
            intro c _
            rfl
      · simp [hsz] at hstep
    · exact absurd hstep (by intro h; cases h)

-- From: CompilerProgress.lean:L5492
/-- `concretizeDrainIter` preserves `NewNameShape`. -/
private theorem concretizeDrainIter_preserves_NewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.NewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

-- From: CompilerProgress.lean:L5878
private theorem concretizeDrainIter_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.StrongNewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

-- From: CompilerProgress.lean:L5505
/-- `concretizeDrain` preserves `NewNameShape`. -/
private theorem concretize_drain_preserves_NewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.NewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.NewNameShape decls := by
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
        have hinv' : state'.NewNameShape decls :=
          concretizeDrainIter_preserves_NewNameShape hinv hstate'
        exact ih state' hinv' hdrain

-- From: CompilerProgress.lean:L5890
private theorem concretize_drain_preserves_StrongNewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.StrongNewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.StrongNewNameShape decls := by
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
        have hinv' : state'.StrongNewNameShape decls :=
          concretizeDrainIter_preserves_StrongNewNameShape hinv hstate'
        exact ih state' hinv' hdrain

-- From: CompilerProgress.lean:L5549
/-- Same for `newDataTypes`. -/
private theorem drain_newDataTypes_name_shape
    {tds : Typed.Decls} {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ dt ∈ drained.newDataTypes,
      ∃ (g : Global) (args : Array Typ) (dt_orig : DataType),
        dt.name = concretizeName g args ∧
        tds.getByKey g = some (.dataType dt_orig) := by
  have hinit : DrainState.NewNameShape tds _ :=
    DrainState.NewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_NewNameShape _ _ hinit hdrain
  exact hfinal.2

-- From: CompilerProgress.lean:L5658
/-- Every `drained.newDataTypes` name is in `cd`. -/
private theorem drain_newDt_in_cd
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ dt ∈ drained.newDataTypes, ∃ d, cd.getByKey dt.name = some d := by
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · contradiction
  rename_i drained' hdrain'
  have hdrained_eq : drained = drained' := by
    have heq : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := ∅, mono := ∅,
          newFunctions := #[], newDataTypes := #[] } = .ok drained := hdrain
    rw [heq] at hdrain'
    exact Except.ok.inj hdrain'
  rw [← hdrained_eq] at hconc'
  let monoDecls : Typed.Decls := concretizeBuild tds drained.mono
    drained.newFunctions drained.newDataTypes
  have hstep4 : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc'
  intro dt hdt_mem
  have array_foldl_mono : ∀ {γ : Type}
      (step : Typed.Decls → γ → Typed.Decls)
      (_ : ∀ acc a c, acc.containsKey a → (step acc c).containsKey a)
      (xs : Array γ) (init : Typed.Decls) (a : Global),
      init.containsKey a → (xs.foldl step init).containsKey a := by
    intro γ step hmono xs init a hac
    rw [← Array.foldl_toList]
    exact list_foldl_containsKey_mono step (fun a' acc c h' => hmono acc a' c h')
      xs.toList init a hac
  have hdt_in_mono : monoDecls.containsKey dt.name := by
    show (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).containsKey dt.name
    unfold concretizeBuild
    simp only
    apply array_foldl_mono _
      (fun acc a f hac => IndexMap.containsKey_insert_preserves _ _ _ _ hac)
    have hdt_list : dt ∈ drained.newDataTypes.toList := Array.mem_toList_iff.mpr hdt_mem
    let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt' =>
      let rewrittenCtors := dt'.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
      let newDt : DataType := { dt' with constructors := rewrittenCtors }
      let acc' := acc.insert dt'.name (.dataType newDt)
      rewrittenCtors.foldl
        (fun acc'' c =>
          let cName := dt'.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc'
    have dtStep_mono : ∀ (init : Typed.Decls) (dt' : DataType) (a : Global),
        init.containsKey a → (dtStep init dt').containsKey a := by
      intro init dt' a hac
      simp only [dtStep]
      apply list_foldl_containsKey_mono (γ := Constructor) _
        (fun _a _acc _c hac' => IndexMap.containsKey_insert_preserves _ _ _ _ hac')
      exact IndexMap.containsKey_insert_preserves _ _ _ _ hac
    have dtStep_self : ∀ (init : Typed.Decls) (dt' : DataType),
        (dtStep init dt').containsKey dt'.name := by
      intro init dt'
      simp only [dtStep]
      apply list_foldl_containsKey_mono (γ := Constructor) _
        (fun _a _acc _c hac' => IndexMap.containsKey_insert_preserves _ _ _ _ hac')
      exact IndexMap.containsKey_insert_self _ _ _
    rw [← Array.foldl_toList]
    revert hdt_list
    generalize (tds.pairs.foldl _ (default : Typed.Decls)) = src0
    generalize drained.newDataTypes.toList = L
    induction L generalizing src0 with
    | nil => intro h; cases h
    | cons hd tl ih =>
      intro hmem
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst heq
        have h_mid : (_ : Typed.Decls).containsKey dt.name := dtStep_self src0 dt
        exact list_foldl_containsKey_mono _ (fun a acc c hac => dtStep_mono acc c a hac)
          tl _ _ h_mid
      · exact ih _ hrest
  have hdt_in_cd : cd.containsKey dt.name := by
    have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hstep4
    exact (hkeys dt.name).mp hdt_in_mono
  rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hdt_in_cd
  cases hget : cd.getByKey dt.name with
  | none => exact absurd hget hdt_in_cd
  | some d => exact ⟨d, rfl⟩

-- From: CompilerProgress.lean:L5616
/-- Every `drained.newFunctions` name is in `cd`. -/
private theorem drain_newFn_in_cd
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ f ∈ drained.newFunctions, ∃ d, cd.getByKey f.name = some d := by
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · contradiction
  rename_i drained' hdrain'
  have hdrained_eq : drained = drained' := by
    have heq : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := ∅, mono := ∅,
          newFunctions := #[], newDataTypes := #[] } = .ok drained := hdrain
    rw [heq] at hdrain'
    exact Except.ok.inj hdrain'
  rw [← hdrained_eq] at hconc'
  let monoDecls : Typed.Decls := concretizeBuild tds drained.mono
    drained.newFunctions drained.newDataTypes
  have hstep4 : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc'
  intro f hfmem
  have hfn_in_mono : monoDecls.containsKey f.name := by
    show (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).containsKey f.name
    unfold concretizeBuild
    apply array_foldl_insert_fn_containsKey _ _ _ drained.newFunctions _ f hfmem
    · intro acc f'
      exact IndexMap.containsKey_insert_self _ _ _
    · intro acc a f' hac
      exact IndexMap.containsKey_insert_preserves _ _ _ _ hac
  have hfn_in_cd : cd.containsKey f.name := by
    have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hstep4
    exact (hkeys f.name).mp hfn_in_mono
  rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hfn_in_cd
  cases hget : cd.getByKey f.name with
  | none => exact absurd hget hfn_in_cd
  | some d => exact ⟨d, rfl⟩

-- From: CompilerProgress.lean:L5533
/-- Every `drained.newFunctions` name is `concretizeName g args` for some drained
`(g, args)` whose source origin is a `.function` entry in `tds`. -/
private theorem drain_newFunctions_name_shape
    {tds : Typed.Decls} {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ f ∈ drained.newFunctions,
      ∃ (g : Global) (args : Array Typ) (f_orig : Typed.Function),
        f.name = concretizeName g args ∧
        tds.getByKey g = some (.function f_orig) := by
  have hinit : DrainState.NewNameShape tds _ :=
    DrainState.NewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_NewNameShape _ _ hinit hdrain
  exact hfinal.1

-- From: CompilerProgress.lean:L5747
/-- The `hFresh` bridge. -/
private theorem hFresh_bridge
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hCtor : Typed.Decls.CtorIsKey tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    (∀ dt ∈ drained.newDataTypes,
      ∀ k dt' c, tds.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead) ∧
    (∀ f ∈ drained.newFunctions,
      ∀ k dt' c, tds.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead) := by
  refine ⟨?_, ?_⟩
  · intro dt hdt_mem k dt' c hk_ctor hname_eq
    obtain ⟨g, args, dt_orig, hdt_name, hg_dt⟩ :=
      drain_newDataTypes_name_shape hdrain dt hdt_mem
    have hk_eq : k = dt'.name.pushNamespace c.nameHead := hCtor k dt' c
      (IndexMap.mem_pairs_of_getByKey _ _ _ hk_ctor)
    have hcn_eq_k : concretizeName g args = k := by
      rw [hk_eq, ← hdt_name]; exact hname_eq
    obtain ⟨d_at_dt, hd_at_dt⟩ := drain_newDt_in_cd hconc hdrain dt hdt_mem
    have hcn_empty : concretizeName k #[] = k := concretizeName_empty_args k
    have hcn_both : concretizeName g args = concretizeName k #[] := by
      rw [hcn_empty]; exact hcn_eq_k
    have hexists : ∃ d, cd.getByKey (concretizeName g args) = some d := by
      refine ⟨d_at_dt, ?_⟩
      rw [hdt_name] at hd_at_dt; exact hd_at_dt
    have := hunique hconc g k args #[] hcn_both hexists
    obtain ⟨hg_eq, _⟩ := this
    rw [hg_eq] at hg_dt
    rw [hg_dt] at hk_ctor
    cases hk_ctor
  · intro f hf_mem k dt' c hk_ctor hname_eq
    obtain ⟨g, args, f_orig, hf_name, hg_fn⟩ :=
      drain_newFunctions_name_shape hdrain f hf_mem
    have hk_eq : k = dt'.name.pushNamespace c.nameHead := hCtor k dt' c
      (IndexMap.mem_pairs_of_getByKey _ _ _ hk_ctor)
    have hcn_eq_k : concretizeName g args = k := by
      rw [hk_eq, ← hf_name]; exact hname_eq
    obtain ⟨d_at_f, hd_at_f⟩ := drain_newFn_in_cd hconc hdrain f hf_mem
    have hcn_empty : concretizeName k #[] = k := concretizeName_empty_args k
    have hcn_both : concretizeName g args = concretizeName k #[] := by
      rw [hcn_empty]; exact hcn_eq_k
    have hexists : ∃ d, cd.getByKey (concretizeName g args) = some d := by
      refine ⟨d_at_f, ?_⟩
      rw [hf_name] at hd_at_f; exact hd_at_f
    have := hunique hconc g k args #[] hcn_both hexists
    obtain ⟨hg_eq, _⟩ := this
    rw [hg_eq] at hg_fn
    rw [hg_fn] at hk_ctor
    cases hk_ctor

/-! ### Bridge derivations for `NewDtBridge` / `NewFnBridge`.

Ported from `NewBridgesScratch.lean` (2026-04-24). Derives the FullyMono-
implied structural correspondence of `drained.newDataTypes` /
`drained.newFunctions` to source `.dataType` / `.function` entries in
`tds`, via a strengthened drain invariant `StrongNewNameShape`.
-/

-- `DrainState.StrongNewNameShape` + `.init` moved to
-- `Ix/Aiur/Semantics/DrainInvariants.lean`.

-- From: CompilerProgress.lean:L5602
/-- Generic `List.foldl` preserves `containsKey` for any already-contained key
when the step is IndexMap.insert-only. -/
private theorem list_foldl_containsKey_mono
    {γ : Type}
    (step : Typed.Decls → γ → Typed.Decls)
    (hmono : ∀ a acc c, acc.containsKey a → (step acc c).containsKey a) :
    ∀ (L : List γ) (init : Typed.Decls) a,
      init.containsKey a → (L.foldl step init).containsKey a
  | [], _, _, h => h
  | hd :: tl, init, a, hac => by
    simp only [List.foldl_cons]
    exact list_foldl_containsKey_mono step hmono tl (step init hd) a
      (hmono a init hd hac)

-- From: CompilerProgress.lean:L5564
/-- Helper: List.foldl with step = `IndexMap.insert` at `Typed.Function.name`
— every `f ∈ L` has its name in the resulting map. -/
private theorem list_foldl_insert_fn_containsKey
    (step : Typed.Decls → Typed.Function → Typed.Decls)
    (hstep_self : ∀ acc f, (step acc f).containsKey f.name)
    (hstep_mono : ∀ acc a f, acc.containsKey a → (step acc f).containsKey a) :
    ∀ (L : List Typed.Function) (init : Typed.Decls) f,
      f ∈ L → (L.foldl step init).containsKey f.name
  | [], _, _, h => by cases h
  | hd :: tl, init, f, hfmem => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hfmem with heq | hrest
    · subst heq
      have hinit' : (step init f).containsKey f.name := hstep_self init f
      have hpres : ∀ (L' : List Typed.Function) (acc : Typed.Decls),
          acc.containsKey f.name → (L'.foldl step acc).containsKey f.name := by
        intro L'
        induction L' with
        | nil => intros acc h; simpa using h
        | cons hd' tl' ih' =>
          intro acc hac
          simp only [List.foldl_cons]
          exact ih' (step acc hd') (hstep_mono _ _ _ hac)
      exact hpres tl (step init f) hinit'
    · exact list_foldl_insert_fn_containsKey step hstep_self hstep_mono tl (step init hd) f hrest

-- From: CompilerProgress.lean:L5058
/-- `step4Lower` preserves `CtorPresent` as a fold-invariant: each step either
inserts a `.function` (no ctor/dt effect), a `.dataType` (establishes its own
ctors via the input's CtorPresent hypothesis and downstream fold), or a
`.constructor` (pass-through keyed at same key). -/
private theorem step4Lower_preserves_ctorPresent
    {monoDecls : Typed.Decls} {cd : Concrete.Decls}
    (hP : TypedCtorPresentP monoDecls)
    (_hDt : ∀ k dt, monoDecls.getByKey k = some (.dataType dt) → k = dt.name)
    (_hCtor : ∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
      k = dt.name.pushNamespace c.nameHead)
    (hfold : monoDecls.foldlM (init := (default : Concrete.Decls)) step4Lower = .ok cd) :
    ConcreteCtorPresentP cd := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hDtBack : ∀ k concDt, cd.getByKey k = some (.dataType concDt) →
      ∃ (dt : DataType) (ctors : List Concrete.Constructor),
        monoDecls.getByKey k = some (.dataType dt) ∧
        dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors ∧
        concDt = { name := dt.name, constructors := ctors } := by
    let Q : Concrete.Decls → Prop := fun acc =>
      ∀ k concDt, acc.getByKey k = some (.dataType concDt) →
        ∃ (dt : DataType) (ctors : List Concrete.Constructor),
          monoDecls.getByKey k = some (.dataType dt) ∧
          dt.constructors.mapM (fun c' => do
            let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
            pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors ∧
          concDt = { name := dt.name, constructors := ctors }
    have hQ0 : Q (default : Concrete.Decls) := by
      intro k concDt hget
      exfalso
      have : (default : Concrete.Decls).getByKey k = none := by
        unfold IndexMap.getByKey
        show ((default : Concrete.Decls).indices[k]?).bind _ = none
        have : (default : Concrete.Decls).indices[k]? = none := by
          show ((default : Std.HashMap Global Nat))[k]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      rw [this] at hget; cases hget
    apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
    · exact hQ0
    · intro acc ⟨name, d⟩ acc' hxmem hstep hQacc
      unfold step4Lower at hstep
      simp only at hstep
      have hname_src : monoDecls.getByKey name = some d :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
      cases d with
      | function f =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
      | dataType dt =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i ctors hctors
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Concrete.Declaration.dataType.injEq] at hget
          refine ⟨dt, ctors, hname_src, ?_, hget.symm⟩
          exact hctors
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
      | constructor dt c =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i ctors _hctors
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i argTypes _hargs
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
  have hCtorForward : ∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
      ∃ concDt concC ctors', cd.getByKey k = some (.constructor concDt concC) ∧
        concC.nameHead = c.nameHead ∧
        dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
        concDt = { name := dt.name, constructors := ctors' } := by
    intro k dt c hmonoget
    have hmem : (k, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hmonoget
    have key_helper : ∀ (processed remaining : List (Global × Typed.Declaration))
        (init finalacc : Concrete.Decls),
        processed ++ remaining = monoDecls.pairs.toList →
        (∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ processed →
          ∃ concDt concC ctors', init.getByKey k = some (.constructor concDt concC) ∧
            concC.nameHead = c.nameHead ∧
            dt.constructors.mapM (fun c' => do
              let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
              pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
            concDt = { name := dt.name, constructors := ctors' }) →
        remaining.foldlM step4Lower init = .ok finalacc →
        ∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList →
          ∃ concDt concC ctors', finalacc.getByKey k = some (.constructor concDt concC) ∧
            concC.nameHead = c.nameHead ∧
            dt.constructors.mapM (fun c' => do
              let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
              pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
            concDt = { name := dt.name, constructors := ctors' } := by
      intro processed remaining
      induction remaining generalizing processed with
      | nil =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
        subst hfold
        have : processed = monoDecls.pairs.toList := by rw [← hsplit]; simp
        rw [this] at hPinit
        exact hPinit k dt c hmemFinal
      | cons x xs ih =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_cons, bind, Except.bind] at hfold
        split at hfold
        · exact absurd hfold (by intro h; cases h)
        rename_i acc' hstep
        obtain ⟨xname, xdecl⟩ := x
        have hsplit' : (processed ++ [(xname, xdecl)]) ++ xs = monoDecls.pairs.toList := by
          simp [← hsplit]
        have hPacc' : ∀ k' dt' c',
            (k', Typed.Declaration.constructor dt' c') ∈ processed ++ [(xname, xdecl)] →
            ∃ concDt concC ctors', acc'.getByKey k' = some (.constructor concDt concC) ∧
              concC.nameHead = c'.nameHead ∧
              dt'.constructors.mapM (fun c'' => do
                let argTypes ← c''.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
                pure ({ nameHead := c''.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
              concDt = { name := dt'.name, constructors := ctors' } := by
          intro k' dt' c' hmem'
          rcases List.mem_append.mp hmem' with hmemL | hmemR
          · obtain ⟨cDt0, cC0, ctors0, hacc_k', hheadEq, hctors0Map, hcDt0Eq⟩ :=
              hPinit k' dt' c' hmemL
            cases xdecl with
            | constructor xd xc =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xctors _hxctors
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xargs _hxargs
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                have h_x_mem : (xname, Typed.Declaration.constructor xd xc) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor xd xc) ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.constructor xd xc) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2
                simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at h2
                obtain ⟨hxdEq, hxcEq⟩ := h2
                subst hxdEq; subst hxcEq
                refine ⟨{ name := xd.name, constructors := xctors },
                        ⟨xc.nameHead, xargs⟩, xctors, ?_, rfl, _hxctors, rfl⟩
                rw [IndexMap.getByKey_insert_self]
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | dataType xd =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xctors _hxctors
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.dataType xd) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.dataType xd) ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.dataType xd) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | function xf =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.function xf) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.function xf) ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.function xf) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
          · rcases List.mem_singleton.mp hmemR with hxeq
            rcases Prod.mk.injEq _ _ _ _ |>.mp hxeq with ⟨hname_eq, hdecl_eq⟩
            subst hname_eq; subst hdecl_eq
            unfold step4Lower at hstep
            simp only [bind, Except.bind, pure, Except.pure] at hstep
            split at hstep
            · exact absurd hstep (by intro h'; cases h')
            rename_i xctors _hxctors
            split at hstep
            · exact absurd hstep (by intro h'; cases h')
            rename_i xargs _hxargs
            simp only [Except.ok.injEq] at hstep
            subst hstep
            refine ⟨{ name := dt'.name, constructors := xctors },
                    ⟨c'.nameHead, xargs⟩, xctors, ?_, rfl, _hxctors, rfl⟩
            rw [IndexMap.getByKey_insert_self]
        exact ih (processed ++ [(xname, xdecl)]) acc' finalacc hsplit' hPacc' hfold k dt c hmemFinal
    exact key_helper [] monoDecls.pairs.toList default cd (by simp)
      (by intro _ _ _ h; cases h) hfold k dt c hmem
  intro k concDt c hget hc
  obtain ⟨dt, ctors, hmonoGet, hctorsMap, hconcDtEq⟩ := hDtBack k concDt hget
  subst hconcDtEq
  simp only at hc
  have hc_in_ctors : c ∈ ctors := hc
  have hExistsOrig : ∀ (orig : List Constructor) (ctors' : List Concrete.Constructor),
      orig.mapM (fun c' => do
        let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
        pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' →
      ∀ (cc : Concrete.Constructor), cc ∈ ctors' →
      ∃ c_orig ∈ orig, cc.nameHead = c_orig.nameHead := by
    intro orig
    induction orig with
    | nil =>
      intro ctors' hmap cc hcc
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      cases hcc
    | cons head rest ih =>
      intro ctors' hmap cc hcc
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hmap
      split at hmap
      · exact absurd hmap (by intro h; cases h)
      rename_i headArgs hheadArgs
      split at hmap
      · exact absurd hmap (by intro h; cases h)
      rename_i restCtors hrestCtors
      simp only [Except.ok.injEq] at hmap
      subst hmap
      split at hheadArgs
      · exact absurd hheadArgs (by intro h; cases h)
      rename_i v _hv
      simp only [Except.ok.injEq] at hheadArgs
      subst hheadArgs
      rcases List.mem_cons.mp hcc with heq | htail
      · refine ⟨head, List.Mem.head _, ?_⟩
        rw [heq]
      · obtain ⟨c_orig, hc_orig_mem, hhead_eq⟩ := ih restCtors hrestCtors cc htail
        exact ⟨c_orig, List.Mem.tail _ hc_orig_mem, hhead_eq⟩
  obtain ⟨c_orig, hc_orig_mem, hhead_eq⟩ :=
    hExistsOrig dt.constructors ctors hctorsMap c hc_in_ctors
  obtain ⟨cc_orig, hccOrigGet⟩ := hP k dt c_orig hmonoGet hc_orig_mem
  obtain ⟨concDt', concC', ctors_fwd, hcdGet, _hconcHead, hctorsFwdMap, hconcDtEq⟩ :=
    hCtorForward _ _ _ hccOrigGet
  -- `dt.constructors.mapM ... = .ok ctors` (hctorsMap) AND
  -- `dt.constructors.mapM ... = .ok ctors_fwd` (hctorsFwdMap), so `ctors = ctors_fwd`.
  have hctorsEq : ctors = ctors_fwd := by
    rw [hctorsMap] at hctorsFwdMap
    exact Except.ok.inj hctorsFwdMap
  refine ⟨concC', ?_⟩
  have hpushEq : ({ name := dt.name, constructors := ctors } : Concrete.DataType).name.pushNamespace c.nameHead
                  = dt.name.pushNamespace c_orig.nameHead := by
    show dt.name.pushNamespace c.nameHead = dt.name.pushNamespace c_orig.nameHead
    rw [hhead_eq]
  rw [hpushEq, hctorsEq, ← hconcDtEq]
  exact hcdGet

-- From: ConcreteEvalInversion.lean:L510
/-- `.toOption.map Prod.fst = some v` implies the original is `.ok (v, _)`. -/
theorem interp_toOption_elim
    {r : Except ConcreteError (Value × EvalState)} {v : Value}
    (h : r.toOption.map Prod.fst = some v) :
    ∃ st, r = .ok (v, st) := by
  cases r with
  | error e => simp [Except.toOption] at h
  | ok p =>
    obtain ⟨v', st'⟩ := p
    simp [Except.toOption, Option.map] at h
    exact ⟨st', by rw [h]⟩

-- From: ConcreteEvalInversion.lean:L522
/-- Wrapping `.ok` through `.toOption.map Prod.fst`. -/
theorem interp_toOption_intro
    {v : Value} {st : EvalState} :
    (Except.ok (v, st) : Except ConcreteError (Value × EvalState)).toOption.map Prod.fst = some v := by
  simp [Except.toOption, Option.map]

-- From: ConcreteEvalInversion.lean:L278
/-- `.tuple` arm output: existence of evalList result. -/
theorem interp_tuple_ok
    (decls : Decls) (fuel : Nat) (env : Bindings)
    (t : Concrete.Typ) (e : Bool) (ts : Array Concrete.Term)
    (st : EvalState) (interp_v : Value) (st' : EvalState)
    (h : interp decls fuel env (.tuple t e ts) st = .ok (interp_v, st')) :
    ∃ vs, evalList decls fuel env ts.toList st = .ok (vs, st') ∧
          interp_v = .tuple vs := by
  rw [interp_tuple] at h
  cases hres : evalList decls fuel env ts.toList st with
  | error e => rw [hres] at h; cases h
  | ok p =>
    obtain ⟨vs, st''⟩ := p
    rw [hres] at h
    simp only at h
    have hpair : (.tuple vs, st'') = (interp_v, st') := Except.ok.inj h
    have hv : interp_v = .tuple vs := (congrArg Prod.fst hpair).symm
    have hst : st'' = st' := congrArg Prod.snd hpair
    subst hst
    exact ⟨vs, rfl, hv⟩

-- From: LowerSoundCore.lean:L220
/-- Width of `flattenValue (.array xs)` when each entry of `xs` is a `.field`.
For `xs.map .field`, width equals `xs.size`. Used by `.ioRead`. -/
private theorem flattenValue_array_map_field_size
    (sourceDecls : Source.Decls) (funcIdx : Global → Option Nat)
    (xs : Array G) :
    (flattenValue sourceDecls funcIdx (.array (xs.map Value.field))).size = xs.size := by
  unfold flattenValue
  rw [Array.size_flatMap]
  -- Strategy: rewrite using `Array.attach_map` to swap out attach over map,
  -- then `Array.map_map`, then point-wise simplify the inner function to 1.
  have hattach_map :
      (Array.map Value.field xs).attach.map
        (fun (v : { a : Value // a ∈ Array.map Value.field xs}) =>
          (flattenValue sourceDecls funcIdx v.val).size) =
      xs.attach.map (fun (_ : { a : G // a ∈ xs}) => 1) := by
    apply Array.ext (h₁ := by simp [Array.size_map, Array.size_attach])
    intro i hi₁ hi₂
    simp only [Array.getElem_map]
    have hi_xs : i < xs.size := by
      rw [Array.size_map, Array.size_attach] at hi₂
      exact hi₂
    -- LHS: flatten of field `xs[i]` = `#[xs[i]]`, size 1.
    have hattach_get : ((Array.map Value.field xs).attach[i]'(by
          rw [Array.size_attach, Array.size_map]; exact hi_xs)).val
        = Value.field (xs[i]'hi_xs) := by
      simp [Array.getElem_attach, Array.getElem_map]
    rw [hattach_get]
    show (flattenValue sourceDecls funcIdx (Value.field (xs[i]'hi_xs))).size = 1
    unfold flattenValue
    rfl
  rw [hattach_map]
  -- Goal: (xs.attach.map (fun _ => 1)).sum = xs.size.
  show (Array.map (fun (_ : { a : G // a ∈ xs}) => 1) xs.attach).sum = xs.size
  rw [← Array.sum_toList]
  rw [Array.toList_map, Array.toList_attach]
  -- Goal: (List.map (fun _ => 1) (xs.toList.attachWith (· ∈ xs) _)).sum = xs.size.
  show (List.map (fun (_ : { a : G // a ∈ xs}) => 1)
      (List.pmap Subtype.mk xs.toList (fun a ha => Array.mem_toList_iff.mp ha))).sum = xs.size
  rw [List.map_pmap]
  -- Goal: (List.pmap (fun a _ => 1) xs.toList _).sum = xs.size.
  have hsum : ∀ (l : List G) (h : ∀ a ∈ l, a ∈ xs),
      (List.pmap (fun (_ : G) (_ : _ ∈ xs) => 1) l h).sum = l.length := by
    intro l h
    induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.pmap, List.sum_cons]
      rw [ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
      simp [List.length]; omega
  rw [hsum]
  simp

-- From: LowerSoundCore.lean:L184
/-- `flattenValue` size-distributivity for `Array.attach.flatMap` over a
list-built array. Used to compute the `.tuple`/`.array` fold size. -/
private theorem flattenValue_attach_flatMap_size_toArray
    (sourceDecls : Source.Decls) (funcIdx : Global → Option Nat)
    (l : List Value) :
    (l.toArray.attach.flatMap
      (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w)).size =
    (l.map (fun v => (flattenValue sourceDecls funcIdx v).size)).sum := by
  -- Direct induction on l. Each cons step uses
  -- `flattenValue_attach_flatMap_size_cons` (which is closed F=0).
  -- Strategy: prove the size equation by reducing both sides to Array form
  -- via plain (non-attach) flatMap. The non-attach equivalent is provable
  -- without motive issues.
  have helper : ∀ (a : Array Value),
      a.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w) =
      a.flatMap (fun w => flattenValue sourceDecls funcIdx w) := by
    intro a
    apply Array.ext'
    simp [Array.toList_flatMap, Array.toList_attach,
          List.attachWith, List.flatMap, List.pmap]
  rw [helper]
  -- Convert to .toList.length form.
  rw [show ∀ (a : Array G), a.size = a.toList.length from fun a => by simp]
  rw [Array.toList_flatMap]
  rw [show l.toArray.toList = l from by simp]
  -- Goal: (List.flatMap _ l).length = sum of map (.size) l.
  induction l with
  | nil => simp
  | cons h t ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    rw [show (flattenValue sourceDecls funcIdx h).toList.length
        = (flattenValue sourceDecls funcIdx h).size from by simp]
    simp [List.map_cons, List.sum_cons]

-- From: LowerSoundCore.lean:L82
/-- SSA-uniqueness inheritance: if every `.letVar` binder in `term` is fresh
w.r.t. `env`, the outer `term` contains a `.letVar _ _ l _ _` sub-term, and
the global `LetVarBinderNeq` invariant rules out `l'' = l` for other
`.letVar`-bound `l''`, then extending `env` with `(l, _)` still satisfies
SSA-freshness for `.letVar` sub-terms of the body. -/
private theorem letVar_SSA_extension_inherits
    (layoutMap : LayoutMap)
    (t : Concrete.Typ) (e : Bool) (l : Local) (v b : Concrete.Term)
    (val : Value) (env : Concrete.Eval.Bindings)
    (_hSsaFresh : ∀ {t' : Concrete.Typ} {e' : Bool} {l' : Local} {v' b' : Concrete.Term},
      IsCore layoutMap (.letVar t' e' l' v' b') →
      ∀ w, (l', w) ∉ env)
    (_houter : IsCore layoutMap (.letVar t e l v b))
    (hBinderNeq : LetVarBinderNeq layoutMap l) :
    ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local} {v'' b'' : Concrete.Term},
    IsCore layoutMap (.letVar t'' e'' l'' v'' b'') →
    ∀ w, (l'', w) ∉ ((l, val) :: env) := by
  intro t'' e'' l'' v'' b'' hinner w hmem
  rw [List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · have heq : l'' = l := by cases hhead; rfl
    exact absurd heq (hBinderNeq hinner)
  · exact absurd htail (_hSsaFresh hinner w)

-- From: LowerSoundCore.lean:L124
/-- Membership transport: every `τ` in `typs.extract 0 i` is in `typs`. -/
private theorem mem_typs_of_mem_extract_prefix
    {typs : Array Concrete.Typ} {i : Nat} {typ : Concrete.Typ}
    (hmem : typ ∈ (typs.extract 0 i).toList) : typ ∈ typs.toList := by
  have hmem_arr : typ ∈ typs.extract 0 i := Array.mem_toList_iff.mp hmem
  rw [Array.mem_iff_getElem] at hmem_arr
  obtain ⟨j, hj, hget⟩ := hmem_arr
  have hsz : (typs.extract 0 i).size = min i typs.size := by
    simp [Array.size_extract]
  have hjsz : j < min i typs.size := hsz ▸ hj
  have hjs : j < typs.size := Nat.lt_of_lt_of_le hjsz (Nat.min_le_right _ _)
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  refine ⟨j, hjs, ?_⟩
  simp only [Array.getElem_extract, Nat.zero_add] at hget
  exact hget

-- From: LowerCalleesFromLayout.lean:L3574
/-- Every index inserted by `toBytecode` into `preNameMap` is strictly less
than the final `functions.size`. -/
theorem preNameMap_in_range
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∀ (name : Global) (i : Bytecode.FunIdx),
      preNameMap[name]? = some i → i < bytecodeRaw.functions.size :=
  (toBytecode_fold_invariant h).1

-- From: LowerCalleesFromLayout.lean:L3418
private theorem IndexMap.getByKey_of_indices_eq
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) (j : Nat) (hj : j < m.pairs.size)
    (hidx : m.indices[m.pairs[j].1]? = some j) :
    m.getByKey m.pairs[j].1 = some m.pairs[j].2 := by
  unfold IndexMap.getByKey
  simp only [hidx, bind, Option.bind]
  have hget : m.pairs[j]? = some m.pairs[j] := Array.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
  rw [hget]
  rfl

-- From: LowerCalleesFromLayout.lean:L98
/-- Strengthened form: a callee in `Block.collectAllCallees b` came from either
a `.call` op in `b.ops` or from `b.ctrl`. -/
private theorem mem_block_collectAllCallees
    (b : Bytecode.Block) (x : Bytecode.FunIdx) :
    x ∈ Bytecode.Block.collectAllCallees b →
    (∃ op ∈ b.ops, ∃ args outSz uc, op = Bytecode.Op.call x args outSz uc) ∨
    x ∈ Bytecode.Ctrl.collectAllCallees b.ctrl := by
  intro h
  unfold Bytecode.Block.collectAllCallees at h
  simp only at h
  rw [Array.mem_append] at h
  cases h with
  | inl hop => left; exact mem_foldl_opCollector_empty b.ops x hop
  | inr hctrl => right; exact hctrl

-- From: LowerCalleesFromLayout.lean:L1717
/-- `.assertEq _ _ a b ret`. -/
private theorem term_compile_delta_assertEq
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (a b ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.assertEq ty es a b ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i aRes s1 hta
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings a s s1 aRes hta hops
  split at hrun
  rotate_left
  · cases hrun
  rename_i bRes s2 htb
  have h2 : AllCallsFromLayout layoutMap s2.ops :=
    toIndex_delta layoutMap bindings b s1 s2 bRes htb h1
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h2)

-- From: LowerCalleesFromLayout.lean:L1671
/-- `.debug _ _ label term ret`. -/
private theorem term_compile_delta_debug
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (label : String) (t_opt : Option Concrete.Term) (ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.debug ty es label t_opt ret)
        returnTyp layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  cases t_opt with
  | none =>
    simp only [Option.mapM, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    exact termCompileDelta ret _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
  | some sub =>
    simp only [Option.mapM_some, Functor.map, EStateM.map,
      bind, EStateM.bind, EStateM.run] at hrun
    cases hti_eq : toIndex layoutMap bindings sub s with
    | error eErr sErr =>
      rw [hti_eq] at hrun
      simp only at hrun
      cases hrun
    | ok subRes sMid =>
      rw [hti_eq] at hrun
      simp only at hrun
      have hti_run : (toIndex layoutMap bindings sub).run s =
          .ok subRes sMid := hti_eq
      have h1 : AllCallsFromLayout layoutMap sMid.ops :=
        toIndex_delta layoutMap bindings sub s sMid subRes hti_run hops
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet] at hrun
      exact termCompileDelta ret _ _ _ _ hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) h1)

-- From: LowerCalleesFromLayout.lean:L1755
/-- `.ioSetInfo _ _ key idx len ret`. -/
private theorem term_compile_delta_ioSetInfo
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (key idx len ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.ioSetInfo ty es key idx len ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i keyRes s1 hk
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings key s s1 keyRes hk hops
  split at hrun
  rotate_left
  · cases hrun
  rename_i idxRes s2 hi
  have h2 : AllCallsFromLayout layoutMap s2.ops :=
    toIndex_delta layoutMap bindings idx s1 s2 idxRes hi h1
  split at hrun
  rotate_left
  · cases hrun
  rename_i lenRes s3 hl
  have h3 : AllCallsFromLayout layoutMap s3.ops :=
    toIndex_delta layoutMap bindings len s2 s3 lenRes hl h2
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h3)

-- From: LowerCalleesFromLayout.lean:L1799
/-- `.ioWrite _ _ data ret`. -/
private theorem term_compile_delta_ioWrite
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (data ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.ioWrite ty es data ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i dataRes s1 hd
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings data s s1 dataRes hd hops
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h1)

-- From: LowerCalleesFromLayout.lean:L1637
/-- `.letLoad _ _ dst dstTyp src bod`. -/
private theorem term_compile_delta_letLoad
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (dst : Local) (dstTyp : Concrete.Typ) (src : Local) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.letLoad ty es dst dstTyp src bod)
        returnTyp layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  cases hts : typSize layoutMap dstTyp with
  | error e =>
    rw [hts] at hrun
    simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
      MonadExceptOf.throw] at hrun
    cases hrun
  | ok size =>
    rw [hts] at hrun
    simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
    rw [pushOp_run] at hrun
    simp only at hrun
    exact termCompileDelta bod _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) hops)

-- From: LowerCalleesFromLayout.lean:L1467
/-- Non-tail `.letVar _ _ _ (.match ... valEscapes=true) bod` — reduces to
`(Concrete.Term.match ...).compile`. -/
private theorem term_compile_delta_letVar_match_escape
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (var : Local) (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letVar typ escapes var
          (.match matchTyp true scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [if_true] at hrun
  exact termCompileDelta
    (.match matchTyp true scrut cases defaultOpt) bindings s s' body hrun hops

-- From: LowerCalleesFromLayout.lean:L1526
/-- `.letVar _ _ _ val bod` where `val` is not a `.match`. -/
private theorem term_compile_delta_letVar_non_match
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (var : Local) (val bod : Concrete.Term)
    (hnm : ∀ mt me scr cs deOpt, val ≠ .match mt me scr cs deOpt)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.letVar typ escapes var val bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  have goal : ∀ (idxs : Array Bytecode.ValIdx) (sMid : CompilerState),
      (toIndex layoutMap bindings val).run s = .ok idxs sMid →
      (Concrete.Term.compile bod returnTyp layoutMap
          (bindings.insert var idxs) yieldCtrl).run sMid = .ok body s' →
      BlockCalleesFromLayout layoutMap body := by
    intro idxs sMid htoi hbod
    have hmid : AllCallsFromLayout layoutMap sMid.ops :=
      toIndex_delta layoutMap bindings val s sMid idxs htoi hops
    exact termCompileDelta bod (bindings.insert var idxs) sMid s' body hbod hmid
  match val, hnm with
  | .match mt me scr cs deOpt, h => exact absurd rfl (h mt me scr cs deOpt)
  | .unit .., _ | .var .., _ | .ref .., _ | .field .., _ | .tuple .., _
  | .array .., _ | .ret .., _ | .letVar .., _ | .letWild .., _
  | .letLoad .., _ | .app .., _ | .add .., _ | .sub .., _ | .mul .., _
  | .eqZero .., _ | .proj .., _ | .get .., _ | .slice .., _ | .set .., _
  | .store .., _ | .load .., _ | .ptrVal .., _ | .assertEq .., _
  | .ioGetInfo .., _ | .ioSetInfo .., _ | .ioRead .., _ | .ioWrite .., _
  | .u8BitDecomposition .., _ | .u8ShiftLeft .., _ | .u8ShiftRight .., _
  | .u8Xor .., _ | .u8Add .., _ | .u8Sub .., _ | .u8And .., _ | .u8Or .., _
  | .u8LessThan .., _ | .u32LessThan .., _ | .debug .., _ =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idx sMid htoi
    exact goal idx sMid htoi hrun

-- From: LowerCalleesFromLayout.lean:L1497
/-- Non-tail `.letWild _ _ (.match ... valEscapes=true) bod`. -/
private theorem term_compile_delta_letWild_match_escape
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letWild typ escapes
          (.match matchTyp true scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [if_true] at hrun
  exact termCompileDelta
    (.match matchTyp true scrut cases defaultOpt) bindings s s' body hrun hops

-- From: LowerShared.lean:L443
/-- Witness producer: every successful `Concrete.Eval.interp` on a term
yields a value that has runtime type `term.typ` (in the strengthened
`ValueHasTyp` predicate post SD-A). This is the bridge consumed by every
access arm of `toIndex_preservation_core_extended`:
- `.proj`: needs `ValueHasTyp (.tuple typs) (.tuple vs)` to feed
  `flattenValue_slice_at_offset`.
- `.get` / `.slice` / `.set`: need `ValueHasTyp (.array τ k) (.array vs)`
  to feed `flattenValue_size_of_ValueHasTyp` per-element + uniform-typing
  preserved under slice / set.
- `.letLoad` / `.load`: need `ValueHasTyp (.pointer τ) (.pointer w n)`
  on the pointer source AND a roundtrip-typing for `unflattenValue`'s
  output — both reducible to this lemma.

The hypothesis side is intentionally weak: only `RefClosed cd` (every
`.ref g` resolves to a registered datatype/function in `concDecls`) and
the input env's typing invariant. The conclusion is the typed-Value
witness on the output.

BLOCKED (F=1): full closure requires:
- 36-arm structural induction over `Concrete.Term`, mirroring the
  `Concrete.Eval.interp` definition.
- Mutual induction with `evalList` for `.tuple` / `.array` arms (each
  `vs[i]` corresponds to `interp ts[i]` with `ValueHasTyp t.typ vs[i]`).
- Cross-recursion with `Concrete.Eval.runFunction` for `.app` arm at
  `fuel - 1` — closure depends on the `runFunction`-side typing
  invariant from S1 (`runFunction_preserves_FnFree` chain).
- For `.letLoad` / `.load`: `unflattenValue_preserves_ValueHasTyp` aux
  lemma (memory layout vs typed-value roundtrip).
- For `.ref g`: depends on `RefClosed cd` chasing through to the
  matching datatype + constructor — produces a `ref` arm witness.

Estimated ~500-1000 LoC for the full induction. Currently a single
sorry; to be decomposed per-arm in subsequent rounds. Currently
consumed in the `.get` arm of `toIndex_preservation_core_extended`
(LowerSoundCore.lean) to extract a runtime-typing witness on the
inner runtime array; future arms (`.proj`, `.slice`, `.set`,
`.letLoad`, `.load`) will follow the same consumption pattern. -/
theorem interp_preserves_ValueHasTyp
    {concDecls : Concrete.Decls} {fuel : Nat}
    {env : Concrete.Eval.Bindings} {term : Concrete.Term}
    {evalSt evalSt' : Concrete.Eval.EvalState} {v : Value}
    (_hRefClosed : Concrete.Decls.RefClosed concDecls)
    (_hEnv : ∀ l v', (l, v') ∈ env →
      ∃ τ, ValueHasTyp concDecls τ v')
    (_hrun : Concrete.Eval.interp concDecls fuel env term evalSt
      = .ok (v, evalSt')) :
    ValueHasTyp concDecls term.typ v := by
  -- BLOCKED: see top-level docstring. Full closure: 36-arm structural
  -- induction over `term`, mutual with `evalList`, cross-recursive with
  -- `runFunction` at `fuel - 1`. For now consumed as a black box in the
  -- `.get` arm of `toIndex_preservation_core_extended`
  -- (LowerSoundCore.lean), where it extracts the typed-value witness
  -- on the runtime array value to bridge to
  -- `flattenValue_size_of_ValueHasTyp` (S18).
  sorry

-- From: LowerShared.lean:L1636
/-- Aux: existence/shape companion of `layoutMap_preserves_function_bound`.
Forward fold-invariant on `layoutMapStep`: every `.function` pair in the
input list produces a `.function`-shaped layout entry (keyed under `f.name`).

Hypotheses:
- `hNameAgrees`: function keys = function names.
- `hDtNameIsKey`: dataType keys = dt names.
- `hCtorIsKey`: constructor keys = pushed names (`dt.name.pushNamespace c.nameHead`).
- `hCtorPresent`: every (dt, c) pair in `.dataType dt`'s constructors has a
  matching `.constructor` pair in `cd.pairs`.

Together these rule out ctor-pushed-name collision with `f.name`: IndexMap
key-uniqueness on `.function f` vs `.constructor cdt cc` → contradiction. -/
theorem layoutMap_preserves_function_exists_aux
    (cd : Concrete.Decls)
    (name : Global) (f : Concrete.Function)
    (hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ cd.pairs.toList → key = g.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (_hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Concrete.Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (hmem : (name, Concrete.Declaration.function f) ∈ cd.pairs.toList)
    (_hlm : ∃ lm, cd.layoutMap = .ok lm) :
    ∀ lm, cd.layoutMap = .ok lm →
      ∃ layout, lm[name]? = some (.function layout) := by
  intro lm hlm
  rw [layoutMap_eq_aux cd] at hlm
  simp only [bind, Except.bind] at hlm
  split at hlm
  · exact absurd hlm (by intro heq; cases heq)
  rename_i r hfold
  simp only [pure, Except.pure] at hlm
  have hLayout : r.1 = lm := Except.ok.inj hlm
  have hsub : ∀ x ∈ cd.pairs.toList, x ∈ cd.pairs.toList := fun _ h => h
  obtain ⟨layout, hget⟩ :=
    layoutMap_fold_forward_exists cd name f hNameAgrees hDtNameIsKey hCtorPresent hmem
      cd.pairs.toList (({}, 0) : LMAcc) r hsub hmem hfold
  exact ⟨layout, by rw [← hLayout]; exact hget⟩

/-! ### T3 infrastructure: `blockLayout` preserves `functionLayout.inputSize`. -/

-- From: LowerShared.lean:L1335
/-- `toBytecode` inserts `concF.name ↦ preIdx` into `preNameMap`.
Requires `hNameAgrees` since `toBytecode` inserts under `function.name`, not
the iteration key. -/
theorem toBytecode_extract_preIdx
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name)
    {concName : Global} {concF : Concrete.Function}
    (hget : concDecls.getByKey concName = some (.function concF)) :
    ∃ preIdx : Bytecode.FunIdx,
      preNameMap[concName]? = some preIdx ∧
      preIdx < bytecodeRaw.functions.size := by
  obtain ⟨key, hkeq, hmem⟩ := IndexMap.mem_pairs_of_getByKey concDecls hget
  have hkey : key = concF.name := hNameAgrees key concF hmem
  obtain ⟨lm, hlm⟩ := toBytecode_layoutMap_ok hbc
  have hbc' := hbc
  rw [toBytecode_eq_aux concDecls lm hlm] at hbc'
  simp only [bind, Except.bind] at hbc'
  split at hbc' <;> rename_i r hfold
  · exact absurd hbc' (by intro heq; cases heq)
  simp only [pure, Except.pure] at hbc'
  have hEq := Prod.mk.inj (Except.ok.inj hbc')
  have hBC : (⟨r.1, r.2.1.toArray⟩ : Bytecode.Toplevel) = bytecodeRaw := hEq.1
  have hNM : r.2.2 = preNameMap := hEq.2
  obtain ⟨i, hi_some, hi_lt⟩ :=
    toBytecode_fold_forward_exists lm concDecls.pairs.toList _ r hfold
      key concF hmem
  refine ⟨i, ?_, ?_⟩
  · rw [← hNM]
    rw [hkey] at hkeq
    have hconcName_eq : (concF.name == concName) = true := hkeq
    rw [Std.HashMap.getElem?_congr hconcName_eq] at hi_some
    exact hi_some
  · have hfunSize : bytecodeRaw.functions = r.1 := by
      cases hBC; rfl
    rw [hfunSize]; exact hi_lt

-- From: LowerShared.lean:L1194
/-- If `m.getByKey k = some v`, there is a pair `(k', v) ∈ m.pairs.toList`
with `k' == k`. -/
private theorem IndexMap.mem_pairs_of_getByKey
    {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : _root_.IndexMap α β) {k : α} {v : β}
    (h : m.getByKey k = some v) :
    ∃ k', (k' == k) = true ∧ (k', v) ∈ m.pairs.toList := by
  unfold _root_.IndexMap.getByKey at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  rename_i i hi
  have hv := m.validIndices k hi
  have hlt : i < m.pairs.size := hv.1
  have hfst_beq : (m.pairs[i]'hlt).1 == k := hv.2
  have hp : m.pairs[i]? = some (m.pairs[i]'hlt) := by
    rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
  simp only [hp, Option.map_some] at h
  have hv_eq : (m.pairs[i]'hlt).2 = v := Option.some.inj h
  refine ⟨(m.pairs[i]'hlt).1, hfst_beq, ?_⟩
  rw [Array.mem_toList_iff]
  have heq : ((m.pairs[i]'hlt).1, v) = m.pairs[i]'hlt := by
    cases hpair : m.pairs[i]'hlt with
    | mk a b =>
      simp only at hv_eq
      rw [hpair] at hv_eq
      simp only at hv_eq
      subst hv_eq
      rfl
  rw [heq]
  exact Array.getElem_mem _

-- From: LowerShared.lean:L1424
/-- Forward fold-invariant: every `.function` pair yields a `.function` entry
in the resulting layout map. -/
private theorem layoutMap_fold_forward_exists
    (cd : Concrete.Decls) (name : Global) (f : Concrete.Function)
    (hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ cd.pairs.toList → key = g.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (hmem : (name, Concrete.Declaration.function f) ∈ cd.pairs.toList) :
    ∀ (xs : List (Global × Concrete.Declaration))
      (init result : LMAcc),
      (∀ x ∈ xs, x ∈ cd.pairs.toList) →
      (name, Concrete.Declaration.function f) ∈ xs →
      xs.foldlM (layoutMapStep cd) init = .ok result →
      ∃ layout, result.1[name]? = some (Layout.function layout) := by
  intro xs
  induction xs with
  | nil =>
    intro init result _ hmem_xs _
    cases hmem_xs
  | cons hd tl ih =>
    intro init result hsub hmem_xs hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro heq; cases heq)
    rename_i acc' hstep
    have hhd_mem : hd ∈ cd.pairs.toList := hsub hd (List.Mem.head _)
    have hsub_tl : ∀ x ∈ tl, x ∈ cd.pairs.toList :=
      fun x hx => hsub x (List.Mem.tail _ hx)
    cases hmem_xs with
    | head _ =>
      unfold layoutMapStep at hstep
      simp only at hstep
      simp only [bind, Except.bind] at hstep
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i inputSize hinp
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i outputSize hout
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i offsets hoff
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_fst : acc'.1 =
        init.1.insert f.name
          (Layout.function { index := init.2, inputSize, outputSize, offsets }) := by
        rw [← hacc']
      have hget0 : acc'.1[f.name]? =
          some (Layout.function { index := init.2, inputSize, outputSize, offsets }) := by
        rw [hacc_fst, Std.HashMap.getElem?_insert]
        simp [BEq.rfl]
      have hname : name = f.name := hNameAgrees name f hmem
      have hacc_name : ∃ layout, acc'.1[name]? = some (Layout.function layout) := by
        refine ⟨{ index := init.2, inputSize, outputSize, offsets }, ?_⟩
        rw [hname]; exact hget0
      exact forward_preserve_from_acc tl acc' result hsub_tl hfold hacc_name
    | tail _ htl =>
      exact ih acc' result hsub_tl htl hfold
where
  forward_preserve_from_acc :
      ∀ (xs : List (Global × Concrete.Declaration))
        (acc result : LMAcc),
        (∀ x ∈ xs, x ∈ cd.pairs.toList) →
        xs.foldlM (layoutMapStep cd) acc = .ok result →
        (∃ layout, acc.1[name]? = some (Layout.function layout)) →
        ∃ layout', result.1[name]? = some (Layout.function layout')
  | [], acc, result, _, hfold, hwit => by
      simp only [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold; exact hwit
  | x :: rest, acc, result, hsub, hfold, hwit => by
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      · exact absurd hfold (by intro heq; cases heq)
      rename_i acc'' hstep
      have hx_mem : x ∈ cd.pairs.toList := hsub x (List.Mem.head _)
      have hsub_rest : ∀ y ∈ rest, y ∈ cd.pairs.toList :=
        fun y hy => hsub y (List.Mem.tail _ hy)
      obtain ⟨layout, hlay⟩ := hwit
      obtain ⟨layout', hnew⟩ :=
        layoutMap_step_preserves_function cd name f hmem
          hDtNameIsKey hCtorPresent x hx_mem acc acc'' hstep layout hlay
      exact forward_preserve_from_acc rest acc'' result hsub_rest hfold ⟨layout', hnew⟩

-- From: LowerShared.lean:L1327
/-- Single-step preservation: `layoutMapStep` preserves a `.function` entry at
`nm` across all decl arms, given the full 4-hypothesis bundle. -/
private theorem layoutMap_step_preserves_function
    (cd : Concrete.Decls) (nm : Global) (f : Concrete.Function)
    (hmem : (nm, Concrete.Declaration.function f) ∈ cd.pairs.toList)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (x : Global × Concrete.Declaration) (hx : x ∈ cd.pairs.toList)
    (acc acc' : LMAcc) (hstep : layoutMapStep cd acc x = .ok acc')
    (layout : FunctionLayout)
    (hget : acc.1[nm]? = some (Layout.function layout)) :
    ∃ layout', acc'.1[nm]? = some (Layout.function layout') := by
  obtain ⟨xname, decl⟩ := x
  unfold layoutMapStep at hstep
  simp only at hstep
  cases decl with
  | function function =>
    simp only [bind, Except.bind] at hstep
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i inputSize hinp
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i outputSize hout
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i offsets hoff
    simp only [pure, Except.pure] at hstep
    have hacc' := Except.ok.inj hstep
    have hacc_fst : acc'.1 =
      acc.1.insert function.name
        (Layout.function { index := acc.2, inputSize, outputSize, offsets }) := by
      rw [← hacc']
    by_cases hnm : (function.name == nm) = true
    · refine ⟨{ index := acc.2, inputSize, outputSize, offsets }, ?_⟩
      rw [hacc_fst, Std.HashMap.getElem?_insert]
      simp [hnm]
    · have hnm' : (function.name == nm) = false := Bool.not_eq_true _ |>.mp hnm
      refine ⟨layout, ?_⟩
      rw [hacc_fst, Std.HashMap.getElem?_insert]
      simp [hnm']; exact hget
  | dataType dt =>
    simp only [bind, Except.bind] at hstep
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i dataTypeSize hsize
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i lmPair hpass
    simp only [pure, Except.pure] at hstep
    have hacc' := Except.ok.inj hstep
    have hacc_fst : acc'.1 = lmPair.1 := by rw [← hacc']
    have hx_dt_name : xname = dt.name := hDtNameIsKey xname dt hx
    have hne_outer : (dt.name == nm) = false := by
      cases heq : (dt.name == nm) with
      | false => rfl
      | true =>
        have hbeq : (nm == dt.name) = true := BEq.symm heq
        have hx' : (dt.name, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList := by
          rw [← hx_dt_name]; exact hx
        have habs := indexMap_key_unique cd hmem hx' hbeq
        cases habs
    have hne_ctors : ∀ c ∈ dt.constructors,
        (dt.name.pushNamespace c.nameHead == nm) = false := by
      intro c hc
      cases heq : (dt.name.pushNamespace c.nameHead == nm) with
      | false => rfl
      | true =>
        obtain ⟨cc, hcmem⟩ := hCtorPresent xname dt c hx hc
        have habs := indexMap_key_unique cd hcmem hmem heq
        cases habs
    have houter_get :
        (acc.1.insert dt.name (Layout.dataType dataTypeSize))[nm]? =
          some (Layout.function layout) := by
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i hbeq; rw [hne_outer] at hbeq; cases hbeq
      · exact hget
    have hf_preserve := ctor_fold_preserves_function cd dt dataTypeSize nm layout
      dt.constructors
      (acc.1.insert dt.name (Layout.dataType dataTypeSize), 0)
      lmPair
      hne_ctors hpass houter_get
    refine ⟨layout, ?_⟩
    rw [hacc_fst]; exact hf_preserve
  | «constructor» dt c =>
    simp only [pure, Except.pure] at hstep
    have hacc' := Except.ok.inj hstep
    refine ⟨layout, ?_⟩
    rw [← hacc']; exact hget

-- From: LowerShared.lean:L1188
/-- Forward existence invariant for `toBytecode`'s fold. -/
private theorem toBytecode_fold_forward_exists
    (lm : LayoutMap) (xs : List (Global × Concrete.Declaration))
    (init result : BCAcc)
    (hfold : xs.foldlM (bytecodeStep lm) init = .ok result)
    (key : Global) (fn : Concrete.Function)
    (hmem : (key, Concrete.Declaration.function fn) ∈ xs) :
    ∃ i : Bytecode.FunIdx,
      (result.2.2 : Std.HashMap Global Bytecode.FunIdx)[fn.name]? = some i ∧
      i < result.1.size := by
  induction xs generalizing init with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro heq; cases heq)
    rename_i acc' hstep
    cases hmem with
    | head _ =>
      unfold bytecodeStep at hstep
      simp only at hstep
      simp only [bind, Except.bind] at hstep
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, lms⟩ := res
      simp only [pure, Except.pure] at hstep
      have hprod := Prod.mk.inj (Except.ok.inj hstep)
      have hF : acc'.1 = init.1.push
          ⟨body, lms.functionLayout, fn.entry, false⟩ := hprod.1.symm
      have hN : acc'.2.2 = init.2.2.insert fn.name init.1.size :=
        (Prod.mk.inj hprod.2).2.symm
      have hget0 : (acc'.2.2 : Std.HashMap Global Bytecode.FunIdx)[fn.name]? =
          some init.1.size := by
        rw [hN, Std.HashMap.getElem?_insert]
        simp [BEq.rfl]
      have hlt0 : init.1.size < acc'.1.size := by
        rw [hF, Array.size_push]; exact Nat.lt_succ_self _
      exact forward_from_acc lm tl acc' result hfold fn.name init.1.size hget0 hlt0
    | tail _ htl =>
      exact ih acc' hfold htl
where
  forward_from_acc (lm : LayoutMap) :
    ∀ (xs : List (Global × Concrete.Declaration))
      (acc result : BCAcc),
      xs.foldlM (bytecodeStep lm) acc = .ok result →
      ∀ (nm : Global) (i : Bytecode.FunIdx),
        (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some i →
        i < acc.1.size →
        ∃ i', (result.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some i' ∧
              i' < result.1.size
  | [], acc, result, hfold, nm, i, hget, hlt => by
      simp only [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold; exact ⟨i, hget, hlt⟩
  | x :: rest, acc, result, hfold, nm, i, hget, hlt => by
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      · exact absurd hfold (by intro heq; cases heq)
      rename_i acc'' hstep
      obtain ⟨i', hget', hlt'⟩ :=
        toBytecode_fold_preserves_witness lm x acc acc'' hstep nm i hget hlt
      exact forward_from_acc lm rest acc'' result hfold nm i' hget' hlt'

-- From: LowerShared.lean:L1142
/-- Monotonicity / witness preservation for `bytecodeStep`. -/
private theorem toBytecode_fold_preserves_witness
    (lm : LayoutMap) (x : Global × Concrete.Declaration) (acc acc' : BCAcc)
    (hstep : bytecodeStep lm acc x = .ok acc')
    (nm : Global) (i : Bytecode.FunIdx)
    (hget : (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some i)
    (hlt : i < acc.1.size) :
    ∃ i', (acc'.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some i' ∧
          i' < acc'.1.size := by
  obtain ⟨xname, decl⟩ := x
  unfold bytecodeStep at hstep
  simp only at hstep
  cases decl with
  | function function =>
    simp only [bind, Except.bind] at hstep
    split at hstep
    · exact absurd hstep (by intro heq; cases heq)
    rename_i res hcomp
    obtain ⟨body, lms⟩ := res
    simp only [pure, Except.pure] at hstep
    have hprod := Prod.mk.inj (Except.ok.inj hstep)
    have hF : acc'.1 = acc.1.push
        ⟨body, lms.functionLayout, function.entry, false⟩ := hprod.1.symm
    have hN : acc'.2.2 = acc.2.2.insert function.name acc.1.size :=
      (Prod.mk.inj hprod.2).2.symm
    by_cases hnm : (function.name == nm) = true
    · refine ⟨acc.1.size, ?_, ?_⟩
      · rw [hN, Std.HashMap.getElem?_insert]; simp [hnm]
      · rw [hF, Array.size_push]; exact Nat.lt_succ_self _
    · have hnm' : (function.name == nm) = false := Bool.not_eq_true _ |>.mp hnm
      refine ⟨i, ?_, ?_⟩
      · rw [hN, Std.HashMap.getElem?_insert]; simp [hnm']; exact hget
      · rw [hF, Array.size_push]; exact Nat.lt_succ_of_lt hlt
  | dataType dt =>
    simp only [pure, Except.pure] at hstep
    have hacc := Except.ok.inj hstep
    refine ⟨i, ?_, ?_⟩
    · rw [← hacc]; exact hget
    · rw [← hacc]; exact hlt
  | «constructor» dt c =>
    simp only [pure, Except.pure] at hstep
    have hacc := Except.ok.inj hstep
    refine ⟨i, ?_, ?_⟩
    · rw [← hacc]; exact hget
    · rw [← hacc]; exact hlt

-- MOVED 2026-04-30 to `Ix/Aiur/Proofs/LowerShared.lean` for use in
-- `Lower.compile_progress_entry` (CompilerProgress.lean). No longer orphan.

-- `preNameMap_in_range` + `toBytecode_callees_in_range` moved to
-- `LowerCalleesFromLayout.lean`.

-- From: LowerShared.lean:L128
/-- Bridge: a typed `Value` flattens to width `typSize layoutMap τ`.

This is the central correspondence the access arms of
`toIndex_preservation_core_extended` need. Given a value `v` known to
have type `τ` (`ValueHasTyp τ v`), its source-side flat size equals the
compiler-side `typSize` of `τ`.

BLOCKED: the proof requires showing per-shape that
- `flattenValue _ _ .unit = #[]` (size 0 = `typSize .unit`),
- `flattenValue _ _ (.field _) = #[_]` (size 1 = `typSize .field`),
- pointer / function sizes both = 1,
- tuple flattens are concatenations of element flattens, summing element
  `typSize`s,
- array flattens are uniform-element, multiplying by length,
- `.ref g` -typed values flatten to `typSize layoutMap (.ref g)` via the
  layout-map / data-type-flat-size correspondence.

The `.ref` case in particular requires a `Concrete.Decls`-vs-`LayoutMap`
correspondence (`LayoutKeysMatch`) that is not threaded into the
predicate. Closure of this lemma will live in `LowerShared.lean`
alongside `flattenValue_slice_at_offset`; for now we leave it as a
named bridge consumed by the 6 access arms. -/
private theorem flattenValue_size_of_ValueHasTyp
    (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) (layoutMap : LayoutMap)
    {τ : Concrete.Typ} {v : Value}
    (hτv : ValueHasTyp concDecls τ v)
    (htypSize : ∃ m, typSize layoutMap τ = .ok m) :
    ∃ n, typSize layoutMap τ = .ok n ∧
      (flattenValue sourceDecls funcIdx v).size = n := by
  -- `htypSize` is consumed in the `.array` empty-array case below, where
  -- it is the only source of an element-typSize witness (the per-element
  -- IH is vacuous on an empty array). All other arms ignore it.
  induction hτv with
  | unit =>
    refine ⟨0, ?_, ?_⟩
    · unfold typSize; rfl
    · unfold flattenValue; simp
  | @field g =>
    refine ⟨1, ?_, ?_⟩
    · unfold typSize; rfl
    · unfold flattenValue; simp
  | @pointer τ' w n =>
    refine ⟨1, ?_, ?_⟩
    · unfold typSize; rfl
    · unfold flattenValue; simp
  | @function ins out g =>
    refine ⟨1, ?_, ?_⟩
    · unfold typSize; rfl
    · unfold flattenValue; simp
  | @tuple τs vs hLen hPer ihPer =>
    -- The IH `ihPer i _ _` requires `∃ m, typSize layoutMap τs[i] = .ok m`;
    -- this comes from `htypSize`'s success on `.tuple τs` (which `foldlM`s
    -- over per-element `typSize` calls — each step must succeed).
    obtain ⟨_, hTup⟩ := htypSize
    have hElemEach : ∀ (i : Nat) (h₁ : i < τs.size),
        ∃ m, typSize layoutMap (τs[i]'h₁) = .ok m := by
      -- The `typSize layoutMap (.tuple τs)` foldlM succeeds, so every step
      -- in the fold succeeded. We deduce per-element success by an
      -- auxiliary list-level lemma on `foldlM` success.
      have hList : ∃ N,
          τs.toList.foldlM (m := Except String) (init := 0)
            (fun acc t => do let s ← typSize layoutMap t; pure (acc + s)) = .ok N := by
        unfold typSize at hTup
        rw [← Array.foldlM_toList] at hTup
        exact ⟨_, hTup⟩
      -- Lemma: foldlM-with-Except succeeds ⇒ each step succeeds.
      have aux : ∀ (ts : List Concrete.Typ) (init : Nat),
          (∃ N, ts.foldlM (m := Except String) (init := init)
            (fun acc t => do let s ← typSize layoutMap t; pure (acc + s)) = .ok N) →
          ∀ t ∈ ts, ∃ m, typSize layoutMap t = .ok m := by
        intro ts
        induction ts with
        | nil =>
          intro _ _ _ hmem
          cases hmem
        | cons t trest ih =>
          intro init hOk t' hmem
          obtain ⟨N, hOk⟩ := hOk
          rw [List.foldlM_cons] at hOk
          simp only [bind, Except.bind] at hOk
          -- Head step: `typSize layoutMap t` must be `.ok _`.
          cases hHd : typSize layoutMap t with
          | error e => rw [hHd] at hOk; simp at hOk
          | ok s =>
            rw [hHd] at hOk
            simp only [pure, Except.pure] at hOk
            cases hmem with
            | head => exact ⟨s, hHd⟩
            | tail _ hmem' =>
              exact ih (init + s) ⟨N, hOk⟩ t' hmem'
      intro i h₁
      have hmem : (τs[i]'h₁) ∈ τs.toList := by
        have : (τs[i]'h₁) ∈ τs := Array.getElem_mem h₁
        exact Array.mem_toList_iff.mpr this
      exact aux τs.toList 0 hList _ hmem
    -- Per-element width witness from IH. Pulled at the `Array` level so the
    -- list induction below can transport it to `vs.toList`-membership.
    have h_each : ∀ (i : Nat) (h₁ : i < τs.size) (h₂ : i < vs.size),
        ∃ ni, typSize layoutMap (τs[i]'h₁) = .ok ni ∧
          (flattenValue sourceDecls funcIdx (vs[i]'h₂)).size = ni :=
      fun i h₁ h₂ => ihPer i h₁ h₂ (hElemEach i h₁)
    -- Convert `attach.flatMap` to plain `flatMap` (the function ignores
    -- the membership proof). Mirrors the `.array` arm.
    have helper : ∀ (a : Array Value),
        a.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w) =
        a.flatMap (fun w => flattenValue sourceDecls funcIdx w) := by
      intro a
      apply Array.ext'
      simp [Array.toList_flatMap, List.flatMap]
    -- Reduce both sides to a list-level statement on `(τs.toList, vs.toList)`,
    -- packaged with their lockstep length-agreement and per-pair witness.
    have hListLen : τs.toList.length = vs.toList.length := by
      simpa using hLen
    -- Per-pair witness on the lists, derived from `ihPer` via `Array.getElem`.
    have h_pair : ∀ (i : Nat) (hi : i < τs.toList.length),
        ∃ ni, typSize layoutMap (τs.toList[i]'hi) = .ok ni ∧
          (flattenValue sourceDecls funcIdx
            (vs.toList[i]'(hListLen ▸ hi))).size = ni := by
      intro i hi
      have hiτ : i < τs.size := by simpa using hi
      have hiv : i < vs.size := hLen ▸ hiτ
      obtain ⟨ni, hts, hfs⟩ := h_each i hiτ hiv
      refine ⟨ni, ?_, ?_⟩
      · simpa using hts
      · simpa using hfs
    -- Auxiliary list-level lemma: lockstep induction over `(ts, ws)` with a
    -- per-pair `ihP` discharges both the foldlM-success and the size equation.
    have aux : ∀ (ts : List Concrete.Typ) (ws : List Value)
        (hLW : ts.length = ws.length)
        (ihP : ∀ (i : Nat) (hi : i < ts.length),
          ∃ ni, typSize layoutMap (ts[i]'hi) = .ok ni ∧
            (flattenValue sourceDecls funcIdx (ws[i]'(hLW ▸ hi))).size = ni)
        (init : Nat),
        ∃ N,
          ts.foldlM (m := Except String) (init := init)
            (fun acc t => do
              let s ← typSize layoutMap t
              pure (acc + s)) = .ok N ∧
          (ws.flatMap (fun w => (flattenValue sourceDecls funcIdx w).toList)).length
            + init = N := by
      intro ts
      induction ts with
      | nil =>
        intro ws hLW _ihP init
        have hws : ws = [] := by
          cases ws with
          | nil => rfl
          | cons _ _ => simp at hLW
        subst hws
        refine ⟨init, ?_, ?_⟩
        · simp [List.foldlM_nil, pure, Except.pure]
        · simp
      | cons t trest ih =>
        intro ws hLW ihP init
        cases ws with
        | nil => simp at hLW
        | cons w wrest =>
          -- Head witness from `ihP 0`.
          have hLW' : trest.length = wrest.length := by
            simpa using hLW
          have h0 : 0 < (t :: trest).length := by simp
          obtain ⟨n0, hts0, hfs0⟩ := ihP 0 h0
          -- Tail witness: shift `ihP` by `i+1`.
          have ihP_tail : ∀ (i : Nat) (hi : i < trest.length),
              ∃ ni, typSize layoutMap (trest[i]'hi) = .ok ni ∧
                (flattenValue sourceDecls funcIdx
                  (wrest[i]'(hLW' ▸ hi))).size = ni := by
            intro i hi
            have hi_succ : i + 1 < (t :: trest).length := by
              simp; omega
            obtain ⟨ni, hts, hfs⟩ := ihP (i + 1) hi_succ
            refine ⟨ni, ?_, ?_⟩
            · simpa using hts
            · simpa using hfs
          obtain ⟨N', hfold', hsz'⟩ := ih wrest hLW' ihP_tail (init + n0)
          refine ⟨N', ?_, ?_⟩
          · simp only [List.foldlM_cons, bind, Except.bind]
            -- Head step: `typSize layoutMap t = .ok n0`.
            have hts0' : typSize layoutMap t = .ok n0 := by simpa using hts0
            rw [hts0']
            simp only [pure, Except.pure]
            exact hfold'
          · -- Size step: head adds `(flattenValue w).toList.length = n0`.
            have hhd : (flattenValue sourceDecls funcIdx w).toList.length = n0 := by
              have : (flattenValue sourceDecls funcIdx w).size = n0 := by
                simpa using hfs0
              simpa using this
            rw [List.flatMap_cons, List.length_append, hhd]
            omega
    -- Apply the aux lemma at `init = 0`.
    obtain ⟨N, hfoldOk, hsumEq⟩ := aux τs.toList vs.toList hListLen h_pair 0
    refine ⟨N, ?_, ?_⟩
    · -- `typSize layoutMap (.tuple τs) = τs.foldlM ... 0`. Convert Array
      -- `foldlM` to list `foldlM`.
      unfold typSize
      rw [← Array.foldlM_toList]
      exact hfoldOk
    · unfold flattenValue
      rw [helper]
      rw [show ∀ (a : Array G), a.size = a.toList.length from fun a => by simp]
      rw [Array.toList_flatMap]
      simpa using hsumEq
  | @array τ' n vs hLen hPer ihPer =>
    -- Uniform-element closure. `ihPer 0 _` (when `vs.size > 0`) yields the
    -- per-element witness `m : typSize layoutMap τ' = .ok m`, and `typSize`
    -- determinism makes every other element's width equal `m` as well.
    -- The attach.flatMap size then becomes `vs.size * m = n * m`, matching
    -- `typSize layoutMap (.array τ' n) = .ok (n * m)`.
    -- Extract `τ'`'s `typSize` success from the parent-level `htypSize`
    -- hypothesis. The `IH ihPer` requires this premise to fire.
    obtain ⟨_, hArr⟩ := htypSize
    have hElem : ∃ m', typSize layoutMap τ' = .ok m' := by
      unfold typSize at hArr
      cases hElemRes : typSize layoutMap τ' with
      | ok m' => exact ⟨m', rfl⟩
      | error e => rw [hElemRes] at hArr; simp [bind, Except.bind] at hArr
    by_cases hsz : 0 < vs.size
    · obtain ⟨m, htsz, _h0⟩ := ihPer 0 hsz hElem
      refine ⟨n * m, ?_, ?_⟩
      · unfold typSize
        rw [htsz]
        rfl
      · -- Each element's flatten has width `m` by determinism of `typSize`.
        have h_each : ∀ (i : Nat) (h : i < vs.size),
            (flattenValue sourceDecls funcIdx (vs[i]'h)).size = m := by
          intro i h
          obtain ⟨m', htsz', hsz'⟩ := ihPer i h hElem
          rw [htsz] at htsz'
          cases htsz'
          exact hsz'
        -- Convert `attach.flatMap` to plain `flatMap` (function ignores proof).
        have helper : ∀ (a : Array Value),
            a.attach.flatMap (fun ⟨w, _⟩ => flattenValue sourceDecls funcIdx w) =
            a.flatMap (fun w => flattenValue sourceDecls funcIdx w) := by
          intro a
          apply Array.ext'
          simp [Array.toList_flatMap, List.flatMap]
        unfold flattenValue
        rw [helper]
        -- Goal: (vs.flatMap (fun w => flattenValue ... w)).size = n * m.
        rw [show ∀ (a : Array G), a.size = a.toList.length from fun a => by simp]
        rw [Array.toList_flatMap]
        -- Replace each per-element list-length by `m` via `h_each`.
        rw [← hLen]
        rw [show vs.size = vs.toList.length from by simp]
        -- Universal width property transported to list-membership.
        have h_each_list : ∀ v ∈ vs.toList,
            (flattenValue sourceDecls funcIdx v).size = m := by
          intro v hv
          have hv' : v ∈ vs := Array.mem_toList_iff.mp hv
          rcases Array.mem_iff_getElem.mp hv' with ⟨i, hi, hget⟩
          rw [← hget]; exact h_each i hi
        clear _h0 h_each hLen hPer ihPer hsz htsz
        generalize hl : vs.toList = l at h_each_list
        clear hl vs
        induction l with
        | nil => simp
        | cons hd tl ih =>
          rw [List.flatMap_cons, List.length_append]
          have hhd : (flattenValue sourceDecls funcIdx hd).toList.length = m := by
            have : (flattenValue sourceDecls funcIdx hd).size = m :=
              h_each_list hd (List.mem_cons_self ..)
            simpa using this
          have htl : (tl.flatMap fun w => (flattenValue sourceDecls funcIdx w).toList).length
                     = tl.length * m :=
            ih (fun v hv => h_each_list v (List.mem_cons_of_mem hd hv))
          rw [hhd, htl]
          simp [List.length_cons, Nat.succ_mul, Nat.add_comm]
    · -- Empty-array case: `vs.size = 0`, hence `n = 0` from `hLen`. The
      -- source side flattens to `#[]` (size 0); the target side
      -- `typSize layoutMap (.array τ' 0)` unfolds to
      -- `do let s ← typSize layoutMap τ'; pure (0 * s)`. The element
      -- typSize witness `hElem` was extracted above from the
      -- parent-level `htypSize` hypothesis (option A in the
      -- BLOCKED-ARRAY-EMPTY note).
      have hsz0 : vs.size = 0 := Nat.eq_zero_of_not_pos hsz
      have hn0 : n = 0 := by rw [hsz0] at hLen; exact hLen.symm
      subst hn0
      obtain ⟨m', hm'⟩ := hElem
      refine ⟨0, ?_, ?_⟩
      · -- `typSize layoutMap (.array τ' 0) = do let s ← typSize τ'; pure (0 * s)`.
        -- Substituting `hm'` and reducing: `pure (0 * m') = .ok 0`.
        unfold typSize
        rw [hm']
        show (Except.ok (0 * m') : Except String Nat) = Except.ok 0
        rw [Nat.zero_mul]
      · -- `vs.size = 0` ⇒ `vs = #[]` ⇒ flattenValue is `#[]`.
        have hvs : vs = #[] := by
          apply Array.ext'
          have : vs.toList.length = 0 := by simpa using hsz0
          exact List.eq_nil_of_length_eq_zero this
        subst hvs
        unfold flattenValue
        simp
  | @ref g cdt cc args hdt hcc hargs hPerArg ihPer =>
    -- BLOCKED-REF: needs a `concDecls`-vs-`layoutMap` agreement
    -- (LayoutKeysMatch-shape) that is NOT yet threaded into the lemma.
    -- The `flattenValue` `.ctor` arm (Flatten.lean:193-202) uses
    -- `sourceDecls.getByKey` (NOT `concDecls.getByKey`) and resolves the
    -- ctor name `(g.pushNamespace cc.nameHead)` to a `(.constructor dt
    -- ctor)` entry. We have the dual entry from `hdt : concDecls.getByKey
    -- g = some (.dataType cdt)` + `hcc : cc ∈ cdt.constructors` — but
    -- the source-vs-conc decls bridge is missing. Threading
    -- `LayoutKeysMatch sourceDecls concDecls layoutMap` through this
    -- lemma's signature is the next decomposition step.
    -- Width equation: `flattenValue (.ctor (g.pushNamespace cc.nameHead)
    -- args) = #[ofNat ctorIdx] ++ argsFlat ++ padding` of total
    -- size = `dataTypeFlatSize sourceDecls cdt` (assuming the dual-decls
    -- bridge). Compiler side: `typSize layoutMap (.ref g) = layoutMap[g]?
    -- |>.size`, which from `Concrete.Decls.layoutMap` correctness equals
    -- `dataTypeFlatSize concDecls cdt`. Closure: ~150 LoC after the
    -- LayoutKeysMatch sig extension.
    sorry

-- ============================================================================
-- MOVED 2026-04-30 from `Ix/Aiur/Proofs/ConcretizeSound/RefClosed.lean`
-- (orphan, FullyMonomorphic-dependent — dropped from WellFormed).
-- ============================================================================

/-- `concretize` lifts a typed-function entry to a concrete-function entry at
`concName = name` (monomorphic), preserving input flat-size identity.
**Orphan, FullyMono-dependent**. -/
theorem concretize_extract_function_at_name
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {name : Global} {tf : Typed.Function}
    (_htyped : typedDecls.getByKey name = some (.function tf)) :
    ∃ (concName : Global) (concF : Concrete.Function),
      concName = name ∧
      concDecls.getByKey concName = some (.function concF) ∧
      ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
        (tf.inputs.map Prod.snd).foldl
            (fun acc t => acc + typFlatSize decls {} t) 0 =
          (concF.inputs.map Prod.snd).foldl
            (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  sorry

/-- S3 heart theorem under FullyMono. Replaced by entry-restricted variant
`concretize_preserves_runFunction_entry`. -/
theorem concretize_preserves_runFunction
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hcompat : SourceTypedCompatible decls typedDecls)
    (name : Global)
    (_hnameSrc : decls.getByKey name ≠ none)
    (_hnameConc : concDecls.getByKey name ≠ none)
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (funcIdx : Global → Option Nat)
    (mono : Std.HashMap (Global × Array Typ) Global)
    (_hidx : FuncIdxRespectsConcretize mono funcIdx) :
    match Source.Eval.runFunction decls name args io₀ fuel,
          Concrete.Eval.runFunction concDecls name args io₀ fuel with
    | .ok (v₁, io₁), .ok (v₂, io₂) =>
        flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
          ∧ IOBuffer.equiv io₁ io₂
    | .error _, .error _ => True
    | _, _ => False := by
  sorry

/-- Phase C main: dataType flat-size agreement under FullyMono.
BLOCKED ON: per-Typ flat-size correspondence (`TypFlatSizeAgreeFM` predicate
above) via `Typ.instantiate_empty_id` + typToConcrete preservation. ~150 LoC. -/
theorem concretize_under_fullymono_dt_flat_size_agree
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {g : Global}
    {src_dt : DataType} {src_c : Constructor}
    {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (_hsrc : decls.getByKey g = some (.constructor src_dt src_c))
    (_hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    dataTypeFlatSize decls {} src_dt =
      Concrete.dataTypeFlatSize concDecls {} cd_dt := by
  sorry

end Scratch

-- ============================================================================
-- MOVED 2026-04-30 from `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
-- (orphan cluster: spine_transfer + concretize_preserves_direct_dag chain
-- + sizeBound_ok_* + concretize_layoutMap_progress).
-- ============================================================================

namespace DirectDagBody

/-- **Main theorem**: given tds-side rank witness + `RankTransport`, every
cd-dt ctor argtype has bounded cd-side spine.

**Proof outline**:
1. Backward-trace `cdt.constructors` through `step4Lower` to `dt_mono.constructors`
   in `monoDecls`.
2. Backward-trace `dt_mono` through `concretizeBuild` to `templateDt` (the
   source template): either `dt_mono` came from a monomorphic source
   (`fromSource` fold, args = `#[]`) or from `drained.newDataTypes`
   (`withNewDts` fold, where each entry has ctors =
   `templateDt.constructors.map (.argTypes.map (Typ.instantiate subst))`).
3. Each cd-ctor argtype `t` is `typToConcrete emptyMono (rewriteTyp emptySubst
   mono t_rewritten)` where `t_rewritten` is the instantiated source argtype.
4. Structural induction on `t` dispatches: `.unit`/`.field`/`.pointer`/`.function`
   are immediate; `.tuple`/`.array` recurse; `.ref g'` requires the rank lift
   via `RankTransport`.

**BLOCKED status (F=1)**: two pieces of infrastructure are missing:

(a) **Backward trace from cd-ctor-argtypes to source ctor-argtypes**:
    ~500 LoC across 3 phases (`fromSource`, `withNewDts`, `newFunctions`) of
    `concretizeBuild`, each preserving a pre-image invariant on ctor argTypes.
    Structurally parallel to `L2_phase1_fromSource` /
    `L2_phase2_withNewDts` / `L2_phase3_newFunctions` (which track dt-shape
    at a key) but adapted to track the exact ctor-argtype-to-source-argtype
    correspondence.

(b) **`templateOf_of_source_ref` lemma**: if `.ref g'` survives from a
    source tds ctor-argtype to a cd-ctor-argtype (i.e., g' is not rewritten
    away by instantiate + rewriteTyp + typToConcrete) AND
    `cd.getByKey g' = some (.dataType _)`, then
    `templateOf tds cd hconc hunique g' = g'`. Required for the `.ref g'`
    case to reduce `rank_cd g' < rank_cd g` to the source-side
    `rank_src g' < rank_src templateName`.
    Proof sketch: under `hunique` + `concretizeName_empty_args g' = g'`,
    any template `(templateName', args')` with
    `concretizeName templateName' args' = g'` and `cd.getByKey g' = dt` must
    have `templateName' = g'` and `args' = #[]` — because source `.ref g'`
    points to a source dt-key g' (by type-wellformedness; under FullyMono
    this dt is monomorphic so survives at key g'), and uniqueness rules out
    any other template producing g'.
    Subtle: requires a `FullyMono`-style hypothesis or drain-level invariant
    not currently threaded here.

Downstream caller `concretize_preserves_direct_dag` depends on this; it
feeds into `sizeBound_ok_of_rank` which certifies `Decls.SizeBoundOk cd`. -/
theorem spine_transfer
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {rank_src : Global → Nat}
    (_hrank_src : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.SpineRefsBelow rank_src (rank_src g) t ∧
          Typed.Typ.ParamSafe dt.params t)
    {rank_cd : Global → Nat}
    (_htransport : RankTransport tds cd rank_src rank_cd)
    {g : Global} {cdt : Concrete.DataType}
    (_hget : cd.getByKey g = some (.dataType cdt))
    {templateName : Global} {templateDt : DataType}
    (_htemplate : TemplateOf tds cd g templateName templateDt)
    -- Sig amendment 2026-05-04 (Defect 3): hoist drain-shape invariant.
    -- For every cd-keyed dataType `g'`, the only template-args pair
    -- producing it under `concretizeName` is the trivial one
    -- `(templateName' = g', args' = #[])`. Required by the `.ref g'` arm
    -- of the structural induction (see docstring above) to reduce
    -- `rank_cd g' < rank_cd g` to the source-side
    -- `rank_src g' < rank_src templateName`. Discharged at the consumer
    -- (`concretize_preserves_direct_dag`) by composing
    -- `ConcretizeUniqueNames` with `StrongNewNameShape`.
    (_hDrainShape : ∀ g' templateName' args',
       (∃ cdt' : Concrete.DataType, cd.getByKey g' = some (.dataType cdt')) →
       concretizeName templateName' args' = g' →
       templateName' = g' ∧ args' = #[]) :
    ∀ c ∈ cdt.constructors, ∀ t ∈ c.argTypes,
      Concrete.Typ.SpineRefsBelow rank_cd (rank_cd g) t := by
  -- BLOCKED: See docstring above. Closing requires the backward-trace +
  -- rank-lift infrastructure (~500-700 LoC of `concretizeBuild` per-phase
  -- per-ctor-argtype preservation, paralleling existing `L2_phase1_fromSource`
  -- / `L2_phase2_withNewDts` / `L2_phase3_newFunctions` + a new
  -- `templateOf_of_source_ref` lemma — now sig-amended to receive
  -- `_hDrainShape` from the consumer).
  let _ := _hDrainShape
  sorry

end DirectDagBody

theorem concretize_preserves_direct_dag
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds) :
    ∃ rank : Global → Nat,
      ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t := by
  obtain ⟨rank_src, hrank_src⟩ := hacyclic
  let origin : Global → Global := DirectDagBody.templateOf tds cd hconc hunique
  let rank_cd : Global → Nat := fun g => rank_src (origin g)
  refine ⟨rank_cd, ?_⟩
  have htransport : DirectDagBody.RankTransport tds cd rank_src rank_cd := by
    intro g templateName templateDt htemplate
    show rank_src (origin g) = rank_src templateName
    have heq : origin g = templateName :=
      DirectDagBody.templateOf_eq_witness hconc hunique htemplate
    rw [heq]
  intro g cdt hget c hc t ht
  obtain ⟨templateDt, htemplate⟩ := DirectDagBody.templateOf_spec hconc hunique hget
  -- BLOCKED-spine-transfer-drain-shape: discharge of `_hDrainShape` premise
  -- (sig amendment 2026-05-04, Defect 3). Composes `ConcretizeUniqueNames`
  -- (uniqueness of (templateName, args) producing each cd-key) with
  -- `StrongNewNameShape` (cd-keyed dataTypes are either source-monomorphic
  -- with `concretizeName g #[] = g`, or drain-produced with the canonical
  -- `(templateName, args)` recorded in `mono`).
  have hDrainShape : ∀ g' templateName' args',
       (∃ cdt' : Concrete.DataType, cd.getByKey g' = some (.dataType cdt')) →
       concretizeName templateName' args' = g' →
       templateName' = g' ∧ args' = #[] := by
    sorry
  exact DirectDagBody.spine_transfer hconc hunique hrank_src htransport hget htemplate hDrainShape c hc t ht

-- `SizeBoundVisInv` DELETED (orphan — mentioned only in `sizeBound_ok_of_rank`'s
-- FINDINGS comment as a proof strategy hint, never consumed). Reintroduce if
-- `sizeBound_ok_of_rank`'s proof actually needs it.

/-- Structural invariant: every `.dataType` in `cd` is keyed by its own name.
True of `concretize`'s output (see `Compiler/Concretize.lean:889, 920`), but
not part of `Concrete.Decls`'s type — must be proved as a separate theorem
about concretize output. -/
@[expose]
def Concrete.Decls.DtNameIsKey (cd : Concrete.Decls) : Prop :=
  ∀ g dt, cd.getByKey g = some (.dataType dt) → g = dt.name

/- `concretize_produces_dtNameIsKey` moved to `CompilerProgress.lean` (takes
a `Typed.Decls.DtNameIsKey` hypothesis discharged by
`checkAndSimplify_preserves_dtNameIsKey`). -/

/-! ### Typ.sizeBound under SpineRefsBelow + vis invariant.

The core lemma for `sizeBound_ok_of_rank`: given a spine-bounded rank witness
and an invariant on `vis` ("every `g'' ∈ vis` has `rank g'' ≥ bd`"), every
`DataType.sizeBound` / `Typ.sizeBound` recursion succeeds. -/

/-- Vis invariant carried through `sizeBound_ok_strong`: every element of
`vis` that IS a cd-dt key has rank strictly greater than `rank g`. Elements of
`vis` that are NOT cd-dt keys are unconstrained (the visited check only
triggers for cd-dt keys in practice). -/
@[expose]
def SizeBoundVisInv (cd : Concrete.Decls) (rank : Global → Nat) (g : Global)
    (vis : Std.HashSet Global) : Prop :=
  ∀ g'' : Global, vis.contains g'' = true →
    ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' > rank g

/-- Strong-induction core lemma: given SpineRefsBelow-form rank + DtNameIsKey +
RefClosed, `DataType.sizeBound` succeeds at every `(bound, vis)` whose cd-dt
members have rank strictly greater than `rank g`. Recursion grows `vis` by
`dt.name = g` while dropping current rank to `rank g' < rank g`; the invariant
is preserved pointwise because new `vis` elements are either old (with rank
> old-rank > new-rank) or `g` (with rank = old-rank > new-rank). -/
theorem sizeBound_ok_strong
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    ∀ (n : Nat) (g : Global) (dt : Concrete.DataType)
      (bound : Nat) (vis : Std.HashSet Global),
      rank g = n →
      cd.getByKey g = some (.dataType dt) →
      SizeBoundVisInv cd rank g vis →
      ∃ m, Concrete.DataType.sizeBound cd bound vis dt = .ok m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g dt bound vis hrankEq hget hvis
    cases bound with
    | zero =>
      refine ⟨1, ?_⟩; unfold Concrete.DataType.sizeBound; rfl
    | succ bound' =>
      -- `¬ vis.contains dt.name`: dt.name = g (DtNameIsKey); if g ∈ vis, the
      -- vis invariant gives `rank g > rank g` via cd.getByKey g = .dataType dt.
      have hdtName : g = dt.name := hdtkey g dt hget
      have hnvis : ¬ vis.contains dt.name = true := by
        intro hc
        rw [← hdtName] at hc
        have : rank g > rank g := hvis g hc dt hget
        exact Nat.lt_irrefl _ this
      unfold Concrete.DataType.sizeBound
      simp only [hnvis, if_false, Bool.false_eq_true]
      simp only [bind, Except.bind, pure, Except.pure]
      -- Typ-level helper: spine-bounded rank → Typ.sizeBound succeeds.
      -- Invariant on `v`: every cd-dt key in v has rank strictly greater than rank g.
      have htypBound : ∀ (b : Nat) (t : Concrete.Typ) (v : Std.HashSet Global),
          Concrete.Typ.RefClosed cd t →
          Concrete.Typ.SpineRefsBelow rank (rank g) t →
          (∀ g'' : Global, v.contains g'' = true →
              ∀ dt'', cd.getByKey g'' = some (.dataType dt'') →
                rank g'' ≥ rank g) →
          ∃ k, Concrete.Typ.sizeBound cd b v t = .ok k := by
        intro b
        induction b with
        | zero =>
          intros; refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
        | succ b' ihb =>
          intro t v hrc_t hspine hv_inv
          cases t with
          | unit =>
            refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | field =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | pointer t' =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | function ins out =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | tuple ts =>
            cases hrc_t; rename_i hrc_ts
            cases hspine; rename_i hsp_ts
            unfold Concrete.Typ.sizeBound
            conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
            simp only [Array.toList_attach, List.attachWith]
            apply List.foldlM_except_ok'
            intro acc t' ht'
            obtain ⟨t'val, ht'mem, ht'eq⟩ := List.mem_pmap.mp ht'
            subst ht'eq
            obtain ⟨m, hm⟩ := ihb t'val v (hrc_ts t'val ht'mem) (hsp_ts t'val ht'mem) hv_inv
            exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
          | array t' n₁ =>
            cases hrc_t; rename_i hrc_inner
            cases hspine; rename_i hsp_inner
            obtain ⟨m, hm⟩ := ihb t' v hrc_inner hsp_inner hv_inv
            refine ⟨n₁ * m, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hm, bind, Except.bind, pure, Except.pure]
          | ref g'' =>
            cases hrc_t; rename_i hdt'
            obtain ⟨dt', hget'⟩ := hdt'
            cases hspine; rename_i hrank_lt
            -- rank g'' < rank g. Recurse via outer IH at rank g''.
            have hrank_lt_n : rank g'' < n := hrankEq ▸ hrank_lt
            have hvis' : SizeBoundVisInv cd rank g'' v := by
              intro g''' hc dt''' hget'''
              have := hv_inv g''' hc dt''' hget'''  -- rank g''' ≥ rank g
              exact Nat.lt_of_lt_of_le hrank_lt this
            obtain ⟨k, hk⟩ := ih (rank g'') hrank_lt_n g'' dt' b' v rfl hget' hvis'
            refine ⟨k, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hget', hk]
      -- Vis invariant after inserting dt.name = g: every cd-dt key g'' in
      -- (vis.insert dt.name) has rank g'' ≥ rank g.
      have hVisInsert :
          ∀ g'' : Global, (vis.insert dt.name).contains g'' = true →
            ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' ≥ rank g := by
        intro g'' hc dt'' hget''
        rw [Std.HashSet.contains_insert] at hc
        rcases Bool.or_eq_true .. |>.mp hc with heq | hin
        · have hname : dt.name = g'' := LawfulBEq.eq_of_beq heq
          rw [← hname, ← hdtName]
          exact Nat.le_refl _
        · exact Nat.le_of_lt (hvis g'' hin dt'' hget'')
      -- mapM over dt.constructors.
      have hMap := @List.mapM_except_ok _ _ _
        (Concrete.Constructor.sizeBound cd bound' (vis.insert dt.name))
        dt.constructors (by
          intro c hc
          unfold Concrete.Constructor.sizeBound
          apply List.foldlM_except_ok'
          intro acc t ht
          have hrc_decl : Concrete.Declaration.RefClosed cd (.dataType dt) :=
            hrc g _ hget
          have hrc_t : Concrete.Typ.RefClosed cd t := hrc_decl c hc t ht
          have hspine : Concrete.Typ.SpineRefsBelow rank (rank g) t :=
            hrank g dt hget c hc t ht
          obtain ⟨k, hk⟩ :=
            htypBound bound' t (vis.insert dt.name) hrc_t hspine hVisInsert
          exact ⟨acc + k, by simp [hk, bind, Except.bind, pure, Except.pure]⟩)
      obtain ⟨sizes, hsizes⟩ := hMap
      refine ⟨sizes.foldl max 0 + 1, ?_⟩
      simp [hsizes, bind, Except.bind, pure, Except.pure]

/-- Size-bound termination from a spine-bounded rank witness + DtNameIsKey.
The entry-point `SizeBoundOk cd` form quantifies over `vis` with full
cd-dt disjointness; that disjointness vacuously satisfies
`SizeBoundVisInv` (no cd-dt keys in vis → the rank-greater hypothesis
is vacuous). -/
theorem sizeBound_ok_of_rank
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    Concrete.Decls.SizeBoundOk cd := by
  intro bound vis dt hex hdisjoint
  obtain ⟨g, hget⟩ := hex
  -- hdisjoint: for all g' dt', cd.getByKey g' = .dataType dt' → ¬ vis.contains dt'.name.
  -- Translate to SizeBoundVisInv: any g'' ∈ vis that IS a cd-dt key contradicts
  -- disjointness (since DtNameIsKey gives dt''.name = g'', and g'' ∈ vis).
  have hVisInv : SizeBoundVisInv cd rank g vis := by
    intro g'' hcontains dt'' hget''
    exfalso
    have hname : g'' = dt''.name := hdtkey g'' dt'' hget''
    have : ¬ vis.contains dt''.name = true := hdisjoint g'' dt'' hget''
    rw [← hname] at this
    exact this hcontains
  exact sizeBound_ok_strong cd hrc hdtkey rank hrank (rank g) g dt bound vis rfl hget hVisInv

/-- `concretize` output has no direct datatype cycles (`SizeBoundOk`).
Composed from `concretize_produces_refClosed` + `concretize_preserves_direct_dag`
+ `concretize_produces_dtNameIsKey` + `sizeBound_ok_of_rank`.

Takes `hDtNameIsKey_tds` and `hCtorPresent_tds` to thread into
`concretize_produces_refClosed` (downstream discharge, `CompilerProgress`). -/
theorem concretize_produces_sizeBoundOk
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hDtNameIsKey_tds : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent_tds : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList) :
    Concrete.Decls.SizeBoundOk cd := by
  have hrc := concretize_produces_refClosed hmono hts hconc hunique
    hDtNameIsKey_tds hCtorPresent_tds
  obtain ⟨rank, hrank⟩ := concretize_preserves_direct_dag hconc hacyclic hunique
  exact sizeBound_ok_of_rank cd hrc hdtkey rank hrank

/-- Concretize's layout map succeeds on every concretize-output `cd`. Requires
the source-level acyclicity hypothesis + `DtNameIsKey cd` (discharged upstream
by `concretize_produces_dtNameIsKey` + source-level `DtNameIsKey tds`). Threads
`hDtNameIsKey_tds` / `hCtorPresent_tds` through to `concretize_produces_refClosed`. -/
theorem concretize_layoutMap_progress
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hDtNameIsKey_tds : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent_tds : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList) :
    ∃ lm, Concrete.Decls.layoutMap cd = .ok lm :=
  layoutMap_ok_of_refClosed cd
    (concretize_produces_refClosed hmono hts hconc hunique hDtNameIsKey_tds hCtorPresent_tds)
    (concretize_produces_sizeBoundOk hmono hts hconc hacyclic hunique hdtkey
      hDtNameIsKey_tds hCtorPresent_tds)

end Aiur

end -- @[expose] public section
