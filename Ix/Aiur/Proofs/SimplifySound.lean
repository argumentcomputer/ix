module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Simple
public import Ix.Aiur.Semantics.SourceEval

/-!
Match compiler soundness.

Adapt Maranget's correctness proof for decision-tree pattern compilation. For
every `Simple.Term` produced from a `Typed.Term` by the rewritten `simplifyTerm`,
the decision tree matches exactly when the original nested pattern would have
matched, and binds the same locals to the same values.

References: CompCert `Cminorgenproof`, CakeML `pat_to_dec`, Maranget 2008.
Largest single proof; iteration depth is the bottleneck.
-/

public section

namespace Aiur

open Source

/-- Predicate: `t` is an "exhaustive match" — placeholder for the real
pattern/tag coverage check. Once `Typed.Term.subTerms` and type-env traversal
are available, this unfolds to: every `.match` node's patterns cover every
constructor of its scrutinee's declared type. -/
def IsExhaustiveMatch (_decls : Source.Decls) (_t : Typed.Term) : Prop :=
  True

/-- Structural precondition for `simplifyDecls`: every `match` in every
function body is exhaustive with respect to the scrutinee's type under
`decls`. -/
def MatchesExhaustive (decls : Source.Decls) (typedDecls : Typed.Decls) : Prop :=
  ∀ name f, typedDecls.getByKey name = some (.function f) →
    IsExhaustiveMatch decls f.body

/-- Computable sigma-form of `Concretize.lean`'s `List.mapM_except_ok`: given a
per-element `Σ'` witness, construct a whole-list witness. Needed in a `def`
context (our `simplifyTypedTerm_ok_witness` lives in `Type` so it can be
consumed destructuring-style). -/
private def List.mapM_except_ok_sigma {α β ε : Type}
    {f : α → Except ε β} : ∀ (l : List α),
    (∀ a ∈ l, Σ' b, f a = .ok b) →
    Σ' bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      let ⟨y, hy⟩ := h x List.mem_cons_self
      have hxs : ∀ a ∈ xs, Σ' b, f a = .ok b :=
        fun a ha => h a (List.mem_cons_of_mem _ ha)
      let ⟨ys, hys⟩ := List.mapM_except_ok_sigma xs hxs
      exact ⟨y :: ys, by
        simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]⟩

/-! `simplifyTypedTerm_ok_witness` proves that every call to `simplifyTypedTerm`
returns `.ok _`. The function body has no `throw` or `.error`: it either ends
in `pure (...)` at each explicit arm, or falls through to the catchall
`| t => pure t`. The proof is by well-founded recursion on `sizeOf t`. -/

def simplifyTypedTerm_ok_witness (decls : Source.Decls) (t : Typed.Term) :
    Σ' t' : Typed.Term, simplifyTypedTerm decls t = .ok t' := by
  match t with
  -- Catchall arms (go through `| t => pure t` in the function body).
  | .unit τ e =>
      exact ⟨.unit τ e, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .var τ e l =>
      exact ⟨.var τ e l, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .ref τ e g tArgs =>
      exact ⟨.ref τ e g tArgs, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .field τ e v =>
      exact ⟨.field τ e v, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .add τ e a b =>
      exact ⟨.add τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .sub τ e a b =>
      exact ⟨.sub τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .mul τ e a b =>
      exact ⟨.mul τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .eqZero τ e a =>
      exact ⟨.eqZero τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .proj τ e a n =>
      exact ⟨.proj τ e a n, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .get τ e a n =>
      exact ⟨.get τ e a n, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .slice τ e a i j =>
      exact ⟨.slice τ e a i j, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .set τ e a n v =>
      exact ⟨.set τ e a n v, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .store τ e a =>
      exact ⟨.store τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .load τ e a =>
      exact ⟨.load τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .ptrVal τ e a =>
      exact ⟨.ptrVal τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .ioGetInfo τ e k =>
      exact ⟨.ioGetInfo τ e k, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .ioRead τ e i n =>
      exact ⟨.ioRead τ e i n, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8BitDecomposition τ e a =>
      exact ⟨.u8BitDecomposition τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8ShiftLeft τ e a =>
      exact ⟨.u8ShiftLeft τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8ShiftRight τ e a =>
      exact ⟨.u8ShiftRight τ e a, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8Xor τ e a b =>
      exact ⟨.u8Xor τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8Add τ e a b =>
      exact ⟨.u8Add τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8Sub τ e a b =>
      exact ⟨.u8Sub τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8And τ e a b =>
      exact ⟨.u8And τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  | .u8Or τ e a b =>
      exact ⟨.u8Or τ e a b, by simp [simplifyTypedTerm, pure, Except.pure]⟩
  -- Recursive: single sub-term.
  | .ret τ e r =>
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.ret τ e r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hr]⟩
  -- Recursive: two sub-terms.
  | .u8LessThan τ e a b =>
      let ⟨a', ha⟩ := simplifyTypedTerm_ok_witness decls a
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      exact ⟨.u8LessThan τ e a' b', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, ha, hb]⟩
  | .u32LessThan τ e a b =>
      let ⟨a', ha⟩ := simplifyTypedTerm_ok_witness decls a
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      exact ⟨.u32LessThan τ e a' b', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, ha, hb]⟩
  | .ioWrite τ e d r =>
      let ⟨d', hd⟩ := simplifyTypedTerm_ok_witness decls d
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.ioWrite τ e d' r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hd, hr]⟩
  -- Recursive: three sub-terms.
  | .assertEq τ e a b r =>
      let ⟨a', ha⟩ := simplifyTypedTerm_ok_witness decls a
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.assertEq τ e a' b' r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, ha, hb, hr]⟩
  -- Recursive: four sub-terms.
  | .ioSetInfo τ e k i l r =>
      let ⟨k', hk⟩ := simplifyTypedTerm_ok_witness decls k
      let ⟨i', hi⟩ := simplifyTypedTerm_ok_witness decls i
      let ⟨l', hl⟩ := simplifyTypedTerm_ok_witness decls l
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.ioSetInfo τ e k' i' l' r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure,
              hk, hi, hl, hr]⟩
  -- Simple `.let` arms (recurses on v, b).
  | .let τ e (.var x) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      exact ⟨.let τ e (.var x) v' b', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]⟩
  | .let τ e .wildcard v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      exact ⟨.let τ e .wildcard v' b', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]⟩
  -- `.tuple` / `.array`: Array sub-terms via `attach.mapM`.
  | .tuple τ e ts =>
      let hall : ∀ t ∈ ts.toList, Σ' t', simplifyTypedTerm decls t = .ok t' :=
        fun t ht => by
          have hmem : t ∈ ts := Array.mem_toList_iff.mp ht
          have : sizeOf t < sizeOf (Typed.Term.tuple τ e ts) := by
            have := Array.sizeOf_lt_of_mem hmem
            grind
          exact simplifyTypedTerm_ok_witness decls t
      let ⟨ls, hls⟩ := List.mapM_except_ok_sigma ts.toList hall
      have hmap :
          ts.attach.mapM (m := Except CheckError)
              (fun ⟨t, _⟩ => simplifyTypedTerm decls t) = .ok ls.toArray := by
        rw [Array.mapM_subtype (g := fun t => simplifyTypedTerm decls t) (fun _ _ => rfl)]
        rw [Array.unattach_attach]
        rw [Array.mapM_eq_mapM_toList]
        rw [hls]
        rfl
      exact ⟨.tuple τ e ls.toArray, by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hmap]⟩
  | .array τ e ts =>
      let hall : ∀ t ∈ ts.toList, Σ' t', simplifyTypedTerm decls t = .ok t' :=
        fun t ht => by
          have hmem : t ∈ ts := Array.mem_toList_iff.mp ht
          have : sizeOf t < sizeOf (Typed.Term.array τ e ts) := by
            have := Array.sizeOf_lt_of_mem hmem
            grind
          exact simplifyTypedTerm_ok_witness decls t
      let ⟨ls, hls⟩ := List.mapM_except_ok_sigma ts.toList hall
      have hmap :
          ts.attach.mapM (m := Except CheckError)
              (fun ⟨t, _⟩ => simplifyTypedTerm decls t) = .ok ls.toArray := by
        rw [Array.mapM_subtype (g := fun t => simplifyTypedTerm decls t) (fun _ _ => rfl)]
        rw [Array.unattach_attach]
        rw [Array.mapM_eq_mapM_toList]
        rw [hls]
        rfl
      exact ⟨.array τ e ls.toArray, by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hmap]⟩
  | .app τ e g tArgs args u =>
      let hall : ∀ a ∈ args, Σ' a', simplifyTypedTerm decls a = .ok a' :=
        fun a ha => by
          have : sizeOf a < sizeOf (Typed.Term.app τ e g tArgs args u) := by
            have := List.sizeOf_lt_of_mem ha
            grind
          exact simplifyTypedTerm_ok_witness decls a
      let ⟨ls, hls⟩ := List.mapM_except_ok_sigma args hall
      have hmap :
          args.attach.mapM (m := Except CheckError)
              (fun ⟨a, _⟩ => simplifyTypedTerm decls a) = .ok ls := by
        rw [List.mapM_subtype (g := fun a => simplifyTypedTerm decls a) (fun _ _ => rfl)]
        rw [List.unattach_attach]
        rw [hls]
      exact ⟨.app τ e g tArgs ls u, by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hmap]⟩
  -- `.debug`: Option sub-term + a tail sub-term `r`.
  | .debug τ e l none r =>
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.debug τ e l none r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hr]⟩
  | .debug τ e l (some sub) r =>
      let ⟨sub', hsub⟩ := simplifyTypedTerm_ok_witness decls sub
      let ⟨r', hr⟩ := simplifyTypedTerm_ok_witness decls r
      exact ⟨.debug τ e l (some sub') r', by
        simp [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hsub, hr]⟩
  -- Refutable-pattern `.let`: six sub-patterns, all with identical structure.
  -- We build the witness explicitly as the body the `do`-block would produce.
  | .let τ e (.ref g pats) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.ref g pats, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.ref g pats, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .let τ e (.field c) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.field c, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.field c, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .let τ e (.tuple pats) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.tuple pats, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.tuple pats, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .let τ e (.array pats) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.array pats, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.array pats, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .let τ e (.or p1 p2) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.or p1 p2, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.or p1 p2, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .let τ e (.pointer inner) v b =>
      let ⟨v', hv⟩ := simplifyTypedTerm_ok_witness decls v
      let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
      let tmp : Typed.Term := .var v'.typ false tmpVar
      let body : Typed.Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ
              (MatchCompiler.runMatchCompiler decls tmp [(.pointer inner, b')]).fst with
        | some rewrite => rewrite
        | none => .match b'.typ b'.escapes tmp [(.pointer inner, b')]
      refine ⟨.let τ e (.var tmpVar) v' body, ?_⟩
      show simplifyTypedTerm _ _ = .ok _
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hv, hb]
      rfl
  | .match τ e scrut branches =>
      let sw := simplifyTypedTerm_ok_witness decls scrut
      let scrut' : Typed.Term := sw.fst
      have hs : simplifyTypedTerm decls scrut = .ok scrut' := sw.snd
      let hall :
          ∀ pb ∈ branches,
            Σ' pb',
              (do let b' ← simplifyTypedTerm decls pb.2; pure (pb.1, b')) =
                (.ok pb' : Except CheckError (Pattern × Typed.Term)) :=
        fun pb hpb => by
          obtain ⟨p, b⟩ := pb
          have hmem : sizeOf (p, b) < sizeOf branches := List.sizeOf_lt_of_mem hpb
          have : sizeOf b < sizeOf (Typed.Term.match τ e scrut branches) := by
            simp [Prod.mk.sizeOf_spec] at hmem
            simp only [Typed.Term.match.sizeOf_spec]
            omega
          have : sizeOf b < 1 + sizeOf τ + 1 + sizeOf scrut + sizeOf branches := by
            simp [Prod.mk.sizeOf_spec] at hmem
            omega
          let ⟨b', hb⟩ := simplifyTypedTerm_ok_witness decls b
          exact ⟨(p, b'), by
            simp [bind, Except.bind, pure, Except.pure, hb]⟩
      let ⟨branches', hbs⟩ := List.mapM_except_ok_sigma branches hall
      have hmap :
          branches.attach.mapM (m := Except CheckError)
              (fun pb => (simplifyTypedTerm decls pb.1.2).map (Prod.mk pb.1.1))
              = .ok branches' := by
        rw [List.mapM_subtype
              (g := fun pb : Pattern × Typed.Term =>
                (simplifyTypedTerm decls pb.2).map (Prod.mk pb.1))
              (by intros; rfl)]
        rw [List.unattach_attach]
        -- Bridge do-block form (hbs) to `.map` form.
        have hbridge :
            (fun pb : Pattern × Typed.Term =>
              (simplifyTypedTerm decls pb.2).map (Prod.mk pb.1))
            = (fun pb => do let b' ← simplifyTypedTerm decls pb.2; pure (pb.1, b')) := by
          funext pb
          cases simplifyTypedTerm decls pb.2 <;>
            simp [Except.map, bind, Except.bind, pure, Except.pure]
        rw [hbridge]
        exact hbs
      -- `mkResult` is defined as a function of its two parameters `s` and `bs`,
      -- so the match-on-`s` inside it does *not* close over `hs` (which only
      -- mentions `scrut'`). That avoids the dependent-motive issue that arises
      -- if we match on `scrut'` directly in the tactic state.
      let mkResult : Typed.Term → List (Pattern × Typed.Term) → Typed.Term :=
        fun s bs =>
          match MatchCompiler.decisionToTyped τ s.typ
                  (MatchCompiler.runMatchCompiler decls s bs).fst with
          | some rewrite => rewrite
          | none =>
            match s with
            | .var .. => .match τ e s bs
            | _ =>
              .let τ e (.var tmpVar) s (.match τ e (.var s.typ false tmpVar) bs)
      refine ⟨mkResult scrut' branches', ?_⟩
      show simplifyTypedTerm _ _ = .ok (mkResult scrut' branches')
      simp only [simplifyTypedTerm, bind, Except.bind, pure, Except.pure, hs]
      rw [hmap]
      simp only [mkResult]
      cases scrut' <;> grind
termination_by sizeOf t

/-! ### Helpers for `simplifyDecls_preservation` -/





/-- The pure version of `simplifyDecls`'s step function. The `.function`
branch's inner simplification result is existential (comes from
`simplifyTypedTerm_ok_witness`); we materialise it via `.1`. -/
private def simplifyDeclsStep (decls : Source.Decls) :
    Typed.Decls → (Global × Typed.Declaration) → Typed.Decls :=
  fun acc (name, d) => match d with
    | .function f =>
      let body' := (simplifyTypedTerm_ok_witness decls f.body).1
      acc.insert name (.function { f with body := body' })
    | .dataType dt => acc.insert name (.dataType dt)
    | .constructor dt c => acc.insert name (.constructor dt c)

end Aiur

end -- public section
