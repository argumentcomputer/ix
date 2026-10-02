import Ix.CompileM
import Ix.Sharing.Verify.TieredWire

/-!
# The compiler's sharing builder

The compiler's canonical sharing builder `Ix.CompileM.buildConstantWithSharing`
shares the payload's roots (`constantInfoRootExprs`) with
`canonicalSharingTiered .tagN` and writes the result back with `withRootExprs`
(`Ix.Sharing.Exact.withRoots`, which fails unless there is one root per slot);
its output facts come from `Tiered.canonicalSharingTiered_format` (`FormatOK`:
every table entry and root is wire-safe, the table count fits a `UInt64`, and
Shares point backwards). The builder fails when the construction does (a
resource limit or an internal error), so the theorems here describe successful
builds, and `SharingSucceeds` is the hypothesis under which a compile step
succeeds. `BlockResult.mk'` then stores bytes that decode back to the built
block, and the singleton-driver tail `finishConstantInfoWithSharing` fails
only when the builder does (`SharingRunOK`).
-/

namespace Ix.Sharing.Verify

/-- The primary reference and universe tables in a production block state are
representable by the constant wire format. -/
structure BlockWireTablesWF (state : Ix.CompileM.BlockState) : Prop where
  refsCount : state.refs.size < UInt64.size
  refs : ∀ ref ∈ state.refs, ref.hash.size = 32
  univsCount : state.univs.size < UInt64.size
  univs : ∀ univ ∈ state.univs, Ixon.Verify.Codec.Univ.WireWF univ

/-- Assemble an unshared axiom constant from one compiled type and the primary
tables of its final production block state. -/
def unsharedAxiomConstant (isUnsafe : Bool) (lvls : UInt64)
    (typ : Ixon.Expr) (state : Ix.CompileM.BlockState) : Ixon.Constant :=
  { info := .axio { isUnsafe, lvls, typ }
    sharing := #[]
    refs := state.refs
    univs := state.univs }

/-- Assemble an unshared definition constant from its two compiled roots and
the primary tables of its final production block state. -/
def unsharedDefinitionConstant (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) (lvls : UInt64)
    (typ value : Ixon.Expr) (state : Ix.CompileM.BlockState) : Ixon.Constant :=
  { info := .defn { kind, safety, lvls, typ, value }
    sharing := #[]
    refs := state.refs
    univs := state.univs }

/-- Every member of an expression array is in the expression codec's public
wire domain. -/
def ExprArrayWireWF (exprs : Array Ixon.Expr) : Prop :=
  ∀ expr ∈ exprs, expr.wireWF

theorem ExprArrayWireWF.empty : ExprArrayWireWF #[] := by
  intro expr hmem
  simp at hmem

/-! ## Root write-back (`Ix.Sharing.Exact.withRoots`)

`Ix.CompileM.withRootExprs` writes the shared roots back with
`Ix.Sharing.Exact.withRoots`, which consumes them as a cursor in
`constantInfoRoots` order and fails unless there is exactly one root per slot. -/

section WithRoots
open Ix.Sharing.Exact

/-- A successful `takeRoot` splits off the head of the cursor. -/
theorem takeRoot_eq_ok {rs : List Ixon.Expr} {e : Ixon.Expr} {rest : List Ixon.Expr}
    (h : takeRoot rs = .ok (e, rest)) : rs = e :: rest := by
  cases rs with
  | nil => simp [takeRoot] at h
  | cons x xs =>
    simp only [takeRoot, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- A successful `takeRoots k` splits off the first `k` roots of the cursor. -/
theorem takeRoots_eq_ok : ∀ {k : Nat} {rs es rest : List Ixon.Expr},
    takeRoots k rs = .ok (es, rest) → es.length = k ∧ rs = es ++ rest
  | 0, rs, es, rest, h => by
    simp only [takeRoots, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | k + 1, rs, es, rest, h => by
    simp only [takeRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨e, r1⟩ := p
      cases h2 : takeRoots k r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨es', r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, rfl⟩ := takeRoots_eq_ok h2
        rw [takeRoot_eq_ok h1]
        simp [hl]

/-- `takeRoots` takes exactly the roots it is asked for. -/
theorem takeRoots_append : ∀ (es rest : List Ixon.Expr),
    takeRoots es.length (es ++ rest) = .ok (es, rest)
  | [], rest => rfl
  | e :: es, rest => by
    simp only [List.length_cons, List.cons_append, takeRoots, takeRoot, bind, Except.bind,
      takeRoots_append es rest, pure, Except.pure]


/-- Writing wire-safe roots into a wire-safe mutual member keeps it wire-safe,
and leaves a wire-safe rest of the cursor. -/
theorem withMutConstRoots_wireWF {m m' : Ixon.MutConst} {rs rest : List Ixon.Expr}
    (h : withMutConstRoots m rs = .ok (m', rest)) (hm : m.wireWF)
    (hrs : ∀ e ∈ rs, e.wireWF) :
    m'.wireWF ∧ ∀ e ∈ rest, e.wireWF := by
  cases m with
  | defn d =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoot r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨value, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := takeRoot_eq_ok h1
        obtain rfl := takeRoot_eq_ok h2
        exact ⟨⟨hrs _ (by simp), hrs _ (by simp)⟩, fun e he => hrs e (by simp [he])⟩
  | indc i =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoots i.ctors.size r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨tys, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := takeRoot_eq_ok h1
        obtain ⟨hlen, rfl⟩ := takeRoots_eq_ok h2
        refine ⟨⟨hrs _ (by simp), ?_, ?_⟩, fun e he => hrs e (by simp [he])⟩
        · have := hm.2.1
          simp only [List.size_toArray, List.length_map, List.length_zip, Array.length_toList]
          omega
        · intro c hc
          simp only [List.mem_toArray, List.mem_map] at hc
          obtain ⟨⟨c0, t⟩, hmem, rfl⟩ := hc
          exact hrs t (by simp [(List.of_mem_zip hmem).2])
  | recr r =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoots r.rules.size r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨rhss, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := takeRoot_eq_ok h1
        obtain ⟨hlen, rfl⟩ := takeRoots_eq_ok h2
        refine ⟨⟨hrs _ (by simp), ?_, ?_⟩, fun e he => hrs e (by simp [he])⟩
        · have := hm.2.1
          simp only [List.size_toArray, List.length_map, List.length_zip, Array.length_toList]
          omega
        · intro c hc
          simp only [List.mem_toArray, List.mem_map] at hc
          obtain ⟨⟨c0, t⟩, hmem, rfl⟩ := hc
          exact hrs t (by simp [(List.of_mem_zip hmem).2])


/-- With one root per slot of the member at the front of the cursor,
`withMutConstRoots` succeeds and leaves the rest. -/
theorem withMutConstRoots_append (m : Ixon.MutConst) (xs rest : List Ixon.Expr)
    (hlen : xs.length = (mutConstRoots m).length) :
    ∃ m', withMutConstRoots m (xs ++ rest) = .ok (m', rest) := by
  cases m with
  | defn d =>
    match xs, hlen with
    | [a, b], _ => exact ⟨_, rfl⟩
  | indc i =>
    match xs, hlen with
    | t :: tys, hlen =>
      have htys : i.ctors.size = tys.length := by
        simp [mutConstRoots] at hlen; omega

      simp only [withMutConstRoots, List.cons_append, takeRoot, bind, Except.bind, htys,
        takeRoots_append, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, and_true, exists_eq']
  | recr r =>
    match xs, hlen with
    | t :: rhss, hlen =>
      have hrhss : r.rules.size = rhss.length := by
        simp [mutConstRoots] at hlen; omega

      simp only [withMutConstRoots, List.cons_append, takeRoot, bind, Except.bind, hrhss,
        takeRoots_append, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, and_true, exists_eq']

/-- An invariant of a `for` loop in `Except` whose body only continues: it holds
of the result when every successful step keeps it. -/
theorem forIn_except_inv {α β ε : Type} (P : List α → β → Prop)
    (f : α → β → Except ε (ForInStep β))
    (step : ∀ a l b r, P (a :: l) b → f a b = .ok r → ∃ b', r = .yield b' ∧ P l b') :
    ∀ (l : List α) (b r : β), P l b → forIn l b f = .ok r → P [] r
  | [], b, r, hb, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | a :: l, b, r, hb, h => by
    simp only [List.forIn_cons] at h
    cases hf : f a b with
    | error e => simp [hf, bind, Except.bind] at h
    | ok s =>
      obtain ⟨b', rfl, hb'⟩ := step a l b s hb hf
      simp only [hf, bind, Except.bind] at h
      exact forIn_except_inv P f step l b' r hb' h

/-- A `for` loop in `Except` succeeds when every step does (continuing) while
an invariant holds. -/
theorem forIn_except_ok {α β ε : Type} (Q : List α → β → Prop)
    (f : α → β → Except ε (ForInStep β))
    (step : ∀ a l b, Q (a :: l) b → ∃ b', f a b = .ok (.yield b') ∧ Q l b') :
    ∀ (l : List α) (b : β), Q l b → ∃ r, forIn l b f = .ok r ∧ Q [] r
  | [], b, hb => ⟨b, rfl, hb⟩
  | a :: l, b, hb => by
    obtain ⟨b', hf, hb'⟩ := step a l b hb
    obtain ⟨r, hr, hq⟩ := forIn_except_ok Q f step l b' hb'
    refine ⟨r, ?_, hq⟩
    simp only [List.forIn_cons, hf, bind, Except.bind, hr]


/-- A successful `Except` bind has a successful first action. -/
theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- The final cursor check of `withRoots` returns the reassembled payload. -/
theorem withRoots_tail {x info' : Ixon.ConstantInfo} {c : Prop} [Decidable c]
    (h : (if c then Except.ok x
      else Except.error (SharingError.internal "root cursor not exhausted")) =
        (Except.ok info' : Except SharingError Ixon.ConstantInfo)) : x = info' := by
  split at h <;> simp_all

/-- **The root write-back keeps the payload wire-safe**: `withRoots` of
wire-safe roots into a wire-safe `ConstantInfo` yields a wire-safe
`ConstantInfo`, for every variant. -/
theorem withRoots_wireWF {info info' : Ixon.ConstantInfo} {roots : Array Ixon.Expr}
    (h : withRoots info roots = .ok info') (hinfo : info.wireWF)
    (hroots : ∀ e ∈ roots, e.wireWF) : info'.wireWF := by
  have hrs : ∀ e ∈ roots.toList, e.wireWF := fun e he => hroots e (by simpa using he)
  simp only [withRoots] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  cases info with
  | defn d =>
    obtain ⟨⟨m, rest⟩, hw, h⟩ := except_bind_eq_ok h
    have hm := (withMutConstRoots_wireWF hw hinfo hrs).1
    cases m with
    | defn d' =>
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      exact withRoots_tail h ▸ hm
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | recr r =>
    obtain ⟨⟨m, rest⟩, hw, h⟩ := except_bind_eq_ok h
    have hm := (withMutConstRoots_wireWF hw hinfo hrs).1
    cases m with
    | recr r' =>
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      exact withRoots_tail h ▸ hm
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | axio a =>
    obtain ⟨⟨typ, rest⟩, hw, h⟩ := except_bind_eq_ok h
    have htyp : typ.wireWF := hrs typ (by simp [takeRoot_eq_ok hw])
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    exact withRoots_tail h ▸ htyp
  | quot q =>
    obtain ⟨⟨typ, rest⟩, hw, h⟩ := except_bind_eq_ok h
    have htyp : typ.wireWF := hrs typ (by simp [takeRoot_eq_ok hw])
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    exact withRoots_tail h ▸ htyp
  | cPrj p | rPrj p | iPrj p | dPrj p =>
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    exact withRoots_tail h ▸ hinfo
  | muts ms =>
    dsimp only at h
    rw [← Array.forIn_toList] at h
    obtain ⟨s, hs, h⟩ := except_bind_eq_ok h
    have hloop := forIn_except_inv
      (fun (l : List Ixon.MutConst) (b : Array Ixon.MutConst × List Ixon.Expr) =>
        b.1.size + l.length = ms.size ∧ (∀ m ∈ b.1, m.wireWF) ∧
          (∀ e ∈ b.2, e.wireWF) ∧ ∀ m ∈ l, m.wireWF) _
      (by
        intro a l b r hb hf
        obtain ⟨⟨m', rest⟩, hw, hf⟩ := except_bind_eq_ok hf
        simp only [pure, Except.pure, Except.ok.injEq] at hf
        have hm := withMutConstRoots_wireWF hw (hb.2.2.2 a (by simp)) hb.2.2.1
        refine ⟨_, hf.symm, ?_, ?_, hm.2, fun m hmem => hb.2.2.2 m (by simp [hmem])⟩
        · simp only [Array.size_push, List.length_cons] at hb ⊢
          omega
        · intro m hmem
          rcases Array.mem_push.mp hmem with hmem | rfl
          · exact hb.2.1 m hmem
          · exact hm.1)
      ms.toList (#[], roots.toList) s
      ⟨by simp, by simp, hrs, fun m hm => hinfo.2 m (by simpa using hm)⟩ hs
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    rw [← withRoots_tail h]
    have hsize : s.1.size = ms.size := by simpa using hloop.1
    exact ⟨hsize ▸ hinfo.1, hloop.2.1⟩


/-- `takeRoots` of a whole cursor. -/
theorem takeRoots_self (es : List Ixon.Expr) : takeRoots es.length es = .ok (es, []) := by
  simpa using takeRoots_append es []

/-- `withRoots` succeeds whenever there is one root per root slot. -/
theorem withRoots_ok_of_size {info : Ixon.ConstantInfo} {roots : Array Ixon.Expr}
    (hsize : roots.size = (constantInfoRoots info).size) :
    ∃ info', withRoots info roots = .ok info' := by
  have hlen : roots.toList.length = (constantInfoRoots info).size := by simpa using hsize
  simp only [withRoots]
  rw [ite_eq_right (by simp [hsize])]
  cases info with
  | defn d =>
    match roots.toList, hlen with
    | [a, b], _ => simp [withMutConstRoots, takeRoot, bind, Except.bind, pure, Except.pure]
  | recr r =>
    match roots.toList, hlen with
    | t :: rhss, hlen =>
      have hr : r.rules.size = rhss.length := by
        simp [constantInfoRoots, mutConstRoots] at hlen; omega
      simp [withMutConstRoots, takeRoot, bind, Except.bind, pure, Except.pure, hr,
        takeRoots_self]
  | axio a =>
    match roots.toList, hlen with
    | [t], _ => simp [takeRoot, bind, Except.bind, pure, Except.pure]
  | quot q =>
    match roots.toList, hlen with
    | [t], _ => simp [takeRoot, bind, Except.bind, pure, Except.pure]
  | cPrj p | rPrj p | iPrj p | dPrj p =>
    match roots.toList, hlen with
    | [], _ => simp [bind, Except.bind, pure, Except.pure]
  | muts ms =>
    dsimp only
    rw [← Array.forIn_toList]
    obtain ⟨s, hs, hq⟩ := forIn_except_ok
      (fun (l : List Ixon.MutConst) (b : Array Ixon.MutConst × List Ixon.Expr) =>
        b.2.length = (l.flatMap mutConstRoots).length)
      (fun m (s : Array Ixon.MutConst × List Ixon.Expr) => do
        let x ← withMutConstRoots m s.snd
        pure (ForInStep.yield (s.fst.push x.fst, x.snd)))
      (by
        intro a l b hb
        have hn : (b.2.take (mutConstRoots a).length).length = (mutConstRoots a).length := by
          simp only [List.flatMap_cons, List.length_append] at hb
          simp [List.length_take]; omega
        obtain ⟨m', hw⟩ := withMutConstRoots_append a _ (b.2.drop (mutConstRoots a).length) hn
        rw [List.take_append_drop] at hw
        refine ⟨(b.1.push m', b.2.drop (mutConstRoots a).length), ?_, ?_⟩
        · simp [hw, bind, Except.bind, pure, Except.pure]
        · simp only [List.flatMap_cons, List.length_append] at hb
          simp [List.length_drop, hb])
      ms.toList (#[], roots.toList) (by simpa [constantInfoRoots] using hlen)
    rw [hs]
    simp at hq
    simp [hq, bind, Except.bind, pure, Except.pure]

end WithRoots

/-- The production cursor-order extractor agrees with the catalog's logical
expression view for every mutual-member variant. -/
theorem mutConstRootExprs_eq_exprs (member : Ixon.MutConst) :
    Ix.CompileM.mutConstRootExprs member = member.exprs := by
  cases member with
  | defn definition => rfl
  | recr recursor => rfl
  | indc indInfo =>
    simp only [Ix.CompileM.mutConstRootExprs, Ixon.MutConst.exprs,
      Ixon.Inductive.exprs]
    congr 1
    change List.map (fun constructor => constructor.typ)
        indInfo.ctors.toList =
      List.flatMap (fun constructor => [constructor.typ])
        indInfo.ctors.toList
    exact List.map_eq_flatMap

/-- The canonical production root array has exactly the catalog's expression
sequence, including flattened mutual members and recursor rules. -/
theorem constantInfoRootExprs_toList (info : Ixon.ConstantInfo) :
    (Ix.CompileM.constantInfoRootExprs info).toList = info.exprs := by
  cases info with
  | defn definition => rfl
  | recr recursor => rfl
  | axio axiomInfo => rfl
  | quot quotient => rfl
  | cPrj projection => rfl
  | rPrj projection => rfl
  | iPrj projection => rfl
  | dPrj projection => rfl
  | muts members =>
    simp only [Ix.CompileM.constantInfoRootExprs,
      Ixon.ConstantInfo.exprs]
    induction members.toList with
    | nil => rfl
    | cons member members ih =>
      simp only [List.flatMap_cons, mutConstRootExprs_eq_exprs, ih]

/-- The canonical sharing roots of one mutual member are exactly its
expression-bearing wire fields, so member wire safety covers every root. -/
theorem mutConstRootExprs_wireWF (member : Ixon.MutConst)
    (hmember : member.wireWF) :
    ∀ expr ∈ Ix.CompileM.mutConstRootExprs member, expr.wireWF := by
  cases member with
  | defn definition =>
    intro expr hmem
    simp [Ix.CompileM.mutConstRootExprs] at hmem
    rcases hmem with rfl | rfl
    · exact hmember.1
    · exact hmember.2
  | indc indInfo =>
    intro expr hmem
    simp only [Ix.CompileM.mutConstRootExprs, List.mem_cons,
      List.mem_map] at hmem
    rcases hmem with rfl | ⟨constructor, hconstructor, rfl⟩
    · exact hmember.1
    · exact hmember.2.2 constructor (by simpa using hconstructor)
  | recr recursor =>
    intro expr hmem
    simp only [Ix.CompileM.mutConstRootExprs, List.mem_cons,
      List.mem_map] at hmem
    rcases hmem with rfl | ⟨rule, hrule, rfl⟩
    · exact hmember.1
    · exact hmember.2.2 rule (by simpa using hrule)

/-- A wire-safe `ConstantInfo` automatically supplies a wire-safe canonical
sharing-root array.  This rules out a mismatch between the payload fields and
the roots consumed by the production singleton driver. -/
theorem constantInfoRootExprs_wireWF (info : Ixon.ConstantInfo)
    (hinfo : info.wireWF) :
    ExprArrayWireWF (Ix.CompileM.constantInfoRootExprs info) := by
  intro expr hmem
  cases info with
  | defn definition =>
    exact mutConstRootExprs_wireWF (.defn definition) hinfo expr
      (by simpa [Ix.CompileM.constantInfoRootExprs] using hmem)
  | recr recursor =>
    exact mutConstRootExprs_wireWF (.recr recursor) hinfo expr
      (by simpa [Ix.CompileM.constantInfoRootExprs] using hmem)
  | axio axiomInfo =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
    subst expr
    exact hinfo
  | quot quotient =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
    subst expr
    exact hinfo
  | cPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | rPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | iPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | dPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | muts members =>
    have hlist : expr ∈ members.toList.flatMap
        Ix.CompileM.mutConstRootExprs := by
      simpa [Ix.CompileM.constantInfoRootExprs] using hmem
    obtain ⟨member, hmember, hexpr⟩ := List.mem_flatMap.mp hlist
    exact mutConstRootExprs_wireWF member
      (hinfo.2 member (by simpa using hmember)) expr hexpr

/-- The compiler's root order is the order of `Ix.Sharing.Exact.constantInfoRoots`,
which `withRootExprs` consumes. -/
theorem constantInfoRootExprs_eq_roots (info : Ixon.ConstantInfo) :
    Ix.CompileM.constantInfoRootExprs info = Ix.Sharing.Exact.constantInfoRoots info := by
  have hm : Ix.CompileM.mutConstRootExprs = Ix.Sharing.Exact.mutConstRoots := by
    funext m
    cases m <;> rfl
  cases info <;> simp [Ix.CompileM.constantInfoRootExprs, Ix.Sharing.Exact.constantInfoRoots, hm]

/-- With one rewritten expression per root, the write-back succeeds. -/
theorem withRootExprs_ok_of_size {info : Ixon.ConstantInfo} {rewritten : Array Ixon.Expr}
    (hsize : rewritten.size = (Ix.CompileM.constantInfoRootExprs info).size) :
    ∃ info', Ix.CompileM.withRootExprs info rewritten = .ok info' := by
  rw [constantInfoRootExprs_eq_roots] at hsize
  obtain ⟨info', h⟩ := withRoots_ok_of_size hsize
  exact ⟨info', by simp [Ix.CompileM.withRootExprs, h, Except.mapError]⟩

/-- Writing wire-safe roots back preserves the payload's wire domain. -/
theorem withRootExprs_wireWF {info info' : Ixon.ConstantInfo} {rewritten : Array Ixon.Expr}
    (h : Ix.CompileM.withRootExprs info rewritten = .ok info')
    (hinfo : info.wireWF) (hwire : ExprArrayWireWF rewritten) : info'.wireWF := by
  simp only [Ix.CompileM.withRootExprs] at h
  cases hw : Ix.Sharing.Exact.withRoots info rewritten with
  | error e => simp [hw, Except.mapError] at h
  | ok x =>
    simp [hw, Except.mapError] at h
    exact h ▸ withRoots_wireWF hw hinfo hwire

/-! ## The canonical sharing builder -/

/-- The canonical sharing construction succeeds on the payload's roots under
`limits` and returns one root per input root: exactly when
`buildConstantWithSharing` succeeds (`buildConstantWithSharing_of_succeeds`). -/
def SharingSucceeds (limits : Ix.Sharing.Exact.Limits) (info : Ixon.ConstantInfo) :
    Prop :=
  ∃ r, Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits = .ok r ∧
    r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size

/-- A successful build is the canonical construction of the payload's roots,
written back into the payload. -/
theorem buildConstantWithSharing_eq_ok {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {refs : Array Address} {univs : Array Ixon.Univ}
    {block : Ixon.Constant}
    (h : Ix.CompileM.buildConstantWithSharing limits info refs univs = .ok block) :
    ∃ r info', Ix.Sharing.Exact.canonicalSharingTiered .tagN
        (Ix.CompileM.constantInfoRootExprs info) limits = .ok r ∧
      r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size ∧
      Ix.CompileM.withRootExprs info r.result.roots = .ok info' ∧
      block = { info := info', sharing := r.result.sharing, refs, univs } := by
  simp only [Ix.CompileM.buildConstantWithSharing] at h
  cases hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits with
  | error e =>
    simp [hr, Except.mapError, bind, Except.bind] at h
  | ok r =>
    simp only [hr, Except.mapError] at h
    by_cases hs : r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size
    · cases hw : Ix.CompileM.withRootExprs info r.result.roots with
      | error e =>
        simp [hs, hw, bind, Except.bind] at h
      | ok info' =>
        refine ⟨r, info', rfl, hs, hw, ?_⟩
        simp [hs, hw, bind, Except.bind, pure, Except.pure] at h
        exact h.symm
    · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The builder's result when the canonical construction succeeds with one
root per input root. -/
theorem buildConstantWithSharing_of_canonical {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {r : Ix.Sharing.Exact.TieredSharingResult}
    (hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits = .ok r)
    (hs : r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size)
    (refs : Array Address) (univs : Array Ixon.Univ) :
    ∃ info', Ix.CompileM.withRootExprs info r.result.roots = .ok info' ∧
      Ix.CompileM.buildConstantWithSharing limits info refs univs =
        .ok { info := info', sharing := r.result.sharing, refs, univs } := by
  obtain ⟨info', hw⟩ := withRootExprs_ok_of_size hs
  exact ⟨info', hw, by
    simp [Ix.CompileM.buildConstantWithSharing, hr, Except.mapError, hs, hw, bind,
      Except.bind, pure, Except.pure]⟩

/-- Under `SharingSucceeds` the builder succeeds, whatever the tables. -/
theorem buildConstantWithSharing_of_succeeds {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} (h : SharingSucceeds limits info)
    (refs : Array Address) (univs : Array Ixon.Univ) :
    ∃ block, Ix.CompileM.buildConstantWithSharing limits info refs univs = .ok block := by
  obtain ⟨r, hr, hs⟩ := h
  obtain ⟨_, _, hb⟩ := buildConstantWithSharing_of_canonical hr hs refs univs
  exact ⟨_, hb⟩

/-- **Every block the compiler's sharing builds is in the constant codec's wire
domain**, for every `ConstantInfo` variant: the payload's fields are kept,
its roots and the table come from the canonical construction, and
`Tiered.canonicalSharingTiered_format` makes them wire-safe with a table count
below `2^64`. -/
theorem buildConstantWithSharing_wireWF {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {state : Ix.CompileM.BlockState}
    {block : Ixon.Constant} (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (h : Ix.CompileM.buildConstantWithSharing limits info
      state.refs state.univs = .ok block) :
    block.wireWF := by
  obtain ⟨r, info', hr, -, hw, rfl⟩ := buildConstantWithSharing_eq_ok h
  obtain ⟨hentries, hroots, hcapacity, -, -⟩ := Tiered.canonicalSharingTiered_format hr
  refine ⟨withRootExprs_wireWF hw hinfo ?_, hcapacity, ?_, htables.refsCount,
    htables.refs, htables.univsCount, htables.univs⟩
  · intro expr hmem
    exact hroots expr (by simpa using hmem)
  · intro expr hmem
    exact hentries expr (by simpa using hmem)

/-- When the canonical construction keeps a singleton axiom root and builds no
table, the builder yields exactly the unshared axiom assembly. -/
theorem buildConstantWithSharing_axiom_eq_unshared
    (limits : Ix.Sharing.Exact.Limits) (isUnsafe : Bool) (lvls : UInt64)
    (typ : Ixon.Expr) (state : Ix.CompileM.BlockState)
    {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN #[typ] limits = .ok r)
    (hroots : r.result.roots = #[typ]) (htable : r.result.sharing = #[]) :
    Ix.CompileM.buildConstantWithSharing limits
        (.axio { isUnsafe, lvls, typ }) state.refs state.univs =
      .ok (unsharedAxiomConstant isUnsafe lvls typ state) := by
  have hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs (.axio { isUnsafe, lvls, typ })) limits = .ok r :=
    hsharing
  obtain ⟨info', hw, hb⟩ :=
    buildConstantWithSharing_of_canonical hr (by rw [hroots]; rfl) state.refs state.univs
  have hinfo : info' = .axio { isUnsafe, lvls, typ } := by
    rw [hroots] at hw
    have : Ix.CompileM.withRootExprs (.axio { isUnsafe, lvls, typ }) #[typ] =
        .ok (.axio { isUnsafe, lvls, typ }) := rfl
    rw [this] at hw
    exact (Except.ok.inj hw).symm
  rw [hb, hinfo]
  simp [htable, unsharedAxiomConstant]

/-- When the canonical construction keeps both definition roots and builds no
table, the builder yields exactly the unshared definition assembly. -/
theorem buildConstantWithSharing_definition_eq_unshared
    (limits : Ix.Sharing.Exact.Limits) (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) (lvls : UInt64) (typ value : Ixon.Expr)
    (state : Ix.CompileM.BlockState) {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN #[typ, value] limits = .ok r)
    (hroots : r.result.roots = #[typ, value]) (htable : r.result.sharing = #[]) :
    Ix.CompileM.buildConstantWithSharing limits
        (.defn { kind, safety, lvls, typ, value }) state.refs state.univs =
      .ok (unsharedDefinitionConstant kind safety lvls typ value state) := by
  have hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs (.defn { kind, safety, lvls, typ, value })) limits =
        .ok r := hsharing
  obtain ⟨info', hw, hb⟩ :=
    buildConstantWithSharing_of_canonical hr (by rw [hroots]; rfl) state.refs state.univs
  have hinfo : info' = .defn { kind, safety, lvls, typ, value } := by
    rw [hroots] at hw
    have : Ix.CompileM.withRootExprs (.defn { kind, safety, lvls, typ, value }) #[typ, value] =
        .ok (.defn { kind, safety, lvls, typ, value }) := rfl
    rw [this] at hw
    exact (Except.ok.inj hw).symm
  rw [hb, hinfo]
  simp [htable, unsharedDefinitionConstant]


/-- `BlockResult.mk'` stores exactly the production constant serialization,
so every wire-well-formed block is recovered from its stored bytes. Metadata
and projections do not affect those bytes. -/
theorem BlockResult.mk'_codec_roundtrip
    (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[])
    (hblock : block.wireWF) :
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes =
      .ok (Ix.CompileM.BlockResult.mk' block blockMeta projections).block := by
  change Ixon.deConstant (Ixon.ser block) = .ok block
  rw [show Ixon.ser block = Ixon.serConstant block from rfl]
  exact Ixon.Verify.deConstant_serConstant block hblock

/-- Verification condition carried from a production declaration driver to
the serialized main block it returns. -/
def BlockResultCodecWF (result : Ix.CompileM.BlockResult) : Prop :=
  result.block.wireWF ∧
  Ixon.deConstant result.blockBytes = .ok result.block

theorem BlockResult.mk'_codecWF
    (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[])
    (hblock : block.wireWF) :
    BlockResultCodecWF
      (Ix.CompileM.BlockResult.mk' block blockMeta projections) := by
  exact ⟨hblock,
    BlockResult.mk'_codec_roundtrip block blockMeta projections hblock⟩

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α)
    (next : α → Ix.CompileM.CompileM β) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (action >>= next) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state action with
      | .error err => .error err
      | .ok (value, state') =>
        Ix.CompileM.CompileM.run compileEnv blockEnv state' (next value) := by
  simp [Ix.CompileM.CompileM.run, ReaderT.run_bind, ExceptT.run_bind,
    StateT.run_bind]
  generalize
    (ReaderT.run action (compileEnv, blockEnv)).run.run state = result
  rcases result with ⟨result, state'⟩
  cases result <;> rfl

theorem run_getBlockState_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state Ix.CompileM.getBlockState =
      .ok (state, state) := rfl

theorem run_read_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state read =
      .ok ((compileEnv, blockEnv), state) := rfl

theorem run_liftSharing_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (x : Except Ix.CompileM.CompileError Ixon.Constant) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (Ix.CompileM.liftSharing x) =
      match x with
      | .ok c => .ok (c, state)
      | .error e => .error e := by
  cases x <;> rfl

/-- A successful build of any wire-safe payload, wrapped in the production
`BlockResult`, stores bytes that decode exactly to the built block. This
includes all projection variants and both empty and nonempty sharing. -/
theorem BlockResult.constantInfo_codec_roundtrip
    {limits : Ix.Sharing.Exact.Limits} (info : Ixon.ConstantInfo)
    {state : Ix.CompileM.BlockState} {block : Ixon.Constant}
    (blockMeta : Ixon.ConstantMeta) (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (h : Ix.CompileM.buildConstantWithSharing limits info
      state.refs state.univs = .ok block)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[]) :
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes =
      .ok block := by
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_wireWF hinfo htables h

/-- The production singleton-driver tail reads the current block state, runs
the canonical sharing builder under `CompileEnv.sharingLimits` and wraps its
result in the canonical `BlockResult`; it leaves the state unchanged, and it
fails exactly when the builder does. -/
theorem finishConstantWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info blockMeta) =
      match Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs with
      | .ok block => .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state)
      | .error e => .error e := by
  simp only [Ix.CompileM.finishConstantWithSharing, Ix.CompileM.buildBlockConstant,
    run_bind, run_getBlockState_eq, run_read_eq, run_liftSharing_eq]
  cases Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
    state.refs state.univs <;> rfl

/-- When the builder succeeds, the singleton-driver tail returns that block in
a wire-safe, exactly decodable `BlockResult` and leaves the state unchanged. -/
theorem finishConstantWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    {block : Ixon.Constant} (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (hbuild : Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
      state.refs state.univs = .ok block) :
    let result := Ix.CompileM.BlockResult.mk' block blockMeta
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info blockMeta) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  dsimp only
  constructor
  · rw [finishConstantWithSharing_run compileEnv blockEnv state info blockMeta, hbuild]
  · apply BlockResult.mk'_codecWF
    exact buildConstantWithSharing_wireWF hinfo htables hbuild

/-- `finishConstantInfoWithSharing` is `finishConstantWithSharing`. -/
theorem finishConstantInfoWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo)
    (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
      match Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs with
      | .ok block => .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state)
      | .error e => .error e :=
  finishConstantWithSharing_run compileEnv blockEnv state info blockMeta


/-- The outcome of a declaration run whose only possible failure is the
canonical sharing builder: either the run succeeds with a wire-safe, exactly
decodable `BlockResult`, or it fails with exactly the error the builder
returns on some payload and tables. This is the conclusion of the compiler
endpoint theorems; with the builder total (`SharingSucceeds`) only the first
case remains. -/
def SharingRunOK (limits : Ix.Sharing.Exact.Limits)
    (run : Except Ix.CompileM.CompileError
      (Ix.CompileM.BlockResult × Ix.CompileM.BlockState)) : Prop :=
  (∃ result state', run = .ok (result, state') ∧ BlockResultCodecWF result) ∨
  ∃ (info : Ixon.ConstantInfo) (state' : Ix.CompileM.BlockState)
    (err : Ix.CompileM.CompileError),
    Ix.CompileM.buildConstantWithSharing limits info state'.refs state'.univs =
      .error err ∧ run = .error err

/-- Every successful run covered by `SharingRunOK` returns a wire-safe, exactly
decodable block. -/
theorem SharingRunOK.codecWF {limits : Ix.Sharing.Exact.Limits}
    {run : Except Ix.CompileM.CompileError
      (Ix.CompileM.BlockResult × Ix.CompileM.BlockState)}
    (h : SharingRunOK limits run) {result : Ix.CompileM.BlockResult}
    {state' : Ix.CompileM.BlockState} (hrun : run = .ok (result, state')) :
    BlockResultCodecWF result := by
  rcases h with ⟨result', state'', hok, hcodec⟩ | ⟨_, _, err, _, herr⟩
  · rw [hrun] at hok
    cases hok
    exact hcodec
  · rw [hrun] at herr
    cases herr

/-- The singleton-driver tail on a wire-safe payload: it fails only when the
canonical sharing builder does, and otherwise returns a wire-safe, exactly
decodable block. -/
theorem finishConstantInfoWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state) :
    SharingRunOK compileEnv.sharingLimits
      (Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta)) := by
  rw [finishConstantInfoWithSharing_run compileEnv blockEnv state info blockMeta]
  cases hbuild : Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
      state.refs state.univs with
  | ok block =>
    exact .inl ⟨_, _, rfl, BlockResult.mk'_codecWF block blockMeta #[]
      (buildConstantWithSharing_wireWF hinfo htables hbuild)⟩
  | error err => exact .inr ⟨info, state, err, hbuild, rfl⟩

/-- When the canonical sharing of the payload succeeds, so does the
singleton-driver tail, with a wire-safe, exactly decodable block. -/
theorem finishConstantInfoWithSharing_run_codecWF_of_succeeds
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state)
    (hshare : SharingSucceeds compileEnv.sharingLimits info) :
    ∃ block,
      Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs = .ok block ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
        .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state) ∧
      BlockResultCodecWF (Ix.CompileM.BlockResult.mk' block blockMeta) := by
  obtain ⟨block, hbuild⟩ := buildConstantWithSharing_of_succeeds hshare state.refs state.univs
  obtain ⟨hrun, hcodec⟩ := finishConstantWithSharing_run_codecWF compileEnv blockEnv state
    info blockMeta hinfo htables hbuild
  exact ⟨block, hbuild, hrun, hcodec⟩

end Ix.Sharing.Verify
