import Ix.Cert.Statement
import Ix.CompileCert.Loop
import Ix.Cert.LowerDistinct

/-! # Each record's and each group's lowering (S1's units,: reader and ingress)

The S1 union is stated over units: one record's lowering, the modeller's
generated records then the record's own declaration, or a definition block's
declarations. IxC's decided units check closes each run of generated records
with an ungenerated declaration whose bases cover the run's
(`IxC/Kernel/Units.lean`). What the reader adds, per record:

* `stream_lowerings`: the stream `readRecords` decodes is its records'
  lowerings (`Read.decls`) concatenated, one per record, in order;
* `lowerDefinition_names`, `readDefinition_key`: a definition member's
  declaration declares exactly the member's key;
* `lowerInductive_decls`, `readInductive_lowering`: an inductive block lowers
  to the modeller's records then its `indDecl`, which declares only the
  block's member keys (its types', its constructors' and the recursors its
  shape indexes), through `readInductive`'s three loops (`forIn_pushes`);
* `readRecord_lowering`, `readRecords_units`: every record's lowering has
  `Lowering`'s shape, so the stream is the records' lowerings, each of that
  shape at its record's address;
* `memberKey_role_or_id`, `Lowering.closed`: under a table that keys only
  roles (`RolesKeyed`, `contextWith_keyed`) a member key is a role or input
  key, never derived, so each lowering is empty or ends in a declaration that
  is not generated (IxC's `Declaration.isGenerated`, `IxC/Kernel/Units.lean`).

The ingress side, the same facts over a Lean group's keys (`GroupKeyOf`: the
ingress keys of its constants):

* `convert_keys`: a group's conversion carries its keys
  (`convertInductive_keys` through the conversion's loops,
  `convertDefinitions_keys` with `defOrder_lt`);
* `lower_lowering`: a converted group's lowering has `LoweringBy`'s shape over
  them; `canonDecl_names`: the canonical levels keep the names;
* `lowerAll_lowerings`, `leanIngress_units`: the ingress's stream is its
  scheduled groups' lowerings concatenated, in schedule order, each with that
  shape over its group's keys (`scheduleOf_ok`, `graph_converted_ok`), which
  are never derived (`GroupKeyOf.not_derived`, so `LoweringBy.closed`).

So IxC's units of each side are the pieces `unitsOf` cuts each lowering into
(each an `IsLowering`, since every lowering ends in a declaration that is not
generated). Nothing here is about what `InModel.generate` returns: IxC's
decided units check closes each run of generated records and requires their
bases among the closing declaration's. -/

namespace Ix.Cert.ReaderUnits

open Ix.Kernel (ConstRef Mode)
open Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)

variable {md : Mode}

/-- A key the reader gives a member of the record at `owner`: of one of its
block's members or constructors, or of a recursor its block's shape indexes. -/
def MemberKeyOf (cx : Ctx md) (owner : Address) (k : CName md) : Prop :=
  ∃ ref : ConstRef Address,
    (ref.block = owner ∨ ∃ shape, cx.index.blocks[owner]? = some shape ∧ ref ∈ shape.recs) ∧
      cx.memberKey ref = .ok k

/-! ## The stream -/

/-- **The decoded stream is the records' lowerings, concatenated**: one
lowering per record, each what `readRecord` returned for it. -/
theorem stream_lowerings {cx : Ctx md} {st st' : State md} {records : List (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : StreamRead cx st records st' out) :
    ∃ rs : List (Read md),
      List.Forall₂ (fun (x : Address × Ixon.Constant) r => ∃ st₀, readRecord cx st₀ x.1 x.2 = .ok r) records rs ∧
        out.toList = (rs.map fun r => r.decls.toList).flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons st _ a c r rest out read _ ih =>
    obtain ⟨rs, holds, flat⟩ := ih
    exact ⟨r :: rs, .cons ⟨st, read⟩ holds, by simp [flat]⟩

/-- `stream_lowerings` for an accepted `readRecords`. -/
theorem readRecords_lowerings {cx : Ctx md} {st st' : State md} {records : Array (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : readRecords cx st records = .ok (st', out)) :
    ∃ rs : List (Read md),
      List.Forall₂ (fun (x : Address × Ixon.Constant) r => ∃ st₀, readRecord cx st₀ x.1 x.2 = .ok r)
        records.toList rs ∧
        out.toList = (rs.map fun r => r.decls.toList).flatten :=
  stream_lowerings (readRecords_spec h)

/-! ## Definition members -/

/-- **A lowered definition declares its header's name**, whatever its kind. -/
theorem lowerDefinition_names {hint : Option Ix.Kernel.ReducibilityHint} {st : State md}
    {heights : CName md → Nat} {cv : CVal md} {value : CExpr md} {kind : Ix.DefKind}
    {safety : Ix.DefinitionSafety} {decl : CDecl md} {rw : Bool}
    (h : lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    decl.names = [cv.name] := by
  unfold lowerDefinition at h
  dsimp only at h
  split at h
  · simp [declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · cases kind <;> simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> rfl

/-- **A definition member's declaration declares exactly the member's key.** -/
theorem readDefinition_key {cx : Ctx md} {st : State md} {heights : CName md → Nat}
    {ref : ConstRef Address} {lps : List Ix.Kernel.LevelParam} {mr : MemberReader md} {d : Ixon.Definition}
    {decl : CDecl md} {rw : Bool} (h : readDefinition cx st heights ref lps mr d = .ok (decl, rw)) :
    ∃ k, cx.memberKey ref = .ok k ∧ decl.names = [k] := by
  unfold readDefinition at h
  cases hk : cx.memberKey ref with
  | error e => simp [hk, bind, Except.bind] at h
  | ok k =>
    simp only [hk, bind, Except.bind] at h
    cases ht : mr.read d.typ with
    | error e => simp [ht] at h
    | ok t =>
      simp only [ht] at h
      cases hv : mr.read d.value with
      | error e => simp [hv] at h
      | ok v =>
        simp only [hv] at h
        exact ⟨k, rfl, lowerDefinition_names h⟩


/-! ## The inductive block's lowering -/

/-- An accepted branch of an `if` in `ReadM` is an accepted branch. -/
theorem ite_ok {α : Type} {c : Prop} [Decidable c] {x y : ReadM α} {r : α}
    (h : (if c then x else y) = .ok r) : x = .ok r ∨ y = .ok r := by
  by_cases hc : c
  · exact .inl (by simpa [hc] using h)
  · exact .inr (by simpa [hc] using h)

/-- **A lowered inductive block ends in its own declaration**: the modeller's
records (as many as `generated` says), then the block's `indDecl`, which
declares the block's types', constructors' and recursors' names, in that
order. -/
theorem lowerInductive_decls {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) :
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧
      d.names = rb.types.toList.map (·.1.name) ++ rb.ctors.toList.map (·.1.name) ++
        rb.recs.toList.map (·.1.name) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  have names : ∀ (block : List (Ix.Kernel.ConstantInfo md)),
      block = types.toList.map (fun x => Ix.Kernel.ConstantInfo.indInfo x.1 {}) ++
        ctors.toList.map (fun x => Ix.Kernel.ConstantInfo.ctorInfo x.1 x.2.1 x.2.2) ++
        recs.toList.map (fun x => Ix.Kernel.ConstantInfo.recInfo x.1
          (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
          (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2) →
      (Ix.Kernel.Declaration.indDecl block nPd).names =
        types.toList.map (·.1.name) ++ ctors.toList.map (·.1.name) ++ recs.toList.map (·.1.name) := by
    intro block hb
    subst hb
    simp only [Ix.Kernel.Declaration.names, List.map_append, List.map_map]
    rfl
  replace h := LowerDistinct.lowerInductiveDecls_of_ok h
  unfold lowerInductiveDecls at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases ite_ok h with h | h
    all_goals first
      | (obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h)
      | skip
    all_goals
      rcases ite_ok h with h | h
      · split at h
        · simp [declined, throw, throwThe, MonadExceptOf.throw] at h
        · rename_i gen _
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨gen, _, by simp, rfl, names _ rfl⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨[], _, rfl, rfl, names _ rfl⟩


/-- A failing reader step accepts nothing. -/
theorem fail_bind {α β : Type} {e : ReadError} {f : α → ReadM β} {r : β}
    (h : ((throw e : ReadM α) >>= f) = .ok r) : False := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- **A reader loop that only pushes `P`-elements** (onto the part of its state
`get` reads) ends with only `P`-elements there, from a start that has only
`P`-elements. -/
theorem forIn_pushes {α σ β : Type} (get : σ → Array β) (P : β → Prop) (xs : Array α)
    (f : α → σ → ReadM (ForInStep σ))
    (step : ∀ x ∈ xs.toList, ∀ s r, f x s = .ok r → ∃ s', r = .yield s' ∧ ∀ e ∈ get s', e ∈ get s ∨ P e)
    {s res : σ} (start : ∀ e ∈ get s, P e) (ran : forIn xs s f = .ok res) : ∀ e ∈ get res, P e :=
  Ix.CompileCert.Loop.forIn_inv_array (fun _ s => ∀ e ∈ get s, P e) f xs
    (fun pre x post s r split hI hf => by
      have hx : x ∈ xs.toList := by rw [← split]; simp
      obtain ⟨s', rfl, pushed⟩ := step x hx s r hf
      exact ⟨s', rfl, fun e he => (pushed e he).elim (hI e) id⟩)
    start ran

/-- A member-key element: its name is the reader's key of a reference `R` allows. -/
def KeyedBy (cx : Ctx md) (R : ConstRef Address → Prop) {β : Type} (name : β → CName md) (e : β) : Prop :=
  ∃ ref, R ref ∧ cx.memberKey ref = .ok (name e)


/-- A failing reader step fails. -/
theorem throw_ok {α : Type} {e : ReadError} {r : α} (h : (throw e : ReadM α) = .ok r) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **An inductive block's lowering, per record**: the modeller's records (as
many as `generated` says), then one declaration every name of which is a
member key of the block: a type's (`.member owner i`) or a constructor's
(`.ctor owner i j`) read by `readInductive`'s first two loops, or a recursor
the block's shape indexes, read by its third. -/
theorem readInductive_lowering {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {r : Read md} (h : readInductive cx st owner c ms = .ok r) :
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧
      ∀ k ∈ d.names, MemberKeyOf cx owner k := by
  unfold readInductive at h
  split at h
  · rename_i shape hshape
    dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · rename_i first _
        rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · rcases ite_ok h with h | h
          · obtain ⟨types, htypes, h⟩ := except_bind_ok.mp h
            have tk := forIn_pushes (fun s => s) (KeyedBy cx (fun ref => ref.block = owner) (·.1.name)) _ _
              (fun x _ s r hf => by
                obtain ⟨k, hk, hf⟩ := except_bind_ok.mp hf
                obtain ⟨_, -, hf⟩ := except_bind_ok.mp hf
                simp only [pure, Except.pure, Except.ok.injEq] at hf
                subst hf
                refine ⟨_, rfl, fun e he => ?_⟩
                rcases Array.mem_push.mp he with he | rfl
                · exact .inl he
                · exact .inr ⟨_, rfl, hk⟩)
              (fun e he => by simp at he) htypes
            obtain ⟨cs, hcs, h⟩ := except_bind_ok.mp h
            have ck := forIn_pushes (fun s => s.1) (KeyedBy cx (fun ref => ref.block = owner) (·.1.name)) _ _
              (fun x _ s r hf => by
                obtain ⟨s1, hs1, hf⟩ := except_bind_ok.mp hf
                simp only [pure, Except.pure, Except.ok.injEq] at hf
                subst hf
                refine ⟨_, rfl, ?_⟩
                refine forIn_pushes (fun s => s.1)
                  (fun e => e ∈ s.1 ∨ KeyedBy cx (fun ref => ref.block = owner) (·.1.name) e) _ _
                  (fun y _ t q hq => ?_) (fun e he => .inl he) hs1
                rcases ite_ok hq with hq | hq
                · rcases ite_ok hq with hq | hq
                  · exact (fail_bind hq).elim
                  · obtain ⟨k, hk, hq⟩ := except_bind_ok.mp hq
                    obtain ⟨_, -, hq⟩ := except_bind_ok.mp hq
                    rcases ite_ok hq with hq | hq
                    · simp only [pure, Except.pure, Except.ok.injEq] at hq
                      subst hq
                      refine ⟨_, rfl, fun e he => ?_⟩
                      rcases Array.mem_push.mp he with he | rfl
                      · exact .inl he
                      · exact .inr (.inr ⟨_, rfl, hk⟩)
                    · exact (fail_bind hq).elim
                · exact (fail_bind hq).elim)
              (fun e he => by simp at he) hcs
            obtain ⟨recs, hrecs, h⟩ := except_bind_ok.mp h
            have rk := forIn_pushes (fun s => s) (KeyedBy cx (· ∈ shape.recs) (·.1.name)) _ _
              (fun x hx s r hf => by
                split at hf
                · split at hf
                  · split at hf
                    · split at hf
                      · rcases ite_ok hf with hf | hf
                        · exact (fail_bind hf).elim
                        · obtain ⟨key, hkey, hf⟩ := except_bind_ok.mp hf
                          obtain ⟨_, -, hf⟩ := except_bind_ok.mp hf
                          split at hf
                          · rcases ite_ok hf with hf | hf
                            · split at hf
                              · obtain ⟨_, -, hf⟩ := except_bind_ok.mp hf
                                simp only [pure, Except.pure, Except.ok.injEq] at hf
                                subst hf
                                refine ⟨_, rfl, fun e he => ?_⟩
                                rcases Array.mem_push.mp he with he | rfl
                                · exact .inl he
                                · exact .inr ⟨_, Array.mem_def.mpr hx, hkey⟩
                              · exact (fail_bind hf).elim
                            · exact (fail_bind hf).elim
                          · exact (fail_bind hf).elim
                      · exact (throw_ok hf).elim
                    · exact (throw_ok hf).elim
                  · exact (throw_ok hf).elim
                · exact (throw_ok hf).elim)
              (fun e he => by simp at he) hrecs
            obtain ⟨gens, d, hd, hg, hnames⟩ := lowerInductive_decls h
            refine ⟨gens, d, hd, hg, fun k hk => ?_⟩
            rw [hnames] at hk
            simp only [List.mem_append, List.mem_map] at hk
            rcases hk with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
            · obtain ⟨ref, hb, hk⟩ := tk e (Array.mem_def.mpr he)
              exact ⟨ref, .inl hb, hk⟩
            · obtain ⟨ref, hb, hk⟩ := ck e (Array.mem_def.mpr he)
              exact ⟨ref, .inl hb, hk⟩
            · obtain ⟨ref, hb, hk⟩ := rk e (Array.mem_def.mpr he)
              exact ⟨ref, .inr ⟨shape, hshape, hb⟩, hk⟩
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim


/-! ## Each record's lowering -/

/-- **One lowering's shape, over the keys `K` its unit may declare**: no
generated records, and every declaration names only `K`-keys (a definition,
axiom or quotient record's one declaration, a definition block's one per
member, or nothing); or the modeller's records, as many as `generated` says,
then one declaration naming only `K`-keys (an inductive block). -/
def LoweringBy (K : CName md → Prop) (r : Read md) : Prop :=
  (r.generated = 0 ∧ ∀ d ∈ r.decls.toList, ∀ k ∈ d.names, K k) ∨
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧ ∀ k ∈ d.names, K k

/-- **One record's lowering**: its keys are the record's member keys. -/
abbrev Lowering (cx : Ctx md) (owner : Address) : Read md → Prop :=
  LoweringBy (MemberKeyOf cx owner)

theorem LoweringBy.empty {K : CName md → Prop} : LoweringBy K ({} : Read md) :=
  .inl ⟨rfl, fun d hd => by simp at hd⟩

/-- A declaration naming exactly the key of member `i` names only member keys. -/
theorem member_names {cx : Ctx md} {owner : Address} {i : Nat} {k : CName md} {d : CDecl md}
    (hk : cx.memberKey (.member owner i) = .ok k) (hn : d.names = [k]) :
    ∀ k' ∈ d.names, MemberKeyOf cx owner k' := by
  intro k' hk'
  rw [hn, List.mem_singleton] at hk'
  subst hk'
  exact ⟨_, .inl rfl, hk⟩

/-- **Every record's lowering has its shape**, whatever the record. -/
theorem readRecord_lowering {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {r : Read md} (h : readRecord cx st owner c = .ok r) : Lowering cx owner r := by
  unfold readRecord at h
  split at h
  case h_1 | h_2 | h_3 | h_4 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact LoweringBy.empty
  case h_5 =>
    obtain ⟨⟨decl, rw⟩, hd, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨k, hk, hn⟩ := readDefinition_key hd
    refine .inl ⟨rfl, fun d hd' => ?_⟩
    simp at hd'
    subst hd'
    exact member_names hk hn
  case h_6 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact LoweringBy.empty
    · exact (fail_bind h).elim
  case h_7 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · obtain ⟨k, hk, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine .inl ⟨rfl, fun d hd' => ?_⟩
      simp at hd'
      subst hd'
      exact member_names hk rfl
  case h_8 =>
    obtain ⟨k, hk, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine .inl ⟨rfl, fun d hd' => ?_⟩
    simp at hd'
    subst hd'
    exact member_names hk rfl
  case h_9 =>
    dsimp only at h
    rcases ite_ok h with h | h
    · rcases ite_ok h with h | h
      · exact (fail_bind h).elim
      · obtain ⟨gens, d, hd, hg, hk⟩ := readInductive_lowering h
        exact .inr ⟨gens, d, hd, hg, hk⟩
    · rcases ite_ok h with h | h
      · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact LoweringBy.empty
      · rcases ite_ok h with h | h
        · split at h
          · exact (fail_bind h).elim
          · split at h
            · obtain ⟨s, hs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have keyed := forIn_pushes (fun s => s.2.1)
                (fun d => ∀ k ∈ d.names, MemberKeyOf cx owner k) _ _
                (fun i _ s q hq => by
                  obtain ⟨⟨decl, rw⟩, hd, hq⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hq
                  obtain ⟨k, hk, hn⟩ := readDefinition_key hd
                  dsimp only at hq
                  split at hq <;> split at hq <;>
                  · simp only [pure, Except.pure, Except.ok.injEq] at hq
                    subst hq
                    refine ⟨_, rfl, fun e he => ?_⟩
                    rcases Array.mem_push.mp he with he | rfl
                    · exact .inl he
                    · exact .inr (member_names hk hn))
                (fun e he => by simp at he) hs
              exact .inl ⟨rfl, fun d hd => keyed d (Array.mem_def.mpr hd)⟩
            · exact (throw_ok h).elim
        · exact (throw_ok h).elim

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hRS _ _ h) (forall₂_imp hRS t)

/-- **The lowering shape over the stream**: the stream `readRecords` decodes is its records'
lowerings concatenated, one per record, in order, each with `Lowering`'s
shape at its record's address. -/
theorem readRecords_units {cx : Ctx md} {st st' : State md} {records : Array (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : readRecords cx st records = .ok (st', out)) :
    ∃ rs : List (Read md),
      List.Forall₂ (fun (x : Address × Ixon.Constant) r => Lowering cx x.1 r) records.toList rs ∧
        out.toList = (rs.map fun r => r.decls.toList).flatten := by
  obtain ⟨rs, holds, flat⟩ := readRecords_lowerings h
  exact ⟨rs, forall₂_imp (fun _ _ ⟨_, read⟩ => readRecord_lowering read) holds, flat⟩

/-! ## Member keys are never derived -/

/-- The role bindings key only roles, as `bindingsOf` builds them. -/
def RolesKeyed (cx : Ctx md) : Prop :=
  ∀ (ref : ConstRef Address) (k : CName md), cx.roles.names[ref]? = some k → ∃ ro, k = Ix.Kernel.Key.role ro

theorem foldl_inv {α β : Type} (I : β → Prop) (f : β → α → β) (step : ∀ b a, I b → I (f b a)) :
    ∀ (l : List α) (b : β), I b → I (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_inv I f step l (f b a) (step b a hb)

/-- **`bindingsOf` keys only roles.** -/
theorem bindingsOf_keyed (store : Store) (t : Ix.Kernel.RoleTable) :
    ∀ (ref : ConstRef Address) (k : CName md), (bindingsOf (md := md) store t).names[ref]? = some k →
      ∃ ro, k = Ix.Kernel.Key.role ro := by
  unfold bindingsOf
  dsimp only
  rw [← Array.foldl_toList]
  refine foldl_inv (fun (m : Std.HashMap (ConstRef Address) (CName md)) =>
    ∀ ref k, m[ref]? = some k → ∃ ro, k = Ix.Kernel.Key.role ro) _ ?_ _ _ (by simp)
  intro m ⟨ro, a⟩ hm
  dsimp only
  split
  · split
    · exact hm
    · intro ref k hk
      rw [Std.HashMap.getElem?_insert] at hk
      split at hk
      · cases hk
        exact ⟨ro, rfl⟩
      · exact hm ref k hk
  · exact hm

/-- The reader's context keys only roles by its table. -/
theorem contextWith_keyed (store : Store) (blob : Address → Option ByteArray) (t : Ix.Kernel.RoleTable)
    (records : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint)
    (reconstruct : ConstRef Address → Option Address) :
    RolesKeyed (contextWith (md := md) store blob t records hint reconstruct) :=
  bindingsOf_keyed store t

/-- **A member key is a role key or an input key**, never a derived one. -/
theorem memberKey_role_or_id {cx : Ctx md} (hr : RolesKeyed cx) {ref : ConstRef Address} {k : CName md}
    (h : cx.memberKey ref = .ok k) : (∃ ro, k = Ix.Kernel.Key.role ro) ∨ ∃ i, k = Ix.Kernel.Key.id i := by
  unfold Ctx.memberKey at h
  cases hn : cx.roles.names[ref]? with
  | some k' =>
    simp only [hn, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .inl (hr _ _ hn)
  | none =>
    simp only [hn] at h
    obtain ⟨a, -, h⟩ := except_bind_ok.mp h
    cases hb : cx.keys.byAddress[a]? with
    | some k' =>
      simp only [hb, pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hs := cx.keys.byAddress_sound a _ hb
      unfold keyOfAddress at hs
      cases hres : resolve cx.store a with
      | none => simp [hres] at hs
      | some r' =>
        cases hrn : cx.roles.names[r']? with
        | some k'' =>
          simp [hres, hrn] at hs
          subst hs
          exact .inl (hr _ _ hrn)
        | none =>
          simp [hres, hrn] at hs
          obtain ⟨i, -, rfl⟩ := hs
          exact .inr ⟨i, rfl⟩
    | none =>
      cases hi : Mode.addressId? md a with
      | some i =>
        simp only [hb, hi, pure, Except.pure, Except.ok.injEq] at h
        exact .inr ⟨i, h.symm⟩
      | none => simp [hb, hi, declined, throw, throwThe, MonadExceptOf.throw] at h

theorem MemberKeyOf.role_or_id {cx : Ctx md} (hr : RolesKeyed cx) {owner : Address} {k : CName md}
    (h : MemberKeyOf cx owner k) : (∃ ro, k = Ix.Kernel.Key.role ro) ∨ ∃ i, k = Ix.Kernel.Key.id i :=
  let ⟨_, _, hk⟩ := h
  memberKey_role_or_id hr hk

/-- A declaration naming no derived key is not generated. -/
theorem isGenerated_false {d : CDecl md} (h : ∀ k ∈ d.names, Ix.Kernel.Key.isAux k = false) :
    Ix.Kernel.Declaration.isGenerated d = false := by
  unfold Ix.Kernel.Declaration.isGenerated
  cases hn : d.names with
  | nil => rfl
  | cons k ks => simp [h k (by simp [hn])]

/-- A member key is not derived. -/
theorem MemberKeyOf.not_derived {cx : Ctx md} (hr : RolesKeyed cx) {owner : Address} {k : CName md}
    (h : MemberKeyOf cx owner k) : Ix.Kernel.Key.isAux k = false := by
  rcases h.role_or_id hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- **Each lowering is empty or ends in a declaration that is not generated**,
whose names are `K`-keys, when no `K`-key is derived (what IxC's units need
of a record or a group). -/
theorem LoweringBy.closed {K : CName md → Prop} (hK : ∀ k, K k → Ix.Kernel.Key.isAux k = false) {r : Read md}
    (h : LoweringBy K r) :
    r.decls.toList = [] ∨ ∃ ds d, r.decls.toList = ds ++ [d] ∧ Ix.Kernel.Declaration.isGenerated d = false ∧
      ∀ k ∈ d.names, K k := by
  rcases h with ⟨-, hall⟩ | ⟨gens, d, hd, -, hk⟩
  · rcases List.eq_nil_or_concat r.decls.toList with he | ⟨ds, d, hd⟩
    · exact .inl he
    · rw [List.concat_eq_append] at hd
      have hk := hall d (by simp [hd])
      exact .inr ⟨ds, d, hd, isGenerated_false fun k h => hK k (hk k h), hk⟩
  · exact .inr ⟨gens, d, hd, isGenerated_false fun k h => hK k (hk k h), hk⟩

/-- `LoweringBy.closed` for a record, under `RolesKeyed`. -/
theorem Lowering.closed {cx : Ctx md} (hr : RolesKeyed cx) {owner : Address} {r : Read md}
    (h : Lowering cx owner r) :
    r.decls.toList = [] ∨ ∃ ds d, r.decls.toList = ds ++ [d] ∧ Ix.Kernel.Declaration.isGenerated d = false ∧
      ∀ k ∈ d.names, MemberKeyOf cx owner k :=
  LoweringBy.closed (fun _ h => h.not_derived hr) h

/-- Mapping the declarations by a function that keeps their names keeps the
shape (the ingress's `canonDecl`). -/
theorem LoweringBy.map {K : CName md → Prop} {f : CDecl md → CDecl md} (hf : ∀ d, (f d).names = d.names)
    {r : Read md} (h : LoweringBy K r) : LoweringBy K { r with decls := r.decls.map f } := by
  rcases h with ⟨hg, hall⟩ | ⟨gens, d, hd, hg, hk⟩
  · refine .inl ⟨hg, fun d' hd' => ?_⟩
    simp only [Array.toList_map, List.mem_map] at hd'
    obtain ⟨d, hd, rfl⟩ := hd'
    rw [hf]
    exact hall d hd
  · refine .inr ⟨gens.map f, f d, ?_, by simp [hg], fun k hk' => hk k (by rwa [hf] at hk')⟩
    simp [hd]

/-- An invariant of an `Id` loop over `[:n]` holds of its result, so of what
follows it. -/
theorem forIn_range_value_inv {σ ρ : Type} (I : σ → Prop) (Q : ρ → Prop) {n : Nat} {s0 : σ}
    {F : Nat → σ → Id (ForInStep σ)} {K : σ → Id ρ}
    (step : ∀ x < n, ∀ t, I t → I (F x t).value) (start : I s0) (conc : ∀ u, I u → Q (K u)) :
    Q (forIn (m := Id) [:n] s0 F >>= K) := by
  refine conc _ ?_
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have loop : ∀ (l : List Nat) (s : σ), (∀ x ∈ l, x < n) → I s → I (forIn (m := Id) l s F) := by
    intro l
    induction l with
    | nil => intro s _ hs; exact hs
    | cons x l ih =>
      intro s hl hs
      rw [List.forIn_cons]
      have hx := step x (hl x List.mem_cons_self) s hs
      generalize F x s = v at hx ⊢
      cases v with
      | done b => exact hx
      | yield b => exact ih b (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hx
  exact loop _ _ (fun x hx => by simp [Std.Legacy.Range.size] at hx; omega) start

/-- `defOrder`'s outer loop invariant: every index pushed, and every index of
an early result, is a member's. -/
def OrderInv (deps : Array (Std.HashSet Nat)) (u : Option (Option (Array Nat)) × Array Bool × Array Nat) : Prop :=
  (∀ i ∈ u.2.2, i < deps.size) ∧ ∀ o, u.1 = some (some o) → ∀ i ∈ o, i < deps.size

/-- **`defOrder` orders the block's members**: every index it returns is a
member's. -/
theorem defOrder_lt {deps : Array (Std.HashSet Nat)} {out : Array Nat} (h : defOrder deps = some out) :
    ∀ i ∈ out, i < deps.size := by
  unfold defOrder at h
  revert h
  apply forIn_range_value_inv (OrderInv deps)
    (fun v => v = some out → ∀ i ∈ out, i < deps.size)
  · intro x _ t ht
    apply forIn_range_value_inv (fun (u : Array Bool × Array Nat × Bool) => ∀ i ∈ u.2.1, i < deps.size)
      (fun v => OrderInv deps (ForInStep.value v))
    · intro i hi u hu
      dsimp only
      split
      · intro j hj
        rcases Array.mem_push.mp hj with hj | rfl
        · exact hu j hj
        · exact hi
      · exact hu
    · exact ht.1
    · intro u hu
      dsimp only
      split
      · exact ⟨hu, fun o ho => by cases ho; exact hu⟩
      · split
        · exact ⟨hu, fun o ho => by cases ho⟩
        · exact ⟨hu, fun o ho => by cases ho⟩
  · exact ⟨fun i hi => by simp at hi, fun o ho => by cases ho⟩
  · intro u hu
    dsimp only
    split
    · rename_i r hr
      intro hro
      cases hro
      exact hu.2 out hr
    · intro hro
      split at hro
      · cases hro
        exact hu.1
      · cases hro


/-! ## The ingress side

The Source ingress lowers each declaration group of the environment through
the same back half (`LeanIngress.lower`: `lowerInductive`, `lowerDefinition`),
so its lowerings have the same shape, over the group's keys: the ingress keys
of the group's constants (`GroupKeyOf`). -/

open Ix.LeanIngress in
/-- A key of group `gr`: the ingress key of one of its constants. -/
def GroupKeyOf (gr : Ix.LeanIngress.Group) (k : CName .source) : Prop :=
  ∃ n ∈ gr.names, k = Ix.LeanIngress.ingressKey n

open Ix.LeanIngress in
/-- The keys a converted group's lowering may declare are `K`-keys. -/
def ConvertedKeys (K : CName .source → Prop) : Converted → Prop
  | .inductive rb => (∀ e ∈ rb.types, K e.1.name) ∧ (∀ e ∈ rb.ctors, K e.1.name) ∧ ∀ e ∈ rb.recs, K e.1.name
  | .definitions ms => ∀ m ∈ ms, K m.cv.name
  | .axiom cv => K cv.name
  | .quot _ cv => K cv.name

open Ix.LeanIngress in
/-- **A converted inductive block's entries carry the group's keys**: each
type's, constructor's and recursor's name is the ingress key of the source
constant it was read from. -/
theorem convertInductive_keys {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Converted} (ran : convertInductive types ctors recs = .ok conv) :
    ∃ rb : BlockRead .source, conv = .inductive rb ∧
      (∀ e ∈ rb.types, ∃ v ∈ types, e.1.name = ingressKey v.cnst.name) ∧
      (∀ e ∈ rb.ctors, ∃ cs ∈ ctors, ∃ c ∈ cs, e.1.name = ingressKey c.cnst.name) ∧
      (∀ e ∈ rb.recs, ∃ r ∈ recs, e.1.name = ingressKey r.cnst.name) := by
  unfold convertInductive at ran
  split at ran
  · simp only at ran
    split at ran
    · cases ran
    · split at ran
      · obtain ⟨ks, -, rest⟩ := except_bind_ok.mp ran
        obtain ⟨s₁, typesLoop, rest⟩ := except_bind_ok.mp rest
        obtain ⟨s₂, ctorsLoop, rest⟩ := except_bind_ok.mp rest
        obtain ⟨s₃, recsLoop, rest⟩ := except_bind_ok.mp rest
        simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        have tk := forIn_pushes (fun s => s.2) (fun e => ∃ v ∈ types, e.1.name = ingressKey v.cnst.name) _ _
          (fun v hv s r hf => by
            simp only [pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            refine ⟨_, rfl, fun e he => ?_⟩
            rcases Array.mem_push.mp he with he | rfl
            · exact .inl he
            · exact .inr ⟨v, Array.mem_def.mpr hv, rfl⟩)
          (fun e he => by simp at he) typesLoop
        have ck := forIn_pushes (fun s => s.2.1)
          (fun e => ∃ cs ∈ ctors, ∃ c ∈ cs, e.1.name = ingressKey c.cnst.name) _ _
          (fun cs hcs s r hf => by
            obtain ⟨s1, hs1, hf⟩ := except_bind_ok.mp hf
            simp only [pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            refine ⟨_, rfl, ?_⟩
            refine forIn_pushes (fun s => s.2.1)
              (fun e => e ∈ s.2.1 ∨ ∃ cs ∈ ctors, ∃ c ∈ cs, e.1.name = ingressKey c.cnst.name) _ _
              (fun c hc t q hq => ?_) (fun e he => .inl he) hs1
            split at hq
            · simp only [pure, Except.pure, Except.ok.injEq] at hq
              subst hq
              refine ⟨_, rfl, fun e he => ?_⟩
              rcases Array.mem_push.mp he with he | rfl
              · exact .inl he
              · exact .inr (.inr ⟨cs, Array.mem_def.mpr hcs, c, Array.mem_def.mpr hc, rfl⟩)
            · cases hq)
          (fun e he => by simp at he) ctorsLoop
        have rk := forIn_pushes (fun s => s.2) (fun e => ∃ r ∈ recs, e.1.name = ingressKey r.cnst.name) _ _
          (fun r hr s q hq => by
            obtain ⟨s1, -, hq⟩ := except_bind_ok.mp hq
            simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst hq
            refine ⟨_, rfl, fun e he => ?_⟩
            rcases Array.mem_push.mp he with he | rfl
            · exact .inl he
            · exact .inr ⟨r, Array.mem_def.mpr hr, rfl⟩)
          (fun e he => by simp at he) recsLoop
        exact ⟨_, rfl, tk, ck, rk⟩
      · cases ran
  · cases ran

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons (a := a) h t, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, r⟩ := forall₂_mem_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem getElem!_mem {α : Type} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i]! ∈ xs := by
  rw [getElem!_pos xs i h]
  exact Array.getElem_mem h

/-- An `Except` `mapM` over an array, run to success, relates the arrays
elementwise. -/
theorem array_mapM_ok {α β ε : Type} {f : α → Except ε β} {xs : Array α} {ys : Array β}
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    simpa using Ix.CompileCert.Loop.mapM_forall₂ f hl

open Ix.LeanIngress in
/-- **A converted definition group's members carry the group's keys**: each
member's name is the ingress key of one of the group's constants (the block
order `defOrder` returns names only members, `defOrder_lt`). -/
theorem convertDefinitions_keys {members : Array Ix.ConstantInfo} {conv : Converted}
    (ran : convertDefinitions members = .ok conv) :
    ∃ ms : Array DefMember, conv = .definitions ms ∧
      ∀ m ∈ ms, ∃ ci ∈ members, m.cv.name = ingressKey ci.getCnst.name := by
  unfold convertDefinitions at ran
  obtain ⟨shapes, hshapes, ran⟩ := except_bind_ok.mp ran
  have shapesOf : ∀ x ∈ shapes, x.1 ∈ members := by
    intro x hx
    obtain ⟨ci, hci, hf⟩ := forall₂_mem_right (array_mapM_ok hshapes) x (Array.mem_toList_iff.mpr hx)
    split at hf
    · simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      exact Array.mem_toList_iff.mp hci
    · cases hf
  dsimp only at ran
  rcases ite_ok ran with ran | ran <;> try (split at ran; exact (fail_bind ran).elim)
  all_goals
    obtain ⟨ks, -, ran⟩ := except_bind_ok.mp ran
    rcases ite_ok ran with ran | ran
    · simp only [pure, Except.pure, Except.ok.injEq] at ran
      subst ran
      refine ⟨_, rfl, fun m hm => ?_⟩
      obtain ⟨⟨⟨ci, ⟨kind, safety, hint⟩, v⟩, j⟩, hx, rfl⟩ := Array.mem_map.mp hm
      exact ⟨ci, shapesOf _ (Array.fst_mem_of_mem_zipIdx hx), rfl⟩
    · split at ran
      · rename_i order horder
        simp only [pure, Except.pure, Except.ok.injEq] at ran
        subst ran
        refine ⟨_, rfl, fun m hm => ?_⟩
        obtain ⟨i, hi, rfl⟩ := Array.mem_map.mp hm
        have hlt := defOrder_lt horder i hi
        rw [Array.size_map] at hlt
        obtain ⟨⟨⟨ci, ⟨kind, safety, hint⟩, v⟩, j⟩, hx, he⟩ := Array.mem_map.mp (getElem!_mem hlt)
        rw [← he]
        exact ⟨ci, shapesOf _ (Array.fst_mem_of_mem_zipIdx hx), rfl⟩
      · cases ran

open Ix.LeanIngress in
/-- **A group's conversion carries the group's keys.** -/
theorem convert_keys {gr : Group} {c : Converted} (h : convert gr = .ok c) :
    ConvertedKeys (GroupKeyOf gr) c := by
  cases gr with
  | «inductive» types ctors recs =>
    obtain ⟨rb, rfl, tk, ck, rk⟩ := convertInductive_keys h
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨v, hv, hn⟩ := tk e he
      exact ⟨_, Array.mem_append_left _ (Array.mem_append_left _ (Array.mem_map_of_mem hv)), hn⟩
    · obtain ⟨cs, hcs, c, hc, hn⟩ := ck e he
      exact ⟨_, Array.mem_append_left _ (Array.mem_append_right _
        (Array.mem_flatMap.mpr ⟨cs, hcs, Array.mem_map_of_mem hc⟩)), hn⟩
    · obtain ⟨r, hr, hn⟩ := rk e he
      exact ⟨_, Array.mem_append_right _ (Array.mem_map_of_mem hr), hn⟩
  | definitions members =>
    obtain ⟨ms, rfl, hk⟩ := convertDefinitions_keys h
    intro m hm
    obtain ⟨ci, hci, hn⟩ := hk m hm
    exact ⟨_, Array.mem_map_of_mem hci, hn⟩
  | «axiom» v =>
    unfold convert at h
    dsimp only at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · obtain ⟨ks, -, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨_, by simp [Group.names], rfl⟩
  | quot v =>
    unfold convert at h
    obtain ⟨ks, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨_, by simp [Group.names], rfl⟩
  | invalid _ e => cases h

open Ix.LeanIngress in
/-- **A converted group's lowering has `LoweringBy`'s shape over its keys**:
an inductive block's through `lowerInductive_decls`, a definition group's one
declaration per member (`lowerDefinition_names`), an axiom's or quotient's
one. -/
theorem lower_lowering {K : CName .source → Prop} {st : State .source} {c : Converted} {r : Read .source}
    (hk : ConvertedKeys K c) (h : lower st c = .ok r) : LoweringBy K r := by
  cases c with
  | «inductive» rb =>
    obtain ⟨tk, ck, rk⟩ := hk
    obtain ⟨gens, d, hd, hg, hn⟩ := lowerInductive_decls h
    refine .inr ⟨gens, d, hd, hg, fun k hk' => ?_⟩
    rw [hn] at hk'
    simp only [List.mem_append, List.mem_map] at hk'
    rcases hk' with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact tk e (Array.mem_def.mpr he)
    · exact ck e (Array.mem_def.mpr he)
    · exact rk e (Array.mem_def.mpr he)
  | definitions ms =>
    unfold lower at h
    delta Ix.LeanIngress.lower.match_6 at h
    dsimp only at h
    split at h
    · rename_i hsz
      obtain ⟨l⟩ := ms
      obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
      · cases hsz
      · simp only at h
        obtain ⟨⟨decl, rw⟩, hd, h⟩ := except_bind_ok.mp h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine .inl ⟨rfl, fun d hd' => ?_⟩
        simp at hd'
        subst hd'
        rw [lowerDefinition_names hd]
        intro k hk'
        rw [List.mem_singleton] at hk'
        subst hk'
        exact hk _ (by unfold Array.getLit; exact Array.getElem_mem _)
      · simp at hsz
    · obtain ⟨s, hs, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have keyed := forIn_pushes (fun s => s.2.1) (fun d => ∀ k ∈ d.names, K k) _ _
        (fun m hm s q hq => by
          obtain ⟨⟨decl, rw⟩, hd, hq⟩ := except_bind_ok.mp hq
          have hn := lowerDefinition_names hd
          dsimp only at hq
          split at hq <;> split at hq <;>
          · simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst hq
            refine ⟨_, rfl, fun e he => ?_⟩
            rcases Array.mem_push.mp he with he | rfl
            · exact .inl he
            · refine .inr fun k hk' => ?_
              rw [hn, List.mem_singleton] at hk'
              subst hk'
              exact hk m (Array.mem_def.mpr hm))
        (fun e he => by simp at he) hs
      exact .inl ⟨rfl, fun d hd => keyed d (Array.mem_def.mpr hd)⟩
  | «axiom» cv =>
    unfold lower at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine .inl ⟨rfl, fun d hd' => ?_⟩
    simp at hd'
    subst hd'
    intro k hk'
    rw [show Ix.Kernel.Declaration.names (.axiomDecl cv) = [cv.name] from rfl, List.mem_singleton] at hk'
    subst hk'
    exact hk
  | quot kind cv =>
    unfold lower at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine .inl ⟨rfl, fun d hd' => ?_⟩
    simp at hd'
    subst hd'
    intro k hk'
    rw [show Ix.Kernel.Declaration.names (.quotDecl kind cv) = [cv.name] from rfl, List.mem_singleton] at hk'
    subst hk'
    exact hk

open Ix.LeanIngress in
/-- `canonDecl` keeps a constant's name. -/
theorem canonInfo_name (ci : Ix.Kernel.ConstantInfo .source) : (canonInfo ci).name = ci.name := by
  cases ci <;> rfl

open Ix.LeanIngress in
/-- `canonDecl` keeps the names a declaration declares. -/
theorem canonDecl_names (d : CDecl .source) : (canonDecl d).names = d.names := by
  cases d with
  | indDecl block nP =>
    show (block.map canonInfo).map (·.name) = block.map (·.name)
    rw [List.map_map]
    exact List.map_congr_left fun ci _ => canonInfo_name ci
  | _ => rfl

theorem forall₂_map_fst {α γ β : Type} {P : α → β → Prop} :
    ∀ {l : List (α × γ)} {rs : List β}, List.Forall₂ (fun x r => P x.1 r) l rs →
      List.Forall₂ P (l.map Prod.fst) rs
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_map_fst t)

open Ix.LeanIngress in
/-- **The ingress's stream is its scheduled groups' lowerings, concatenated**
in schedule order, each a converted group's lowering from some reader state,
with canonical levels (`canonDecl`). -/
theorem lowerAll_lowerings {st : State .source} {g : Graph} {sched : Array (Nat × Except ReadError Converted)}
    {res : State .source × Array (CDecl .source)} (h : lowerAll st g sched = .ok res) :
    ∃ rs : List (Read .source),
      List.Forall₂ (fun (x : Nat × Except ReadError Converted) r => ∃ c st₀, x.2 = .ok c ∧ lower st₀ c = .ok r)
        sched.toList rs ∧
      res.2.toList = (rs.map fun r => (r.decls.map canonDecl).toList).flatten := by
  unfold lowerAll at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i r' hr
    cases h
    have inv := Ix.CompileCert.Loop.forIn_inv_array
      (fun pre (s : State .source × Array (CDecl .source)) => ∃ rs : List (Read .source),
        List.Forall₂ (fun (x : (Nat × Except ReadError Converted) × Nat) r =>
          ∃ c st₀, x.1.2 = .ok c ∧ lower st₀ c = .ok r) pre rs ∧
        s.2.toList = (rs.map fun r => (r.decls.map canonDecl).toList).flatten) _ sched.zipIdx
      (fun pre x post s q _ hI hq => by
        obtain ⟨⟨gi, c⟩, i⟩ := x
        obtain ⟨rs, hrs, hflat⟩ := hI
        cases c with
        | error e => simp [Except.mapError] at hq
        | ok conv =>
          simp only [Except.mapError] at hq
          split at hq
          · cases hq
          · rename_i rd hrd
            cases hq
            have hl : lower s.1 conv = .ok rd := by
              cases hl : lower s.1 conv with
              | error e => rw [hl] at hrd; cases hrd
              | ok v => rw [hl] at hrd; cases hrd; rfl
            refine ⟨_, rfl, rs ++ [rd],
              Ix.CompileCert.Loop.forall₂_append hrs (.cons ⟨conv, s.1, rfl, hl⟩ .nil), ?_⟩
            simp [hflat])
      ⟨[], .nil, rfl⟩ hr
    obtain ⟨rs, hrs, hflat⟩ := inv
    refine ⟨rs, ?_, hflat⟩
    have := forall₂_map_fst (P := fun (x : Nat × Except ReadError Converted) r =>
      ∃ c st₀, x.2 = .ok c ∧ lower st₀ c = .ok r) hrs
    rwa [← Array.toList_map, Array.zipIdx_map_fst] at this

open Ix.LeanIngress in
theorem graph_groups (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    (graph env blocks).groups = groupsOf env blocks := rfl

open Ix.LeanIngress in
theorem graph_converted (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    (graph env blocks).converted = (groupsOf env blocks).map convert := rfl

open Ix.LeanIngress in
/-- A scheduled group's conversion, when it succeeds, is the graph's
conversion at its index. -/
theorem scheduleOf_ok {g : Graph} {x : Nat × Except ReadError Converted} {c : Converted}
    (hx : x ∈ (scheduleOf g).toList) (hc : x.2 = .ok c) : g.converted[x.1]! = .ok c := by
  unfold scheduleOf at hx
  obtain ⟨i, -, rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp hx)
  obtain ⟨c0, hc0, rest⟩ := except_bind_ok.mp hc
  show g.converted[i]! = .ok c
  have : c0 = c := by
    dsimp only at rest
    split at rest
    · exact (fail_bind rest).elim
    · rcases ite_ok rest with rest | rest
      · simpa [pure, Except.pure] using rest
      · exact (fail_bind rest).elim
  rw [hc0, this]

open Ix.LeanIngress in
/-- The graph's conversion at an index that succeeds is a group's conversion. -/
theorem graph_converted_ok {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {i : Nat} {c : Converted}
    (h : (graph env blocks).converted[i]! = .ok c) :
    ∃ gr, (graph env blocks).groups[i]? = some gr ∧ convert gr = .ok c := by
  rw [graph_converted] at h
  rw [graph_groups]
  simp only [getElem!_def, Array.getElem?_map] at h
  cases hg : (groupsOf env blocks)[i]? with
  | none => simp [hg] at h
  | some gr => simp only [hg, Option.map_some] at h; exact ⟨gr, rfl, h⟩

open Ix.LeanIngress in
/-- **The lowering shape on the ingress side**: the Source ingress's declarations are its
scheduled groups' lowerings concatenated, in schedule order, with canonical
levels; each is the lowering of a group of the graph, with `LoweringBy`'s
shape over that group's keys. -/
theorem leanIngress_units {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {st : State .source}
    {out : Array (CDecl .source)} (h : leanIngress env blocks st = .ok out) :
    ∃ rs : List (Read .source),
      List.Forall₂ (fun (x : Nat × Except ReadError Converted) r =>
          ∃ gr, (graph env blocks).groups[x.1]? = some gr ∧
            LoweringBy (GroupKeyOf gr) { r with decls := r.decls.map canonDecl })
        (scheduleOf (graph env blocks)).toList rs ∧
      out.toList = (rs.map fun r => (r.decls.map canonDecl).toList).flatten := by
  unfold leanIngress at h
  obtain ⟨res, hres, h⟩ := except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rs, hrs, hflat⟩ := lowerAll_lowerings hres
  refine ⟨rs, ?_, hflat⟩
  have mem : ∀ {l : List (Nat × Except ReadError Converted)} {rs : List (Read .source)},
      List.Forall₂ (fun (x : Nat × Except ReadError Converted) r =>
        ∃ c st₀, x.2 = .ok c ∧ lower st₀ c = .ok r) l rs →
      (∀ x ∈ l, x ∈ (scheduleOf (graph env blocks)).toList) →
      List.Forall₂ (fun (x : Nat × Except ReadError Converted) r =>
          ∃ gr, (graph env blocks).groups[x.1]? = some gr ∧
            LoweringBy (GroupKeyOf gr) { r with decls := r.decls.map canonDecl }) l rs := by
    intro l rs hl hin
    induction hl with
    | nil => exact .nil
    | @cons x r l rs hx _ ih =>
      obtain ⟨c, st₀, hc, hlow⟩ := hx
      obtain ⟨gr, hgr, hconv⟩ := graph_converted_ok (scheduleOf_ok (hin x List.mem_cons_self) hc)
      exact .cons ⟨gr, hgr, (lower_lowering (convert_keys hconv) hlow).map canonDecl_names⟩
        (ih fun y hy => hin y (List.mem_cons_of_mem _ hy))
  exact mem hrs fun x hx => hx

open Ix.LeanIngress in
/-- An ingress key is not derived: Source mode's fixed binding gives a role key
or the name itself. -/
theorem ingressKey_not_derived (n : Ix.Name) : Ix.Kernel.Key.isAux (ingressKey n) = false := by
  unfold ingressKey Ix.Kernel.Key.ofName
  split <;> rfl

/-- A group's key is not derived. -/
theorem GroupKeyOf.not_derived {gr : Ix.LeanIngress.Group} {k : CName .source} (h : GroupKeyOf gr k) :
    Ix.Kernel.Key.isAux k = false := by
  obtain ⟨n, -, rfl⟩ := h
  exact ingressKey_not_derived n


end Ix.Cert.ReaderUnits
