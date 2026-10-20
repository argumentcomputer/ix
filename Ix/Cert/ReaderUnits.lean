import Ix.Cert.Statement
import Ix.CompileCert.Loop

/-! # Each record's lowering (S1's units, reader side; (R1))

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
  is not generated (`isGenerated`, a stand-in for IxC's until
  `IxC/Kernel/Units.lean` is on the branch).

Nothing here is about what `InModel.generate` returns: IxC's decided units
check closes each run of generated records and requires their bases among
the closing declaration's. -/

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
  unfold lowerInductive at h
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

/-- **One record's lowering (R1)**: no generated records, and every
declaration names only the record's member keys (a definition, axiom or
quotient record's one declaration, a definition block's one per member, or
nothing); or the modeller's records, as many as `generated` says, then one
declaration naming only the record's member keys (an inductive block). -/
def Lowering (cx : Ctx md) (owner : Address) (r : Read md) : Prop :=
  (r.generated = 0 ∧ ∀ d ∈ r.decls.toList, ∀ k ∈ d.names, MemberKeyOf cx owner k) ∨
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧
      ∀ k ∈ d.names, MemberKeyOf cx owner k

theorem Lowering.empty {cx : Ctx md} {owner : Address} : Lowering cx owner ({} : Read md) :=
  .inl ⟨rfl, fun d hd => by simp at hd⟩

/-- A declaration naming exactly the key of member `i` names only member keys. -/
theorem member_names {cx : Ctx md} {owner : Address} {i : Nat} {k : CName md} {d : CDecl md}
    (hk : cx.memberKey (.member owner i) = .ok k) (hn : d.names = [k]) :
    ∀ k' ∈ d.names, MemberKeyOf cx owner k' := by
  intro k' hk'
  rw [hn, List.mem_singleton] at hk'
  subst hk'
  exact ⟨_, .inl rfl, hk⟩

/-- **Every record's lowering has its shape (R1)**, whatever the record. -/
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
      exact Lowering.empty
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
      exact Lowering.empty
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
        exact Lowering.empty
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

/-- **(R1) over the stream**: the stream `readRecords` decodes is its records'
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

/-- A derived key (stand-in for IxC's `Key.isAux`, `IxC/Kernel/Units.lean`,
not yet on the branch; the same definition). -/
def isDerived : Ix.Kernel.Key md → Bool
  | .aux _ _ => true
  | _ => false

/-- A generated declaration: it declares names, all derived (stand-in for
IxC's `Declaration.isGenerated`; the same definition). -/
def isGenerated (d : CDecl md) : Bool :=
  !d.names.isEmpty && d.names.all isDerived

/-- A declaration naming only member keys is not generated. -/
theorem isGenerated_false {cx : Ctx md} (hr : RolesKeyed cx) {owner : Address} {d : CDecl md}
    (h : ∀ k ∈ d.names, MemberKeyOf cx owner k) : isGenerated d = false := by
  unfold isGenerated
  cases hn : d.names with
  | nil => rfl
  | cons k ks =>
    have hk : isDerived k = false := by
      rcases (h k (by simp [hn])).role_or_id hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    simp [hk]

/-- **Each lowering is empty or ends in a declaration that is not generated**,
whose names are the record's member keys (what IxC's units need of a record,
under `RolesKeyed`). -/
theorem Lowering.closed {cx : Ctx md} (hr : RolesKeyed cx) {owner : Address} {r : Read md}
    (h : Lowering cx owner r) :
    r.decls.toList = [] ∨ ∃ ds d, r.decls.toList = ds ++ [d] ∧ isGenerated d = false ∧
      ∀ k ∈ d.names, MemberKeyOf cx owner k := by
  rcases h with ⟨-, hall⟩ | ⟨gens, d, hd, -, hk⟩
  · rcases List.eq_nil_or_concat r.decls.toList with he | ⟨ds, d, hd⟩
    · exact .inl he
    · rw [List.concat_eq_append] at hd
      have hk := hall d (by simp [hd])
      exact .inr ⟨ds, d, hd, isGenerated_false hr hk, hk⟩
  · exact .inr ⟨gens, d, hd, isGenerated_false hr hk, hk⟩

end Ix.Cert.ReaderUnits
