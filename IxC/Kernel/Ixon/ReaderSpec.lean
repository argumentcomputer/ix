import IxC.Kernel.Ixon.Reader
import IxC.Kernel.Ingress.Records
import Std.Data.HashSet.Lemmas

/-! # What the Ixon reader produces

Facts about the executed reader (`Ix.Kernel.Reader`), proved about
its definitions as they stand. They are the reader half of the fidelity
theorem of the kernel entry (`Ix.Kernel.Admission.Theorems`): the
declarations the fold checks are the ones the records describe.

* `readRecords_spec`: an accepted stream reading is a record-by-record
  reading (`StreamRead`): every record is read by `readRecord` against the
  state the records before it left, and the output is the concatenation of
  the records' declarations, in order.
* `readRecords_nodup`: an accepted stream has no two records under one
  address (the loop's `Std.HashSet` check, through `LawfulBEq Address` in
  `Ix.Kernel.Ingress.Records`).
* `readRecord_singleton`: a singleton definition, axiom or quotient record
  contributes exactly one declaration, under the record's key
  (`Ctx.memberKey (.member owner 0)`), with the record's level parameters,
  the reading of its type (`MemberReader.read`), and for a definition or
  theorem the reading of its value, or that value's projection rewrite
  (`projRewrite`, upstream con-leche's `ExportC.projRewriteD`) where it applies
  (`SingletonRead`).
* `Ctx.keyAt_eq_ok`, `Ctx.memberKey_of_role`, `Ctx.memberKey_of_unbound`: the
  key a reference and a member are read under: its role's where the table
  binds it, otherwise the input key of the address it is keyed by.

None of this is needed for consistency: `Ix.Kernel.model_exists` holds for
every declaration array. -/

namespace Ix.Kernel.Reader

open Ix.Kernel (ConstRef)

/-! ## The stream -/

/-- The declarations `readRecords` produces, record by record: each record is
read against the state the records before it left (`State.commit`), and the
output is the records' declarations in order. -/
inductive StreamRead (cx : Ctx md) : State md → List (Address × Ixon.Constant) → State md → Array (CDecl md) → Prop where
  | nil {st : State md} : StreamRead cx st [] st #[]
  | cons {st st' : State md} {a : Address} {c : Ixon.Constant} {r : Read md}
      {rest : List (Address × Ixon.Constant)} {out : Array (CDecl md)}
      (read : readRecord cx st a c = .ok r)
      (tail : StreamRead cx (st.commit r) rest st' out) :
      StreamRead cx st ((a, c) :: rest) st' (r.decls ++ out)

/-- Every record of a stream reading was read, and its declarations are in
the output. -/
theorem StreamRead.mem {cx : Ctx md} {st st' : State md} {records : List (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : StreamRead cx st records st' out) {a : Address} {c : Ixon.Constant}
    (hm : (a, c) ∈ records) :
    ∃ st₀ r, readRecord cx st₀ a c = .ok r ∧ ∀ d ∈ r.decls, d ∈ out := by
  induction h with
  | nil => simp at hm
  | @cons st _ a' c' r rest out read _ ih =>
    rcases List.mem_cons.mp hm with same | hm
    · cases same
      exact ⟨st, r, read, fun d hd => Array.mem_append_left _ hd⟩
    · obtain ⟨st₀, r₀, h₀, hd⟩ := ih hm
      exact ⟨st₀, r₀, h₀, fun d hd' => Array.mem_append_right _ (hd d hd')⟩

/-- The loop of `readRecords`, over any body that reads one record per step. -/
theorem forIn_streamRead {cx : Ctx md}
    {f : (Address × Ixon.Constant) × Nat → Std.HashSet Address × State md × Array (CDecl md) →
      Except (ReadError × Nat) (ForInStep (Std.HashSet Address × State md × Array (CDecl md)))}
    (hf : ∀ x s res, f x s = .ok res → ∃ r, readRecord cx s.2.1 x.1.1 x.1.2 = .ok r ∧
        res = .yield (s.1.insert x.1.1, s.2.1.commit r, s.2.2 ++ r.decls)) :
    ∀ (l : List ((Address × Ixon.Constant) × Nat)) (s res), forIn l s f = .ok res →
      ∃ out', StreamRead cx s.2.1 (l.map Prod.fst) res.2.1 out' ∧ res.2.2 = s.2.2 ++ out' := by
  intro l
  induction l with
  | nil =>
    intro s res h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨#[], .nil, by simp⟩
  | cons x l ih =>
    intro s res h
    rw [List.forIn_cons] at h
    cases hx : f x s with
    | error e => simp [hx, bind, Except.bind] at h
    | ok step =>
      obtain ⟨r, hr, rfl⟩ := hf x s step hx
      simp only [hx, bind, Except.bind] at h
      obtain ⟨out', hs, ho⟩ := ih _ _ h
      refine ⟨r.decls ++ out', ?_, ?_⟩
      · obtain ⟨⟨a, c⟩, i⟩ := x
        exact .cons hr hs
      · simp [ho, Array.append_assoc]

private theorem bind_ok_pure {ε α β : Type _} {x : Except ε α} {g : α → β} {v : β}
    (h : (x >>= fun a => pure (g a)) = .ok v) : ∃ a, x = .ok a ∧ g a = v := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [bind, Except.bind, pure, Except.pure] using h⟩

/-- **The stream reading.** An accepted `readRecords` is a record-by-record
reading of the records, in their order. -/
theorem readRecords_spec {cx : Ctx md} {st st' : State md} {records : Array (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : readRecords cx st records = .ok (st', out)) :
    StreamRead cx st records.toList st' out := by
  unfold readRecords at h
  dsimp only at h
  rw [← Array.forIn_toList, Array.toList_zipIdx] at h
  obtain ⟨res, hfor, hres⟩ := bind_ok_pure h
  simp only [Prod.mk.injEq] at hres
  obtain ⟨rfl, rfl⟩ := hres
  generalize hl : records.toList.zipIdx = l at hfor
  have key := forIn_streamRead (cx := cx) ?_ l _ res hfor
  · obtain ⟨out', hs, ho⟩ := key
    have hm : l.map Prod.fst = records.toList := by
      rw [← hl]; simp
    rw [hm] at hs
    simpa [ho] using hs
  · intro x s res h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · rename_i r hr
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨r, hr, h.symm⟩
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The loop of `readRecords`, over any body that refuses a key it has seen
and records every key it accepts: the keys it ran over are distinct and new. -/
theorem forIn_nodup {β : Type}
    {f : (Address × Ixon.Constant) × Nat → Std.HashSet Address × β →
      Except (ReadError × Nat) (ForInStep (Std.HashSet Address × β))}
    (hf : ∀ x s res, f x s = .ok res →
      s.1.contains x.1.1 = false ∧ ∃ b, res = .yield (s.1.insert x.1.1, b)) :
    ∀ (l : List ((Address × Ixon.Constant) × Nat)) (s res), forIn l s f = .ok res →
      (l.map (·.1.1)).Nodup ∧ ∀ y ∈ l, s.1.contains y.1.1 = false := by
  intro l
  induction l with
  | nil => intro s res _; simp
  | cons x l ih =>
    intro s res h
    rw [List.forIn_cons] at h
    cases hx : f x s with
    | error e => simp [hx, bind, Except.bind] at h
    | ok step =>
      obtain ⟨hfresh, b, rfl⟩ := hf x s step hx
      simp only [hx, bind, Except.bind] at h
      obtain ⟨hnd, hall⟩ := ih _ _ h
      simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hall
      refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun y hy => ?_⟩
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
        exact (hall y hy).1 he.symm
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hfresh
        · exact (hall y hy).2

/-- **No duplicate records.** An accepted `readRecords` ran over records
with pairwise distinct addresses. -/
theorem readRecords_nodup {cx : Ctx md} {st st' : State md} {records : Array (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : readRecords cx st records = .ok (st', out)) :
    (records.toList.map Prod.fst).Nodup := by
  unfold readRecords at h
  dsimp only at h
  rw [← Array.forIn_toList, Array.toList_zipIdx] at h
  obtain ⟨res, hfor, _⟩ := bind_ok_pure h
  have key := forIn_nodup ?_ _ _ res hfor
  · have hm : records.toList.zipIdx.map (·.1.1) = records.toList.map Prod.fst := by
      rw [show (fun y : (Address × Ixon.Constant) × Nat => y.1.1) = Prod.fst ∘ Prod.fst from rfl,
        ← List.map_map]
      simp
    rw [← hm]
    exact key.1
  · intro x s res h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hc
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨by simpa using hc, _, h.symm⟩
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-! ## Singleton records -/

/-- The level parameters of a singleton record's member, as `readRecord`
assigns them: one per universe variable, `[0, …, lvls - 1]`. -/
def singletonLps (lvls : UInt64) : List LevelParam :=
  List.range lvls.toNat

/-- The expression reader of a singleton definition record, as `readRecord`
builds it: `recur 0` is the record itself, and universe variable `i` is the
level parameter `i` (the definition's header does not enter). -/
def definitionReader (cx : Ctx md) (owner : Address) (c : Ixon.Constant) (_d : Ixon.Definition) :
    MemberReader md :=
  .mk' cx c id
    (fun i => if i == 0 then some (cx.memberKey (.member owner 0)) else none)

/-- The expression reader of a singleton axiom or quotient record, as
`readRecord` builds it (no `recur`). -/
def headerReader (cx : Ctx md) (c : Ixon.Constant) : MemberReader md :=
  .mk' cx c id (fun _ => none)

/-- The declaration a definition record's kind makes of its header `cv`, the
reading of its value `value`, and the projection rewrite's result
`rewritten`: a definition and a theorem carry the rewritten value where the
rewrite applies, an opaque the value as read. A definition's reducibility
hint is the host's or the height rule's; it is not part of the reading. -/
inductive DefinitionDecl (cv : CVal md) (value : CExpr md) (rewritten : Option (CExpr md)) :
    Ix.DefKind → CDecl md → Prop where
  | defn (hint : Ix.Kernel.ReducibilityHint) :
      DefinitionDecl cv value rewritten .defn (.defnDecl cv (rewritten.getD value) hint)
  | thm : DefinitionDecl cv value rewritten .thm (.thmDecl cv (rewritten.getD value))
  | opaq : DefinitionDecl cv value rewritten .opaq (.opaqueDecl cv value)

/-- What `readDefinition` makes of a definition member: a declaration under
the member's key (`Ctx.memberKey`). -/
theorem readDefinition_spec {cx : Ctx md} {st : State md} {heights : CName md → Nat}
    {ref : ConstRef Address} {lps : List LevelParam} {mr : MemberReader md} {d : Ixon.Definition}
    {decl : CDecl md} {rw : Bool}
    (h : readDefinition cx st heights ref lps mr d = .ok (decl, rw)) :
    ∃ key ty value, cx.memberKey ref = .ok key ∧ mr.read d.typ = .ok ty ∧
      mr.read d.value = .ok value ∧
      DefinitionDecl ⟨key, lps, ty⟩ value (projRewrite st ⟨key, lps, ty⟩ value) d.kind decl := by
  unfold readDefinition lowerDefinition at h
  cases hk : cx.memberKey ref with
  | error e => simp [hk, bind, Except.bind] at h
  | ok key =>
    cases ht : mr.read d.typ with
    | error e => simp [hk, ht, bind, Except.bind] at h
    | ok ty =>
      cases hv : mr.read d.value with
      | error e => simp [hk, ht, hv, bind, Except.bind] at h
      | ok value =>
        refine ⟨key, ty, value, rfl, rfl, rfl, ?_⟩
        simp only [hk, ht, hv, bind, Except.bind] at h
        cases hs : safetyDeclineOf d.kind d.safety with
        | some why => simp [hs, declined, throw, throwThe, MonadExceptOf.throw] at h
        | none =>
          simp only [hs] at h
          cases hkd : d.kind <;>
            simp only [hkd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
            obtain ⟨rfl, -⟩ := h
          · exact .defn _
          · exact .opaq
          · exact .thm

/-- Con-leche's quotient kind of an Ixon quotient record. -/
def quotKind : Ix.QuotKind → Ix.Kernel.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- **The reading of a singleton record**: the declaration a `defn`, `axio`
or `quot` record contributes. It is stored under the record's key `key`
(`Ctx.memberKey (.member owner 0)`: its role's key, otherwise the input key
of its own address), with the record's level parameters and the reading of
its type; a definition or theorem also carries the reading of its value (or
its projection rewrite), an opaque its value as read. Unsafe axioms and
unsafe or partial definitions are never read (they decline). -/
inductive SingletonRead (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant) :
    CDecl md → Prop where
  | defn {d : Ixon.Definition} {key : CName md} {ty value : CExpr md} {decl : CDecl md}
      (info : c.info = .defn d)
      (keyed : cx.memberKey (.member owner 0) = .ok key)
      (type : (definitionReader cx owner c d).read d.typ = .ok ty)
      (body : (definitionReader cx owner c d).read d.value = .ok value)
      (kind : DefinitionDecl ⟨key, singletonLps d.lvls, ty⟩ value
        (projRewrite st ⟨key, singletonLps d.lvls, ty⟩ value)
        d.kind decl) :
      SingletonRead cx st owner c decl
  | axio {ax : Ixon.Axiom} {key : CName md} {ty : CExpr md}
      (info : c.info = .axio ax) (safe : ax.isUnsafe = false)
      (keyed : cx.memberKey (.member owner 0) = .ok key)
      (type : (headerReader cx c).read ax.typ = .ok ty) :
      SingletonRead cx st owner c (.axiomDecl ⟨key, singletonLps ax.lvls, ty⟩)
  | quot {q : Ixon.Quotient} {key : CName md} {ty : CExpr md}
      (info : c.info = .quot q)
      (keyed : cx.memberKey (.member owner 0) = .ok key)
      (type : (headerReader cx c).read q.typ = .ok ty) :
      SingletonRead cx st owner c
        (.quotDecl (quotKind q.kind) ⟨key, singletonLps q.lvls, ty⟩)

/-- The singleton record kinds. -/
def isSingleton : Ixon.ConstantInfo → Bool
  | .defn _ | .axio _ | .quot _ => true
  | _ => false

/-- A singleton record contributes exactly its reading. -/
theorem readRecord_singleton {cx : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    {r : Read md} (hs : isSingleton c.info = true) (h : readRecord cx st owner c = .ok r) :
    ∃ decl, SingletonRead cx st owner c decl ∧ r.decls = #[decl] := by
  unfold readRecord at h
  cases hc : c.info with
  | defn d =>
    rw [hc] at h
    dsimp only at h
    obtain ⟨⟨decl, rw⟩, hd, rfl⟩ := bind_ok_pure h
    obtain ⟨key, ty, value, hk, hty, hv, hkd⟩ := readDefinition_spec hd
    exact ⟨decl, .defn hc hk hty hv hkd, rfl⟩
  | axio ax =>
    simp only [hc] at h
    cases hu : ax.isUnsafe
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hk : cx.memberKey (.member owner 0) with
      | error e => simp [hk, bind, Except.bind] at h
      | ok key =>
        cases hty : (headerReader cx c).read ax.typ with
        | error e =>
          simp only [headerReader] at hty
          simp [hk, hty, bind, Except.bind] at h
        | ok ty =>
          simp only [headerReader] at hty
          simp only [hk, hty, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨_, .axio hc hu hk (by simpa [headerReader, singletonLps] using hty), rfl⟩
    · simp [hu, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | quot q =>
    simp only [hc] at h
    cases hk : cx.memberKey (.member owner 0) with
    | error e => simp [hk, bind, Except.bind] at h
    | ok key =>
      cases hty : (headerReader cx c).read q.typ with
      | error e =>
        simp only [headerReader] at hty
        simp [hk, hty, bind, Except.bind] at h
      | ok ty =>
        simp only [headerReader] at hty
        simp only [hk, hty, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨.quotDecl (quotKind q.kind) ⟨key, singletonLps q.lvls, ty⟩,
          .quot hc hk (by simpa [headerReader, singletonLps] using hty), ?_⟩
        obtain ⟨kind, lvls, typ⟩ := q
        cases kind <;> rfl
  | recr _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ | muts _ => simp [isSingleton, hc] at hs

/-- Every singleton record of an accepted stream is read, and its
declaration is in the output. -/
theorem StreamRead.singleton {cx : Ctx md} {st st' : State md} {records : List (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : StreamRead cx st records st' out) {owner : Address}
    {c : Ixon.Constant} (hm : (owner, c) ∈ records) (hs : isSingleton c.info = true) :
    ∃ st₀ decl, SingletonRead cx st₀ owner c decl ∧ decl ∈ out := by
  obtain ⟨st₀, r, hr, hd⟩ := h.mem hm
  obtain ⟨decl, hread, hdecls⟩ := readRecord_singleton hs hr
  exact ⟨st₀, decl, hread, hd decl (by simp [hdecls])⟩

/-! ## Keys -/

/-- **The key a reference reads as** is `keyOfAddress`: its role's key where
the role table binds the reference the address resolves to, otherwise the
input key of the address itself. The keys computed ahead (`Keys.byAddress`)
agree with it. -/
theorem Ctx.keyAt_eq_ok {cx : Ctx md} {a : Address} {k : CName md} :
    cx.keyAt a = .ok k ↔ keyOfAddress cx.store cx.roles a = some k := by
  unfold Ctx.keyAt
  cases hm : cx.keys.byAddress[a]? with
  | some k' =>
    have hs := cx.keys.byAddress_sound a k' hm
    simp only [pure, Except.pure, Except.ok.injEq, hs, Option.some.injEq]
  | none =>
    unfold keyOfAddress
    cases hr : resolve cx.store a with
    | none => simp [malformed, throw, throwThe, MonadExceptOf.throw]
    | some r =>
      cases hrole : cx.roles.names[r]? with
      | some k' => simp [hrole, pure, Except.pure, eq_comm]
      | none =>
        cases hid : Mode.addressId? md a with
        | some i => simp [hrole, pure, Except.pure, eq_comm]
        | none => simp [hrole, declined, throw, throwThe, MonadExceptOf.throw]

/-- A member reference the role table binds is keyed by its role. -/
theorem Ctx.memberKey_of_role {cx : Ctx md} {r : ConstRef Address} {k : CName md}
    (hrole : cx.roles.names[r]? = some k) : cx.memberKey r = .ok k := by
  simp [Ctx.memberKey, hrole, pure, Except.pure]

/-- A member reference the role table does not bind, with a record that
resolves to it at `a` (`Keys.address`), is keyed by the input key of `a`. -/
theorem Ctx.memberKey_of_unbound {cx : Ctx md} {r : ConstRef Address} {a : Address}
    {k : CName md} (hrole : cx.roles.names[r]? = none) (haddr : cx.keys.address[r]? = some a)
    (h : cx.memberKey r = .ok k) :
    resolve cx.store a = some r ∧ ∃ i, Mode.addressId? md a = some i ∧ k = .id i := by
  have hres := cx.keys.address_sound r a haddr
  refine ⟨hres, ?_⟩
  simp only [Ctx.memberKey, Ctx.addressOf, hrole, haddr, bind, Except.bind, pure,
    Except.pure] at h
  cases hm : cx.keys.byAddress[a]? with
  | some k' =>
    rw [hm] at h
    cases h
    have hs := cx.keys.byAddress_sound a k hm
    cases hid : Mode.addressId? md a with
    | none => simp [keyOfAddress, hres, hrole, hid] at hs
    | some i =>
      refine ⟨i, rfl, ?_⟩
      simp [keyOfAddress, hres, hrole, hid] at hs
      first | exact hs.symm | exact hs
  | none =>
    rw [hm] at h
    cases hid : Mode.addressId? md a with
    | none => simp [hid, declined, throw, throwThe, MonadExceptOf.throw] at h
    | some i => simp only [hid, Except.ok.injEq] at h; exact ⟨i, rfl, h.symm⟩

/-- The reading of a bare reference with no universe arguments: the
constant at its record address, under that address's key (`Ctx.keyAt`). -/
theorem MemberReader.read_ref {mr : MemberReader md} {i : UInt64} {a : Address}
    {k : CName md} (href : mr.ecx.src.refs[i.toNat]? = some a)
    (hkey : mr.ecx.cx.keyAt a = .ok k) :
    mr.read (.ref i #[]) = .ok (.const k []) := by
  simp [MemberReader.read, convExpr, ECx.keyAt, ECx.levels, href, hkey, bind, Except.bind,
    pure, Except.pure]

@[simp] theorem MemberReader.mk'_ecx_cx (cx : Ctx md) (src : Ixon.Constant)
    (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) : (MemberReader.mk' cx src param self).ecx.cx = cx := by
  simp only [MemberReader.mk']
  rfl

@[simp] theorem MemberReader.mk'_ecx_src (cx : Ctx md) (src : Ixon.Constant)
    (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) : (MemberReader.mk' cx src param self).ecx.src = src := by
  simp only [MemberReader.mk']
  rfl

end Ix.Kernel.Reader
