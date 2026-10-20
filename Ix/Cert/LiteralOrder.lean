import Ix.Cert.Statement

/-! # String literals after their support in the certificate's order (S1's `Closed`)

A string literal mentions the constants its expansion is spelled with
(`Ix.Kernel.strLitToConstructor`, guarded by `Ix.Kernel.strLitSupported`):
`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char` and
`Char.ofNat`. They are roles (`stringRoles`), none of them the prelude's (the
prelude installs `Eq`, `Nat`, `PUnit`, `Empty`, `False`, the quotient package, `And`
and `Bool`), so in the certificate's stream they are installed by the stream's own
records. A record's reference table does not show these edges, so B4's
`ClosureOrder` does not order them (its own docstring says so). S1's `Closed` counts
a literal's support roles as mentions (IxC, 2026-10-20), so the certificate's side
needs them ordered: **every record of the order with a string literal comes after
the stream record of every string role** (`StringSupportOrdered`), decided by
`stringSupportOrdered` (`stringSupportOrdered_iff`). A `Nat` literal's support (the
`Nat` roles) is the prelude's, at the front, and needs nothing.

A record "has a string literal" when it or its owner block (a projection's) has one
in its expressions or its sharing table (`strAt`): an over-approximation, so the
decided fact is at least as strong as one over decoded declarations. -/

namespace Ix.Cert.LiteralOrder

open Ix.Kernel (Role RoleTable)

/-- **The roles a string literal mentions** (`Ix.Kernel.strLitSupported`'s). -/
def stringRoles : List Role :=
  [.string, .stringOfList, .list, .listNil, .listCons, .char, .charOfNat]

/-- Whether an Ixon expression has a string literal. -/
def exprHasStr : Ixon.Expr → Bool
  | .str _ => true
  | .prj _ _ e => exprHasStr e
  | .app f a => exprHasStr f || exprHasStr a
  | .lam _ t b => exprHasStr t || exprHasStr b
  | .all _ _ t b => exprHasStr t || exprHasStr b
  | .letE _ t v b => exprHasStr t || exprHasStr v || exprHasStr b
  | _ => false

/-- Whether a member of a mutual block has a string literal. -/
def mutHasStr : Ixon.MutConst → Bool
  | .defn d => exprHasStr d.typ || exprHasStr d.value
  | .indc i => exprHasStr i.typ || i.ctors.any (exprHasStr ·.typ)
  | .recr r => exprHasStr r.typ || r.rules.any (exprHasStr ·.rhs)

/-- Whether a record's own constant has a string literal (a projection has no
expressions; its block holds them). -/
def infoHasStr : Ixon.ConstantInfo → Bool
  | .defn d => exprHasStr d.typ || exprHasStr d.value
  | .recr r => exprHasStr r.typ || r.rules.any (exprHasStr ·.rhs)
  | .axio a => exprHasStr a.typ
  | .quot q => exprHasStr q.typ
  | .muts ms => ms.any mutHasStr
  | _ => false

/-- Whether a record has a string literal: in its constant or its sharing table. -/
def recordHasStr (c : Ixon.Constant) : Bool :=
  infoHasStr c.info || c.sharing.any exprHasStr

/-- **Whether the record at `a` has a string literal**, itself or its owner block. -/
def strAt (ixe : Ixon.Env) (a : Address) : Bool :=
  match recordAt ixe a with
  | some c =>
    recordHasStr c ||
      match recordAt ixe (ownerOf a c) with
      | some o => recordHasStr o
      | none => false
  | none => false

/-- **The stream record that installs role `r`**: the owner of the record at the
table's address for `r`. -/
def supportOwner (ixe : Ixon.Env) (t : RoleTable) (r : Role) : Option Address := do
  let a ← t.addressOf? r
  let c ← recordAt ixe a
  pure (ownerOf a c)

/-- **String literals come after their support** in `order`: for every record of
`order` with a string literal, every string role has a stream record, and that record
is the literal's own or comes earlier in `order`. -/
def StringSupportOrdered (ixe : Ixon.Env) (t : RoleTable) (order : List Address) : Prop :=
  ∀ pre a post, order = pre ++ a :: post → strAt ixe a = true →
    ∀ r ∈ stringRoles, ∃ b, supportOwner ixe t r = some b ∧ (b = a ∨ b ∈ pre)

/-- One record's verdict: no string literal, or every support record is the record
itself or among the records before it (`seen`). -/
def recordOk (ixe : Ixon.Env) (owners : List (Option Address)) (seen : Std.HashSet Address)
    (a : Address) : Bool :=
  !strAt ixe a || owners.all fun o =>
    match o with
    | some b => b == a || seen.contains b
    | none => false

/-- The walk of `stringSupportOrdered`, the records before the current one in `seen`. -/
def orderedFrom (ixe : Ixon.Env) (owners : List (Option Address)) :
    Std.HashSet Address → List Address → Bool
  | _, [] => true
  | seen, a :: rest => recordOk ixe owners seen a && orderedFrom ixe owners (seen.insert a) rest

/-- `StringSupportOrdered`, decided. -/
def stringSupportOrdered (ixe : Ixon.Env) (t : RoleTable) (order : List Address) : Bool :=
  orderedFrom ixe (stringRoles.map (supportOwner ixe t)) {} order

theorem recordOk_iff {ixe : Ixon.Env} {owners : List (Option Address)} {seen : Std.HashSet Address}
    {a : Address} {pre : List Address} (hpre : ∀ b, seen.contains b = true ↔ b ∈ pre) :
    recordOk ixe owners seen a = true ↔
      (strAt ixe a = true → ∀ o ∈ owners, ∃ b, o = some b ∧ (b = a ∨ b ∈ pre)) := by
  unfold recordOk
  rw [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  constructor
  · rintro (h | h) hs o ho
    · rw [hs] at h; cases h
    · have := h o ho
      cases o with
      | none => cases this
      | some b =>
        refine ⟨b, rfl, ?_⟩
        rcases Bool.or_eq_true _ _ ▸ this with e | e
        · exact .inl (beq_iff_eq.mp e)
        · exact .inr ((hpre b).mp e)
  · intro h
    cases hs : strAt ixe a with
    | false => exact .inl rfl
    | true =>
      refine .inr fun o ho => ?_
      obtain ⟨b, rfl, hb⟩ := h hs o ho
      show (b == a || seen.contains b) = true
      rcases hb with e | e
      · rw [e, beq_self_eq_true, Bool.true_or]
      · rw [(hpre b).mpr e, Bool.or_true]

theorem orderedFrom_iff {ixe : Ixon.Env} {owners : List (Option Address)} :
    ∀ (l : List Address) (seen : Std.HashSet Address) (done : List Address),
      (∀ b, seen.contains b = true ↔ b ∈ done) →
      (orderedFrom ixe owners seen l = true ↔
        ∀ pre a post, l = pre ++ a :: post → strAt ixe a = true →
          ∀ o ∈ owners, ∃ b, o = some b ∧ (b = a ∨ b ∈ done ++ pre))
  | [], _, _, _ => by
    simp only [orderedFrom, true_iff]
    intro pre a post h
    cases pre <;> simp at h
  | x :: rest, seen, done, hseen => by
    have hseen' : ∀ b, (seen.insert x).contains b = true ↔ b ∈ done ++ [x] := by
      intro b
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hseen b, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro (e | e)
        · exact .inr e.symm
        · exact .inl e
      · rintro (e | e)
        · exact .inr e
        · exact .inl e.symm
    simp only [orderedFrom, Bool.and_eq_true]
    rw [recordOk_iff hseen, orderedFrom_iff rest (seen.insert x) (done ++ [x]) hseen']
    constructor
    · rintro ⟨hx, hrest⟩ pre a post h hs o ho
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨b, hb, e⟩ := hx hs o ho
        exact ⟨b, hb, by simpa using e⟩
      | cons y pre' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨b, hb, e⟩ := hrest pre' a post h hs o ho
        exact ⟨b, hb, by simpa using e⟩
    · intro h
      refine ⟨fun hs o ho => ?_, fun pre a post hl hs o ho => ?_⟩
      · obtain ⟨b, hb, e⟩ := h [] x rest rfl hs o ho
        exact ⟨b, hb, by simpa using e⟩
      · obtain ⟨b, hb, e⟩ := h (x :: pre) a post (by rw [hl]; rfl) hs o ho
        exact ⟨b, hb, by simpa using e⟩

/-- **`stringSupportOrdered` decides `StringSupportOrdered`.** -/
theorem stringSupportOrdered_iff (ixe : Ixon.Env) (t : RoleTable) (order : List Address) :
    stringSupportOrdered ixe t order = true ↔ StringSupportOrdered ixe t order := by
  unfold stringSupportOrdered StringSupportOrdered
  rw [orderedFrom_iff order {} [] (fun b => by simp)]
  constructor
  · intro h pre a post hl hs r hr
    obtain ⟨b, hb, e⟩ := h pre a post hl hs _ (List.mem_map_of_mem hr)
    exact ⟨b, hb, by simpa using e⟩
  · intro h pre a post hl hs o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    obtain ⟨b, hb, e⟩ := h pre a post hl hs r hr
    exact ⟨b, hb, by simpa using e⟩

end Ix.Cert.LiteralOrder
