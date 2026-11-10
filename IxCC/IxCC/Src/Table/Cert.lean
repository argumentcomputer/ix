import IxCC.Src.Table.Validate

/-! # The unfolding table as certificate data

The table part of the compiler's certificate (`Cert.table`): the entries `Table.build` accepted, in
the form of the proposals they came from, without anything a check re-derives.
An `eqn` entry names its theorem but not its body, a `csimp` entry its
target and theorem but not the target's levels, a `case` entry nothing but
its key, and a recursor kind only the recursor.

`Table.ofCert` rebuilds the table from such a certificate on the recheck path
(style V): every entry is produced by the entry check that justifies it
(`checkPrim`, `checkCsimp`, `checkEqn`, `checkCase`, `deriveRecKind`,
`checkLazy`, `checkInline`, the opaque-by-value allowlist), and the global
conditions of `Table.validate` are checked on the result (pinned identities,
`csimp` targets admissible and redirects acyclic). So it accepts exactly the
tables `Table.validate` accepts, up to the entries a check derives, and
never evaluates a check twice. A missing entry only degrades to the kernel
body; a wrong one is rejected with the constant it concerns.

Kernel style (D17): lists, `NatMap`s and structural recursion. -/

namespace IxCC.Src.Table

/-- A `resolve` entry as the certificate states it. -/
inductive Entry where
  | prim (op : PrimOp)
  | csimp (g thm : CId)
  | eqn (thm : CId)
  | case
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The table as certificate data, column by column. -/
structure TableCert where
  resolve : List (CId × Entry) := []
  /-- Recursors whose kind is derived. -/
  recKind : List CId := []
  lazy : List (CId × Nat) := []
  inline : List CId := []
  opaqueByValue : List CId := []
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The certificate form of a `resolve` entry. -/
def Entry.ofResolve : Resolve → Entry
  | .prim op => .prim op
  | .csimp g _ thm => .csimp g thm
  | .eqn thm _ => .eqn thm
  | .case _ => .case

/-- The certificate of a table (the producer's side). -/
def TableCert.ofTable (t : Table) : TableCert :=
  { resolve := t.resolve.toList.map fun (c, r) => (c, Entry.ofResolve r)
    recKind := t.recKind.toList.map (·.1)
    lazy := t.lazy.toList
    inline := t.inline.toList.map (·.1)
    opaqueByValue := t.opaqueByValue.toList.map (·.1) }

/-- Constants of a program of `size` constants, none named twice (`seen`
holds those passed). A loop. -/
def idsDistinct (size : Nat) : List CId → NatSet → Bool
  | [], _ => true
  | c :: rest, seen => decide (c < size) && !seen.contains c && idsDistinct size rest (seen.insert c)

/-- Each column names constants of the program, each at most once (as a
table built from maps does): so no column is longer than the program and no
entry's check runs twice. -/
def TableCert.keysOk (size : Nat) (t : TableCert) : Bool :=
  idsDistinct size (t.resolve.map (·.1)) .leaf && idsDistinct size t.recKind .leaf &&
    idsDistinct size (t.lazy.map (·.1)) .leaf && idsDistinct size t.inline .leaf &&
    idsDistinct size t.opaqueByValue .leaf

/-- The entry a certificate line names, produced by its check. -/
def entryOf (cfg : Config) (p : Program) (f : CId) : Entry → Except String Resolve
  | .prim op => do checkPrim p f op cfg.prims; pure (.prim op)
  | .csimp g thm => checkCsimp p f g thm
  | .eqn thm => checkEqn p f thm
  | .case => checkCase p f

/-- The `resolve` column (structural on the certificate's list). -/
def resolveOfCert (cfg : Config) (p : Program) :
    List (CId × Entry) → NatMap Resolve → Except String (NatMap Resolve)
  | [], m => pure m
  | (f, e) :: rest, m =>
    match entryOf cfg p f e with
    | .ok r => resolveOfCert cfg p rest (m.insert f r)
    | .error msg => .error s!"table entry of constant {f}: {msg}"

/-- The `recKind` column: each listed recursor's derived kind. -/
def recKindOfCert (p : Program) : List CId → NatMap RecKind → Except String (NatMap RecKind)
  | [], m => pure m
  | r :: rest, m =>
    match deriveRecKind p r with
    | some k => recKindOfCert p rest (m.insert r k)
    | none => .error s!"table entry of constant {r}: recKind: not a recursor"

/-- Check each listed constant and insert it (structural on the list). -/
def columnOfCert {α β : Type} (check : CId → α → Except String Unit) (val : α → β) :
    List (CId × α) → NatMap β → Except String (NatMap β)
  | [], m => pure m
  | (c, x) :: rest, m =>
    match check c x with
    | .ok () => columnOfCert check val rest (m.insert c (val x))
    | .error msg => .error s!"table entry of constant {c}: {msg}"

/-- Every `csimp` target of the rebuilt column is admissible and its
redirect chain acyclic (as `Table.validate` asks). -/
def csimpTargetsOk (p : Program) (resolve : NatMap Resolve) :
    List (CId × Resolve) → Except String Unit
  | [] => pure ()
  | (f, .csimp g _ _) :: rest =>
    if !((safeDefn? p g).isSome || (resolve.get? g).isSome) then
      .error s!"table entry of constant {f}: csimp: target not admissible"
    else if !csimpAcyclic resolve p.size f then
      .error s!"table entry of constant {f}: csimp: redirect cycle"
    else csimpTargetsOk p resolve rest
  | _ :: rest => csimpTargetsOk p resolve rest

/-- Rebuild the checked table of `p` from its certificate (the recheck
path, style V). -/
def ofCert (cfg : Config) (p : Program) (c : TableCert) : Except String Table := do
  unless Pinned.knownOk p do throw "known: a pinned constant is misidentified"
  unless c.keysOk p.size do throw "a column names a constant outside the program, or one twice"
  let resolve ← resolveOfCert cfg p c.resolve .leaf
  csimpTargetsOk p resolve resolve.toList
  let recKind ← recKindOfCert p c.recKind .leaf
  let lazy ← columnOfCert (checkLazy p) id c.lazy .leaf
  let inline ← columnOfCert (fun f (_ : Unit) => checkInline p f cfg.inlineCap) id
    (c.inline.map (·, ())) .leaf
  let opaqueByValue ← columnOfCert (validateOpaque p) id (c.opaqueByValue.map (·, ())) .leaf
  let table : Table := { resolve, recKind, lazy, inline, opaqueByValue }
  Resource.selected p table
  pure table

/-! ## Soundness of `ofCert` -/

private theorem natMap_get?_parts {α : Type} (m : NatMap α) (k : Nat) :
    m.get? k = if k == 0 then m.parts.1 else if k % 2 == 0 then m.parts.2.1.get? (k / 2)
      else m.parts.2.2.get? (k / 2) := by
  cases m with
  | leaf => simp [NatMap.get?, NatMap.parts]
  | node v z o => rfl

private theorem natMap_get?_setF {α : Type} :
    ∀ (fuel : Nat) (m : NatMap α) (k : Nat) (x : Option α) (k' : Nat),
      k < fuel → (NatMap.setF fuel m k x).get? k' = if k' = k then x else m.get? k'
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, m, k, x, k', h => by
    rw [natMap_get?_parts m k']
    unfold NatMap.setF
    obtain ⟨v, z, o⟩ := m.parts
    dsimp only
    by_cases hk : k = 0
    · subst hk
      simp only [BEq.rfl, ↓reduceIte, NatMap.get?]
      by_cases hk' : k' = 0 <;> simp [hk']
    · have hk0 : (k == 0) = false := by simpa using hk
      by_cases he : k % 2 = 0
      · have he' : (k % 2 == 0) = true := by simpa using he
        simp only [hk0, he', Bool.false_eq_true, ↓reduceIte, NatMap.get?]
        rw [natMap_get?_setF fuel z (k / 2) x (k' / 2) (by omega)]
        by_cases hk' : k' = 0
        · simp [hk', Ne.symm hk]
        · by_cases he2 : k' % 2 = 0
          · have : (k' / 2 = k / 2) ↔ k' = k := by omega
            simp [hk', he2, this]
          · have : k' ≠ k := by omega
            simp [hk', he2, this]
      · have he' : (k % 2 == 0) = false := by simpa using he
        simp only [hk0, he', Bool.false_eq_true, ↓reduceIte, NatMap.get?]
        rw [natMap_get?_setF fuel o (k / 2) x (k' / 2) (by omega)]
        by_cases hk' : k' = 0
        · simp [hk', Ne.symm hk]
        · by_cases he2 : k' % 2 = 0
          · have : k' ≠ k := by omega
            simp [hk', he2, this]
          · have : (k' / 2 = k / 2) ↔ k' = k := by omega
            simp [hk', he2, this]

private theorem natMap_get?_insert {α : Type} (m : NatMap α) (k : Nat) (x : α) (k' : Nat) :
    (m.insert k x).get? k' = if k' = k then some x else m.get? k' :=
  natMap_get?_setF (k + 1) m k (some x) k' (Nat.lt_succ_self k)

private theorem natMap_get?_insert_self {α : Type} (m : NatMap α) (k : Nat) (x : α) :
    (m.insert k x).get? k = some x := by
  simp [natMap_get?_insert]

theorem resolveOfCert_mem_ok {cfg : Config} {p : Program} :
    ∀ (entries : List (CId × Entry)) (m res : NatMap Resolve),
      resolveOfCert cfg p entries m = .ok res →
      ∀ f e, (f, e) ∈ entries → ∃ r, entryOf cfg p f e = .ok r
  | [], _, _, _, _, _, hmem => by cases hmem
  | (f₀, e₀) :: rest, m, res, h, f, e, hmem => by
    unfold resolveOfCert at h
    cases he : entryOf cfg p f₀ e₀ with
    | error _ => rw [he] at h; cases h
    | ok r₀ =>
      rw [he] at h
      dsimp only at h
      rcases List.mem_cons.1 hmem with hhead | htail
      · cases hhead
        exact ⟨r₀, he⟩
      · exact resolveOfCert_mem_ok rest (m.insert f₀ r₀) res h f e htail

theorem resolveOfCert_get?_ok {cfg : Config} {p : Program} :
    ∀ (entries : List (CId × Entry)) (m res : NatMap Resolve),
      resolveOfCert cfg p entries m = .ok res →
      ∀ c r, res.get? c = some r →
        m.get? c = some r ∨ ∃ e, (c, e) ∈ entries ∧ entryOf cfg p c e = .ok r
  | [], m, res, h, c, r, hget => by
    unfold resolveOfCert at h
    cases h
    exact Or.inl hget
  | (f₀, e₀) :: rest, m, res, h, c, r, hget => by
    unfold resolveOfCert at h
    cases he : entryOf cfg p f₀ e₀ with
    | error _ => rw [he] at h; cases h
    | ok r₀ =>
      rw [he] at h
      dsimp only at h
      rcases resolveOfCert_get?_ok rest (m.insert f₀ r₀) res h c r hget with hm | ⟨e, hmem, he'⟩
      · rw [natMap_get?_insert] at hm
        by_cases hc : c = f₀
        · subst hc
          simp only [↓reduceIte, Option.some.injEq] at hm
          subst hm
          exact Or.inr ⟨e₀, List.mem_cons_self, he⟩
        · simp only [hc, ↓reduceIte] at hm
          exact Or.inl hm
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ hmem, he'⟩

theorem recKindOfCert_preserves {p : Program} :
    ∀ (rs : List CId) (m res : NatMap RecKind) (c : CId) (rk : RecKind),
      recKindOfCert p rs m = .ok res →
      deriveRecKind p c = some rk →
      m.get? c = some rk →
      res.get? c = some rk
  | [], m, res, c, rk, h, _, hm => by
    unfold recKindOfCert at h
    cases h
    exact hm
  | r :: rest, m, res, c, rk, h, hder, hm => by
    unfold recKindOfCert at h
    cases hdr : deriveRecKind p r with
    | none => rw [hdr] at h; cases h
    | some k =>
      rw [hdr] at h
      dsimp only at h
      refine recKindOfCert_preserves rest (m.insert r k) res c rk h hder ?_
      rw [natMap_get?_insert]
      by_cases hc : c = r
      · subst hc
        rw [hder] at hdr
        cases hdr
        simp
      · simp [hc, hm]

theorem recKindOfCert_mem_ok {p : Program} :
    ∀ (rs : List CId) (m res : NatMap RecKind),
      recKindOfCert p rs m = .ok res →
      ∀ c ∈ rs, ∃ rk, deriveRecKind p c = some rk ∧ res.get? c = some rk
  | [], _, _, _, _, hmem => by cases hmem
  | r :: rest, m, res, h, c, hmem => by
    unfold recKindOfCert at h
    cases hdr : deriveRecKind p r with
    | none => rw [hdr] at h; cases h
    | some k =>
      rw [hdr] at h
      dsimp only at h
      rcases List.mem_cons.1 hmem with rfl | htail
      · refine ⟨k, hdr, recKindOfCert_preserves rest (m.insert c k) res c k h hdr ?_⟩
        exact natMap_get?_insert_self m c k
      · exact recKindOfCert_mem_ok rest (m.insert r k) res h c htail

theorem recKindOfCert_get?_ok {p : Program} :
    ∀ (rs : List CId) (m res : NatMap RecKind),
      recKindOfCert p rs m = .ok res →
      ∀ c rk, res.get? c = some rk →
        m.get? c = some rk ∨ (c ∈ rs ∧ deriveRecKind p c = some rk)
  | [], m, res, h, c, rk, hget => by
    unfold recKindOfCert at h
    cases h
    exact Or.inl hget
  | r :: rest, m, res, h, c, rk, hget => by
    unfold recKindOfCert at h
    cases hdr : deriveRecKind p r with
    | none => rw [hdr] at h; cases h
    | some k =>
      rw [hdr] at h
      dsimp only at h
      rcases recKindOfCert_get?_ok rest (m.insert r k) res h c rk hget with hm | ⟨hmem, hder⟩
      · rw [natMap_get?_insert] at hm
        by_cases hc : c = r
        · subst hc
          simp only [↓reduceIte, Option.some.injEq] at hm
          subst hm
          exact Or.inr ⟨List.mem_cons_self, hdr⟩
        · simp only [hc, ↓reduceIte] at hm
          exact Or.inl hm
      · exact Or.inr ⟨List.mem_cons_of_mem _ hmem, hder⟩

theorem columnOfCert_mem_ok {α β : Type} {check : CId → α → Except String Unit} {val : α → β} :
    ∀ (xs : List (CId × α)) (m res : NatMap β),
      columnOfCert check val xs m = .ok res →
      ∀ c x, (c, x) ∈ xs → check c x = .ok ()
  | [], _, _, _, _, _, hmem => by cases hmem
  | (c₀, x₀) :: rest, m, res, h, c, x, hmem => by
    unfold columnOfCert at h
    cases hc : check c₀ x₀ with
    | error _ => rw [hc] at h; cases h
    | ok u =>
      cases u
      rw [hc] at h
      dsimp only at h
      rcases List.mem_cons.1 hmem with hhead | htail
      · cases hhead
        exact hc
      · exact columnOfCert_mem_ok rest (m.insert c₀ (val x₀)) res h c x htail

theorem columnOfCert_get?_ok {α β : Type} {check : CId → α → Except String Unit} {val : α → β} :
    ∀ (xs : List (CId × α)) (m res : NatMap β),
      columnOfCert check val xs m = .ok res →
      ∀ c y, res.get? c = some y →
        m.get? c = some y ∨ ∃ x, (c, x) ∈ xs ∧ check c x = .ok () ∧ val x = y
  | [], m, res, h, c, y, hget => by
    unfold columnOfCert at h
    cases h
    exact Or.inl hget
  | (c₀, x₀) :: rest, m, res, h, c, y, hget => by
    unfold columnOfCert at h
    cases hc : check c₀ x₀ with
    | error _ => rw [hc] at h; cases h
    | ok u =>
      cases u
      rw [hc] at h
      dsimp only at h
      rcases columnOfCert_get?_ok rest (m.insert c₀ (val x₀)) res h c y hget with hm | ⟨x, hmem, hchk, hval⟩
      · rw [natMap_get?_insert] at hm
        by_cases hceq : c = c₀
        · subst hceq
          simp only [↓reduceIte, Option.some.injEq] at hm
          exact Or.inr ⟨x₀, List.mem_cons_self, hc, hm⟩
        · simp only [hceq, ↓reduceIte] at hm
          exact Or.inl hm
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hmem, hchk, hval⟩

theorem columnOfCert_unit_preserves {check : CId → Unit → Except String Unit} :
    ∀ (xs : List (CId × Unit)) (m res : NatMap Unit) (c : CId),
      columnOfCert check id xs m = .ok res →
      m.get? c = some () →
      res.get? c = some ()
  | [], m, res, c, h, hm => by
    unfold columnOfCert at h
    cases h
    exact hm
  | (c₀, x₀) :: rest, m, res, c, h, hm => by
    cases x₀
    unfold columnOfCert at h
    cases hc : check c₀ () with
    | error _ => rw [hc] at h; cases h
    | ok u =>
      cases u
      rw [hc] at h
      dsimp only at h
      refine columnOfCert_unit_preserves rest (m.insert c₀ ()) res c h ?_
      rw [natMap_get?_insert]
      by_cases hceq : c = c₀
      · simp [hceq]
      · simp [hceq, hm]

theorem columnOfCert_unit_mem_ok {check : CId → Unit → Except String Unit} :
    ∀ (xs : List (CId × Unit)) (m res : NatMap Unit),
      columnOfCert check id xs m = .ok res →
      ∀ c, (c, ()) ∈ xs → check c () = .ok () ∧ res.get? c = some ()
  | [], _, _, _, _, hmem => by cases hmem
  | (c₀, x₀) :: rest, m, res, h, c, hmem => by
    cases x₀
    unfold columnOfCert at h
    cases hc : check c₀ () with
    | error _ => rw [hc] at h; cases h
    | ok u =>
      cases u
      rw [hc] at h
      dsimp only at h
      rcases List.mem_cons.1 hmem with hhead | htail
      · injection hhead with hce _
        subst hce
        refine ⟨hc, columnOfCert_unit_preserves rest (m.insert c ()) res c h ?_⟩
        exact natMap_get?_insert_self m c ()
      · exact columnOfCert_unit_mem_ok rest (m.insert c₀ ()) res h c htail

theorem ofCert_ok_props {cfg : Config} {p : Program} {cert : TableCert} {t : Table}
    (h : ofCert cfg p cert = .ok t) :
    Pinned.knownOk p = true ∧
    Resource.selected p t = .ok () ∧
    (∀ f e, (f, e) ∈ cert.resolve → ∃ r, entryOf cfg p f e = .ok r) ∧
    (∀ c r, t.resolveOf c = some r → ∃ e, (c, e) ∈ cert.resolve ∧ entryOf cfg p c e = .ok r) ∧
    (∀ c ∈ cert.recKind, ∃ rk, deriveRecKind p c = some rk ∧ t.recKindOf c = some rk) ∧
    (∀ c rk, t.recKindOf c = some rk → c ∈ cert.recKind ∧ deriveRecKind p c = some rk) ∧
    (∀ p_lazy ∈ cert.lazy, checkLazy p p_lazy.1 p_lazy.2 = .ok ()) ∧
    (∀ c a, t.lazyOf c = some a → (c, a) ∈ cert.lazy ∧ checkLazy p c a = .ok ()) ∧
    (∀ c ∈ cert.inline, checkInline p c cfg.inlineCap = .ok () ∧ t.isInline c = true) ∧
    (∀ c, t.isInline c = true → c ∈ cert.inline ∧ checkInline p c cfg.inlineCap = .ok ()) ∧
    (∀ c ∈ cert.opaqueByValue, validateOpaque p c () = .ok () ∧ t.isOpaqueByValue c = true) ∧
    (∀ c, t.isOpaqueByValue c = true → c ∈ cert.opaqueByValue ∧ validateOpaque p c () = .ok ()) := by
  unfold ofCert at h
  cases hkn : Pinned.knownOk p with
  | false =>
    rw [hkn] at h
    cases h
  | true =>
    simp only [hkn, ↓reduceIte, pure, Except.pure, bind, Except.bind] at h
    have hkeys : cert.keysOk p.size = true := by
      cases hk : cert.keysOk p.size with
      | false => simp [hk] at h
      | true => rfl
    simp only [hkeys, ↓reduceIte] at h
    cases hres : resolveOfCert cfg p cert.resolve .leaf with
    | error _ => rw [hres] at h; cases h
    | ok resolve =>
      rw [hres] at h
      dsimp only at h
      cases hcs : csimpTargetsOk p resolve resolve.toList with
      | error _ => rw [hcs] at h; cases h
      | ok u =>
        cases u
        rw [hcs] at h
        dsimp only at h
        cases hrk : recKindOfCert p cert.recKind .leaf with
        | error _ => rw [hrk] at h; cases h
        | ok recKind =>
          rw [hrk] at h
          dsimp only at h
          cases hlz : columnOfCert (checkLazy p) id cert.lazy .leaf with
          | error _ => rw [hlz] at h; cases h
          | ok lazy =>
            rw [hlz] at h
            dsimp only at h
            cases hinl : columnOfCert (fun f (_ : Unit) => checkInline p f cfg.inlineCap) id
                (cert.inline.map (·, ())) .leaf with
            | error _ => rw [hinl] at h; cases h
            | ok inline =>
              rw [hinl] at h
              dsimp only at h
              cases hopq : columnOfCert (validateOpaque p) id (cert.opaqueByValue.map (·, ())) .leaf with
              | error _ => rw [hopq] at h; cases h
              | ok opaqueByValue =>
                rw [hopq] at h
                dsimp only at h
                cases hsel : Resource.selected p { resolve, recKind, lazy, inline, opaqueByValue } with
                | error _ => rw [hsel] at h; cases h
                | ok u =>
                  cases u
                  rw [hsel] at h
                  injection h with ht
                  subst ht
                  refine ⟨rfl, hsel,
                    resolveOfCert_mem_ok cert.resolve .leaf resolve hres,
                    fun c r hget => ?_,
                    recKindOfCert_mem_ok cert.recKind .leaf recKind hrk,
                    fun c rk hget => ?_,
                    fun pl hpl => columnOfCert_mem_ok cert.lazy .leaf lazy hlz pl.1 pl.2 hpl,
                    fun c a hget => ?_,
                    fun c hc => ?_,
                    fun c hget => ?_,
                    fun c hc => ?_,
                    fun c hget => ?_⟩
                  · rcases resolveOfCert_get?_ok cert.resolve .leaf resolve hres c r hget with hm | hex
                    · simp [NatMap.get?] at hm
                    · exact hex
                  · rcases recKindOfCert_get?_ok cert.recKind .leaf recKind hrk c rk hget with hm | hex
                    · simp [NatMap.get?] at hm
                    · exact hex
                  · rcases columnOfCert_get?_ok cert.lazy .leaf lazy hlz c a hget with hm | ⟨x, hmem, hchk, rfl⟩
                    · simp [NatMap.get?] at hm
                    · exact ⟨hmem, hchk⟩
                  · have hmem : (c, ()) ∈ cert.inline.map (·, ()) := List.mem_map.2 ⟨c, hc, rfl⟩
                    obtain ⟨h1, h2⟩ := columnOfCert_unit_mem_ok _ .leaf inline hinl c hmem
                    exact ⟨h1, by simp [Table.isInline, NatMap.contains, h2]⟩
                  · simp only [Table.isInline, NatMap.contains, Option.isSome_iff_exists] at hget
                    obtain ⟨u, hu⟩ := hget
                    cases u
                    rcases columnOfCert_get?_ok _ .leaf inline hinl c () hu with hm | ⟨_, hmem, hchk, _⟩
                    · simp [NatMap.get?] at hm
                    · obtain ⟨c', hc', heq⟩ := List.mem_map.1 hmem
                      cases heq
                      exact ⟨hc', hchk⟩
                  · have hmem : (c, ()) ∈ cert.opaqueByValue.map (·, ()) := List.mem_map.2 ⟨c, hc, rfl⟩
                    obtain ⟨h1, h2⟩ := columnOfCert_unit_mem_ok _ .leaf opaqueByValue hopq c hmem
                    exact ⟨h1, by simp [Table.isOpaqueByValue, NatMap.contains, h2]⟩
                  · simp only [Table.isOpaqueByValue, NatMap.contains, Option.isSome_iff_exists] at hget
                    obtain ⟨u, hu⟩ := hget
                    cases u
                    rcases columnOfCert_get?_ok _ .leaf opaqueByValue hopq c () hu with hm | ⟨_, hmem, hchk, _⟩
                    · simp [NatMap.get?] at hm
                    · obtain ⟨c', hc', heq⟩ := List.mem_map.1 hmem
                      cases heq
                      exact ⟨hc', hchk⟩

theorem buildResolve_sound {cfg : Config} {p : Program} {cert : TableCert} {t : Table}
    (h : ofCert cfg p cert = .ok t) :
    (∀ f e, (f, e) ∈ cert.resolve → ∃ r, entryOf cfg p f e = .ok r) ∧
    (∀ c r, t.resolveOf c = some r → ∃ e, (c, e) ∈ cert.resolve ∧ entryOf cfg p c e = .ok r) := by
  obtain ⟨_, _, h1, h2, _⟩ := ofCert_ok_props h
  exact ⟨h1, h2⟩

end IxCC.Src.Table
