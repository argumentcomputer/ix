import Ix.Compiler.Ixon.Expr

/-!
# Sharing-table invariants and inlining

The cheap structural layer of canonical Ixon sharing. Ix.Compiler's local
policy accepts a decoded table only when:

1. every body reference is in bounds;
2. entry `i` references only entries `< i`;
3. no entry is a bare `.share` alias;
4. every entry is referenced at least twice by later entries and bodies.

The first three rules make left-to-right inlining total and rule out cycles.
The fourth rejects dead/single-use entries, which a canonical compressor never
emits and which otherwise mint distinct addresses for the same inlined term.
Exact compressor-image canonicality is the next layer; it is deliberately not
claimed here.  The pinned upstream ixon-v2 compressor can leave a nested entry
with one direct use after sharing its parent.  `structuralWF` names the common
first three rules so external ix artifacts can be checked against that exact
compressor without weakening the stricter local `layer1WF` policy.
-/

namespace Ix.Compiler.Ixon.Sharing

/-- Every `.share i` inside `e` satisfies `i < bound`. -/
def sharesBelow (bound : Nat) : Expr → Bool
  | .share i => i.toNat < bound
  | .app f a => sharesBelow bound f && sharesBelow bound a
  | .lam _ t b => sharesBelow bound t && sharesBelow bound b
  | .all _ _ d c => sharesBelow bound d && sharesBelow bound c
  | .letE _ t v b =>
    sharesBelow bound t && sharesBelow bound v && sharesBelow bound b
  | .prj _ _ v => sharesBelow bound v
  | _ => true

/-- Entry `i` may reference only earlier entries and may not be a bare alias. -/
def entryWF (i : Nat) : Expr → Bool
  | .share _ => false
  | e => sharesBelow i e

/-- Check entries left-to-right, using their final table index as the bound. -/
def entriesWF (next : Nat) : List Expr → Bool
  | [] => true
  | e :: es => entryWF next e && entriesWF (next + 1) es

/-- Backward-only, in-bounds, non-alias table structure (rules 2–3). -/
def tableWF (table : Array Expr) : Bool :=
  entriesWF 0 table.toList

/-- Occurrences of `.share i` in an expression. -/
def countShare (i : Nat) : Expr → Nat
  | .share j => if j.toNat == i then 1 else 0
  | .app f a => countShare i f + countShare i a
  | .lam _ t b => countShare i t + countShare i b
  | .all _ _ d c => countShare i d + countShare i c
  | .letE _ t v b => countShare i t + countShare i v + countShare i b
  | .prj _ _ v => countShare i v
  | _ => 0

/-- Rule 4: every entry is referenced at least twice by later entries and
constant bodies. Earlier entries cannot refer forward once `tableWF` holds. -/
def entriesUsedTwice (table bodies : Array Expr) : Bool :=
  (List.range table.size).all fun i =>
    let inEntries := (table.toList.drop (i + 1)).foldl
      (fun total e => total + countShare i e) 0
    let inBodies := bodies.foldl (fun total e => total + countShare i e) 0
    inEntries + inBodies ≥ 2

/-- The safety-critical sharing invariant common to Ix.Compiler and the
pinned upstream ixon-v2 compressor: entries are backward-only and non-alias,
and every body reference is in bounds.  Unlike `layer1WF`, this intentionally
does not impose a direct-use-count policy. -/
def structuralWF (table bodies : Array Expr) : Bool :=
  tableWF table && bodies.all (sharesBelow table.size)

/-- All four cheap sharing-table rules. -/
def layer1WF (table bodies : Array Expr) : Bool :=
  tableWF table
    && bodies.all (sharesBelow table.size)
    && entriesUsedTwice table bodies

/-- Propositional view of the executable layer-1 check. -/
structure Layer1 (table bodies : Array Expr) : Prop where
  tableOk : tableWF table = true
  bodiesOk : bodies.all (sharesBelow table.size) = true
  usedTwice : entriesUsedTwice table bodies = true

theorem layer1WF_iff (table bodies : Array Expr) :
    layer1WF table bodies = true ↔ Layer1 table bodies := by
  simp only [layer1WF, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨htable, hbodies⟩, hused⟩
    exact ⟨htable, hbodies, hused⟩
  · rintro ⟨htable, hbodies, hused⟩
    exact ⟨⟨htable, hbodies⟩, hused⟩

/-! ## Share elimination -/

/-- List core for share substitution. Keeping the proof-facing core structural
avoids depending on implementation details of `Array.foldl`. -/
def substSharesList (table : List Expr) : Expr → Expr
  | .share i => table[i.toNat]?.getD (.share i)
  | .app f a => .app (substSharesList table f) (substSharesList table a)
  | .lam u t b => .lam u (substSharesList table t) (substSharesList table b)
  | .all u o d c => .all u o (substSharesList table d) (substSharesList table c)
  | .letE nd t v b =>
    .letE nd (substSharesList table t) (substSharesList table v)
      (substSharesList table b)
  | .prj r f v => .prj r f (substSharesList table v)
  | e => e

/-- Substitute shares through a table whose entries are already inlined.
Out-of-range indices remain visible; `layer1WF` excludes that case. -/
def substShares (table : Array Expr) (e : Expr) : Expr :=
  substSharesList table.toList e

/-- Inline a suffix after an already-inlined prefix. Appending preserves the
original sharing indices. -/
def inlineEntries (inlined : List Expr) : List Expr → List Expr
  | [] => inlined
  | e :: es =>
    inlineEntries (inlined ++ [substSharesList inlined e]) es

/-- Inline entries left-to-right. Backward references therefore resolve in
one pass when `tableWF` holds. -/
def inlineTable (table : Array Expr) : Array Expr :=
  (inlineEntries [] table.toList).toArray

/-- Inline all sharing-table references in one expression. -/
def inlineExpr (table : Array Expr) (e : Expr) : Expr :=
  substShares (inlineTable table) e

/-- No `.share` node occurs in `e`. -/
def shareFree : Expr → Bool
  | .share _ => false
  | .app f a => shareFree f && shareFree a
  | .lam _ t b => shareFree t && shareFree b
  | .all _ _ d c => shareFree d && shareFree c
  | .letE _ t v b => shareFree t && shareFree v && shareFree b
  | .prj _ _ v => shareFree v
  | _ => true

/-! ## Share-elimination proofs -/

/-- A structurally well-formed entry has no references at or above its own
index. The non-alias condition is stronger than this conclusion. -/
theorem sharesBelow_of_entryWF {i : Nat} {e : Expr}
    (h : entryWF i e = true) : sharesBelow i e = true := by
  cases e <;> simp_all [entryWF, sharesBelow]

theorem substSharesList_append_of_sharesBelow
    (pre suffix : List Expr) (e : Expr)
    (hbelow : sharesBelow pre.length e = true) :
    substSharesList (pre ++ suffix) e = substSharesList pre e := by
  induction e with
  | sort | var | ref | recur | str | nat => simp [substSharesList]
  | share i =>
    simp only [sharesBelow, decide_eq_true_eq] at hbelow
    simp [substSharesList, List.getElem?_append_left hbelow]
  | prj r f val ih =>
    simp only [sharesBelow] at hbelow
    simp [substSharesList, ih hbelow]
  | app fn arg ihFn ihArg =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp [substSharesList, ihFn hbelow.1, ihArg hbelow.2]
  | lam u typ body ihTyp ihBody =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp [substSharesList, ihTyp hbelow.1, ihBody hbelow.2]
  | all u o typ body ihTyp ihBody =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp [substSharesList, ihTyp hbelow.1, ihBody hbelow.2]
  | letE nd typ val body ihTyp ihVal ihBody =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp [substSharesList, ihTyp hbelow.1.1, ihVal hbelow.1.2,
      ihBody hbelow.2]

theorem inlineEntries_eq_append_map_subst
    (pre entries : List Expr)
    (hwf : entriesWF pre.length entries = true) :
    let full := inlineEntries pre entries
    full = pre ++ entries.map (substSharesList full) := by
  induction entries generalizing pre with
  | nil => simp [inlineEntries]
  | cons entry entries ih =>
    simp only [entriesWF, Bool.and_eq_true] at hwf
    let entry' := substSharesList pre entry
    have hwfTail : entriesWF (pre ++ [entry']).length entries = true := by
      simpa using hwf.2
    have htail := ih (pre ++ [entry']) hwfTail
    have hbelow : sharesBelow pre.length entry = true :=
      sharesBelow_of_entryWF hwf.1
    have hhead :
        substSharesList (inlineEntries (pre ++ [entry']) entries) entry =
          entry' := by
      rw [htail]
      rw [show (pre ++ [entry']) ++
          entries.map
            (substSharesList (inlineEntries (pre ++ [entry']) entries)) =
          pre ++ ([entry'] ++ entries.map
            (substSharesList (inlineEntries (pre ++ [entry']) entries))) by
        simp [List.append_assoc]]
      exact substSharesList_append_of_sharesBelow pre _ entry hbelow
    simp only [inlineEntries, List.map_cons]
    change inlineEntries (pre ++ [entry']) entries =
      pre ++ substSharesList (inlineEntries (pre ++ [entry']) entries) entry ::
        entries.map
          (substSharesList (inlineEntries (pre ++ [entry']) entries))
    calc
      inlineEntries (pre ++ [entry']) entries =
          (pre ++ [entry']) ++ entries.map
            (substSharesList (inlineEntries (pre ++ [entry']) entries)) :=
        htail
      _ = pre ++ entry' :: entries.map
            (substSharesList (inlineEntries (pre ++ [entry']) entries)) := by
        simp [List.append_assoc]
      _ = pre ++ substSharesList
            (inlineEntries (pre ++ [entry']) entries) entry ::
            entries.map
              (substSharesList (inlineEntries (pre ++ [entry']) entries)) := by
        rw [hhead]

theorem inlineTable_toList_eq_map (table : Array Expr)
    (htable : tableWF table = true) :
    (inlineTable table).toList =
      table.toList.map (substSharesList (inlineTable table).toList) := by
  have h := inlineEntries_eq_append_map_subst [] table.toList htable
  simpa [inlineTable] using h

theorem inlineTable_getElem?_eq_inlineExpr
    (table : Array Expr) (i : Nat) (entry : Expr)
    (htable : tableWF table = true)
    (hget : table[i]? = some entry) :
    (inlineTable table)[i]? = some (inlineExpr table entry) := by
  have hlist : table.toList[i]? = some entry := by
    simpa using hget
  have hmap := congrArg (fun xs : List Expr => xs[i]?)
    (inlineTable_toList_eq_map table htable)
  simp [List.getElem?_map, hlist] at hmap
  change (inlineTable table)[i]? =
    some (substSharesList (inlineTable table).toList entry)
  exact hmap

theorem inlineExpr_share_eq_inlineExpr_entry
    (table : Array Expr) (i : UInt64) (entry : Expr)
    (htable : tableWF table = true)
    (hget : table[i.toNat]? = some entry) :
    inlineExpr table (.share i) = inlineExpr table entry := by
  have hinlined := inlineTable_getElem?_eq_inlineExpr table i.toNat entry
    htable hget
  simp [inlineExpr, substShares, substSharesList, hinlined]

private theorem shareFree_get?_getD
    (table : List Expr) (i : Nat) (fallback : Expr)
    (hi : i < table.length)
    (hfree : ∀ x ∈ table, shareFree x = true) :
    shareFree ((table[i]?).getD fallback) = true := by
  induction table generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simpa using hfree x (by simp)
    | succ i =>
      rw [List.getElem?_cons_succ]
      apply ih i
      · simpa using hi
      · intro y hy
        exact hfree y (by simp [hy])

/-- Substitution through a share-free table eliminates every in-bounds share
in the input expression. -/
theorem shareFree_substSharesList (table : List Expr) (e : Expr)
    (hbelow : sharesBelow table.length e = true)
    (hfree : ∀ x ∈ table, shareFree x = true) :
    shareFree (substSharesList table e) = true := by
  induction e with
  | sort | var | ref | recur | str | nat =>
    simp [substSharesList, shareFree]
  | share i =>
    simp only [sharesBelow, decide_eq_true_eq] at hbelow
    exact shareFree_get?_getD table i.toNat (.share i) hbelow hfree
  | prj r f v ih =>
    simp only [sharesBelow] at hbelow
    simpa [substSharesList, shareFree] using ih hbelow
  | app f a ihf iha =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp only [substSharesList, shareFree, Bool.and_eq_true]
    exact ⟨ihf hbelow.1, iha hbelow.2⟩
  | lam u t b iht ihb =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp only [substSharesList, shareFree, Bool.and_eq_true]
    exact ⟨iht hbelow.1, ihb hbelow.2⟩
  | all u o d c ihd ihc =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp only [substSharesList, shareFree, Bool.and_eq_true]
    exact ⟨ihd hbelow.1, ihc hbelow.2⟩
  | letE nd t v b iht ihv ihb =>
    simp only [sharesBelow, Bool.and_eq_true] at hbelow
    simp only [substSharesList, shareFree, Bool.and_eq_true]
    exact ⟨⟨iht hbelow.1.1, ihv hbelow.1.2⟩, ihb hbelow.2⟩

/-- Left-to-right inlining preserves the prefix and adds exactly one result
per source entry. -/
theorem inlineEntries_length (inlined entries : List Expr) :
    (inlineEntries inlined entries).length = inlined.length + entries.length := by
  induction entries generalizing inlined with
  | nil => simp [inlineEntries]
  | cons e es ih =>
    simp only [inlineEntries]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- If the prefix is share-free and each suffix entry points backward from its
eventual index, the completed inlined table is share-free. -/
theorem inlineEntries_shareFree (inlined entries : List Expr)
    (hfree : ∀ x ∈ inlined, shareFree x = true)
    (hwf : entriesWF inlined.length entries = true) :
    ∀ x ∈ inlineEntries inlined entries, shareFree x = true := by
  induction entries generalizing inlined with
  | nil => simpa [inlineEntries] using hfree
  | cons e es ih =>
    simp only [entriesWF, Bool.and_eq_true] at hwf
    let e' := substSharesList inlined e
    have heBelow : sharesBelow inlined.length e = true :=
      sharesBelow_of_entryWF hwf.1
    have heFree : shareFree e' = true :=
      shareFree_substSharesList inlined e heBelow hfree
    apply ih (inlined ++ [e'])
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hfree x hx
      · exact heFree
    · simpa [e'] using hwf.2

/-- Every result entry of a structurally well-formed table is share-free. -/
theorem inlineTable_shareFree (table : Array Expr)
    (htable : tableWF table = true) :
    ∀ x ∈ (inlineTable table).toList, shareFree x = true := by
  simpa [inlineTable, tableWF] using
    (inlineEntries_shareFree [] table.toList (by simp) htable)

/-- Inlining preserves the number and indices of table entries. -/
theorem inlineTable_size (table : Array Expr) :
    (inlineTable table).size = table.size := by
  simp [inlineTable, inlineEntries_length]

/-- The structural table invariant plus an in-bounds body suffices to remove
all shares. The profitability rule is intentionally unnecessary here. -/
theorem shareFree_inlineExpr_of_tableWF (table : Array Expr) (e : Expr)
    (htable : tableWF table = true)
    (hbelow : sharesBelow table.size e = true) :
    shareFree (inlineExpr table e) = true := by
  apply shareFree_substSharesList
  · simpa [inlineExpr, inlineTable_size] using hbelow
  · simpa [inlineExpr, substShares, inlineTable] using
      inlineTable_shareFree table htable

/-- Every body admitted by layer 1 becomes share-free after inlining. -/
theorem shareFree_inlineExpr_of_layer1 (table bodies : Array Expr) (e : Expr)
    (hlayer : layer1WF table bodies = true)
    (he : e ∈ bodies.toList) :
    shareFree (inlineExpr table e) = true := by
  have h : Layer1 table bodies := (layer1WF_iff table bodies).mp hlayer
  apply shareFree_inlineExpr_of_tableWF table e h.tableOk
  exact (List.all_eq_true.mp (by simpa using h.bodiesOk)) e he

/-- Substitution cannot change an expression that contains no share nodes. -/
theorem substSharesList_eq_self_of_shareFree (table : List Expr) (e : Expr)
    (hfree : shareFree e = true) :
    substSharesList table e = e := by
  induction e with
  | sort | var | ref | recur | str | nat => simp [substSharesList]
  | share => simp [shareFree] at hfree
  | prj r f v ih =>
    simp only [shareFree] at hfree
    simp [substSharesList, ih hfree]
  | app f a ihf iha =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [substSharesList, ihf hfree.1, iha hfree.2]
  | lam u t b iht ihb =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [substSharesList, iht hfree.1, ihb hfree.2]
  | all u o d c ihd ihc =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [substSharesList, ihd hfree.1, ihc hfree.2]
  | letE nd t v b iht ihv ihb =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [substSharesList, iht hfree.1.1, ihv hfree.1.2, ihb hfree.2]

/-- Inlining any table is the identity on an already share-free expression. -/
theorem inlineExpr_eq_self_of_shareFree (table : Array Expr) (e : Expr)
    (hfree : shareFree e = true) :
    inlineExpr table e = e := by
  simpa [inlineExpr, substShares] using
    substSharesList_eq_self_of_shareFree (inlineTable table).toList e hfree

/-- Share-free expressions satisfy every share-index bound, including zero. -/
theorem sharesBelow_of_shareFree (bound : Nat) (e : Expr)
    (hfree : shareFree e = true) :
    sharesBelow bound e = true := by
  induction e with
  | sort | var | ref | recur | str | nat => simp [sharesBelow]
  | share => simp [shareFree] at hfree
  | prj r f v ih =>
    simp only [shareFree] at hfree
    simpa [sharesBelow] using ih hfree
  | app f a ihf iha =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [sharesBelow, ihf hfree.1, iha hfree.2]
  | lam u t b iht ihb =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [sharesBelow, iht hfree.1, ihb hfree.2]
  | all u o d c ihd ihc =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [sharesBelow, ihd hfree.1, ihc hfree.2]
  | letE nd t v b iht ihv ihb =>
    simp only [shareFree, Bool.and_eq_true] at hfree
    simp [sharesBelow, iht hfree.1.1, ihv hfree.1.2, ihb hfree.2]

/-- Empty sharing is a layer-1 representation of every share-free body list. -/
theorem layer1WF_empty_of_shareFree (bodies : Array Expr)
    (hfree : bodies.all shareFree = true) :
    layer1WF #[] bodies = true := by
  apply (layer1WF_iff #[] bodies).mpr
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rw [Array.all_eq_true]
    intro i hi
    exact sharesBelow_of_shareFree 0 bodies[i]
      ((Array.all_eq_true.mp hfree) i hi)
  · rfl

/-! Executable boundary tests. Constant-level decoder tests live in
`Const.lean`, where all embedded bodies are available. -/

#guard tableWF #[]
#guard tableWF #[.sort 0, .app (.share 0) (.share 0)]
#guard !tableWF #[.app (.share 0) (.share 0)]
#guard !tableWF #[.app (.share 1) (.share 1), .sort 0]
#guard !tableWF #[.sort 0, .share 0]

#guard entriesUsedTwice #[.sort 0, .app (.share 0) (.share 0)]
  #[.app (.share 1) (.share 1)]
#guard !entriesUsedTwice #[.sort 0, .app (.share 0) (.share 0)]
  #[.share 1]

#guard inlineExpr #[.sort 0, .app (.share 0) (.share 0)] (.share 1)
  == .app (.sort 0) (.sort 0)
#guard shareFree (inlineExpr #[.sort 0, .app (.share 0) (.share 0)]
  (.lam .many (.share 0) (.share 1)))

end Ix.Compiler.Ixon.Sharing
