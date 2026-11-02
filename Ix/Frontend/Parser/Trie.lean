/-
  Ix.Frontend.Parser.Trie: Pure, total character prefix trie for maximal-munch
  tokenization in the Ix Frontend parser.
-/
module

@[expose] public section

namespace Ix.Frontend.Parser

/-- A pure character trie for maximal-munch operator and punctuation matching.
    Uses an association list of children sorted by `Char` so it requires no
    hash tables or `unsafe` code and supports structural recursion. -/
inductive Trie (α : Type) where
  | node (val : Option α) (children : List (Char × Trie α))
  deriving Repr, Inhabited

namespace Trie

/-- The empty trie. -/
def empty : Trie α := .node none []

/-- Look up or insert a child in a sorted `(Char × Trie α)` association list. -/
def upsertChild (c : Char) (f : Option (Trie α) → Trie α) :
    List (Char × Trie α) → List (Char × Trie α)
  | [] => [(c, f none)]
  | (k, t) :: rest =>
    if c == k then
      (k, f (some t)) :: rest
    else if c < k then
      (c, f none) :: (k, t) :: rest
    else
      (k, t) :: upsertChild c f rest

/-- Find a child for character `c` in a sorted `(Char × Trie α)` association list. -/
def findChild? (c : Char) : List (Char × Trie α) → Option (Trie α)
  | [] => none
  | (k, t) :: rest =>
    if c == k then some t
    else if c < k then none
    else findChild? c rest

/-- Insert a character list key into the trie (structurally recursive on `List Char`). -/
def insertChars : Trie α → List Char → α → Trie α
  | .node _ children, [], v => .node (some v) children
  | .node val children, c :: cs, v =>
    let children' := upsertChild c (fun prev? =>
      insertChars (prev?.getD empty) cs v) children
    .node val children'

/-- Insert a string key into the trie. -/
def insert (t : Trie α) (s : String) (v : α) : Trie α :=
  insertChars t s.toList v

/-- Build a trie from a list of strings (mapping each string to itself). -/
def ofSymbols (syms : List String) : Trie String :=
  syms.foldl (fun t s => t.insert s s) empty

/-- Exact lookup of a character list key in the trie. -/
def findExact? : Trie α → List Char → Option α
  | .node val _, [] => val
  | .node _ children, c :: cs =>
    match findChild? c children with
    | none       => none
    | some child => findExact? child cs

/-- Match the longest prefix in `rem : List Char`, tracking current position `idx`. -/
def matchPrefixList (idx : Nat) (best : Option (α × Nat)) :
    List Char → Trie α → Option (α × Nat)
  | [], .node val _ =>
    match val with
    | some v => some (v, idx)
    | none   => best
  | c :: cs, .node val children =>
    let best' := match val with
      | some v => some (v, idx)
      | none   => best
    match findChild? c children with
    | none       => best'
    | some child => matchPrefixList (idx + 1) best' cs child

/-- Match the longest prefix of `chars` starting at `idx`. -/
def matchPrefix (t : Trie α) (chars : List Char) (idx : Nat) : Option (α × Nat) :=
  matchPrefixList idx none (chars.drop idx) t

end Trie

end Ix.Frontend.Parser
