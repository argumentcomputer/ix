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

/-- Force `c.val.toNat` to WHNF before binding it in `k`. -/
@[inline] def bindCharNat (c : Char) (k : Nat → α) : α :=
  match c.val.toNat with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- Look up or insert a child for codepoint `cn` (`c`) in a sorted `(Char × Trie α)` association list,
    strictly forcing the updated child `Trie` and tail list before constructing nodes. -/
def upsertChildNat (cn : Nat) (c : Char) (f : Option (Trie α) → Trie α) :
    List (Char × Trie α) → List (Char × Trie α)
  | [] =>
    match f none with
    | .node v ch => [(c, .node v ch)]
  | (k, t) :: rest =>
    bindCharNat k fun kn =>
    if Nat.beq cn kn then
      match f (some t) with
      | .node v ch => (k, .node v ch) :: rest
    else if Nat.ble (cn + 1) kn then
      match f none with
      | .node v ch => (c, .node v ch) :: (k, t) :: rest
    else
      match upsertChildNat cn c f rest with
      | [] => [(k, t)]
      | hd :: tl => (k, t) :: hd :: tl

/-- Look up or insert a child in a sorted `(Char × Trie α)` association list. -/
@[inline] def upsertChild (c : Char) (f : Option (Trie α) → Trie α)
    (children : List (Char × Trie α)) : List (Char × Trie α) :=
  bindCharNat c fun cn => upsertChildNat cn c f children

/-- Find a child for character codepoint `cn` in a sorted `(Char × Trie α)` association list. -/
def findChildNat? (cn : Nat) : List (Char × Trie α) → Option (Trie α)
  | [] => none
  | (k, t) :: rest =>
    bindCharNat k fun kn =>
    if Nat.beq cn kn then some t
    else if Nat.ble (cn + 1) kn then none
    else findChildNat? cn rest

/-- Find a child for character `c` in a sorted `(Char × Trie α)` association list. -/
@[inline] def findChild? (c : Char) (children : List (Char × Trie α)) : Option (Trie α) :=
  bindCharNat c fun cn => findChildNat? cn children

/-- Insert a character list key into the trie (structurally recursive on `List Char`),
    strictly forcing the updated children list before wrapping in `.node`. -/
def insertChars : Trie α → List Char → α → Trie α
  | .node _ children, [], v => .node (some v) children
  | .node val children, c :: cs, v =>
    match upsertChild c (fun prev? => insertChars (prev?.getD empty) cs v) children with
    | [] => .node val []
    | hd :: tl => .node val (hd :: tl)

/-- Insert a string key into the trie. -/
def insert (t : Trie α) (s : String) (v : α) : Trie α :=
  insertChars t s.toList v

/-- Strictly fold a list of strings into a `Trie String`. -/
def ofSymbolsLoop : Trie String → List String → Trie String
  | t, [] => t
  | t, s :: ss =>
    match t.insert s s with
    | .node v ch => ofSymbolsLoop (.node v ch) ss

/-- Build a trie from a list of strings (mapping each string to itself). -/
def ofSymbols (syms : List String) : Trie String :=
  ofSymbolsLoop empty syms

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
