import Aiur.Generic.Runtime
import Aiur.Generic.SymbolFacts

/-! # Lookups by name, without comparing names

`List.find?` by a string key compares the key with every earlier entry, and
the kernel compares string literals character by character: on the checked
IxVM program (850 functions), one `findFunction?` lemma costs about two
seconds of kernel time, and all of them half an hour. Here a lookup costs a
membership proof (an index), and the names' distinctness is certified once by
comparing natural-number keys (`nameKey`), which the kernel compares as
numbers.

* `nameKey`: a name as a number, injective (`nameKey_injective`).
* `find?_key`: in a list whose keys are distinct, `find?` by a member's key
  finds that member.
* `Program.findFunction?_of_mem`, `Consts.lookup_of_mem`,
  `Program.sourceFunction?_of_mem`: the program lookups.
* `Source.world_prepare_of_sourceFunction`: what a successful `world.prepare`
  of such a function returns. It does not evaluate the argument type check,
  whose `$` types may be long; it only reads its success. -/

namespace Aiur.Generic

/-- A string's characters as a number: base `2^32 + 1` digits, each a
character's code plus one. -/
def keyOfChars : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat + 1) + 4294967297 * keyOfChars cs

/-- **A name as a number.** -/
def nameKey (s : String) : Nat := keyOfChars s.toList

theorem keyOfChars_injective : ∀ {a b : List Char}, keyOfChars a = keyOfChars b → a = b
  | [], [], _ => rfl
  | [], c :: cs, h => by simp only [keyOfChars] at h; omega
  | c :: cs, [], h => by simp only [keyOfChars] at h; omega
  | c :: cs, d :: ds, h => by
    simp only [keyOfChars] at h
    have hc : c.toNat < 2 ^ 32 := by rw [← Char.toNat_val]; exact UInt32.toNat_lt _
    have hd : d.toNat < 2 ^ 32 := by rw [← Char.toNat_val]; exact UInt32.toNat_lt _
    have h1 : c.toNat = d.toNat := by omega
    have h2 : keyOfChars cs = keyOfChars ds := by omega
    rw [Char.toNat_inj.mp h1, keyOfChars_injective h2]

theorem nameKey_injective {a b : String} (h : nameKey a = nameKey b) : a = b :=
  String.toList_injective (keyOfChars_injective h)

/-- **Distinct keys, distinct names.** -/
theorem nodup_of_nameKeys {l : List String} (h : (l.map nameKey).Nodup) : l.Nodup :=
  List.Pairwise.of_map nameKey (fun _ _ ne eq => ne (congrArg nameKey eq)) h

/-- In a list with distinct keys, `find?` by a member's key finds that member. -/
theorem find?_key {α : Type} (key : α → String) :
    ∀ {l : List α}, (l.map key).Nodup → ∀ {x : α}, x ∈ l →
      l.find? (fun y => key y == key x) = some x
  | [], _, _, hx => by simp at hx
  | y :: ys, hd, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : key y ≠ key x := by
        intro e
        exact hd.1 (e ▸ List.mem_map_of_mem hx)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find?_key key hd.2 hx

/-- **A function by name**: a member of a program whose function names are
distinct. -/
theorem Program.findFunction?_of_mem {p : Program α} (hd : (p.functions.map (·.name)).Nodup)
    {f : Function α} (hf : f ∈ p.functions) : p.findFunction? f.name = some f := by
  unfold Program.findFunction?
  exact find?_key (fun g : Function α => g.name) hd hf

/-- **A const by name.** -/
theorem Consts.lookup_of_mem {decls : List (ConstDecl α)} (hd : (decls.map (·.name)).Nodup)
    {d : ConstDecl α} (hx : d ∈ decls) : Consts.lookup decls d.name = .ok d.value := by
  unfold Consts.lookup
  rw [find?_key (fun d : ConstDecl α => d.name) hd hx]
  rfl

/-- **A non-generic function's closure by name**: the body is the
function's, with no type arguments. -/
theorem Program.sourceFunction?_of_mem {p : Program F} (hd : (p.functions.map (·.name)).Nodup)
    {f : Function F} (hf : f ∈ p.functions) (hplain : f.name.toList.head? ≠ some '$')
    (htypes : f.typeParams = []) :
    p.sourceFunction? f.name =
      some { types := [], params := f.params.map fun (n, t) => (n, (t.subst []).toCore),
             body := f.body } := by
  have hsym : Instance.ofSymbol f.name = .ok ⟨f.name, []⟩ := by
    have := Instance.ofSymbol_symbol ⟨f.name, []⟩ (fun _ => hplain)
    simpa [Instance.symbol] using this
  simp [Program.sourceFunction?, hsym, Except.toOption, Program.findFunction?_of_mem hd hf, htypes,
    arguments, pure, Except.pure, bind, Except.bind]

/-- **What a successful call preparation returns**, read off the closure:
the closure's type environment, its parameters bound to the arguments, and
its body. -/
theorem Source.world_prepare_of_sourceFunction [DecidableEq F] {s : Source F} {name : String}
    {fn : SourceFunction F} (hfn : s.program.sourceFunction? name = some fn)
    {args : List (SourceValue F)} {types : SourceSemantics.Types} {locals : Environment F Nat}
    {body : Expr F} (h : s.world.prepare name args = .ok (types, locals, body)) :
    types = fn.types ∧ locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  simp only [Source.world, sourceWorld, hfn, SourceFunction.prepare] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · cases h

end Aiur.Generic
