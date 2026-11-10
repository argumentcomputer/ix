import Aiur.Generic.Runtime
import Aiur.Generic.SymbolFacts

/-! # Lookups by name, without comparing names

`List.find?` by a string key compares the key with every earlier entry, and
the kernel compares string literals character by character: on the checked
IxVM program (855 functions), one `findFunction?` lemma costs about two
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

/-- A byte string as a number: base `257` digits, each a byte plus one.
Quadratic in the byte length `L` (`257 * keyOfBytes bs`), intended for short
identifier names (`L ≤ 64`) rather than arbitrary data blobs. -/
def keyOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => (b.toNat + 1) + 257 * keyOfBytes bs

/-- **A name as a number**, from its UTF-8 bytes. The kernel reads a string
literal's bytes directly; decoding its characters (`String.toList`) costs
about a tenth of a second per name. -/
def nameKey (s : String) : Nat := keyOfBytes s.toByteArray.data.toList

theorem keyOfBytes_injective : ∀ {a b : List UInt8}, keyOfBytes a = keyOfBytes b → a = b
  | [], [], _ => rfl
  | [], c :: cs, h => by simp only [keyOfBytes] at h; omega
  | c :: cs, [], h => by simp only [keyOfBytes] at h; omega
  | c :: cs, d :: ds, h => by
    simp only [keyOfBytes] at h
    have hc : c.toNat < 256 := c.toNat_lt
    have hd : d.toNat < 256 := d.toNat_lt
    have h1 : c.toNat = d.toNat := by omega
    have h2 : keyOfBytes cs = keyOfBytes ds := by omega
    rw [UInt8.toNat_inj.mp h1, keyOfBytes_injective h2]

theorem nameKey_injective {a b : String} (h : nameKey a = nameKey b) : a = b := by
  have hl := keyOfBytes_injective h
  apply String.toByteArray_inj.mp
  cases ha : a.toByteArray with
  | mk da =>
    cases hb : b.toByteArray with
    | mk db =>
      simp only [nameKey, ha, hb] at hl
      cases da; cases db
      simp only [Array.toList] at hl
      rw [hl]

/-- **A plain name**: a string whose first byte is not `$`'s does not start
with `$`. -/
theorem head_ne_of_bytes {s : String} (h : s.toByteArray.data.toList.head? ≠ some 36) :
    s.toList.head? ≠ some '$' := by
  intro hs
  obtain ⟨cs, hcs⟩ : ∃ cs, s.toList = '$' :: cs := by
    cases e : s.toList with
    | nil => simp [e] at hs
    | cons c cs => simp only [e, List.head?_cons, Option.some.injEq] at hs; exact ⟨cs, by rw [hs]⟩
  have enc := String.utf8Encode_toList (b := s)
  rw [hcs, List.utf8Encode_cons, List.utf8Encode_singleton] at enc
  apply h
  rw [← enc]
  simp [String.utf8EncodeChar, ByteArray.append, List.toByteArray, ByteArray.data_append]
  exact Or.inl (by decide)

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

/-- In a list whose keys miss `nameKey name`, `find?` by `name` finds nothing. -/
theorem find?_none_of_key {α : Type} (key : α → String) {name : String} :
    ∀ {l : List α}, nameKey name ∉ l.map (fun y => nameKey (key y)) →
      l.find? (fun y => key y == name) = none
  | [], _ => rfl
  | y :: ys, hk => by
    rw [List.map_cons, List.mem_cons, not_or] at hk
    have hne : key y ≠ name := fun e => hk.1 (congrArg nameKey e).symm
    rw [List.find?_cons_of_neg (by simpa using hne)]
    exact find?_none_of_key key hk.2

/-- **No function by that name**: a plain name whose key is not a function's
key resolves to no closure (a map, at a call). -/
theorem Program.sourceFunction?_of_key {p : Program F} {name : String}
    (hkey : nameKey name ∉ p.functions.map (fun f => nameKey f.name))
    (hplain : name.toList.head? ≠ some '$') : p.sourceFunction? name = none := by
  have hsym : Instance.ofSymbol name = .ok ⟨name, []⟩ := by
    have := Instance.ofSymbol_symbol ⟨name, []⟩ (fun _ => hplain)
    simpa [Instance.symbol] using this
  have hnone : p.findFunction? name = none := by
    unfold Program.findFunction?
    exact find?_none_of_key (fun g : Function F => g.name) hkey
  simp [Program.sourceFunction?, hsym, Except.toOption, hnone, bind, Option.bind]

/-- **Every closure `sourceFunction?` returns has the body of some function in
the program.** -/
theorem Program.sourceFunction?_body_mem {p : Program F} {name : String} {sf : SourceFunction F}
    (h : p.sourceFunction? name = some sf) :
    ∃ f ∈ p.functions, sf.body = f.body := by
  unfold Program.sourceFunction? at h
  cases h1 : (Instance.ofSymbol name).toOption with
  | none => simp [h1] at h
  | some key =>
    cases h2 : p.findFunction? key.name with
    | none => simp [h1, h2] at h
    | some fn =>
      cases h3 : (arguments fn.typeParams key.types).toOption with
      | none => simp [h1, h2, h3] at h
      | some types =>
        simp only [h1, h2, h3, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        exact ⟨fn, List.mem_of_find?_eq_some h2, rfl⟩

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
