import Aiur.WireRelation
import Aiur.LayoutComposition
import Aiur.ConstructorFacts

namespace Aiur

/-- Canonical component encodings assemble to a canonical tuple payload. -/
theorem DecodesValues.encodeList [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {wires : List (WireValue F)} {values : List (Value F)}
    (decoded : DecodesValues decls wires values) :
    ∃ layouts, List.Forall₂ (fun ty layout => decls.layout ty = .ok layout)
      (wires.map WireValue.type) layouts ∧
      Layout.encodeList layouts values = some (wires.flatMap WireValue.words) := by
  induction decoded with
  | nil => exact ⟨[], .nil, by simp [Layout.encodeList]⟩
  | @cons wire value wires values head tail ih =>
      obtain ⟨_, _, layout, expanded, rawDecode⟩ := WireValue.decode_spec head
      obtain ⟨layouts, expansions, encoded⟩ := ih
      refine ⟨layout :: layouts, .cons expanded expansions, ?_⟩
      have first := Layout.encode_decode (Declarations.layout_namesUnique checked expanded) rawDecode
      simp [Layout.encodeList, first, encoded]

theorem WireValue.decode_tuple [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values) :
    (WireValue.tuple wires).decode decls = some (.tuple values) := by
  obtain ⟨layouts, expansions, encoded⟩ := decoded.encodeList checked
  have expanded := Declarations.layout_tuple expansions
  apply WireValue.decode_of_layout checked expanded
  apply Layout.decode_encode (Declarations.layout_tagSafe tags expanded)
  simpa only [Layout.encode, WireValue.tuple] using encoded

theorem WireValue.decode_ptr [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {target : Ty} (names : target.checkNames decls = .ok ()) (address : F) :
    (WireValue.ptr target address).decode decls = some (.ptr target address) := by
  have expanded := Declarations.layout_ptr names
  simp [WireValue.decode, WireValue.ptr, expanded, Except.toOption, Layout.decode,
    Value.hasType, Value.type, Value.wellFormed]

theorem Layout.encodeConstructor_at [NatCast F] [Zero F]
    {constructors : List (String × Layout)} (names : (constructors.map Prod.fst).Nodup)
    {index start : Nat} {ctor : String} {layout : Layout}
    (found : constructors[index]? = some (ctor, layout))
    {args : List (Value F)} {payload : List F} (encoded : layout.encode (.tuple args) = some payload) :
    Layout.encodeConstructor constructors ctor args start = some (start + index, payload) := by
  induction constructors generalizing index start with
  | nil => simp at found
  | cons pair rest ih =>
      rcases pair with ⟨name, head⟩
      simp only [List.map_cons, List.nodup_cons] at names
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          simp [Layout.encodeConstructor, encoded]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have different : name ≠ ctor := by
            intro same
            exact names.1 (List.mem_map.mpr ⟨(ctor, layout), List.mem_of_getElem? found, same.symm⟩)
          simpa [Layout.encodeConstructor, different, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih names.2 found (start := start + 1)

/-- Constructor assembly uses its declared tag and zeroes every unused payload column. -/
theorem WireValue.decode_construct [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {name : String} {definition : EnumDecl} (found : decls.findEnum? name = some definition)
    {index : Nat} {ctor : ConstructorDecl} (atIndex : definition.constructors[index]? = some ctor)
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values)
    (types : wires.map WireValue.type = ctor.fields)
    {layout : Layout} (expanded : decls.layout (.enum name) = .ok layout) :
    (WireValue.mk (.enum name) (Layout.enumWords definition.constructors.length (index : F)
      (wires.flatMap WireValue.words ++
      List.replicate (layout.width - Layout.tagWidth definition.constructors.length -
        (wires.flatMap WireValue.words).length) 0))).decode decls =
      some (.construct name ctor.name values) := by
  have description := Declarations.layout_describes expanded
  cases description with
  | @enum _ other constructors otherFound related =>
      have same := Option.some.inj (found.symm.trans otherFound)
      subst other
      obtain ⟨chosen, chosenAt, chosenDescription⟩ := related.at atIndex
      obtain ⟨layouts, expansions, encoded⟩ := decoded.encodeList checked
      have payloadExpanded := Declarations.layout_tuple expansions
      rw [types] at payloadExpanded
      have sameLayout := chosenDescription.unique (Declarations.layout_describes payloadExpanded)
      subst chosen
      have unique := Declarations.layout_namesUnique checked expanded
      simp only [Layout.NamesUnique] at unique
      have chosenEncoded := Layout.encodeConstructor_at unique.1 chosenAt
        (by simpa only [Layout.encode, WireValue.tuple] using encoded) (start := 0)
      apply WireValue.decode_of_layout checked expanded
      apply Layout.decode_encode (Declarations.layout_tagSafe tags expanded)
      simp [Layout.encode, chosenEncoded, Layout.width, Layout.payloadWidth, related.length]

theorem WireValue.ptr_decoded_eq [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {target : Ty} {address : F} {value : Value F}
    (decoded : (WireValue.ptr target address).decode decls = some value) : value = .ptr target address := by
  obtain ⟨_, _, layout, expanded, rawDecode⟩ := WireValue.decode_spec decoded
  have described := Declarations.layout_describes expanded
  cases described
  simpa only [WireValue.ptr, Layout.decode, Option.some.injEq] using rawDecode.symm

end Aiur
