import Aiur.WireCanonical
import Aiur.ValueFormed

namespace Aiur

theorem WireValue.decode_spec [NatCast F] [Zero F] [DecidableEq F]
    {decls : Declarations} {wire : WireValue F} {value : Value F}
    (decoded : wire.decode decls = some value) :
    value.type = wire.type ∧ value.wellFormed decls = true ∧ ∃ layout,
      decls.layout wire.type = .ok layout ∧ layout.decode wire.words = some value := by
  unfold WireValue.decode at decoded
  cases expanded : decls.layout wire.type with
  | error error => simp [expanded, Except.toOption] at decoded
  | ok layout =>
      simp only [expanded, Except.toOption, bind, Option.bind] at decoded
      obtain ⟨result, run, finished⟩ := Option.bind_eq_some_iff.mp decoded
      split at finished
      · rename_i formed
        cases finished
        simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at formed
        exact ⟨formed.1, formed.2, layout, rfl, run⟩
      · cases finished

theorem Value.encode_spec [NatCast F] [Zero F] {decls : Declarations}
    {value : Value F} {wire : WireValue F} (encoded : value.encode decls = some wire) :
    value.wellFormed decls = true ∧ wire.type = value.type ∧ ∃ layout,
      decls.layout value.type = .ok layout ∧ layout.encode value = some wire.words := by
  unfold Value.encode at encoded
  split at encoded
  · cases encoded
  · rename_i formed
    have formed : value.wellFormed decls = true := by simpa using formed
    cases expanded : decls.layout value.type with
    | error error => simp [expanded, Except.toOption] at encoded
    | ok layout =>
        simp only [expanded, Except.toOption, bind, Option.bind] at encoded
        obtain ⟨words, run, finished⟩ := Option.bind_eq_some_iff.mp encoded
        cases finished
        exact ⟨formed, rfl, layout, rfl, run⟩

theorem Value.encode_sized [NatCast F] [Zero F] {decls : Declarations}
    {value : Value F} {wire : WireValue F} (encoded : value.encode decls = some wire) :
    wire.Sized decls := by
  obtain ⟨_, type, layout, expanded, run⟩ := Value.encode_spec encoded
  exact ⟨layout, by rwa [type], Layout.encode_length run⟩

theorem Value.decode_encode [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {value : Value F} {wire : WireValue F} (encoded : value.encode decls = some wire)
    (safe : ∀ layout, decls.layout value.type = .ok layout → layout.TagSafe F) :
    wire.decode decls = some value := by
  obtain ⟨formed, type, layout, expanded, run⟩ := Value.encode_spec encoded
  have decoded := Layout.decode_encode (safe layout expanded) run
  simp [WireValue.decode, type, expanded, Except.toOption, decoded, Value.hasType, formed]

theorem WireValue.encode_decode [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wire : WireValue F} {value : Value F} (decoded : wire.decode decls = some value)
    (unique : ∀ layout, decls.layout wire.type = .ok layout → layout.NamesUnique) :
    value.encode decls = some wire := by
  obtain ⟨type, formed, layout, expanded, run⟩ := WireValue.decode_spec decoded
  have encoded := Layout.encode_decode (unique layout expanded) run
  cases wire
  simp [Value.encode, formed, type, expanded, Except.toOption, encoded]

end Aiur
