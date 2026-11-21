module

public import IxC.Address.Core
import all IxC.Address.Core

/-! # Hexadecimal string round-trip for `bytesOfHex`

Provides `hexCharsOfBytes` and proves `bytesOfHex_ofList_hexChars`:
`bytesOfHex (String.ofList (hexCharsOfBytes bs)) = some ⟨bs.toArray⟩`, using `import all` on
`IxC.Address.Core` in this leaf module so `bytesOfHex.go` is visible privately without exposing
`IxC.Address.Core`'s internals downstream. -/

@[expose] public section

namespace IxVM.Refinement.Claim

def nibbleChar : UInt8 → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

def hexCharsOfBytes : List UInt8 → List Char
  | [] => []
  | b :: bs => nibbleChar (b >>> 4) :: nibbleChar (b &&& 0xF) :: hexCharsOfBytes bs

private theorem uint8_ofNat_toNat (x : UInt8) : UInt8.ofNat x.toNat = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt x.toNat_lt

private theorem forall_uint8 (P : UInt8 → Bool)
    (h : (List.range 256).all (fun k => P (UInt8.ofNat k)) = true) (b : UInt8) :
    P b = true := by
  have hm : b.toNat ∈ List.range 256 := List.mem_range.mpr b.toNat_lt
  have hb := List.all_eq_true.mp h b.toNat hm
  simpa [uint8_ofNat_toNat] using hb

private theorem byteOfHex_nibble_bool (b : UInt8) :
    (byteOfHex (nibbleChar (b >>> 4)) (nibbleChar (b &&& 0xF)) == some b) = true :=
  forall_uint8
    (fun x => byteOfHex (nibbleChar (x >>> 4)) (nibbleChar (x &&& 0xF)) == some x)
    (by decide +kernel) b

private theorem byteOfHex_nibble (b : UInt8) :
    byteOfHex (nibbleChar (b >>> 4)) (nibbleChar (b &&& 0xF)) = some b :=
  beq_iff_eq.mp (byteOfHex_nibble_bool b)

private theorem bytesOfHex_go_hexChars :
    ∀ bs : List UInt8, bytesOfHex.go (hexCharsOfBytes bs) = some bs
  | [] => rfl
  | b :: bs => by
    simp [hexCharsOfBytes, bytesOfHex.go, byteOfHex_nibble b, bytesOfHex_go_hexChars bs, bind]

theorem bytesOfHex_ofList_hexChars (bs : List UInt8) :
    bytesOfHex (String.ofList (hexCharsOfBytes bs)) = some ⟨bs.toArray⟩ := by
  unfold bytesOfHex
  rw [String.toList_ofList, bytesOfHex_go_hexChars bs]
  rfl

private theorem bytesOfHex_go_append :
    ∀ {cs₁ cs₂ : List Char} {bs₁ bs₂ : List UInt8},
      bytesOfHex.go cs₁ = some bs₁ →
      bytesOfHex.go cs₂ = some bs₂ →
      bytesOfHex.go (cs₁ ++ cs₂) = some (bs₁ ++ bs₂)
  | [], _, _, _, h₁, h₂ => by
    cases h₁
    simpa using h₂
  | [_], _, _, _, h₁, _ => by
    cases h₁
  | hi :: lo :: rest, _, _, _, h₁, h₂ => by
    simp only [bytesOfHex.go, bind, Option.bind] at h₁
    cases hb : byteOfHex hi lo with
    | none => simp [hb] at h₁
    | some b =>
      simp only [hb] at h₁
      cases hr : bytesOfHex.go rest with
      | none => simp [hr] at h₁
      | some bs =>
        simp only [hr, Option.some.injEq] at h₁
        subst h₁
        have ih := bytesOfHex_go_append hr h₂
        simp [List.cons_append, bytesOfHex.go, bind, Option.bind, hb, ih]

theorem bytesOfHex_append {s₁ s₂ : String} {bs₁ bs₂ : List UInt8}
    (h₁ : bytesOfHex s₁ = some ⟨bs₁.toArray⟩)
    (h₂ : bytesOfHex s₂ = some ⟨bs₂.toArray⟩) :
    bytesOfHex (s₁ ++ s₂) = some ⟨(bs₁ ++ bs₂).toArray⟩ := by
  unfold bytesOfHex at h₁ h₂ ⊢
  simp only [bind, Option.bind, pure] at h₁ h₂ ⊢
  cases hg₁ : bytesOfHex.go s₁.toList with
  | none => simp [hg₁] at h₁
  | some xs₁ =>
    simp only [hg₁, Option.some.injEq] at h₁
    have he₁ : xs₁ = bs₁ := by
      have := congrArg (fun ba : ByteArray => ba.data.toList) h₁
      simpa using this
    subst he₁
    cases hg₂ : bytesOfHex.go s₂.toList with
    | none => simp [hg₂] at h₂
    | some xs₂ =>
      simp only [hg₂, Option.some.injEq] at h₂
      have he₂ : xs₂ = bs₂ := by
        have := congrArg (fun ba : ByteArray => ba.data.toList) h₂
        simpa using this
      subst he₂
      rw [String.toList_append, bytesOfHex_go_append hg₁ hg₂]

end IxVM.Refinement.Claim
