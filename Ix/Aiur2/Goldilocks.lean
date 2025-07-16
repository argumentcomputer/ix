namespace Aiur

abbrev gSize := 0xFFFFFFFF00000001
abbrev G := Fin gSize

@[inline] def G.ofNat n := Fin.ofNat' gSize n

end Aiur
