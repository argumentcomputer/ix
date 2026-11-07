import IxCC.Own.Plain.Proof.Program

/-! Derive the callee's actual numbered source body and checked scope from
the canonical checker. A call arity lookup cannot authorize an unchecked
out-of-range map entry. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

theorem programDomain_function {P : Fir.Program} (h : programDomain P = true)
    {f : Fir.FunId} {fd : Fir.Fun} (hf : f < P.size) (hd : P.fun? f = some fd) :
    funDomain fd = true ∧ fresh [] (fd.params.map (·.1)) = true ∧
      scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body = true := by
  unfold programDomain at h
  have he := List.all_eq_true.mp h f (List.mem_range.mpr hf)
  simpa only [hd, Bool.and_eq_true, and_assoc] using he

theorem signatures_lookup {P : Fir.Program} {f : Fir.FunId} {n : Nat}
    (h : (signatures P).lookup f = some n) :
    ∃ fd, f < P.size ∧ P.fun? f = some fd ∧ fd.arity = n := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hm : (f, n) ∈ signatures P := by rw [he]; simp
  unfold signatures at hm
  obtain ⟨⟨g, fd⟩, hg, hpair⟩ := List.mem_map.mp hm
  have hp : g = f ∧ fd.arity = n := by simpa using hpair
  rcases hp with ⟨rfl, hn⟩
  unfold Fir.Program.funList at hg
  obtain ⟨i, hi, hlookup⟩ := List.mem_filterMap.mp hg
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hlookup
  obtain ⟨fd', hfd, hif, hff⟩ := hlookup
  subst i
  subst fd'
  exact ⟨fd, List.mem_range.mp hi, hfd, hn⟩


end IxCC.Own.Plain
