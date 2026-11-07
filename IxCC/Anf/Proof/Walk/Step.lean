import IxCC.Anf.Proof.Walk.Basic

/-! # The rewriting walk: the statement at one fuel level

`Ctx n` gathers what the walk's simulation at clock bound `n` assumes of the
two programs: the source program is the configurations' program, constructor
tables and pinned keys agree, every source global has a target global of
the same arity, and applying related values, calling a global and reading a
global's value simulate at `n` (`Rel.AppSim`, `CallSim`, `GlobSim`); a
redirected call (P4) simulates the call it replaces.

`WalkAt n fuel` is the simulation, at bound `n`, of each walk function at
`fuel`: the walked term simulates the source term followed by the source
continuation that matches the walk's continuation (M2.3). Join entries,
environments and continuations survive growing target environments
(`JEnv.suffix`, `KontW.suffix`), and lower bounds (`JEnv.mono`,
`KontW.mono`). -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

theorem getElem?_level {α : Type} {xs ys : List α} (h : xs <:+ ys) {l : Nat} (hl : l < xs.length) :
    ys[ys.length - 1 - l]? = xs[xs.length - 1 - l]? := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_right (by simp; omega)]
  congr 1
  simp; omega

variable {P Q : Program} {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg}

/-! ## Join entries and continuations under growth -/

theorem JEnv.suffix {n : Nat} {T : Option (Val → Nat → Result Val)} {ρ' ρ₂ : List Val}
    {J' J₂ : List JClo} (hρ : ρ' <:+ ρ₂) (hJ : J' <:+ J₂) :
    ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo}, JEnv P Q Valid Xc C n T ρ' J' jl jσ J →
      JEnv P Q Valid Xc C n T ρ₂ J₂ jl jσ J
  | _, _, _, .nil => .nil
  | _, _, _, .emitted hl hjc hT hR henv hJj hnd hv h =>
    .emitted (Nat.lt_of_lt_of_le hl hJ.length_le) (by rw [getElem?_level hJ hl]; exact hjc) hT hR
      (henv.suffix hρ) (JEnv.suffix hρ hJ hJj) hnd (fun ρ'' h'' => hv ρ'' (hρ.trans h''))
      (JEnv.suffix hρ hJ h)
  | _, _, _, .once henv hJj hnd hv h =>
    .once (henv.suffix hρ) (JEnv.suffix hρ hJ hJj) hnd (fun ρ'' h'' => hv ρ'' (hρ.trans h''))
      (JEnv.suffix hρ hJ h)
  | _, _, _, .dead h => .dead (JEnv.suffix hρ hJ h)

theorem JoinR.mono {n m : Nat} {T : Val → Nat → Result Val} {jc jc' : JClo}
    (h : JoinR P Q Valid Xc n T jc jc') (hm : m ≤ n) : JoinR P Q Valid Xc m T jc jc' :=
  fun i hi => h i (Nat.le_trans hi hm)

theorem JEnv.mono {n m : Nat} (hm : m ≤ n) {T : Option (Val → Nat → Result Val)} {ρ' : List Val}
    {J' : List JClo} :
    ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo}, JEnv P Q Valid Xc C n T ρ' J' jl jσ J →
      JEnv P Q Valid Xc C m T ρ' J' jl jσ J
  | _, _, _, .nil => .nil
  | _, _, _, .emitted hl hjc hT hR henv hJj hnd hv h =>
    .emitted hl hjc hT (hR.mono hm) henv (JEnv.mono hm hJj) hnd hv (JEnv.mono hm h)
  | _, _, _, .once henv hJj hnd hv h => .once henv (JEnv.mono hm hJj) hnd hv (JEnv.mono hm h)
  | _, _, _, .dead h => .dead (JEnv.mono hm h)

/-- Without a target meaning there are no emitted join points, so the
entries are valid for every target meaning and join environment. -/
theorem JEnv.retarget {n : Nat} {ρ' : List Val} {J' J₂ : List JClo}
    {T : Option (Val → Nat → Result Val)} :
    ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo}, JEnv P Q Valid Xc C n none ρ' J' jl jσ J →
      JEnv P Q Valid Xc C n T ρ' J₂ jl jσ J
  | _, _, _, .nil => .nil
  | _, _, _, .emitted _ _ hT _ _ _ _ _ _ => nomatch hT
  | _, _, _, .once henv hJj hnd hv h => .once henv (JEnv.retarget hJj) hnd hv (JEnv.retarget h)
  | _, _, _, .dead h => .dead (JEnv.retarget h)

theorem JEnv.length {n : Nat} {T : Option (Val → Nat → Result Val)} {ρ' : List Val}
    {J' : List JClo} : ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo},
    JEnv P Q Valid Xc C n T ρ' J' jl jσ J → jσ.length = J.length ∧ jl.length = J.length
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .emitted _ _ _ _ _ _ _ _ h => by have := h.length; simp [this.1, this.2]
  | _, _, _, .once _ _ _ _ h => by have := h.length; simp [this.1, this.2]
  | _, _, _, .dead h => by have := h.length; simp [this.1, this.2]

theorem KT_suffix {k : Kont} {J' J₂ : List JClo} (hJ : J' <:+ J₂) {T : Val → Nat → Result Val}
    (h : KT Q k J' = some T) : KT Q k J₂ = some T := by
  cases k with
  | ret => exact h
  | jump l =>
    simp only [KT] at h ⊢
    split at h
    · next hl =>
      rw [if_pos (Nat.lt_of_lt_of_le hl hJ.length_le), getElem?_level hJ hl]
      exact h
    · cases h
  | cont f => cases h

theorem KontW.suffix {n : Nat} {k : Kont} {SK : Val → Nat → Result Val} {ρ' ρ₂ : List Val}
    {J' J₂ : List JClo} (h : KontW Q Valid Xc n k SK ρ' J') (hρ : ρ' <:+ ρ₂) (hJ : J' <:+ J₂) :
    KontW Q Valid Xc n k SK ρ₂ J₂ := by
  cases k with
  | cont f =>
    intro here' o e s s' ρ'' J'' hf hρ' hJ' hd hdj hfacts x w hw hxw
    exact h here' o e s s' ρ'' J'' hf (hρ.trans hρ') (hJ.trans hJ') hd hdj hfacts x w hw hxw
  | ret => obtain ⟨T, hT, hs⟩ := h; exact ⟨T, KT_suffix hJ hT, hs⟩
  | jump l => obtain ⟨T, hT, hs⟩ := h; exact ⟨T, KT_suffix hJ hT, hs⟩

theorem KontW.mono {n m : Nat} (hm : m ≤ n) {k : Kont} {SK : Val → Nat → Result Val}
    {ρ' : List Val} {J' : List JClo} (h : KontW Q Valid Xc n k SK ρ' J') : KontW Q Valid Xc m k SK ρ' J' := by
  cases k with
  | cont f =>
    intro here' o e s s' ρ'' J'' hf hρ' hJ' hd hdj hfacts x w hw hxw
    exact (h here' o e s s' ρ'' J'' hf hρ' hJ' hd hdj hfacts x w hw hxw).mono_n hm
  | ret => obtain ⟨T, hT, hs⟩ := h; exact ⟨T, hT, fun x w hxw => (hs x w hxw).mono_n hm⟩
  | jump l => obtain ⟨T, hT, hs⟩ := h; exact ⟨T, hT, fun x w hxw => (hs x w hxw).mono_n hm⟩

/-- The target meaning of a continuation relates to the source
continuation. -/
theorem KontW.meaning {n : Nat} {k : Kont} {SK : Val → Nat → Result Val} {ρ' : List Val}
    {J' : List JClo} (h : KontW Q Valid Xc n k SK ρ' J') {T : Val → Nat → Result Val}
    (hT : KT Q k J' = some T) : ∀ x w, WV Q Valid Xc x w → SimUpTo (WV Q Valid Xc) n (SK x) (T w) := by
  cases k with
  | cont f => cases hT
  | ret => obtain ⟨T', hT', hs⟩ := h; rw [hT] at hT'; cases hT'; exact hs
  | jump l => obtain ⟨T', hT', hs⟩ := h; rw [hT] at hT'; cases hT'; exact hs

/-! ## The statement -/

/-- A redirected call (P4) simulates the call it replaces: a call whose
masked arguments are the redirected global's own parameters (`fixedAt`, at
the source depth) and whose operands the redirect accepts, in source and
target environments where the configuration is valid. -/
def RedSim (n : Nat) (r : Walk.Redirect) (ρ ρ' : List Val) : Prop :=
  ∀ (as : List Atom) (os os' : List Opd) (vs ws : List Val),
    Walk.fixedAt r ρ.length as = true → Walk.redirectArgs r os = some os' →
    evalAtoms ρ as = some vs → os.mapM (·.val ρ') = some ws → WVs Q Valid Xc vs ws →
    ∃ ws', os'.mapM (·.val ρ') = some ws' ∧
      SimUpTo (WV Q Valid Xc) n (fun k => (Result.ofOption (P.global? r.g)).bind (callVal P k · vs))
        (fun k => (Result.ofOption (Q.global? r.spec)).bind (callVal Q k · ws'))

variable (P Q Valid Xc) in
/-- What the walk's simulation at bound `n` assumes of the programs and of
the pass's predicate on configurations (`Valid C ρ ρ' prs`: configuration
`C` may walk a term whose source environment is `ρ` and target environment
`ρ'`, given that the pairs `prs` are related; closed under growing both
environments). -/
structure Ctx (n : Nat) : Prop where
  known : Q.known = P.known
  arity : ∀ g gd, P.global? g = some gd → ∃ gd', Q.global? g = some gd' ∧ gd'.ps.length = gd.ps.length
  suffix : ∀ C ρ ρ' prs ρ₂ ρ'₂, Valid C ρ ρ' prs → ρ <:+ ρ₂ → ρ' <:+ ρ'₂ → Valid C ρ₂ ρ'₂ prs
  cknown : ∀ C ρ ρ' prs, Valid C ρ ρ' prs → C.prog.known = P.known
  cglob : ∀ C ρ ρ' prs, Valid C ρ ρ' prs → ∀ g,
    (C.prog.global? g).map (·.ps.length) = (P.global? g).map (·.ps.length)
  cbody : ∀ C ρ ρ' prs, Valid C ρ ρ' prs → ∀ g, C.inline.contains g = true → C.prog.global? g = P.global? g
  inl : ∀ C ρ ρ' prs ρ₂, Valid C ρ ρ' prs → Valid { C with inline := [], redirect := none } ρ₂ ρ' prs
  app : Rel.AppSim P Q (WV Q Valid Xc) n
  call : Rel.CallSim P Q (WV Q Valid Xc) n
  glob : Rel.GlobSim P Q (WV Q Valid Xc) n
  red : ∀ C ρ ρ' r, VOk Q Valid Xc C ρ ρ' → C.redirect = some r →
    RedSim (P := P) (Q := Q) (Valid := Valid) (Xc := Xc) n r ρ ρ'

section

variable {n : Nat} (hctx : Ctx P Q Valid Xc n)
include hctx

/-- A valid configuration stays valid as both environments grow. -/
theorem Ctx.vsuffix {ρ ρ' ρ₂ ρ'₂ : List Val} (hV : VOk Q Valid Xc C ρ ρ') (h₁ : ρ <:+ ρ₂)
    (h₂ : ρ' <:+ ρ'₂) : VOk Q Valid Xc C ρ₂ ρ'₂ :=
  VOk.suffix hctx.suffix hV h₁ h₂

theorem Ctx.vknown {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') : C.prog.known = P.known := by
  cases hV with | mk hv _ => exact hctx.cknown _ _ _ _ hv

theorem Ctx.vglob {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') (g : GlobalId) :
    (C.prog.global? g).map (·.ps.length) = (P.global? g).map (·.ps.length) := by
  cases hV with | mk hv _ => exact hctx.cglob _ _ _ _ hv g

theorem Ctx.vbody {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') (g : GlobalId)
    (hin : C.inline.contains g = true) : C.prog.global? g = P.global? g := by
  cases hV with | mk hv _ => exact hctx.cbody _ _ _ _ hv g hin

/-- An inlined callee's body is walked under a valid configuration, for
every source environment. -/
theorem Ctx.vinl {ρ ρ' : List Val} (ρ₂ : List Val) (hV : VOk Q Valid Xc C ρ ρ') :
    VOk Q Valid Xc { C with inline := [], redirect := none } ρ₂ ρ' := by
  cases hV with | mk hv hp => exact .mk (hctx.inl _ _ _ _ ρ₂ hv) hp

/-- A valid configuration stays valid when a source value is pushed. -/
theorem Ctx.push {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') (v : Val) : VOk Q Valid Xc C (v :: ρ) ρ' :=
  hctx.vsuffix hV (List.suffix_cons _ _) (List.suffix_refl _)

/-- A valid configuration stays valid when the target environment grows. -/
theorem Ctx.ext {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') :
    ∀ ρ'', ρ' <:+ ρ'' → VOk Q Valid Xc C ρ ρ'' :=
  fun _ h => hctx.vsuffix hV (List.suffix_refl _) h

/-- A recorded environment (a join point's or an inlined local function's),
valid in every extension of the target environment, with values pushed. -/
theorem Ctx.pre {ρj ρ' : List Val} (hVj : ∀ ρ'', ρ' <:+ ρ'' → VOk Q Valid Xc C ρj ρ'') (pre : List Val) :
    VOk Q Valid Xc C (pre ++ ρj) ρ' :=
  hctx.vsuffix (hVj ρ' (List.suffix_refl _)) (List.suffix_append _ _) (List.suffix_refl _)

end

end IxCC.Anf.WalkProof
