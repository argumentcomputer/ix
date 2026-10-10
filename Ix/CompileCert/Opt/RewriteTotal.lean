import Ix.CompileCert.Opt.Rewrite

/-!
# M7 L3-def: the rewrite never fails outside its named failures; its result does not depend on the fuel

* **`rwP_error`**: the rewrite fails only with one of the named failures: its own recursion bound
  (`"Pass 3 rewrite: recursion bound exhausted"`), a failure of the development (X1:
  never on simply typable input with enough fuel, `develop_total`), or a failure of the expansion lookup (an image that does not build: L2a-syn's
  totality), never otherwise;
* **`rwP_mono`**: a result at some fuel is the result at every larger fuel (the fuel is a
  resource bound, never a parameter of the result: design C-4);
* `rewriteConstP`, `rewriteConstP_faithful`: a constant rewritten expression by expression
  (`Translate.rewriteConstM`'s core: the type with no site, a definition's value at its own
  name, a theorem's proof and a recursor's rules with no site), each expression convertible to
  the original.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.Pass (Expansion)

/-! ## The development's failures -/

theorem except_bind_error {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {m : ε}
    (h : (x >>= f) = .error m) : x = .error m ∨ ∃ a, x = .ok a ∧ f a = .error m := by
  cases x with
  | error e => cases h; exact .inl rfl
  | ok a => exact .inr ⟨a, rfl, h⟩

theorem mapM_error {ε : Type} {f : Expr → Except ε Expr} {P : ε → Prop} (hf : ∀ a m, f a = .error m → P m) :
    ∀ {l : List Expr} {m : ε}, l.mapM f = .error m → P m
  | [], m, h => by simp only [List.mapM_nil, pure, Except.pure] at h; cases h
  | a :: l, m, h => by
    rw [List.mapM_cons] at h
    rcases except_bind_error h with h1 | ⟨b, -, h2⟩
    · exact hf a m h1
    · rcases except_bind_error h2 with h3 | ⟨bs, -, h4⟩
      · exact mapM_error hf h3
      · cases h4


/-! ## The rewrite's failures -/

/-- The failures the rewrite may report. -/
def RwFailure (expansion? : Name → Except String (Option Expansion)) (m : String) : Prop :=
  m = "Pass 3 rewrite: recursion bound exhausted" ∨ (∃ f args, instantiateP f args = .error m) ∨
    ∃ n, expansion? n = .error m

theorem spineP_error {expansion? : Name → Except String (Option Expansion)} {opt? : Hook} {inPlace : Bool}
    {rec : Expr → Except String Expr} {expOf : Name → Except String (Option Expansion)}
    (hrec : ∀ a m, rec a = .error m → RwFailure expansion? m)
    (hexp : ∀ n m, expOf n = .error m → RwFailure expansion? m)
    {site : Option Name} {e : Expr} {m : String} (h : spineP opt? inPlace rec expOf site e = .error m) :
    RwFailure expansion? m := by
  unfold spineP at h
  split at h
  · rename_i n us hsh args heq
    rcases except_bind_error h with h1 | ⟨xo, -, h2⟩
    · exact hexp n m h1
    · cases xo with
      | none =>
        rcases except_bind_error h2 with h3 | ⟨args', -, h4⟩
        · exact mapM_error hrec h3
        · cases h4
      | some x =>
        rcases except_bind_error h2 with h3 | ⟨args', -, h4⟩
        · exact mapM_error hrec h3
        · split at h4
          · cases h4
          · split at h4
            · cases h4
            · exact .inr (.inl ⟨_, _, h4⟩)
  · rcases except_bind_error h with h1 | ⟨h', -, h2⟩
    · exact hrec _ m h1
    · rcases except_bind_error h2 with h3 | ⟨args', -, h4⟩
      · exact mapM_error hrec h3
      · cases h4

/-- **The rewrite fails only with a named failure.** -/
theorem rwP_error {expansion? : Name → Except String (Option Expansion)} {opt? : Hook} {inPlace : Bool} :
    ∀ fuel : Nat,
    (∀ n m, expansionOfP expansion? opt? inPlace fuel n = .error m → RwFailure expansion? m) ∧
    (∀ site e m, rwP expansion? opt? inPlace fuel site e = .error m → RwFailure expansion? m)
  | 0 => ⟨fun n m h => by simp only [expansionOfP] at h; cases h; exact .inl rfl,
          fun site e m h => by simp only [rwP] at h; cases h; exact .inl rfl⟩
  | fuel + 1 => by
    have IH := rwP_error (expansion? := expansion?) (opt? := opt?) (inPlace := inPlace) fuel
    refine ⟨fun n m h => ?_, fun site e m h => ?_⟩
    · simp only [expansionOfP] at h
      rcases except_bind_error h with h1 | ⟨xo, hxo, h2⟩
      · exact .inr (.inr ⟨n, h1⟩)
      · cases xo with
        | none => cases h2
        | some x =>
          simp only at h2
          split at h2
          · rcases except_bind_error h2 with h3 | ⟨v, -, h4⟩
            · exact IH.2 none x.value m h3
            · cases h4
          · cases h2
    · cases e
      case app f a hh =>
        simp only [rwP] at h
        exact spineP_error (fun a m ha => IH.2 site a m ha) IH.1 h
      case const n us hh =>
        simp only [rwP] at h
        exact spineP_error (fun a m ha => IH.2 site a m ha) IH.1 h
      case lam n t b bi hh =>
        simp only [rwP] at h
        rcases except_bind_error h with h1 | ⟨t', -, h2⟩
        · exact IH.2 _ _ m h1
        · rcases except_bind_error h2 with h3 | ⟨b', -, h4⟩
          · exact IH.2 _ _ m h3
          · cases h4
      case forallE n t b bi hh =>
        simp only [rwP] at h
        rcases except_bind_error h with h1 | ⟨t', -, h2⟩
        · exact IH.2 _ _ m h1
        · rcases except_bind_error h2 with h3 | ⟨b', -, h4⟩
          · exact IH.2 _ _ m h3
          · cases h4
      case letE n t v b nd hh =>
        simp only [rwP] at h
        rcases except_bind_error h with h1 | ⟨t', -, h2⟩
        · exact IH.2 _ _ m h1
        · rcases except_bind_error h2 with h3 | ⟨v', -, h4⟩
          · exact IH.2 _ _ m h3
          · rcases except_bind_error h4 with h5 | ⟨b', -, h6⟩
            · exact IH.2 _ _ m h5
            · cases h6
      case proj s i x hh =>
        simp only [rwP] at h
        rcases except_bind_error h with h1 | ⟨x', -, h2⟩
        · exact IH.2 _ _ m h1
        · cases h2
      case mdata md x hh =>
        simp only [rwP] at h
        rcases except_bind_error h with h1 | ⟨x', -, h2⟩
        · exact IH.2 _ _ m h1
        · cases h2
      all_goals
        simp only [rwP] at h
        cases h

/-! ## The fuel -/

theorem except_bind_of_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (hx : x = .ok a) (hf : f a = .ok b) : (x >>= f) = .ok b := by
  rw [hx]; exact hf

theorem mapM_mono {f g : Expr → Except String Expr} (hfg : ∀ a r, f a = .ok r → g a = .ok r) :
    ∀ {l l' : List Expr}, l.mapM f = .ok l' → l.mapM g = .ok l'
  | [], l', h => by simpa only [List.mapM_nil] using h
  | a :: l, l', h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    exact except_bind_of_ok (hfg a b hb) (except_bind_of_ok (mapM_mono hfg hbs) h)

theorem spineP_mono {opt? : Hook} {inPlace : Bool} {rec rec' : Expr → Except String Expr}
    {expOf expOf' : Name → Except String (Option Expansion)}
    (hrec : ∀ a r, rec a = .ok r → rec' a = .ok r)
    (hexp : ∀ n r, expOf n = .ok r → expOf' n = .ok r)
    {site : Option Name} {e r : Expr} (h : spineP opt? inPlace rec expOf site e = .ok r) :
    spineP opt? inPlace rec' expOf' site e = .ok r := by
  unfold spineP at h ⊢
  split at h
  · rename_i n us hsh args heq
    obtain ⟨xo, hxo, h⟩ := except_bind_ok h
    refine except_bind_of_ok (hexp n xo hxo) ?_
    cases xo with
    | none =>
      obtain ⟨args', ha, h⟩ := except_bind_ok h
      exact except_bind_of_ok (mapM_mono hrec ha) h
    | some x =>
      obtain ⟨args', ha, h⟩ := except_bind_ok h
      exact except_bind_of_ok (mapM_mono hrec ha) h
  · obtain ⟨h', hh', h⟩ := except_bind_ok h
    obtain ⟨args', ha, h⟩ := except_bind_ok h
    exact except_bind_of_ok (hrec _ _ hh') (except_bind_of_ok (mapM_mono hrec ha) h)

/-- **The rewrite's result does not depend on the fuel**, once it suffices. -/
theorem rwP_mono {expansion? : Name → Except String (Option Expansion)} {opt? : Hook} {inPlace : Bool} :
    ∀ n m : Nat, n ≤ m →
    (∀ name r, expansionOfP expansion? opt? inPlace n name = .ok r →
      expansionOfP expansion? opt? inPlace m name = .ok r) ∧
    (∀ site e r, rwP expansion? opt? inPlace n site e = .ok r → rwP expansion? opt? inPlace m site e = .ok r)
  | 0, _, _ => ⟨fun _ _ h => (by simp only [expansionOfP] at h; cases h),
                fun _ _ _ h => (by simp only [rwP] at h; cases h)⟩
  | n + 1, 0, hnm => absurd hnm (by omega)
  | n + 1, m + 1, hnm => by
    have IH := rwP_mono (expansion? := expansion?) (opt? := opt?) (inPlace := inPlace) n m (by omega)
    refine ⟨fun name r h => ?_, fun site e r h => ?_⟩
    · simp only [expansionOfP] at h ⊢
      obtain ⟨xo, hxo, h⟩ := except_bind_ok h
      refine except_bind_of_ok hxo ?_
      cases xo with
      | none => exact h
      | some x =>
        simp only at h ⊢
        split at h
        · rename_i hnr
          simp only [hnr, ↓reduceIte]
          obtain ⟨v, hv, h⟩ := except_bind_ok h
          exact except_bind_of_ok (IH.2 none x.value v hv) h
        · rename_i hnr
          simp only [hnr, Bool.false_eq_true, ↓reduceIte]
          exact h
    · cases e
      case app f a hh =>
        simp only [rwP] at h ⊢
        exact spineP_mono (fun a r ha => IH.2 site a r ha) IH.1 h
      case const c us hh =>
        simp only [rwP] at h ⊢
        exact spineP_mono (fun a r ha => IH.2 site a r ha) IH.1 h
      case lam nm t b bi hh =>
        simp only [rwP] at h ⊢
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        exact except_bind_of_ok (IH.2 _ _ _ ht) (except_bind_of_ok (IH.2 _ _ _ hb) h)
      case forallE nm t b bi hh =>
        simp only [rwP] at h ⊢
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        exact except_bind_of_ok (IH.2 _ _ _ ht) (except_bind_of_ok (IH.2 _ _ _ hb) h)
      case letE nm t v b nd hh =>
        simp only [rwP] at h ⊢
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨v', hv, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        exact except_bind_of_ok (IH.2 _ _ _ ht) (except_bind_of_ok (IH.2 _ _ _ hv)
          (except_bind_of_ok (IH.2 _ _ _ hb) h))
      case proj s i x hh =>
        simp only [rwP] at h ⊢
        obtain ⟨x', hx, h⟩ := except_bind_ok h
        exact except_bind_of_ok (IH.2 _ _ _ hx) h
      case mdata md x hh =>
        simp only [rwP] at h ⊢
        obtain ⟨x', hx, h⟩ := except_bind_ok h
        exact except_bind_of_ok (IH.2 _ _ _ hx) h
      all_goals
        simp only [rwP] at h ⊢
        exact h


/-! ## A constant -/

/-- `Translate.rewriteConstM`'s core: every expression of a constant rewritten, the value of a
definition at its own name (the one site of the proof-justified passes). -/
def rewriteConstP (expansion? : Name → Except String (Option Expansion)) (opt? : Hook) (inPlace : Bool)
    (ci : ConstantInfo) : Except String ConstantInfo :=
  let go := rwP expansion? opt? inPlace Ix.Compile.Pass.rewriteFuel
  let cnst (c : Ix.ConstantVal) : Except String Ix.ConstantVal := do pure { c with type := ← go none c.type }
  match ci with
  | .axiomInfo v => do pure (.axiomInfo { v with cnst := ← cnst v.cnst })
  | .defnInfo v => do
    let c ← cnst v.cnst
    let value ← go (some v.cnst.name) v.value
    pure (.defnInfo { v with cnst := c, value })
  | .thmInfo v => do
    let c ← cnst v.cnst
    pure (.thmInfo { v with cnst := c, value := ← go none v.value })
  | .opaqueInfo v => do
    let c ← cnst v.cnst
    pure (.opaqueInfo { v with cnst := c, value := ← go none v.value })
  | .quotInfo v => do pure (.quotInfo { v with cnst := ← cnst v.cnst })
  | .inductInfo v => do pure (.inductInfo { v with cnst := ← cnst v.cnst })
  | .ctorInfo v => do pure (.ctorInfo { v with cnst := ← cnst v.cnst })
  | .recInfo v => do
    let c ← cnst v.cnst
    let rules ← v.rules.toList.mapM fun r => do pure { r with rhs := ← go none r.rhs }
    pure (.recInfo { v with cnst := c, rules := rules.toArray })

theorem cnst_type {go : Option Name → Expr → Except String Expr} {c c' : Ix.ConstantVal}
    (h : (do pure { c with type := ← go none c.type } : Except String Ix.ConstantVal) = .ok c') :
    ∃ t, go none c.type = .ok t ∧ c' = { c with type := t } := by
  obtain ⟨t, ht, h⟩ := except_bind_ok h
  exact ⟨t, ht, (except_pure_ok' h).symm⟩

/-- **A rewritten constant**: its type converts to the original's, and so does the value of a
definition. -/
theorem rewriteConstP_faithful {Γ : Env} {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hlv : LevelClosed Γ) (hF : HookFaithful Γ opt?) (hS : HookSiteStable opt?)
    {ci ci' : ConstantInfo} (h : rewriteConstP expansion? opt? false ci = .ok ci') :
    ExprConv Γ ci'.getCnst.type ci.getCnst.type ∧
    (∀ v v', ci = .defnInfo v → ci' = .defnInfo v' → ExprConv Γ v'.value v.value) := by
  have hrw := fun site e r (h : rwP expansion? opt? false Ix.Compile.Pass.rewriteFuel site e = .ok r) =>
    (rwP_faithful hH hlv hF hS Ix.Compile.Pass.rewriteFuel).2 site e r h
  unfold rewriteConstP at h
  cases ci with
  | defnInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨val, hval, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    refine ⟨hrw _ _ _ ht, ?_⟩
    intro w w' hw hw'
    cases hw
    cases hw'
    exact hrw _ _ _ hval
  | thmInfo v | opaqueInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨val, -, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩
  | recInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨rules, -, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩
  | axiomInfo v | quotInfo v | inductInfo v | ctorInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩

end Ix.CompileCert.Opt

