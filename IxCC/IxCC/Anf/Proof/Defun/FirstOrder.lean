import IxCC.Anf.Defun
import IxCC.Src.Proof.NatMap
import IxCC.Anf.WellFormed

/-! # P8's output is first order

`Defun.Proof.run_firstOrder`: every program P8 returns is `Anf.FirstOrder`,
the fragment `Fir.lower` accepts. The walk leaves no `fn` and no `app`, and
keeps a `glob` only of a CAF or of an absent id below the input's size; both
keep that arity in the output, whose dispatchers and lifted functions come
after the input's ids (`keeps_assemble`). Renaming variables changes none of
this (`renameVars_fo`), and the dispatchers are made of `case`, `call`, `con`
and `ret` (`dispatcher_fo`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-! ## `Except`, maps and lists -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b := by
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact h

theorem throw_ok {ε α : Type} {e : ε} {a : α} (h : (throw e : Except ε α) = .ok a) : False := by
  cases h

theorem foldl_insert_mem {α : Type} : ∀ (xs : List (Nat × α)) (m : Src.NatMap α) {k : Nat} {x : α},
    (xs.foldl (fun m p => m.insert p.1 p.2) m).get? k = some x → (k, x) ∈ xs ∨ m.get? k = some x
  | [], _, _, _, h => .inr h
  | (k₀, x₀) :: xs, m, k, x, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insert_mem xs _ h with h' | h'
    · exact .inl (List.mem_cons_of_mem _ h')
    · rw [Src.NatMap.get?_insert] at h'
      by_cases hk : k = k₀
      · subst hk
        rw [if_pos rfl] at h'
        cases h'
        exact .inl List.mem_cons_self
      · rw [if_neg hk] at h'
        exact .inr h'

/-- Every entry of a map built from a list comes from the list. -/
theorem ofList_mem {α : Type} {xs : List (Nat × α)} {k : Nat} {x : α}
    (h : (Src.NatMap.ofList xs).get? k = some x) : (k, x) ∈ xs := by
  rcases foldl_insert_mem xs .leaf h with h' | h'
  · exact h'
  · simp [Src.NatMap.get?] at h'

theorem mem_globalList {P : Program} {g : GlobalId} {gd : GDef} :
    (g, gd) ∈ P.globalList ↔ g < P.size ∧ P.global? g = some gd := by
  unfold Program.globalList
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨g', hg', gd', hgd, rfl, rfl⟩
    exact ⟨hg', hgd⟩
  · rintro ⟨hg, hgd⟩
    exact ⟨g, hg, gd, hgd, rfl, rfl⟩

theorem mem_numbered {α : Type} : ∀ {k : Nat} {xs : List α} {i : Nat} {x : α},
    (i, x) ∈ numbered k xs → x ∈ xs ∧ k ≤ i
  | _, [], _, _, h => by simp [numbered] at h
  | k, y :: ys, i, x, h => by
    simp only [numbered, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self, Nat.le_refl _⟩
    · obtain ⟨h1, h2⟩ := mem_numbered h
      exact ⟨List.mem_cons_of_mem _ h1, by omega⟩

/-! ## Renaming keeps first order -/

mutual

theorem renameVars_fo (isFn : GlobalId → Bool) (f : Nat → Nat) :
    ∀ (d : Nat) (e : Exp), Exp.firstOrder isFn (Exp.renameVars f d e) = Exp.firstOrder isFn e
  | d, .bind c b e => by
    simp only [Exp.renameVars, Exp.firstOrder, renameBind_fo isFn f d b, renameVars_fo isFn f (d + 1) e]
  | d, .join n r b e => by
    simp only [Exp.renameVars, Exp.firstOrder, renameVars_fo isFn f (d + n) b, renameVars_fo isFn f d e]
  | _, .jump _ _ => by simp only [Exp.renameVars, Exp.firstOrder]
  | d, .case x alts dft => by
    simp only [Exp.renameVars, Exp.firstOrder, renameAlts_fo isFn f d alts, renameOpt_fo isFn f d dft]
  | _, .ret _ => by simp only [Exp.renameVars, Exp.firstOrder]
  | d, .tick e => by simp only [Exp.renameVars, Exp.firstOrder, renameVars_fo isFn f d e]
  | _, .trap => by simp only [Exp.renameVars, Exp.firstOrder]

theorem renameBind_fo (isFn : GlobalId → Bool) (f : Nat → Nat) :
    ∀ (d : Nat) (b : Bind), Bind.firstOrder isFn (Bind.renameVars f d b) = Bind.firstOrder isFn b
  | _, .atom _ => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .con .. => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .proj .. => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .prim .. => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .glob _ => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .call .. => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .app .. => by simp only [Bind.renameVars, Bind.firstOrder]
  | _, .fn .. => by simp only [Bind.renameVars, Bind.firstOrder]

theorem renameAlts_fo (isFn : GlobalId → Bool) (f : Nat → Nat) :
    ∀ (d : Nat) (alts : List Alt),
      Exp.altsFirstOrder isFn (Exp.renameAlts f d alts) = Exp.altsFirstOrder isFn alts
  | _, [] => by simp only [Exp.renameAlts, Exp.altsFirstOrder]
  | d, .mk k n b :: as => by
    simp only [Exp.renameAlts, Exp.altsFirstOrder, renameVars_fo isFn f (d + n) b,
      renameAlts_fo isFn f d as]

theorem renameOpt_fo (isFn : GlobalId → Bool) (f : Nat → Nat) :
    ∀ (d : Nat) (o : Option Exp), Exp.optFirstOrder isFn (Exp.renameOpt f d o) = Exp.optFirstOrder isFn o
  | _, none => by simp only [Exp.renameOpt, Exp.optFirstOrder]
  | d, some e => by simp only [Exp.renameOpt, Exp.optFirstOrder, renameVars_fo isFn f d e]

end

/-! ## The walk -/

/-- The output's `isFn` is false at every `glob` the walk keeps: below the
input's size, a CAF or an absent id. -/
def Keeps (isFn : GlobalId → Bool) (P : Program) : Prop :=
  ∀ h, h < P.size → (∀ hd, P.global? h = some hd → hd.ps = [] → isFn h = false) ∧
    (P.global? h = none → isFn h = false)

/-- Every lifted body so far is first order. -/
def AccFO (isFn : GlobalId → Bool) (acc : Acc) : Prop := ∀ l ∈ acc.lifted, l.body.firstOrder isFn = true

mutual

theorem exp_fo {isFn : GlobalId → Bool} {C : Ctx} (hC : Keeps isFn C.prog) :
    ∀ (Γ : Nat) (acc : Acc) (e : Exp) (e' : Exp) (acc' : Acc), AccFO isFn acc →
      Defun.exp C Γ acc e = .ok (e', acc') → e'.firstOrder isFn = true ∧ AccFO isFn acc'
  | Γ, acc, .bind c b e, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨hb1, ha1⟩ := bind_fo hC Γ acc b b' acc1 ha hb
    obtain ⟨he1, ha2⟩ := exp_fo hC (Γ + 1) acc1 e e1 acc2 ha1 he
    exact ⟨by simp only [Exp.firstOrder, hb1, he1, Bool.and_self], ha2⟩
  | Γ, acc, .join n r b e, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨hb1, ha1⟩ := exp_fo hC (Γ + n) acc b b' acc1 ha hb
    obtain ⟨he1, ha2⟩ := exp_fo hC Γ acc1 e e1 acc2 ha1 he
    exact ⟨by simp only [Exp.firstOrder, hb1, he1, Bool.and_self], ha2⟩
  | _, acc, .jump j as, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Exp.firstOrder], ha⟩
  | Γ, acc, .case x as d, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨as', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨d', acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨hb1, ha1⟩ := alts_fo hC Γ acc as as' acc1 ha hb
    obtain ⟨he1, ha2⟩ := opt_fo hC Γ acc1 d d' acc2 ha1 he
    exact ⟨by simp only [Exp.firstOrder, hb1, he1, Bool.and_self], ha2⟩
  | _, acc, .ret a, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Exp.firstOrder], ha⟩
  | Γ, acc, .tick e, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨he1, ha1⟩ := exp_fo hC Γ acc e e1 acc1 ha he
    exact ⟨by simp only [Exp.firstOrder, he1], ha1⟩
  | _, acc, .trap, e', acc', ha, h => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Exp.firstOrder], ha⟩

theorem bind_fo {isFn : GlobalId → Bool} {C : Ctx} (hC : Keeps isFn C.prog) :
    ∀ (Γ : Nat) (acc : Acc) (b : Bind) (b' : Bind) (acc' : Acc), AccFO isFn acc →
      Defun.bind C Γ acc b = .ok (b', acc') → b'.firstOrder isFn = true ∧ AccFO isFn acc'
  | _, acc, .glob g, b', acc', ha, h => by
    simp only [Defun.bind] at h
    by_cases hlt : g < C.prog.size
    · rw [if_pos hlt] at h
      cases hg : C.prog.global? g with
      | some hd =>
        simp only [hg] at h
        cases hps : hd.ps with
        | nil =>
          simp only [hps] at h
          obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq1, ← hq2]
          exact ⟨by simp only [Bind.firstOrder, (hC g hlt).1 hd hg hps, Bool.not_false], ha⟩
        | cons p ps =>
          simp only [hps] at h
          obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq1, ← hq2]
          exact ⟨by simp only [Bind.firstOrder], ha⟩
      | none =>
        simp only [hg] at h
        obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
        rw [← hq1, ← hq2]
        exact ⟨by simp only [Bind.firstOrder, (hC g hlt).2 hg, Bool.not_false], ha⟩
    · rw [if_neg hlt] at h
      exact (throw_ok h).elim
  | _, acc, .app f as, b', acc', ha, h => by
    simp only [Defun.bind] at h
    cases as with
    | nil =>
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      exact ⟨by simp only [Bind.firstOrder], ha⟩
    | cons a as =>
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      exact ⟨by simp only [Bind.firstOrder], ha⟩
  | Γ, acc, .fn ps fb, b', acc', ha, h => by
    cases ps with
    | nil =>
      simp only [Defun.bind] at h
      exact (throw_ok h).elim
    | cons p ps =>
      simp only [Defun.bind] at h
      obtain ⟨⟨fb', acc1⟩, hb, h⟩ := bind_ok h
      dsimp only at h
      split at h
      case isFalse => exact (throw_ok h).elim
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      obtain ⟨hb1, ha1⟩ := exp_fo hC _ acc fb fb' acc1 ha hb
      refine ⟨by simp only [Bind.firstOrder], ?_⟩
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp only [renameVars_fo, hb1]
      · exact ha1 l hl
  | _, acc, .atom _, b', acc', ha, h => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Bind.firstOrder], ha⟩
  | _, acc, .con .., b', acc', ha, h => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Bind.firstOrder], ha⟩
  | _, acc, .proj .., b', acc', ha, h => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Bind.firstOrder], ha⟩
  | _, acc, .prim .., b', acc', ha, h => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Bind.firstOrder], ha⟩
  | _, acc, .call .., b', acc', ha, h => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Bind.firstOrder], ha⟩

theorem alts_fo {isFn : GlobalId → Bool} {C : Ctx} (hC : Keeps isFn C.prog) :
    ∀ (Γ : Nat) (acc : Acc) (as : List Alt) (as' : List Alt) (acc' : Acc), AccFO isFn acc →
      Defun.alts C Γ acc as = .ok (as', acc') → Exp.altsFirstOrder isFn as' = true ∧ AccFO isFn acc'
  | _, acc, [], as', acc', ha, h => by
    simp only [Defun.alts] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Exp.altsFirstOrder], ha⟩
  | Γ, acc, .mk k n b :: as, as', acc', ha, h => by
    simp only [Defun.alts] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨as1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨hb1, ha1⟩ := exp_fo hC (Γ + n) acc b b' acc1 ha hb
    obtain ⟨he1, ha2⟩ := alts_fo hC Γ acc1 as as1 acc2 ha1 he
    exact ⟨by simp only [Exp.altsFirstOrder, hb1, he1, Bool.and_self], ha2⟩

theorem opt_fo {isFn : GlobalId → Bool} {C : Ctx} (hC : Keeps isFn C.prog) :
    ∀ (Γ : Nat) (acc : Acc) (o : Option Exp) (o' : Option Exp) (acc' : Acc), AccFO isFn acc →
      Defun.opt C Γ acc o = .ok (o', acc') → Exp.optFirstOrder isFn o' = true ∧ AccFO isFn acc'
  | _, acc, none, o', acc', ha, h => by
    simp only [Defun.opt] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨by simp only [Exp.optFirstOrder], ha⟩
  | Γ, acc, some e, o', acc', ha, h => by
    simp only [Defun.opt] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    obtain ⟨he1, ha1⟩ := exp_fo hC Γ acc e e1 acc1 ha he
    exact ⟨by simp only [Exp.optFirstOrder, he1], ha1⟩

end

theorem global_fo {isFn : GlobalId → Bool} {P : Program} (hP : Keeps isFn P) {g : GlobalId} {gd gd' : GDef}
    {acc acc' : Acc} (ha : AccFO isFn acc) (h : Defun.global P g gd acc = .ok (gd', acc')) :
    gd'.body.firstOrder isFn = true ∧ AccFO isFn acc' := by
  simp only [Defun.global] at h
  obtain ⟨⟨body, acc1⟩, hb, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
  rw [← hq1, ← hq2]
  exact exp_fo (C := { prog := P, g, key := gd.key }) hP gd.ps.length { acc with next := 0 } gd.body body acc1
    ha hb

theorem global_ps {P : Program} {g : GlobalId} {gd gd' : GDef} {acc acc' : Acc}
    (h : Defun.global P g gd acc = .ok (gd', acc')) : gd'.ps = gd.ps := by
  simp only [Defun.global] at h
  obtain ⟨⟨body, acc1⟩, -, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨hq1, -⟩ := Prod.mk.inj (pure_ok h)
  rw [← hq1]

/-- The rewritten globals keep their ids and parameters. -/
theorem globalsGo_ps {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {acc' : Acc} {parents' : List GlobalId},
    (∀ g gd', (g, gd') ∈ out → ∃ gd, P.global? g = some gd ∧ g < P.size ∧ gd'.ps = gd.ps) →
    (∀ g gd, (g, gd) ∈ l → P.global? g = some gd ∧ g < P.size) →
    globalsGo P l acc parents out = .ok (gs, acc', parents') →
    ∀ g gd', (g, gd') ∈ gs → ∃ gd, P.global? g = some gd ∧ g < P.size ∧ gd'.ps = gd.ps
  | [], _, _, out, gs, _, _, hout, _, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    intro g gd' hx
    exact hout g gd' (List.mem_reverse.1 hx)
  | (g, gd) :: rest, acc, parents, out, gs, acc', parents', hout, hl, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      refine globalsGo_ps rest acc1 _ ((g, gd') :: out) (fun g₁ gd₁ hx => ?_)
        (fun g₁ gd₁ hx => hl g₁ gd₁ (List.mem_cons_of_mem _ hx)) h
      rcases List.mem_cons.1 hx with he | hx
      · simp only [Prod.mk.injEq] at he
        rw [he.1, he.2]
        obtain ⟨hgd, hlt⟩ := hl g gd List.mem_cons_self
        exact ⟨gd, hgd, hlt, global_ps hg⟩
      · exact hout g₁ gd₁ hx

/-- The rewritten globals and the lifted bodies are first order. -/
theorem globalsGo_fo {isFn : GlobalId → Bool} {P : Program} (hP : Keeps isFn P) :
    ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {acc' : Acc} {parents' : List GlobalId},
    AccFO isFn acc → (∀ g gd', (g, gd') ∈ out → gd'.body.firstOrder isFn = true) →
    globalsGo P l acc parents out = .ok (gs, acc', parents') →
    AccFO isFn acc' ∧ ∀ g gd', (g, gd') ∈ gs → gd'.body.firstOrder isFn = true
  | [], acc, _, out, gs, acc', _, ha, hout, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨ha, fun g gd' hx => hout g gd' (List.mem_reverse.1 hx)⟩
  | (g, gd) :: rest, acc, parents, out, gs, acc', parents', ha, hout, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      obtain ⟨hb, ha1⟩ := global_fo hP ha hg
      refine globalsGo_fo hP rest acc1 _ ((g, gd') :: out) ha1 (fun g₁ gd₁ hx => ?_) h
      rcases List.mem_cons.1 hx with he | hx
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hb
      · exact hout g₁ gd₁ hx

/-! ## The dispatchers -/

theorem altBody_fo (isFn : GlobalId → Bool) (size : Nat) (s : Source) (j m : Nat) :
    (altBody size s j m).firstOrder isFn = true := by
  by_cases h1 : m = s.arity - j <;> by_cases h2 : m < s.arity - j <;>
    simp [altBody, h1, h2, Exp.firstOrder, Bind.firstOrder]

theorem altsFirstOrder_append (isFn : GlobalId → Bool) :
    ∀ (as bs : List Alt), Exp.altsFirstOrder isFn (as ++ bs) =
      (Exp.altsFirstOrder isFn as && Exp.altsFirstOrder isFn bs)
  | [], _ => by simp only [List.nil_append, Exp.altsFirstOrder, Bool.true_and]
  | .mk _ _ b :: as, bs => by
    simp only [List.cons_append, Exp.altsFirstOrder, altsFirstOrder_append isFn as bs, Bool.and_assoc]

theorem keyAlts_fo (isFn : GlobalId → Bool) (size : Nat) (s : Source) (m : Nat) :
    ∀ js : List Nat, Exp.altsFirstOrder isFn
      (js.map fun j => Alt.mk (.clo s.key j) (s.caps + j) (altBody size s j m)) = true
  | [] => by simp only [List.map_nil, Exp.altsFirstOrder]
  | j :: js => by
    simp only [List.map_cons, Exp.altsFirstOrder, altBody_fo, keyAlts_fo isFn size s m js, Bool.and_self]

theorem dispAlts_fo (isFn : GlobalId → Bool) (size m : Nat) :
    ∀ srcs : List Source, Exp.altsFirstOrder isFn (dispAlts size m srcs) = true
  | [] => by simp only [dispAlts, Exp.altsFirstOrder]
  | s :: ss => by
    simp only [dispAlts, altsFirstOrder_append, keyAlts_fo, dispAlts_fo isFn size m ss, Bool.and_self]

theorem dispatcher_fo (isFn : GlobalId → Bool) (size : Nat) (srcs : List Source) (m : Nat) :
    (dispatcher size srcs m).body.firstOrder isFn = true := by
  simp only [dispatcher, Exp.firstOrder, dispAlts_fo, Exp.optFirstOrder, Bool.and_self]

/-! ## The program -/

/-- What a successful run is made of. -/
theorem run_ok {P q : Program} (h : run P = .ok q) :
    ∃ gs acc parents, globalsGo P P.globalList {} [] [] = .ok (gs, acc, parents) ∧ q = assemble P gs acc := by
  simp only [run] at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨⟨gs, acc, parents⟩, hgo, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok h
  exact ⟨gs, acc, parents, hgo, (pure_ok h).symm⟩

/-- An entry of the output's global map: a rewritten global, a dispatcher
(at the input's size and above) or a lifted function (above the
dispatchers). -/
theorem assemble_mem {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {g : GlobalId} {gd : GDef}
    (h : (assemble P gs acc).global? g = some gd) :
    (g, gd) ∈ gs ∨ (P.size ≤ g ∧ ∃ m, gd = dispatcher P.size (sources P acc) m) ∨
      (P.size ≤ g ∧ ∃ l ∈ acc.lifted, gd = l.toGDef) := by
  have hm := ofList_mem h
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact .inl hm
  · obtain ⟨i, -, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .inr (.inl ⟨Nat.le_add_right _ _, _, rfl⟩)
  · obtain ⟨⟨i, l⟩, hli, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hl, hle⟩ := mem_numbered hli
    refine .inr (.inr ⟨?_, l, List.mem_reverse.1 hl, rfl⟩)
    unfold liftBase at hle
    omega

/-- The output keeps every CAF below the input's size a CAF, and every absent
id below it absent. -/
theorem keeps_assemble {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc}
    (hgs : ∀ g gd', (g, gd') ∈ gs → ∃ gd, P.global? g = some gd ∧ g < P.size ∧ gd'.ps = gd.ps) :
    Keeps (fun g => ((assemble P gs acc).arity? g).any (· > 0)) P := by
  intro h hlt
  refine ⟨fun hd hhd hps => ?_, fun hnone => ?_⟩
  · simp only [Program.arity?]
    cases hq : (assemble P gs acc).global? h with
    | none => rfl
    | some gd =>
      rcases assemble_mem hq with hm | ⟨hle, -⟩ | ⟨hle, -⟩
      · obtain ⟨gd0, hgd0, -, hps'⟩ := hgs _ _ hm
        rw [hhd] at hgd0
        cases hgd0
        simp [GDef.arity, hps', hps]
      · omega
      · omega
  · simp only [Program.arity?]
    cases hq : (assemble P gs acc).global? h with
    | none => rfl
    | some gd =>
      rcases assemble_mem hq with hm | ⟨hle, -⟩ | ⟨hle, -⟩
      · obtain ⟨gd0, hgd0, -, -⟩ := hgs _ _ hm
        rw [hnone] at hgd0
        cases hgd0
      · omega
      · omega

/-- **P8's output is first order**: `Anf.FirstOrder`, what `Fir.lower`
accepts. -/
theorem run_firstOrder {P q : Program} (h : run P = .ok q) : firstOrder q = true := by
  obtain ⟨gs, acc, parents, hgo, rfl⟩ := run_ok h
  have hgs := globalsGo_ps P.globalList {} [] [] (by simp) (fun g gd hx => by
    obtain ⟨hlt, hgd⟩ := mem_globalList.1 hx
    exact ⟨hgd, hlt⟩) hgo
  have hK := keeps_assemble (acc := acc) hgs
  obtain ⟨hacc, hfo⟩ := globalsGo_fo hK P.globalList {} [] [] (by simp [AccFO]) (by simp) hgo
  unfold firstOrder
  simp only [List.all_eq_true]
  intro ⟨g, gd⟩ hmem
  have hq := (mem_globalList.1 hmem).2
  dsimp only
  rcases assemble_mem hq with hm | ⟨-, m, rfl⟩ | ⟨-, l, hl, rfl⟩
  · exact hfo _ _ hm
  · exact dispatcher_fo _ _ _ _
  · exact hacc l hl

theorem defun_firstOrder {P q : Program} (h : Anf.defun P = .ok q) : Anf.FirstOrder q := by
  unfold Anf.defun at h
  cases hr : run P with
  | error e => rw [hr] at h; cases h
  | ok q' =>
    rw [hr] at h
    cases h
    exact run_firstOrder hr

end IxCC.Anf.Defun.Proof
