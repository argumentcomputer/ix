import IxCC.Anf.Proof.Defun.Assemble
import IxCC.Anf.Proof.Defun.Rel
import IxCC.Anf.Proof.Defun.Rename

/-! # P8's walk is the translation

The walk's image of each input global's body is related to it by the
translation relation `Tr` (`docs/closures-design.md`, "Proof obligation"), in
the setting of the assembled program (`setting`): the closure sources, the
output and its dispatchers (`exp_tr`, `global_tr`). What the relation needs of
the walk's final state (`Final`: every lifted function is a closure source
whose global sits at its id, every escape is a source, the dispatchers cover
every arity) holds of a successful run (`final_ran`), so a run fixes a valid
setting (`Valid`, `ran_valid`, `run_valid`) with the input's globals at their
ids with translated bodies, absent ids absent, the dispatchers at `dispId` and
distinct source keys.

The same walk lemma carries scoping: the image of a well-scoped expression is
well scoped in the output (`tr_ws`, given what scoping reads from the output,
`SigOk`), and the local functions it lifts have well-scoped bodies (`LWS`),
by the scoping core of λ-lifting (`lifted_ws`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-! ## The walk is the translation -/

/-- What the translation relation needs of the walk's final state: each
lifted function is a closure source whose global is at its id, each escape
is a closure source, and the dispatchers cover every arity. -/
structure Final (X : Setting) (accF : Acc) : Prop where
  lifted : ∀ l ∈ accF.lifted, ∃ s ∈ X.srcs, s.key = l.key ∧ s.caps = l.ncaps ∧ s.arity = l.ps.length ∧
    X.Q.global? s.id = some l.toGDef
  escapes : ∀ h hd, accF.escapes.contains h = true → h < X.P.size → X.P.global? h = some hd →
    ({ key := hd.key, id := h, caps := 0, arity := hd.ps.length } : Source) ∈ X.srcs
  maxApp : accF.maxApp ≤ X.M

theorem natSet_contains_insert_self (s : Src.NatSet) (h : Nat) : (s.insert h).contains h = true := by
  unfold Src.NatSet.insert Src.NatMap.contains
  rw [Src.NatMap.get?_insert_self]
  rfl


/-! ## The translation keeps scope -/

/-- What scoping reads from P8's output: the input's constructors and
globals keep their arities, the size grows, every closure key has its
source's captures and supplied arguments as fields, and the dispatcher of
arity `m` takes the callee and `m` arguments. -/
structure SigOk (X : Setting) : Prop where
  ctor : ∀ c n, X.P.sig.ctorArity? c = some n → X.Q.sig.ctorArity? c = some n
  arity : ∀ g n, X.P.sig.arity? g = some n → X.Q.sig.arity? g = some n
  size : X.P.size ≤ X.Q.size
  clo : ∀ s ∈ X.srcs, ∀ j, j < s.arity → X.Q.sig.ctorArity? (.clo s.key j) = some (s.caps + j)
  disp : ∀ m, 1 ≤ m → m ≤ X.M → X.Q.sig.arity? (X.dispId m) = some (m + 1)

theorem wsList_vars {Γ : Nat} : ∀ {xs : List Nat}, (∀ x ∈ xs, x < Γ) → Atom.WSList Γ (xs.map .var)
  | [], _ => trivial
  | x :: _, h => ⟨h x List.mem_cons_self, wsList_vars fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem projOk_mono {S S' : Sig} (h : ∀ c n, S.ctorArity? c = some n → S'.ctorArity? c = some n)
    {c : Key.CtorKey} {i : Nat} (hp : projOk S c i = true) : projOk S' c i = true := by
  unfold projOk at hp ⊢
  cases hc : S.ctorArity? c with
  | none => rw [hc] at hp; cases hp
  | some n => rw [hc] at hp; rw [h c n hc]; exact hp

theorem trAlts_keys {X : Setting} : ∀ {Γ : Nat} {alts alts' : List Alt}, TrAlts X Γ alts alts' →
    altKeys alts' = altKeys alts
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp only [altKeys, trAlts_keys h]

section

variable {X : Setting}

mutual

/-- The image of a well-scoped expression is well scoped in the output. -/
theorem tr_ws (hS : SigOk X) : ∀ {Γ : Nat} {Δ : List Nat} {e e' : Exp}, Tr X Γ e e' → Exp.WS X.P.sig Γ Δ e →
    Exp.WS X.Q.sig Γ Δ e'
  | _, _, _, _, .bind hb he, h => ⟨trB_ws hS hb h.1, tr_ws hS he h.2⟩
  | _, _, _, _, .join hb he, h => ⟨tr_ws hS hb h.1, tr_ws hS he h.2⟩
  | _, _, _, _, .jump, h => h
  | _, _, _, _, .case ha ho, h => ⟨h.1, trAlts_ws hS ha h.2.1, by rw [trAlts_keys ha]; exact h.2.2.1, trOpt_ws hS ho h.2.2.2⟩
  | _, _, _, _, .ret, h => h
  | _, _, _, _, .tick he, h => by have := tr_ws hS he h; exact this
  | _, _, _, _, .trap, h => h

theorem trB_ws (hS : SigOk X) : ∀ {Γ : Nat} {b b' : Bind}, TrB X Γ b b' → Bind.WS X.P.sig Γ b → Bind.WS X.Q.sig Γ b'
  | _, _, _, .atom, h => h
  | _, _, _, .con, h => ⟨hS.ctor _ _ h.1, h.2⟩
  | _, _, _, .proj, h => ⟨projOk_mono hS.ctor h.1, h.2⟩
  | _, _, _, .prim, h => h
  | _, _, _, .call, h => ⟨hS.arity _ _ h.1, h.2.1, h.2.2⟩
  | _, _, _, .caf .., h => Nat.lt_of_lt_of_le h hS.size
  | _, _, _, .absent .., h => Nat.lt_of_lt_of_le h hS.size
  | _, _, _, .glob _ _ hps hs, _ => by
    refine ⟨?_, trivial⟩
    have := hS.clo _ hs 0 (List.length_pos_iff.2 hps)
    simpa using this
  | _, _, _, .app0, h => absurd rfl h.2.1
  | _, _, _, .app hne hm, h => by
    refine ⟨?_, List.cons_ne_nil _ _, h.1, h.2.2⟩
    have := hS.disp _ (List.length_pos_iff.2 hne) hm
    simpa using this
  | _, _, _, .fn (Γ := Γ) (b' := b') hps _ hfree hs hcaps harity _ _ _, _ => by
    refine ⟨?_, wsList_vars fun x hx => captures_lt hx⟩
    have := hS.clo _ hs 0 (by rw [harity]; exact List.length_pos_iff.2 hps)
    rw [hcaps] at this
    simpa using this

theorem trAlts_ws (hS : SigOk X) : ∀ {Γ : Nat} {Δ : List Nat} {alts alts' : List Alt}, TrAlts X Γ alts alts' →
    Exp.AltsWS X.P.sig Γ Δ alts → Exp.AltsWS X.Q.sig Γ Δ alts'
  | _, _, _, _, .nil, _ => trivial
  | _, _, _, _, .cons hb ha, h => ⟨hS.ctor _ _ h.1, tr_ws hS hb h.2.1, trAlts_ws hS ha h.2.2⟩

theorem trOpt_ws (hS : SigOk X) : ∀ {Γ : Nat} {Δ : List Nat} {o o' : Option Exp}, TrOpt X Γ o o' →
    Exp.OptWS X.P.sig Γ Δ o → Exp.OptWS X.Q.sig Γ Δ o'
  | _, _, _, _, .none, _ => trivial
  | _, _, _, _, .some he, h => tr_ws hS he h

end

end

/-! ## The walk is the translation -/

/-- Every lifted function so far has a body well scoped over its captures
and its parameters, in the output. -/
def LWS (X : Setting) (acc : Acc) : Prop :=
  ∀ l ∈ acc.lifted, l.body.WS X.Q.sig (l.ncaps + l.ps.length) []

section

variable {X : Setting} {accF : Acc} {C : Ctx}

mutual

/-- **The walk is the translation**: its image of an expression is related
to it by `Tr`, and when the expression is well scoped, the local functions it
lifts have well-scoped bodies. -/
theorem exp_tr (hF : Final X accF) (hC : C.prog = X.P) : ∀ (Γ : Nat) (acc : Acc) (e : Exp) (e' : Exp) (acc' : Acc),
    Defun.exp C Γ acc e = .ok (e', acc') → AccLe acc' accF →
    Tr X Γ e e' ∧ (SigOk X → ∀ Δ, Exp.WS X.P.sig Γ Δ e → LWS X acc → LWS X acc')
  | Γ, acc, .bind c b e, e', acc', h, hle => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    have h1 := (exp_grows (Γ + 1) acc1 e e1 acc2 he).le.trans hle
    obtain ⟨tb, wb⟩ := bind_tr hF hC Γ acc b b' acc1 hb h1
    obtain ⟨te, we⟩ := exp_tr hF hC (Γ + 1) acc1 e e1 acc2 he hle
    exact ⟨.bind tb te, fun hS Δ hws hl => we hS Δ hws.2 (wb hS hws.1 hl)⟩
  | Γ, acc, .join n r b e, e', acc', h, hle => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    have h1 := (exp_grows Γ acc1 e e1 acc2 he).le.trans hle
    obtain ⟨tb, wb⟩ := exp_tr hF hC (Γ + n) acc b b' acc1 hb h1
    obtain ⟨te, we⟩ := exp_tr hF hC Γ acc1 e e1 acc2 he hle
    exact ⟨.join tb te, fun hS Δ hws hl => we hS _ hws.2 (wb hS _ hws.1 hl)⟩
  | _, acc, .jump j as, e', acc', h, _ => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.jump, fun _ _ _ hl => hl⟩
  | Γ, acc, .case x as d, e', acc', h, hle => by
    simp only [Defun.exp] at h
    obtain ⟨⟨as', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨d', acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    have h1 := (opt_grows Γ acc1 d d' acc2 he).le.trans hle
    obtain ⟨ta, wa⟩ := alts_tr hF hC Γ acc as as' acc1 hb h1
    obtain ⟨to, wo⟩ := opt_tr hF hC Γ acc1 d d' acc2 he hle
    exact ⟨.case ta to, fun hS Δ hws hl => wo hS Δ hws.2.2.2 (wa hS Δ hws.2.1 hl)⟩
  | _, acc, .ret a, e', acc', h, _ => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.ret, fun _ _ _ hl => hl⟩
  | Γ, acc, .tick e, e', acc', h, hle => by
    simp only [Defun.exp] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    obtain ⟨te, we⟩ := exp_tr hF hC Γ acc e e1 acc1 he hle
    exact ⟨.tick te, fun hS Δ hws hl => we hS Δ hws hl⟩
  | _, acc, .trap, e', acc', h, _ => by
    simp only [Defun.exp] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.trap, fun _ _ _ hl => hl⟩

theorem bind_tr (hF : Final X accF) (hC : C.prog = X.P) : ∀ (Γ : Nat) (acc : Acc) (b : Bind) (b' : Bind) (acc' : Acc),
    Defun.bind C Γ acc b = .ok (b', acc') → AccLe acc' accF →
    TrB X Γ b b' ∧ (SigOk X → Bind.WS X.P.sig Γ b → LWS X acc → LWS X acc')
  | _, acc, .glob g, b', acc', h, hle => by
    simp only [Defun.bind] at h
    by_cases hlt : g < C.prog.size
    · rw [ite_eq_left hlt] at h
      rw [hC] at hlt
      cases hg : C.prog.global? g with
      | some hd =>
        simp only [hg] at h
        rw [hC] at hg
        cases hps : hd.ps with
        | nil =>
          simp only [hps] at h
          obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq1, ← hq2]
          exact ⟨.caf hlt hg hps, fun _ _ hl => hl⟩
        | cons p ps =>
          simp only [hps] at h
          obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq1, ← hq2]
          rw [← hq2] at hle
          have hesc := hle.2.1 g (natSet_contains_insert_self _ _)
          exact ⟨.glob hlt hg (by rw [hps]; exact List.cons_ne_nil _ _) (hF.escapes g hd hesc hlt hg),
            fun _ _ hl => hl⟩
      | none =>
        simp only [hg] at h
        rw [hC] at hg
        obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
        rw [← hq1, ← hq2]
        exact ⟨.absent hlt hg, fun _ _ hl => hl⟩
    · rw [ite_eq_right hlt] at h
      exact (throw_ok h).elim
  | Γ, acc, .app f as, b', acc', h, hle => by
    simp only [Defun.bind] at h
    cases as with
    | nil =>
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      exact ⟨.app0, fun _ _ hl => hl⟩
    | cons a as =>
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      rw [← hq2] at hle
      have hm : (a :: as).length ≤ X.M :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hle.2.2 hF.maxApp)
      have := TrB.app (X := X) (Γ := Γ) (f := f) (List.cons_ne_nil a as) hm
      rw [Setting.dispId, ← hC] at this
      exact ⟨this, fun _ _ hl => hl⟩
  | Γ, acc, .fn ps fb, b', acc', h, hle => by
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
      rename_i hall
      obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq1, ← hq2]
      rw [← hq2] at hle
      have hle1 : AccLe acc1 accF :=
        ⟨fun x hx => hle.1 x (List.mem_cons_of_mem _ hx), fun h hh => hle.2.1 h hh, hle.2.2⟩
      obtain ⟨hb', wb⟩ := exp_tr hF hC _ acc fb fb' acc1 hb hle1
      obtain ⟨s, hs, hkey, hcaps, harity, hgd⟩ := hF.lifted _ (hle.1 _ List.mem_cons_self)
      have hfree : ∀ x ∈ fb'.free (p :: ps).length, x < Γ := fun x hx =>
        of_decide_eq_true (List.all_eq_true.1 hall x hx)
      dsimp only at hkey hcaps harity
      refine ⟨?_, fun hS hws hl l hl' => ?_⟩
      · rw [← hkey]
        exact .fn (List.cons_ne_nil _ _) hb' hfree hs hcaps harity hgd
          (by simp [Lifted.toGDef, hcaps]) rfl
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · exact lifted_ws _ (tr_ws hS hb' hws.2) hfree
        · exact wb hS [] hws.2 hl l hl'
  | _, acc, .atom _, b', acc', h, _ => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.atom, fun _ _ hl => hl⟩
  | _, acc, .con .., b', acc', h, _ => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.con, fun _ _ hl => hl⟩
  | _, acc, .proj .., b', acc', h, _ => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.proj, fun _ _ hl => hl⟩
  | _, acc, .prim .., b', acc', h, _ => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.prim, fun _ _ hl => hl⟩
  | _, acc, .call .., b', acc', h, _ => by
    simp only [Defun.bind] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.call, fun _ _ hl => hl⟩

theorem alts_tr (hF : Final X accF) (hC : C.prog = X.P) : ∀ (Γ : Nat) (acc : Acc) (as : List Alt) (as' : List Alt) (acc' : Acc),
    Defun.alts C Γ acc as = .ok (as', acc') → AccLe acc' accF →
    TrAlts X Γ as as' ∧ (SigOk X → ∀ Δ, Exp.AltsWS X.P.sig Γ Δ as → LWS X acc → LWS X acc')
  | _, acc, [], as', acc', h, _ => by
    simp only [Defun.alts] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.nil, fun _ _ _ hl => hl⟩
  | Γ, acc, .mk k n b :: as, as', acc', h, hle => by
    simp only [Defun.alts] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨as1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    have h1 := (alts_grows Γ acc1 as as1 acc2 he).le.trans hle
    obtain ⟨tb, wb⟩ := exp_tr hF hC (Γ + n) acc b b' acc1 hb h1
    obtain ⟨ta, wa⟩ := alts_tr hF hC Γ acc1 as as1 acc2 he hle
    exact ⟨.cons tb ta, fun hS Δ hws hl => wa hS Δ hws.2.2 (wb hS Δ hws.2.1 hl)⟩

theorem opt_tr (hF : Final X accF) (hC : C.prog = X.P) : ∀ (Γ : Nat) (acc : Acc) (o : Option Exp) (o' : Option Exp) (acc' : Acc),
    Defun.opt C Γ acc o = .ok (o', acc') → AccLe acc' accF →
    TrOpt X Γ o o' ∧ (SigOk X → ∀ Δ, Exp.OptWS X.P.sig Γ Δ o → LWS X acc → LWS X acc')
  | _, acc, none, o', acc', h, _ => by
    simp only [Defun.opt] at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    exact ⟨.none, fun _ _ _ hl => hl⟩
  | Γ, acc, some e, o', acc', h, hle => by
    simp only [Defun.opt] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq1, ← hq2]
    rw [← hq2] at hle
    obtain ⟨te, we⟩ := exp_tr hF hC Γ acc e e1 acc1 he hle
    exact ⟨.some te, fun hS Δ hws hl => we hS Δ hws hl⟩

end

end

/-- A rewritten global keeps its parameters and has the translated body; when
it is well scoped, so are the local functions it lifts. -/
theorem global_tr {X : Setting} {accF : Acc} (hF : Final X accF) {g : GlobalId} {gd gd' : GDef} {a a' : Acc}
    (h : Defun.global X.P g gd a = .ok (gd', a')) (hle : AccLe a' accF) :
    gd'.ps = gd.ps ∧ Tr X gd.ps.length gd.body gd'.body ∧
      (SigOk X → Exp.WS X.P.sig gd.ps.length [] gd.body → LWS X a → LWS X a') := by
  have hps := global_ps h
  simp only [Defun.global] at h
  obtain ⟨⟨body, acc1⟩, hb, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨hq1, hq2⟩ := Prod.mk.inj (pure_ok h)
  rw [← hq1] at hps ⊢
  rw [← hq2] at hle ⊢
  obtain ⟨t, w⟩ := exp_tr (C := { prog := X.P, g, key := gd.key }) hF rfl _ _ _ _ _ hb hle
  exact ⟨hps, t, fun hS hws hl => w hS [] hws hl⟩

/-! ## The setting of a run -/

/-- The setting of a successful run: the input, the output, the closure
sources and the largest dispatcher arity. -/
def setting (P : Program) (gs : List (GlobalId × GDef)) (acc : Acc) : Setting :=
  { P, Q := assemble P gs acc, srcs := sources P acc, M := acc.maxApp }

theorem mem_numbered_of {α : Type} : ∀ (k : Nat) {xs : List α} {x : α}, x ∈ xs → ∃ i, (i, x) ∈ numbered k xs
  | _, [], _, h => absurd h List.not_mem_nil
  | k, y :: ys, x, h => by
    rcases List.mem_cons.1 h with h | h
    · exact ⟨k, by rw [h]; exact List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := mem_numbered_of (k + 1) h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

theorem final_ran {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) : Final (setting P gs acc) acc where
  lifted l hl := by
    obtain ⟨i, hi⟩ := mem_numbered_of (liftBase P acc) (List.mem_reverse.2 hl)
    refine ⟨{ key := l.key, id := i, caps := l.ncaps, arity := l.ps.length }, ?_, rfl, rfl, rfl,
      assemble_lifted hr hi⟩
    exact List.mem_append_right _ (List.mem_map.2 ⟨(i, l), hi, rfl⟩)
  escapes h hd he hlt hg := by
    refine List.mem_append_left _ (List.mem_filterMap.2 ⟨h, List.mem_range.2 hlt, ?_⟩)
    show (if acc.escapes.contains h = true then _ else none) = _
    rw [ite_eq_left he, show P.global? h = some hd from hg]
    rfl
  maxApp := Nat.le_refl _

/-- The facts about P8's output the simulation uses. -/
structure Valid (X : Setting) : Prop where
  known : X.Q.known = X.P.known
  roots : X.Q.roots = X.P.roots
  /-- The input's globals keep their ids and parameters; their bodies are translated. -/
  old : ∀ g gd, X.P.global? g = some gd →
    ∃ gd', X.Q.global? g = some gd' ∧ gd'.ps = gd.ps ∧ Tr X gd.ps.length gd.body gd'.body
  /-- An absent id below the input's size stays absent. -/
  absent : ∀ g, g < X.P.size → X.P.global? g = none → X.Q.global? g = none
  /-- The dispatchers. -/
  disp : ∀ m, 1 ≤ m → m ≤ X.M → X.Q.global? (X.dispId m) = some (dispatcher X.P.size X.srcs m)
  /-- The closure sources' keys are distinct. -/
  keys : (X.srcs.map (·.key)).Nodup

/-- **A successful run fixes a valid setting**, for an input whose globals lie
below its size. -/
theorem ran_valid {P : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size)
    {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId} (hr : Ran P gs acc parents) :
    Valid (setting P gs acc) where
  known := rfl
  roots := rfl
  old g gd hg := by
    obtain ⟨gd', a, a', hq, hgl, hle⟩ := assemble_old hr (hwf g gd hg) hg
    obtain ⟨hps, htr, -⟩ := global_tr (X := setting P gs acc) (final_ran hr) hgl hle
    exact ⟨gd', hq, hps, htr⟩
  absent g hlt hg := assemble_absent hr hlt hg
  disp m h1 h2 := assemble_disp hr h1 h2
  keys := sources_keys hr

theorem run_valid {P Q : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size) (h : run P = .ok Q) :
    ∃ X : Setting, X.P = P ∧ X.Q = Q ∧ Valid X := by
  obtain ⟨gs, acc, parents, hr, rfl⟩ := run_ran h
  exact ⟨setting P gs acc, rfl, rfl, ran_valid hwf hr⟩

end IxCC.Anf.Defun.Proof
