import Ix.CompileCert.Conv
import Ix.CompileCert.Translate
import IxC.Kernel.StdAxioms
import IxC.Kernel.ExprOps

/-!
# M7 X2: the bridge from the compiler's terms to the reader's `Kernel.Expr`

The compiler states its terms as `Ix.Expr` (hashes at every node, binder names and infos, `letE`
flags, `mdata`), X1 reasons about their erasure `Conv.er : Ix.Expr → Conv.Tm`, and the certified
checker reads `Kernel.Expr` from the bytes: constants named by their address keys, level
parameters positional, **every binder annotated `pw := .never`** (the reader's convention,
`IxC/Kernel/Ixon/Reader.lean`), `mdata` and binder metadata absent. The bridge is the direct
translation between the two, on the erased skeleton:

* `bridgeT N L : Tm → Option Kernel.Expr`, parameterised by a constant-name map `N` and a level
  translation `L` (both partial: a name outside the artifact has no image);
* `bridge N L e := bridgeT N L (er e)`.

What this module proves:

* **totality** (`bridgeT_isSome_iff`): defined exactly on `Supported N L` terms (no `fvar`, no
  `mvar`, every constant, projection owner and level in the maps' domains);
* **injectivity on erased content** (`bridgeT_agree`, `bridgeT_injective`): two terms with one
  image `Agree` (are equal except where `N`/`L` identify names or levels), hence are equal when
  `N` and `L` are injective;
* **commutation with X1's de Bruijn operations**: `Tm.lift ↔ liftLooseBVars`, `Tm.lower ↔
  lowerBVars`, `Tm.inst ↔ instantiate1Lift` (IxC's capture-avoiding substitution has exactly X1's
  convention), `Tm.appN ↔ mkAppN`; so every syntactic fact about `Tm` transports;
* the reader form: every binder of an image is `.never` (`bridgeT_erasePw`), and `Skel N L t k`
  (`k`'s binder-annotation erasure is `t`'s image) relates the bridge to annotated terms, the
  installed forms the checker's model reads; `Skel` commutes with the same operations.

Emission (the compiler's `Ix.Expr` serialised to Ixon and read back) is not here: it is L4's.
-/

namespace Ix.CompileCert.Bridge

open Ix.CompileCert.Conv (Tm er)

/-- The reader's binder annotation. -/
abbrev never : Kernel.BinderMeta := ⟨.never⟩

/-! ## Option plumbing -/

/-- `List.mapM` in `Option`, stated by its own equations. -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: l =>
    match f a, optMap f l with
    | some b, some bs => some (b :: bs)
    | _, _ => none

theorem optMap_nil {α β : Type} (f : α → Option β) : optMap f [] = some [] := rfl

theorem optMap_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {b : β}
    {bs : List β} (ha : f a = some b) (hl : optMap f l = some bs) :
    optMap f (a :: l) = some (b :: bs) := by simp [optMap, ha, hl]

theorem optMap_cons_inv {α β : Type} {f : α → Option β} {a : α} {l : List α} {r : List β}
    (h : optMap f (a :: l) = some r) : ∃ b bs, f a = some b ∧ optMap f l = some bs ∧ r = b :: bs := by
  simp only [optMap] at h
  split at h
  · rename_i b bs hb hbs; cases h; exact ⟨b, bs, hb, hbs, rfl⟩
  · cases h

theorem optMap_isSome_iff {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (optMap f l).isSome ↔ ∀ a ∈ l, (f a).isSome
  | [] => by simp [optMap]
  | a :: l => by
    have ih := optMap_isSome_iff f l
    simp only [optMap, List.mem_cons, forall_eq_or_imp]
    cases hfa : f a <;> cases hl : optMap f l <;> simp_all

theorem optMap_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, optMap f l = some r → r.length = l.length
  | [], r, h => by simp [optMap] at h; subst h; rfl
  | a :: l, r, h => by
    obtain ⟨b, bs, -, hl, rfl⟩ := optMap_cons_inv h
    simp [optMap_length hl]

theorem optMap_inj {α β : Type} {f : α → Option β} (hf : ∀ a b k, f a = some k → f b = some k → a = b) :
    ∀ {l l' : List α} {r : List β}, optMap f l = some r → optMap f l' = some r → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, r, h1, h2 => by
    have := optMap_length h1; have := optMap_length h2; simp_all
  | _ :: _, [], r, h1, h2 => by
    have := optMap_length h1; have := optMap_length h2; simp_all
  | a :: l, b :: l', r, h1, h2 => by
    obtain ⟨x, xs, hx, hxs, rfl⟩ := optMap_cons_inv h1
    obtain ⟨y, ys, hy, hys, he⟩ := optMap_cons_inv h2
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hf a b x hx hy, optMap_inj hf hxs hys]


section Bridge

variable (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level)

/-- A literal, as the reader spells it. -/
def bridgeLit : Lean.Literal → Kernel.Literal
  | .natVal n => .natVal n
  | .strVal s => .strVal s

/-- Two optional results combined. -/
def app2 {α β γ : Type} (g : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some (g a b)
  | _, _ => none

/-- Three optional results combined. -/
def app3 {α β γ δ : Type} (g : α → β → γ → δ) : Option α → Option β → Option γ → Option δ
  | some a, some b, some c => some (g a b c)
  | _, _, _ => none

@[simp] theorem app2_some {α β γ : Type} (g : α → β → γ) (a : α) (b : β) :
    app2 g (some a) (some b) = some (g a b) := rfl
@[simp] theorem app2_none_left {α β γ : Type} (g : α → β → γ) (y : Option β) :
    app2 g none y = none := by cases y <;> rfl
@[simp] theorem app2_none_right {α β γ : Type} (g : α → β → γ) (x : Option α) :
    app2 g x none = none := by cases x <;> rfl
@[simp] theorem app3_some {α β γ δ : Type} (g : α → β → γ → δ) (a : α) (b : β) (c : γ) :
    app3 g (some a) (some b) (some c) = some (g a b c) := rfl
@[simp] theorem app3_none_1 {α β γ δ : Type} (g : α → β → γ → δ) (y : Option β) (z : Option γ) :
    app3 g none y z = none := by cases y <;> cases z <;> rfl
@[simp] theorem app3_none_2 {α β γ δ : Type} (g : α → β → γ → δ) (x : Option α) (z : Option γ) :
    app3 g x none z = none := by cases x <;> cases z <;> rfl
@[simp] theorem app3_none_3 {α β γ δ : Type} (g : α → β → γ → δ) (x : Option α) (y : Option β) :
    app3 g x y none = none := by cases x <;> cases y <;> rfl

theorem app2_inv {α β γ : Type} {g : α → β → γ} {x : Option α} {y : Option β} {r : γ}
    (h : app2 g x y = some r) : ∃ a b, x = some a ∧ y = some b ∧ r = g a b := by
  cases x <;> cases y <;> simp_all [app2]

theorem app3_inv {α β γ δ : Type} {g : α → β → γ → δ} {x : Option α} {y : Option β}
    {z : Option γ} {r : δ} (h : app3 g x y z = some r) :
    ∃ a b c, x = some a ∧ y = some b ∧ z = some c ∧ r = g a b c := by
  cases x <;> cases y <;> cases z <;> simp_all [app3]

/-- **The bridge** on the erased skeleton: the reader's term for `t`. -/
def bridgeT : Tm → Option Kernel.Expr
  | .bvar i => some (.bvar i)
  | .fvar _ => none
  | .mvar _ => none
  | .sort u => (L u).map .sort
  | .const c us => app2 .const (N c) (optMap L us.toList)
  | .app f a => app2 .app (bridgeT f) (bridgeT a)
  | .lam t b => app2 (fun t' b' => .lam t' b' never) (bridgeT t) (bridgeT b)
  | .pi t b => app2 (fun t' b' => .forallE t' b' never) (bridgeT t) (bridgeT b)
  | .letE t v b => app3 .letE (bridgeT t) (bridgeT v) (bridgeT b)
  | .lit l => some (.lit (bridgeLit l))
  | .proj s i e => app2 (fun s' e' => .proj s' i e') (N s) (bridgeT e)

/-- **The bridge** on compiler expressions: through X1's erasure. -/
def bridge (e : Ix.Expr) : Option Kernel.Expr := bridgeT N L (er e)

/-- The fragment the bridge is defined on. -/
def Supported : Tm → Prop
  | .bvar _ => True
  | .fvar _ => False
  | .mvar _ => False
  | .sort u => (L u).isSome
  | .const c us => (N c).isSome ∧ ∀ u ∈ us.toList, (L u).isSome
  | .app f a => Supported f ∧ Supported a
  | .lam t b => Supported t ∧ Supported b
  | .pi t b => Supported t ∧ Supported b
  | .letE t v b => Supported t ∧ Supported v ∧ Supported b
  | .lit _ => True
  | .proj s _ e => (N s).isSome ∧ Supported e

end Bridge

/-! ## Totality -/

section Total

variable {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

/-- **Totality**: the bridge is defined exactly on the supported fragment. -/
theorem bridgeT_isSome_iff : ∀ (t : Tm), (bridgeT N L t).isSome ↔ Supported N L t := by
  intro t
  induction t with
  | bvar _ => simp [bridgeT, Supported]
  | fvar _ => simp [bridgeT, Supported]
  | mvar _ => simp [bridgeT, Supported]
  | sort u => cases h : L u <;> simp [bridgeT, Supported, h]
  | const c us =>
    have hl := optMap_isSome_iff L us.toList
    cases hc : N c <;> cases hm : optMap L us.toList <;> simp_all [bridgeT, Supported]
  | app f a ihf iha =>
    cases h1 : bridgeT N L f <;> cases h2 : bridgeT N L a <;> simp_all [bridgeT, Supported]
  | lam t b iht ihb =>
    cases h1 : bridgeT N L t <;> cases h2 : bridgeT N L b <;> simp_all [bridgeT, Supported]
  | pi t b iht ihb =>
    cases h1 : bridgeT N L t <;> cases h2 : bridgeT N L b <;> simp_all [bridgeT, Supported]
  | letE t v b iht ihv ihb =>
    cases h1 : bridgeT N L t <;> cases h2 : bridgeT N L v <;> cases h3 : bridgeT N L b <;>
      simp_all [bridgeT, Supported]
  | lit _ => simp [bridgeT, Supported]
  | proj s i e ih =>
    cases hs : N s <;> cases h1 : bridgeT N L e <;> simp_all [bridgeT, Supported]

instance (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level) (t : Tm) :
    Decidable (Supported N L t) :=
  decidable_of_iff _ (bridgeT_isSome_iff (N := N) (L := L) t)

end Total

/-! ## Inversion of the bridge -/

section Inv

variable {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

theorem bridgeT_bvar_inv {i : Nat} {k : Kernel.Expr} (h : bridgeT N L (.bvar i) = some k) :
    k = .bvar i := by simp [bridgeT] at h; exact h.symm

theorem bridgeT_sort_inv {u : Ix.Level} {k : Kernel.Expr} (h : bridgeT N L (.sort u) = some k) :
    ∃ u', L u = some u' ∧ k = .sort u' := by
  simp only [bridgeT, Option.map_eq_some_iff] at h
  obtain ⟨u', h1, h2⟩ := h; exact ⟨u', h1, h2.symm⟩

theorem bridgeT_const_inv {c : Ix.Name} {us : Array Ix.Level} {k : Kernel.Expr}
    (h : bridgeT N L (.const c us) = some k) :
    ∃ c' ls, N c = some c' ∧ optMap L us.toList = some ls ∧ k = .const c' ls := by
  simp only [bridgeT] at h; exact app2_inv h

theorem bridgeT_app_inv {f a : Tm} {k : Kernel.Expr} (h : bridgeT N L (.app f a) = some k) :
    ∃ f' a', bridgeT N L f = some f' ∧ bridgeT N L a = some a' ∧ k = .app f' a' := by
  simp only [bridgeT] at h; exact app2_inv h

theorem bridgeT_lam_inv {t b : Tm} {k : Kernel.Expr} (h : bridgeT N L (.lam t b) = some k) :
    ∃ t' b', bridgeT N L t = some t' ∧ bridgeT N L b = some b' ∧ k = .lam t' b' never := by
  simp only [bridgeT] at h; exact app2_inv h

theorem bridgeT_pi_inv {t b : Tm} {k : Kernel.Expr} (h : bridgeT N L (.pi t b) = some k) :
    ∃ t' b', bridgeT N L t = some t' ∧ bridgeT N L b = some b' ∧ k = .forallE t' b' never := by
  simp only [bridgeT] at h; exact app2_inv h

theorem bridgeT_letE_inv {t v b : Tm} {k : Kernel.Expr} (h : bridgeT N L (.letE t v b) = some k) :
    ∃ t' v' b', bridgeT N L t = some t' ∧ bridgeT N L v = some v' ∧ bridgeT N L b = some b' ∧
      k = .letE t' v' b' := by
  simp only [bridgeT] at h; exact app3_inv h

theorem bridgeT_proj_inv {s : Ix.Name} {i : Nat} {e : Tm} {k : Kernel.Expr}
    (h : bridgeT N L (.proj s i e) = some k) :
    ∃ s' e', N s = some s' ∧ bridgeT N L e = some e' ∧ k = .proj s' i e' := by
  simp only [bridgeT] at h; exact app2_inv h

end Inv

/-! ## Injectivity on erased content -/

section Agree

variable (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level)

/-- Two erased terms agree **as the artifact sees them**: the same skeleton, constants, projection
owners and levels compared through their images (both images defined). -/
def Agree : Tm → Tm → Prop
  | .bvar i, .bvar j => i = j
  | .sort u, .sort v => (L u).isSome ∧ L u = L v
  | .const c us, .const d vs =>
    (N c).isSome ∧ N c = N d ∧ (optMap L us.toList).isSome ∧ optMap L us.toList = optMap L vs.toList
  | .app f a, .app f' a' => Agree f f' ∧ Agree a a'
  | .lam t b, .lam t' b' => Agree t t' ∧ Agree b b'
  | .pi t b, .pi t' b' => Agree t t' ∧ Agree b b'
  | .letE t v b, .letE t' v' b' => Agree t t' ∧ Agree v v' ∧ Agree b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => (N s).isSome ∧ N s = N s' ∧ i = i' ∧ Agree e e'
  | _, _ => False

end Agree

section Inj

variable {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

theorem bridgeLit_injective : Function.Injective bridgeLit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bridgeLit]

/-- The head constructor of an erased term (`fvar`/`mvar` share one tag: never bridged). -/
def tTag : Tm → Nat
  | .bvar _ => 0 | .fvar _ => 1 | .mvar _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ => 5 | .pi _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

/-- The head constructor of a reader term. -/
def kTag : Kernel.Expr → Nat
  | .bvar _ => 0 | .fvar _ _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ _ => 5 | .forallE _ _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

theorem bridgeT_tag : ∀ {t : Tm} {k : Kernel.Expr}, bridgeT N L t = some k → kTag k = tTag t
  | .bvar _, _, h => by rw [bridgeT_bvar_inv h]; rfl
  | .fvar _, _, h => by simp [bridgeT] at h
  | .mvar _, _, h => by simp [bridgeT] at h
  | .sort _, _, h => by obtain ⟨_, _, rfl⟩ := bridgeT_sort_inv h; rfl
  | .const _ _, _, h => by obtain ⟨_, _, _, _, rfl⟩ := bridgeT_const_inv h; rfl
  | .app _ _, _, h => by obtain ⟨_, _, _, _, rfl⟩ := bridgeT_app_inv h; rfl
  | .lam _ _, _, h => by obtain ⟨_, _, _, _, rfl⟩ := bridgeT_lam_inv h; rfl
  | .pi _ _, _, h => by obtain ⟨_, _, _, _, rfl⟩ := bridgeT_pi_inv h; rfl
  | .letE _ _ _, _, h => by obtain ⟨_, _, _, _, _, _, rfl⟩ := bridgeT_letE_inv h; rfl
  | .lit _, _, h => by simp only [bridgeT, Option.some.injEq] at h; subst h; rfl
  | .proj _ _ _, _, h => by obtain ⟨_, _, _, _, rfl⟩ := bridgeT_proj_inv h; rfl

theorem bridgeT_mismatch {a b : Tm} {k : Kernel.Expr} (ha : bridgeT N L a = some k)
    (hb : bridgeT N L b = some k) (h : tTag a ≠ tTag b) : False :=
  h ((bridgeT_tag ha).symm.trans (bridgeT_tag hb))

/-- **Injectivity on erased content**: one image, agreeing terms. -/
theorem bridgeT_agree : ∀ (a b : Tm) {k : Kernel.Expr},
    bridgeT N L a = some k → bridgeT N L b = some k → Agree N L a b := by
  intro a
  induction a with
  | bvar i =>
    intro b k ha hb
    cases b
    case bvar j =>
      rw [bridgeT_bvar_inv ha] at hb
      simp only [Agree]; exact Kernel.Expr.bvar.inj (bridgeT_bvar_inv hb)
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | fvar _ => intro b k ha; simp [bridgeT] at ha
  | mvar _ => intro b k ha; simp [bridgeT] at ha
  | sort u =>
    intro b k ha hb
    cases b
    case sort v =>
      obtain ⟨u', hu, rfl⟩ := bridgeT_sort_inv ha
      obtain ⟨v', hv, he⟩ := bridgeT_sort_inv hb
      simp only [Kernel.Expr.sort.injEq] at he; subst he
      simp [Agree, hu, hv]
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | const c us =>
    intro b k ha hb
    cases b
    case const d vs =>
      obtain ⟨c', ls, hc, hl, rfl⟩ := bridgeT_const_inv ha
      obtain ⟨d', ls', hd, hl', heq⟩ := bridgeT_const_inv hb
      simp only [Kernel.Expr.const.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp [Agree, hc, hd, hl, hl']
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | app f a ihf iha =>
    intro b k ha hb
    cases b
    case app g c =>
      obtain ⟨f', a', hf, ha', rfl⟩ := bridgeT_app_inv ha
      obtain ⟨g', c', hg, hc, heq⟩ := bridgeT_app_inv hb
      simp only [Kernel.Expr.app.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨ihf g hf hg, iha c ha' hc⟩
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | lam t c iht ihc =>
    intro b k ha hb
    cases b
    case lam s d =>
      obtain ⟨t', c', ht, hc, rfl⟩ := bridgeT_lam_inv ha
      obtain ⟨s', d', hs, hd, heq⟩ := bridgeT_lam_inv hb
      simp only [Kernel.Expr.lam.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      exact ⟨iht s ht hs, ihc d hc hd⟩
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | pi t c iht ihc =>
    intro b k ha hb
    cases b
    case pi s d =>
      obtain ⟨t', c', ht, hc, rfl⟩ := bridgeT_pi_inv ha
      obtain ⟨s', d', hs, hd, heq⟩ := bridgeT_pi_inv hb
      simp only [Kernel.Expr.forallE.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      exact ⟨iht s ht hs, ihc d hc hd⟩
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | letE t v c iht ihv ihc =>
    intro b k ha hb
    cases b
    case letE s w d =>
      obtain ⟨t', v', c', ht, hv, hc, rfl⟩ := bridgeT_letE_inv ha
      obtain ⟨s', w', d', hs, hw, hd, heq⟩ := bridgeT_letE_inv hb
      simp only [Kernel.Expr.letE.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨iht s ht hs, ihv w hv hw, ihc d hc hd⟩
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | lit l =>
    intro b k ha hb
    cases b
    case lit l' =>
      simp only [bridgeT, Option.some.injEq] at ha; subst ha
      simp only [bridgeT, Option.some.injEq, Kernel.Expr.lit.injEq] at hb
      exact bridgeLit_injective hb.symm
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim
  | proj s i e ih =>
    intro b k ha hb
    cases b
    case proj r j d =>
      obtain ⟨s', e', hs, he, rfl⟩ := bridgeT_proj_inv ha
      obtain ⟨r', d', hr, hd, heq⟩ := bridgeT_proj_inv hb
      simp only [Kernel.Expr.proj.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨by simp [hs], by rw [hs, hr], rfl, ih d he hd⟩
    all_goals exact (bridgeT_mismatch ha hb (by simp [tTag])).elim

/-- Injective maps on names and levels make the bridge injective. -/
def NameInj (N : Ix.Name → Option Kernel.Name) : Prop :=
  ∀ a b k, N a = some k → N b = some k → a = b

theorem agree_eq (hN : NameInj N) (hL : ∀ a b k, L a = some k → L b = some k → a = b) :
    ∀ (a b : Tm), Agree N L a b → a = b := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp only [Agree] at h; rw [h]
  | fvar _ => intro b h; cases b <;> simp only [Agree] at h
  | mvar _ => intro b h; cases b <;> simp only [Agree] at h
  | sort u =>
    intro b h; cases b <;> simp only [Agree] at h
    case sort v =>
      obtain ⟨hs, he⟩ := h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      rw [hL u v k hk (he ▸ hk)]
  | const c us =>
    intro b h; cases b <;> simp only [Agree] at h
    case const d vs =>
      obtain ⟨hs, he, hls, hle⟩ := h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨ks, hks⟩ := Option.isSome_iff_exists.mp hls
      have hcd := hN c d k hk (he ▸ hk)
      have huv := optMap_inj hL hks (hle ▸ hks)
      subst hcd
      have : us = vs := by cases us; cases vs; simp_all
      rw [this]
  | app f a ihf iha =>
    intro b h; cases b <;> simp only [Agree] at h
    case app f' a' => rw [ihf f' h.1, iha a' h.2]
  | lam t b iht ihb =>
    intro b' h; cases b' <;> simp only [Agree] at h
    case lam t' b' => rw [iht t' h.1, ihb b' h.2]
  | pi t b iht ihb =>
    intro b' h; cases b' <;> simp only [Agree] at h
    case pi t' b' => rw [iht t' h.1, ihb b' h.2]
  | letE t v b iht ihv ihb =>
    intro b' h; cases b' <;> simp only [Agree] at h
    case letE t' v' b' => rw [iht t' h.1, ihv v' h.2.1, ihb b' h.2.2]
  | lit l => intro b h; cases b <;> simp only [Agree] at h; rw [h]
  | proj s i e ih =>
    intro b h; cases b <;> simp only [Agree] at h
    case proj s' i' e' =>
      obtain ⟨hs, he, rfl, ha⟩ := h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      rw [hN s s' k hk (he ▸ hk), ih e' ha]

/-- **The bridge is injective** under injective name and level maps. -/
theorem bridgeT_injective (hN : NameInj N) (hL : ∀ a b k, L a = some k → L b = some k → a = b)
    {a b : Tm} {k : Kernel.Expr} (ha : bridgeT N L a = some k) (hb : bridgeT N L b = some k) :
    a = b :=
  agree_eq hN hL a b (bridgeT_agree a b ha hb)

end Inj

/-! ## Commutation with X1's de Bruijn operations -/

section Commute

variable {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}

open Kernel.Expr in
/-- Lifting: X1's `Tm.lift` is IxC's `liftLooseBVars`. -/
theorem bridgeT_lift (n : Nat) : ∀ (t : Tm) (c : Nat),
    bridgeT N L (Tm.lift n c t) = (bridgeT N L t).map (liftLooseBVars n c) := by
  intro t
  induction t with
  | bvar i =>
    intro c
    by_cases h : c ≤ i
    · simp [Tm.lift, bridgeT, liftLooseBVars, h]
    · simp [Tm.lift, bridgeT, liftLooseBVars, h]
  | fvar _ => intro c; rfl
  | mvar _ => intro c; rfl
  | sort u => intro c; cases h : L u <;> simp [Tm.lift, bridgeT, liftLooseBVars, h]
  | const x us =>
    intro c
    cases h1 : N x <;> cases h2 : optMap L us.toList <;>
      simp [Tm.lift, bridgeT, liftLooseBVars, h1, h2]
  | app f a ihf iha =>
    intro c
    simp only [Tm.lift, bridgeT, ihf c, iha c]
    cases bridgeT N L f <;> cases bridgeT N L a <;> simp [liftLooseBVars]
  | lam t b iht ihb =>
    intro c
    simp only [Tm.lift, bridgeT, iht c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [liftLooseBVars]
  | pi t b iht ihb =>
    intro c
    simp only [Tm.lift, bridgeT, iht c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [liftLooseBVars]
  | letE t v b iht ihv ihb =>
    intro c
    simp only [Tm.lift, bridgeT, iht c, ihv c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L v <;> cases bridgeT N L b <;>
      simp [liftLooseBVars]
  | lit l => intro c; rfl
  | proj s i e ih =>
    intro c
    simp only [Tm.lift, bridgeT, ih c]
    cases N s <;> cases bridgeT N L e <;> simp [liftLooseBVars]

open Kernel.Expr in
/-- Lowering: X1's `Tm.lower` is IxC's `lowerBVars`. -/
theorem bridgeT_lower (n : Nat) : ∀ (t : Tm) (c : Nat),
    bridgeT N L (Tm.lower n c t) = (bridgeT N L t).map (lowerBVars n c) := by
  intro t
  induction t with
  | bvar i =>
    intro c
    by_cases h : c + n ≤ i
    · simp [Tm.lower, bridgeT, lowerBVars, h]
    · simp [Tm.lower, bridgeT, lowerBVars, h]
  | fvar _ => intro c; rfl
  | mvar _ => intro c; rfl
  | sort u => intro c; cases h : L u <;> simp [Tm.lower, bridgeT, lowerBVars, h]
  | const x us =>
    intro c
    cases h1 : N x <;> cases h2 : optMap L us.toList <;>
      simp [Tm.lower, bridgeT, lowerBVars, h1, h2]
  | app f a ihf iha =>
    intro c
    simp only [Tm.lower, bridgeT, ihf c, iha c]
    cases bridgeT N L f <;> cases bridgeT N L a <;> simp [lowerBVars]
  | lam t b iht ihb =>
    intro c
    simp only [Tm.lower, bridgeT, iht c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [lowerBVars]
  | pi t b iht ihb =>
    intro c
    simp only [Tm.lower, bridgeT, iht c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [lowerBVars]
  | letE t v b iht ihv ihb =>
    intro c
    simp only [Tm.lower, bridgeT, iht c, ihv c, ihb (c + 1)]
    cases bridgeT N L t <;> cases bridgeT N L v <;> cases bridgeT N L b <;>
      simp [lowerBVars]
  | lit l => intro c; rfl
  | proj s i e ih =>
    intro c
    simp only [Tm.lower, bridgeT, ih c]
    cases N s <;> cases bridgeT N L e <;> simp [lowerBVars]

open Kernel.Expr in
/-- Substitution: X1's `Tm.inst v k` is IxC's capture-avoiding `instantiate1Lift · v k` (the
value lifted past the `k` binders crossed, the variables above lowered). -/
theorem bridgeT_inst {v : Tm} {kv : Kernel.Expr} (hv : bridgeT N L v = some kv) :
    ∀ (t : Tm) (k : Nat),
      bridgeT N L (Tm.inst v k t) = (bridgeT N L t).map (fun e => e.instantiate1Lift kv k) := by
  intro t
  induction t with
  | bvar i =>
    intro k
    by_cases h : i = k
    · subst h; simp [Tm.inst, bridgeT, instantiate1Lift, bridgeT_lift, hv]
    · by_cases h2 : k < i
      · simp [Tm.inst, bridgeT, instantiate1Lift, h, h2]
      · simp [Tm.inst, bridgeT, instantiate1Lift, h, h2]
  | fvar _ => intro k; rfl
  | mvar _ => intro k; rfl
  | sort u => intro k; cases h : L u <;> simp [Tm.inst, bridgeT, instantiate1Lift, h]
  | const x us =>
    intro k
    cases h1 : N x <;> cases h2 : optMap L us.toList <;>
      simp [Tm.inst, bridgeT, instantiate1Lift, h1, h2]
  | app f a ihf iha =>
    intro k
    simp only [Tm.inst, bridgeT, ihf k, iha k]
    cases bridgeT N L f <;> cases bridgeT N L a <;> simp [instantiate1Lift]
  | lam t b iht ihb =>
    intro k
    simp only [Tm.inst, bridgeT, iht k, ihb (k + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [instantiate1Lift]
  | pi t b iht ihb =>
    intro k
    simp only [Tm.inst, bridgeT, iht k, ihb (k + 1)]
    cases bridgeT N L t <;> cases bridgeT N L b <;> simp [instantiate1Lift]
  | letE t w b iht ihw ihb =>
    intro k
    simp only [Tm.inst, bridgeT, iht k, ihw k, ihb (k + 1)]
    cases bridgeT N L t <;> cases bridgeT N L w <;> cases bridgeT N L b <;>
      simp [instantiate1Lift]
  | lit l => intro k; rfl
  | proj s i e ih =>
    intro k
    simp only [Tm.inst, bridgeT, ih k]
    cases N s <;> cases bridgeT N L e <;> simp [instantiate1Lift]

/-- Application spines. -/
theorem bridgeT_appN : ∀ (as : List Tm) (f : Tm) {kf : Kernel.Expr} {ks : List Kernel.Expr},
    bridgeT N L f = some kf → optMap (bridgeT N L) as = some ks →
      bridgeT N L (Tm.appN f as) = some (Kernel.Expr.mkAppN kf ks)
  | [], f, kf, ks, hf, hs => by
    simp only [optMap, Option.some.injEq] at hs
    subst hs; simpa [Tm.appN, Kernel.Expr.mkAppN] using hf
  | a :: as, f, kf, ks, hf, hs => by
    obtain ⟨ka, kr, ha, hr, rfl⟩ := optMap_cons_inv hs
    rw [Tm.appN_cons, Kernel.Expr.mkAppN]
    exact bridgeT_appN as (.app f a) (by simp [bridgeT, hf, ha]) hr

/-- The bridge's output is the reader's form: every binder `.never`, no free variable. -/
theorem bridgeT_erasePw : ∀ (t : Tm) {k : Kernel.Expr}, bridgeT N L t = some k → k.erasePw = k := by
  intro t
  induction t with
  | bvar i => intro k h; rw [bridgeT_bvar_inv h]; rfl
  | fvar _ => intro k h; simp [bridgeT] at h
  | mvar _ => intro k h; simp [bridgeT] at h
  | sort u => intro k h; obtain ⟨_, _, rfl⟩ := bridgeT_sort_inv h; rfl
  | const x us => intro k h; obtain ⟨_, _, _, _, rfl⟩ := bridgeT_const_inv h; rfl
  | app f a ihf iha =>
    intro k h; obtain ⟨f', a', hf, ha, rfl⟩ := bridgeT_app_inv h
    simp [Kernel.Expr.erasePw, ihf hf, iha ha]
  | lam t b iht ihb =>
    intro k h; obtain ⟨t', b', ht, hb, rfl⟩ := bridgeT_lam_inv h
    simp [Kernel.Expr.erasePw, iht ht, ihb hb]
  | pi t b iht ihb =>
    intro k h; obtain ⟨t', b', ht, hb, rfl⟩ := bridgeT_pi_inv h
    simp [Kernel.Expr.erasePw, iht ht, ihb hb]
  | letE t v b iht ihv ihb =>
    intro k h; obtain ⟨t', v', b', ht, hv, hb, rfl⟩ := bridgeT_letE_inv h
    simp [Kernel.Expr.erasePw, iht ht, ihv hv, ihb hb]
  | lit l => intro k h; simp only [bridgeT, Option.some.injEq] at h; subst h; rfl
  | proj s i e ih =>
    intro k h; obtain ⟨s', e', hs, he, rfl⟩ := bridgeT_proj_inv h
    simp [Kernel.Expr.erasePw, ih he]

end Commute

/-! ## The skeleton relation: annotated terms over a bridged skeleton

The checker installs annotated terms (its own `pw` at every binder); the model reads those. An
annotated term `k` **has the skeleton** of `t` when its annotation erasure is `t`'s bridge. -/

section Skel

variable (N : Ix.Name → Option Kernel.Name) (L : Ix.Level → Option Kernel.Level)

/-- `k` is an annotation of `t`'s image. -/
def Skel (t : Tm) (k : Kernel.Expr) : Prop := bridgeT N L t = some k.erasePw

variable {N L}

theorem skel_of_bridgeT {t : Tm} {k : Kernel.Expr} (h : bridgeT N L t = some k) : Skel N L t k := by
  unfold Skel; rw [bridgeT_erasePw t h]; exact h

open Kernel.Expr in
theorem erasePw_liftLooseBVars (n : Nat) : ∀ (e : Kernel.Expr) (c : Nat),
    (liftLooseBVars n c e).erasePw = liftLooseBVars n c e.erasePw := by
  intro e
  induction e with
  | bvar i => intro c; by_cases h : i ≥ c <;> simp [liftLooseBVars, erasePw, h]
  | fvar i ty ih => intro c; simp [liftLooseBVars, erasePw]
  | sort u => intro c; rfl
  | const n us => intro c; rfl
  | app f a ihf iha => intro c; simp [liftLooseBVars, erasePw, ihf, iha]
  | lam t b m iht ihb => intro c; simp [liftLooseBVars, erasePw, iht, ihb]
  | forallE t b m iht ihb => intro c; simp [liftLooseBVars, erasePw, iht, ihb]
  | letE t v b iht ihv ihb => intro c; simp [liftLooseBVars, erasePw, iht, ihv, ihb]
  | lit l => intro c; rfl
  | proj s i e ih => intro c; simp [liftLooseBVars, erasePw, ih]

open Kernel.Expr in
theorem erasePw_lowerBVars (n : Nat) : ∀ (e : Kernel.Expr) (c : Nat),
    (lowerBVars n c e).erasePw = lowerBVars n c e.erasePw := by
  intro e
  induction e with
  | bvar i => intro c; by_cases h : i ≥ c + n <;> simp [lowerBVars, erasePw, h]
  | fvar i ty ih => intro c; simp [lowerBVars, erasePw]
  | sort u => intro c; rfl
  | const n us => intro c; rfl
  | app f a ihf iha => intro c; simp [lowerBVars, erasePw, ihf, iha]
  | lam t b m iht ihb => intro c; simp [lowerBVars, erasePw, iht, ihb]
  | forallE t b m iht ihb => intro c; simp [lowerBVars, erasePw, iht, ihb]
  | letE t v b iht ihv ihb => intro c; simp [lowerBVars, erasePw, iht, ihv, ihb]
  | lit l => intro c; rfl
  | proj s i e ih => intro c; simp [lowerBVars, erasePw, ih]

open Kernel.Expr in
theorem erasePw_instantiate1Lift (v : Kernel.Expr) : ∀ (e : Kernel.Expr) (k : Nat),
    (e.instantiate1Lift v k).erasePw = e.erasePw.instantiate1Lift v.erasePw k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    by_cases h : i = k
    · simp [instantiate1Lift, erasePw, h, erasePw_liftLooseBVars]
    · by_cases h2 : i > k <;> simp [instantiate1Lift, erasePw, h, h2]
  | fvar i ty ih => intro k; simp [instantiate1Lift, erasePw]
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | app f a ihf iha => intro k; simp [instantiate1Lift, erasePw, ihf, iha]
  | lam t b m iht ihb => intro k; simp [instantiate1Lift, erasePw, iht, ihb]
  | forallE t b m iht ihb => intro k; simp [instantiate1Lift, erasePw, iht, ihb]
  | letE t w b iht ihw ihb => intro k; simp [instantiate1Lift, erasePw, iht, ihw, ihb]
  | lit l => intro k; rfl
  | proj s i e ih => intro k; simp [instantiate1Lift, erasePw, ih]

theorem Skel.lift {t : Tm} {k : Kernel.Expr} (h : Skel N L t k) (n c : Nat) :
    Skel N L (Tm.lift n c t) (Kernel.Expr.liftLooseBVars n c k) := by
  unfold Skel at *; rw [bridgeT_lift, h, erasePw_liftLooseBVars]; rfl

theorem Skel.lower {t : Tm} {k : Kernel.Expr} (h : Skel N L t k) (n c : Nat) :
    Skel N L (Tm.lower n c t) (Kernel.Expr.lowerBVars n c k) := by
  unfold Skel at *; rw [bridgeT_lower, h, erasePw_lowerBVars]; rfl

theorem Skel.inst {v t : Tm} {kv kt : Kernel.Expr} (hv : Skel N L v kv) (ht : Skel N L t kt)
    (k : Nat) : Skel N L (Tm.inst v k t) (kt.instantiate1Lift kv k) := by
  unfold Skel at *; rw [bridgeT_inst hv t k, ht, erasePw_instantiate1Lift]; rfl

theorem skel_app {f a : Tm} {kf ka : Kernel.Expr} :
    Skel N L (.app f a) (.app kf ka) ↔ Skel N L f kf ∧ Skel N L a ka := by
  unfold Skel
  constructor
  · intro h
    obtain ⟨f', a', hf, ha, he⟩ := bridgeT_app_inv h
    simp only [Kernel.Expr.erasePw, Kernel.Expr.app.injEq] at he
    exact ⟨he.1 ▸ hf, he.2 ▸ ha⟩
  · rintro ⟨hf, ha⟩; simp [bridgeT, hf, ha, Kernel.Expr.erasePw]

theorem skel_lam {t b : Tm} {kt kb : Kernel.Expr} {m : Kernel.BinderMeta} :
    Skel N L (.lam t b) (.lam kt kb m) ↔ Skel N L t kt ∧ Skel N L b kb := by
  unfold Skel
  constructor
  · intro h
    obtain ⟨t', b', ht, hb, he⟩ := bridgeT_lam_inv h
    simp only [Kernel.Expr.erasePw, Kernel.Expr.lam.injEq] at he
    exact ⟨he.1 ▸ ht, he.2.1 ▸ hb⟩
  · rintro ⟨ht, hb⟩; simp [bridgeT, ht, hb, Kernel.Expr.erasePw]

theorem skel_pi {t b : Tm} {kt kb : Kernel.Expr} {m : Kernel.BinderMeta} :
    Skel N L (.pi t b) (.forallE kt kb m) ↔ Skel N L t kt ∧ Skel N L b kb := by
  unfold Skel
  constructor
  · intro h
    obtain ⟨t', b', ht, hb, he⟩ := bridgeT_pi_inv h
    simp only [Kernel.Expr.erasePw, Kernel.Expr.forallE.injEq] at he
    exact ⟨he.1 ▸ ht, he.2.1 ▸ hb⟩
  · rintro ⟨ht, hb⟩; simp [bridgeT, ht, hb, Kernel.Expr.erasePw]

theorem skel_proj {s : Ix.Name} {i : Nat} {e : Tm} {s' : Kernel.Name} {ke : Kernel.Expr} :
    Skel N L (.proj s i e) (.proj s' i ke) ↔ N s = some s' ∧ Skel N L e ke := by
  unfold Skel
  constructor
  · intro h
    obtain ⟨s'', e', hs, he, heq⟩ := bridgeT_proj_inv h
    simp only [Kernel.Expr.erasePw, Kernel.Expr.proj.injEq] at heq
    exact ⟨heq.1 ▸ hs, heq.2.2 ▸ he⟩
  · rintro ⟨hs, he⟩; simp [bridgeT, hs, he, Kernel.Expr.erasePw]

theorem skel_const {c : Ix.Name} {us : Array Ix.Level} {c' : Kernel.Name} {ls : List Kernel.Level} :
    Skel N L (.const c us) (.const c' ls) ↔ N c = some c' ∧ optMap L us.toList = some ls := by
  unfold Skel
  constructor
  · intro h
    obtain ⟨c'', ls', hc, hl, heq⟩ := bridgeT_const_inv h
    simp only [Kernel.Expr.erasePw, Kernel.Expr.const.injEq] at heq
    exact ⟨heq.1 ▸ hc, heq.2 ▸ hl⟩
  · rintro ⟨hc, hl⟩; simp [bridgeT, hc, hl, Kernel.Expr.erasePw]

theorem skel_bvar {i : Nat} : Skel N L (.bvar i) (.bvar i) := by
  simp [Skel, bridgeT, Kernel.Expr.erasePw]

end Skel

end Ix.CompileCert.Bridge
