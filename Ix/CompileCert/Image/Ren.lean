import Ix.CompileCert.Image.Build
import Batteries.Tactic.OpenPrivate

/-!
# M7 L2a-syn: free-variable renaming of the compiler's terms

The image construction opens binders with fresh free variables named from a counter
(`Ix.Compile.Image.freshName`: `_img_fvar.N`). Two runs of the same construction from different
counters build the same terms up to the names of those variables (and the cached hashes, which
`Ix.Expr`'s constructors recompute). `Ren ρ a b` says exactly that: `b` is `a` with every free
variable `n` renamed to `ρ n`, every other field equal, hashes arbitrary.

The construction's helpers respect `Ren` (they treat free variables as opaque leaves, comparing
their names with `==` at most, which a renaming injective on the names involved preserves).
-/

open private Ix.Compile.Canon.liftLoose.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.lowerLoose.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.substLevels.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.canonicalizeConstNames.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.replaceConstNames.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Image.abstractFVars.go from Ix.Compile.Image.Expr
open private Ix.Compile.Image.hasLooseBVar.go from Ix.Compile.Image.Expr
open private Ix.Compile.Image.usedConstants.go from Ix.Compile.Image.Expr

namespace Ix.CompileCert.Img

open Ix (Name Level Expr)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose instantiateRevAt instantiateRev)
open Ix.Compile.Image (Created)

/-- `b` is `a` with its free variables renamed by `ρ`, hashes ignored. -/
inductive Ren (ρ : Name → Name) : Expr → Expr → Prop
  | bvar (i : Nat) (h h' : Address) : Ren ρ (.bvar i h) (.bvar i h')
  | fvar (n : Name) (h h' : Address) : Ren ρ (.fvar n h) (.fvar (ρ n) h')
  | mvar (n : Name) (h h' : Address) : Ren ρ (.mvar n h) (.mvar n h')
  | sort (u : Level) (h h' : Address) : Ren ρ (.sort u h) (.sort u h')
  | const (n : Name) (us : Array Level) (h h' : Address) : Ren ρ (.const n us h) (.const n us h')
  | app {f f' a a' : Expr} (h h' : Address) : Ren ρ f f' → Ren ρ a a' →
      Ren ρ (.app f a h) (.app f' a' h')
  | lam (n : Name) {t t' b b' : Expr} (bi : Lean.BinderInfo) (h h' : Address) :
      Ren ρ t t' → Ren ρ b b' → Ren ρ (.lam n t b bi h) (.lam n t' b' bi h')
  | forallE (n : Name) {t t' b b' : Expr} (bi : Lean.BinderInfo) (h h' : Address) :
      Ren ρ t t' → Ren ρ b b' → Ren ρ (.forallE n t b bi h) (.forallE n t' b' bi h')
  | letE (n : Name) {t t' v v' b b' : Expr} (nd : Bool) (h h' : Address) :
      Ren ρ t t' → Ren ρ v v' → Ren ρ b b' → Ren ρ (.letE n t v b nd h) (.letE n t' v' b' nd h')
  | lit (l : Lean.Literal) (h h' : Address) : Ren ρ (.lit l h) (.lit l h')
  | mdata (d : Array (Name × Ix.DataValue)) {x x' : Expr} (h h' : Address) :
      Ren ρ x x' → Ren ρ (.mdata d x h) (.mdata d x' h')
  | proj (s : Name) (i : Nat) {x x' : Expr} (h h' : Address) :
      Ren ρ x x' → Ren ρ (.proj s i x h) (.proj s i x' h')

/-- Every free variable of `e` satisfies `P`. -/
def FvAll (P : Name → Prop) : Expr → Prop
  | .fvar n _ => P n
  | .app f a _ => FvAll P f ∧ FvAll P a
  | .lam _ t b _ _ | .forallE _ t b _ _ => FvAll P t ∧ FvAll P b
  | .letE _ t v b _ _ => FvAll P t ∧ FvAll P v ∧ FvAll P b
  | .mdata _ x _ | .proj _ _ x _ => FvAll P x
  | .bvar .. | .mvar .. | .sort .. | .const .. | .lit .. => True

/-- Pointwise `Ren` on lists. -/
inductive LRen (ρ : Name → Name) : List Expr → List Expr → Prop
  | nil : LRen ρ [] []
  | cons {a b : Expr} {as bs : List Expr} : Ren ρ a b → LRen ρ as bs → LRen ρ (a :: as) (b :: bs)

/-- Pointwise `Ren` on arrays. -/
def ARen (ρ : Name → Name) (a b : Array Expr) : Prop := LRen ρ a.toList b.toList

namespace Ren

variable {ρ : Name → Name}

theorem mkBVar (i : Nat) (h : Address) : Ren ρ (.bvar i h) (Expr.mkBVar i) := .bvar _ _ _
theorem mkApp {f f' a a' : Expr} (h : Address) (hf : Ren ρ f f') (ha : Ren ρ a a') :
    Ren ρ (.app f a h) (Expr.mkApp f' a') := .app _ _ hf ha

/-- Both sides rebuilt with the hashing constructors. -/
theorem mkApp' {f f' a a' : Expr} (hf : Ren ρ f f') (ha : Ren ρ a a') :
    Ren ρ (Expr.mkApp f a) (Expr.mkApp f' a') := .app _ _ hf ha
theorem mkLam' (n : Name) {t t' b b' : Expr} (bi : Lean.BinderInfo) (ht : Ren ρ t t')
    (hb : Ren ρ b b') : Ren ρ (Expr.mkLam n t b bi) (Expr.mkLam n t' b' bi) := .lam _ _ _ _ ht hb
theorem mkForallE' (n : Name) {t t' b b' : Expr} (bi : Lean.BinderInfo) (ht : Ren ρ t t')
    (hb : Ren ρ b b') : Ren ρ (Expr.mkForallE n t b bi) (Expr.mkForallE n t' b' bi) :=
  .forallE _ _ _ _ ht hb
theorem mkLetE' (n : Name) {t t' v v' b b' : Expr} (nd : Bool) (ht : Ren ρ t t') (hv : Ren ρ v v')
    (hb : Ren ρ b b') : Ren ρ (Expr.mkLetE n t v b nd) (Expr.mkLetE n t' v' b' nd) :=
  .letE _ _ _ _ ht hv hb
theorem mkMData' (d : Array (Name × Ix.DataValue)) {x x' : Expr} (hx : Ren ρ x x') :
    Ren ρ (Expr.mkMData d x) (Expr.mkMData d x') := .mdata _ _ _ hx
theorem mkProj' (s : Name) (i : Nat) {x x' : Expr} (hx : Ren ρ x x') :
    Ren ρ (Expr.mkProj s i x) (Expr.mkProj s i x') := .proj _ _ _ _ hx
theorem mkConst' (n : Name) (us : Array Level) : Ren ρ (Expr.mkConst n us) (Expr.mkConst n us) :=
  .const _ _ _ _
theorem mkFVar' (n : Name) : Ren ρ (Expr.mkFVar n) (Expr.mkFVar (ρ n)) := .fvar _ _ _
theorem mkSort' (u : Level) : Ren ρ (Expr.mkSort u) (Expr.mkSort u) := .sort _ _ _
theorem mkBVar' (i : Nat) : Ren ρ (Expr.mkBVar i) (Expr.mkBVar i) := .bvar _ _ _

/-- A renaming that fixes the free variables of `e` relates `e` to itself. -/
theorem refl_of : ∀ {e : Expr}, FvAll (fun n => ρ n = n) e → Ren ρ e e
  | .bvar .., _ => .bvar _ _ _
  | .fvar n h, hf => by
    have : ρ n = n := hf
    have h1 := Ren.fvar (ρ := ρ) n h h
    rw [this] at h1; exact h1
  | .mvar .., _ => .mvar _ _ _
  | .sort .., _ => .sort _ _ _
  | .const .., _ => .const _ _ _ _
  | .app f a h, hf => .app _ _ (refl_of hf.1) (refl_of hf.2)
  | .lam .., hf => .lam _ _ _ _ (refl_of hf.1) (refl_of hf.2)
  | .forallE .., hf => .forallE _ _ _ _ (refl_of hf.1) (refl_of hf.2)
  | .letE .., hf => .letE _ _ _ _ (refl_of hf.1) (refl_of hf.2.1) (refl_of hf.2.2)
  | .lit .., _ => .lit _ _ _
  | .mdata .., hf => .mdata _ _ _ (refl_of hf)
  | .proj .., hf => .proj _ _ _ _ (refl_of hf)

theorem id_refl : ∀ (e : Expr), Ren id e e := fun e =>
  refl_of (by
    induction e <;> simp_all [FvAll])

/-- Renamings compose. -/
theorem trans {ρ σ : Name → Name} : ∀ {a b c : Expr}, Ren ρ a b → Ren σ b c → Ren (σ ∘ ρ) a c
  | _, _, _, .bvar .., .bvar .. => .bvar _ _ _
  | _, _, _, .fvar .., .fvar .. => .fvar _ _ _
  | _, _, _, .mvar .., .mvar .. => .mvar _ _ _
  | _, _, _, .sort .., .sort .. => .sort _ _ _
  | _, _, _, .const .., .const .. => .const _ _ _ _
  | _, _, _, .app _ _ h1 h2, .app _ _ h3 h4 => .app _ _ (trans h1 h3) (trans h2 h4)
  | _, _, _, .lam _ _ _ _ h1 h2, .lam _ _ _ _ h3 h4 => .lam _ _ _ _ (trans h1 h3) (trans h2 h4)
  | _, _, _, .forallE _ _ _ _ h1 h2, .forallE _ _ _ _ h3 h4 =>
    .forallE _ _ _ _ (trans h1 h3) (trans h2 h4)
  | _, _, _, .letE _ _ _ _ h1 h2 h5, .letE _ _ _ _ h3 h4 h6 =>
    .letE _ _ _ _ (trans h1 h3) (trans h2 h4) (trans h5 h6)
  | _, _, _, .lit .., .lit .. => .lit _ _ _
  | _, _, _, .mdata _ _ _ h1, .mdata _ _ _ h2 => .mdata _ _ _ (trans h1 h2)
  | _, _, _, .proj _ _ _ _ h1, .proj _ _ _ _ h2 => .proj _ _ _ _ (trans h1 h2)

/-- A renaming of `a` keeps the free variables' property after renaming. -/
theorem fvAll {P Q : Name → Prop} (hPQ : ∀ n, P n → Q (ρ n)) :
    ∀ {a b : Expr}, Ren ρ a b → FvAll P a → FvAll Q b
  | _, _, .bvar .., _ | _, _, .mvar .., _ | _, _, .sort .., _ | _, _, .const .., _
  | _, _, .lit .., _ => trivial
  | _, _, .fvar n _ _, h => hPQ n h
  | _, _, .app _ _ h1 h2, h => ⟨fvAll hPQ h1 h.1, fvAll hPQ h2 h.2⟩
  | _, _, .lam _ _ _ _ h1 h2, h => ⟨fvAll hPQ h1 h.1, fvAll hPQ h2 h.2⟩
  | _, _, .forallE _ _ _ _ h1 h2, h => ⟨fvAll hPQ h1 h.1, fvAll hPQ h2 h.2⟩
  | _, _, .letE _ _ _ _ h1 h2 h3, h => ⟨fvAll hPQ h1 h.1, fvAll hPQ h2 h.2.1, fvAll hPQ h3 h.2.2⟩
  | _, _, .mdata _ _ _ h1, h => by simp only [FvAll] at h ⊢; exact fvAll hPQ h1 h
  | _, _, .proj _ _ _ _ h1, h => by simp only [FvAll] at h ⊢; exact fvAll hPQ h1 h

end Ren

theorem FvAll.mono {P Q : Name → Prop} (h : ∀ n, P n → Q n) : ∀ {e : Expr}, FvAll P e → FvAll Q e
  | .fvar n _, hp => h n hp
  | .app .., hp => ⟨FvAll.mono h hp.1, FvAll.mono h hp.2⟩
  | .lam .., hp | .forallE .., hp => ⟨FvAll.mono h hp.1, FvAll.mono h hp.2⟩
  | .letE .., hp => ⟨FvAll.mono h hp.1, FvAll.mono h hp.2.1, FvAll.mono h hp.2.2⟩
  | .mdata _ x _, hp => FvAll.mono h (e := x) hp
  | .proj _ _ x _, hp => FvAll.mono h (e := x) hp
  | .bvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => trivial

/-! ## The erasure of a renaming -/

/-- Free-variable renaming of erased terms. -/
def Tm.renF (ρ : Name → Name) : Tm → Tm
  | .fvar n => .fvar (ρ n)
  | .app f a => .app (Tm.renF ρ f) (Tm.renF ρ a)
  | .lam t b => .lam (Tm.renF ρ t) (Tm.renF ρ b)
  | .pi t b => .pi (Tm.renF ρ t) (Tm.renF ρ b)
  | .letE t v b => .letE (Tm.renF ρ t) (Tm.renF ρ v) (Tm.renF ρ b)
  | .proj s i e => .proj s i (Tm.renF ρ e)
  | t => t

theorem er_ren {ρ : Name → Name} : ∀ {a b : Expr}, Ren ρ a b → er b = Tm.renF ρ (er a)
  | _, _, .bvar .. | _, _, .fvar .. | _, _, .mvar .. | _, _, .sort .. | _, _, .const ..
  | _, _, .lit .. => rfl
  | _, _, .app _ _ h1 h2 => by simp only [er, Tm.renF, er_ren h1, er_ren h2]
  | _, _, .lam _ _ _ _ h1 h2 => by simp only [er, Tm.renF, er_ren h1, er_ren h2]
  | _, _, .forallE _ _ _ _ h1 h2 => by simp only [er, Tm.renF, er_ren h1, er_ren h2]
  | _, _, .letE _ _ _ _ h1 h2 h3 => by simp only [er, Tm.renF, er_ren h1, er_ren h2, er_ren h3]
  | _, _, .mdata _ _ _ h1 => by simp only [er, er_ren h1]
  | _, _, .proj _ _ _ _ h1 => by simp only [er, Tm.renF, er_ren h1]

/-- With the identity renaming: the same erased term. -/
theorem er_ren_id : ∀ {a b : Expr}, Ren id a b → er b = er a := fun h => by
  rw [er_ren h]
  generalize er _ = t
  induction t <;> simp_all [Tm.renF]

/-! ## Spines -/

theorem LRen.length {ρ : Name → Name} : ∀ {as bs : List Expr}, LRen ρ as bs → as.length = bs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [LRen.length h]

theorem LRen.append {ρ : Name → Name} : ∀ {as bs cs ds : List Expr}, LRen ρ as bs → LRen ρ cs ds →
    LRen ρ (as ++ cs) (bs ++ ds)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (LRen.append h2 h)

theorem LRen.map {ρ : Name → Name} {f g : Expr → Expr} (h : ∀ a b, Ren ρ a b → Ren ρ (f a) (g b)) :
    ∀ {as bs : List Expr}, LRen ρ as bs → LRen ρ (as.map f) (bs.map g)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (h _ _ h1) (LRen.map h h2)

theorem LRen.get {ρ : Name → Name} : ∀ {as bs : List Expr}, LRen ρ as bs → ∀ (i : Nat),
    match as[i]?, bs[i]? with
    | some a, some b => Ren ρ a b
    | none, none => True
    | _, _ => False
  | [], [], .nil, i => by simp
  | _ :: _, _ :: _, .cons h1 h2, 0 => by simpa using h1
  | _ :: _, _ :: _, .cons h1 h2, i + 1 => by simpa using LRen.get h2 i

theorem foldl_mkApp_ren {ρ : Name → Name} : ∀ {as bs : List Expr} {f g : Expr}, Ren ρ f g →
    LRen ρ as bs → Ren ρ (as.foldl Expr.mkApp f) (bs.foldl Expr.mkApp g)
  | [], [], _, _, h, .nil => h
  | _ :: _, _ :: _, _, _, h, .cons h1 h2 => by
    simp only [List.foldl_cons]; exact foldl_mkApp_ren (Ren.mkApp' h h1) h2

theorem mkAppN_ren {ρ : Name → Name} {f g : Expr} {as bs : Array Expr} (hf : Ren ρ f g)
    (ha : ARen ρ as bs) : Ren ρ (mkAppN f as) (mkAppN g bs) := by
  simp only [mkAppN, ← Array.foldl_toList]
  exact foldl_mkApp_ren hf ha

/-- The spine decomposition respects renaming. -/
theorem getAppFnArgs_ren {ρ : Name → Name} : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (getAppFnArgs a).1 (getAppFnArgs b).1 ∧ ARen ρ (getAppFnArgs a).2 (getAppFnArgs b).2
  | _, _, .app _ _ h1 h2 => by
    obtain ⟨g1, g2⟩ := getAppFnArgs_ren h1
    simp only [getAppFnArgs]
    refine ⟨g1, ?_⟩
    unfold ARen at g2 ⊢
    simp only [Array.toList_push]
    exact g2.append (.cons h2 .nil)
  | _, _, .bvar .. => ⟨.bvar _ _ _, .nil⟩
  | _, _, .fvar .. => ⟨.fvar _ _ _, .nil⟩
  | _, _, .mvar .. => ⟨.mvar _ _ _, .nil⟩
  | _, _, .sort .. => ⟨.sort _ _ _, .nil⟩
  | _, _, .const .. => ⟨.const _ _ _ _, .nil⟩
  | _, _, .lam _ _ _ _ h1 h2 => ⟨.lam _ _ _ _ h1 h2, .nil⟩
  | _, _, .forallE _ _ _ _ h1 h2 => ⟨.forallE _ _ _ _ h1 h2, .nil⟩
  | _, _, .letE _ _ _ _ h1 h2 h3 => ⟨.letE _ _ _ _ h1 h2 h3, .nil⟩
  | _, _, .lit .. => ⟨.lit _ _ _, .nil⟩
  | _, _, .mdata _ _ _ h1 => ⟨.mdata _ _ _ h1, .nil⟩
  | _, _, .proj _ _ _ _ h1 => ⟨.proj _ _ _ _ h1, .nil⟩

/-! ## The de Bruijn helpers -/

section
variable {ρ : Name → Name}

theorem liftLoose_go_ren (n : Nat) : ∀ {a b : Expr} (c : Nat), Ren ρ a b →
    Ren ρ (Ix.Compile.Canon.liftLoose.go n a c) (Ix.Compile.Canon.liftLoose.go n b c)
  | _, _, c, .bvar i .. => by
    simp only [Ix.Compile.Canon.liftLoose.go]; split <;> exact .bvar _ _ _
  | _, _, _, .fvar .. => .fvar _ _ _
  | _, _, _, .mvar .. => .mvar _ _ _
  | _, _, _, .sort .. => .sort _ _ _
  | _, _, _, .const .. => .const _ _ _ _
  | _, _, _, .lit .. => .lit _ _ _
  | _, _, c, .app _ _ h1 h2 => Ren.mkApp' (liftLoose_go_ren n c h1) (liftLoose_go_ren n c h2)
  | _, _, c, .lam _ _ _ _ h1 h2 =>
    Ren.mkLam' _ _ (liftLoose_go_ren n c h1) (liftLoose_go_ren n (c + 1) h2)
  | _, _, c, .forallE _ _ _ _ h1 h2 =>
    Ren.mkForallE' _ _ (liftLoose_go_ren n c h1) (liftLoose_go_ren n (c + 1) h2)
  | _, _, c, .letE _ _ _ _ h1 h2 h3 =>
    Ren.mkLetE' _ _ (liftLoose_go_ren n c h1) (liftLoose_go_ren n c h2)
      (liftLoose_go_ren n (c + 1) h3)
  | _, _, c, .mdata _ _ _ h1 => Ren.mkMData' _ (liftLoose_go_ren n c h1)
  | _, _, c, .proj _ _ _ _ h1 => Ren.mkProj' _ _ (liftLoose_go_ren n c h1)

theorem liftLoose_ren {a b : Expr} (h : Ren ρ a b) (n c : Nat) :
    Ren ρ (liftLoose a n c) (liftLoose b n c) := by
  unfold liftLoose; split
  · exact h
  · exact liftLoose_go_ren n c h

theorem lowerLoose_go_ren (n : Nat) : ∀ {a b : Expr} (c : Nat), Ren ρ a b →
    Ren ρ (Ix.Compile.Canon.lowerLoose.go n a c) (Ix.Compile.Canon.lowerLoose.go n b c)
  | _, _, c, .bvar i .. => by
    simp only [Ix.Compile.Canon.lowerLoose.go]; split <;> exact .bvar _ _ _
  | _, _, _, .fvar .. => .fvar _ _ _
  | _, _, _, .mvar .. => .mvar _ _ _
  | _, _, _, .sort .. => .sort _ _ _
  | _, _, _, .const .. => .const _ _ _ _
  | _, _, _, .lit .. => .lit _ _ _
  | _, _, c, .app _ _ h1 h2 => Ren.mkApp' (lowerLoose_go_ren n c h1) (lowerLoose_go_ren n c h2)
  | _, _, c, .lam _ _ _ _ h1 h2 =>
    Ren.mkLam' _ _ (lowerLoose_go_ren n c h1) (lowerLoose_go_ren n (c + 1) h2)
  | _, _, c, .forallE _ _ _ _ h1 h2 =>
    Ren.mkForallE' _ _ (lowerLoose_go_ren n c h1) (lowerLoose_go_ren n (c + 1) h2)
  | _, _, c, .letE _ _ _ _ h1 h2 h3 =>
    Ren.mkLetE' _ _ (lowerLoose_go_ren n c h1) (lowerLoose_go_ren n c h2)
      (lowerLoose_go_ren n (c + 1) h3)
  | _, _, c, .mdata _ _ _ h1 => Ren.mkMData' _ (lowerLoose_go_ren n c h1)
  | _, _, c, .proj _ _ _ _ h1 => Ren.mkProj' _ _ (lowerLoose_go_ren n c h1)

theorem lowerLoose_ren {a b : Expr} (h : Ren ρ a b) (n c : Nat) :
    Ren ρ (lowerLoose a n c) (lowerLoose b n c) := by
  unfold lowerLoose; split
  · exact h
  · exact lowerLoose_go_ren n c h

theorem ARen.size {as bs : Array Expr} (h : ARen ρ as bs) : as.size = bs.size := by
  have := LRen.length h; simpa using this

theorem ARen.get {as bs : Array Expr} (h : ARen ρ as bs) (i : Nat) (hi : i < as.size)
    (hi' : i < bs.size) : Ren ρ as[i] bs[i] := by
  have := LRen.get h i
  simp only [Array.getElem?_toList] at this
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] at this
  exact this

theorem instantiateRevAt_ren {as bs : Array Expr} (hab : ARen ρ as bs) :
    ∀ {a b : Expr} (d : Nat), Ren ρ a b → Ren ρ (instantiateRevAt as a d) (instantiateRevAt bs b d)
  | _, _, d, .bvar i .. => by
    simp only [instantiateRevAt]
    have hs := hab.size
    split
    · split
      · rename_i h1 h2
        have h2' : i - d < bs.size := by omega
        simp only [h2', ↓reduceDIte]
        exact liftLoose_ren (hab.get _ h2 h2') d 0
      · rename_i h1 h2
        have h2' : ¬ i - d < bs.size := by omega
        simp only [h2', ↓reduceDIte, hs]; exact .bvar _ _ _
    · exact .bvar _ _ _
  | _, _, _, .fvar .. => .fvar _ _ _
  | _, _, _, .mvar .. => .mvar _ _ _
  | _, _, _, .sort .. => .sort _ _ _
  | _, _, _, .const .. => .const _ _ _ _
  | _, _, _, .lit .. => .lit _ _ _
  | _, _, d, .app _ _ h1 h2 =>
    Ren.mkApp' (instantiateRevAt_ren hab d h1) (instantiateRevAt_ren hab d h2)
  | _, _, d, .lam _ _ _ _ h1 h2 =>
    Ren.mkLam' _ _ (instantiateRevAt_ren hab d h1) (instantiateRevAt_ren hab (d + 1) h2)
  | _, _, d, .forallE _ _ _ _ h1 h2 =>
    Ren.mkForallE' _ _ (instantiateRevAt_ren hab d h1) (instantiateRevAt_ren hab (d + 1) h2)
  | _, _, d, .letE _ _ _ _ h1 h2 h3 =>
    Ren.mkLetE' _ _ (instantiateRevAt_ren hab d h1) (instantiateRevAt_ren hab d h2)
      (instantiateRevAt_ren hab (d + 1) h3)
  | _, _, d, .mdata _ _ _ h1 => Ren.mkMData' _ (instantiateRevAt_ren hab d h1)
  | _, _, d, .proj _ _ _ _ h1 => Ren.mkProj' _ _ (instantiateRevAt_ren hab d h1)

theorem instantiateRev_ren {as bs : Array Expr} (hab : ARen ρ as bs) {a b : Expr} (h : Ren ρ a b) :
    Ren ρ (instantiateRev a as) (instantiateRev b bs) := by
  unfold instantiateRev
  have hs := hab.size
  have e : bs.isEmpty = as.isEmpty := by unfold Array.isEmpty; rw [hs]
  rw [e]
  cases as.isEmpty
  · exact instantiateRevAt_ren hab 0 h
  · exact h

theorem ARen.reverse {as bs : Array Expr} (h : ARen ρ as bs) : ARen ρ as.reverse bs.reverse := by
  unfold ARen at h ⊢
  simp only [Array.toList_reverse]
  generalize as.toList = l at h; generalize bs.toList = l' at h
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => simp only [List.reverse_cons]; exact ih.append (.cons h1 .nil)

theorem instLocals_ren {as bs : Array Expr} (hab : ARen ρ as bs) {a b : Expr} (h : Ren ρ a b) :
    Ren ρ (Ix.Compile.Image.instLocals a as) (Ix.Compile.Image.instLocals b bs) :=
  instantiateRev_ren hab.reverse h

theorem stripMdata_ren : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (Ix.Compile.Canon.stripMdata a) (Ix.Compile.Canon.stripMdata b)
  | _, _, .mdata _ _ _ h1 => by simp only [Ix.Compile.Canon.stripMdata]; exact stripMdata_ren h1
  | _, _, h@(.bvar ..) | _, _, h@(.fvar ..) | _, _, h@(.mvar ..) | _, _, h@(.sort ..)
  | _, _, h@(.const ..) | _, _, h@(.lit ..) | _, _, h@(.app ..) | _, _, h@(.lam ..)
  | _, _, h@(.forallE ..) | _, _, h@(.letE ..) | _, _, h@(.proj ..) => by
    simp only [Ix.Compile.Canon.stripMdata]; exact h

theorem forallArity_ren : ∀ {a b : Expr}, Ren ρ a b →
    Ix.Compile.Image.forallArity b = Ix.Compile.Image.forallArity a
  | _, _, .forallE _ _ _ _ _ h2 => by
    simp only [Ix.Compile.Image.forallArity, forallArity_ren h2]
  | _, _, .mdata _ _ _ h1 => by simp only [Ix.Compile.Image.forallArity, forallArity_ren h1]
  | _, _, .bvar .. | _, _, .fvar .. | _, _, .mvar .. | _, _, .sort .. | _, _, .const ..
  | _, _, .lit .. | _, _, .app .. | _, _, .lam .. | _, _, .letE .. | _, _, .proj .. => rfl

/-- Binders related: same name and info, types renamed. -/
def BRen (ρ : Name → Name) (x y : Ix.Compile.Canon.Binder) : Prop :=
  x.1 = y.1 ∧ Ren ρ x.2.1 y.2.1 ∧ x.2.2 = y.2.2

/-- Pointwise `BRen`. -/
def BsRen (ρ : Name → Name) (xs ys : Array Ix.Compile.Canon.Binder) : Prop :=
  xs.size = ys.size ∧ ∀ i (h : i < xs.size) (h' : i < ys.size), BRen ρ xs[i] ys[i]

theorem BsRen.push {xs ys : Array Ix.Compile.Canon.Binder} (h : BsRen ρ xs ys) {x y}
    (hxy : BRen ρ x y) : BsRen ρ (xs.push x) (ys.push y) := by
  have hsz := h.1
  refine ⟨by simp [h.1], fun i hi hi' => ?_⟩
  simp only [Array.size_push] at hi hi'
  by_cases hl : i < xs.size
  · rw [Array.getElem_push_lt hl, Array.getElem_push_lt (by omega)]; exact h.2 i hl (by omega)
  · have e1 : i = xs.size := by omega
    have e2 : i = ys.size := by rw [← h.1]; omega
    subst e1
    rw [Array.getElem_push_eq]; simp only [e2, Array.getElem_push_eq]; exact hxy

theorem peelForalls_ren : ∀ (n : Nat) {a b : Expr} {xs ys : Array Ix.Compile.Canon.Binder},
    Ren ρ a b → BsRen ρ xs ys →
    BsRen ρ (Ix.Compile.Canon.peelForalls n a xs).1 (Ix.Compile.Canon.peelForalls n b ys).1 ∧
      Ren ρ (Ix.Compile.Canon.peelForalls n a xs).2 (Ix.Compile.Canon.peelForalls n b ys).2
  | 0, _, _, _, _, h, hb => ⟨hb, h⟩
  | n + 1, a, b, xs, ys, h, hb => by
    have hs := stripMdata_ren h
    simp only [Ix.Compile.Canon.peelForalls]
    generalize Ix.Compile.Canon.stripMdata a = a' at hs
    generalize Ix.Compile.Canon.stripMdata b = b' at hs
    cases hs with
    | forallE nm bi _ _ h1 h2 =>
      exact peelForalls_ren n h2 (hb.push ⟨rfl, h1, rfl⟩)
    | bvar | fvar | mvar | sort | const | lit => exact ⟨hb, by first | exact .bvar _ _ _ | exact .fvar _ _ _ | exact .mvar _ _ _ | exact .sort _ _ _ | exact .const _ _ _ _ | exact .lit _ _ _⟩
    | app _ _ h1 h2 => exact ⟨hb, .app _ _ h1 h2⟩
    | lam _ _ _ _ h1 h2 => exact ⟨hb, .lam _ _ _ _ h1 h2⟩
    | letE _ _ _ _ h1 h2 h3 => exact ⟨hb, .letE _ _ _ _ h1 h2 h3⟩
    | mdata _ _ _ h1 => exact ⟨hb, .mdata _ _ _ h1⟩
    | proj _ _ _ _ h1 => exact ⟨hb, .proj _ _ _ _ h1⟩

theorem instForall_ren {a b : Expr} {as bs : Array Expr} (h : Ren ρ a b) (hab : ARen ρ as bs) :
    match Ix.Compile.Image.instForall a as, Ix.Compile.Image.instForall b bs with
    | .ok x, .ok y => Ren ρ x y
    | .error _, .error _ => True
    | _, _ => False := by
  unfold Ix.Compile.Image.instForall
  have hp := peelForalls_ren as.size h (xs := #[]) (ys := #[]) ⟨rfl, fun i h => by simp at h⟩
  have hs := hab.size
  rw [← hs]
  generalize Ix.Compile.Canon.peelForalls as.size a #[] = p at hp
  generalize Ix.Compile.Canon.peelForalls as.size b #[] = q at hp
  obtain ⟨pb, pbody⟩ := p
  obtain ⟨qb, qbody⟩ := q
  obtain ⟨⟨hsz, -⟩, hbody⟩ := hp
  simp only at hsz hbody ⊢
  rw [← hsz]
  cases (pb.size != as.size)
  · exact instLocals_ren hab hbody
  · trivial

end

/-! ## Finding positions -/

theorem list_findIdx?_congr {α β : Type} {p : α → Bool} {q : β → Bool} :
    ∀ (l : List α) (l' : List β), l.length = l'.length →
      (∀ i (h : i < l.length) (h' : i < l'.length), p l[i] = q l'[i]) → l.findIdx? p = l'.findIdx? q
  | [], [], _, _ => rfl
  | a :: l, b :: l', hl, h => by
    simp only [List.findIdx?_cons]
    have h0 := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, list_findIdx?_congr l l' (by simpa using hl) fun i hi hi' => by
      have := h (i + 1) (by simp; omega) (by simp; omega)
      rw [List.getElem_cons_succ, List.getElem_cons_succ] at this; exact this]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem array_findIdx?_congr {α β : Type} {p : α → Bool} {q : β → Bool} (xs : Array α) (ys : Array β)
    (hs : xs.size = ys.size) (h : ∀ i (hi : i < xs.size) (hi' : i < ys.size), p xs[i] = q ys[i]) :
    xs.findIdx? p = ys.findIdx? q := by
  rcases xs with ⟨l⟩; rcases ys with ⟨l'⟩
  simp only [List.findIdx?_toArray]
  exact list_findIdx?_congr l l' (by simpa using hs) fun i hi hi' => by simpa using h i hi hi'

theorem array_idxOf?_eq {α : Type} [BEq α] (xs : Array α) (a : α) :
    xs.idxOf? a = xs.toList.findIdx? (· == a) := by
  rw [Array.idxOf?_eq_map_finIdxOf?_val]
  show _ = List.idxOf? a xs.toList
  rw [List.idxOf?_eq_map_finIdxOf?_val, Array.finIdxOf?_toList, Option.map_map]; rfl

/-- `ρ` keeps `==` on the names satisfying `P`. -/
def InjOn (ρ : Name → Name) (P : Name → Prop) : Prop := ∀ a b, P a → P b → (ρ a == ρ b) = (a == b)

theorem array_idxOf?_ren {ρ : Name → Name} {P : Name → Prop} (hi : InjOn ρ P) (xs : Array Name)
    (n : Name) (hx : ∀ x ∈ xs, P x) (hn : P n) : (xs.map ρ).idxOf? (ρ n) = xs.idxOf? n := by
  rw [array_idxOf?_eq, array_idxOf?_eq]
  rcases xs with ⟨l⟩
  simp only [List.map_toArray]
  apply list_findIdx?_congr _ _ (by simp)
  intro i h h'
  simp only [List.getElem_map]
  exact hi _ _ (hx _ (by simp)) hn

/-! ## Comparisons -/

section
variable {ρ : Name → Name}

theorem alphaEq_ren {P : Name → Prop} (hi : InjOn ρ P) : ∀ {a a' b b' : Expr}, Ren ρ a a' →
    Ren ρ b b' → FvAll P a → FvAll P b →
    Ix.Compile.Image.alphaEq a' b' = Ix.Compile.Image.alphaEq a b
  | _, _, _, _, .bvar .., hb, _, _ => by cases hb <;> rfl
  | _, _, _, _, .fvar n .., hb, ha, hbP => by
    cases hb
    case fvar m _ _ => simp only [Ix.Compile.Image.alphaEq]; exact hi _ _ ha hbP
    all_goals rfl
  | _, _, _, _, .mvar .., hb, _, _ => by cases hb <;> rfl
  | _, _, _, _, .sort .., hb, _, _ => by cases hb <;> rfl
  | _, _, _, _, .const .., hb, _, _ => by cases hb <;> rfl
  | _, _, _, _, .lit .., hb, _, _ => by cases hb <;> rfl
  | _, _, _, _, .app _ _ h1 h2, hb, ha, hbP => by
    cases hb
    case app _ _ h3 h4 =>
      simp only [Ix.Compile.Image.alphaEq]
      rw [alphaEq_ren hi h1 h3 ha.1 hbP.1, alphaEq_ren hi h2 h4 ha.2 hbP.2]
    all_goals rfl
  | _, _, _, _, .lam _ _ _ _ h1 h2, hb, ha, hbP => by
    cases hb
    case lam _ _ _ _ h3 h4 =>
      simp only [Ix.Compile.Image.alphaEq]
      rw [alphaEq_ren hi h1 h3 ha.1 hbP.1, alphaEq_ren hi h2 h4 ha.2 hbP.2]
    all_goals rfl
  | _, _, _, _, .forallE _ _ _ _ h1 h2, hb, ha, hbP => by
    cases hb
    case forallE _ _ _ _ h3 h4 =>
      simp only [Ix.Compile.Image.alphaEq]
      rw [alphaEq_ren hi h1 h3 ha.1 hbP.1, alphaEq_ren hi h2 h4 ha.2 hbP.2]
    all_goals rfl
  | _, _, _, _, .letE _ _ _ _ h1 h2 h5, hb, ha, hbP => by
    cases hb
    case letE _ _ _ _ h3 h4 h6 =>
      simp only [Ix.Compile.Image.alphaEq]
      rw [alphaEq_ren hi h1 h3 ha.1 hbP.1, alphaEq_ren hi h2 h4 ha.2.1 hbP.2.1,
        alphaEq_ren hi h5 h6 ha.2.2 hbP.2.2]
    all_goals rfl
  | _, _, _, _, .mdata _ _ _ h1, hb, ha, hbP => by
    cases hb
    case mdata _ _ _ h3 =>
      simp only [Ix.Compile.Image.alphaEq]
      exact alphaEq_ren hi h1 h3 ha hbP
    all_goals rfl
  | _, _, _, _, .proj _ _ _ _ h1, hb, ha, hbP => by
    cases hb
    case proj _ _ _ _ h3 =>
      simp only [Ix.Compile.Image.alphaEq]
      rw [alphaEq_ren hi h1 h3 ha hbP]
    all_goals rfl

/-- A local renamed: its variable by `ρ`, its type by `Ren ρ`, name and info kept. -/
def LocRen (ρ : Name → Name) (l l' : Ix.Compile.Image.Local) : Prop :=
  l'.fvar = ρ l.fvar ∧ l'.userName = l.userName ∧ Ren ρ l.type l'.type ∧ l'.bi = l.bi

/-- Arrays of locals renamed pointwise. -/
def LsRen (ρ : Name → Name) (xs ys : Array Ix.Compile.Image.Local) : Prop :=
  xs.size = ys.size ∧ ∀ i (h : i < xs.size) (h' : i < ys.size), LocRen ρ xs[i] ys[i]

theorem fvarIdx?_ren {P : Name → Prop} (hi : InjOn ρ P) {xs ys : Array Ix.Compile.Image.Local}
    (hxy : LsRen ρ xs ys) (hx : ∀ l ∈ xs, P l.fvar) {e e' : Expr} (he : Ren ρ e e') (heP : FvAll P e) :
    Ix.Compile.Image.fvarIdx? ys e' = Ix.Compile.Image.fvarIdx? xs e := by
  cases he
  case fvar n _ _ =>
    simp only [Ix.Compile.Image.fvarIdx?]
    apply array_findIdx?_congr _ _ hxy.1.symm
    intro i hi1 hi2
    rw [(hxy.2 i hi2 hi1).1]
    exact hi _ _ (hx _ (Array.getElem_mem hi2)) heP
  all_goals rfl

end

/-! ## Abstraction and binders -/

section
variable {ρ : Name → Name}

theorem abstractFVars_go_ren {P : Name → Prop} (hi : InjOn ρ P) (xs : Array Name)
    (hx : ∀ x ∈ xs, P x) : ∀ {a b : Expr} (d : Nat), Ren ρ a b → FvAll P a →
    Ren ρ (Ix.Compile.Image.abstractFVars.go xs a d)
      (Ix.Compile.Image.abstractFVars.go (xs.map ρ) b d)
  | _, _, d, .fvar n h h', hP => by
    simp only [Ix.Compile.Image.abstractFVars.go]
    rw [array_idxOf?_ren hi xs n hx hP]
    cases xs.idxOf? n with
    | some i => simp only [Array.size_map]; exact .bvar _ _ _
    | none => exact .fvar _ _ _
  | _, _, _, .bvar .., _ => .bvar _ _ _
  | _, _, _, .mvar .., _ => .mvar _ _ _
  | _, _, _, .sort .., _ => .sort _ _ _
  | _, _, _, .const .., _ => .const _ _ _ _
  | _, _, _, .lit .., _ => .lit _ _ _
  | _, _, d, .app _ _ h1 h2, hP =>
    Ren.mkApp' (abstractFVars_go_ren hi xs hx d h1 hP.1) (abstractFVars_go_ren hi xs hx d h2 hP.2)
  | _, _, d, .lam _ _ _ _ h1 h2, hP =>
    Ren.mkLam' _ _ (abstractFVars_go_ren hi xs hx d h1 hP.1)
      (abstractFVars_go_ren hi xs hx (d + 1) h2 hP.2)
  | _, _, d, .forallE _ _ _ _ h1 h2, hP =>
    Ren.mkForallE' _ _ (abstractFVars_go_ren hi xs hx d h1 hP.1)
      (abstractFVars_go_ren hi xs hx (d + 1) h2 hP.2)
  | _, _, d, .letE _ _ _ _ h1 h2 h3, hP =>
    Ren.mkLetE' _ _ (abstractFVars_go_ren hi xs hx d h1 hP.1)
      (abstractFVars_go_ren hi xs hx d h2 hP.2.1) (abstractFVars_go_ren hi xs hx (d + 1) h3 hP.2.2)
  | _, _, d, .mdata _ _ _ h1, hP => Ren.mkMData' _ (abstractFVars_go_ren hi xs hx d h1 hP)
  | _, _, d, .proj _ _ _ _ h1, hP => Ren.mkProj' _ _ (abstractFVars_go_ren hi xs hx d h1 hP)

theorem abstractFVars_ren {P : Name → Prop} (hi : InjOn ρ P) (xs : Array Name)
    (hx : ∀ x ∈ xs, P x) {a b : Expr} (h : Ren ρ a b) (hP : FvAll P a) :
    Ren ρ (Ix.Compile.Image.abstractFVars xs a) (Ix.Compile.Image.abstractFVars (xs.map ρ) b) := by
  unfold Ix.Compile.Image.abstractFVars
  have e : (xs.map ρ).isEmpty = xs.isEmpty := by unfold Array.isEmpty; simp
  rw [e]
  cases xs.isEmpty
  · exact abstractFVars_go_ren hi xs hx 0 h hP
  · exact h

theorem LsRen.names {xs ys : Array Ix.Compile.Image.Local} (h : LsRen ρ xs ys) :
    ys.map (·.fvar) = (xs.map (·.fvar)).map ρ := by
  apply Array.ext
  · simp [h.1]
  · intro i h1 h2
    simp only [Array.getElem_map]
    exact (h.2 i (by simpa using h2) (by simpa using h1)).1

/-- One binder of `mkBinders`. -/
def binderStep (isLam : Bool) (names : Array Name) (p : Ix.Compile.Image.Local × Nat) (acc : Expr) :
    Expr :=
  if isLam then Expr.mkLam p.1.userName
      (Ix.Compile.Image.abstractFVars (names.extract 0 p.2) p.1.type) acc p.1.bi
    else Expr.mkForallE p.1.userName
      (Ix.Compile.Image.abstractFVars (names.extract 0 p.2) p.1.type) acc p.1.bi

/-- `mkBinders` as a right fold over the binders. -/
theorem mkBinders_eq (isLam : Bool) (xs : Array Ix.Compile.Image.Local) (b : Expr) :
    Ix.Compile.Image.mkBinders isLam xs b =
      xs.zipIdx.foldr (binderStep isLam (xs.map (·.fvar)))
        (Ix.Compile.Image.abstractFVars (xs.map (·.fvar)) b) := by
  simp [Ix.Compile.Image.mkBinders, Id.run]; rfl

theorem mkBinders_ren {P : Name → Prop} (hi : InjOn ρ P) (isLam : Bool)
    {xs ys : Array Ix.Compile.Image.Local} (hxy : LsRen ρ xs ys)
    (hx : ∀ l ∈ xs, P l.fvar ∧ FvAll P l.type) {a b : Expr} (h : Ren ρ a b) (hP : FvAll P a) :
    Ren ρ (Ix.Compile.Image.mkBinders isLam xs a) (Ix.Compile.Image.mkBinders isLam ys b) := by
  rw [mkBinders_eq, mkBinders_eq, hxy.names, ← Array.foldr_toList, ← Array.foldr_toList]
  have hn : ∀ x ∈ xs.map (·.fvar), P x := by
    intro x hm
    obtain ⟨l, hl, rfl⟩ := Array.mem_map.1 hm
    exact (hx l hl).1
  have h0 := abstractFVars_ren hi (xs.map (·.fvar)) hn h hP
  have hstep : ∀ (p q : Ix.Compile.Image.Local × Nat), LocRen ρ p.1 q.1 → p.2 = q.2 → p.1 ∈ xs →
      ∀ acc acc', Ren ρ acc acc' →
      Ren ρ (binderStep isLam (xs.map (·.fvar)) p acc)
        (binderStep isLam ((xs.map (·.fvar)).map ρ) q acc') := by
    intro p q ⟨hf, hu, ht, hb⟩ hidx hmem acc acc' hacc
    have hext : ∀ x ∈ (xs.map (·.fvar)).extract 0 p.2, P x := by
      intro x hm
      obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hm
      exact hn _ (Array.getElem_mem _)
    have hty := abstractFVars_ren hi ((xs.map (·.fvar)).extract 0 p.2) hext ht (hx _ hmem).2
    rw [Array.map_extract] at hty
    unfold binderStep
    cases isLam
    · simp only [Bool.false_eq_true, ↓reduceIte, hu, hb, ← hidx]
      exact Ren.mkForallE' _ _ hty hacc
    · simp only [↓reduceIte, hu, hb, ← hidx]
      exact Ren.mkLam' _ _ hty hacc
  have hlist : ∀ (L1 L2 : List (Ix.Compile.Image.Local × Nat)), L1.length = L2.length →
      (∀ k (h1 : k < L1.length) (h2 : k < L2.length),
        LocRen ρ L1[k].1 L2[k].1 ∧ L1[k].2 = L2[k].2 ∧ L1[k].1 ∈ xs) →
      Ren ρ (L1.foldr (binderStep isLam (xs.map (·.fvar)))
          (Ix.Compile.Image.abstractFVars (xs.map (·.fvar)) a))
        (L2.foldr (binderStep isLam ((xs.map (·.fvar)).map ρ))
          (Ix.Compile.Image.abstractFVars ((xs.map (·.fvar)).map ρ) b)) := by
    intro L1
    induction L1 with
    | nil => intro L2 hl _; cases L2 with
      | nil => exact h0
      | cons => simp at hl
    | cons p L1 ih =>
      intro L2 hl hk
      cases L2 with
      | nil => simp at hl
      | cons q L2 =>
        simp only [List.foldr_cons]
        have h0' := hk 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0'
        apply hstep p q h0'.1 h0'.2.1 h0'.2.2
        apply ih L2 (by simpa using hl)
        intro k h1 h2
        have := hk (k + 1) (by simp; omega) (by simp; omega)
        rw [List.getElem_cons_succ, List.getElem_cons_succ] at this; exact this
  apply hlist _ _ (by simp [hxy.1])
  intro k h1 h2
  simp only [Array.length_toList, Array.size_zipIdx] at h1 h2
  simp only [Array.getElem_toList, Array.getElem_zipIdx]
  refine ⟨hxy.2 _ h1 h2, ?_, ?_⟩ <;> simp

theorem mkLambda_ren {P : Name → Prop} (hi : InjOn ρ P) {xs ys : Array Ix.Compile.Image.Local}
    (hxy : LsRen ρ xs ys) (hx : ∀ l ∈ xs, P l.fvar ∧ FvAll P l.type) {a b : Expr} (h : Ren ρ a b)
    (hP : FvAll P a) : Ren ρ (Ix.Compile.Image.mkLambda xs a) (Ix.Compile.Image.mkLambda ys b) :=
  mkBinders_ren hi true hxy hx h hP

theorem mkForall_ren {P : Name → Prop} (hi : InjOn ρ P) {xs ys : Array Ix.Compile.Image.Local}
    (hxy : LsRen ρ xs ys) (hx : ∀ l ∈ xs, P l.fvar ∧ FvAll P l.type) {a b : Expr} (h : Ren ρ a b)
    (hP : FvAll P a) : Ren ρ (Ix.Compile.Image.mkForall xs a) (Ix.Compile.Image.mkForall ys b) :=
  mkBinders_ren hi false hxy hx h hP

end

/-! ## Small structural functions -/

section
variable {ρ : Name → Name}

/-- Options related by `Ren`. -/
def ORen (ρ : Name → Name) : Option Expr → Option Expr → Prop
  | some a, some b => Ren ρ a b
  | none, none => True
  | _, _ => False

theorem hasLooseBVar_go_ren : ∀ {a b : Expr} (k : Nat), Ren ρ a b →
    Ix.Compile.Image.hasLooseBVar.go b k = Ix.Compile.Image.hasLooseBVar.go a k
  | _, _, _, .bvar .. | _, _, _, .fvar .. | _, _, _, .mvar .. | _, _, _, .sort .. | _, _, _, .const ..
  | _, _, _, .lit .. => rfl
  | _, _, k, .app _ _ h1 h2 => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1, hasLooseBVar_go_ren k h2]
  | _, _, k, .lam _ _ _ _ h1 h2 => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1,
      hasLooseBVar_go_ren (k + 1) h2]
  | _, _, k, .forallE _ _ _ _ h1 h2 => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1,
      hasLooseBVar_go_ren (k + 1) h2]
  | _, _, k, .letE _ _ _ _ h1 h2 h3 => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1, hasLooseBVar_go_ren k h2,
      hasLooseBVar_go_ren (k + 1) h3]
  | _, _, k, .mdata _ _ _ h1 => by simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1]
  | _, _, k, .proj _ _ _ _ h1 => by simp only [Ix.Compile.Image.hasLooseBVar.go, hasLooseBVar_go_ren k h1]

/-- The η step of `etaReduce` at one binder. -/
def etaStep (n : Name) (d b' : Expr) (bi : Lean.BinderInfo) : Expr :=
  match b' with
  | .app f (.bvar 0 _) _ =>
    if !Ix.Compile.Image.hasLooseBVar f 0 then lowerLoose f 1 0 else Expr.mkLam n d b' bi
  | _ => Expr.mkLam n d b' bi

theorem etaReduce_lam (n : Name) (d b : Expr) (bi : Lean.BinderInfo) (h : Address) :
    Ix.Compile.Image.etaReduce (.lam n d b bi h) = etaStep n d (Ix.Compile.Image.etaReduce b) bi := by
  rfl

theorem etaStep_ren (n : Name) (bi : Lean.BinderInfo) {d d' x y : Expr} (hd : Ren ρ d d')
    (h : Ren ρ x y) : Ren ρ (etaStep n d x bi) (etaStep n d' y bi) := by
  unfold etaStep
  split
  · rename_i f h1 h2
    cases h with
    | app _ _ hf hz =>
      cases hz with
      | bvar _ _ _ =>
        simp only [Ix.Compile.Image.hasLooseBVar]
        have e := hasLooseBVar_go_ren 0 hf
        simp only [e]
        by_cases hc : (!Ix.Compile.Image.hasLooseBVar.go f 0) = true
        · simp only [hc, ↓reduceIte]; exact lowerLoose_ren hf 1 0
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          exact Ren.mkLam' _ _ hd (.app _ _ hf (.bvar _ _ _))
  · rename_i hx
    split
    · rename_i f' h1 h2
      exfalso
      cases h with
      | app _ _ hf hz =>
        cases hz with
        | bvar _ _ _ => exact hx _ _ _ rfl
    · exact Ren.mkLam' _ _ hd h

theorem etaReduce_ren : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (Ix.Compile.Image.etaReduce a) (Ix.Compile.Image.etaReduce b)
  | _, _, .lam n bi _ _ h1 h2 => by
    rw [etaReduce_lam, etaReduce_lam]
    exact etaStep_ren n bi h1 (etaReduce_ren h2)
  | _, _, h@(.bvar ..) | _, _, h@(.fvar ..) | _, _, h@(.mvar ..) | _, _, h@(.sort ..)
  | _, _, h@(.const ..) | _, _, h@(.lit ..) | _, _, h@(.app ..) | _, _, h@(.forallE ..)
  | _, _, h@(.letE ..) | _, _, h@(.mdata ..) | _, _, h@(.proj ..) => by
    simp only [Ix.Compile.Image.etaReduce]; exact h

theorem headConst?_ren {a b : Expr} (h : Ren ρ a b) :
    Ix.Compile.Image.headConst? b = Ix.Compile.Image.headConst? a := by
  have := (getAppFnArgs_ren h).1
  unfold Ix.Compile.Image.headConst?
  generalize (getAppFnArgs a).1 = x at this
  generalize (getAppFnArgs b).1 = y at this
  cases this <;> rfl

theorem getAppFn_ren {a b : Expr} (h : Ren ρ a b) :
    Ren ρ (Ix.Compile.Image.getAppFn a) (Ix.Compile.Image.getAppFn b) := (getAppFnArgs_ren h).1

theorem getAppArgs_ren {a b : Expr} (h : Ren ρ a b) :
    ARen ρ (Ix.Compile.Image.getAppArgs a) (Ix.Compile.Image.getAppArgs b) := (getAppFnArgs_ren h).2

theorem appArg?_ren {a b : Expr} (h : Ren ρ a b) :
    ORen ρ (Ix.Compile.Image.appArg? a) (Ix.Compile.Image.appArg? b) := by
  cases h
  case app _ _ _ h2 => exact h2
  all_goals trivial

theorem usedConstants_go_ren : ∀ {a b : Expr} (s : Array Name × Std.HashSet Name), Ren ρ a b →
    Ix.Compile.Image.usedConstants.go b s = Ix.Compile.Image.usedConstants.go a s
  | _, _, _, .bvar .. | _, _, _, .fvar .. | _, _, _, .mvar .. | _, _, _, .sort .. | _, _, _, .const ..
  | _, _, _, .lit .. => rfl
  | _, _, s, .app _ _ h1 h2 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1,
      usedConstants_go_ren _ h2]
  | _, _, s, .lam _ _ _ _ h1 h2 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1,
      usedConstants_go_ren _ h2]
  | _, _, s, .forallE _ _ _ _ h1 h2 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1,
      usedConstants_go_ren _ h2]
  | _, _, s, .letE _ _ _ _ h1 h2 h3 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1,
      usedConstants_go_ren _ h2, usedConstants_go_ren _ h3]
  | _, _, s, .mdata _ _ _ h1 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1]
  | _, _, s, .proj _ _ _ _ h1 => by
    simp only [Ix.Compile.Image.usedConstants.go, usedConstants_go_ren s h1]

theorem usedConstants_ren {a b : Expr} (h : Ren ρ a b) :
    Ix.Compile.Image.usedConstants b = Ix.Compile.Image.usedConstants a := by
  unfold Ix.Compile.Image.usedConstants; rw [usedConstants_go_ren _ h]

theorem findSub?_ren {p : Expr → Bool} (hp : ∀ a b, Ren ρ a b → p b = p a) :
    ∀ {a b : Expr}, Ren ρ a b → ORen ρ (Ix.Compile.Image.findSub? p a) (Ix.Compile.Image.findSub? p b)
  | a, b, h => by
    unfold Ix.Compile.Image.findSub?
    rw [hp a b h]
    split
    · exact h
    · have first2_ren : ∀ {x y x' y' : Option Expr}, ORen ρ x x' → ORen ρ y y' →
          ORen ρ (Ix.Compile.Image.first2 x y) (Ix.Compile.Image.first2 x' y') := by
        intro x y x' y' hx hy
        cases x <;> cases x' <;> simp_all [ORen, Ix.Compile.Image.first2]
      cases h with
      | app _ _ h1 h2 => exact first2_ren (findSub?_ren hp h1) (findSub?_ren hp h2)
      | lam _ _ _ _ h1 h2 => exact first2_ren (findSub?_ren hp h1) (findSub?_ren hp h2)
      | forallE _ _ _ _ h1 h2 => exact first2_ren (findSub?_ren hp h1) (findSub?_ren hp h2)
      | letE _ _ _ _ h1 h2 h3 =>
        exact first2_ren (findSub?_ren hp h1) (first2_ren (findSub?_ren hp h2) (findSub?_ren hp h3))
      | proj _ _ _ _ h1 => exact findSub?_ren hp h1
      | mdata _ _ _ h1 => exact findSub?_ren hp h1
      | bvar | fvar | mvar | sort | const | lit => trivial

theorem stripSort_ren : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (Ix.Compile.Image.stripSort a) (Ix.Compile.Image.stripSort b)
  | _, _, .forallE _ _ _ _ h1 h2 => by
    simp only [Ix.Compile.Image.stripSort]; exact Ren.mkForallE' _ _ h1 (stripSort_ren h2)
  | _, _, .mdata _ _ _ h1 => by simp only [Ix.Compile.Image.stripSort]; exact stripSort_ren h1
  | _, _, .sort .. => by simp only [Ix.Compile.Image.stripSort]; exact .sort _ _ _
  | _, _, h@(.bvar ..) | _, _, h@(.fvar ..) | _, _, h@(.mvar ..) | _, _, h@(.const ..)
  | _, _, h@(.lit ..) | _, _, h@(.app ..) | _, _, h@(.lam ..) | _, _, h@(.letE ..)
  | _, _, h@(.proj ..) => by simp only [Ix.Compile.Image.stripSort]; exact h

theorem motiveLevel_ren : ∀ {a b : Expr}, Ren ρ a b →
    Ix.Compile.Image.motiveLevel b = Ix.Compile.Image.motiveLevel a
  | _, _, .forallE _ _ _ _ _ h2 => by simp only [Ix.Compile.Image.motiveLevel, motiveLevel_ren h2]
  | _, _, .mdata _ _ _ h1 => by simp only [Ix.Compile.Image.motiveLevel, motiveLevel_ren h1]
  | _, _, .sort .. | _, _, .bvar .. | _, _, .fvar .. | _, _, .mvar .. | _, _, .const ..
  | _, _, .lit .. | _, _, .app .. | _, _, .lam .. | _, _, .letE .. | _, _, .proj .. => rfl

theorem substLevels_go_ren (ps : Array Name) (us : Array Level) : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (Ix.Compile.Canon.substLevels.go ps us a) (Ix.Compile.Canon.substLevels.go ps us b)
  | _, _, .sort .. => .sort _ _ _
  | _, _, .const .. => .const _ _ _ _
  | _, _, .app _ _ h1 h2 => Ren.mkApp' (substLevels_go_ren ps us h1) (substLevels_go_ren ps us h2)
  | _, _, .lam _ _ _ _ h1 h2 =>
    Ren.mkLam' _ _ (substLevels_go_ren ps us h1) (substLevels_go_ren ps us h2)
  | _, _, .forallE _ _ _ _ h1 h2 =>
    Ren.mkForallE' _ _ (substLevels_go_ren ps us h1) (substLevels_go_ren ps us h2)
  | _, _, .letE _ _ _ _ h1 h2 h3 =>
    Ren.mkLetE' _ _ (substLevels_go_ren ps us h1) (substLevels_go_ren ps us h2)
      (substLevels_go_ren ps us h3)
  | _, _, .proj _ _ _ _ h1 => Ren.mkProj' _ _ (substLevels_go_ren ps us h1)
  | _, _, .mdata _ _ _ h1 => Ren.mkMData' _ (substLevels_go_ren ps us h1)
  | _, _, .bvar .. => .bvar _ _ _
  | _, _, .fvar .. => .fvar _ _ _
  | _, _, .mvar .. => .mvar _ _ _
  | _, _, .lit .. => .lit _ _ _

theorem substLevels_ren (ps : Array Name) (us : Array Level) {a b : Expr} (h : Ren ρ a b) :
    Ren ρ (Ix.Compile.Canon.substLevels ps us a) (Ix.Compile.Canon.substLevels ps us b) := by
  unfold Ix.Compile.Canon.substLevels; split
  · exact h
  · exact substLevels_go_ren ps us h

theorem canonicalizeConstNames_go_ren (m : Std.HashMap Name Name) : ∀ {a b : Expr}, Ren ρ a b →
    Ren ρ (Ix.Compile.Canon.canonicalizeConstNames.go m a)
      (Ix.Compile.Canon.canonicalizeConstNames.go m b)
  | _, _, .const n us .. => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go]; split
    · exact .const _ _ _ _
    · exact .const _ _ _ _
  | _, _, .app _ _ h1 h2 =>
    Ren.mkApp' (canonicalizeConstNames_go_ren m h1) (canonicalizeConstNames_go_ren m h2)
  | _, _, .lam _ _ _ _ h1 h2 =>
    Ren.mkLam' _ _ (canonicalizeConstNames_go_ren m h1) (canonicalizeConstNames_go_ren m h2)
  | _, _, .forallE _ _ _ _ h1 h2 =>
    Ren.mkForallE' _ _ (canonicalizeConstNames_go_ren m h1) (canonicalizeConstNames_go_ren m h2)
  | _, _, .letE _ _ _ _ h1 h2 h3 =>
    Ren.mkLetE' _ _ (canonicalizeConstNames_go_ren m h1) (canonicalizeConstNames_go_ren m h2)
      (canonicalizeConstNames_go_ren m h3)
  | _, _, .proj _ _ _ _ h1 => Ren.mkProj' _ _ (canonicalizeConstNames_go_ren m h1)
  | _, _, .mdata _ _ _ h1 => Ren.mkMData' _ (canonicalizeConstNames_go_ren m h1)
  | _, _, .bvar .. => .bvar _ _ _
  | _, _, .fvar .. => .fvar _ _ _
  | _, _, .mvar .. => .mvar _ _ _
  | _, _, .sort .. => .sort _ _ _
  | _, _, .lit .. => .lit _ _ _

theorem canonicalizeConstNames_ren (m : Std.HashMap Name Name) {a b : Expr} (h : Ren ρ a b) :
    Ren ρ (Ix.Compile.Canon.canonicalizeConstNames m a)
      (Ix.Compile.Canon.canonicalizeConstNames m b) := by
  unfold Ix.Compile.Canon.canonicalizeConstNames; split
  · exact h
  · exact canonicalizeConstNames_go_ren m h

end

/-! ## Related `Except` results -/

/-- Both fail, or both succeed with related values. -/
def ExRel {α β : Type} (R : α → β → Prop) : Except String α → Except String β → Prop
  | .ok a, .ok b => R a b
  | .error _, .error _ => True
  | _, _ => False

theorem ExRel.ok {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ExRel R (.ok a) (.ok b) := h

theorem ExRel.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ExRel R (Pure.pure a) (Pure.pure b) := h

theorem ExRel.err {α β : Type} {R : α → β → Prop} (e e' : String) :
    ExRel R (Except.error e : Except String α) (Except.error e' : Except String β) := trivial

theorem ExRel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except String α} {y : Except String β} {f : α → Except String γ} {g : β → Except String δ}
    (hx : ExRel R x y) (hf : ∀ a b, R a b → ExRel S (f a) (g b)) : ExRel S (x >>= f) (y >>= g) := by
  cases x <;> cases y <;> simp_all [ExRel] <;> first | trivial | exact hf _ _ hx

theorem ExRel.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except String α} {y : Except String β} {f : α → γ} {g : β → δ}
    (hx : ExRel R x y) (hf : ∀ a b, R a b → S (f a) (g b)) : ExRel S (f <$> x) (g <$> y) := by
  cases x <;> cases y <;> simp_all [ExRel] <;> first | trivial | exact hf _ _ hx

theorem ExRel.ok_of {α β : Type} {R : α → β → Prop} {x : Except String α} {y : Except String β}
    (h : ExRel R x y) {a : α} (ha : x = .ok a) : ∃ b, y = .ok b ∧ R a b := by
  subst ha; cases y <;> simp_all [ExRel]

/-! ## The development without tables (X1's core) -/

section
variable {ρ : Name → Name}

theorem looseRangeP_ren : ∀ {a b : Expr}, Ren ρ a b → looseRangeP b = looseRangeP a
  | _, _, .bvar .. | _, _, .fvar .. | _, _, .mvar .. | _, _, .sort .. | _, _, .const ..
  | _, _, .lit .. => rfl
  | _, _, .app _ _ h1 h2 => by simp only [looseRangeP, looseRangeP_ren h1, looseRangeP_ren h2]
  | _, _, .lam _ _ _ _ h1 h2 => by simp only [looseRangeP, looseRangeP_ren h1, looseRangeP_ren h2]
  | _, _, .forallE _ _ _ _ h1 h2 => by
    simp only [looseRangeP, looseRangeP_ren h1, looseRangeP_ren h2]
  | _, _, .letE _ _ _ _ h1 h2 h3 => by
    simp only [looseRangeP, looseRangeP_ren h1, looseRangeP_ren h2, looseRangeP_ren h3]
  | _, _, .mdata _ _ _ h1 => by simp only [looseRangeP, looseRangeP_ren h1]
  | _, _, .proj _ _ _ _ h1 => by simp only [looseRangeP, looseRangeP_ren h1]

theorem liftP_ren : ∀ {a b : Expr} (n c : Nat), Ren ρ a b → Ren ρ (liftP a n c) (liftP b n c)
  | a, b, n, c, h => by
    unfold liftP
    rw [looseRangeP_ren h]
    by_cases hn : n = 0
    · simp only [hn, beq_self_eq_true, ↓reduceIte]; exact h
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP a ≤ c
    · simp only [hr, ↓reduceIte]; exact h
    simp only [hr, ↓reduceIte]
    cases h with
    | bvar i _ _ => by_cases hi : i ≥ c <;> simp only [hi, ↓reduceIte] <;> exact .bvar _ _ _
    | app _ _ h1 h2 => exact Ren.mkApp' (liftP_ren n c h1) (liftP_ren n c h2)
    | lam _ _ _ _ h1 h2 => exact Ren.mkLam' _ _ (liftP_ren n c h1) (liftP_ren n (c + 1) h2)
    | forallE _ _ _ _ h1 h2 => exact Ren.mkForallE' _ _ (liftP_ren n c h1) (liftP_ren n (c + 1) h2)
    | letE _ _ _ _ h1 h2 h3 =>
      exact Ren.mkLetE' _ _ (liftP_ren n c h1) (liftP_ren n c h2) (liftP_ren n (c + 1) h3)
    | proj _ _ _ _ h1 => exact Ren.mkProj' _ _ (liftP_ren n c h1)
    | mdata _ _ _ h1 => exact Ren.mkMData' _ (liftP_ren n c h1)
    | fvar => exact .fvar _ _ _
    | mvar => exact .mvar _ _ _
    | sort => exact .sort _ _ _
    | const => exact .const _ _ _ _
    | lit => exact .lit _ _ _

theorem lowerP_ren : ∀ {a b : Expr} (n c : Nat), Ren ρ a b → Ren ρ (lowerP a n c) (lowerP b n c)
  | a, b, n, c, h => by
    unfold lowerP
    rw [looseRangeP_ren h]
    by_cases hn : n = 0
    · simp only [hn, beq_self_eq_true, ↓reduceIte]; exact h
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP a ≤ c
    · simp only [hr, ↓reduceIte]; exact h
    simp only [hr, ↓reduceIte]
    cases h with
    | bvar i _ _ => by_cases hi : i ≥ c + n <;> simp only [hi, ↓reduceIte] <;> exact .bvar _ _ _
    | app _ _ h1 h2 => exact Ren.mkApp' (lowerP_ren n c h1) (lowerP_ren n c h2)
    | lam _ _ _ _ h1 h2 => exact Ren.mkLam' _ _ (lowerP_ren n c h1) (lowerP_ren n (c + 1) h2)
    | forallE _ _ _ _ h1 h2 =>
      exact Ren.mkForallE' _ _ (lowerP_ren n c h1) (lowerP_ren n (c + 1) h2)
    | letE _ _ _ _ h1 h2 h3 =>
      exact Ren.mkLetE' _ _ (lowerP_ren n c h1) (lowerP_ren n c h2) (lowerP_ren n (c + 1) h3)
    | proj _ _ _ _ h1 => exact Ren.mkProj' _ _ (lowerP_ren n c h1)
    | mdata _ _ _ h1 => exact Ren.mkMData' _ (lowerP_ren n c h1)
    | fvar => exact .fvar _ _ _
    | mvar => exact .mvar _ _ _
    | sort => exact .sort _ _ _
    | const => exact .const _ _ _ _
    | lit => exact .lit _ _ _

theorem occursP_ren : ∀ {a b : Expr} (k : Nat), Ren ρ a b → occursP b k = occursP a k
  | a, b, k, h => by
    unfold occursP
    rw [looseRangeP_ren h]
    by_cases hr : looseRangeP a ≤ k
    · simp only [hr, ↓reduceIte]
    simp only [hr, ↓reduceIte]
    cases h with
    | app _ _ h1 h2 => simp only [occursP_ren k h1, occursP_ren k h2]
    | lam _ _ _ _ h1 h2 => simp only [occursP_ren k h1, occursP_ren (k + 1) h2]
    | forallE _ _ _ _ h1 h2 => simp only [occursP_ren k h1, occursP_ren (k + 1) h2]
    | letE _ _ _ _ h1 h2 h3 => simp only [occursP_ren k h1, occursP_ren k h2, occursP_ren (k + 1) h3]
    | proj _ _ _ _ h1 => simp only [occursP_ren k h1]
    | mdata _ _ _ h1 => simp only [occursP_ren k h1]
    | bvar | fvar | mvar | sort | const | lit => rfl

theorem projCtor?_ren (s : Name) (i : Nat) {a b : Expr} (h : Ren ρ a b) :
    ORen ρ (Ix.Compile.Image.projCtor? s i a) (Ix.Compile.Image.projCtor? s i b) := by
  unfold Ix.Compile.Image.projCtor?
  obtain ⟨hh, ha⟩ := getAppFnArgs_ren h
  generalize getAppFnArgs a = p at hh ha
  generalize getAppFnArgs b = q at hh ha
  obtain ⟨h0, as⟩ := p
  obtain ⟨h1, bs⟩ := q
  simp only at hh ha ⊢
  have hs := ha.size
  cases hh
  case const c us _ _ =>
    simp only [hs]
    split
    · have := LRen.get ha (2 + i)
      simp only [Array.getElem?_toList] at this
      revert this
      cases as[2 + i]? <;> cases bs[2 + i]? <;> simp [ORen]
    · trivial
  all_goals trivial

/-- Lists related by `LRen`, through `mapM`. -/
theorem mapM_ren {f g : Expr → Except String Expr}
    (h : ∀ a b, Ren ρ a b → ExRel (Ren ρ) (f a) (g b)) :
    ∀ {as bs : List Expr}, LRen ρ as bs → ExRel (LRen ρ) (as.mapM f) (bs.mapM g)
  | [], [], .nil => LRen.nil
  | a :: as, b :: bs, .cons hab hs => by
    simp only [List.mapM_cons]
    exact ExRel.bind (h a b hab) fun x y hxy =>
      ExRel.bind (mapM_ren h hs) fun xs ys hl => ExRel.pure (.cons hxy hl)

/-- The pair results of `hinstP` related. -/
def PRen (ρ : Name → Name) (p q : Expr × Created) : Prop := Ren ρ p.1 q.1 ∧ p.2 = q.2

/-- The tail of `hinstP`'s λ case: η at a `.direct` body. -/
def lamStepP (n : Name) (t b : Expr) (bi : Lean.BinderInfo) (c : Created) :
    Except String (Expr × Created) :=
  match c, b with
  | .direct, .app f (.bvar 0 _) _ =>
    if !(occursP f 0) then pure (lowerP f 1 0, .direct) else pure (Expr.mkLam n t b bi, .no)
  | _, _ => pure (Expr.mkLam n t b bi, .no)

theorem lamStepP_ren (n : Name) (bi : Lean.BinderInfo) (c : Created) {t t' b b' : Expr}
    (ht : Ren ρ t t') (hb : Ren ρ b b') :
    ExRel (PRen ρ) (lamStepP n t b bi c) (lamStepP n t' b' bi c) := by
  unfold lamStepP
  split
  · rename_i f h1 h2
    cases hb with
    | app _ _ hf hz =>
      cases hz with
      | bvar _ _ _ =>
        simp only
        rw [occursP_ren 0 hf]
        by_cases ho : (!occursP f 0) = true
        · simp only [ho, ↓reduceIte]; exact ⟨lowerP_ren 1 0 hf, rfl⟩
        · simp only [ho, Bool.false_eq_true, ↓reduceIte]
          exact ⟨Ren.mkLam' _ _ ht (.app _ _ hf (.bvar _ _ _)), rfl⟩
  · rename_i hx
    split
    · rename_i f' h1 h2
      exfalso
      cases hb with
      | app _ _ hf hz =>
        cases hz with
        | bvar _ _ _ => exact hx _ _ _ rfl rfl
    · exact ⟨Ren.mkLam' _ _ ht hb, rfl⟩

theorem develop_ren : ∀ fuel : Nat,
    (∀ v v' k e e', Ren ρ v v' → Ren ρ e e' →
      ExRel (PRen ρ) (hinstP fuel v k e) (hinstP fuel v' k e')) ∧
    (∀ f f' args args', Ren ρ f f' → LRen ρ args args' →
      ExRel (Ren ρ) (happP fuel f args) (happP fuel f' args'))
  | 0 => ⟨fun _ _ _ _ _ _ _ => by simp only [hinstP_zero]; exact ExRel.err _ _,
          fun _ _ _ _ _ _ => by simp only [happP_zero]; exact ExRel.err _ _⟩
  | fuel + 1 => by
    have IH := develop_ren fuel
    refine ⟨fun v v' k e e' hv he => ?_, fun f f' args args' hf ha => ?_⟩
    · unfold hinstP
      rw [looseRangeP_ren he]
      by_cases hr : looseRangeP e ≤ k
      · simp only [hr, ↓reduceIte]; exact ⟨he, rfl⟩
      simp only [hr, ↓reduceIte]
      cases he with
      | bvar i _ _ =>
        by_cases hik : i = k
        · simp only [hik, beq_self_eq_true, ↓reduceIte]; exact ⟨liftP_ren k 0 hv, rfl⟩
        · have hb : (i == k) = false := by simp [hik]
          simp only [hb, Bool.false_eq_true, ↓reduceIte]
          by_cases hg : i > k <;> simp only [hg, ↓reduceIte] <;> exact ⟨.bvar _ _ _, rfl⟩
      | app hh hh' h1 h2 =>
        have hs := getAppFnArgs_ren (Ren.app (ρ := ρ) hh hh' h1 h2)
        generalize getAppFnArgs (Expr.app _ _ hh) = p at hs
        generalize getAppFnArgs (Expr.app _ _ hh') = q at hs
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        obtain ⟨hH, hA⟩ := hs
        simp only at hH hA ⊢
        refine ExRel.bind (R := LRen ρ) (mapM_ren (fun a b hab =>
          ExRel.map (IH.1 v v' k a b hv hab) fun x y hxy => hxy.1) hA) fun xs ys hxy => ?_
        refine ExRel.bind (IH.1 v v' k p1 q1 hv hH) fun x y hxy' => ?_
        obtain ⟨x1, xc⟩ := x
        obtain ⟨y1, yc⟩ := y
        obtain ⟨hx1, hxc⟩ := hxy'
        simp only at hx1 hxc ⊢
        subst hxc
        have hxy'' : ARen ρ xs.toArray ys.toArray := by unfold ARen; simpa using hxy
        cases xc with
        | no => exact ⟨mkAppN_ren hx1 hxy'', rfl⟩
        | direct =>
          cases hx1 with
          | lam _ _ _ _ g1 g2 =>
            exact ExRel.bind (IH.2 _ _ xs ys (.lam _ _ _ _ g1 g2) hxy) fun a b hab =>
              ExRel.pure ⟨hab, rfl⟩
          | bvar => exact ⟨mkAppN_ren (.bvar _ _ _) hxy'', rfl⟩
          | fvar => exact ⟨mkAppN_ren (.fvar _ _ _) hxy'', rfl⟩
          | mvar => exact ⟨mkAppN_ren (.mvar _ _ _) hxy'', rfl⟩
          | sort => exact ⟨mkAppN_ren (.sort _ _ _) hxy'', rfl⟩
          | const => exact ⟨mkAppN_ren (.const _ _ _ _) hxy'', rfl⟩
          | lit => exact ⟨mkAppN_ren (.lit _ _ _) hxy'', rfl⟩
          | app _ _ g1 g2 => exact ⟨mkAppN_ren (.app _ _ g1 g2) hxy'', rfl⟩
          | forallE _ _ _ _ g1 g2 => exact ⟨mkAppN_ren (.forallE _ _ _ _ g1 g2) hxy'', rfl⟩
          | letE _ _ _ _ g1 g2 g3 => exact ⟨mkAppN_ren (.letE _ _ _ _ g1 g2 g3) hxy'', rfl⟩
          | mdata _ _ _ g1 => exact ⟨mkAppN_ren (.mdata _ _ _ g1) hxy'', rfl⟩
          | proj _ _ _ _ g1 => exact ⟨mkAppN_ren (.proj _ _ _ _ g1) hxy'', rfl⟩
        | reduced =>
          cases hx1 with
          | lam _ _ _ _ g1 g2 =>
            exact ExRel.bind (IH.2 _ _ xs ys (.lam _ _ _ _ g1 g2) hxy) fun a b hab =>
              ExRel.pure ⟨hab, rfl⟩
          | bvar => exact ⟨mkAppN_ren (.bvar _ _ _) hxy'', rfl⟩
          | fvar => exact ⟨mkAppN_ren (.fvar _ _ _) hxy'', rfl⟩
          | mvar => exact ⟨mkAppN_ren (.mvar _ _ _) hxy'', rfl⟩
          | sort => exact ⟨mkAppN_ren (.sort _ _ _) hxy'', rfl⟩
          | const => exact ⟨mkAppN_ren (.const _ _ _ _) hxy'', rfl⟩
          | lit => exact ⟨mkAppN_ren (.lit _ _ _) hxy'', rfl⟩
          | app _ _ g1 g2 => exact ⟨mkAppN_ren (.app _ _ g1 g2) hxy'', rfl⟩
          | forallE _ _ _ _ g1 g2 => exact ⟨mkAppN_ren (.forallE _ _ _ _ g1 g2) hxy'', rfl⟩
          | letE _ _ _ _ g1 g2 g3 => exact ⟨mkAppN_ren (.letE _ _ _ _ g1 g2 g3) hxy'', rfl⟩
          | mdata _ _ _ g1 => exact ⟨mkAppN_ren (.mdata _ _ _ g1) hxy'', rfl⟩
          | proj _ _ _ _ g1 => exact ⟨mkAppN_ren (.proj _ _ _ _ g1) hxy'', rfl⟩
      | proj s i hh hh' h1 =>
        refine ExRel.bind (IH.1 v v' k _ _ hv h1) fun x y hxy => ?_
        obtain ⟨x1, xc⟩ := x
        obtain ⟨y1, yc⟩ := y
        obtain ⟨hx1, hxc⟩ := hxy
        simp only at hx1 hxc ⊢
        subst hxc
        cases xc
        case no => exact ⟨Ren.mkProj' _ _ hx1, rfl⟩
        all_goals
          have hp := projCtor?_ren s i hx1
          generalize Ix.Compile.Image.projCtor? s i x1 = o1 at hp ⊢
          generalize Ix.Compile.Image.projCtor? s i y1 = o2 at hp ⊢
          cases o1 <;> cases o2 <;> simp only [ORen] at hp
          · exact ⟨Ren.mkProj' _ _ hx1, rfl⟩
          · exact ⟨hp, rfl⟩
      | lam n bi hh hh' h1 h2 =>
        refine ExRel.bind (IH.1 v v' k _ _ hv h1) fun x y hxy => ?_
        refine ExRel.bind (IH.1 v v' (k + 1) _ _ hv h2) fun x' y' hxy' => ?_
        obtain ⟨x1, xc⟩ := x
        obtain ⟨y1, yc⟩ := y
        obtain ⟨b1, bc⟩ := x'
        obtain ⟨c1, cc⟩ := y'
        obtain ⟨hx1, -⟩ := hxy
        obtain ⟨hb1, hbc⟩ := hxy'
        simp only at hx1 hb1 hbc ⊢
        subst hbc
        exact lamStepP_ren n bi bc hx1 hb1
      | forallE n bi hh hh' h1 h2 =>
        refine ExRel.bind (IH.1 v v' k _ _ hv h1) fun x y hxy => ?_
        refine ExRel.bind (IH.1 v v' (k + 1) _ _ hv h2) fun x' y' hxy' => ?_
        exact ⟨Ren.mkForallE' _ _ hxy.1 hxy'.1, rfl⟩
      | letE n nd hh hh' h1 h2 h3 =>
        refine ExRel.bind (IH.1 v v' k _ _ hv h1) fun x y hxy => ?_
        refine ExRel.bind (IH.1 v v' k _ _ hv h2) fun x' y' hxy' => ?_
        refine ExRel.bind (IH.1 v v' (k + 1) _ _ hv h3) fun x'' y'' hxy'' => ?_
        exact ⟨Ren.mkLetE' _ _ hxy.1 hxy'.1 hxy''.1, rfl⟩
      | mdata d hh hh' h1 =>
        refine ExRel.bind (IH.1 v v' k _ _ hv h1) fun x y hxy => ?_
        exact ⟨Ren.mkMData' _ hxy.1, hxy.2⟩
      | fvar => exact ⟨.fvar _ _ _, rfl⟩
      | mvar => exact ⟨.mvar _ _ _, rfl⟩
      | sort => exact ⟨.sort _ _ _, rfl⟩
      | const => exact ⟨.const _ _ _ _, rfl⟩
      | lit => exact ⟨.lit _ _ _, rfl⟩
    · rw [happP_succ, happP_succ]
      cases hf with
      | lam _ _ _ _ g1 g2 =>
        cases ha with
        | nil => exact mkAppN_ren (.lam _ _ _ _ g1 g2) .nil
        | cons hab hs =>
          exact ExRel.bind (IH.1 _ _ 0 _ _ hab g2) fun x y hxy => IH.2 _ _ _ _ hxy.1 hs
      | bvar => exact mkAppN_ren (.bvar _ _ _) (by unfold ARen; simpa using ha)
      | fvar => exact mkAppN_ren (.fvar _ _ _) (by unfold ARen; simpa using ha)
      | mvar => exact mkAppN_ren (.mvar _ _ _) (by unfold ARen; simpa using ha)
      | sort => exact mkAppN_ren (.sort _ _ _) (by unfold ARen; simpa using ha)
      | const => exact mkAppN_ren (.const _ _ _ _) (by unfold ARen; simpa using ha)
      | lit => exact mkAppN_ren (.lit _ _ _) (by unfold ARen; simpa using ha)
      | app _ _ g1 g2 => exact mkAppN_ren (.app _ _ g1 g2) (by unfold ARen; simpa using ha)
      | forallE _ _ _ _ g1 g2 => exact mkAppN_ren (.forallE _ _ _ _ g1 g2) (by unfold ARen; simpa using ha)
      | letE _ _ _ _ g1 g2 g3 =>
        exact mkAppN_ren (.letE _ _ _ _ g1 g2 g3) (by unfold ARen; simpa using ha)
      | mdata _ _ _ g1 => exact mkAppN_ren (.mdata _ _ _ g1) (by unfold ARen; simpa using ha)
      | proj _ _ _ _ g1 => exact mkAppN_ren (.proj _ _ _ _ g1) (by unfold ARen; simpa using ha)

end

/-! ## The two developments the construction calls, and the packing -/

section
variable {ρ : Name → Name}

theorem instantiateP_ren {f f' : Expr} {args args' : Array Expr} (hf : Ren ρ f f')
    (ha : ARen ρ args args') :
    ExRel (Ren ρ) (instantiateP f args) (instantiateP f' args') :=
  (develop_ren _).2 _ _ _ _ hf ha

theorem foldlM_hinst_ren (F : Nat) : ∀ {vs vs' : List Expr} {acc acc' : Expr}, LRen ρ vs vs' →
    Ren ρ acc acc' →
    ExRel (Ren ρ) (vs.foldlM (fun acc v => Prod.fst <$> hinstP F v 0 acc) acc)
      (vs'.foldlM (fun acc v => Prod.fst <$> hinstP F v 0 acc) acc')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hv hs, h => by
    simp only [List.foldlM_cons]
    exact ExRel.bind (ExRel.map ((develop_ren F).1 _ _ 0 _ _ hv h) fun _ _ hp => hp.1)
      fun _ _ hacc => foldlM_hinst_ren F hs hacc

theorem LRen.reverse : ∀ {as bs : List Expr}, LRen ρ as bs → LRen ρ as.reverse bs.reverse
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => by
    simp only [List.reverse_cons]; exact (LRen.reverse h2).append (.cons h1 .nil)

theorem substFVarsP_ren {P : Name → Prop} (hi : InjOn ρ P) (xs : Array Name) (hx : ∀ x ∈ xs, P x)
    {vs vs' : Array Expr} (hv : ARen ρ vs vs') {e e' : Expr} (he : Ren ρ e e') (hP : FvAll P e) :
    ExRel (Ren ρ) (substFVarsP xs vs e) (substFVarsP (xs.map ρ) vs' e') := by
  unfold substFVarsP
  have hs := hv.size
  simp only [Array.size_map, ← hs]
  by_cases hne : (xs.size != vs.size) = true
  · simp only [hne, ↓reduceIte]; exact ExRel.err _ _
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact foldlM_hinst_ren _ (LRen.reverse hv) (abstractFVars_ren hi xs hx he hP)

/-- Pairs of an expression and a level, related. -/
def PLRen (ρ : Name → Name) (x y : Expr × Level) : Prop := Ren ρ x.1 y.1 ∧ x.2 = y.2

/-- Two lists related pointwise. -/
inductive LRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : LRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → LRel R as bs → LRel R (a :: as) (b :: bs)

theorem LRel.of_getElem {α β : Type} {R : α → β → Prop} : ∀ (l : List α) (l' : List β),
    l.length = l'.length → (∀ i (h : i < l.length) (h' : i < l'.length), R l[i] l'[i]) → LRel R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hl, h => by
    refine .cons (h 0 (by simp) (by simp)) (LRel.of_getElem l l' (by simpa using hl) fun i h1 h2 => ?_)
    have := h (i + 1) (by simp; omega) (by simp; omega)
    rw [List.getElem_cons_succ, List.getElem_cons_succ] at this; exact this
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem LRel.foldr {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ → γ} {g : β → δ → δ} (hfg : ∀ a b c c', R a b → S c c' → S (f a c) (g b c')) :
    ∀ {l : List α} {l' : List β}, LRel R l l' → ∀ {c : γ} {c' : δ}, S c c' → S (l.foldr f c) (l'.foldr g c')
  | [], [], .nil, _, _, h => h
  | _ :: _, _ :: _, .cons h1 h2, _, _, h => hfg _ _ _ _ h1 (LRel.foldr hfg h2 h)

theorem foldr1_rel {α β : Type} {R : α → β → Prop} {f : α → α → α} {g : β → β → β}
    (hfg : ∀ a b c c', R a b → R c c' → R (f a c) (g b c')) (xs : Array α) (ys : Array β)
    (hs : xs.size = ys.size) (hR : ∀ i (h : i < xs.size) (h' : i < ys.size), R xs[i] ys[i])
    {d : α} {d' : β} (hd : R d d') : R (Ix.Compile.Image.foldr1 f xs d) (Ix.Compile.Image.foldr1 g ys d') := by
  unfold Ix.Compile.Image.foldr1
  by_cases h0 : xs.size = 0
  · have h0' : ys.size = 0 := by omega
    have e1 : xs.back? = none := by
      rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_none (by omega)
    have e2 : ys.back? = none := by
      rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_none (by omega)
    rw [e1, e2]; exact hd
  · have e1 : xs.back? = some xs[xs.size - 1] := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
    have e2 : ys.back? = some ys[ys.size - 1] := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
    rw [e1, e2]
    simp only
    rw [← Array.foldr_toList, ← Array.foldr_toList]
    apply LRel.foldr hfg
    · apply LRel.of_getElem _ _ (by simp [hs])
      intro i h1 h2
      simp only [Array.toList_pop, List.getElem_dropLast, Array.getElem_toList]
      simp only [Array.toList_pop, List.length_dropLast, Array.length_toList] at h1 h2
      exact hR i (by omega) (by omega)
    · have e : xs.size - 1 = ys.size - 1 := by omega
      simp only [e]
      exact hR (ys.size - 1) (by omega) (by omega)

theorem mkPProdTy_ren {x x' y y' : Expr × Level} (hx : PLRen ρ x x') (hy : PLRen ρ y y') :
    PLRen ρ (Ix.Compile.Image.mkPProdTy x y) (Ix.Compile.Image.mkPProdTy x' y') := by
  obtain ⟨x1, xl⟩ := x; obtain ⟨x1', xl'⟩ := x'; obtain ⟨y1, yl⟩ := y; obtain ⟨y1', yl'⟩ := y'
  obtain ⟨h1, h1'⟩ := hx; obtain ⟨h2, h2'⟩ := hy
  simp only at h1 h1' h2 h2'
  subst h1' h2'
  unfold Ix.Compile.Image.mkPProdTy
  split
  · exact ⟨mkAppN_ren (Ren.mkConst' _ _) (.cons h1 (.cons h2 .nil)), rfl⟩
  · exact ⟨mkAppN_ren (Ren.mkConst' _ _) (.cons h1 (.cons h2 .nil)), rfl⟩

theorem wrapTy_ren (p : Ix.Compile.Image.Pack) (lu : Level) {tys tys' : Array Expr}
    (h : ARen ρ tys tys') :
    ExRel (Ren ρ) (Ix.Compile.Image.wrapTy p lu tys) (Ix.Compile.Image.wrapTy p lu tys') := by
  unfold Ix.Compile.Image.wrapTy
  have hs := h.size
  by_cases h0 : tys.size = 0
  · have e1 : tys[0]? = none := by simp [h0]
    have e2 : tys'[0]? = none := Array.getElem?_eq_none (by omega)
    rw [e1, e2]; cases p <;> exact ExRel.err _ _
  · have e1 : tys[0]? = some tys[0] := Array.getElem?_eq_getElem (by omega)
    have e2 : tys'[0]? = some tys'[0] := Array.getElem?_eq_getElem (by omega)
    rw [e1, e2]
    have h00 := ARen.get h 0 (by omega) (by omega)
    cases p with
    | single => exact h00
    | lift => exact mkAppN_ren (Ren.mkConst' _ _) (.cons h00 (.cons (Ren.mkConst' _ _) .nil))
    | tuple n =>
      exact (foldr1_rel (R := PLRen ρ) (fun _ _ _ _ h1 h2 => mkPProdTy_ren h1 h2)
        (tys.map (·, lu)) (tys'.map (·, lu)) (by simp [hs])
        (fun i h1 h2 => ⟨by simpa using ARen.get h i (by simpa using h1) (by simpa using h2), by simp⟩)
        (d := (tys[0], lu)) (d' := (tys'[0], lu)) ⟨h00, rfl⟩).1

/-- Pairs of expressions, related. -/
def P2Ren (ρ : Name → Name) (x y : Expr × Expr) : Prop := Ren ρ x.1 y.1 ∧ Ren ρ x.2 y.2

/-- Triples (value, type, level), related. -/
def TRen (ρ : Name → Name) (x y : Expr × Expr × Level) : Prop :=
  Ren ρ x.1 y.1 ∧ Ren ρ x.2.1 y.2.1 ∧ x.2.2 = y.2.2

theorem mkPProdVal_ren {x x' y y' : Expr × Expr × Level} (hx : TRen ρ x x') (hy : TRen ρ y y') :
    TRen ρ (Ix.Compile.Image.mkPProdVal x y) (Ix.Compile.Image.mkPProdVal x' y') := by
  obtain ⟨a1, a2, al⟩ := x; obtain ⟨a1', a2', al'⟩ := x'
  obtain ⟨b1, b2, bl⟩ := y; obtain ⟨b1', b2', bl'⟩ := y'
  obtain ⟨h1, h2, h3⟩ := hx; obtain ⟨h4, h5, h6⟩ := hy
  simp only at h1 h2 h3 h4 h5 h6
  subst h3 h6
  have hty := mkPProdTy_ren (ρ := ρ) (x := (a2, al)) (x' := (a2', al)) (y := (b2, bl))
    (y' := (b2', bl)) ⟨h2, rfl⟩ ⟨h5, rfl⟩
  unfold Ix.Compile.Image.mkPProdVal
  generalize Ix.Compile.Image.mkPProdTy (a2, al) (b2, bl) = t at hty
  generalize Ix.Compile.Image.mkPProdTy (a2', al) (b2', bl) = t' at hty
  obtain ⟨t1, tl⟩ := t; obtain ⟨t1', tl'⟩ := t'
  obtain ⟨ht1, htl⟩ := hty
  simp only at ht1 htl ⊢
  subst htl
  split
  · exact ⟨mkAppN_ren (Ren.mkConst' _ _) (.cons h2 (.cons h5 (.cons h1 (.cons h4 .nil)))), ht1, rfl⟩
  · exact ⟨mkAppN_ren (Ren.mkConst' _ _) (.cons h2 (.cons h5 (.cons h1 (.cons h4 .nil)))), ht1, rfl⟩

theorem wrapVal_ren (p : Ix.Compile.Image.Pack) (lu : Level) {vs vs' : Array (Expr × Expr)}
    (hs : vs.size = vs'.size) (h : ∀ i (h1 : i < vs.size) (h2 : i < vs'.size), P2Ren ρ vs[i] vs'[i]) :
    ExRel (Ren ρ) (Ix.Compile.Image.wrapVal p lu vs) (Ix.Compile.Image.wrapVal p lu vs') := by
  unfold Ix.Compile.Image.wrapVal
  by_cases h0 : vs.size = 0
  · have e1 : vs[0]? = none := Array.getElem?_eq_none (by omega)
    have e2 : vs'[0]? = none := Array.getElem?_eq_none (by omega)
    rw [e1, e2]; cases p <;> exact ExRel.err _ _
  · have e1 : vs[0]? = some vs[0] := Array.getElem?_eq_getElem (by omega)
    have e2 : vs'[0]? = some vs'[0] := Array.getElem?_eq_getElem (by omega)
    rw [e1, e2]
    have h00 := h 0 (by omega) (by omega)
    cases p with
    | single => exact h00.1
    | lift =>
      exact mkAppN_ren (Ren.mkConst' _ _)
        (.cons h00.2 (.cons (Ren.mkConst' _ _) (.cons h00.1 (.cons (Ren.mkConst' _ _) .nil))))
    | tuple n =>
      exact (foldr1_rel (R := TRen ρ) (fun _ _ _ _ h1 h2 => mkPProdVal_ren h1 h2)
        (vs.map fun (v, t) => (v, t, lu)) (vs'.map fun (v, t) => (v, t, lu)) (by simp [hs])
        (fun i h1 h2 => by
          simp only [Array.getElem_map]
          have := h i (by simpa using h1) (by simpa using h2)
          exact ⟨this.1, this.2, rfl⟩)
        (d := (vs[0].1, vs[0].2, lu)) (d' := (vs'[0].1, vs'[0].2, lu)) ⟨h00.1, h00.2, rfl⟩).1

theorem unwrap_ren (p : Ix.Compile.Image.Pack) (lz : Bool) (pos : Nat) {v v' : Expr}
    (h : Ren ρ v v') : Ren ρ (Ix.Compile.Image.unwrap p lz pos v) (Ix.Compile.Image.unwrap p lz pos v') := by
  unfold Ix.Compile.Image.unwrap
  cases p with
  | single => exact h
  | lift => exact Ren.mkProj' _ _ h
  | tuple n =>
    simp only
    have hf : ∀ (l : List Nat) (a b : Expr), Ren ρ a b →
        Ren ρ (l.foldl (fun v _ => Expr.mkProj (if lz then Ix.Compile.Image.nAnd else Ix.Compile.Image.nPProd) 1 v) a)
          (l.foldl (fun v _ => Expr.mkProj (if lz then Ix.Compile.Image.nAnd else Ix.Compile.Image.nPProd) 1 v) b) := by
      intro l
      induction l with
      | nil => intro a b h; exact h
      | cons _ l ih => intro a b h; exact ih _ _ (Ren.mkProj' _ _ h)
    split
    · exact Ren.mkProj' _ _ (hf _ _ _ h)
    · exact hf _ _ _ h

end

end Ix.CompileCert.Img
