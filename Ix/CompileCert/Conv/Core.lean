import Ix.CompileCert.Conv.Erase

/-!
# M7 X1: the development without its tables (the pure core of `Ix.Compile.Image.Develop`)

`Ix/Compile/Image/Develop.lean` runs the hereditary substitution in `DevM`, a state of five hash
tables (`range`, `lifted`, `lowered`, `occurs`, `insts`) keyed by `Ix.Expr` under its `BEq`,
which compares the embedded Blake3 hashes. A table hit returns the entry of a key with the same
hash, which is the entry of the same term only when no two terms met by the run share a hash: a
fact about Blake3 on the run, not provable here (the hash is 32 bytes, so collisions exist among
`Ix.Expr` values). The tables also carry results across fuel levels (`instantiateWith`).

This module states the same functions without the tables, clause by clause in the code's order
(the early exits on `looseRange`, the head flags `Created`, the η test, `projCtor?`, the fuel
decremented at every call): `looseRangeP`, `liftP`, `lowerP`, `occursP`, `hinstP`, `happP`,
`instantiateP`, `substFVarsP`. They are what the executable computes when every table hit is a
hit on the same term. **The equality of the executable with this core is not proved here** (it
needs the hit confirmed by structural equality or the tables made self-proving; see the
runtime-refinement obligation in `docs/compiler-certification.md` §1.7). Every
theorem of this package about the development is a theorem about this core.
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor? abstractFVars)

/-- `Ix.Compile.Image.looseRange` without its table. -/
def looseRangeP : Expr → Nat
  | .bvar i _ => i + 1
  | .app f a _ => max (looseRangeP f) (looseRangeP a)
  | .lam _ t b _ _ => max (looseRangeP t) (looseRangeP b - 1)
  | .forallE _ t b _ _ => max (looseRangeP t) (looseRangeP b - 1)
  | .letE _ t v b _ _ => max (max (looseRangeP t) (looseRangeP v)) (looseRangeP b - 1)
  | .proj _ _ s _ => looseRangeP s
  | .mdata _ s _ => looseRangeP s
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 0

/-- `Ix.Compile.Image.liftM` without its table. -/
def liftP (e : Expr) (n c : Nat) : Expr :=
  if n == 0 then e else if looseRangeP e ≤ c then e else
  match e with
  | .bvar i _ => if i ≥ c then Expr.mkBVar (i + n) else e
  | .app f a _ => Expr.mkApp (liftP f n c) (liftP a n c)
  | .lam nm t b bi _ => Expr.mkLam nm (liftP t n c) (liftP b n (c + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (liftP t n c) (liftP b n (c + 1)) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (liftP t n c) (liftP v n c) (liftP b n (c + 1)) nd
  | .proj nm i s _ => Expr.mkProj nm i (liftP s n c)
  | .mdata md x _ => Expr.mkMData md (liftP x n c)
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e

/-- `Ix.Compile.Image.lowerM` without its table. -/
def lowerP (e : Expr) (n c : Nat) : Expr :=
  if n == 0 then e else if looseRangeP e ≤ c then e else
  match e with
  | .bvar i _ => if i ≥ c + n then Expr.mkBVar (i - n) else e
  | .app f a _ => Expr.mkApp (lowerP f n c) (lowerP a n c)
  | .lam nm t b bi _ => Expr.mkLam nm (lowerP t n c) (lowerP b n (c + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (lowerP t n c) (lowerP b n (c + 1)) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (lowerP t n c) (lowerP v n c) (lowerP b n (c + 1)) nd
  | .proj nm i s _ => Expr.mkProj nm i (lowerP s n c)
  | .mdata md x _ => Expr.mkMData md (lowerP x n c)
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e

/-- `Ix.Compile.Image.occursM` without its table. -/
def occursP (e : Expr) (k : Nat) : Bool :=
  if looseRangeP e ≤ k then false else
  match e with
  | .bvar i _ => i == k
  | .app f a _ => occursP f k || occursP a k
  | .lam _ t b _ _ => occursP t k || occursP b (k + 1)
  | .forallE _ t b _ _ => occursP t k || occursP b (k + 1)
  | .letE _ t v b _ _ => occursP t k || occursP v k || occursP b (k + 1)
  | .proj _ _ s _ => occursP s k
  | .mdata _ s _ => occursP s k
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => false

mutual
/-- `Ix.Compile.Image.hinst` without its tables: `e[bvar k := v]`, contracting the β-, pair
projection and η-redexes formed at the substituted positions, hereditarily. -/
def hinstP : Nat → Expr → Nat → Expr → Except String (Expr × Created)
  | 0, _, _, _ => throw "development: out of fuel"
  | fuel + 1, v, k, e =>
    if looseRangeP e ≤ k then pure (e, .no) else
    match e with
    | .bvar i _ =>
      if i == k then pure (liftP v k 0, .direct)
      else if i > k then pure (Expr.mkBVar (i - 1), .no)
      else pure (e, .no)
    | .app .. => do
      let p := getAppFnArgs e
      let args' ← p.2.toList.mapM fun a => Prod.fst <$> hinstP fuel v k a
      let (h', c) ← hinstP fuel v k p.1
      match c, h' with
      | .no, _ => pure (mkAppN h' args'.toArray, .no)
      | _, .lam .. => do pure ((← happP fuel h' args'), .reduced)
      | c, _ => pure (mkAppN h' args'.toArray, c)
    | .proj s i x _ => do
      let (x', c) ← hinstP fuel v k x
      match c with
      | .no => pure (Expr.mkProj s i x', .no)
      | _ =>
        match projCtor? s i x' with
        | some f => pure (f, .reduced)
        | none => pure (Expr.mkProj s i x', .no)
    | .lam n t b bi _ => do
      let (t', _) ← hinstP fuel v k t
      let (b', c) ← hinstP fuel v (k + 1) b
      match c, b' with
      | .direct, .app f (.bvar 0 _) _ =>
        if !(occursP f 0) then pure (lowerP f 1 0, .direct)
        else pure (Expr.mkLam n t' b' bi, .no)
      | _, _ => pure (Expr.mkLam n t' b' bi, .no)
    | .forallE n t b bi _ => do
      let (t', _) ← hinstP fuel v k t
      let (b', _) ← hinstP fuel v (k + 1) b
      pure (Expr.mkForallE n t' b' bi, .no)
    | .letE n t x b nd _ => do
      let (t', _) ← hinstP fuel v k t
      let (x', _) ← hinstP fuel v k x
      let (b', _) ← hinstP fuel v (k + 1) b
      pure (Expr.mkLetE n t' x' b' nd, .no)
    | .mdata md x _ => do
      let (x', c) ← hinstP fuel v k x
      pure (Expr.mkMData md x', c)
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => pure (e, .no)

/-- `Ix.Compile.Image.happ` without its tables: `f a₁ … aₙ` with the β-redexes at the head
contracted hereditarily. -/
def happP : Nat → Expr → List Expr → Except String Expr
  | 0, _, _ => throw "development: out of fuel"
  | fuel + 1, .lam _ _ b _ _, a :: rest => do
    let (b', _) ← hinstP fuel a 0 b
    happP fuel b' rest
  | _ + 1, f, args => pure (mkAppN f args.toArray)
end

/-- `Ix.Compile.Image.instantiate` without its tables (P3b at a call site). -/
def instantiateP (f : Expr) (args : Array Expr) : Except String Expr :=
  happP Ix.Compile.Image.defaultFuel f args.toList

/-- `Ix.Compile.Image.substFVars` without its tables (P3a: `e[xs := vs]`, developed). -/
def substFVarsP (xs : Array Name) (vs : Array Expr) (e : Expr) : Except String Expr := do
  if xs.size != vs.size then throw "substFVars: arity mismatch"
  vs.toList.reverse.foldlM (fun acc v => Prod.fst <$> hinstP Ix.Compile.Image.defaultFuel v 0 acc)
    (abstractFVars xs e)

/-! ## The helpers erase to the de Bruijn operations -/

theorem looseRangeP_eq : ∀ (e : Expr), looseRangeP e = Tm.range (er e)
  | .bvar i _ => rfl
  | .app f a _ => by simp only [looseRangeP, er, Tm.range, looseRangeP_eq f, looseRangeP_eq a]
  | .lam _ t b _ _ => by simp only [looseRangeP, er, Tm.range, looseRangeP_eq t, looseRangeP_eq b]
  | .forallE _ t b _ _ => by
    simp only [looseRangeP, er, Tm.range, looseRangeP_eq t, looseRangeP_eq b]
  | .letE _ t v b _ _ => by
    simp only [looseRangeP, er, Tm.range, looseRangeP_eq t, looseRangeP_eq v, looseRangeP_eq b]
  | .proj _ _ s _ => by simp only [looseRangeP, er, Tm.range, looseRangeP_eq s]
  | .mdata _ s _ => by simp only [looseRangeP, er, looseRangeP_eq s]
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

theorem er_liftP : ∀ (e : Expr) (n c : Nat), er (liftP e n c) = Tm.lift n c (er e)
  | e, n, c => by
    unfold liftP
    by_cases hn : n = 0
    · subst hn; simp [Tm.lift_zero]
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP e ≤ c
    · simp only [hr, ↓reduceIte]
      rw [looseRangeP_eq] at hr; rw [Tm.lift_of_range_le n c _ hr]
    simp only [hr, ↓reduceIte]
    match e with
    | .bvar i _ =>
      by_cases hi : i ≥ c
      · simp only [hi, ↓reduceIte, er_mkBVar, er, Tm.lift]
      · simp only [hi, ↓reduceIte, er, Tm.lift]
    | .app f a _ => simp only [er_mkApp, er, Tm.lift, er_liftP f n c, er_liftP a n c]
    | .lam _ t b _ _ => simp only [er_mkLam, er, Tm.lift, er_liftP t n c, er_liftP b n (c + 1)]
    | .forallE _ t b _ _ =>
      simp only [er_mkForallE, er, Tm.lift, er_liftP t n c, er_liftP b n (c + 1)]
    | .letE _ t v b _ _ =>
      simp only [er_mkLetE, er, Tm.lift, er_liftP t n c, er_liftP v n c, er_liftP b n (c + 1)]
    | .proj _ _ s _ => simp only [er_mkProj, er, Tm.lift, er_liftP s n c]
    | .mdata _ x _ => simp only [er_mkMData, er, er_liftP x n c]
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

theorem er_lowerP : ∀ (e : Expr) (n c : Nat), er (lowerP e n c) = Tm.lower n c (er e)
  | e, n, c => by
    unfold lowerP
    by_cases hn : n = 0
    · subst hn; simp [Tm.lower_zero]
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP e ≤ c
    · simp only [hr, ↓reduceIte]
      rw [looseRangeP_eq] at hr; rw [Tm.lower_of_range_le n c _ hr]
    simp only [hr, ↓reduceIte]
    match e with
    | .bvar i _ =>
      by_cases hi : i ≥ c + n
      · simp only [hi, ↓reduceIte, er_mkBVar, er, Tm.lower]
      · simp only [hi, ↓reduceIte, er, Tm.lower]
    | .app f a _ => simp only [er_mkApp, er, Tm.lower, er_lowerP f n c, er_lowerP a n c]
    | .lam _ t b _ _ => simp only [er_mkLam, er, Tm.lower, er_lowerP t n c, er_lowerP b n (c + 1)]
    | .forallE _ t b _ _ =>
      simp only [er_mkForallE, er, Tm.lower, er_lowerP t n c, er_lowerP b n (c + 1)]
    | .letE _ t v b _ _ =>
      simp only [er_mkLetE, er, Tm.lower, er_lowerP t n c, er_lowerP v n c, er_lowerP b n (c + 1)]
    | .proj _ _ s _ => simp only [er_mkProj, er, Tm.lower, er_lowerP s n c]
    | .mdata _ x _ => simp only [er_mkMData, er, er_lowerP x n c]
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

theorem occursP_eq : ∀ (e : Expr) (k : Nat), occursP e k = Tm.occ (er e) k
  | e, k => by
    unfold occursP
    by_cases hr : looseRangeP e ≤ k
    · simp only [hr, ↓reduceIte]
      rw [looseRangeP_eq] at hr; rw [Tm.occ_of_range_le _ k hr]
    simp only [hr, ↓reduceIte]
    match e with
    | .bvar i _ => rfl
    | .app f a _ => simp only [er, Tm.occ, occursP_eq f k, occursP_eq a k]
    | .lam _ t b _ _ => simp only [er, Tm.occ, occursP_eq t k, occursP_eq b (k + 1)]
    | .forallE _ t b _ _ => simp only [er, Tm.occ, occursP_eq t k, occursP_eq b (k + 1)]
    | .letE _ t v b _ _ =>
      simp only [er, Tm.occ, occursP_eq t k, occursP_eq v k, occursP_eq b (k + 1)]
    | .proj _ _ s _ => simp only [er, Tm.occ, occursP_eq s k]
    | .mdata _ x _ => simp only [er, occursP_eq x k]
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

/-! ## `List.mapM` in `Except` -/

/-- Two lists of expressions related pointwise. -/
inductive EForall2 (R : Expr → Expr → Prop) : List Expr → List Expr → Prop
  | nil : EForall2 R [] []
  | cons {a b : Expr} {as bs : List Expr} : R a b → EForall2 R as bs →
      EForall2 R (a :: as) (b :: bs)

theorem mapM_ok {f : Expr → Except String Expr} :
    ∀ {l l' : List Expr}, l.mapM f = .ok l' → EForall2 (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        cases h
        exact .cons hfa (mapM_ok hl)

end Ix.CompileCert.Conv
