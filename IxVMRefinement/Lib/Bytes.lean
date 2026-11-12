import IxVMRefinement.Obs.Bytes
import IxVMRefinement.Obs.UInt8
import IxVMRefinement.Core.Obs
import Aiur.Library.Bytes.Correctness
import Aiur.Library.U64.Goldilocks
import Mathlib.Tactic.IntervalCases

/-! # `Bytes::address_eq`, over observed derivations

`address_eq(a, b)` on two represented addresses answers `1` exactly when they are equal,
and allocates nothing (`address_eq_spec`). The derivation computes the hand-written model
`Aiur.Library.Bytes.addressEq` (the first byte, then `address_eq_tail`'s five packed
limbs), which `Aiur.Library.Bytes.address_eq_one_iff` and `address_eq_zero_iff` decide.

The generator emits no path lemma for `Bytes::address_eq_tail`: its body binds 62 bytes
and ten limbs, and inverting it node by node looks every variable up in the whole list of
bindings at once. Here the body is evaluated compositionally instead. `ComputesAt h locals
e u` says that `e`, at the heap `h` under the bindings `locals`, yields the field element
`u` and allocates nothing; one lemma per expression form (`computes_let`,
`computes_match0`, `computes_add`, …) builds it for the body, and a variable is found by
walking the bindings one name at a time (`find_here`, `find_skip`). -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The type of `Bytes::Address`: 32 field elements. -/
abbrev addrTy : Aiur.Ty := .tuple (List.replicate 32 .field)

/-! ## Looking a name up in a list of bindings -/

theorem find_cons_eq {α : Type} {p : α → Bool} {a : α} {l : List α} (hp : p a = true) :
    (a :: l).find? p = some a := by
  simp [List.find?, hp]

theorem find_cons_ne {α : Type} {p : α → Bool} {a : α} {l : List α} (hp : p a = false) :
    (a :: l).find? p = l.find? p := by
  simp [List.find?, hp]

/-- The name is bound first. -/
theorem find_here {n : String} {v : SourceValue F} {l : List (String × SourceValue F)} :
    ((n, v) :: l).find? (·.1 == n) = some (n, v) :=
  find_cons_eq (p := fun x : String × SourceValue F => x.1 == n) (a := (n, v)) (l := l)
    (by simp)

/-- Another name is bound first. -/
theorem find_skip {n m : String} {v v' : SourceValue F} {l : List (String × SourceValue F)}
    (hne : m ≠ n) (hl : l.find? (·.1 == n) = some (n, v)) :
    ((m, v') :: l).find? (·.1 == n) = some (n, v) := by
  have hb : (m == n) = false := by
    cases hmn : (m == n) with
    | false => rfl
    | true => exact absurd (eq_of_beq hmn) hne
  exact (find_cons_ne (p := fun x : String × SourceValue F => x.1 == n) (a := (m, v')) (l := l)
    hb).trans hl

/-- Find a name in a list of bindings: skip each binding of another name. -/
local macro "bytes_lookup" : tactic =>
  `(tactic| repeat (first | exact find_here | refine find_skip (by decide) ?_))

/-! ## Expressions that compute a field element without allocating -/

/-- `e`, evaluated at the heap `h` under the bindings `locals`, yields the field element `u`
and allocates nothing. -/
def ComputesAt (h : Heap F) (locals : List (String × SourceValue F)) (e : Generic.Expr F)
    (u : F) : Prop :=
  ∀ (r : SourceValue F) (h' : Heap F) (cs : List (Call F)),
    ObsExpr W [] locals e h r h' cs → r = .field u ∧ h' = h

section
variable {h : Heap F} {locals : List (String × SourceValue F)}

theorem computes_lit (c : F) : ComputesAt h locals (.literal c) c := by
  intro r h' cs d
  obtain ⟨hr, hh, -⟩ := d.literal_inv
  exact ⟨hr, hh⟩

theorem computes_var {n : String} {u : F}
    (hn : locals.find? (·.1 == n) = some (n, .field u)) : ComputesAt h locals (.var n) u := by
  intro r h' cs d
  obtain ⟨l, hh, -⟩ := d.var_inv
  exact ⟨((Prod.mk.inj (Option.some.inj (hn.symm.trans l))).2).symm, hh⟩

theorem computes_add {e1 e2 : Generic.Expr F} {a b : F}
    (ha : ComputesAt h locals e1 a) (hb : ComputesAt h locals e2 b) :
    ComputesAt h locals (.binary .add e1 e2) (a + b) := by
  intro r h' cs d
  obtain ⟨x, y, m, c1, c2, d1, d2, op, -⟩ := d.binary_inv
  obtain ⟨hx, hm⟩ := ha _ _ _ d1
  subst hx hm
  obtain ⟨hy, hh⟩ := hb _ _ _ d2
  subst hy
  simp only [evalBinOp, Except.ok.injEq] at op
  exact ⟨op.symm, hh⟩

theorem computes_mul {e1 e2 : Generic.Expr F} {a b : F}
    (ha : ComputesAt h locals e1 a) (hb : ComputesAt h locals e2 b) :
    ComputesAt h locals (.binary .mul e1 e2) (a * b) := by
  intro r h' cs d
  obtain ⟨x, y, m, c1, c2, d1, d2, op, -⟩ := d.binary_inv
  obtain ⟨hx, hm⟩ := ha _ _ _ d1
  subst hx hm
  obtain ⟨hy, hh⟩ := hb _ _ _ d2
  subst hy
  simp only [evalBinOp, Except.ok.injEq] at op
  exact ⟨op.symm, hh⟩

theorem computes_sub {e1 e2 : Generic.Expr F} {a b : F}
    (ha : ComputesAt h locals e1 a) (hb : ComputesAt h locals e2 b) :
    ComputesAt h locals (.binary .sub e1 e2) (a - b) := by
  intro r h' cs d
  obtain ⟨x, y, m, c1, c2, d1, d2, op, -⟩ := d.binary_inv
  obtain ⟨hx, hm⟩ := ha _ _ _ d1
  subst hx hm
  obtain ⟨hy, hh⟩ := hb _ _ _ d2
  subst hy
  simp only [evalBinOp, Except.ok.injEq] at op
  exact ⟨op.symm, hh⟩

/-- `UInt8::to_field` of a variable bound to a field element. -/
theorem computes_toField {n : String} {u : F}
    (hn : locals.find? (·.1 == n) = some (n, .field u)) :
    ComputesAt h locals (.call "UInt8::to_field" (some []) [.var n]) u := by
  intro r h' cs d
  obtain ⟨vs, m, c1, c2, a, ev, -⟩ := d.call_inv
  rw [instanceName_plain_some] at ev
  obtain ⟨v, vs2, m2, c3, c4, hvs, dv, a2, -⟩ := a.cons_inv
  obtain ⟨hv, hm2⟩ := computes_var hn _ _ _ dv
  obtain ⟨hvs2, hm, -⟩ := a2.nil_inv
  subst hvs hvs2 hv
  obtain ⟨hr, hh, -⟩ := Obs.«UInt8::to_field».obs ev
  exact ⟨hr, hh.trans (hm.trans hm2)⟩

/-- `let n = e; rest`. -/
theorem computes_let {n : String} {e rest : Generic.Expr F} {u w : F}
    (he : ComputesAt h locals e u)
    (hrest : ComputesAt h ((n, .field u) :: locals) rest w) :
    ComputesAt h locals (.letValue (.bind n) e rest) w := by
  intro r h' cs d
  obtain ⟨input, m, bs, c1, c2, dv, mt, db, -⟩ := d.letValue_inv
  obtain ⟨hin, hm⟩ := he _ _ _ dv
  subst hin hm
  have hbs := matchPattern_bind_inv mt
  subst hbs
  first
    | exact hrest _ _ _ db
    | (simp only [List.cons_append, List.nil_append] at db
       exact hrest _ _ _ db)

/-- `match s { 0 => b0, _ => b1 }` on a field element. -/
theorem computes_match0 {s b0 b1 : Generic.Expr F} {c w0 w1 : F} {dec : Decidable (c = 0)}
    (hs : ComputesAt h locals s c)
    (h0 : c = 0 → ComputesAt h locals b0 w0)
    (h1 : c ≠ 0 → ComputesAt h locals b1 w1) :
    ComputesAt h locals (.matchValue s [(.literal 0, b0), (.wildcard, b1)])
      (@ite F (c = 0) dec w0 w1) := by
  intro r h' cs d
  obtain ⟨input, m, bs, body, c1, c2, ds, sel, db, -⟩ := d.matchValue_inv
  obtain ⟨hin, hm⟩ := hs _ _ _ ds
  subst hin hm
  rcases selectArm_cons_inv sel with ⟨mt, hbody⟩ | ⟨nm, sel2⟩
  · subst hbody
    obtain ⟨hv, hbs⟩ := MatchesConst.some_inv (MatchesConst.literal 0) mt
    subst hbs
    have hc : c = 0 := Value.field.inj hv
    rw [if_pos hc]
    first
      | exact h0 hc _ _ _ db
      | (simp only [List.nil_append] at db
         exact h0 hc _ _ _ db)
  · have hne := MatchesConst.none_inv (MatchesConst.literal 0) nm
    have hc : c ≠ 0 := fun e => hne (congrArg Value.field e)
    rw [if_neg hc]
    rcases selectArm_cons_inv sel2 with ⟨mt2, hbody⟩ | ⟨nm2, sel3⟩
    · subst hbody
      have hbs := matchPattern_wildcard_inv mt2
      subst hbs
      first
        | exact h1 hc _ _ _ db
        | (simp only [List.nil_append] at db
           exact h1 hc _ _ _ db)
    · exact (matchPattern_wildcard_none nm2).elim

end

/-! ## A `let` of wildcards and variables against a loaded tuple -/

/-- The bindings of a list of wildcard and variable patterns against a list of values, in
front of `base`. -/
inductive BindsOnto (base : List (String × SourceValue F)) :
    List (Generic.Pattern F) → List (SourceValue F) → List (String × SourceValue F) → Prop where
  | nil : BindsOnto base [] [] base
  | wild {ps : List (Generic.Pattern F)} {v : SourceValue F} {vs : List (SourceValue F)}
      {env : List (String × SourceValue F)} :
      BindsOnto base ps vs env → BindsOnto base (.wildcard :: ps) (v :: vs) env
  | bind {n : String} {ps : List (Generic.Pattern F)} {v : SourceValue F}
      {vs : List (SourceValue F)} {env : List (String × SourceValue F)} :
      BindsOnto base ps vs env → BindsOnto base (.bind n :: ps) (v :: vs) ((n, v) :: env)

theorem BindsOnto.sound {base : List (String × SourceValue F)} {heap : Heap F}
    {ps : List (Generic.Pattern F)} {vs : List (SourceValue F)}
    {env : List (String × SourceValue F)} (hb : BindsOnto base ps vs env) :
    ∀ {bs : List (String × SourceValue F)},
      matchListWith (W.matchPattern [] heap) ps vs = .ok (some bs) → bs ++ base = env := by
  induction hb with
  | nil =>
    intro bs hm
    obtain ⟨-, hbs⟩ := matchListWith_nil_inv hm
    subst hbs
    rfl
  | wild _ ih =>
    intro bs hm
    obtain ⟨b1, b2, h1, h2, hbs⟩ := matchListWith_cons_cons_inv hm
    have hb1 := matchPattern_wildcard_inv h1
    subst hbs hb1
    simpa using ih h2
  | bind _ ih =>
    intro bs hm
    obtain ⟨b1, b2, h1, h2, hbs⟩ := matchListWith_cons_cons_inv hm
    have hb1 := matchPattern_bind_inv h1
    subst hbs hb1
    simpa using ih h2

/-- `let [p₀, …] = *x; rest`, the patterns wildcards and variables, `x` a variable bound to
a pointer whose cell is a tuple. -/
theorem computes_let_array {h : Heap F} {locals env : List (String × SourceValue F)}
    {p : String} {ptr : SourceValue F} {pats : List (Generic.Pattern F)}
    {vs : List (SourceValue F)} {rest : Generic.Expr F} {w : F}
    (hp : locals.find? (·.1 == p) = some (p, ptr))
    (hl : ∀ v, loadValue h ptr = .ok v → v = .tuple vs)
    (hb : BindsOnto locals pats vs env)
    (hrest : ComputesAt h env rest w) :
    ComputesAt h locals (.letValue (.array pats) (.load (.var p)) rest) w := by
  intro r h' cs d
  obtain ⟨input, m, bs, c1, c2, dv, mt, db, -⟩ := d.letValue_inv
  obtain ⟨q, dq, ld⟩ := dv.load_inv
  obtain ⟨lq, hm, -⟩ := dq.var_inv
  subst hm
  have hq : q = ptr := (Prod.mk.inj (Option.some.inj (lq.symm.trans hp))).2
  subst hq
  have hin := hl _ ld
  subst hin
  have henv := hb.sound (matchPattern_array_tuple_inv mt)
  subst henv
  exact hrest _ _ _ db

/-! ## Addresses -/


/-- The cell of an address: its 32 bytes as field elements. -/
def addrCell (K : Type) [Field K] (a : Bytes.Address) : List (SourceValue K) :=
  [.field (a[0].toNat : K), .field (a[1].toNat : K), .field (a[2].toNat : K), .field (a[3].toNat : K),
   .field (a[4].toNat : K), .field (a[5].toNat : K), .field (a[6].toNat : K), .field (a[7].toNat : K),
   .field (a[8].toNat : K), .field (a[9].toNat : K), .field (a[10].toNat : K), .field (a[11].toNat : K),
   .field (a[12].toNat : K), .field (a[13].toNat : K), .field (a[14].toNat : K), .field (a[15].toNat : K),
   .field (a[16].toNat : K), .field (a[17].toNat : K), .field (a[18].toNat : K), .field (a[19].toNat : K),
   .field (a[20].toNat : K), .field (a[21].toNat : K), .field (a[22].toNat : K), .field (a[23].toNat : K),
   .field (a[24].toNat : K), .field (a[25].toNat : K), .field (a[26].toNat : K), .field (a[27].toNat : K),
   .field (a[28].toNat : K), .field (a[29].toNat : K), .field (a[30].toNat : K), .field (a[31].toNat : K)]

/-- An address's bytes, listed. -/
set_option maxHeartbeats 1000000 in
theorem vec32_toList (a : Bytes.Address) :
    a.toList =
      [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15],
      a[16], a[17], a[18], a[19], a[20], a[21], a[22], a[23], a[24], a[25], a[26], a[27], a[28], a[29], a[30], a[31]] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < 32 := by simpa using h1
    interval_cases i <;> first | rfl | simp

/-- A pointer's load is its cell. -/
theorem load_ptr_inv {h : Heap F} {t : Aiur.Ty} {addr : Nat} {v0 v : SourceValue F}
    (cell : h[addr]? = some v0) (hl : loadValue h (.ptr t addr) = .ok v) : v = v0 := by
  by_cases typed : v0.type = t
  · simp [loadValue, cell, typed, pure, Except.pure, bind, Except.bind] at hl
    exact hl.symm
  · simp [loadValue, cell, typed] at hl

/-- **A represented address loads as its 32 bytes.** -/
theorem load_addr {h : Heap F} {a : Bytes.Address} {x : SourceValue F}
    (ha : Bytes.RepAddressRef addrTy h a x) :
    ∀ v, loadValue h x = .ok v → v = .tuple (addrCell F a) := by
  obtain ⟨addr, v0, hx, cell, hv⟩ := ha
  intro v hl
  subst hx
  have hv2 : v0 = .tuple (a.toList.map fun c => .field (c.toNat : F)) := hv
  have hv0 : v0 = .tuple (addrCell F a) :=
    hv2.trans (by rw [vec32_toList a] <;> rfl)
  exact (load_ptr_inv cell hl).trans hv0

/-- The first projection of a tuple. -/
theorem projectValue_zero {v r : SourceValue F} {vs : List (SourceValue F)}
    (hp : projectValue (.tuple (v :: vs)) 0 = .ok r) : r = v := by
  have e : projectValue (Value.tuple (v :: vs) : SourceValue F) 0 = .ok v := by
    first | rfl | simp [projectValue, bind, Except.bind, pure, Except.pure]
  rw [e] at hp
  exact (Except.ok.inj hp).symm

/-! ## `Bytes::address_eq_tail` -/

/-- Evaluate a packed limb: sums and products of `UInt8::to_field` calls and literals. -/
local macro "bytes_pack" : tactic =>
  `(tactic| repeat (first | exact computes_lit _ | exact computes_toField (by bytes_lookup) | refine computes_add ?_ ?_ | refine computes_mul ?_ ?_))

set_option maxHeartbeats 4000000 in
/-- **The body of `Bytes::address_eq_tail` computes the model's `addressEqTail`** of the two
loaded addresses, and allocates nothing: two array `let`s bind the bytes, and at each of
the five levels two `let`s pack a limb of each address and a `match` compares them. -/
theorem tail_computes {x y : SourceValue F} {h : Heap F} {a b : Bytes.Address}
    (hx : ∀ v, loadValue h x = .ok v → v = .tuple (addrCell F a))
    (hy : ∀ v, loadValue h y = .ok v → v = .tuple (addrCell F b)) :
    ComputesAt h [("a", x), ("b", y)] IxVM.Bytes.address_eq_tail.body
      (Bytes.addressEqTail F a b) := by
  unfold addrCell at hx hy
  unfold Bytes.addressEqTail
  simp only [IxVM.Bytes.address_eq_tail]
  refine computes_let_array (by bytes_lookup) hx (by repeat constructor) ?_
  refine computes_let_array (by bytes_lookup) hy (by repeat constructor) ?_

  -- limb 1
  refine computes_let (u := Bytes.limb1 F a) (by bytes_pack) ?_
  refine computes_let (u := Bytes.limb1 F b) (by bytes_pack) ?_
  refine computes_match0 ?_ (fun _ => ?_) (fun _ => ?_)
  · exact computes_sub (computes_var (by bytes_lookup)) (computes_var (by bytes_lookup))
  rotate_left
  · exact computes_lit _
  -- limb 2
  refine computes_let (u := Bytes.limb2 F a) (by bytes_pack) ?_
  refine computes_let (u := Bytes.limb2 F b) (by bytes_pack) ?_
  refine computes_match0 ?_ (fun _ => ?_) (fun _ => ?_)
  · exact computes_sub (computes_var (by bytes_lookup)) (computes_var (by bytes_lookup))
  rotate_left
  · exact computes_lit _
  -- limb 3
  refine computes_let (u := Bytes.limb3 F a) (by bytes_pack) ?_
  refine computes_let (u := Bytes.limb3 F b) (by bytes_pack) ?_
  refine computes_match0 ?_ (fun _ => ?_) (fun _ => ?_)
  · exact computes_sub (computes_var (by bytes_lookup)) (computes_var (by bytes_lookup))
  rotate_left
  · exact computes_lit _
  -- limb 4
  refine computes_let (u := Bytes.limb4 F a) (by bytes_pack) ?_
  refine computes_let (u := Bytes.limb4 F b) (by bytes_pack) ?_
  refine computes_match0 ?_ (fun _ => ?_) (fun _ => ?_)
  · exact computes_sub (computes_var (by bytes_lookup)) (computes_var (by bytes_lookup))
  rotate_left
  · exact computes_lit _
  -- limb 5
  refine computes_let (u := Bytes.limb5 F a) (by bytes_pack) ?_
  refine computes_let (u := Bytes.limb5 F b) (by bytes_pack) ?_
  refine computes_match0 ?_ (fun _ => ?_) (fun _ => ?_)
  · exact computes_sub (computes_var (by bytes_lookup)) (computes_var (by bytes_lookup))
  · exact computes_lit _
  · exact computes_lit _

/-- **`Bytes::address_eq_tail` on two loaded addresses computes the model's
`addressEqTail`**, and allocates nothing. -/
theorem tail_eval {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address}
    (hx : ∀ v, loadValue h x = .ok v → v = .tuple (addrCell F a))
    (hy : ∀ v, loadValue h y = .ok v → v = .tuple (addrCell F b))
    (ev : ObsFn W "Bytes::address_eq_tail" [x, y] h r h' cs) :
    r = .field (Bytes.addressEqTail F a b) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Bytes.address_eq_tail.lookup
    (by simp [IxVM.Bytes.address_eq_tail, ControlLower.hasControl]) ev
  first
    | exact tail_computes hx hy r h' cs d0
    | (simp only [IxVM.Bytes.address_eq_tail, List.map, List.zip, List.zipWith] at d0
       exact tail_computes hx hy r h' cs d0)

/-! ## `Bytes::address_eq` -/

/-- `Bytes::address_eq` computes the model's `addressEq`. -/
theorem address_eq_model {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address}
    (ev : ObsFn W "Bytes::address_eq" [x, y] h r h' cs)
    (ha : Bytes.RepAddressRef addrTy h a x) (hb : Bytes.RepAddressRef addrTy h b y) :
    r = .field (Bytes.addressEq F a b) ∧ h' = h := by
  have hxl := load_addr ha
  have hyl := load_addr hb
  rcases Obs.«Bytes::address_eq».obs ev with
    ⟨v1, v13, m26, x34, y35, m36, cs45, v48, cs62, v65, cs83, ld11, ld23, pr57, ev47, pr74, ev64,
      op41, ev85, -⟩ |
    ⟨v1, v13, v25, m26, x34, y35, m36, cs45, v48, cs62, v65, ld11, ld23, pr57, ev47, pr74, ev64,
      op41, hne, hr, hh, -⟩
  · -- the first bytes agree: `address_eq_tail(a, b)`
    have h1 := hxl _ ld11
    have h13 := hyl _ ld23
    subst h1 h13
    have h48 := projectValue_zero pr57
    have h65 := projectValue_zero pr74
    subst h48 h65
    obtain ⟨e1, e2, -⟩ := Obs.«UInt8::to_field».obs ev47
    subst e1 e2
    obtain ⟨e3, e4, -⟩ := Obs.«UInt8::to_field».obs ev64
    subst e3 e4
    simp only [evalBinOp, Except.ok.injEq] at op41
    have e0 := Value.field.inj op41
    have haddr : Bytes.addressEq F a b = Bytes.addressEqTail F a b := by
      unfold Bytes.addressEq
      exact if_pos e0
    obtain ⟨hr, hh⟩ := tail_eval hxl hyl ev85
    exact ⟨hr.trans (congrArg Value.field haddr.symm), hh⟩
  · -- the first bytes differ: `0`
    have h1 := hxl _ ld11
    have h13 := hyl _ ld23
    subst h1 h13
    have h48 := projectValue_zero pr57
    have h65 := projectValue_zero pr74
    subst h48 h65
    obtain ⟨e1, e2, -⟩ := Obs.«UInt8::to_field».obs ev47
    subst e1 e2
    obtain ⟨e3, e4, -⟩ := Obs.«UInt8::to_field».obs ev64
    subst e3 e4
    simp only [evalBinOp, Except.ok.injEq] at op41
    subst op41
    have n0 : ¬ (_ = _) := fun e => hne (congrArg Value.field e)
    have haddr : Bytes.addressEq F a b = 0 := by
      unfold Bytes.addressEq
      exact if_neg n0
    exact ⟨hr.trans (congrArg Value.field haddr.symm), hh⟩

/-- **`Bytes::address_eq`**: on two represented addresses, `1` if they are equal and `0`
otherwise; no allocation. -/
theorem address_eq_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address}
    (ev : ObsFn W "Bytes::address_eq" [x, y] h r h' cs)
    (ha : Bytes.RepAddressRef addrTy h a x) (hb : Bytes.RepAddressRef addrTy h b y) :
    r = .field (if a = b then 1 else 0) ∧ h' = h := by
  have key := address_eq_model ev ha hb
  have large : Aiur.Library.U64.Compatible F := Aiur.Library.U64.Goldilocks.compatible
  by_cases hab : a = b
  · rw [if_pos hab]
    exact ⟨key.1.trans (congrArg Value.field ((Bytes.address_eq_one_iff large a b).mpr hab)),
      key.2⟩
  · rw [if_neg hab]
    exact ⟨key.1.trans (congrArg Value.field ((Bytes.address_eq_zero_iff large a b).mpr hab)),
      key.2⟩

end IxVM.Refinement.Lib
