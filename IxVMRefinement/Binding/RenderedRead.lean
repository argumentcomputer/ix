import IxVMRefinement.Binding.RenderedSpecs
import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Obs.Names
import IxVMRefinement.Binding.TermCells

/-! # Reading a rendered specification off the function's syntax tree

The rendered specification functions of `KernelRoleSpec` (`role_type`, `op_equation_lhs`,
`op_equation_rhs`, `op_certificate`) are each one `match` on a field value whose arms allocate a
closed term. The arms use eleven kinds of node and one call, and every `let` binds a name:

* levels `Zero`, `Succ`, `Param`; level lists `Nil`, `Cons`;
* terms `Srt`, `Const`, `App`, `BVar`, `Lam`, `Forall`;
* the call `KernelRoles::role_bound_addr(tbl, i)`.

This file reads that fragment once, for every arm of every such function.

* `litArmBody`, `selectArm_litArmBody`: the body of the arm a `match` on literals selects, by
  evaluation over the arm list.
* `Rendered`, `readExpr`: what an expression of the fragment allocates, computed from its syntax
  tree (`readExpr` is evaluated by the kernel on the functions' bodies).
* `Reads`: a value represents what was read, on a heap.
* `readExpr_sound`: an observed evaluation of an expression that reads as `s` extends the heap
  and returns a value that represents `s`.
* `armReadsAs`, `renders_of_armReadsAs`: when the arm at a key reads as a closed term that is
  `T₀` up to its binders' data, the selected arm's observed evaluation returns a pointer that
  represents such a term exactly under the table's keying, along the leading `Forall` cells.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Role)

/-! ## The arm a `match` on literals selects -/

/-- The body of the arm that a `match` on literals selects at a field value. -/
def litArmBody (n : Nat) : List (Generic.Pattern F × Generic.Expr F) → Option (Generic.Expr F)
  | [] => none
  | (.literal c, e) :: rest => if n == ZMod.val c then some e else litArmBody n rest
  | (.wildcard, e) :: _ => some e
  | _ :: _ => none

theorem selectArm_litArmBody {arms : List (Generic.Pattern F × Generic.Expr F)} {x : F}
    {e : Generic.Expr F} (ht : litArmBody (ZMod.val x) arms = some e)
    {h : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (hsel : selectArm W [] h (.field x) arms = Except.ok (some (bs, body))) :
    bs = [] ∧ body = e := by
  induction arms with
  | nil => simp [litArmBody] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, expr⟩
    cases pat with
    | literal c =>
      simp only [litArmBody] at ht
      by_cases hxc_b : (ZMod.val x == ZMod.val c) = true
      · rw [ite_eq_left hxc_b] at ht
        injection ht with hm_eq
        have hxc : x = c := ZMod.val_injective _ (beq_iff_eq.mp hxc_b)
        subst hxc
        rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
        · obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal x) mt
          exact ⟨rfl, hm_eq⟩
        · exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal x) nm)
      · rw [ite_eq_right hxc_b] at ht
        have hxc_ne : x ≠ c := fun e => hxc_b (beq_iff_eq.mpr (congrArg ZMod.val e))
        rcases selectArm_cons_inv hsel with ⟨mt, _⟩ | ⟨_, hsel'⟩
        · obtain ⟨hv, _⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
          exact absurd (Value.field.inj hv) hxc_ne
        · exact ih ht hsel'
    | wildcard =>
      simp only [litArmBody, Option.some.injEq] at ht
      rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
      · exact ⟨matchPattern_wildcard_inv mt, ht⟩
      · exact (matchPattern_wildcard_none nm).elim
    | _ => simp [litArmBody] at ht

/-! ## What is read, and what represents it -/

/-- What a rendered subterm stands for. -/
inductive Rendered where
  /-- A field literal. -/
  | num (i : F)
  /-- The role table. -/
  | table
  /-- The address the table binds a role to. -/
  | addr (r : Role)
  /-- A universe level. -/
  | lvl (l : KLevel)
  /-- A list of universe levels. -/
  | lvls (ls : List KLevel)
  /-- A term, and the number of `Forall` cells its pointer leads with. -/
  | tm (e : KExpr) (sp : Nat)

/-- Every loose bound variable of the term is below `k`, and the term has no free variable,
`let`, literal or projection. -/
def closedBelow : Nat → KExpr → Bool
  | k, .bvar i => decide (i < k)
  | _, .fvar _ _ => false
  | _, .sort _ => true
  | _, .const _ _ => true
  | k, .app f a => closedBelow k f && closedBelow k a
  | k, .lam T B _ => closedBelow k T && closedBelow (k + 1) B
  | k, .forallE T B _ => closedBelow k T && closedBelow (k + 1) B
  | _, .letE _ _ _ _ => false
  | _, .lit _ => false
  | _, .proj _ _ _ => false

/-- **A heap term with no `Let` and no `Proj` cell**: the pointer is to a `Srt`, `Const` or `BVar`
cell, or to an `App`, `Lam` or `Forall` cell whose term arguments are such terms. Such a term is
its image cell by cell: no cell hides under a `let`'s ζ-reduct, and no cell of it heads a
projection. It stays so on every larger heap (`LetProjFree.mono`). -/
inductive LetProjFree (h : Heap F) : SourceValue F → Prop where
  | sort {addr : Nat} {lp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp])) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)
  | const {addr : Nat} {ap lsp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp])) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)
  | bvar {addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i])) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : LetProjFree h fp) (ra : LetProjFree h ap) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)
  | lam {addr : Nat} {tp bp lp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : LetProjFree h tp) (rb : LetProjFree h bp) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)
  | forallE {addr : Nat} {tp bp lp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : LetProjFree h tp) (rb : LetProjFree h bp) :
      LetProjFree h (.ptr (.enum kexprEnum) addr)

theorem LetProjFree.mono {h h' : Heap F} {p : SourceValue F} (ext : Heap.Extends h h')
    (hp : LetProjFree h p) : LetProjFree h' p := by
  induction hp with
  | sort cell => exact .sort (ext.getElem?_eq cell)
  | const cell => exact .const (ext.getElem?_eq cell)
  | bvar cell => exact .bvar (ext.getElem?_eq cell)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb
  | forallE cell _ _ iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb

private theorem cell_ctor_eq {h : Heap F} {addr : Nat} {n n' : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct kexprEnum n xs))
    (c₂ : h[addr]? = some (.construct kexprEnum n' ys)) : n = n' ∧ xs = ys := by
  have := Option.some.inj (c₁.symm.trans c₂)
  injection this with _ hn hx
  exact ⟨hn, hx⟩

/-- The cell of a term with no `Let` and no `Proj` cell is none of `Let`, `Proj`, `Lit`. -/
theorem LetProjFree.cell_ok {h : Heap F} {addr : Nat} {n : String} {xs : List (SourceValue F)}
    (hp : LetProjFree h (.ptr (.enum kexprEnum) addr))
    (cell : h[addr]? = some (.construct kexprEnum n xs)) :
    n ≠ "Let" ∧ n ≠ "Proj" ∧ n ≠ "Lit" := by
  have hn : n = "Srt" ∨ n = "Const" ∨ n = "BVar" ∨ n = "App" ∨ n = "Lam" ∨ n = "Forall" := by
    cases hp with
    | sort c' => exact Or.inl (cell_ctor_eq cell c').1
    | const c' => exact Or.inr (Or.inl (cell_ctor_eq cell c').1)
    | bvar c' => exact Or.inr (Or.inr (Or.inl (cell_ctor_eq cell c').1))
    | app c' _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl (cell_ctor_eq cell c').1)))
    | lam c' _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cell_ctor_eq cell c').1))))
    | forallE c' _ _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (cell_ctor_eq cell c').1))))
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem LetProjFree.app_inv {h : Heap F} {addr : Nat} {fp ap : SourceValue F}
    (hp : LetProjFree h (.ptr (.enum kexprEnum) addr))
    (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap])) :
    LetProjFree h fp ∧ LetProjFree h ap := by
  cases hp with
  | app c' rf ra =>
    have hxs := (cell_ctor_eq cell c').2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨rf, ra⟩
  | sort c' | const c' | bvar c' => exact absurd (cell_ctor_eq cell c').1 (by decide)
  | lam c' _ _ | forallE c' _ _ => exact absurd (cell_ctor_eq cell c').1 (by decide)

theorem LetProjFree.lam_inv {h : Heap F} {addr : Nat} {tp bp lp : SourceValue F}
    (hp : LetProjFree h (.ptr (.enum kexprEnum) addr))
    (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp])) :
    LetProjFree h tp ∧ LetProjFree h bp := by
  cases hp with
  | lam c' rt rb =>
    have hxs := (cell_ctor_eq cell c').2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, -⟩ := hxs
    exact ⟨rt, rb⟩
  | sort c' | const c' | bvar c' => exact absurd (cell_ctor_eq cell c').1 (by decide)
  | app c' _ _ | forallE c' _ _ => exact absurd (cell_ctor_eq cell c').1 (by decide)

theorem LetProjFree.forall_inv {h : Heap F} {addr : Nat} {tp bp lp : SourceValue F}
    (hp : LetProjFree h (.ptr (.enum kexprEnum) addr))
    (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp])) :
    LetProjFree h tp ∧ LetProjFree h bp := by
  cases hp with
  | forallE c' rt rb =>
    have hxs := (cell_ctor_eq cell c').2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, -⟩ := hxs
    exact ⟨rt, rb⟩
  | sort c' | const c' | bvar c' => exact absurd (cell_ctor_eq cell c').1 (by decide)
  | app c' _ _ | lam c' _ _ => exact absurd (cell_ctor_eq cell c').1 (by decide)

/-- A term with no `Let` and no `Proj` cell points to a term cell. -/
theorem LetProjFree.ptr {h : Heap F} {p : SourceValue F} (hp : LetProjFree h p) :
    ∃ addr n xs, p = .ptr (.enum kexprEnum) addr ∧
      h[addr]? = some (.construct kexprEnum n xs) := by
  cases hp with
  | sort cell | const cell | bvar cell => exact ⟨_, _, _, rfl, cell⟩
  | app cell _ _ | lam cell _ _ | forallE cell _ _ => exact ⟨_, _, _, rfl, cell⟩

private theorem cell_of_load {h : Heap F} {addr : Nat} {n : String} {xs : List (SourceValue F)}
    {v : SourceValue F} (cell : h[addr]? = some (.construct kexprEnum n xs))
    (hl : loadValue h (.ptr (.enum kexprEnum) addr) = .ok v) : h[addr]? = some v := by
  rw [loadValue_enum_cell cell] at hl
  injection hl with hv
  rw [← hv]
  exact cell

/-- The two parts of a `Lam` cell a term with no `Let` and no `Proj` cell loads. -/
theorem LetProjFree.lam_of_load {h : Heap F} {p tp bp lp : SourceValue F}
    (hp : LetProjFree h p) (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp])) :
    LetProjFree h tp ∧ LetProjFree h bp := by
  obtain ⟨addr, n, xs, rfl, cell⟩ := hp.ptr
  exact hp.lam_inv (cell_of_load cell ld)

/-- The two parts of a `Forall` cell a term with no `Let` and no `Proj` cell loads. -/
theorem LetProjFree.forall_of_load {h : Heap F} {p tp bp lp : SourceValue F}
    (hp : LetProjFree h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    LetProjFree h tp ∧ LetProjFree h bp := by
  obtain ⟨addr, n, xs, rfl, cell⟩ := hp.ptr
  exact hp.forall_inv (cell_of_load cell ld)

/-- **A term with no `Let` and no `Proj` cell heads no projection.** -/
theorem LetProjFree.not_projIn {h : Heap F} {p : SourceValue F} {x : Bytes.Address}
    (m : ProjIn h p x) : LetProjFree h p → False := by
  induction m with
  | head cell _ => exact fun hp => (hp.cell_ok cell).2.1 rfl
  | projArg cell _ _ => exact fun hp => (hp.cell_ok cell).2.1 rfl
  | appFn cell _ ih => exact fun hp => ih (hp.app_inv cell).1
  | appArg cell _ ih => exact fun hp => ih (hp.app_inv cell).2
  | lamTy cell _ ih => exact fun hp => ih (hp.lam_inv cell).1
  | lamBody cell _ ih => exact fun hp => ih (hp.lam_inv cell).2
  | forallTy cell _ ih => exact fun hp => ih (hp.forall_inv cell).1
  | forallBody cell _ ih => exact fun hp => ih (hp.forall_inv cell).2
  | letTy cell _ _ | letVal cell _ _ | letBody cell _ _ =>
    exact fun hp => (hp.cell_ok cell).1 rfl

/-- **The cells of a term with no `Let` and no `Proj` cell are constants its image names**: every
predicate all the image's constants satisfy holds of the key of each cell. -/
theorem LetProjFree.addrIn_named {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    LetProjFree h p → ∀ x, AddrIn h p x →
      ∀ P, E.constsResolveBy P = true → P (κ (ixAddr x)) = true := by
  induction rep with
  | bvarLocal cell => exact fun _ x hin => (addrIn_none cell (by decide) hin).elim
  | bvarFree cell => exact fun _ x hin => (addrIn_none cell (by decide) hin).elim
  | sort cell => exact fun _ x hin => (addrIn_none cell (by decide) hin).elim
  | const cell ra rls hus =>
    intro _ x hin P hP
    have e := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra (addrIn_const_inv cell hin)
    subst e
    simpa only [Ix.Kernel.Expr.constsResolveBy] using hP
  | app cell _ _ ihf iha =>
    intro hp x hin P hP
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hP
    rcases addrIn_app_inv cell hin with h1 | h1
    · exact ihf (hp.app_inv cell).1 x h1 P hP.1
    · exact iha (hp.app_inv cell).2 x h1 P hP.2
  | lam cell _ _ _ iht ihb =>
    intro hp x hin P hP
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hP
    rcases addrIn_lam_inv cell hin with h1 | h1
    · exact iht (hp.lam_inv cell).1 x h1 P hP.1
    · exact ihb (hp.lam_inv cell).2 x h1 P hP.2
  | forallE cell _ _ _ iht ihb =>
    intro hp x hin P hP
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hP
    rcases addrIn_forall_inv cell hin with h1 | h1
    · exact iht (hp.forall_inv cell).1 x h1 P hP.1
    · exact ihb (hp.forall_inv cell).2 x h1 P hP.2
  | letE cell => exact fun hp => ((hp.cell_ok cell).1 rfl).elim
  | litNat cell => exact fun hp => ((hp.cell_ok cell).2.2 rfl).elim
  | litStr cell => exact fun hp => ((hp.cell_ok cell).2.2 rfl).elim
  | proj cell => exact fun hp => ((hp.cell_ok cell).2.1 rfl).elim

/-- **A value represents what was read**, on the heap `h`, under the keying of the table `t`. A
term is represented exactly at every binder depth that closes it, its cells are addresses of
roles it names, and its pointer reaches no `Let` and no `Proj` cell. -/
inductive Reads (t : Ix.Kernel.RoleTable) (h : Heap F) : Rendered → SourceValue F → Prop where
  | num {i : F} : Reads t h (.num i) (.field i)
  | table {v : SourceValue F} (rep : TableRep t h v) : Reads t h .table v
  | addr {r : Role} {v : SourceValue F} {a : Bytes.Address}
      (ra : Bytes.RepAddressRef addrTy h a v) (had : t.addressOf? r = some (ixAddr a)) :
      Reads t h (.addr r) v
  | lvl {l : KLevel} {v : SourceValue F} (rep : RepKLevel h l v) : Reads t h (.lvl l) v
  | lvls {ls : List KLevel} {v : SourceValue F} (rep : RepKLevelList h ls v) :
      Reads t h (.lvls ls) v
  | tm {e : KExpr} {sp : Nat} {v : SourceValue F}
      (rep : ∀ (d : Nat) (Γ : Nat → KExpr) (k : Nat), closedBelow k e = true →
        Decl.TmExact (keyOf t) d Γ h k e v)
      (spine : OpOpen.ForallSpine h sp v)
      (cells : ∀ (h₂ : Heap F), Heap.Extends h h₂ → ∀ x, AddrIn h₂ v x →
        ∃ r, t.addressOf? r = some (ixAddr x) ∧
          ∀ P, e.constsResolveBy P = true → P (Ix.Kernel.Key.role r) = true)
      (plain : LetProjFree h v) :
      Reads t h (.tm e sp) v

theorem Reads.mono {t : Ix.Kernel.RoleTable} {h h' : Heap F} {s : Rendered} {v : SourceValue F}
    (ext : Heap.Extends h h') (rd : Reads t h s v) : Reads t h' s v := by
  cases rd with
  | num => exact .num
  | table rep => exact .table (rep.mono ext)
  | addr ra had => exact .addr (Bytes.repAddressRef_heapMono₂ addrTy ext ra) had
  | lvl rep => exact .lvl (rep.mono ext)
  | lvls rep => exact .lvls (rep.mono ext)
  | tm rep spine cells plain =>
    exact .tm (fun d Γ k hk => (rep d Γ k hk).mono ext) (spine.mono ext)
      (fun h₂ e₂ x hin => cells h₂ (ext.trans e₂) x hin) (plain.mono ext)

theorem readsAll_mono {t : Ix.Kernel.RoleTable} {h h' : Heap F} {rs : List Rendered}
    {vs : List (SourceValue F)} (ext : Heap.Extends h h')
    (hx : List.Forall₂ (Reads t h) rs vs) : List.Forall₂ (Reads t h') rs vs := by
  induction hx with
  | nil => exact .nil
  | cons r _ ih => exact .cons (r.mono ext) ih

private theorem natCast_val (x : F) : ((ZMod.val x : Nat) : F) = x := by
  apply ZMod.val_injective
  exact RolesAux.val_natCast (ZMod.val_lt x)

private theorem ext_of_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    Heap.Extends h h' := by
  rw [hm]
  exact Heap.Extends.snoc _ _

private theorem cell_of_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    h'[h.length]? = some x := by
  rw [hm]
  simp

/-! ## The nodes -/

def readZero : List Rendered → Option Rendered
  | [] => some (.lvl .zero)
  | _ => none

def readSucc : List Rendered → Option Rendered
  | [.lvl l] => some (.lvl (.succ l))
  | _ => none

def readParam : List Rendered → Option Rendered
  | [.num i] => if ZMod.val i < 4294967296 then some (.lvl (.param (ZMod.val i))) else none
  | _ => none

def readNil : List Rendered → Option Rendered
  | [] => some (.lvls [])
  | _ => none

def readCons : List Rendered → Option Rendered
  | [.lvl l, .lvls ls] => some (.lvls (l :: ls))
  | _ => none

def readSort : List Rendered → Option Rendered
  | [.lvl l] => some (.tm (.sort l) 0)
  | _ => none

def readConst : List Rendered → Option Rendered
  | [.addr r, .lvls ls] => some (.tm (.const (Ix.Kernel.Key.role r) ls) 0)
  | _ => none

def readApp : List Rendered → Option Rendered
  | [.tm f _, .tm a _] => some (.tm (.app f a) 0)
  | _ => none

def readBVar : List Rendered → Option Rendered
  | [.num i] =>
    if ZMod.val i < 9223372036854775808 then some (.tm (.bvar (ZMod.val i)) 0) else none
  | _ => none

def readLam : List Rendered → Option Rendered
  | [.tm T _, .tm B _, .lvl l] => some (.tm (.lam T B (bmeta l)) 0)
  | _ => none

def readForall : List Rendered → Option Rendered
  | [.tm T _, .tm B sp, .lvl l] => some (.tm (.forallE T B (bmeta l)) (sp + 1))
  | _ => none

/-- What a cell of the enumeration `ty` with the constructor `ctor` stands for, from what its
arguments stand for. -/
def readNode (ty ctor : String) (xs : List Rendered) : Option Rendered :=
  if ty = klevelEnum then
    if ctor = "Zero" then readZero xs
    else if ctor = "Succ" then readSucc xs
    else if ctor = "Param" then readParam xs
    else none
  else if ty = KernelLevels.klevelListEnum then
    if ctor = "Nil" then readNil xs
    else if ctor = "Cons" then readCons xs
    else none
  else if ty = kexprEnum then
    if ctor = "Srt" then readSort xs
    else if ctor = "Const" then readConst xs
    else if ctor = "App" then readApp xs
    else if ctor = "BVar" then readBVar xs
    else if ctor = "Lam" then readLam xs
    else if ctor = "Forall" then readForall xs
    else none
  else none

section Nodes

variable {t : Ix.Kernel.RoleTable} {h : Heap F} {xs : List Rendered} {s : Rendered}
  {addr : Nat} {vs : List (SourceValue F)}

theorem readZero_sound (hn : readZero xs = some s)
    (cell : h[addr]? = some (.construct klevelEnum "Zero" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum klevelEnum) addr) := by
  unfold readZero at hn
  split at hn
  · cases hn
    cases hxs
    exact .lvl (.zero cell)
  · cases hn

theorem readSucc_sound (hn : readSucc xs = some s)
    (cell : h[addr]? = some (.construct klevelEnum "Succ" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum klevelEnum) addr) := by
  unfold readSucc at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2
      cases r1 with
      | lvl rep => exact .lvl (.succ cell rep)
  · cases hn

theorem readParam_sound (hn : readParam xs = some s)
    (cell : h[addr]? = some (.construct klevelEnum "Param" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum klevelEnum) addr) := by
  unfold readParam at hn
  split at hn
  · split at hn
    · rename_i hlt
      cases hn
      cases hxs with
      | cons r1 r2 =>
        cases r2
        cases r1 with
        | num =>
          refine .lvl (.param hlt ?_)
          rw [natCast_val]
          exact cell
    · cases hn
  · cases hn

theorem readNil_sound (hn : readNil xs = some s)
    (cell : h[addr]? = some (.construct KernelLevels.klevelListEnum "Nil" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) :
    Reads t h s (.ptr (.enum KernelLevels.klevelListEnum) addr) := by
  unfold readNil at hn
  split at hn
  · cases hn
    cases hxs
    exact .lvls (RepLinkedList.nil cell)
  · cases hn

theorem readCons_sound (hn : readCons xs = some s)
    (cell : h[addr]? = some (.construct KernelLevels.klevelListEnum "Cons" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) :
    Reads t h s (.ptr (.enum KernelLevels.klevelListEnum) addr) := by
  unfold readCons at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2 with
      | cons r2a r2b =>
        cases r2b
        cases r1 with
        | lvl rep =>
          cases r2a with
          | lvls reps => exact .lvls (RepLinkedList.cons cell rep reps)
  · cases hn

theorem readSort_sound (hn : readSort xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "Srt" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readSort at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2
      cases r1 with
      | lvl rep =>
        exact .tm (fun d Γ k _ => .sort cell rep) (.zero _)
          (fun h₂ e₂ x hin => (addrIn_none (e₂.getElem?_eq cell) (by decide) hin).elim)
          (.sort cell)
  · cases hn

theorem readConst_sound (htwf : t.wf = true) (hn : readConst xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "Const" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readConst at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2 with
      | cons r2a r2b =>
        cases r2b
        cases r1 with
        | addr ra had =>
          cases r2a with
          | lvls reps =>
            refine .tm (fun d Γ k _ => ?_) (.zero _) (fun h₂ e₂ x hin => ?_) (.const cell)
            · have hk := keyOf_of_addressOf htwf had
              rw [← hk]
              exact .const cell ra reps
            · have e := Bytes.repAddressRef_inj U32.Goldilocks.compatible
                (Bytes.repAddressRef_heapMono₂ addrTy e₂ ra)
                (addrIn_const_inv (e₂.getElem?_eq cell) hin)
              subst e
              exact ⟨_, had, fun P hP => hP⟩
  · cases hn

theorem readApp_sound (hn : readApp xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "App" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readApp at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2 with
      | cons r2a r2b =>
        cases r2b
        cases r1 with
        | tm repf _ cf pf =>
          cases r2a with
          | tm repa _ ca pa =>
            refine .tm (fun d Γ k hk => ?_) (.zero _) (fun h₂ e₂ x hin => ?_) (.app cell pf pa)
            · simp only [closedBelow, Bool.and_eq_true] at hk
              exact .app cell (repf d Γ k hk.1) (repa d Γ k hk.2)
            · rcases addrIn_app_inv (e₂.getElem?_eq cell) hin with h1 | h1
              · obtain ⟨r, hr, hP⟩ := cf h₂ e₂ x h1
                exact ⟨r, hr, fun P hp => hP P (by
                  simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp
                  exact hp.1)⟩
              · obtain ⟨r, hr, hP⟩ := ca h₂ e₂ x h1
                exact ⟨r, hr, fun P hp => hP P (by
                  simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp
                  exact hp.2)⟩
  · cases hn

theorem readBVar_sound (hn : readBVar xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "BVar" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readBVar at hn
  split at hn
  · split at hn
    · rename_i hsmall
      cases hn
      cases hxs with
      | cons r1 r2 =>
        cases r2
        cases r1 with
        | num =>
          refine .tm (fun d Γ k hk => ?_) (.zero _)
            (fun h₂ e₂ x hin => (addrIn_none (e₂.getElem?_eq cell) (by decide) hin).elim)
            (.bvar cell)
          simp only [closedBelow, decide_eq_true_eq] at hk
          exact .bvarLocal cell hsmall hk
    · cases hn
  · cases hn

/-- The cells of a binder term are those of its two parts, each a role a part names. -/
private theorem binder_cells {t : Ix.Kernel.RoleTable} {h₂ : Heap F} {tp bp : SourceValue F}
    {x : Bytes.Address} {T B : KExpr} {m : Ix.Kernel.BinderMeta}
    (hin : AddrIn h₂ tp x ∨ AddrIn h₂ bp x)
    (cT : AddrIn h₂ tp x → ∃ r, t.addressOf? r = some (ixAddr x) ∧
      ∀ P, T.constsResolveBy P = true → P (Ix.Kernel.Key.role r) = true)
    (cB : AddrIn h₂ bp x → ∃ r, t.addressOf? r = some (ixAddr x) ∧
      ∀ P, B.constsResolveBy P = true → P (Ix.Kernel.Key.role r) = true) :
    (∃ r, t.addressOf? r = some (ixAddr x) ∧
      ∀ P, (Ix.Kernel.Expr.lam T B m : KExpr).constsResolveBy P = true →
        P (Ix.Kernel.Key.role r) = true) ∧
    (∃ r, t.addressOf? r = some (ixAddr x) ∧
      ∀ P, (Ix.Kernel.Expr.forallE T B m : KExpr).constsResolveBy P = true →
        P (Ix.Kernel.Key.role r) = true) := by
  rcases hin with h1 | h1
  · obtain ⟨r, hr, hP⟩ := cT h1
    exact ⟨⟨r, hr, fun P hp => hP P (by
        simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp; exact hp.1)⟩,
      ⟨r, hr, fun P hp => hP P (by
        simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp; exact hp.1)⟩⟩
  · obtain ⟨r, hr, hP⟩ := cB h1
    exact ⟨⟨r, hr, fun P hp => hP P (by
        simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp; exact hp.2)⟩,
      ⟨r, hr, fun P hp => hP P (by
        simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at hp; exact hp.2)⟩⟩

theorem readLam_sound (hn : readLam xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "Lam" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readLam at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2 with
      | cons r2a r2b =>
        cases r2b with
        | cons r3a r3b =>
          cases r3b
          cases r1 with
          | tm repT _ cT pT =>
            cases r2a with
            | tm repB _ cB pB =>
              cases r3a with
              | lvl repl =>
                refine .tm (fun d Γ k hk => ?_) (.zero _) (fun h₂ e₂ x hin => ?_)
                  (.lam cell pT pB)
                · simp only [closedBelow, Bool.and_eq_true] at hk
                  exact .lam cell (repT d Γ k hk.1) (repB d Γ (k + 1) hk.2) repl
                · exact (binder_cells (addrIn_lam_inv (e₂.getElem?_eq cell) hin)
                    (cT h₂ e₂ x) (cB h₂ e₂ x)).1
  · cases hn

theorem readForall_sound (hn : readForall xs = some s)
    (cell : h[addr]? = some (.construct kexprEnum "Forall" vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum kexprEnum) addr) := by
  unfold readForall at hn
  split at hn
  · cases hn
    cases hxs with
    | cons r1 r2 =>
      cases r2 with
      | cons r2a r2b =>
        cases r2b with
        | cons r3a r3b =>
          cases r3b
          cases r1 with
          | tm repT _ cT pT =>
            cases r2a with
            | tm repB spB cB pB =>
              cases r3a with
              | lvl repl =>
                refine .tm (fun d Γ k hk => ?_) (.succ (loadValue_enum_cell cell) spB)
                  (fun h₂ e₂ x hin => ?_) (.forallE cell pT pB)
                · simp only [closedBelow, Bool.and_eq_true] at hk
                  exact .forallE cell (repT d Γ k hk.1) (repB d Γ (k + 1) hk.2) repl
                · exact (binder_cells (addrIn_forall_inv (e₂.getElem?_eq cell) hin)
                    (cT h₂ e₂ x) (cB h₂ e₂ x)).2
  · cases hn

/-- **A stored cell represents what its node reads as**, when its arguments represent what they
read as. -/
theorem readNode_sound (htwf : t.wf = true) {ty ctor : String}
    (hn : readNode ty ctor xs = some s)
    (cell : h[addr]? = some (.construct ty ctor vs))
    (hxs : List.Forall₂ (Reads t h) xs vs) : Reads t h s (.ptr (.enum ty) addr) := by
  unfold readNode at hn
  split at hn
  · rename_i hty
    subst hty
    split at hn
    · rename_i hc
      subst hc
      exact readZero_sound hn cell hxs
    · split at hn
      · rename_i hc
        subst hc
        exact readSucc_sound hn cell hxs
      · split at hn
        · rename_i hc
          subst hc
          exact readParam_sound hn cell hxs
        · cases hn
  · split at hn
    · rename_i hty
      subst hty
      split at hn
      · rename_i hc
        subst hc
        exact readNil_sound hn cell hxs
      · split at hn
        · rename_i hc
          subst hc
          exact readCons_sound hn cell hxs
        · cases hn
    · split at hn
      · rename_i hty
        subst hty
        split at hn
        · rename_i hc
          subst hc
          exact readSort_sound hn cell hxs
        · split at hn
          · rename_i hc
            subst hc
            exact readConst_sound htwf hn cell hxs
          · split at hn
            · rename_i hc
              subst hc
              exact readApp_sound hn cell hxs
            · split at hn
              · rename_i hc
                subst hc
                exact readBVar_sound hn cell hxs
              · split at hn
                · rename_i hc
                  subst hc
                  exact readLam_sound hn cell hxs
                · split at hn
                  · rename_i hc
                    subst hc
                    exact readForall_sound hn cell hxs
                  · cases hn
      · cases hn

end Nodes

/-! ## The instance a constructed cell belongs to, and the one call -/

/-- The level list's cell enumeration is the instance of `Lists::Node` at level pointers. -/
theorem klevelList_instance :
    instanceName [] "Lists::Node" (some [.ptr (.named "KernelTypes::KLevelNode" [])]) =
      KernelLevels.klevelListEnum := by
  decide +kernel

/-- The enumeration a `construct` node's cell belongs to: the named type at no arguments, or the
level list's. -/
def nodeInstance (name : String) : Option (List Generic.Ty) → Option String
  | some [] => some name
  | some [.ptr (.named inner [])] =>
    if name = "Lists::Node" ∧ inner = "KernelTypes::KLevelNode" then
      some KernelLevels.klevelListEnum
    else none
  | _ => none

theorem nodeInstance_sound {name : String} {targs : Option (List Generic.Ty)} {iname : String}
    (hi : nodeInstance name targs = some iname) : instanceName [] name targs = iname := by
  unfold nodeInstance at hi
  split at hi
  · cases hi
    exact instanceName_plain_some [] _
  · split at hi
    · rename_i hc
      cases hi
      obtain ⟨rfl, rfl⟩ := hc
      exact klevelList_instance
    · cases hi
  · cases hi

/-- The address the table binds the role numbered `i` to. -/
def readAddr (i : F) : Option Rendered := (Role.ofIdx? (ZMod.val i)).map Rendered.addr

theorem readAddr_sound {t : Ix.Kernel.RoleTable} {i : F} {s : Rendered} {vt res : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hc : readAddr i = some s) (htbl : TableRep t h vt)
    (ev : ObsFn W "KernelRoles::role_bound_addr" [vt, .field i] h res h' cs) :
    Heap.Extends h h' ∧ Reads t h' s res := by
  unfold readAddr at hc
  cases hro : Role.ofIdx? (ZMod.val i) with
  | none =>
    rw [hro] at hc
    cases hc
  | some ro =>
    rw [hro] at hc
    cases hc
    have hi : roleNum ro = i := by
      have hidx := Ix.Kernel.Role.idx_ofIdx? hro
      unfold roleNum
      rw [hidx]
      exact natCast_val i
    rw [← hi] at ev
    obtain ⟨x1, a, ⟨a', ra, ha⟩, had⟩ := RoleVal.role_bound_addr_uncond htbl ev
    subst ha
    exact ⟨x1, .addr ra had⟩

/-- What a call returns, from what its arguments stand for: only the table's address lookup. -/
def readCall (fname : String) (targs : Option (List Generic.Ty)) (xs : List Rendered) :
    Option Rendered :=
  match targs, xs with
  | some [], [.table, .num i] =>
    if fname = "KernelRoles::role_bound_addr" then readAddr i else none
  | _, _ => none

theorem readCall_sound {t : Ix.Kernel.RoleTable} {fname : String}
    {targs : Option (List Generic.Ty)} {xs : List Rendered} {s : Rendered}
    {vs : List (SourceValue F)} {res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hc : readCall fname targs xs = some s) (hxs : List.Forall₂ (Reads t h) xs vs)
    (ev : ObsFn W (instanceName [] fname targs) vs h res h' cs) :
    Heap.Extends h h' ∧ Reads t h' s res := by
  unfold readCall at hc
  split at hc
  · split at hc
    · rename_i hf
      subst hf
      rw [instanceName_plain_some] at ev
      cases hxs with
      | cons r1 r2 =>
        cases r2 with
        | cons r2a r2b =>
          cases r2b
          cases r1 with
          | table htbl =>
            cases r2a with
            | num => exact readAddr_sound hc htbl ev
    · cases hc
  · cases hc

/-! ## The reader -/

/-- What a name stands for, in what was read so far. -/
def lookupR (x : String) : List (String × Rendered) → Option Rendered
  | [] => none
  | p :: rest => if p.1 = x then some p.2 else lookupR x rest

/-- What the arguments stand for, left to right. -/
def readArgs (rd : Generic.Expr F → Option Rendered) :
    List (Generic.Expr F) → Option (List Rendered)
  | [] => some []
  | e :: es =>
    match rd e with
    | none => none
    | some r =>
      match readArgs rd es with
      | none => none
      | some rs => some (r :: rs)

/-- A `let` that binds a name. -/
def readLet (rd : List (String × Rendered) → Generic.Expr F → Option Rendered)
    (env : List (String × Rendered)) (p : Generic.Pattern F) (v b : Generic.Expr F) :
    Option Rendered :=
  match p with
  | .bind x =>
    match rd env v with
    | none => none
    | some r => rd ((x, r) :: env) b
  | _ => none

/-- A stored constructed cell. -/
def readStore (rd : List (String × Rendered) → Generic.Expr F → Option Rendered)
    (env : List (String × Rendered)) : Generic.Expr F → Option Rendered
  | .construct name targs ctor args =>
    match nodeInstance name targs with
    | none => none
    | some iname =>
      match readArgs (rd env) args with
      | none => none
      | some rs => readNode iname ctor rs
  | _ => none

/-- One layer of the reader over a reader of the subexpressions. -/
def readStep (rd : List (String × Rendered) → Generic.Expr F → Option Rendered)
    (env : List (String × Rendered)) : Generic.Expr F → Option Rendered
  | .var x => lookupR x env
  | .literal i => some (.num i)
  | .letValue p v b => readLet rd env p v b
  | .call fname targs args =>
    match readArgs (rd env) args with
    | none => none
    | some rs => readCall fname targs rs
  | .store inner => readStore rd env inner
  | _ => none

/-- **What an expression of the fragment allocates**, to a depth. -/
def readExpr : Nat → List (String × Rendered) → Generic.Expr F → Option Rendered
  | 0 => fun _ _ => none
  | n + 1 => readStep (readExpr n)

/-- The names read so far are bound, in the evaluation's environment, to values that represent
what they stand for. -/
def EnvReads (t : Ix.Kernel.RoleTable) (h : Heap F) (env : List (String × Rendered))
    (locals : Environment F Nat) : Prop :=
  ∀ x r, lookupR x env = some r →
    ∃ v, List.find? (fun p => p.1 == x) locals = some (x, v) ∧ Reads t h r v

theorem EnvReads.mono {t : Ix.Kernel.RoleTable} {h h' : Heap F}
    {env : List (String × Rendered)} {locals : Environment F Nat} (ext : Heap.Extends h h')
    (henv : EnvReads t h env locals) : EnvReads t h' env locals := by
  intro x r hx
  obtain ⟨v, hf, rv⟩ := henv x r hx
  exact ⟨v, hf, rv.mono ext⟩

theorem EnvReads.cons {t : Ix.Kernel.RoleTable} {h : Heap F} {env : List (String × Rendered)}
    {locals : Environment F Nat} {x : String} {r : Rendered} {v : SourceValue F}
    (henv : EnvReads t h env locals) (rv : Reads t h r v) :
    EnvReads t h ((x, r) :: env) ((x, v) :: locals) := by
  intro y s hy
  have hy' : (if x = y then some r else lookupR y env) = some s := hy
  by_cases hxy : x = y
  · rw [ite_eq_left hxy] at hy'
    cases hy'
    subst hxy
    exact ⟨v, by simp, rv⟩
  · rw [ite_eq_right hxy] at hy'
    obtain ⟨w, hw, rdw⟩ := henv y s hy'
    have hb : (x == y) = false := by simp [hxy]
    refine ⟨w, ?_, rdw⟩
    rw [← hw]
    simp [hb]

/-- A reader is sound: an observed evaluation of an expression it reads extends the heap and
returns a value that represents what was read. -/
def SoundReader (t : Ix.Kernel.RoleTable)
    (rd : List (String × Rendered) → Generic.Expr F → Option Rendered) : Prop :=
  ∀ {env : List (String × Rendered)} {e : Generic.Expr F} {s : Rendered}
    {locals : Environment F Nat} {h : Heap F} {res : SourceValue F} {h' : Heap F}
    {cs : List (Call F)},
    rd env e = some s → EnvReads t h env locals → ObsExpr W [] locals e h res h' cs →
    Heap.Extends h h' ∧ Reads t h' s res

section Sound

variable {t : Ix.Kernel.RoleTable}
  {rd : List (String × Rendered) → Generic.Expr F → Option Rendered}

theorem readArgs_sound (hrd : SoundReader t rd) {env : List (String × Rendered)}
    {locals : Environment F Nat} :
    ∀ {es : List (Generic.Expr F)} {rs : List Rendered} {h : Heap F}
      {vs : List (SourceValue F)} {h' : Heap F} {cs : List (Call F)},
      readArgs (rd env) es = some rs → EnvReads t h env locals →
      ObsArgs W [] locals es h vs h' cs →
      Heap.Extends h h' ∧ List.Forall₂ (Reads t h') rs vs := by
  intro es
  induction es with
  | nil =>
    intro rs h vs h' cs hr henv oa
    simp only [readArgs, Option.some.injEq] at hr
    subst hr
    obtain ⟨hvs, hh, -⟩ := oa.nil_inv
    subst hvs
    subst hh
    exact ⟨Heap.Extends.refl _, .nil⟩
  | cons e es ih =>
    intro rs h vs h' cs hr henv oa
    cases he : rd env e with
    | none => simp [readArgs, he] at hr
    | some r =>
      cases hes : readArgs (rd env) es with
      | none => simp [readArgs, he, hes] at hr
      | some rs' =>
        simp only [readArgs, he, hes, Option.some.injEq] at hr
        subst hr
        obtain ⟨v, vs', mid, c1, c2, hvs, de, oes, -⟩ := oa.cons_inv
        subst hvs
        obtain ⟨x1, rv⟩ := hrd he henv de
        obtain ⟨x2, rvs⟩ := ih hes (henv.mono x1) oes
        exact ⟨x1.trans x2, .cons (rv.mono x2) rvs⟩

theorem readLet_sound (hrd : SoundReader t rd) {env : List (String × Rendered)}
    {p : Generic.Pattern F} {v b : Generic.Expr F} {s : Rendered} {locals : Environment F Nat}
    {h : Heap F} {res : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (hr : readLet rd env p v b = some s) (henv : EnvReads t h env locals)
    (ob : ObsExpr W [] locals (.letValue p v b) h res h' cs) :
    Heap.Extends h h' ∧ Reads t h' s res := by
  cases p with
  | bind x =>
    cases hv : rd env v with
    | none => simp [readLet, hv] at hr
    | some r =>
      simp only [readLet, hv] at hr
      obtain ⟨vin, mid, bs, c1, c2, dv, mt, db, -⟩ := ob.letValue_inv
      obtain ⟨x1, rv⟩ := hrd hv henv dv
      have hbs := matchPattern_bind_inv mt
      subst hbs
      have db' : ObsExpr W [] ((x, vin) :: locals) b mid res h' c2 := db
      obtain ⟨x2, rb⟩ := hrd hr ((henv.mono x1).cons rv) db'
      exact ⟨x1.trans x2, rb⟩
  | _ => simp [readLet] at hr

theorem readStore_sound (htwf : t.wf = true) (hrd : SoundReader t rd)
    {env : List (String × Rendered)} {inner : Generic.Expr F} {s : Rendered}
    {locals : Environment F Nat} {h : Heap F} {res : SourceValue F} {h' : Heap F}
    {cs : List (Call F)}
    (hr : readStore rd env inner = some s) (henv : EnvReads t h env locals)
    (ob : ObsExpr W [] locals (.store inner) h res h' cs) :
    Heap.Extends h h' ∧ Reads t h' s res := by
  cases inner with
  | construct name targs ctor args =>
    cases hi : nodeInstance name targs with
    | none => simp [readStore, hi] at hr
    | some iname =>
      cases ha : readArgs (rd env) args with
      | none => simp [readStore, hi, ha] at hr
      | some rs =>
        simp only [readStore, hi, ha] at hr
        obtain ⟨vin, mid, dc, hres, hh'⟩ := ob.store_inv
        obtain ⟨vs, oa, hvin⟩ := dc.construct_inv
        rw [nodeInstance_sound hi] at hvin
        subst hvin
        obtain ⟨x1, rvs⟩ := readArgs_sound hrd ha henv oa
        have x2 : Heap.Extends mid h' := ext_of_snoc hh'
        have cell := cell_of_snoc hh'
        simp only [Value.type] at hres
        subst hres
        exact ⟨x1.trans x2, readNode_sound htwf hr cell (readsAll_mono x2 rvs)⟩
  | _ => simp [readStore] at hr

theorem readStep_sound (htwf : t.wf = true) (hrd : SoundReader t rd) :
    SoundReader t (readStep rd) := by
  intro env e s locals h res h' cs hr henv ob
  cases e with
  | var x =>
    have hr' : lookupR x env = some s := hr
    obtain ⟨v, hf, rv⟩ := henv x s hr'
    obtain ⟨hl, hh, -⟩ := ob.var_inv
    rw [hf] at hl
    cases hl
    subst hh
    exact ⟨Heap.Extends.refl _, rv⟩
  | literal i =>
    have hr' : some (Rendered.num i) = some s := hr
    cases hr'
    obtain ⟨hres, hh, -⟩ := ob.literal_inv
    subst hres
    subst hh
    exact ⟨Heap.Extends.refl _, .num⟩
  | letValue p v b => exact readLet_sound hrd hr henv ob
  | call fname targs args =>
    cases ha : readArgs (rd env) args with
    | none => simp [readStep, ha] at hr
    | some rs =>
      simp only [readStep, ha] at hr
      obtain ⟨vs, mid, c1, c2, oa, ev, -⟩ := ob.call_inv
      obtain ⟨x1, rvs⟩ := readArgs_sound hrd ha henv oa
      obtain ⟨x2, rr⟩ := readCall_sound hr rvs ev
      exact ⟨x1.trans x2, rr⟩
  | store inner => exact readStore_sound htwf hrd hr henv ob
  | _ => simp [readStep] at hr

end Sound

/-- **The reader is sound at every depth.** -/
theorem readExpr_sound {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) :
    ∀ n : Nat, SoundReader t (readExpr n)
  | 0 => by
    intro hr henv ob
    cases hr
  | n + 1 => readStep_sound htwf (readExpr_sound htwf n)

/-! ## An arm that reads as a specified term -/

/-- The depth the arms are read to. -/
def readDepth : Nat := 4096

/-- **The arm at a key reads as a closed term that is `T₀` up to its binders' data**, its pointer
leading with at least `sp` `Forall` cells. -/
def armReadsAs (arms : List (Generic.Pattern F × Generic.Expr F)) (key : Nat) (T₀ : KExpr)
    (sp : Nat) : Bool :=
  match litArmBody key arms with
  | none => false
  | some e =>
    match readExpr readDepth [("tbl", .table)] e with
    | some (.tm T sp') => closedBelow 0 T && decide (T.erasePw = T₀.erasePw) && decide (sp ≤ sp')
    | _ => false

theorem forallSpine_of_le {h : Heap F} {m : Nat} {v : SourceValue F}
    (hs : OpOpen.ForallSpine h m v) : ∀ {n : Nat}, n ≤ m → OpOpen.ForallSpine h n v := by
  induction hs with
  | zero e =>
    intro n hle
    have h0 : n = 0 := Nat.le_zero.mp hle
    subst h0
    exact .zero e
  | succ ld rest ih =>
    intro n hle
    cases n with
    | zero => exact .zero _
    | succ n' => exact .succ ld (ih (Nat.le_of_succ_le_succ hle))

/-- **The selected arm of a rendered `match` returns the specified term.** When the arm at the
key reads as `T₀` up to binder data, the observed evaluation of the arm the `match` selects at
that key extends the heap and returns a pointer that represents, exactly and under the table's
keying, a term that is `T₀` up to its binders' data, along `sp` leading `Forall` cells, and
that reaches no `Let` and no `Proj` cell. -/
theorem renders_of_armReadsAs {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {key : F} {T₀ : KExpr} {sp : Nat}
    (hread : armReadsAs arms (ZMod.val key) T₀ sp = true)
    {x_tbl : SourceValue F} {locals : Environment F Nat}
    (hloc : List.find? (fun p => p.1 == "tbl") locals = some ("tbl", x_tbl))
    {h : Heap F} {res : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    {bs : Environment F Nat} {body : Generic.Expr F}
    (htbl : TableRep t h x_tbl)
    (sel : selectArm W [] h (.field key) arms = Except.ok (some (bs, body)))
    (dArm : ObsExpr W [] (bs ++ locals) body h res h' cs) :
    Heap.Extends h h' ∧ RendersUpToBinderData t h' T₀ res ∧ OpOpen.ForallSpine h' sp res ∧
      LetProjFree h' res := by
  unfold armReadsAs at hread
  cases hb : litArmBody (ZMod.val key) arms with
  | none => simp [hb] at hread
  | some e =>
    cases hre : readExpr readDepth [("tbl", .table)] e with
    | none => simp [hb, hre] at hread
    | some s =>
      cases s with
      | tm T sp' =>
        simp only [hb, hre, Bool.and_eq_true, decide_eq_true_eq] at hread
        obtain ⟨⟨hcl, her⟩, hsp⟩ := hread
        obtain ⟨hbs, hbody⟩ := selectArm_litArmBody hb sel
        subst hbs
        rw [hbody] at dArm
        have henv : EnvReads t h [("tbl", .table)] locals := by
          intro x r hx
          have hx' : (if "tbl" = x then some Rendered.table else none) = some r := hx
          by_cases hxt : "tbl" = x
          · rw [ite_eq_left hxt] at hx'
            cases hx'
            subst hxt
            exact ⟨x_tbl, hloc, .table htbl⟩
          · rw [ite_eq_right hxt] at hx'
            cases hx'
        have dArm' : ObsExpr W [] locals e h res h' cs := dArm
        obtain ⟨x1, rd⟩ := readExpr_sound htwf readDepth hre henv dArm'
        cases rd with
        | tm rep spine _ plain =>
          have hT : Decl.TmCExact (keyOf t) h' T res := fun d Γ => rep d Γ 0 hcl
          exact ⟨x1, Exists.intro T ⟨hT, her⟩, forallSpine_of_le spine hsp, plain⟩
      | _ => simp [hb, hre] at hread

/-- Erasing binder data keeps the constants a term names. -/
theorem constsResolveBy_erasePw (P : KKey → Bool) (e : KExpr) :
    e.erasePw.constsResolveBy P = e.constsResolveBy P := by
  induction e <;> simp_all [Ix.Kernel.Expr.erasePw, Ix.Kernel.Expr.constsResolveBy]

/-- **The cells of the selected arm's term are the addresses of the roles `T₀` names.** Under
the premises of `renders_of_armReadsAs`: every cell of the returned term is the address the
table binds a role to, and that role's key is one `T₀` names (every predicate all of `T₀`'s
constants satisfy holds of it). -/
theorem cells_of_armReadsAs {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {key : F} {T₀ : KExpr} {sp : Nat}
    (hread : armReadsAs arms (ZMod.val key) T₀ sp = true)
    {x_tbl : SourceValue F} {locals : Environment F Nat}
    (hloc : List.find? (fun p => p.1 == "tbl") locals = some ("tbl", x_tbl))
    {h : Heap F} {res : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    {bs : Environment F Nat} {body : Generic.Expr F}
    (htbl : TableRep t h x_tbl)
    (sel : selectArm W [] h (.field key) arms = Except.ok (some (bs, body)))
    (dArm : ObsExpr W [] (bs ++ locals) body h res h' cs) :
    ∀ x, AddrIn h' res x → ∃ r, t.addressOf? r = some (ixAddr x) ∧
      ∀ P, T₀.constsResolveBy P = true → P (Ix.Kernel.Key.role r) = true := by
  unfold armReadsAs at hread
  cases hb : litArmBody (ZMod.val key) arms with
  | none => simp [hb] at hread
  | some e =>
    cases hre : readExpr readDepth [("tbl", .table)] e with
    | none => simp [hb, hre] at hread
    | some s =>
      cases s with
      | tm T sp' =>
        simp only [hb, hre, Bool.and_eq_true, decide_eq_true_eq] at hread
        obtain ⟨⟨hcl, her⟩, hsp⟩ := hread
        obtain ⟨hbs, hbody⟩ := selectArm_litArmBody hb sel
        subst hbs
        rw [hbody] at dArm
        have henv : EnvReads t h [("tbl", .table)] locals := by
          intro x r hx
          have hx' : (if "tbl" = x then some Rendered.table else none) = some r := hx
          by_cases hxt : "tbl" = x
          · rw [ite_eq_left hxt] at hx'
            cases hx'
            subst hxt
            exact ⟨x_tbl, hloc, .table htbl⟩
          · rw [ite_eq_right hxt] at hx'
            cases hx'
        have dArm' : ObsExpr W [] locals e h res h' cs := dArm
        obtain ⟨-, rd⟩ := readExpr_sound htwf readDepth hre henv dArm'
        cases rd with
        | tm rep spine cells _ =>
          intro x hin
          obtain ⟨r, hr, hP⟩ := cells h' (Heap.Extends.refl _) x hin
          refine ⟨r, hr, fun P hp => hP P ?_⟩
          rw [← constsResolveBy_erasePw P T, her, constsResolveBy_erasePw]
          exact hp
      | _ => simp [hb, hre] at hread

end IxVM.Refinement.Binding
