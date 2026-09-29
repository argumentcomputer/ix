import Compilatrix.Lir.Semantics

/-!
# Operand metadata

The register operands of each statement and terminator, for the allocator
and its validator (05 §2, §5). The lists are built from `Stmt.uses` and
`Stmt.defs`, the registers `Stmt.exec` reads and writes, and the frame
lemmas below prove that those are all it reads and writes. That closes
regalloc2's gap 6 (trusted operand descriptions) at Lir.

At Lir every use is early, every definition late, and every constraint
`any`, except the operands the internal convention fixes (05 §6): call and
tail-call arguments (`rdi rsi rdx rcx r8 r9 r10`, then outgoing stack
slots) and call and return results (`rax rdx`, then stack). Immediate
arguments have no register operand. Edge arguments are not operands: they
are block-parameter bindings, which the validator checks as a parallel move.
-/

namespace Compilatrix.Lir

inductive Kind where
  | use
  /-- A definition (`def` is a keyword). -/
  | define
  deriving DecidableEq, Repr, Inhabited

inductive Pos where
  | early
  | late
  deriving DecidableEq, Repr, Inhabited

inductive Con where
  | any
  | reg
  | stack
  | fixed (r : X86.GPR)
  | reuse (i : Nat)
  deriving DecidableEq, Repr, Inhabited

structure Operand (ρ : Type) where
  v : ρ
  kind : Kind
  pos : Pos
  con : Con
  deriving DecidableEq, Repr, Inhabited

namespace Conv

/-- Internal-convention argument registers (05 §6). -/
def argRegs : List X86.GPR := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10]

/-- Internal-convention result registers. -/
def resultRegs : List X86.GPR := [.rax, .rdx]

def argCon (i : Nat) : Con := match argRegs[i]? with | some r => .fixed r | none => .stack

def resultCon (i : Nat) : Con := match resultRegs[i]? with | some r => .fixed r | none => .stack

end Conv

def useOp (con : Con) (x : VReg) : Operand VReg := ⟨x, .use, .early, con⟩

def defOp (con : Con) (x : VReg) : Operand VReg := ⟨x, .define, .late, con⟩

/-- Positional uses: the `i`-th argument has constraint `con i`. -/
def positionalUses (con : Nat → Con) : Nat → List Arg → List (Operand VReg)
  | _, [] => []
  | i, .v x :: as => useOp (con i) x :: positionalUses con (i + 1) as
  | i, .imm _ :: as => positionalUses con (i + 1) as

/-- Positional definitions: the `i`-th result has constraint `con i`. -/
def positionalDefs (con : Nat → Con) : Nat → List VReg → List (Operand VReg)
  | _, [] => []
  | i, x :: xs => defOp (con i) x :: positionalDefs con (i + 1) xs

def Stmt.operands : Stmt → List (Operand VReg)
  | .assign x r => r.uses.map (useOp .any) ++ [defOp .any x]
  | .store _ m a => (m.uses ++ a.uses).map (useOp .any)
  | .call rs _ as => positionalUses Conv.argCon 0 as ++ positionalDefs Conv.resultCon 0 rs

/-- Terminator operands; edge arguments excluded. -/
def Term.operands : Term → List (Operand VReg)
  | .jump _ => []
  | .br _ _ a b _ _ => (a.uses ++ b.uses).map (useOp .any)
  | .brOvf _ x a b _ _ => (a.uses ++ b.uses).map (useOp .any) ++ [defOp .any x]
  | .ret as => positionalUses Conv.resultCon 0 as
  | .tail _ as => positionalUses Conv.argCon 0 as
  | .fail _ | .trap => []

def operandUses (os : List (Operand VReg)) : List VReg :=
  (os.filter (·.kind == .use)).map (·.v)

def operandDefs (os : List (Operand VReg)) : List VReg :=
  (os.filter (·.kind == .define)).map (·.v)

/-! ## The operands are the semantics' reads and writes -/

@[simp] private theorem use_beq_use : (Kind.use == Kind.use) = true := rfl
@[simp] private theorem use_beq_define : (Kind.use == Kind.define) = false := rfl
@[simp] private theorem define_beq_use : (Kind.define == Kind.use) = false := rfl
@[simp] private theorem define_beq_define : (Kind.define == Kind.define) = true := rfl

private theorem operandUses_append (xs ys : List (Operand VReg)) :
    operandUses (xs ++ ys) = operandUses xs ++ operandUses ys := by
  simp [operandUses]

private theorem operandDefs_append (xs ys : List (Operand VReg)) :
    operandDefs (xs ++ ys) = operandDefs xs ++ operandDefs ys := by
  simp [operandDefs]

private theorem positionalUses_uses (con : Nat → Con) (i : Nat) (as : List Arg) :
    operandUses (positionalUses con i as) = argsUses as := by
  induction as generalizing i with
  | nil => rfl
  | cons a as ih =>
      cases a <;> simp [positionalUses, operandUses, argsUses, Arg.uses, Arg.vreg?, useOp] at ih ⊢ <;>
        exact ih (i + 1)

private theorem positionalUses_defs (con : Nat → Con) (i : Nat) (as : List Arg) :
    operandDefs (positionalUses con i as) = [] := by
  induction as generalizing i with
  | nil => rfl
  | cons a as ih =>
      cases a <;> simp [positionalUses, operandDefs, useOp] at ih ⊢ <;> exact ih (i + 1)

private theorem positionalDefs_uses (con : Nat → Con) (i : Nat) (xs : List VReg) :
    operandUses (positionalDefs con i xs) = [] := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [positionalDefs, operandUses, defOp] at ih ⊢; exact ih (i + 1)

private theorem positionalDefs_defs (con : Nat → Con) (i : Nat) (xs : List VReg) :
    operandDefs (positionalDefs con i xs) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [positionalDefs, operandDefs, defOp] at ih ⊢; exact ih (i + 1)

private theorem map_useOp_uses (con : Con) (xs : List VReg) :
    operandUses (xs.map (useOp con)) = xs := by
  simp [operandUses, useOp, List.filter_map, Function.comp_def]

private theorem map_useOp_defs (con : Con) (xs : List VReg) :
    operandDefs (xs.map (useOp con)) = [] := by
  simp [operandDefs, useOp, List.filter_map, Function.comp_def]

@[simp] theorem Stmt.operandUses_eq (s : Stmt) : operandUses s.operands = s.uses := by
  cases s with
  | assign x r => simp [Stmt.operands, Stmt.uses, operandUses, useOp, defOp, List.filter_map,
      Function.comp_def]
  | store w m a => exact map_useOp_uses _ _
  | call rs f as =>
      simp only [Stmt.operands, Stmt.uses, operandUses, List.filter_append, List.map_append]
      have h1 := positionalUses_uses Conv.argCon 0 as
      have h2 := positionalDefs_uses Conv.resultCon 0 rs
      simp only [operandUses] at h1 h2
      rw [h1, h2, List.append_nil]

@[simp] theorem Stmt.operandDefs_eq (s : Stmt) : operandDefs s.operands = s.defs := by
  cases s with
  | assign x r => simp [Stmt.operands, Stmt.defs, operandDefs, useOp, defOp, List.filter_map,
      Function.comp_def]
  | store w m a => exact map_useOp_defs _ _
  | call rs f as =>
      simp only [Stmt.operands, Stmt.defs, operandDefs, List.filter_append, List.map_append]
      have h1 := positionalUses_defs Conv.argCon 0 as
      have h2 := positionalDefs_defs Conv.resultCon 0 rs
      simp only [operandDefs] at h1 h2
      rw [h1, h2, List.nil_append]

@[simp] theorem Term.operandUses_eq (t : Term) : operandUses t.operands = t.uses := by
  cases t with
  | jump e => rfl
  | br c w a b t f => exact map_useOp_uses _ _
  | brOvf o x a b ok ovf =>
      rw [Term.operands, operandUses_append, map_useOp_uses]
      simp [Term.uses, operandUses, defOp]
  | ret as => exact positionalUses_uses _ _ _
  | tail f as => exact positionalUses_uses _ _ _
  | fail r => rfl
  | trap => rfl

@[simp] theorem Term.operandDefs_eq (t : Term) : operandDefs t.operands = t.defs := by
  cases t with
  | jump e => rfl
  | br c w a b t f => exact map_useOp_defs _ _
  | brOvf o x a b ok ovf =>
      rw [Term.operands, operandDefs_append, map_useOp_defs]
      simp [Term.defs, operandDefs, defOp]
  | ret as => exact positionalUses_defs _ _ _
  | tail f as => exact positionalUses_defs _ _ _
  | fail r => rfl
  | trap => rfl

/-! ## Frame lemmas -/

/-- Two environments agree on the registers `xs`. -/
def Agree (xs : List VReg) (ρ ρ' : Env) : Prop := ∀ x ∈ xs, ρ[x]? = ρ'[x]?

theorem Agree.append_left {xs ys : List VReg} {ρ ρ' : Env} (h : Agree (xs ++ ys) ρ ρ') :
    Agree xs ρ ρ' := fun x hx => h x (List.mem_append_left _ hx)

theorem Agree.append_right {xs ys : List VReg} {ρ ρ' : Env} (h : Agree (xs ++ ys) ρ ρ') :
    Agree ys ρ ρ' := fun x hx => h x (List.mem_append_right _ hx)

theorem Arg.eval_congr {a : Arg} {ρ ρ' : Env} (h : Agree a.uses ρ ρ') : a.eval ρ = a.eval ρ' := by
  cases a with
  | v x => exact h x (by simp [Arg.uses, Arg.vreg?])
  | imm w => rfl

theorem evalArgs_congr {as : List Arg} {ρ ρ' : Env} (h : Agree (argsUses as) ρ ρ') :
    evalArgs ρ as = evalArgs ρ' as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      have h' : Agree (a.uses ++ argsUses as) ρ ρ' := by simpa [argsUses] using h
      simp only [evalArgs, List.mapM_cons] at ih ⊢
      rw [Arg.eval_congr h'.append_left, ih h'.append_right]

theorem Addr.eval_congr {m : Addr} {ρ ρ' : Env} (ctx : Word) (h : Agree m.uses ρ ρ') :
    m.eval ρ ctx = m.eval ρ' ctx := by
  rcases m with ⟨base, index, disp⟩
  rcases base with _ | (x | _) <;> rcases index with _ | ⟨y, s⟩ <;>
    simp_all [Addr.eval, Addr.uses, Base.uses, Agree]

theorem Rhs.eval_congr {r : Rhs} {ρ ρ' : Env} (mem : X86.Memory) (ctx : Word)
    (h : Agree r.uses ρ ρ') : r.eval ρ mem ctx = r.eval ρ' mem ctx := by
  cases r with
  | arg a => exact Arg.eval_congr h
  | bin o w a b =>
      simp only [Rhs.eval]
      rw [Arg.eval_congr h.append_left, Arg.eval_congr h.append_right]
  | load w e m => simp only [Rhs.eval]; rw [Addr.eval_congr ctx h]
  | addr m => exact Addr.eval_congr ctx h
  | select c w a b t f =>
      have h' : Agree (((a.uses ++ b.uses) ++ t.uses) ++ f.uses) ρ ρ' := h
      simp only [Rhs.eval]
      rw [Arg.eval_congr h'.append_left.append_left.append_left,
        Arg.eval_congr h'.append_left.append_left.append_right,
        Arg.eval_congr h'.append_left.append_right, Arg.eval_congr h'.append_right]
  | test c w a b =>
      simp only [Rhs.eval]
      rw [Arg.eval_congr h.append_left, Arg.eval_congr h.append_right]

/-- The frame lemma of 05 §2 for local statements: a statement's result
depends only on its uses, and it changes only its definitions. -/
theorem Stmt.exec_frame {s : Stmt} {ρ ρ' ρ₁ : Env} {mem mem₁ : X86.Memory} {ctx : Word}
    (agree : Agree s.uses ρ ρ') (h : s.exec ρ mem ctx = some (ρ₁, mem₁)) :
    ∃ ρ₁', s.exec ρ' mem ctx = some (ρ₁', mem₁) ∧
      (∀ x, x ∉ s.defs → ρ₁[x]? = ρ[x]? ∧ ρ₁'[x]? = ρ'[x]?) ∧
      (∀ x ∈ s.defs, ρ₁[x]? = ρ₁'[x]?) := by
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨v, hv, hρ, hm⟩ := h
      subst hρ hm
      refine ⟨ρ'.insert x v, ?_, ?_, ?_⟩
      · simp only [Stmt.exec, Option.bind_eq_bind]
        rw [← Rhs.eval_congr mem ctx agree, hv]
        rfl
      · intro y hy
        have ne : (x == y) = false := by
          simp only [Stmt.defs, List.mem_singleton] at hy
          simpa [beq_iff_eq] using fun e => hy e.symm
        simp [Std.HashMap.getElem?_insert, ne]
      · intro y hy
        simp only [Stmt.defs, List.mem_singleton] at hy
        subst hy
        simp
  | store w m a =>
      have ha := Addr.eval_congr ctx agree.append_left
      have hv := Arg.eval_congr agree.append_right
      refine ⟨ρ', ?_, fun y _ => ?_, fun y hy => by simp [Stmt.defs] at hy⟩
      · simp only [Stmt.exec] at h ⊢
        rw [← ha, ← hv]
        revert h
        cases m.eval ρ ctx <;> cases a.eval ρ <;> simp only [Option.bind_none, Option.bind_some,
          reduceCtorEq, imp_self, Option.bind_eq_bind]
        rename_i address v
        cases mem.write? w address v <;> simp
      · simp only [Stmt.exec] at h
        revert h
        cases m.eval ρ ctx <;> cases a.eval ρ <;> simp only [Option.bind_none, Option.bind_some,
          reduceCtorEq, false_implies, Option.bind_eq_bind]
        rename_i address v
        cases mem.write? w address v <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq,
          false_implies]
        rintro ⟨rfl, -⟩
        simp
  | call rs f as => simp [Stmt.exec] at h

end Compilatrix.Lir
