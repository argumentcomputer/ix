/-! # Self-Contained Fir IR and Operational Semantics

Port of IxCC's first-order intermediate representation (`Fir`) and clocked
big-step evaluator (`Fir.eval`, `Fir.run`), including:
- Persistent binary-trie maps (`NatMap`) with verified lookup/update laws.
- Full constructor keys (`CtorKey.src` and `CtorKey.clo` closures) and global
  keys (`GKey`, `ArgKey`) with structural `DecidableEq`.
- Full literals (`Lit.nat` and `Lit.str`), all 16 `Nat` primitives (`Prim`),
  and all 7 `Code` forms (`bind`, `jp`, `jmp`, `case`, `ret`, `tcall`, `trap`).
- Bind-form unfolding equations and clock monotonicity (`eval_mono`, `run_mono`).

Zero `sorry`, zero external dependencies beyond Lean's core library. -/

namespace Ix.Cert.IxccAiur.Fir

/-! ## Persistent `Nat`-keyed Map -/

/-- Binary trie on the key's bits (low bit first); key 0 sits at the root. -/
inductive NatMap (α : Type) where
  | leaf
  | node (value : Option α) (zero one : NatMap α)
  deriving BEq, DecidableEq, Inhabited, Repr

namespace NatMap

variable {α β : Type}

def empty : NatMap α := .leaf

def parts : NatMap α → Option α × NatMap α × NatMap α
  | .leaf => (none, .leaf, .leaf)
  | .node v z o => (v, z, o)

def get? : NatMap α → Nat → Option α
  | .leaf, _ => none
  | .node v z o, k =>
    if k == 0 then v
    else if k % 2 == 0 then get? z (k / 2)
    else get? o (k / 2)

def setF : Nat → NatMap α → Nat → Option α → NatMap α
  | 0, m, _, x => let (_, z, o) := parts m; .node x z o
  | fuel + 1, m, k, x =>
    let (v, z, o) := parts m
    if k == 0 then .node x z o
    else if k % 2 == 0 then .node v (setF fuel z (k / 2) x) o
    else .node v z (setF fuel o (k / 2) x)

def insert (m : NatMap α) (k : Nat) (x : α) : NatMap α :=
  setF (k + 1) m k (some x)

def erase (m : NatMap α) (k : Nat) : NatMap α :=
  setF (k + 1) m k none

def getD (m : NatMap α) (k : Nat) (d : α) : α :=
  (m.get? k).getD d

def contains (m : NatMap α) (k : Nat) : Bool :=
  (m.get? k).isSome

def ofList (xs : List (Nat × α)) : NatMap α :=
  xs.foldl (fun m (k, x) => m.insert k x) .leaf

theorem get?_leaf (k : Nat) : (NatMap.leaf : NatMap α).get? k = none := rfl

theorem get?_parts_zero (m : NatMap α) : (parts m).1 = m.get? 0 := by
  cases m <;> rfl

theorem get?_parts_even (m : NatMap α) {k : Nat} (hk0 : k ≠ 0) (he : k % 2 = 0) :
    (parts m).2.1.get? (k / 2) = m.get? k := by
  cases m with
  | leaf => rfl
  | node v z o => simp [parts, get?, hk0, he]

theorem get?_parts_odd (m : NatMap α) {k : Nat} (hk0 : k ≠ 0) (ho : k % 2 ≠ 0) :
    (parts m).2.2.get? (k / 2) = m.get? k := by
  cases m with
  | leaf => rfl
  | node v z o => simp [parts, get?, hk0, ho]

theorem get?_setF_self :
    ∀ (fuel : Nat) (m : NatMap α) (k : Nat) (x : Option α),
      k ≤ fuel → (setF fuel m k x).get? k = x
  | 0, m, k, x, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp [setF, get?]
  | fuel + 1, m, k, x, hk => by
    unfold setF
    by_cases hk0 : k = 0
    · subst hk0; simp [get?]
    · by_cases he : k % 2 = 0
      · simp only [hk0, beq_iff_eq, ↓reduceIte, he]
        unfold get?
        simp only [hk0, beq_iff_eq, ↓reduceIte, he]
        exact get?_setF_self fuel (parts m).2.1 (k / 2) x (by omega)
      · simp only [hk0, beq_iff_eq, ↓reduceIte, he]
        unfold get?
        simp only [hk0, beq_iff_eq, ↓reduceIte, he]
        exact get?_setF_self fuel (parts m).2.2 (k / 2) x (by omega)

theorem get?_node (v : Option α) (z o : NatMap α) (k : Nat) :
    (NatMap.node v z o).get? k =
      if k == 0 then v else if k % 2 == 0 then z.get? (k / 2) else o.get? (k / 2) := rfl

theorem get?_setF_ne :
    ∀ (fuel : Nat) (m : NatMap α) (k k' : Nat) (x : Option α),
      k ≤ fuel → k ≠ k' → (setF fuel m k x).get? k' = m.get? k'
  | 0, m, k, k', x, hk, hne => by
    have hk0 : k = 0 := by omega
    have hk'0 : k' ≠ 0 := by omega
    simp only [setF, get?_node, hk'0, beq_iff_eq, ↓reduceIte]
    by_cases he : k' % 2 = 0
    · simp only [he, ↓reduceIte]
      exact get?_parts_even m hk'0 he
    · simp only [he, ↓reduceIte]
      exact get?_parts_odd m hk'0 he
  | fuel + 1, m, k, k', x, hk, hne => by
    unfold setF
    by_cases hk0 : k = 0
    · subst hk0
      have hk'0 : k' ≠ 0 := Ne.symm hne
      simp only [beq_self_eq_true, ↓reduceIte, get?_node, hk'0, beq_iff_eq]
      by_cases he : k' % 2 = 0
      · simp only [he, ↓reduceIte]
        exact get?_parts_even m hk'0 he
      · simp only [he, ↓reduceIte]
        exact get?_parts_odd m hk'0 he
    · by_cases he : k % 2 = 0
      · simp only [hk0, beq_iff_eq, ↓reduceIte, he, get?_node]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp only [↓reduceIte]; exact get?_parts_zero m
        · simp only [hk'0, ↓reduceIte]
          by_cases he' : k' % 2 = 0
          · simp only [he', ↓reduceIte]
            rw [get?_setF_ne fuel (parts m).2.1 (k / 2) (k' / 2) x (by omega) (by omega)]
            exact get?_parts_even m hk'0 he'
          · simp only [he', ↓reduceIte]
            exact get?_parts_odd m hk'0 he'
      · simp only [hk0, beq_iff_eq, ↓reduceIte, he, get?_node]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp only [↓reduceIte]; exact get?_parts_zero m
        · simp only [hk'0, ↓reduceIte]
          by_cases he' : k' % 2 = 0
          · simp only [he', ↓reduceIte]
            exact get?_parts_even m hk'0 he'
          · simp only [he', ↓reduceIte]
            rw [get?_setF_ne fuel (parts m).2.2 (k / 2) (k' / 2) x (by omega) (by omega)]
            exact get?_parts_odd m hk'0 he'

theorem get?_insert_self (m : NatMap α) (k : Nat) (x : α) :
    (m.insert k x).get? k = some x :=
  get?_setF_self (k + 1) m k (some x) (by omega)

theorem get?_insert_ne (m : NatMap α) {k k' : Nat} (x : α) (hne : k ≠ k') :
    (m.insert k x).get? k' = m.get? k' :=
  get?_setF_ne (k + 1) m k k' (some x) (by omega) hne

theorem get?_insert (m : NatMap α) (k k' : Nat) (x : α) :
    (m.insert k x).get? k' = if k = k' then some x else m.get? k' := by
  by_cases h : k = k'
  · subst h; simp [get?_insert_self]
  · simp [h, get?_insert_ne m x h]

end NatMap

/-! ## Primitives, Keys, and Literals -/

abbrev CId := Nat
abbrev Profile := List Bool

/-- Exact result of a `Nat` primitive. -/
inductive PrimResult where
  | nat (n : Nat)
  | bool (b : Bool)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- All 16 `Nat` primitives of IxCC's `Lam`/`Fir`. -/
inductive Prim where
  | natAdd | natSub | natMul | natDiv | natMod | natPow | natGcd | natBeq | natBle
  | natLand | natLor | natXor | natShl | natShr | natPred
  | natBlt
  deriving DecidableEq, Repr, Inhabited

namespace Prim

def arity : Prim → Nat
  | .natPred => 1
  | _ => 2

def name : Prim → String
  | .natAdd => "natAdd" | .natSub => "natSub" | .natMul => "natMul" | .natDiv => "natDiv"
  | .natMod => "natMod" | .natPow => "natPow" | .natGcd => "natGcd" | .natBeq => "natBeq"
  | .natBle => "natBle" | .natLand => "natLand" | .natLor => "natLor" | .natXor => "natXor"
  | .natShl => "natShl" | .natShr => "natShr" | .natPred => "natPred" | .natBlt => "natBlt"

/-- Exact mathematical semantics of primitives on natural numbers. -/
def sem : Prim → List Nat → Option PrimResult
  | .natAdd, [a, b] => some (.nat (a + b))
  | .natSub, [a, b] => some (.nat (a - b))
  | .natMul, [a, b] => some (.nat (a * b))
  | .natDiv, [a, b] => some (.nat (if b == 0 then 0 else a / b))
  | .natMod, [a, b] => some (.nat (if b == 0 then a else a % b))
  | .natPow, [a, b] => some (.nat (a ^ b))
  | .natGcd, [a, b] => some (.nat (Nat.gcd a b))
  | .natBeq, [a, b] => some (.bool (a == b))
  | .natBle, [a, b] => some (.bool (decide (a ≤ b)))
  | .natBlt, [a, b] => some (.bool (decide (a < b)))
  | .natLand, [a, b] => some (.nat (a &&& b))
  | .natLor, [a, b] => some (.nat (a ||| b))
  | .natXor, [a, b] => some (.nat (a ^^^ b))
  | .natShl, [a, b] => some (.nat (a * 2 ^ b))
  | .natShr, [a, b] => some (.nat (if a.log2 < b then 0 else a / 2 ^ b))
  | .natPred, [a] => some (.nat (a - 1))
  | _, _ => none

end Prim

/-- Special heads for `GKey.wrapper`. -/
inductive Head where
  | ctor (c : CId)
  | quotMk (c : CId)
  | quotLift (c : CId)
  | recr (r : CId)
  | cases (c : CId)
  | prim (op : Prim)
  deriving BEq, DecidableEq, Repr, Inhabited

mutual

/-- Constructor identity: either a source constructor or a closure shape. -/
inductive CtorKey where
  | src (c : CId)
  | clo (f : GKey) (supplied : Nat)

/-- Global function identity. -/
inductive GKey where
  | const (c : CId) (prof : Profile)
  | byName (c : CId) (prof : Profile)
  | recStar (r : CId) (prof : Profile)
  | wrapper (h : Head) (prof : Profile)
  | spec (g : GKey) (args : List ArgKey)
  | worker (g : GKey) (keep : List Bool)
  | lam (g : GKey) (path : List Nat)
  | dispatch (arity : Nat)

/-- Specialisation argument key. -/
inductive ArgKey where
  | glob (g : GKey)
  | con (c : CtorKey) (args : List ArgKey)
  | lit (n : Nat)
  | hole (i : Nat)

end

deriving instance Repr for CtorKey, GKey, ArgKey

instance : Inhabited CtorKey := ⟨.src 0⟩
instance : Inhabited GKey := ⟨.dispatch 0⟩

mutual

def CtorKey.decEq : (a b : CtorKey) → Decidable (a = b)
  | .src c, .src d =>
    if h : c = d then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .clo f n, .clo g m =>
    match GKey.decEq f g with
    | isTrue hf =>
      if hn : n = m then isTrue (hf ▸ hn ▸ rfl) else isFalse (fun e => by cases e; exact hn rfl)
    | isFalse hf => isFalse (fun e => by cases e; exact hf rfl)
  | .src _, .clo .. | .clo .., .src _ => isFalse (fun e => by cases e)
  termination_by structural a => a

def GKey.decEq : (a b : GKey) → Decidable (a = b)
  | .const c p, .const d q | .byName c p, .byName d q | .recStar c p, .recStar d q =>
    if h : c = d ∧ p = q then isTrue (h.1 ▸ h.2 ▸ rfl)
    else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | .wrapper c p, .wrapper d q =>
    if h : c = d ∧ p = q then isTrue (h.1 ▸ h.2 ▸ rfl)
    else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | .spec f xs, .spec g ys =>
    match GKey.decEq f g, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | .worker f xs, .worker g ys =>
    match GKey.decEq f g with
    | isTrue h1 =>
      if h2 : xs = ys then isTrue (h1 ▸ h2 ▸ rfl) else isFalse (fun e => by cases e; exact h2 rfl)
    | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
  | .lam f xs, .lam g ys =>
    match GKey.decEq f g with
    | isTrue h1 =>
      if h2 : xs = ys then isTrue (h1 ▸ h2 ▸ rfl) else isFalse (fun e => by cases e; exact h2 rfl)
    | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
  | .dispatch n, .dispatch m =>
    if h : n = m then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .const .., .byName .. | .const .., .recStar .. | .const .., .wrapper .. | .const .., .spec ..
  | .const .., .worker .. | .const .., .lam .. | .const .., .dispatch ..
  | .byName .., .const .. | .byName .., .recStar .. | .byName .., .wrapper ..
  | .byName .., .spec .. | .byName .., .worker .. | .byName .., .lam .. | .byName .., .dispatch ..
  | .recStar .., .const .. | .recStar .., .byName .. | .recStar .., .wrapper ..
  | .recStar .., .spec .. | .recStar .., .worker .. | .recStar .., .lam ..
  | .recStar .., .dispatch ..
  | .wrapper .., .const .. | .wrapper .., .byName .. | .wrapper .., .recStar ..
  | .wrapper .., .spec .. | .wrapper .., .worker .. | .wrapper .., .lam ..
  | .wrapper .., .dispatch ..
  | .spec .., .const .. | .spec .., .byName .. | .spec .., .recStar .. | .spec .., .wrapper ..
  | .spec .., .worker .. | .spec .., .lam .. | .spec .., .dispatch ..
  | .worker .., .const .. | .worker .., .byName .. | .worker .., .recStar ..
  | .worker .., .wrapper .. | .worker .., .spec .. | .worker .., .lam ..
  | .worker .., .dispatch ..
  | .lam .., .const .. | .lam .., .byName .. | .lam .., .recStar .. | .lam .., .wrapper ..
  | .lam .., .spec .. | .lam .., .worker .. | .lam .., .dispatch ..
  | .dispatch .., .const .. | .dispatch .., .byName .. | .dispatch .., .recStar ..
  | .dispatch .., .wrapper .. | .dispatch .., .spec .. | .dispatch .., .worker ..
  | .dispatch .., .lam .. => isFalse (fun e => by cases e)
  termination_by structural a => a

def ArgKey.decEq : (a b : ArgKey) → Decidable (a = b)
  | .glob f, .glob g =>
    match GKey.decEq f g with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .con c xs, .con d ys =>
    match CtorKey.decEq c d, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | .lit n, .lit m | .hole n, .hole m =>
    if h : n = m then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .glob _, .con .. | .glob _, .lit _ | .glob _, .hole _
  | .con .., .glob _ | .con .., .lit _ | .con .., .hole _
  | .lit _, .glob _ | .lit _, .con .. | .lit _, .hole _
  | .hole _, .glob _ | .hole _, .con .. | .hole _, .lit _ => isFalse (fun e => by cases e)
  termination_by structural a => a

def ArgKey.decEqList : (a b : List ArgKey) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match ArgKey.decEq x y, ArgKey.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)
  termination_by structural a => a

end

instance : DecidableEq CtorKey := CtorKey.decEq
instance : DecidableEq GKey := GKey.decEq
instance : DecidableEq ArgKey := ArgKey.decEq

/-- Literals: exact natural numbers and UTF-8 strings. -/
inductive Lit where
  | nat (n : Nat)
  | str (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- Ownership field kinds carried by `CtorInfo`. -/
inductive OwnKind where
  | shared
  | unique (dup : Bool)
  | region
  deriving DecidableEq, Repr, Inhabited

/-- A constructor-table row: key, source tag, and kept-field arity. -/
structure CtorTableEntry where
  key : CtorKey
  tag : Nat
  arity : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Pinned constructor keys for `Nat` peeling and `Bool` primitive results. -/
structure Known where
  natZero : Option CtorKey := none
  natSucc : Option CtorKey := none
  boolFalse : Option CtorKey := none
  boolTrue : Option CtorKey := none
  deriving DecidableEq, Repr, Inhabited

/-! ## Fir Syntax -/

abbrev Var := Nat
abbrev FunId := Nat
abbrev JoinId := Nat

structure CtorInfo where
  key : CtorKey
  tag : Nat
  nobj : Nat
  nscalar : Nat := 0
  fieldKinds : List OwnKind := []
  deriving DecidableEq, Repr, Inhabited

namespace CtorInfo

def ofKey (table : List CtorTableEntry) (c : CtorKey) : Option CtorInfo :=
  (table.find? (·.key == c)).map fun r =>
    { key := c, tag := r.tag, nobj := r.arity, fieldKinds := List.replicate r.arity .shared }

def arity (c : CtorInfo) : Nat := c.nobj + c.nscalar

def fieldless (c : CtorInfo) : Bool := c.arity == 0

end CtorInfo

inductive Rep where
  | obj
  | tobj
  | word
  | erased
  deriving DecidableEq, Repr, Inhabited

inductive Arg where
  | var (x : Var)
  | lit (l : Lit)
  | erased
  deriving DecidableEq, Repr, Inhabited

inductive Rhs where
  | arg (a : Arg)
  | ctor (c : CtorInfo) (args : List Arg)
  | proj (x : Var) (c : CtorKey) (i : Nat)
  | prim (op : Prim) (args : List Arg)
  | call (f : FunId) (args : List Arg)
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Code where
  | bind (x : Var) (rhs : Rhs) (k : Code)
  | jp (j : JoinId) (params : List Var) (isRec : Bool) (body k : Code)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List Alt) (dflt : Option Code)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

inductive Alt where
  | mk (key : CtorKey) (body : Code)

end

deriving instance Repr for Code, Alt

instance : Inhabited Code := ⟨.trap⟩

namespace Alt

def key : Alt → CtorKey | .mk k _ => k
def body : Alt → Code | .mk _ b => b

end Alt

structure Fun where
  key : GKey
  params : List (Var × Rep)
  body : Code
  vars : Nat := 0
  joins : Nat := 0
  deriving Inhabited

def Fun.arity (f : Fun) : Nat := f.params.length

structure Program where
  funs : NatMap Fun
  size : Nat
  exports : List FunId
  ctors : List CtorTableEntry
  known : Known
  deriving Inhabited

namespace Program

def fun? (P : Program) (f : FunId) : Option Fun := P.funs.get? f

def funList (P : Program) : List (FunId × Fun) :=
  (List.range P.size).filterMap fun f => (P.fun? f).map (f, ·)

def ctorInfo? (P : Program) (c : CtorKey) : Option CtorInfo :=
  CtorInfo.ofKey P.ctors c

end Program

mutual

def Code.size : Code → Nat
  | .bind _ _ k => k.size + 1
  | .jp _ _ _ b k => b.size + k.size + 1
  | .case _ alts d => Code.altsSize alts + Code.optSize d + 2
  | .jmp .. | .ret _ | .tcall .. | .trap => 1

def Code.altsSize : List Alt → Nat
  | [] => 0
  | .mk _ b :: as => b.size + Code.altsSize as

def Code.optSize : Option Code → Nat
  | none => 0
  | some c => c.size

end

theorem Code.size_pos (c : Code) : 0 < c.size := by
  cases c <;> simp [Code.size]

/-! ## Semantic Vocabulary and Clocked Operational Semantics -/

inductive Resource where
  | heap
  | stack
  | natOverflow
  deriving DecidableEq, Repr, Inhabited

inductive Result (α : Type) where
  | ok (value : α)
  | timeout
  | resource (failure : Resource)
  | trap
  | stuck
  deriving DecidableEq, Repr, Inhabited

namespace Result

@[inline] def bind {α β : Type} : Result α → (α → Result β) → Result β
  | ok value, next => next value
  | timeout, _ => timeout
  | resource failure, _ => resource failure
  | trap, _ => trap
  | stuck, _ => stuck

instance : Monad Result where
  pure := ok
  bind := bind

@[simp] theorem bind_ok {α β : Type} (value : α) (next : α → Result β) :
    bind (ok value) next = next value := rfl

@[inline] def ofOption {α : Type} : Option α → Result α
  | some value => ok value
  | none => stuck

/-- `Agrees r' r`: if `r` is not `timeout`, then `r' = r`. -/
def Agrees {α : Type} (r' r : Result α) : Prop :=
  r ≠ .timeout → r' = r

theorem Agrees.refl {α : Type} (r : Result α) : Agrees r r := fun _ => rfl

theorem Agrees.of_timeout {α : Type} (r' : Result α) : Agrees r' .timeout :=
  fun h => absurd rfl h

theorem Agrees.bind {α β : Type} {r' r : Result α} {f' f : α → Result β}
    (hr : Agrees r' r) (hf : ∀ a, r = .ok a → Agrees (f' a) (f a)) :
    Agrees (r'.bind f') (r.bind f) := by
  cases r with
  | timeout => exact Agrees.of_timeout _
  | ok a =>
    have hEq : r' = .ok a := hr (by intro h; cases h)
    rw [hEq]
    exact hf a rfl
  | resource e =>
    have hEq : r' = .resource e := hr (by intro h; cases h)
    rw [hEq]; exact Agrees.refl _
  | trap =>
    have hEq : r' = .trap := hr (by intro h; cases h)
    rw [hEq]; exact Agrees.refl _
  | stuck =>
    have hEq : r' = .stuck := hr (by intro h; cases h)
    rw [hEq]; exact Agrees.refl _

theorem Agrees.ofOption {α β : Type} (o : Option α) {f' f : α → Result β}
    (h : ∀ a, o = some a → Agrees (f' a) (f a)) :
    Agrees ((Result.ofOption o).bind f') ((Result.ofOption o).bind f) := by
  cases o with
  | none => exact Agrees.refl _
  | some a => exact h a rfl

end Result

/-- Charge one clock unit; return `.timeout` at `0`. -/
def later {α : Type} : Nat → (Nat → Result α) → Result α
  | 0, _ => .timeout
  | k + 1, f => f k

theorem Result.Agrees.later {α : Type} {k k' : Nat} (hk : k ≤ k') {f' f : Nat → Result α}
    (h : ∀ j j', j + 1 = k → j' + 1 = k' → Result.Agrees (f' j') (f j)) :
    Result.Agrees (Fir.later k' f') (Fir.later k f) := by
  cases k with
  | zero => exact Result.Agrees.of_timeout _
  | succ j =>
    obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
    exact h j j' rfl rfl

/-- First-order observations for readback. -/
inductive Obs where
  | nat (value : Nat)
  | word (value : UInt64)
  | ctor (tag : Nat) (fields : List Obs)
  | bytes (data : List UInt8)
  deriving BEq, Repr, Inhabited

/-- Fir runtime values. -/
inductive Val where
  | lit (l : Lit)
  | ctor (c : CtorInfo) (fields : List Val)
  | erased
  deriving Repr, Inhabited

abbrev Env := NatMap Val

namespace Val

/-- View a value as a constructor: `Nat` literals peel with the pinned keys. -/
def asCtor (K : Known) : Val → Option (CtorKey × List Val)
  | .ctor c fs => some (c.key, fs)
  | .lit (.nat 0) => K.natZero.map (·, [])
  | .lit (.nat (n + 1)) => K.natSucc.map (·, [.lit (.nat n)])
  | _ => none

end Val

def Arg.eval (ρ : Env) : Arg → Option Val
  | .var x => ρ.get? x
  | .lit l => some (.lit l)
  | .erased => some .erased

def evalArgs (ρ : Env) : List Arg → Option (List Val)
  | [] => some []
  | a :: as =>
    match a.eval ρ, evalArgs ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Bind variables to values pairwise left-to-right. -/
def bindAll (ρ : Env) : List Var → List Val → Env
  | x :: xs, v :: vs => bindAll (ρ.insert x v) xs vs
  | _, _ => ρ

theorem bindAll_nil (ρ : Env) : bindAll ρ [] [] = ρ := rfl

theorem bindAll_cons (ρ : Env) (x : Var) (xs : List Var) (v : Val) (vs : List Val) :
    bindAll ρ (x :: xs) (v :: vs) = bindAll (ρ.insert x v) xs vs := rfl

def natArgs : List Val → Option (List Nat)
  | [] => some []
  | .lit (.nat n) :: vs => (natArgs vs).map (n :: ·)
  | _ => none

def boolVal (P : Program) (b : Bool) : Option Val :=
  match (if b then P.known.boolTrue else P.known.boolFalse) with
  | some c => (P.ctorInfo? c).map (.ctor · [])
  | none => none

def primResult (P : Program) (p : Prim) (vs : List Val) : Result Val :=
  match natArgs vs with
  | some ns =>
    match p.sem ns with
    | some (.nat n) => .ok (.lit (.nat n))
    | some (.bool b) => Result.ofOption (boolVal P b)
    | none => .stuck
  | none => .stuck

def projVal (P : Program) (c : CtorKey) (i : Nat) (v : Val) : Result Val :=
  match v.asCtor P.known with
  | some (c', fs) => if c' = c then Result.ofOption fs[i]? else .stuck
  | none => .stuck

def evalRhs (P : Program) (ρ : Env) : Rhs → Result Val
  | .arg a => Result.ofOption (a.eval ρ)
  | .ctor c as =>
    match evalArgs ρ as with
    | some vs => if vs.length = c.arity then .ok (.ctor c vs) else .stuck
    | none => .stuck
  | .proj x c i =>
    match ρ.get? x with
    | some v => projVal P c i v
    | none => .stuck
  | .prim op as =>
    match evalArgs ρ as with
    | some vs => primResult P op vs
    | none => .stuck
  | .call .. => .stuck

/-! ## Join Points -/

structure JEntry where
  id : JoinId
  charged : Bool
  env : Env
  params : List Var
  body : Code
  isRec : Bool

def JEntry.weight (e : JEntry) : Nat :=
  if e.charged then 0 else e.body.size

def jweight : List JEntry → Nat
  | [] => 0
  | e :: J => e.weight + jweight J

def lookupJ (j : JoinId) : List JEntry → Option (JEntry × List JEntry)
  | [] => none
  | e :: J => if e.id = j then some (e, J) else lookupJ j J

theorem lookupJ_weight (j : JoinId) :
    ∀ {J : List JEntry} {e : JEntry} {rest : List JEntry},
      lookupJ j J = some (e, rest) → e.weight + jweight rest ≤ jweight J
  | [], _, _, h => by simp [lookupJ] at h
  | e' :: J, e, rest, h => by
    simp only [lookupJ] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jweight]
    · have := lookupJ_weight j h
      simp only [jweight]
      omega

def JEntry.after (e : JEntry) (rest : List JEntry) : List JEntry :=
  if e.isRec then { e with charged := true } :: rest else rest

theorem JEntry.jweight_after (e : JEntry) (rest : List JEntry) :
    jweight (e.after rest) = jweight rest := by
  unfold JEntry.after
  split <;> simp [jweight, JEntry.weight]

/-! ## Clocked Evaluation -/

mutual

def eval (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (c : Code) : Result Val :=
  match c with
  | .bind x (.call f as) c' =>
    match evalArgs ρ as with
    | some vs =>
      match evalCall P k f vs with
      | .ok v => eval P k (ρ.insert x v) J c'
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .bind x r c' =>
    match evalRhs P ρ r with
    | .ok v => eval P k (ρ.insert x v) J c'
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .jp j ps r b c' =>
    eval P k ρ ({ id := j, charged := false, env := ρ, params := ps, body := b, isRec := r } :: J) c'
  | .jmp j as =>
    match _h : lookupJ j J, evalArgs ρ as with
    | some (e, rest), some vs =>
      if vs.length = e.params.length then
        if _hc : e.charged then
          match k with
          | 0 => .timeout
          | k + 1 => eval P k (bindAll e.env e.params vs) (e.after rest) e.body
        else eval P k (bindAll e.env e.params vs) (e.after rest) e.body
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.known with
      | some (key, _) => evalAlts P k ρ J key alts d
      | none => .stuck
    | none => .stuck
  | .ret a => Result.ofOption (a.eval ρ)
  | .tcall f as =>
    match evalArgs ρ as with
    | some vs => evalCall P k f vs
    | none => .stuck
  | .trap => .trap
termination_by (k, c.size + jweight J)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hw := lookupJ_weight j _h
       rw [JEntry.jweight_after]
       simp only [JEntry.weight, _hc, Bool.false_eq_true, ↓reduceIte] at hw
       simp only [Code.size]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size]
       omega)

def evalAlts (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (key : CtorKey)
    (alts : List Alt) (d : Option Code) : Result Val :=
  match alts with
  | [] =>
    match d with
    | some c => eval P k ρ J c
    | none => .stuck
  | .mk key' body :: rest =>
    if key' = key then eval P k ρ J body else evalAlts P k ρ J key rest d
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

def evalCall (P : Program) (k : Nat) (f : FunId) (vs : List Val) : Result Val :=
  match P.fun? f with
  | some fd =>
    if vs.length = fd.params.length then
      match k with
      | 0 => .timeout
      | k + 1 => eval P k (bindAll .leaf (fd.params.map (·.1)) vs) [] fd.body
    else .stuck
  | none => .stuck
termination_by (k, 0)

end

/-- Run function `f` on argument values (entering the function is charged). -/
def run (P : Program) (k : Nat) (f : FunId) (args : List Val) : Result Val :=
  evalCall P k f args

/-! ## Readback -/

mutual

def readback : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .ctor c fs => if c.arity == fs.length then (readbackList fs).map (.ctor c.tag) else none
  | .erased => none

def readbackList : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match readback v, readbackList vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

/-! ## Bind-Form Unfolding Equations -/

def callFun (P : Program) (k : Nat) (fd : Fun) (vs : List Val) : Result Val :=
  if vs.length = fd.params.length then
    later k fun k => eval P k (bindAll .leaf (fd.params.map (·.1)) vs) [] fd.body
  else .stuck

def jumpTo (P : Program) (k : Nat) (e : JEntry) (rest : List JEntry) (vs : List Val) :
    Result Val :=
  if vs.length = e.params.length then
    if e.charged then later k fun k => eval P k (bindAll e.env e.params vs) (e.after rest) e.body
    else eval P k (bindAll e.env e.params vs) (e.after rest) e.body
  else .stuck

theorem evalCall_eq (P : Program) (k : Nat) (f : FunId) (vs : List Val) :
    evalCall P k f vs = (Result.ofOption (P.fun? f)).bind fun fd => callFun P k fd vs := by
  rw [evalCall]
  cases P.fun? f with
  | none => rfl
  | some fd =>
    simp only [Result.ofOption, Result.bind_ok, callFun]
    split
    · cases k <;> rfl
    · rfl

theorem evalCall_of (P : Program) (k : Nat) {f : FunId} {fd : Fun}
    (h : P.fun? f = some fd) (vs : List Val) :
    evalCall P k f vs = callFun P k fd vs := by
  rw [evalCall_eq, h]; rfl

theorem run_eq (P : Program) (k : Nat) (f : FunId) (args : List Val) :
    run P k f args = evalCall P k f args := rfl

theorem eval_bindCall (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (x : Var) (f : FunId) (as : List Arg) (c : Code) :
    eval P k ρ J (.bind x (.call f as) c) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs =>
        (evalCall P k f vs).bind fun v => eval P k (ρ.insert x v) J c := by
  rw [eval]
  cases evalArgs ρ as with
  | none => rfl
  | some vs => simp only [Result.ofOption, Result.bind_ok]; cases evalCall P k f vs <;> rfl

theorem eval_bindRhs (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (x : Var) (r : Rhs) (c : Code) (hr : ∀ f as, r ≠ .call f as) :
    eval P k ρ J (.bind x r c) = (evalRhs P ρ r).bind fun v => eval P k (ρ.insert x v) J c := by
  cases r with
  | call f as => exact absurd rfl (hr f as)
  | _ =>
    rw [eval]
    all_goals first
      | (intro _ _ h; cases h)
      | (cases evalRhs P ρ _ <;> rfl)

theorem eval_jp (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (j : JoinId) (ps : List Var) (r : Bool) (b c : Code) :
    eval P k ρ J (.jp j ps r b c) =
      eval P k ρ ({ id := j, charged := false, env := ρ, params := ps, body := b, isRec := r } :: J) c := by
  rw [eval]

theorem eval_jmp (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (j : JoinId) (as : List Arg) :
    eval P k ρ J (.jmp j as) =
      (Result.ofOption (lookupJ j J)).bind fun p =>
        (Result.ofOption (evalArgs ρ as)).bind fun vs => jumpTo P k p.1 p.2 vs := by
  rw [eval]
  split
  · next _ e rest vs h₁ h₂ =>
    rw [h₁, h₂]
    simp only [Result.ofOption, Result.bind_ok, jumpTo]
    split
    · split
      · cases k <;> rfl
      · rfl
    · rfl
  · next _ hne =>
    cases h₁ : lookupJ j J with
    | none => rfl
    | some p =>
      cases h₂ : evalArgs ρ as with
      | none => simp [Result.ofOption, Result.bind]
      | some vs => exact absurd h₂ (hne p.1 p.2 vs h₁)

theorem eval_case (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (x : Var) (alts : List Alt) (d : Option Code) :
    eval P k ρ J (.case x alts d) = (Result.ofOption (ρ.get? x)).bind fun v =>
      match v.asCtor P.known with
      | some (key, _) => evalAlts P k ρ J key alts d
      | none => .stuck := by
  rw [eval]; cases ρ.get? x <;> rfl

theorem eval_ret (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (a : Arg) :
    eval P k ρ J (.ret a) = Result.ofOption (a.eval ρ) := by
  rw [eval]

theorem eval_tcall (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (f : FunId) (as : List Arg) :
    eval P k ρ J (.tcall f as) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs => evalCall P k f vs := by
  rw [eval]; cases evalArgs ρ as <;> rfl

theorem eval_trap (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) :
    eval P k ρ J .trap = .trap := by
  rw [eval]

theorem evalAlts_nil (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (key : CtorKey) (d : Option Code) :
    evalAlts P k ρ J key [] d = (match d with | some c => eval P k ρ J c | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (key key' : CtorKey) (body : Code) (rest : List Alt) (d : Option Code) :
    evalAlts P k ρ J key (.mk key' body :: rest) d =
      if key' = key then eval P k ρ J body else evalAlts P k ρ J key rest d := by
  rw [evalAlts]

/-! ## Clock Monotonicity -/

theorem jump_measure {j : JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry}
    (h : lookupJ j J = some (e, rest)) (hc : e.charged = false) :
    e.body.size + jweight (e.after rest) < (Code.jmp j []).size + jweight J := by
  have hw := lookupJ_weight j h
  rw [JEntry.jweight_after]
  simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [Code.size]
  omega

section Mono

variable (P : Program)

private theorem callFun_agrees_of {k k' : Nat}
    (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J c, Result.Agrees (eval P j' ρ J c) (eval P j ρ J c))
    (hk : k ≤ k') (fd : Fun) (vs : List Val) :
    Result.Agrees (callFun P k' fd vs) (callFun P k fd vs) := by
  unfold callFun
  split
  · exact Result.Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ [] fd.body
  · exact Result.Agrees.refl _

private theorem evalCall_agrees_of {k k' : Nat}
    (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J c, Result.Agrees (eval P j' ρ J c) (eval P j ρ J c))
    (hk : k ≤ k') (f : FunId) (vs : List Val) :
    Result.Agrees (evalCall P k' f vs) (evalCall P k f vs) := by
  rw [evalCall_eq, evalCall_eq]
  exact Result.Agrees.ofOption _ fun fd _ => callFun_agrees_of P ih hk fd vs

mutual

private theorem eval_agrees_of {k k' : Nat}
    (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J c, Result.Agrees (eval P j' ρ J c) (eval P j ρ J c))
    (hk : k ≤ k') (ρ : Env) (J : List JEntry) (c : Code) :
    Result.Agrees (eval P k' ρ J c) (eval P k ρ J c) := by
  match c with
  | .bind x (.call f as) c' =>
    rw [eval_bindCall, eval_bindCall]
    exact Result.Agrees.ofOption _ fun vs _ =>
      Result.Agrees.bind (evalCall_agrees_of P ih hk f vs) fun v _ =>
        eval_agrees_of ih hk (ρ.insert x v) J c'
  | .bind x (.arg a) c' =>
    rw [eval_bindRhs P k' ρ J x (.arg a) c' (by intro _ _ h; cases h),
        eval_bindRhs P k ρ J x (.arg a) c' (by intro _ _ h; cases h)]
    exact Result.Agrees.bind (Result.Agrees.refl _) fun v _ =>
      eval_agrees_of ih hk (ρ.insert x v) J c'
  | .bind x (.ctor ci as) c' =>
    rw [eval_bindRhs P k' ρ J x (.ctor ci as) c' (by intro _ _ h; cases h),
        eval_bindRhs P k ρ J x (.ctor ci as) c' (by intro _ _ h; cases h)]
    exact Result.Agrees.bind (Result.Agrees.refl _) fun v _ =>
      eval_agrees_of ih hk (ρ.insert x v) J c'
  | .bind x (.proj y ci i) c' =>
    rw [eval_bindRhs P k' ρ J x (.proj y ci i) c' (by intro _ _ h; cases h),
        eval_bindRhs P k ρ J x (.proj y ci i) c' (by intro _ _ h; cases h)]
    exact Result.Agrees.bind (Result.Agrees.refl _) fun v _ =>
      eval_agrees_of ih hk (ρ.insert x v) J c'
  | .bind x (.prim op as) c' =>
    rw [eval_bindRhs P k' ρ J x (.prim op as) c' (by intro _ _ h; cases h),
        eval_bindRhs P k ρ J x (.prim op as) c' (by intro _ _ h; cases h)]
    exact Result.Agrees.bind (Result.Agrees.refl _) fun v _ =>
      eval_agrees_of ih hk (ρ.insert x v) J c'
  | .jp j ps r b c' =>
    rw [eval_jp, eval_jp]
    exact eval_agrees_of ih hk ρ _ c'
  | .jmp j as =>
    rw [eval_jmp, eval_jmp]
    refine Result.Agrees.ofOption _ fun p hp => Result.Agrees.ofOption _ fun vs _ => ?_
    obtain ⟨e, rest⟩ := p
    unfold jumpTo
    split
    · split
      · exact Result.Agrees.later hk fun i i' hi hi' => ih i (by omega) i' (by omega) _ _ e.body
      · next hc =>
        have := jump_measure hp (by simpa using hc)
        exact eval_agrees_of ih hk _ (e.after rest) e.body
    · exact Result.Agrees.refl _
  | .case x alts d =>
    rw [eval_case, eval_case]
    refine Result.Agrees.ofOption _ fun v _ => ?_
    cases v.asCtor P.known with
    | some kf => exact evalAlts_agrees_of ih hk ρ J kf.1 alts d
    | none => exact Result.Agrees.refl _
  | .ret a => rw [eval_ret, eval_ret]; exact Result.Agrees.refl _
  | .tcall f as =>
    rw [eval_tcall, eval_tcall]
    exact Result.Agrees.ofOption _ fun vs _ => evalCall_agrees_of P ih hk f vs
  | .trap => rw [eval_trap, eval_trap]; exact Result.Agrees.refl _
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

private theorem evalAlts_agrees_of {k k' : Nat}
    (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J c, Result.Agrees (eval P j' ρ J c) (eval P j ρ J c))
    (hk : k ≤ k') (ρ : Env) (J : List JEntry) (key : CtorKey) (alts : List Alt) (d : Option Code) :
    Result.Agrees (evalAlts P k' ρ J key alts d) (evalAlts P k ρ J key alts d) := by
  match alts, d with
  | [], some c =>
    rw [evalAlts_nil, evalAlts_nil]
    exact eval_agrees_of ih hk ρ J c
  | [], none => rw [evalAlts_nil, evalAlts_nil]; exact Result.Agrees.refl _
  | .mk key' body :: rest, d =>
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_agrees_of ih hk ρ J body
    · exact evalAlts_agrees_of ih hk ρ J key rest d
termination_by Code.altsSize alts + Code.optSize d + jweight J + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

end

theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ J c,
    Result.Agrees (eval P k' ρ J c) (eval P k ρ J c) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ J c; exact eval_agrees_of P ih hk ρ J c

theorem evalCall_agrees {k k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List Val) :
    Result.Agrees (evalCall P k' f vs) (evalCall P k f vs) :=
  evalCall_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk f vs

theorem eval_mono {k k' : Nat} {ρ : Env} {J : List JEntry} {c : Code} {v : Val}
    (hok : eval P k ρ J c = .ok v) (hk : k ≤ k') :
    eval P k' ρ J c = .ok v :=
  (eval_agrees P k k' hk ρ J c (by rw [hok]; intro h; cases h)).trans hok

theorem evalCall_mono {k k' : Nat} {f : FunId} {vs : List Val} {v : Val}
    (hok : evalCall P k f vs = .ok v) (hk : k ≤ k') :
    evalCall P k' f vs = .ok v :=
  (evalCall_agrees P hk f vs (by rw [hok]; intro h; cases h)).trans hok

theorem run_mono {k k' : Nat} {f : FunId} {vs : List Val} {v : Val}
    (hok : run P k f vs = .ok v) (hk : k ≤ k') :
    run P k' f vs = .ok v :=
  evalCall_mono P hok hk

end Mono

end Ix.Cert.IxccAiur.Fir
