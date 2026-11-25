import IxCCAiur.FirFacts
import Aiur.Modules
import Aiur.Library.U64
import Aiur.HeapMono

/-! # `Fir → Formal Aiur` Lowering

Lowers the compiler's own `IxCC.Fir.Program` (the program `Fir.lower` makes, before
ownership and reference counting; `IxCC.Recheck.runFir`) to a Formal Aiur module
(`Prog`) linking with `Aiur.Library.U64.source`. The driver (`IxCCAiur.Driver`)
runs the result through `Aiur.Modules.prepare`; the world hypothesis
`Backward.LoweredWorld` follows from a check on what that returns
(`IxCCAiur.World`). Covers:
- **Closure constructors (`CtorKey.clo`)** alongside source constructors
  (`CtorKey.src`), indexed injectively into `Obj` (`C<idx>` / `K<idx>`).
- **String / UTF-8 byte literals (`Lit.str`)** via a linked `Bytes` enum
  (`Bytes::Nil`, `Bytes::Cons(Field, &Bytes)`) carried in `Obj::S(Bytes)`.
- **Join points (`.jp` and `.jmp`)**, both non-recursive and recursive, with
  arbitrary nesting and captured lexical variables, lowered via lambda-lifting
  to top-level Aiur functions `j<fid>_<uid>` in `Prog`.
- **12 of 16 `Nat` primitive helpers** (`p_add`, `p_sub`, `p_mul`, `divmod`,
  `p_div`, `p_mod`, `p_pred`, `p_land`, `p_lor`, `p_xor`, `p_beq`, `p_ble`,
  `p_blt`); the remaining 4 `Nat` operations (`natPow`, `natGcd`, `natShl`,
  `natShr`) and every fixed-width word operation (`Lam.Prim.word`) are not yet
  lowered and return `.error` (`primFun` throws `"not supported"`).
- `Fir.Fun`'s modes (`result`, `contracts`, `letContracts`) and the parameters'
  `Rep` are not read: `Fir.eval` does not read them either.
- **Explicit linked/elaborated image (`qualifyExprF`)** and structural plainness
  + freshness invariants consumed by `Gadgets.lean` and `Backward.lean`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`. -/

namespace IxCC.AiurBackend.Lower

open IxCC.Fir
open IxCC.Key
open IxCC.Lam (Lit Prim)

abbrev Ty := Aiur.Generic.Ty
abbrev Expr := Aiur.Generic.Expr Nat
abbrev Pat := Aiur.Generic.Pattern Nat
abbrev Fn := Aiur.Generic.Function Nat

/-- Small `Nat`s are represented as field elements strictly below `2^56`. -/
def natLimit : Nat := 2 ^ 56

/-- Name of the lowered Aiur module. -/
def moduleName : String := "Prog"

/-- Universal Fir value enum name inside `Prog`. -/
def objName : String := "Obj"

/-- Byte-list enum name inside `Prog` for `Lit.str` values. -/
def bytesName : String := "Bytes"

/-- Qualify a local declaration name of module `Prog`. -/
def qualified (name : String) : String := moduleName ++ "::" ++ name

/-- Qualified name of `Prog::Obj`. -/
def objQName : String := qualified objName

/-- Qualified name of `Prog::Bytes`. -/
def bytesQName : String := qualified bytesName

def objTy : Ty := .named objName []
def bytesTy : Ty := .named bytesName []
def ptrObjTy : Ty := .ptr objTy
def ptrBytesTy : Ty := .ptr bytesTy

/-- Decimal digits of `n`, most significant first (provably injective). -/
def natDigits (n : Nat) : List Char :=
  if _h : n < 10 then [Nat.digitChar n]
  else natDigits (n / 10) ++ [Nat.digitChar (n % 10)]
termination_by n
decreasing_by omega

def funName (f : FunId) : String := String.ofList ('f' :: natDigits f)
def entryName (i : Nat) : String := String.ofList ('m' :: 'a' :: 'i' :: 'n' :: natDigits i)
def jpFunName (f : FunId) (uid : Nat) : String :=
  String.ofList ('j' :: natDigits f ++ '_' :: natDigits uid)

def localName (n : Nat) : String := String.ofList ('l' :: natDigits n)
def entryParamName (n : Nat) : String := String.ofList ('x' :: natDigits n)

private theorem digitChar_inj {a b : Nat} (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  have : ∀ x : Fin 10, ∀ y : Fin 10, Nat.digitChar x.1 = Nat.digitChar y.1 → x = y := by decide
  have := this ⟨a, ha⟩ ⟨b, hb⟩ h
  exact congrArg Fin.val this

private theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  unfold natDigits
  split
  · simp
  · simp

private theorem natDigits_inj : ∀ {i j : Nat}, natDigits i = natDigits j → i = j := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro j h
    unfold natDigits at h
    split at h <;> split at h
    · simp only [List.cons.injEq, and_true] at h
      exact digitChar_inj ‹_› ‹_› h
    · next hi hj =>
      have hlen := congrArg List.length h
      simp only [List.length_singleton, List.length_append] at hlen
      have hne := natDigits_ne_nil (j / 10)
      have hpos : 0 < (natDigits (j / 10)).length := List.length_pos_of_ne_nil hne
      omega
    · next hi hj =>
      have hlen := congrArg List.length h
      simp only [List.length_singleton, List.length_append] at hlen
      have hne := natDigits_ne_nil (i / 10)
      have hpos : 0 < (natDigits (i / 10)).length := List.length_pos_of_ne_nil hne
      omega
    · next hi hj =>
      have hl := List.append_inj_right' h rfl
      simp only [List.cons.injEq, and_true] at hl
      have hmod : i % 10 = j % 10 :=
        digitChar_inj (Nat.mod_lt i (by omega)) (Nat.mod_lt j (by omega)) hl
      rw [hl] at h
      have hp := List.append_cancel_right h
      have hdiv : i / 10 = j / 10 := ih (i / 10) (by omega) hp
      omega

theorem localName_inj {i j : Nat} (h : localName i = localName j) : i = j := by
  unfold localName at h
  have h1 := congrArg String.toList h
  simp only [String.toList_ofList, List.cons.injEq, true_and] at h1
  exact natDigits_inj h1

theorem entryParamName_inj {i j : Nat} (h : entryParamName i = entryParamName j) : i = j := by
  unfold entryParamName at h
  have h1 := congrArg String.toList h
  simp only [String.toList_ofList, List.cons.injEq, true_and] at h1
  exact natDigits_inj h1

/-- Constructor name in `Obj` for table entry at index `idx`:
source constructors use `C<idx>`, closure constructors use `K<idx>`. -/
def ctorNameOf (idx : Nat) : CtorKey → String
  | .src _ => String.ofList ('C' :: natDigits idx)
  | .clo _ _ => String.ofList ('K' :: natDigits idx)

theorem ctorNameOf_ne_N (idx : Nat) (k : CtorKey) : ctorNameOf idx k ≠ "N" := by
  cases k <;> intro h <;> have h' := congrArg String.toList h <;> simp [ctorNameOf] at h'

theorem ctorNameOf_ne_E (idx : Nat) (k : CtorKey) : ctorNameOf idx k ≠ "E" := by
  cases k <;> intro h <;> have h' := congrArg String.toList h <;> simp [ctorNameOf] at h'

theorem ctorNameOf_ne_S (idx : Nat) (k : CtorKey) : ctorNameOf idx k ≠ "S" := by
  cases k <;> intro h <;> have h' := congrArg String.toList h <;> simp [ctorNameOf] at h'

theorem localName_ne_q (n : Nat) : localName n ≠ "q" := by
  intro h
  have h' := congrArg String.toList h
  simp [localName] at h'

/-! ## Constructor Table Lookups and Distinctness -/

def ctorEntryAux : Nat → List Lam.CtorInfo → CtorKey → Option (Nat × Lam.CtorInfo)
  | _, [], _ => none
  | idx, e :: rest, k => if e.key == k then some (idx, e) else ctorEntryAux (idx + 1) rest k

def ctorEntry? (P : Program) (k : CtorKey) : Option (Nat × Lam.CtorInfo) :=
  ctorEntryAux 0 P.ctors k

/-- Constructor names generated for `P.ctors`, in table order. -/
def objCtorNames (P : Program) : List String :=
  P.ctors.zipIdx.map fun (e, i) => ctorNameOf i e.key

/-- Decidable duplicate detector (returns `true` iff every element is distinct). -/
def allDistinct [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && allDistinct xs

theorem allDistinct_iff_nodup [DecidableEq α] : ∀ (l : List α), allDistinct l = true ↔ l.Nodup
  | [] => by simp [allDistinct]
  | x :: xs => by
    have hmem : (xs.contains x = false) ↔ x ∉ xs := by simp
    simp only [allDistinct, Bool.and_eq_true, Bool.not_eq_true', hmem,
      List.nodup_cons, allDistinct_iff_nodup xs]

theorem ctorEntryAux_sound :
    ∀ (base : Nat) (l : List Lam.CtorInfo) (k : CtorKey) (idx : Nat) (e : Lam.CtorInfo),
      ctorEntryAux base l k = some (idx, e) →
      base ≤ idx ∧ l[idx - base]? = some e ∧ e.key = k
  | _, [], _, _, _, h => by simp [ctorEntryAux] at h
  | base, x :: xs, k, idx, e, h => by
    unfold ctorEntryAux at h
    by_cases hk : x.key = k
    · simp only [hk, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, hk⟩
    · simp only [hk, beq_iff_eq, ↓reduceIte] at h
      obtain ⟨hle, hget, heq⟩ := ctorEntryAux_sound (base + 1) xs k idx e h
      have hsub : idx - base = (idx - (base + 1)) + 1 := by omega
      refine ⟨by omega, ?_, heq⟩
      rw [hsub]
      simpa using hget

theorem ctorEntry?_sound {P : Program} {k : CtorKey} {idx : Nat} {e : Lam.CtorInfo}
    (h : ctorEntry? P k = some (idx, e)) :
    P.ctors[idx]? = some e ∧ e.key = k := by
  obtain ⟨_, hget, heq⟩ := ctorEntryAux_sound 0 P.ctors k idx e h
  simpa using ⟨hget, heq⟩

theorem ctorEntryAux_complete :
    ∀ (base : Nat) (l : List Lam.CtorInfo) (k : CtorKey) (j : Nat) (e : Lam.CtorInfo),
      (l.map (·.key)).Nodup → l[j]? = some e → e.key = k →
      ctorEntryAux base l k = some (base + j, e)
  | _, [], _, _, _, _, hget, _ => by simp at hget
  | base, x :: xs, k, 0, e, _, hget, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    simp [ctorEntryAux, hk]
  | base, x :: xs, k, j + 1, e, hnd, hget, hk => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hmem : e ∈ xs := List.mem_of_getElem? hget
    have hne : x.key ≠ k := by
      intro heq
      apply hnd.1
      rw [heq, ← hk]
      exact List.mem_map.mpr ⟨e, hmem, rfl⟩
    unfold ctorEntryAux
    simp only [hne, beq_iff_eq, ↓reduceIte]
    have ih := ctorEntryAux_complete (base + 1) xs k j e hnd.2 hget hk
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem ctorEntry?_complete {P : Program} {idx : Nat} {e : Lam.CtorInfo}
    (hnd : (P.ctors.map (·.key)).Nodup) (hget : P.ctors[idx]? = some e) :
    ctorEntry? P e.key = some (idx, e) := by
  simpa [ctorEntry?] using ctorEntryAux_complete 0 P.ctors e.key idx e hnd hget rfl

theorem ctorEntry?_find? {P : Program} {k : CtorKey} {idx : Nat} {e : Lam.CtorInfo}
    (hnd : (P.ctors.map (·.key)).Nodup) (h : ctorEntry? P k = some (idx, e)) :
    P.ctors.find? (·.key == k) = some e := by
  obtain ⟨hget, hk⟩ := ctorEntry?_sound h
  have aux : ∀ (l : List Lam.CtorInfo), (l.map (·.key)).Nodup →
      ∀ (j : Nat) (e : Lam.CtorInfo), l[j]? = some e → e.key = k →
      l.find? (·.key == k) = some e := by
    intro l
    induction l with
    | nil => intro _ _ _ hget; simp at hget
    | cons x xs ih =>
      intro hnd j e hget hk
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        simp [hk]
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hget
        have hne : x.key ≠ k := by
          intro heq
          apply hnd.1
          rw [heq, ← hk]
          exact List.mem_map.mpr ⟨e, List.mem_of_getElem? hget, rfl⟩
        have hbeq : (x.key == k) = false := beq_false_of_ne hne
        simp only [List.find?_cons, hbeq]
        exact ih hnd.2 j' e hget hk
  exact aux P.ctors hnd idx e hget hk

theorem objCtorNames_getElem? (P : Program) {idx : Nat} {e : Lam.CtorInfo}
    (hget : P.ctors[idx]? = some e) :
    (objCtorNames P)[idx]? = some (ctorNameOf idx e.key) := by
  have hlt : idx < P.ctors.length := (List.getElem?_eq_some_iff.mp hget).1
  have heq : P.ctors[idx] = e := (List.getElem?_eq_some_iff.mp hget).2
  unfold objCtorNames
  rw [List.getElem?_map, List.getElem?_zipIdx]
  simp [hlt, heq]

theorem ctorNameOf_inj_of_nodup {P : Program} (hnd : (objCtorNames P).Nodup)
    {i j : Nat} {ei ej : Lam.CtorInfo}
    (hi : P.ctors[i]? = some ei) (hj : P.ctors[j]? = some ej)
    (heq : ctorNameOf i ei.key = ctorNameOf j ej.key) :
    i = j ∧ ei = ej := by
  have hni := objCtorNames_getElem? P hi
  have hnj := objCtorNames_getElem? P hj
  have hli : i < (objCtorNames P).length := (List.getElem?_eq_some_iff.mp hni).1
  have hlj : j < (objCtorNames P).length := (List.getElem?_eq_some_iff.mp hnj).1
  have hgi : (objCtorNames P)[i] = ctorNameOf i ei.key := (List.getElem?_eq_some_iff.mp hni).2
  have hgj : (objCtorNames P)[j] = ctorNameOf j ej.key := (List.getElem?_eq_some_iff.mp hnj).2
  have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp (hgi.trans (heq.trans hgj.symm))
  subst hij
  rw [hi, Option.some.injEq] at hj
  exact ⟨rfl, hj⟩

/-! ## Expression Builders (Explicit Empty Type Arguments) -/

def mk (ctor : String) (args : List Expr) : Expr := .construct objName (some []) ctor args
def natE (e : Expr) : Expr := mk "N" [e]
def erasedE : Expr := mk "E" []
def bytesNilE : Expr := .construct bytesName (some []) "Nil" []
def bytesConsE (b : UInt8) (rest : Expr) : Expr :=
  .construct bytesName (some []) "Cons" [.literal b.toNat, .store rest]

def bytesE : List UInt8 → Expr
  | [] => bytesNilE
  | b :: bs => bytesConsE b (bytesE bs)

def strE (s : String) : Expr := mk "S" [bytesE s.toUTF8.toList]

def pN (p : Pat) : Pat := .construct objTy "N" [p]
def pC (ctor : String) (args : List Pat) : Pat := .construct objTy ctor args
def callE (f : String) (args : List Expr) : Expr := .call f (some []) args
def vE (n : String) : Expr := .var n
def litE (n : Nat) : Expr := .literal n
def letE (n : String) (e body : Expr) : Expr := .letValue (.bind n) e body
def seqE (e body : Expr) : Expr := .letValue .wildcard e body
def matchE (e : Expr) (arms : List (Pat × Expr)) : Expr := .matchValue e arms
def addE (a b : Expr) : Expr := .binary .add a b
def subE (a b : Expr) : Expr := .binary .sub a b

def assertion (msg : String) : Aiur.Assertion := { message := some msg }

/-- Unsatisfiable assertion (`0 = 1`): admits no source derivation. -/
def trapE (msg : String) : Expr :=
  seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) erasedE

/-- Range-checked 64-bit word conversion (`e < 2^56`). -/
def wordE (e : Expr) : Expr := callE "UInt64::from_field" [e]

/-! ## `Nat` Primitive Helpers -/

def binParams : List (String × Ty) := [("a", objTy), ("b", objTy)]

def natPair (body : Expr) : Expr :=
  matchE (.tuple [vE "a", vE "b"]) [(.tuple [pN (.bind "x"), pN (.bind "y")], body)]

def helper (name : String) (params : List (String × Ty)) (body : Expr) : Fn :=
  { name, params, result := objTy, body }

def pAdd : Fn := helper "p_add" binParams <| natPair <|
  letE "s" (addE (vE "x") (vE "y")) (seqE (wordE (vE "s")) (natE (vE "s")))

def pSub : Fn := helper "p_sub" binParams <| natPair <|
  matchE (callE "UInt64::sub_with_borrow" [wordE (vE "x"), wordE (vE "y")])
    [(.tuple [.wildcard, .literal 0], natE (subE (vE "x") (vE "y"))),
     (.wildcard, natE (litE 0))]

def pMul : Fn := helper "p_mul" binParams <| natPair <|
  matchE (callE "UInt64::mul" [wordE (vE "x"), wordE (vE "y")])
    [(.tuple [.bind "lo", .bind "hi"],
      matchE (callE "UInt64::is_zero" [vE "hi"])
        [(.literal 1, natE (callE "UInt64::to_field" [vE "lo"]))])]

def divmod : Fn :=
  { name := "divmod", params := [("x", .field), ("y", .field)], result := .tuple [.field, .field]
    body :=
      .letValue (.tuple [.bind "q", .bind "r"])
        (.hint (.tuple [.field, .field]) (.tuple [vE "x", vE "y"]) "ixcc.divmod") <|
      letE "yw" (wordE (vE "y")) <|
      letE "rw" (wordE (vE "r")) <|
      matchE (callE "UInt64::mul" [wordE (vE "q"), vE "yw"])
        [(.tuple [.bind "lo", .bind "hi"],
          matchE (callE "UInt64::is_zero" [vE "hi"])
            [(.literal 1,
              letE "l" (callE "UInt64::to_field" [vE "lo"]) <|
              seqE (.builtin (.assertEq (assertion "divmod: q*y + r = x"))
                [addE (vE "l") (vE "r"), vE "x"]) <|
              matchE (callE "UInt64::sub_with_borrow" [vE "rw", vE "yw"])
                [(.tuple [.wildcard, .literal 1], .tuple [vE "q", vE "r"])])])] }

def pDiv : Fn := helper "p_div" binParams <| natPair <|
  matchE (vE "y")
    [(.literal 0, natE (litE 0)),
     (.wildcard, matchE (callE "divmod" [vE "x", vE "y"])
       [(.tuple [.bind "q", .wildcard], natE (vE "q"))])]

def pMod : Fn := helper "p_mod" binParams <| natPair <|
  matchE (vE "y")
    [(.literal 0, natE (vE "x")),
     (.wildcard, matchE (callE "divmod" [vE "x", vE "y"])
       [(.tuple [.wildcard, .bind "r"], natE (vE "r"))])]

def pPred : Fn := helper "p_pred" [("a", objTy)] <|
  matchE (vE "a") [(pN (.bind "x"),
    matchE (vE "x") [(.literal 0, natE (litE 0)), (.wildcard, natE (subE (vE "x") (litE 1)))])]

def pBitwise (name op : String) : Fn := helper name binParams <| natPair <|
  natE (callE "UInt64::to_field" [callE op [wordE (vE "x"), wordE (vE "y")]])

def pBeq (tt ff : String) : Fn := helper "p_beq" binParams <| natPair <|
  matchE (subE (vE "x") (vE "y")) [(.literal 0, mk tt []), (.wildcard, mk ff [])]

def pBle (tt ff : String) : Fn := helper "p_ble" binParams <| natPair <|
  matchE (callE "UInt64::sub_with_borrow" [wordE (vE "y"), wordE (vE "x")])
    [(.tuple [.wildcard, .literal 0], mk tt []), (.wildcard, mk ff [])]

def pBlt (tt ff : String) : Fn := helper "p_blt" binParams <| natPair <|
  matchE (callE "UInt64::sub_with_borrow" [wordE (vE "x"), wordE (vE "y")])
    [(.tuple [.wildcard, .literal 0], mk ff []), (.wildcard, mk tt [])]

def boolHelpers (tt ff : String) : List Fn :=
  [pBeq tt ff, pBle tt ff, pBlt tt ff]

def primFun : Prim → Except String (String × Nat)
  | .natAdd => pure ("p_add", 2) | .natSub => pure ("p_sub", 2) | .natMul => pure ("p_mul", 2)
  | .natDiv => pure ("p_div", 2) | .natMod => pure ("p_mod", 2)
  | .natBeq => pure ("p_beq", 2) | .natBle => pure ("p_ble", 2) | .natBlt => pure ("p_blt", 2)
  | .natLand => pure ("p_land", 2) | .natLor => pure ("p_lor", 2) | .natXor => pure ("p_xor", 2)
  | .natPred => pure ("p_pred", 1)
  | p => throw s!"primitive {p.name}: not supported"

def isBoolPrim : Prim → Bool
  | .natBeq | .natBle | .natBlt => true
  | _ => false

/-! ## Lowering Context, Variable Maps, and Join-Point Lifting -/

structure Cx where
  P : Program

def Cx.ctorEntry? (cx : Cx) (k : CtorKey) : Option (Nat × Lam.CtorInfo) :=
  Lower.ctorEntry? cx.P k

def Cx.arity? (cx : Cx) (k : CtorKey) : Option Nat :=
  (cx.ctorEntry? k).map (·.2.arity)

/-- Both pinned `Bool` constructors, present in `P.ctors` with arity `0`. -/
def Cx.boolNames (cx : Cx) : Option (String × String) := do
  let tt ← cx.P.known.boolTrue
  let ff ← cx.P.known.boolFalse
  let (it, et) ← cx.ctorEntry? tt
  let (if_, ef) ← cx.ctorEntry? ff
  if et.arity == 0 && ef.arity == 0 then
    some (ctorNameOf it et.key, ctorNameOf if_ ef.key)
  else
    none

/-- Static variable map from Fir variables to unique Aiur local names `l<n>`. -/
abbrev VarMap := List (Var × String)

/-- Static descriptor of a lifted join point in lexical scope. -/
structure JEntryL where
  id : JoinId
  fnName : String
  capNames : List String
  paramCount : Nat
  deriving DecidableEq, Repr, Inhabited

/-- All Aiur local variable names currently live (in `vm` or captured by `jenv`). -/
def liveNames (vm : VarMap) (jenv : List JEntryL) : List String :=
  (vm.map Prod.snd ++ jenv.flatMap (·.capNames)).eraseDups

/-- Extend `vm` with parameters pairwise left-to-right (matching `Fir.bindAll`). -/
def bindVm (vm : VarMap) : List Var → List String → VarMap
  | x :: xs, nm :: nms => bindVm ((x, nm) :: vm) xs nms
  | _, _ => vm

/-- Lowering state within a single Fir function. -/
structure LowerState where
  nextLocal : Nat := 0
  nextJp : Nat := 0
  lifted : List Fn := []

abbrev LowerM := StateT LowerState (Except String)

def liftExcept {α : Type} (r : Except String α) : LowerM α := fun st =>
  match r with
  | .ok a => .ok (a, st)
  | .error e => .error e

def freshLocal : LowerM String := fun st =>
  .ok (localName st.nextLocal, { st with nextLocal := st.nextLocal + 1 })

def freshLocals : Nat → LowerM (List String)
  | 0 => pure []
  | n + 1 => do
    let h ← freshLocal
    let t ← freshLocals n
    return h :: t

def freshJp : LowerM Nat := fun st =>
  .ok (st.nextJp, { st with nextJp := st.nextJp + 1 })

def emitLifted (f : Fn) : LowerM Unit := fun st =>
  .ok ((), { st with lifted := st.lifted ++ [f] })

/-! ## Lowering Arguments, Right-Hand Sides, Case, and Code -/

def argE (vm : VarMap) : Arg → Except String Expr
  | .var x =>
    match vm.lookup x with
    | some nx => pure (vE nx)
    | none => throw s!"unbound variable {x}"
  | .lit (.nat n) =>
    if n < natLimit then pure (natE (litE n))
    else throw s!"literal {n} ≥ 2^56"
  | .lit (.str s) => pure (strE s)
  | .erased => pure erasedE

def argsE (vm : VarMap) (as : List Arg) : Except String (List Expr) :=
  as.mapM (argE vm)

def projE (cx : Cx) (nx : String) (c : CtorKey) (i : Nat) : Expr :=
  let tableArm : List (Pat × Expr) := match cx.ctorEntry? c with
    | some (idx, entry) =>
      if i < entry.arity then
        let name := ctorNameOf idx entry.key
        [(pC name ((List.range entry.arity).map fun j => if j = i then .bind "q" else .wildcard),
          .load (vE "q"))]
      else []
    | none => []
  let natArm : List (Pat × Expr) :=
    if cx.P.known.natSucc == some c && i == 0 then
      [(pN (.bind "q"), matchE (vE "q")
        [(.literal 0, trapE "Nat.zero has no field"),
         (.wildcard, natE (subE (vE "q") (litE 1)))])]
    else []
  let arms := tableArm ++ natArm
  if arms.isEmpty then trapE "projection of a missing field"
  else matchE (vE nx) arms

def rhsE (cx : Cx) (vm : VarMap) : Rhs → Except String Expr
  | .arg a => argE vm a
  | .ctor c as => do
    let some (idx, entry) := cx.ctorEntry? c.key
      | throw "constructor is not in the constructor table"
    unless as.length == entry.arity && c.arity == entry.arity do
      throw s!"constructor {ctorNameOf idx entry.key}: arity mismatch"
    return mk (ctorNameOf idx entry.key) ((← argsE vm as).map .store)
  | .proj x c i => do
    let some nx := vm.lookup x | throw s!"unbound variable {x}"
    return projE cx nx c i
  | .prim op as => do
    let (f, n) ← primFun op
    unless as.length == n do throw s!"primitive {op.name}: {as.length} arguments"
    if isBoolPrim op && cx.boolNames.isNone then
      throw s!"primitive {op.name}: Bool pins missing or non-nullary"
    return callE f (← argsE vm as)
  | .call f as => do
    let some fd := cx.P.fun? f | throw s!"unknown function {f}"
    unless f < cx.P.size do throw s!"function {f} outside program size"
    unless as.length == fd.params.length do throw s!"function {f}: arity mismatch"
    return callE (funName f) (← argsE vm as)

/-- Keep only the first alternative of each constructor key (matching `Fir.evalAlts`). -/
def firstPerKey : List (CtorKey × Expr) → List (CtorKey × Expr) → List (CtorKey × Expr)
  | acc, [] => acc.reverse
  | acc, (k, e) :: rest =>
    if acc.any (·.1 == k) then firstPerKey acc rest else firstPerKey ((k, e) :: acc) rest

/-- Constructor arms for alternatives whose key is in `P.ctors`. -/
def ctorArms (cx : Cx) : List (CtorKey × Expr) → List (Pat × Expr)
  | [] => []
  | (k, body) :: rest =>
    let tail := ctorArms cx rest
    match cx.ctorEntry? k with
    | some (idx, entry) =>
      (pC (ctorNameOf idx entry.key) (List.replicate entry.arity .wildcard), body) :: tail
    | none => tail

/-- `case x alts d`: constructor arms (including `.src` and `.clo`), then `Nat`
literal peeling, then `E` and `S` traps, then optional default arm. -/
def caseE (cx : Cx) (nx : String) (alts : List (CtorKey × Expr)) (d : Option Expr) : Expr :=
  let firsts := firstPerKey [] alts
  let fallback := d.getD (trapE "no alternative")
  let pick : Option CtorKey → Expr
    | some k => ((firsts.find? (·.1 == k)).map (·.2)).getD fallback
    | none => trapE "unpinned Nat literal under case"
  let arms := ctorArms cx firsts
  let natArm : Pat × Expr :=
    (pN (.bind "q"), matchE (vE "q")
      [(.literal 0, pick cx.P.known.natZero), (.wildcard, pick cx.P.known.natSucc)])
  let erasedArm : Pat × Expr := (pC "E" [], trapE "case on an erased value")
  let strArm : Pat × Expr := (pC "S" [.wildcard], trapE "case on a string literal")
  let dfltArm : List (Pat × Expr) := match d with
    | some e => [(.wildcard, e)]
    | none => []
  matchE (vE nx) (arms ++ [natArm, erasedArm, strArm] ++ dfltArm)

mutual

def codeE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    Code → LowerM Expr
  | .bind x r k => do
    let re ← liftExcept (rhsE cx vm r)
    let nx ← freshLocal
    let ke ← codeE cx fid ((x, nx) :: vm) jenv k
    return letE nx re ke
  | .jp j ps isRec body k => do
    let capNames := liveNames vm jenv
    let uid ← freshJp
    let jpName := jpFunName fid uid
    let paramNames ← freshLocals ps.length
    let ji : JEntryL := ⟨j, jpName, capNames, ps.length⟩
    let bodyVm := bindVm vm ps paramNames
    let bodyJenv := if isRec then ji :: jenv else jenv
    let bodyExpr ← codeE cx fid bodyVm bodyJenv body
    emitLifted {
      name := jpName
      params := (capNames ++ paramNames).map (·, objTy)
      result := objTy
      body := bodyExpr
    }
    codeE cx fid vm (ji :: jenv) k
  | .jmp j as => do
    let some ji := jenv.find? (·.id == j) | liftExcept (throw s!"unbound join point {j}")
    unless as.length == ji.paramCount do
      liftExcept (throw s!"join point {j}: arity mismatch")
    let argExprs ← liftExcept (argsE vm as)
    return callE ji.fnName (ji.capNames.map vE ++ argExprs)
  | .case x alts d => do
    let some nx := vm.lookup x | liftExcept (throw s!"unbound variable {x}")
    let altExprs ← altsE cx fid vm jenv alts
    let dExpr ← optE cx fid vm jenv d
    return caseE cx nx altExprs dExpr
  | .ret a => liftExcept (argE vm a)
  | .tcall f as => do
    let some fd := cx.P.fun? f | liftExcept (throw s!"unknown function {f}")
    unless f < cx.P.size do liftExcept (throw s!"function {f} outside program size")
    unless as.length == fd.params.length do liftExcept (throw s!"function {f}: arity mismatch")
    let argExprs ← liftExcept (argsE vm as)
    return callE (funName f) argExprs
  | .trap => pure (trapE "trap")

def altsE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    List Alt → LowerM (List (CtorKey × Expr))
  | [] => pure []
  | .mk k b :: rest => do
    let be ← codeE cx fid vm jenv b
    let re ← altsE cx fid vm jenv rest
    return (k, be) :: re

def optE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    Option Code → LowerM (Option Expr)
  | none => pure none
  | some c => do return some (← codeE cx fid vm jenv c)

end

/-! ## Functions, Entries, Enums, and Module Assembly -/

/-- Lower one Fir function `fid`, returning `[f<fid>] ++ liftedJoinPointFns`. -/
def funE (cx : Cx) (fid : FunId) (fd : Fun) : Except String (List Fn) := do
  let ((paramNames, body), st) ← (do
    let paramNames ← freshLocals fd.params.length
    let vm := bindVm [] (fd.params.map Prod.fst) paramNames
    let body ← codeE cx fid vm [] fd.body
    return (paramNames, body)).run {}
  let mainFn : Fn := {
    name := funName fid
    params := paramNames.map (·, objTy)
    result := objTy
    body
  }
  return mainFn :: st.lifted

/-- Entry wrapper `main<i>(x0 … : Field) -> Obj`: range-checks each `Field`
argument via `UInt64::from_field` and invokes `f<f>`. -/
def entryE (P : Program) (i : Nat) (f : FunId) : Except String Fn := do
  let some fd := P.fun? f | throw s!"export {i}: function {f} is missing"
  unless f < P.size do throw s!"export {i}: function {f} outside program size"
  let n := fd.params.length
  return {
    name := entryName i
    params := (List.range n).map fun j => (entryParamName j, (.field : Ty))
    result := objTy
    body := callE (funName f) ((List.range n).map fun j =>
      seqE (wordE (vE (entryParamName j))) (natE (vE (entryParamName j))))
  }

def bytesEnumDecl : Aiur.Generic.EnumDecl := {
  name := bytesName
  constructors := [
    { name := "Nil", fields := [] },
    { name := "Cons", fields := [.field, ptrBytesTy] }
  ]
}

def objEnumDecl (P : Program) : Aiur.Generic.EnumDecl :=
  let cs := P.ctors.zipIdx.map fun (r, idx) =>
    ({ name := ctorNameOf idx r.key, fields := List.replicate r.arity ptrObjTy } :
      Aiur.Generic.ConstructorDecl)
  {
    name := objName
    constructors := [
      { name := "N", fields := [.field] },
      { name := "E", fields := [] },
      { name := "S", fields := [bytesTy] }
    ] ++ cs
  }

def helpers (cx : Cx) : List Fn :=
  [pAdd, pSub, pMul, divmod, pDiv, pMod, pPred,
   pBitwise "p_land" "UInt64::and", pBitwise "p_lor" "UInt64::or", pBitwise "p_xor" "UInt64::xor"] ++
  (match cx.boolNames with
   | some (t, f) => boolHelpers t f
   | none => [])

/-- Lower a complete `Fir.Program` to an Aiur `Generic.Program Nat`. -/
def lowerProgram (P : Program) : Except String (Aiur.Generic.Program Nat) := do
  unless allDistinct (P.ctors.map (·.key)) do
    throw "duplicate constructor key in constructor table"
  unless allDistinct (objCtorNames P) do
    throw "duplicate constructor name in constructor table"
  let cx : Cx := ⟨P⟩
  let fnGroups ← P.funList.mapM fun (f, fd) => funE cx f fd
  let fns := fnGroups.flatten
  let entries ← ((List.range P.exports.length).zip P.exports).mapM fun (i, f) => entryE P i f
  return {
    functions := entries ++ fns ++ helpers cx
    enums := [bytesEnumDecl, objEnumDecl P]
  }

/-- Lower a `Fir.Program` to module `Prog`, ready to link with `Aiur.Library.U64.source`. -/
def lowerModule (P : Program) : Except String (Aiur.Modules.Program Nat) := do
  let program ← lowerProgram P
  return { modules := [{ name := moduleName, body := .definitions { program } }] }

/-- Link a lowered `Fir.Program` with `Aiur.Library.U64.source` over field `F`. -/
def linkedProgram (F : Type) [NatCast F] (m : Aiur.Modules.Program Nat) : Aiur.Modules.Program F :=
  (Aiur.Library.U64.source.append m).toField F

/-! ## Linked / Elaborated AST Qualification (`Prog::`) -/

/-- Check structurally whether a character list contains the substring `"::"`. -/
def hasDoubleColon : List Char → Bool
  | c1 :: c2 :: cs => (c1 == ':' && c2 == ':') || hasDoubleColon (c2 :: cs)
  | _ => false

private theorem digitChar_ne_colon {a : Nat} (ha : a < 10) : Nat.digitChar a ≠ ':' := by
  have : ∀ x : Fin 10, Nat.digitChar x.1 ≠ ':' := by decide
  exact this ⟨a, ha⟩

private theorem natDigits_no_colon : ∀ n c, c ∈ natDigits n → c ≠ ':' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    unfold natDigits at hc
    split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact digitChar_ne_colon ‹_›
    · simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hl | rfl
      · exact ih (n / 10) (by omega) c hl
      · exact digitChar_ne_colon (Nat.mod_lt n (by omega))

theorem hasDoubleColon_false_of_no_colon :
    ∀ {cs : List Char}, (∀ c ∈ cs, c ≠ ':') → hasDoubleColon cs = false
  | [], _ => rfl
  | [_], _ => rfl
  | c1 :: c2 :: cs, h => by
    have h1 : (c1 == ':') = false := beq_false_of_ne (h c1 List.mem_cons_self)
    have htl : hasDoubleColon (c2 :: cs) = false :=
      hasDoubleColon_false_of_no_colon fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp [hasDoubleColon, h1, htl]

/-- Qualify a name unless it is already module-qualified (`::`). -/
def qualifyName (name : String) : String :=
  if hasDoubleColon name.toList then name else qualified name

theorem qualifyName_funName (f : FunId) : qualifyName (funName f) = qualified (funName f) := by
  unfold qualifyName
  have h : hasDoubleColon (funName f).toList = false := by
    apply hasDoubleColon_false_of_no_colon
    intro c hc
    simp only [funName, String.toList_ofList, List.mem_cons] at hc
    rcases hc with rfl | hd
    · decide
    · exact natDigits_no_colon f c hd
  simp [h]

theorem qualifyName_entryName (i : Nat) : qualifyName (entryName i) = qualified (entryName i) := by
  unfold qualifyName
  have h : hasDoubleColon (entryName i).toList = false := by
    apply hasDoubleColon_false_of_no_colon
    intro c hc
    simp only [entryName, String.toList_ofList, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | hd
    · decide
    · decide
    · decide
    · decide
    · exact natDigits_no_colon i c hd
  simp [h]

theorem qualifyName_jpFunName (f : FunId) (uid : Nat) :
    qualifyName (jpFunName f uid) = qualified (jpFunName f uid) := by
  unfold qualifyName
  have h : hasDoubleColon (jpFunName f uid).toList = false := by
    apply hasDoubleColon_false_of_no_colon
    intro c hc
    simp only [jpFunName, String.toList_ofList, List.mem_cons, List.mem_append] at hc
    rcases hc with (rfl | hd) | rfl | hd'
    · decide
    · exact natDigits_no_colon f c hd
    · decide
    · exact natDigits_no_colon uid c hd'
  simp [h]

theorem qualifyName_primFun {op : Prim} {nm : String} {ar : Nat}
    (h : primFun op = .ok (nm, ar)) : qualifyName nm = qualified nm := by
  cases op <;> simp [primFun, pure, Except.pure, throw] at h <;>
    obtain ⟨rfl, _⟩ := h <;> rfl

@[simp] theorem qualifyName_obj : qualifyName objName = objQName := rfl
@[simp] theorem qualifyName_bytes : qualifyName bytesName = bytesQName := rfl
@[simp] theorem qualifyName_divmod : qualifyName "divmod" = qualified "divmod" := rfl
@[simp] theorem qualifyName_u64_from_field :
    qualifyName "UInt64::from_field" = "UInt64::from_field" := rfl
@[simp] theorem qualifyName_u64_to_field :
    qualifyName "UInt64::to_field" = "UInt64::to_field" := rfl
@[simp] theorem qualifyName_u64_is_zero :
    qualifyName "UInt64::is_zero" = "UInt64::is_zero" := rfl
@[simp] theorem qualifyName_u64_sub_with_borrow :
    qualifyName "UInt64::sub_with_borrow" = "UInt64::sub_with_borrow" := rfl
@[simp] theorem qualifyName_u64_mul :
    qualifyName "UInt64::mul" = "UInt64::mul" := rfl
@[simp] theorem qualifyName_u64_and :
    qualifyName "UInt64::and" = "UInt64::and" := rfl
@[simp] theorem qualifyName_u64_or :
    qualifyName "UInt64::or" = "UInt64::or" := rfl
@[simp] theorem qualifyName_u64_xor :
    qualifyName "UInt64::xor" = "UInt64::xor" := rfl

def qualifyTy : Ty → Ty
  | .field => .field
  | .param p => .param p
  | .ptr t => .ptr (qualifyTy t)
  | .array t n => .array (qualifyTy t) n
  | .tuple ts => .tuple (ts.map qualifyTy)
  | .named n ts => .named (qualifyName n) (ts.map qualifyTy)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega

def qualifyPat : Pat → Pat
  | .literal x => .literal x
  | .wildcard => .wildcard
  | .bind n => .bind n
  | .global n t => .global (qualifyName n) (t.map qualifyTy)
  | .load p => .load (qualifyPat p)
  | .orElse l r b => .orElse (qualifyPat l) (qualifyPat r) b
  | .tuple ps => .tuple (ps.map qualifyPat)
  | .array ps => .array (ps.map qualifyPat)
  | .repeat p n => .repeat (qualifyPat p) n
  | .record h ps => .record { h with type := qualifyTy h.type } (ps.map qualifyPat)
  | .construct t c ps => .construct (qualifyTy t) c (ps.map qualifyPat)
  | .constructAs a t c ps => .constructAs a (qualifyTy t) c (ps.map qualifyPat)
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega

def qualifyExpr : Expr → Expr
  | .literal x => .literal x
  | .var n => .var n
  | .global n t => .global (qualifyName n) (t.map qualifyTy)
  | .tuple xs => .tuple (xs.map qualifyExpr)
  | .array xs => .array (xs.map qualifyExpr)
  | .repeat x n => .repeat (qualifyExpr x) n
  | .index x i => .index (qualifyExpr x) i
  | .slice x s e => .slice (qualifyExpr x) s e
  | .construct n ts c xs =>
    .construct (qualifyName n) (ts.map (List.map qualifyTy)) c (xs.map qualifyExpr)
  | .constructAs a t c xs => .constructAs a (qualifyTy t) c (xs.map qualifyExpr)
  | .record h xs => .record { h with type := qualifyTy h.type } (xs.map qualifyExpr)
  | .member x f => .member (qualifyExpr x) { f with owner := f.owner.map qualifyTy }
  | .update ps xs => .update ps (xs.map qualifyExpr)
  | .builtin op xs => .builtin op (xs.map qualifyExpr)
  | .project x i => .project (qualifyExpr x) i
  | .letValue p x b => .letValue (qualifyPat p) (qualifyExpr x) (qualifyExpr b)
  | .store x => .store (qualifyExpr x)
  | .load x => .load (qualifyExpr x)
  | .hint t k ch => .hint (qualifyTy t) (qualifyExpr k) ch
  | .neg x => .neg (qualifyExpr x)
  | .binary op l r => .binary op (qualifyExpr l) (qualifyExpr r)
  | .call n ts xs => .call (qualifyName n) (ts.map (List.map qualifyTy)) (xs.map qualifyExpr)
  | .matchValue x arms => .matchValue (qualifyExpr x) (arms.map fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
  | .control k b => .control k (qualifyExpr b)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      cases ‹Pat × Expr›
      simp_all only [Prod.mk.sizeOf_spec]
      omega

def qualifyPatF (F : Type) [NatCast F] (p : Pat) : Aiur.Generic.Pattern F :=
  (qualifyPat p).map Nat.cast

def qualifyExprF (F : Type) [NatCast F] (e : Expr) : Aiur.Generic.Expr F :=
  (qualifyExpr e).map Nat.cast

/-! ## Plainness (No `.control` and No Expression-Level `.global`) -/

mutual

/-- An expression with no `.control` (`block`/`exit`) and no expression-level `.global`
cannot produce an abrupt `EvalExit`. -/
def isPlainExpr {α : Type} : Aiur.Generic.Expr α → Bool
  | .control .. | .global .. => false
  | .literal _ | .var _ => true
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs =>
    isPlainList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => isPlainExpr x
  | .letValue _ x b | .binary _ x b => isPlainExpr x && isPlainExpr b
  | .matchValue x arms => isPlainExpr x && isPlainArms arms

def isPlainList {α : Type} : List (Aiur.Generic.Expr α) → Bool
  | [] => true
  | x :: xs => isPlainExpr x && isPlainList xs

def isPlainArms {α : Type} : List (Aiur.Generic.Pattern α × Aiur.Generic.Expr α) → Bool
  | [] => true
  | (_, b) :: arms => isPlainExpr b && isPlainArms arms

end

theorem isPlainList_iff {α : Type} : ∀ {xs : List (Aiur.Generic.Expr α)},
    isPlainList xs = true ↔ ∀ x ∈ xs, isPlainExpr x = true
  | [] => by simp [isPlainList]
  | x :: xs => by
    simp only [isPlainList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, isPlainList_iff]

theorem isPlainArms_iff {α : Type} : ∀ {arms : List (Aiur.Generic.Pattern α × Aiur.Generic.Expr α)},
    isPlainArms arms = true ↔ ∀ a ∈ arms, isPlainExpr a.2 = true
  | [] => by simp [isPlainArms]
  | (p, b) :: arms => by
    simp only [isPlainArms, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, isPlainArms_iff]

mutual

theorem isPlainExpr_map {α β : Type} (f : α → β) :
    ∀ (e : Aiur.Generic.Expr α), isPlainExpr (e.map f) = isPlainExpr e
  | .control .. | .global .. | .literal _ | .var _ => by simp [Aiur.Generic.Expr.map, isPlainExpr]
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => by
    simp [Aiur.Generic.Expr.map, isPlainExpr, isPlainExpr_map f x]
  | .letValue _ x b | .binary _ x b => by
    simp [Aiur.Generic.Expr.map, isPlainExpr, isPlainExpr_map f x, isPlainExpr_map f b]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => by
    simp [Aiur.Generic.Expr.map, isPlainExpr, isPlainList_map f xs]
  | .matchValue x arms => by
    simp [Aiur.Generic.Expr.map, isPlainExpr, isPlainExpr_map f x, isPlainArms_map f arms]

theorem isPlainList_map {α β : Type} (f : α → β) :
    ∀ (xs : List (Aiur.Generic.Expr α)), isPlainList (xs.map (Aiur.Generic.Expr.map f)) = isPlainList xs
  | [] => rfl
  | x :: xs => by simp [isPlainList, isPlainExpr_map f x, isPlainList_map f xs]

theorem isPlainArms_map {α β : Type} (f : α → β) :
    ∀ (arms : List (Aiur.Generic.Pattern α × Aiur.Generic.Expr α)),
      isPlainArms (arms.map fun arm => (arm.1.map f, arm.2.map f)) = isPlainArms arms
  | [] => rfl
  | (p, b) :: arms => by simp [isPlainArms, isPlainExpr_map f b, isPlainArms_map f arms]

end

mutual

theorem isPlainExpr_qualifyExpr : ∀ (e : Expr), isPlainExpr (qualifyExpr e) = isPlainExpr e
  | .control .. | .global .. | .literal _ | .var _ => by simp [qualifyExpr, isPlainExpr]
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => by
    simp [qualifyExpr, isPlainExpr, isPlainExpr_qualifyExpr x]
  | .letValue _ x b | .binary _ x b => by
    simp [qualifyExpr, isPlainExpr, isPlainExpr_qualifyExpr x, isPlainExpr_qualifyExpr b]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => by
    simp [qualifyExpr, isPlainExpr, isPlainList_qualifyExpr xs]
  | .matchValue x arms => by
    simp [qualifyExpr, isPlainExpr, isPlainExpr_qualifyExpr x, isPlainArms_qualifyExpr arms]

theorem isPlainList_qualifyExpr :
    ∀ (xs : List Expr), isPlainList (xs.map qualifyExpr) = isPlainList xs
  | [] => rfl
  | x :: xs => by simp [isPlainList, isPlainExpr_qualifyExpr x, isPlainList_qualifyExpr xs]

theorem isPlainArms_qualifyExpr :
    ∀ (arms : List (Pat × Expr)),
      isPlainArms (arms.map fun arm => (qualifyPat arm.1, qualifyExpr arm.2)) = isPlainArms arms
  | [] => rfl
  | (p, b) :: arms => by simp [isPlainArms, isPlainExpr_qualifyExpr b, isPlainArms_qualifyExpr arms]

end

theorem isPlainExpr_qualifyExprF {F : Type} [NatCast F] (e : Expr) :
    isPlainExpr (qualifyExprF F e) = isPlainExpr e := by
  rw [qualifyExprF, isPlainExpr_map, isPlainExpr_qualifyExpr]

/-! ## Freshness, State Monotonicity, and Plainness Invariants of `LowerM` -/

/-- Every string in `xs` is `localName k` for some `k < n`. -/
def AllLocalLt (n : Nat) (xs : List String) : Prop :=
  ∀ s ∈ xs, ∃ k < n, s = localName k

theorem AllLocalLt.mono {n m : Nat} {xs : List String} (h : AllLocalLt n xs) (hle : n ≤ m) :
    AllLocalLt m xs := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := h s hs
  exact ⟨k, Nat.lt_of_lt_of_le hk hle, rfl⟩

theorem AllLocalLt.not_mem {n k : Nat} {xs : List String}
    (h : AllLocalLt n xs) (hk : n ≤ k) : localName k ∉ xs := by
  intro hmem
  obtain ⟨j, hj, heq⟩ := h _ hmem
  have := localName_inj heq
  omega

theorem AllLocalLt.ne_q {n : Nat} {xs : List String} (h : AllLocalLt n xs) :
    ∀ s ∈ xs, s ≠ "q" := by
  intro s hs
  obtain ⟨k, _, rfl⟩ := h s hs
  exact localName_ne_q k

theorem freshLocals_spec :
    ∀ (m : Nat) (st : LowerState),
      ∃ names,
        freshLocals m st = .ok (names, { st with nextLocal := st.nextLocal + m }) ∧
        names = (List.range m).map (fun i => localName (st.nextLocal + i))
  | 0, st => ⟨[], by simp [freshLocals, pure, StateT.pure, Except.pure], by simp⟩
  | m + 1, st => by
    obtain ⟨tail, htail, htailEq⟩ := freshLocals_spec m { st with nextLocal := st.nextLocal + 1 }
    refine ⟨localName st.nextLocal :: tail, ?_, ?_⟩
    · simp only [freshLocals, bind, StateT.bind, freshLocal, pure, StateT.pure,
        Except.bind, Except.pure, htail]
      have hadd : st.nextLocal + 1 + m = st.nextLocal + (m + 1) := by omega
      rw [hadd]
    · rw [htailEq, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem freshLocals_length {m : Nat} {st st' : LowerState} {names : List String}
    (h : freshLocals m st = .ok (names, st')) : names.length = m := by
  obtain ⟨ns, hns, hnsEq⟩ := freshLocals_spec m st
  rw [hns, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  simp [hnsEq]

theorem freshLocals_nodup {m : Nat} {st st' : LowerState} {names : List String}
    (h : freshLocals m st = .ok (names, st')) : names.Nodup := by
  obtain ⟨ns, hns, hnsEq⟩ := freshLocals_spec m st
  rw [hns, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  rw [hnsEq]
  exact List.Nodup.map (fun i j heq => by have := localName_inj heq; omega) List.nodup_range

theorem freshLocals_range {m : Nat} {st st' : LowerState} {names : List String}
    (h : freshLocals m st = .ok (names, st')) :
    st'.nextLocal = st.nextLocal + m ∧ st'.lifted = st.lifted ∧
    (∀ s ∈ names, ∃ k, st.nextLocal ≤ k ∧ k < st'.nextLocal ∧ s = localName k) := by
  obtain ⟨ns, hns, hnsEq⟩ := freshLocals_spec m st
  rw [hns, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  rw [hnsEq, List.mem_map] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  rw [List.mem_range] at hi
  exact ⟨st.nextLocal + i, by omega, by dsimp; omega, rfl⟩

/-! ## Inversion Lemmas for `codeE`, `altsE`, `optE`, and `funE` -/

theorem codeE_bind_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {x : Var} {r : Rhs} {k : Code} {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.bind x r k) st = .ok (e, st')) :
    ∃ re ke,
      rhsE cx vm r = .ok re ∧
      codeE cx fid ((x, localName st.nextLocal) :: vm) jenv k
        { st with nextLocal := st.nextLocal + 1 } = .ok (ke, st') ∧
      e = letE (localName st.nextLocal) re ke := by
  unfold codeE at h
  cases hr : rhsE cx vm r with
  | error err => simp [hr, liftExcept, bind, StateT.bind, Except.bind] at h
  | ok re =>
    simp only [hr, liftExcept, freshLocal, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure] at h
    cases hk : codeE cx fid ((x, localName st.nextLocal) :: vm) jenv k
        { st with nextLocal := st.nextLocal + 1 } with
    | error err => simp [hk] at h
    | ok res =>
      rcases res with ⟨ke, st''⟩
      simp only [hk, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨re, ke, rfl, rfl, rfl⟩

theorem codeE_jp_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {j : JoinId} {ps : List Var} {isRec : Bool} {body k : Code}
    {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.jp j ps isRec body k) st = .ok (e, st')) :
    let capNames := liveNames vm jenv
    let jpName := jpFunName fid st.nextJp
    let pns := (List.range ps.length).map (fun i => localName (st.nextLocal + i))
    let ji : JEntryL := ⟨j, jpName, capNames, ps.length⟩
    let st1 : LowerState := { st with nextLocal := st.nextLocal + ps.length, nextJp := st.nextJp + 1 }
    ∃ bodyExpr st2,
      codeE cx fid (bindVm vm ps pns) (if isRec then ji :: jenv else jenv) body st1 =
        .ok (bodyExpr, st2) ∧
      codeE cx fid vm (ji :: jenv) k
        { st2 with lifted := st2.lifted ++ [⟨jpName, [], (capNames ++ pns).map (·, objTy),
          objTy, bodyExpr, false⟩] } = .ok (e, st') := by
  unfold codeE at h
  obtain ⟨pns, hpns, hpnsEq⟩ := freshLocals_spec ps.length { st with nextJp := st.nextJp + 1 }
  simp only [freshJp, emitLifted, bind, StateT.bind, Except.bind, hpns] at h
  cases hb : codeE cx fid (bindVm vm ps pns)
      (if isRec then ⟨j, jpFunName fid st.nextJp, liveNames vm jenv, ps.length⟩ :: jenv else jenv)
      body { st with nextLocal := st.nextLocal + ps.length, nextJp := st.nextJp + 1 } with
  | error err => simp [hb] at h
  | ok bres =>
    simp only [hb] at h
    subst hpnsEq
    exact ⟨bres.1, bres.2, hb, h⟩

theorem codeE_jmp_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {j : JoinId} {as : List Arg} {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.jmp j as) st = .ok (e, st')) :
    ∃ ji argEs,
      jenv.find? (·.id == j) = some ji ∧
      as.length = ji.paramCount ∧
      argsE vm as = .ok argEs ∧
      e = callE ji.fnName (ji.capNames.map vE ++ argEs) ∧
      st' = st := by
  unfold codeE at h
  cases hj : jenv.find? (·.id == j) with
  | none =>
    simp [hj, liftExcept, throw, throwThe, MonadExceptOf.throw] at h
  | some ji =>
    simp only [hj] at h
    by_cases hlen : as.length = ji.paramCount
    · simp only [hlen, beq_self_eq_true, ↓reduceIte, bind, StateT.bind, pure, StateT.pure,
        liftExcept, Except.bind, Except.pure] at h
      cases ha : argsE vm as with
      | error err => simp [ha] at h
      | ok argEs =>
        simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ji, argEs, rfl, hlen, rfl, rfl, rfl⟩
    · have hbeq : (as.length == ji.paramCount) = false := beq_false_of_ne hlen
      simp [hbeq, bind, StateT.bind, liftExcept, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h

theorem codeE_case_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {x : Var} {alts : List Alt} {d : Option Code} {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.case x alts d) st = .ok (e, st')) :
    ∃ nx altEs st1 dE,
      vm.lookup x = some nx ∧
      altsE cx fid vm jenv alts st = .ok (altEs, st1) ∧
      optE cx fid vm jenv d st1 = .ok (dE, st') ∧
      e = caseE cx nx altEs dE := by
  unfold codeE at h
  cases hv : vm.lookup x with
  | none => simp [hv, liftExcept, throw, throwThe, MonadExceptOf.throw] at h
  | some nx =>
    simp only [hv, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h
    cases hal : altsE cx fid vm jenv alts st with
    | error err => simp [hal] at h
    | ok ares =>
      rcases ares with ⟨altEs, st1⟩
      simp only [hal] at h
      cases hd : optE cx fid vm jenv d st1 with
      | error err => simp [hd] at h
      | ok dres =>
        rcases dres with ⟨dE, st''⟩
        simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨nx, altEs, st1, dE, rfl, rfl, hd, rfl⟩

theorem codeE_ret_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {a : Arg} {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.ret a) st = .ok (e, st')) :
    argE vm a = .ok e ∧ st' = st := by
  unfold codeE at h
  cases ha : argE vm a with
  | error err => simp [ha, liftExcept] at h
  | ok ae =>
    simp only [ha, liftExcept, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem codeE_tcall_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {f : FunId} {as : List Arg} {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv (.tcall f as) st = .ok (e, st')) :
    ∃ fd argEs,
      cx.P.fun? f = some fd ∧
      f < cx.P.size ∧
      as.length = fd.params.length ∧
      argsE vm as = .ok argEs ∧
      e = callE (funName f) argEs ∧
      st' = st := by
  unfold codeE at h
  cases hf : cx.P.fun? f with
  | none => simp [hf, liftExcept, throw, throwThe, MonadExceptOf.throw] at h
  | some fd =>
    simp only [hf] at h
    by_cases hsz : f < cx.P.size
    · simp only [hsz, ↓reduceIte] at h
      by_cases hlen : as.length = fd.params.length
      · simp only [hlen, beq_self_eq_true, ↓reduceIte, bind, StateT.bind, pure, StateT.pure,
          liftExcept, Except.bind, Except.pure] at h
        cases ha : argsE vm as with
        | error err => simp [ha] at h
        | ok argEs =>
          simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨fd, argEs, rfl, hsz, hlen, rfl, rfl, rfl⟩
      · have hbeq : (as.length == fd.params.length) = false := beq_false_of_ne hlen
        simp [hbeq, bind, StateT.bind, liftExcept, throw, throwThe, MonadExceptOf.throw,
          Except.bind] at h
    · simp [hsz, bind, StateT.bind, liftExcept, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h

theorem codeE_trap_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {st st' : LowerState} {e : Expr}
    (h : codeE cx fid vm jenv .trap st = .ok (e, st')) :
    e = trapE "trap" ∧ st' = st := by
  simp only [codeE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem altsE_nil_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {st st' : LowerState} {res : List (CtorKey × Expr)}
    (h : altsE cx fid vm jenv [] st = .ok (res, st')) :
    res = [] ∧ st' = st := by
  simp only [altsE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem altsE_cons_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {k : CtorKey} {b : Code} {rest : List Alt} {st st' : LowerState}
    {res : List (CtorKey × Expr)}
    (h : altsE cx fid vm jenv (.mk k b :: rest) st = .ok (res, st')) :
    ∃ be st1 re,
      codeE cx fid vm jenv b st = .ok (be, st1) ∧
      altsE cx fid vm jenv rest st1 = .ok (re, st') ∧
      res = (k, be) :: re := by
  unfold altsE at h
  simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h
  cases hb : codeE cx fid vm jenv b st with
  | error err => simp [hb] at h
  | ok bres =>
    rcases bres with ⟨be, st1⟩
    simp only [hb] at h
    cases hr : altsE cx fid vm jenv rest st1 with
    | error err => simp [hr] at h
    | ok rres =>
      rcases rres with ⟨re, st''⟩
      simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨be, st1, re, rfl, hr, rfl⟩

theorem optE_none_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {st st' : LowerState} {res : Option Expr}
    (h : optE cx fid vm jenv none st = .ok (res, st')) :
    res = none ∧ st' = st := by
  simp only [optE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem optE_some_inv {cx : Cx} {fid : FunId} {vm : VarMap} {jenv : List JEntryL}
    {c : Code} {st st' : LowerState} {res : Option Expr}
    (h : optE cx fid vm jenv (some c) st = .ok (res, st')) :
    ∃ ce, codeE cx fid vm jenv c st = .ok (ce, st') ∧ res = some ce := by
  unfold optE at h
  simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h
  cases hc : codeE cx fid vm jenv c st with
  | error err => simp [hc] at h
  | ok cres =>
    rcases cres with ⟨ce, st''⟩
    simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ce, rfl, rfl⟩

/- `codeE` only increases `nextLocal` and only appends to `lifted`. -/
mutual

theorem codeE_state_mono (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (c : Code) (st st' : LowerState) (e : Expr),
      codeE cx fid vm jenv c st = .ok (e, st') →
      st.nextLocal ≤ st'.nextLocal ∧ ∃ tail, st'.lifted = st.lifted ++ tail
  | .bind x r k, st, st', e, h => by
    obtain ⟨_, _, _, hk, _⟩ := codeE_bind_inv h
    obtain ⟨hle, tail, hlif⟩ := codeE_state_mono cx fid _ jenv k _ _ _ hk
    exact ⟨by dsimp at hle; omega, tail, hlif⟩
  | .jp j ps isRec body k, st, st', e, h => by
    obtain ⟨be, st2, hb, hk⟩ := codeE_jp_inv h
    obtain ⟨hle1, t1, hlif1⟩ := codeE_state_mono cx fid _ _ body _ _ _ hb
    obtain ⟨hle2, t2, hlif2⟩ := codeE_state_mono cx fid _ _ k _ _ _ hk
    refine ⟨by dsimp at hle1 hle2; omega, t1 ++ [⟨jpFunName fid st.nextJp, [],
      (liveNames vm jenv ++ (List.range ps.length).map (fun i => localName (st.nextLocal + i))).map
        (·, objTy), objTy, be, false⟩] ++ t2, ?_⟩
    simp only [hlif2, hlif1, List.append_assoc]
  | .jmp j as, st, st', e, h => by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := codeE_jmp_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩
  | .case x alts d, st, st', e, h => by
    obtain ⟨_, altEs, st1, dE, _, halts, hd, _⟩ := codeE_case_inv h
    obtain ⟨hle1, t1, hlif1⟩ := altsE_state_mono cx fid vm jenv alts st st1 altEs halts
    obtain ⟨hle2, t2, hlif2⟩ := optE_state_mono cx fid vm jenv d st1 st' dE hd
    exact ⟨Nat.le_trans hle1 hle2, t1 ++ t2, by rw [hlif2, hlif1, List.append_assoc]⟩
  | .ret a, st, st', e, h => by
    obtain ⟨_, rfl⟩ := codeE_ret_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩
  | .tcall f as, st, st', e, h => by
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := codeE_tcall_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩
  | .trap, st, st', e, h => by
    obtain ⟨_, rfl⟩ := codeE_trap_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩

theorem altsE_state_mono (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (alts : List Alt) (st st' : LowerState) (res : List (CtorKey × Expr)),
      altsE cx fid vm jenv alts st = .ok (res, st') →
      st.nextLocal ≤ st'.nextLocal ∧ ∃ tail, st'.lifted = st.lifted ++ tail
  | [], st, st', res, h => by
    obtain ⟨_, rfl⟩ := altsE_nil_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩
  | .mk k b :: rest, st, st', res, h => by
    obtain ⟨be, st1, re, hb, hr, _⟩ := altsE_cons_inv h
    obtain ⟨hle1, t1, hlif1⟩ := codeE_state_mono cx fid vm jenv b st st1 be hb
    obtain ⟨hle2, t2, hlif2⟩ := altsE_state_mono cx fid vm jenv rest st1 st' re hr
    exact ⟨Nat.le_trans hle1 hle2, t1 ++ t2, by rw [hlif2, hlif1, List.append_assoc]⟩

theorem optE_state_mono (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (o : Option Code) (st st' : LowerState) (res : Option Expr),
      optE cx fid vm jenv o st = .ok (res, st') →
      st.nextLocal ≤ st'.nextLocal ∧ ∃ tail, st'.lifted = st.lifted ++ tail
  | none, st, st', res, h => by
    obtain ⟨_, rfl⟩ := optE_none_inv h
    exact ⟨Nat.le_refl _, [], by simp⟩
  | some c, st, st', res, h => by
    obtain ⟨ce, hc, _⟩ := optE_some_inv h
    exact codeE_state_mono cx fid vm jenv c st st' ce hc

end

/-! ## Plainness of Lowered Expressions -/

theorem isPlainExpr_bytesE : ∀ (bs : List UInt8), isPlainExpr (bytesE bs) = true
  | [] => by simp [bytesE, bytesNilE, isPlainExpr, isPlainList]
  | b :: bs => by simp [bytesE, bytesConsE, isPlainExpr, isPlainList, isPlainExpr_bytesE bs]

theorem isPlainExpr_argE {vm : VarMap} {a : Arg} {e : Expr} (h : argE vm a = .ok e) :
    isPlainExpr e = true := by
  cases a with
  | var x =>
    simp only [argE] at h
    cases hv : vm.lookup x <;> simp [hv, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    subst h; simp [vE, isPlainExpr]
  | lit l =>
    cases l with
    | nat n =>
      simp only [argE] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [natE, mk, litE, isPlainExpr, isPlainList]
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | str s =>
      simp only [argE, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [strE, mk, isPlainExpr, isPlainList, isPlainExpr_bytesE]
  | erased =>
    simp only [argE, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [erasedE, mk, isPlainExpr, isPlainList]

theorem isPlainExpr_argsE {vm : VarMap} : ∀ {as : List Arg} {es : List Expr},
    argsE vm as = .ok es → ∀ e ∈ es, isPlainExpr e = true
  | [], es, h => by simp [argsE, List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | a :: as, es, h => by
    simp only [argsE, List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases ha : argE vm a with
    | error _ => simp [ha] at h
    | ok ea =>
      simp only [ha] at h
      cases has : as.mapM (argE vm) with
      | error _ => simp [has] at h
      | ok eas =>
        simp only [has, Except.ok.injEq] at h
        subst h
        intro e he
        rcases List.mem_cons.mp he with rfl | hmem
        · exact isPlainExpr_argE ha
        · exact isPlainExpr_argsE has e hmem

theorem isPlainExpr_trapE (msg : String) : isPlainExpr (trapE msg) = true := by
  simp [trapE, seqE, litE, erasedE, mk, isPlainExpr, isPlainList]

theorem isPlainExpr_projE (cx : Cx) (nx : String) (c : CtorKey) (i : Nat) :
    isPlainExpr (projE cx nx c i) = true := by
  unfold projE
  dsimp only
  generalize hcond :
    ((match cx.ctorEntry? c with
      | some (idx, entry) =>
        if i < entry.arity then
          [(pC (ctorNameOf idx entry.key)
            ((List.range entry.arity).map fun j => if j = i then .bind "q" else .wildcard),
            .load (vE "q"))]
        else []
      | none => []) ++
    if (cx.P.known.natSucc == some c && i == 0) = true then
      [(pN (.bind "q"), matchE (vE "q")
        [(.literal 0, trapE "Nat.zero has no field"),
         (.wildcard, natE (subE (vE "q") (litE 1)))])]
    else []).isEmpty = b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, matchE, vE, isPlainExpr, Bool.true_and, isPlainArms_iff]
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · cases hc : cx.ctorEntry? c with
      | none => simp [hc] at h1
      | some p =>
        simp only [hc] at h1
        split at h1
        · simp only [List.mem_singleton] at h1; subst h1; simp [isPlainExpr]
        · simp at h1
    · split at h2
      · simp only [List.mem_singleton] at h2; subst h2
        simp [trapE, seqE, natE, mk, subE, litE, erasedE,
          isPlainExpr, isPlainList, isPlainArms]
      · simp at h2
  · simp only [↓reduceIte]
    exact isPlainExpr_trapE _

theorem isPlainExpr_rhsE {cx : Cx} {vm : VarMap} {r : Rhs} {e : Expr}
    (h : rhsE cx vm r = .ok e) : isPlainExpr e = true := by
  cases r with
  | arg a => exact isPlainExpr_argE h
  | ctor c as =>
    unfold rhsE at h
    cases hc : cx.ctorEntry? c.key with
    | none => simp [hc] at h
    | some p =>
      simp only [hc] at h
      split at h
      · simp only [bind, Except.bind, pure, Except.pure] at h
        cases ha : argsE vm as with
        | error _ => simp [ha] at h
        | ok es =>
          simp only [ha, Except.ok.injEq] at h
          subst h
          simp only [mk, isPlainExpr, isPlainList_iff, List.mem_map]
          rintro _ ⟨x, hx, rfl⟩
          exact isPlainExpr_argsE ha x hx
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | proj x c i =>
    unfold rhsE at h
    cases hv : vm.lookup x with
    | none => simp [hv] at h
    | some nx =>
      simp only [hv, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact isPlainExpr_projE cx nx c i
  | prim op as =>
    unfold rhsE at h
    cases hp : primFun op with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok pn =>
      simp only [hp, bind, Except.bind, pure, Except.pure] at h
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases ha : argsE vm as with
          | error _ => simp [ha] at h
          | ok es =>
            simp only [ha, Except.ok.injEq] at h
            subst h
            simp only [callE, isPlainExpr, isPlainList_iff]
            exact isPlainExpr_argsE ha
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  | call f as =>
    unfold rhsE at h
    cases hf : cx.P.fun? f with
    | none => simp [hf] at h
    | some fd =>
      simp only [hf, bind, Except.bind, pure, Except.pure] at h
      split at h
      · split at h
        · cases ha : argsE vm as with
          | error _ => simp [ha] at h
          | ok es =>
            simp only [ha, Except.ok.injEq] at h
            subst h
            simp only [callE, isPlainExpr, isPlainList_iff]
            exact isPlainExpr_argsE ha
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem firstPerKey_mem {acc alts : List (CtorKey × Expr)} {p : CtorKey × Expr}
    (h : p ∈ firstPerKey acc alts) : p ∈ acc ∨ p ∈ alts := by
  induction alts generalizing acc with
  | nil => simp [firstPerKey] at h; exact Or.inl h
  | cons hd tl ih =>
    unfold firstPerKey at h
    split at h
    · rcases ih h with hacc | htl
      · exact Or.inl hacc
      · exact Or.inr (List.mem_cons_of_mem _ htl)
    · rcases ih h with hacc | htl
      · rcases List.mem_cons.mp hacc with rfl | hacc'
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hacc'
      · exact Or.inr (List.mem_cons_of_mem _ htl)

private theorem isPlainExpr_ctorArms (cx : Cx) {xs : List (CtorKey × Expr)}
    (hplain : ∀ p ∈ xs, isPlainExpr p.2 = true) :
    ∀ a ∈ ctorArms cx xs, isPlainExpr a.2 = true := by
  induction xs with
  | nil => simp [ctorArms]
  | cons hd tl ih =>
    intro a ha
    unfold ctorArms at ha
    cases hc : cx.ctorEntry? hd.1 with
    | none =>
      simp only [hc] at ha
      exact ih (fun p hp => hplain p (List.mem_cons_of_mem _ hp)) a ha
    | some p =>
      simp only [hc] at ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact hplain hd List.mem_cons_self
      · exact ih (fun p hp => hplain p (List.mem_cons_of_mem _ hp)) a hmem

theorem isPlainExpr_caseE (cx : Cx) (nx : String) {alts : List (CtorKey × Expr)} {d : Option Expr}
    (hal : ∀ p ∈ alts, isPlainExpr p.2 = true)
    (hd : ∀ e, d = some e → isPlainExpr e = true) :
    isPlainExpr (caseE cx nx alts d) = true := by
  have hfirsts : ∀ p ∈ firstPerKey [] alts, isPlainExpr p.2 = true := by
    intro p hp
    rcases firstPerKey_mem hp with hnil | hmem
    · cases hnil
    · exact hal p hmem
  have hfb : isPlainExpr (d.getD (trapE "no alternative")) = true := by
    cases d with
    | none => exact isPlainExpr_trapE _
    | some e => exact hd e rfl
  have hpick : ∀ o : Option CtorKey,
      isPlainExpr (match o with
        | some k => (((firstPerKey [] alts).find? (·.1 == k)).map (·.2)).getD (d.getD (trapE "no alternative"))
        | none => trapE "unpinned Nat literal under case") = true := by
    intro o
    cases o with
    | none => exact isPlainExpr_trapE _
    | some k =>
      dsimp only
      cases hf : (firstPerKey [] alts).find? (·.1 == k) with
      | none => exact hfb
      | some p => exact hfirsts p (List.mem_of_find?_eq_some hf)
  unfold caseE
  simp only [matchE, vE, isPlainExpr, Bool.true_and, isPlainArms_iff]
  intro a ha
  rcases List.mem_append.mp ha with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact isPlainExpr_ctorArms cx hfirsts a h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl | rfl
      · simp only [isPlainExpr, isPlainArms, Bool.true_and, Bool.and_true, Bool.and_eq_true]
        exact ⟨hpick _, hpick _⟩
      · exact isPlainExpr_trapE _
      · exact isPlainExpr_trapE _
  · cases d with
    | none => simp at h3
    | some e =>
      simp only [List.mem_singleton] at h3
      subst h3
      exact hd e rfl

mutual

theorem isPlainExpr_codeE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (c : Code) (st st' : LowerState) (e : Expr),
      codeE cx fid vm jenv c st = .ok (e, st') →
      (∀ g ∈ st.lifted, isPlainExpr g.body = true) →
      isPlainExpr e = true ∧ (∀ g ∈ st'.lifted, isPlainExpr g.body = true)
  | .bind x r k, st, st', e, h, hst => by
    obtain ⟨re, ke, hr, hk, rfl⟩ := codeE_bind_inv h
    obtain ⟨hkp, hlif⟩ := isPlainExpr_codeE cx fid _ jenv k _ _ _ hk hst
    exact ⟨by simp [letE, isPlainExpr, isPlainExpr_rhsE hr, hkp], hlif⟩
  | .jp j ps isRec body k, st, st', e, h, hst => by
    obtain ⟨be, st2, hb, hk⟩ := codeE_jp_inv h
    obtain ⟨hbp, hlif1⟩ := isPlainExpr_codeE cx fid _ _ body _ _ _ hb hst
    have hlif1' : ∀ g ∈ st2.lifted ++ [⟨jpFunName fid st.nextJp, [],
        (liveNames vm jenv ++ (List.range ps.length).map (fun i => localName (st.nextLocal + i))).map
          (·, objTy), objTy, be, false⟩],
        isPlainExpr g.body = true := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hlif1 g h1
      · simp only [List.mem_singleton] at h2; subst h2; exact hbp
    exact isPlainExpr_codeE cx fid _ _ k _ _ _ hk hlif1'
  | .jmp j as, st, st', e, h, hst => by
    obtain ⟨ji, argEs, _, _, ha, rfl, rfl⟩ := codeE_jmp_inv h
    refine ⟨?_, hst⟩
    simp only [callE, isPlainExpr, isPlainList_iff]
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · rw [List.mem_map] at h1; obtain ⟨nm, _, rfl⟩ := h1; simp [vE, isPlainExpr]
    · exact isPlainExpr_argsE ha x h2
  | .case x alts d, st, st', e, h, hst => by
    obtain ⟨nx, altEs, st1, dE, _, halts, hd, rfl⟩ := codeE_case_inv h
    obtain ⟨hap, hlif1⟩ := isPlainExpr_altsE cx fid vm jenv alts st st1 altEs halts hst
    obtain ⟨hdp, hlif2⟩ := isPlainExpr_optE cx fid vm jenv d st1 st' dE hd hlif1
    exact ⟨isPlainExpr_caseE cx nx hap hdp, hlif2⟩
  | .ret a, st, st', e, h, hst => by
    obtain ⟨ha, rfl⟩ := codeE_ret_inv h
    exact ⟨isPlainExpr_argE ha, hst⟩
  | .tcall f as, st, st', e, h, hst => by
    obtain ⟨_, argEs, _, _, _, ha, rfl, rfl⟩ := codeE_tcall_inv h
    refine ⟨?_, hst⟩
    simp only [callE, isPlainExpr, isPlainList_iff]
    exact isPlainExpr_argsE ha
  | .trap, st, st', e, h, hst => by
    obtain ⟨rfl, rfl⟩ := codeE_trap_inv h
    exact ⟨isPlainExpr_trapE _, hst⟩

theorem isPlainExpr_altsE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (alts : List Alt) (st st' : LowerState) (res : List (CtorKey × Expr)),
      altsE cx fid vm jenv alts st = .ok (res, st') →
      (∀ g ∈ st.lifted, isPlainExpr g.body = true) →
      (∀ p ∈ res, isPlainExpr p.2 = true) ∧ (∀ g ∈ st'.lifted, isPlainExpr g.body = true)
  | [], st, st', res, h, hst => by
    obtain ⟨rfl, rfl⟩ := altsE_nil_inv h
    exact ⟨by simp, hst⟩
  | .mk k b :: rest, st, st', res, h, hst => by
    obtain ⟨be, st1, re, hb, hr, rfl⟩ := altsE_cons_inv h
    obtain ⟨hbp, hlif1⟩ := isPlainExpr_codeE cx fid vm jenv b st st1 be hb hst
    obtain ⟨hrp, hlif2⟩ := isPlainExpr_altsE cx fid vm jenv rest st1 st' re hr hlif1
    refine ⟨?_, hlif2⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact hbp
    · exact hrp p hmem

theorem isPlainExpr_optE (cx : Cx) (fid : FunId) (vm : VarMap) (jenv : List JEntryL) :
    ∀ (o : Option Code) (st st' : LowerState) (res : Option Expr),
      optE cx fid vm jenv o st = .ok (res, st') →
      (∀ g ∈ st.lifted, isPlainExpr g.body = true) →
      (∀ e, res = some e → isPlainExpr e = true) ∧ (∀ g ∈ st'.lifted, isPlainExpr g.body = true)
  | none, st, st', res, h, hst => by
    obtain ⟨rfl, rfl⟩ := optE_none_inv h
    exact ⟨(by intro e he; cases he), hst⟩
  | some c, st, st', res, h, hst => by
    obtain ⟨ce, hc, rfl⟩ := optE_some_inv h
    obtain ⟨hcp, hlif⟩ := isPlainExpr_codeE cx fid vm jenv c st st' ce hc hst
    exact ⟨(by intro e he; cases he; exact hcp), hlif⟩

end

theorem isPlainExpr_helpers (cx : Cx) :
    ∀ g ∈ helpers cx, isPlainExpr g.body = true := by
  intro g hg
  unfold helpers at hg
  rcases List.mem_append.mp hg with h1 | h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pAdd, pSub, pMul, divmod, pDiv, pMod, pPred, pBitwise, helper, natPair,
        matchE, letE, seqE, callE, wordE, natE, mk, addE, subE, vE, litE,
        isPlainExpr, isPlainList, isPlainArms]
  · cases hbool : cx.boolNames with
    | none => simp [hbool] at h2
    | some tf =>
      rcases tf with ⟨t, f⟩
      simp only [hbool, boolHelpers, List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl | rfl <;>
        simp [pBeq, pBle, pBlt, helper, natPair, matchE, callE, wordE, mk, subE, vE,
          isPlainExpr, isPlainList, isPlainArms]

theorem isPlainExpr_entryE {P : Program} {i : Nat} {f : FunId} {g : Fn}
    (h : entryE P i f = .ok g) : isPlainExpr g.body = true := by
  unfold entryE at h
  cases hf : P.fun? f with
  | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
  | some fd =>
    simp only [hf] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [callE, isPlainExpr, isPlainList_iff, List.mem_map]
      rintro _ ⟨j, _, rfl⟩
      simp [seqE, wordE, callE, natE, mk, vE, isPlainExpr, isPlainList]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem funE_inv {cx : Cx} {fid : FunId} {fd : Fun} {fns : List Fn}
    (h : funE cx fid fd = .ok fns) :
    let pns := (List.range fd.params.length).map localName
    ∃ body st,
      codeE cx fid (bindVm [] (fd.params.map Prod.fst) pns) [] fd.body
        { nextLocal := fd.params.length, nextJp := 0, lifted := [] } = .ok (body, st) ∧
      fns = { name := funName fid, params := pns.map (·, objTy), result := objTy, body } :: st.lifted := by
  unfold funE at h
  obtain ⟨pns, hpns, hpnsEq⟩ := freshLocals_spec fd.params.length
    ({ nextLocal := 0, nextJp := 0, lifted := [] } : LowerState)
  have hst0 : ({ nextLocal := 0 + fd.params.length, nextJp := 0, lifted := [] } : LowerState) =
      { nextLocal := fd.params.length, nextJp := 0, lifted := [] } := by simp
  have hpns0 : pns = (List.range fd.params.length).map localName := by simpa using hpnsEq
  rw [hst0, hpns0] at hpns
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hpns] at h
  cases hc : codeE cx fid (bindVm [] (fd.params.map Prod.fst)
      ((List.range fd.params.length).map localName)) [] fd.body
      { nextLocal := fd.params.length, nextJp := 0, lifted := [] } with
  | error err => simp [hc] at h
  | ok res =>
    rcases res with ⟨body, st⟩
    simp only [hc, Except.ok.injEq] at h
    exact ⟨body, st, hc, h.symm⟩

theorem isPlainExpr_funE {cx : Cx} {fid : FunId} {fd : Fun} {fns : List Fn}
    (h : funE cx fid fd = .ok fns) : ∀ g ∈ fns, isPlainExpr g.body = true := by
  obtain ⟨body, st, hc, rfl⟩ := funE_inv h
  obtain ⟨hbp, hlif⟩ := isPlainExpr_codeE cx fid _ [] fd.body _ _ _ hc (by simp)
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hmem
  · exact hbp
  · exact hlif g hmem

end IxCC.AiurBackend.Lower
