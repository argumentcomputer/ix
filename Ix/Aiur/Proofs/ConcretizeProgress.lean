module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Concretize

/-!
Progress proofs for `Concretize`: predicates characterizing the inputs on
which `typToConcrete` / `termToConcrete` succeed, plus the supporting
progress lemmas. Paired with `Proofs/ConcretizeSound.lean` which proves
semantic preservation.

Companion to `Ix/Aiur/Compiler/Concretize.lean`. Kept out of the
implementation file so the compiler passes can evolve without churn in
the proof layer.
-/

@[expose] public section

namespace Aiur

open Source

/-- Structural predicate: `t` contains no `.mvar` anywhere. The only failure
mode of `typToConcrete` is hitting an `.mvar`, so under `MvarFree t` the
conversion succeeds. -/
inductive Typ.MvarFree : Typ → Prop
  | unit                       : Typ.MvarFree .unit
  | field                      : Typ.MvarFree .field
  | ref (g)                    : Typ.MvarFree (.ref g)
  | pointer {t}  (h : Typ.MvarFree t) : Typ.MvarFree (.pointer t)
  | array {t n}  (h : Typ.MvarFree t) : Typ.MvarFree (.array t n)
  | tuple {ts}   (h : ∀ t ∈ ts, Typ.MvarFree t) : Typ.MvarFree (.tuple ts)
  | app   {g as} (h : ∀ t ∈ as, Typ.MvarFree t) : Typ.MvarFree (.app g as)
  | function {ins out}
      (hi : ∀ t ∈ ins, Typ.MvarFree t)
      (ho : Typ.MvarFree out) : Typ.MvarFree (.function ins out)

/-! ## Typed.Term.MvarFree — reusable predicate

Structural predicate that every `Typ` annotation appearing anywhere in a
`Typed.Term` is `Typ.MvarFree`. Pure; says nothing about pattern shapes or
match forms. -/
inductive Typed.Term.MvarFree : Typed.Term → Prop
  | unit {τ e} (hτ : Typ.MvarFree τ) : MvarFree (.unit τ e)
  | var {τ e x} (hτ : Typ.MvarFree τ) : MvarFree (.var τ e x)
  | ref {τ e g ta} (hτ : Typ.MvarFree τ)
      (hta : ∀ t ∈ ta, Typ.MvarFree t) : MvarFree (.ref τ e g ta)
  | field {τ e g} (hτ : Typ.MvarFree τ) : MvarFree (.field τ e g)
  | tuple {τ e ts} (hτ : Typ.MvarFree τ)
      (hts : ∀ t ∈ ts, MvarFree t) : MvarFree (.tuple τ e ts)
  | array {τ e ts} (hτ : Typ.MvarFree τ)
      (hts : ∀ t ∈ ts, MvarFree t) : MvarFree (.array τ e ts)
  | ret {τ e r} (hτ : Typ.MvarFree τ) (hr : MvarFree r) : MvarFree (.ret τ e r)
  | letT {τ e p v b} (hτ : Typ.MvarFree τ)
      (hv : MvarFree v) (hb : MvarFree b) : MvarFree (.let τ e p v b)
  | matchT {τ e scrut bs} (hτ : Typ.MvarFree τ) (hs : MvarFree scrut)
      (hbs : ∀ pb ∈ bs, MvarFree pb.snd) : MvarFree (.match τ e scrut bs)
  | app {τ e g ta args u} (hτ : Typ.MvarFree τ)
      (hta : ∀ t ∈ ta, Typ.MvarFree t)
      (hargs : ∀ a ∈ args, MvarFree a) : MvarFree (.app τ e g ta args u)
  | add {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.add τ e a b)
  | sub {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.sub τ e a b)
  | mul {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.mul τ e a b)
  | eqZero {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.eqZero τ e a)
  | proj {τ e a n} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.proj τ e a n)
  | get {τ e a n} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.get τ e a n)
  | slice {τ e a i j} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.slice τ e a i j)
  | set {τ e a n v} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hv : MvarFree v) :
      MvarFree (.set τ e a n v)
  | store {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.store τ e a)
  | load {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.load τ e a)
  | ptrVal {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) : MvarFree (.ptrVal τ e a)
  | assertEq {τ e a b r} (hτ : Typ.MvarFree τ)
      (ha : MvarFree a) (hb : MvarFree b) (hr : MvarFree r) :
      MvarFree (.assertEq τ e a b r)
  | ioGetInfo {τ e k} (hτ : Typ.MvarFree τ) (hk : MvarFree k) :
      MvarFree (.ioGetInfo τ e k)
  | ioSetInfo {τ e k i l r} (hτ : Typ.MvarFree τ)
      (hk : MvarFree k) (hi : MvarFree i) (hl : MvarFree l) (hr : MvarFree r) :
      MvarFree (.ioSetInfo τ e k i l r)
  | ioRead {τ e i n} (hτ : Typ.MvarFree τ) (hi : MvarFree i) :
      MvarFree (.ioRead τ e i n)
  | ioWrite {τ e d r} (hτ : Typ.MvarFree τ) (hd : MvarFree d) (hr : MvarFree r) :
      MvarFree (.ioWrite τ e d r)
  | u8BitDecomposition {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8BitDecomposition τ e a)
  | u8ShiftLeft {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8ShiftLeft τ e a)
  | u8ShiftRight {τ e a} (hτ : Typ.MvarFree τ) (ha : MvarFree a) :
      MvarFree (.u8ShiftRight τ e a)
  | u8Xor {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Xor τ e a b)
  | u8Add {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Add τ e a b)
  | u8Sub {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Sub τ e a b)
  | u8And {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8And τ e a b)
  | u8Or {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8Or τ e a b)
  | u8LessThan {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u8LessThan τ e a b)
  | u32LessThan {τ e a b} (hτ : Typ.MvarFree τ) (ha : MvarFree a) (hb : MvarFree b) :
      MvarFree (.u32LessThan τ e a b)
  | debug {τ e l t r} (hτ : Typ.MvarFree τ)
      (ht : ∀ sub, t = some sub → MvarFree sub) (hr : MvarFree r) :
      MvarFree (.debug τ e l t r)

/-- A `Source.Pattern` is *simple* iff `subPatternsToLocals` / `expandPattern`
accept it: only `.var`/`.wildcard` at any leaf, `.ref/.tuple/.array` with
such leaves, and `.or` of simples. No `.pointer` sub-patterns (must have been
eliminated by the match compiler). -/
inductive Pattern.Simple : Pattern → Prop
  | var (x) : Simple (.var x)
  | wildcard : Simple .wildcard
  | field (g) : Simple (.field g)
  | refCtor {g ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.ref g ps)
  | tup {ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.tuple ps)
  | arr {ps} (h : ∀ p ∈ ps, p = .wildcard ∨ ∃ x, p = .var x) :
      Simple (.array ps)
  | orP {a b} (ha : Simple a) (hb : Simple b) : Simple (.or a b)

/-- Compound predicate used by `termToConcrete_ok_of_concretizeReady`:
`MvarFree` + structural shape constraints that match what `termToConcrete`
currently requires (simplify-pass output). -/
inductive Typed.Term.ConcretizeReady : Typed.Term → Prop
  | unit {τ e} : ConcretizeReady (.unit τ e)
  | var {τ e x} : ConcretizeReady (.var τ e x)
  | ref {τ e g ta} : ConcretizeReady (.ref τ e g ta)
  | field {τ e g} : ConcretizeReady (.field τ e g)
  | tuple {τ e ts} (hts : ∀ t ∈ ts, ConcretizeReady t) :
      ConcretizeReady (.tuple τ e ts)
  | array {τ e ts} (hts : ∀ t ∈ ts, ConcretizeReady t) :
      ConcretizeReady (.array τ e ts)
  | ret {τ e r} (hr : ConcretizeReady r) : ConcretizeReady (.ret τ e r)
  | letT {τ e p v b} (hv : ConcretizeReady v) (hb : ConcretizeReady b) :
      ConcretizeReady (.let τ e p v b)
  | matchT {τ e sx st se bs}
      (hps : ∀ pb ∈ bs, Pattern.Simple pb.fst)
      (hbs : ∀ pb ∈ bs, ConcretizeReady pb.snd) :
      ConcretizeReady (.match τ e (.var st se sx) bs)
  | app {τ e g ta args u} (hargs : ∀ a ∈ args, ConcretizeReady a) :
      ConcretizeReady (.app τ e g ta args u)
  | add {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.add τ e a b)
  | sub {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.sub τ e a b)
  | mul {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.mul τ e a b)
  | eqZero {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.eqZero τ e a)
  | proj {τ e a n} (ha : ConcretizeReady a) : ConcretizeReady (.proj τ e a n)
  | get {τ e a n} (ha : ConcretizeReady a) : ConcretizeReady (.get τ e a n)
  | slice {τ e a i j} (ha : ConcretizeReady a) : ConcretizeReady (.slice τ e a i j)
  | set {τ e a n v} (ha : ConcretizeReady a) (hv : ConcretizeReady v) :
      ConcretizeReady (.set τ e a n v)
  | store {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.store τ e a)
  | load {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.load τ e a)
  | ptrVal {τ e a} (ha : ConcretizeReady a) : ConcretizeReady (.ptrVal τ e a)
  | assertEq {τ e a b r} (ha : ConcretizeReady a) (hb : ConcretizeReady b)
      (hr : ConcretizeReady r) : ConcretizeReady (.assertEq τ e a b r)
  | ioGetInfo {τ e k} (hk : ConcretizeReady k) : ConcretizeReady (.ioGetInfo τ e k)
  | ioSetInfo {τ e k i l r} (hk : ConcretizeReady k) (hi : ConcretizeReady i)
      (hl : ConcretizeReady l) (hr : ConcretizeReady r) :
      ConcretizeReady (.ioSetInfo τ e k i l r)
  | ioRead {τ e i n} (hi : ConcretizeReady i) : ConcretizeReady (.ioRead τ e i n)
  | ioWrite {τ e d r} (hd : ConcretizeReady d) (hr : ConcretizeReady r) :
      ConcretizeReady (.ioWrite τ e d r)
  | u8BitDecomposition {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8BitDecomposition τ e a)
  | u8ShiftLeft {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8ShiftLeft τ e a)
  | u8ShiftRight {τ e a} (ha : ConcretizeReady a) :
      ConcretizeReady (.u8ShiftRight τ e a)
  | u8Xor {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Xor τ e a b)
  | u8Add {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Add τ e a b)
  | u8Sub {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Sub τ e a b)
  | u8And {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8And τ e a b)
  | u8Or {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8Or τ e a b)
  | u8LessThan {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u8LessThan τ e a b)
  | u32LessThan {τ e a b} (ha : ConcretizeReady a) (hb : ConcretizeReady b) :
      ConcretizeReady (.u32LessThan τ e a b)
  | debug {τ e l t r} (ht : ∀ sub, t = some sub → ConcretizeReady sub)
      (hr : ConcretizeReady r) : ConcretizeReady (.debug τ e l t r)

/-! ## Progress lemma: `termToConcrete` succeeds on `ConcretizeReady` terms. -/



end Aiur

end -- @[expose] public section
