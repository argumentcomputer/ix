module
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Compiler.Concretize
public import Ix.IndexMap

/-!
Structural invariants on `Concrete.Decls` types / terms / declarations.

All `Prop` definitions live here (with `@[expose] section` wrapping) so
downstream proof files can `unfold` freely without scattering attributes.
-/

public section
@[expose] section

namespace Aiur

/-- A concrete type is *first-order* iff it contains no `.function` constructor.
Parallels `Typ.FirstOrder` on typed types. Since `Concrete.Typ.ref g` points
into `cd`, first-orderness alone doesn't rule out `g` being a function key —
that's enforced at the `FirstOrderReturn` level, which quantifies over the
specific decls. -/
inductive Concrete.Typ.FirstOrder : Concrete.Typ → Prop
  | unit : FirstOrder .unit
  | field : FirstOrder .field
  | ref (g) : FirstOrder (.ref g)
  | tuple {ts} : (∀ t ∈ ts, FirstOrder t) → FirstOrder (.tuple ts)
  | array {t n} : FirstOrder t → FirstOrder (.array t n)
  | pointer {t} : FirstOrder t → FirstOrder (.pointer t)

/-- First-order return condition on concrete decls. Every function has
a first-order return type; required to rule out `.fn`-valued returns via
`.ref g` where `g` is a function key. -/
def Concrete.Decls.FirstOrderReturn (cd : Concrete.Decls) : Prop :=
  ∀ g f, cd.getByKey g = some (.function f) → Concrete.Typ.FirstOrder f.output

/-- Every `.ref g` in a `Concrete.Typ` resolves to a `.dataType` in `cd`. -/
inductive Concrete.Typ.RefClosed (cd : Concrete.Decls) : Concrete.Typ → Prop
  | unit    : RefClosed cd .unit
  | field   : RefClosed cd .field
  | pointer {inner} (h : RefClosed cd inner) : RefClosed cd (.pointer inner)
  | function {ins out} : RefClosed cd (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, RefClosed cd t) : RefClosed cd (.tuple ts)
  | array {t n} (h : RefClosed cd t) : RefClosed cd (.array t n)
  | ref {g} (hdt : ∃ dt, cd.getByKey g = some (.dataType dt)) : RefClosed cd (.ref g)

/-- Every type in a `Concrete.Declaration` has `RefClosed`. -/
def Concrete.Declaration.RefClosed (cd : Concrete.Decls) (d : Concrete.Declaration) : Prop :=
  match d with
  | .function f =>
      (∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd) ∧
      Concrete.Typ.RefClosed cd f.output
  | .dataType dt =>
      ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t
  | .constructor _ c =>
      ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t

/-- All declarations in `cd` are ref-closed w.r.t. `cd`. -/
def Concrete.Decls.RefClosed (cd : Concrete.Decls) : Prop :=
  ∀ name d, cd.getByKey name = some d → Concrete.Declaration.RefClosed cd d

/-- Every `.ref g` **term** subterm of a `Concrete.Term` has `g` keyed to
a `.dataType _` or `.constructor _ _` in `cd` — NOT a function. Rules
out the `.ref g ↦ .fn g` counterexample for `runFunction_preserves_FnFree`. -/
inductive Concrete.Term.RefsDt (cd : Concrete.Decls) : Concrete.Term → Prop
  | unit  {typ e} : RefsDt cd (.unit typ e)
  | var   {typ e l} : RefsDt cd (.var typ e l)
  | ref   {typ e g}
      (hdt : (∃ dt, cd.getByKey g = some (.dataType dt)) ∨
             (∃ dt c, cd.getByKey g = some (.constructor dt c))) :
      RefsDt cd (.ref typ e g)
  | field {typ e g} : RefsDt cd (.field typ e g)
  | tuple {typ e ts} (h : ∀ sub ∈ ts, RefsDt cd sub) :
      RefsDt cd (.tuple typ e ts)
  | array {typ e ts} (h : ∀ sub ∈ ts, RefsDt cd sub) :
      RefsDt cd (.array typ e ts)
  | ret   {typ e sub} (h : RefsDt cd sub) : RefsDt cd (.ret typ e sub)
  | letVar {typ e l v b}
      (hv : RefsDt cd v) (hb : RefsDt cd b) : RefsDt cd (.letVar typ e l v b)
  | letWild {typ e v b}
      (hv : RefsDt cd v) (hb : RefsDt cd b) : RefsDt cd (.letWild typ e v b)
  | letLoad {typ e dst dstTyp src b}
      (hb : RefsDt cd b) : RefsDt cd (.letLoad typ e dst dstTyp src b)
  | match {typ e scrut cases defaultOpt}
      (hcases : ∀ pc ∈ cases, RefsDt cd pc.2)
      (hdef : ∀ d, defaultOpt = some d → RefsDt cd d) :
      RefsDt cd (.match typ e scrut cases defaultOpt)
  | app {typ e g args u} (hargs : ∀ a ∈ args, RefsDt cd a) :
      RefsDt cd (.app typ e g args u)
  | add {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) :
      RefsDt cd (.add typ e a b)
  | sub {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) :
      RefsDt cd (.sub typ e a b)
  | mul {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) :
      RefsDt cd (.mul typ e a b)
  | eqZero {typ e a} (ha : RefsDt cd a) : RefsDt cd (.eqZero typ e a)
  | proj {typ e a n} (ha : RefsDt cd a) : RefsDt cd (.proj typ e a n)
  | get {typ e a n} (ha : RefsDt cd a) : RefsDt cd (.get typ e a n)
  | slice {typ e a i j} (ha : RefsDt cd a) : RefsDt cd (.slice typ e a i j)
  | set {typ e a n v} (ha : RefsDt cd a) (hv : RefsDt cd v) :
      RefsDt cd (.set typ e a n v)
  | store {typ e a} (ha : RefsDt cd a) : RefsDt cd (.store typ e a)
  | load {typ e a} (ha : RefsDt cd a) : RefsDt cd (.load typ e a)
  | ptrVal {typ e a} (ha : RefsDt cd a) : RefsDt cd (.ptrVal typ e a)
  | assertEq {typ e a b r} (ha : RefsDt cd a) (hb : RefsDt cd b) (hr : RefsDt cd r) :
      RefsDt cd (.assertEq typ e a b r)
  | ioGetInfo {typ e k} (hk : RefsDt cd k) : RefsDt cd (.ioGetInfo typ e k)
  | ioSetInfo {typ e k i l r}
      (hk : RefsDt cd k) (hi : RefsDt cd i) (hl : RefsDt cd l) (hr : RefsDt cd r) :
      RefsDt cd (.ioSetInfo typ e k i l r)
  | ioRead {typ e i n} (hi : RefsDt cd i) : RefsDt cd (.ioRead typ e i n)
  | ioWrite {typ e d r} (hd : RefsDt cd d) (hr : RefsDt cd r) :
      RefsDt cd (.ioWrite typ e d r)
  | u8BitDecomposition {typ e a} (ha : RefsDt cd a) : RefsDt cd (.u8BitDecomposition typ e a)
  | u8ShiftLeft  {typ e a} (ha : RefsDt cd a) : RefsDt cd (.u8ShiftLeft  typ e a)
  | u8ShiftRight {typ e a} (ha : RefsDt cd a) : RefsDt cd (.u8ShiftRight typ e a)
  | u8Xor {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) : RefsDt cd (.u8Xor typ e a b)
  | u8Add {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) : RefsDt cd (.u8Add typ e a b)
  | u8Sub {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) : RefsDt cd (.u8Sub typ e a b)
  | u8And {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) : RefsDt cd (.u8And typ e a b)
  | u8Or  {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) : RefsDt cd (.u8Or  typ e a b)
  | u8LessThan  {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) :
      RefsDt cd (.u8LessThan typ e a b)
  | u32LessThan {typ e a b} (ha : RefsDt cd a) (hb : RefsDt cd b) :
      RefsDt cd (.u32LessThan typ e a b)
  | debug {typ e label t r}
      (ht : ∀ tval, t = some tval → RefsDt cd tval) (hr : RefsDt cd r) :
      RefsDt cd (.debug typ e label t r)

/-- Every function body in `cd` syntactically respects `RefsDt`. -/
def Concrete.Decls.TermRefsDt (cd : Concrete.Decls) : Prop :=
  ∀ g f, cd.getByKey g = some (.function f) → Concrete.Term.RefsDt cd f.body

/-- Every `.ref g'` appearing in the non-`.pointer`/`.function` spine of a
concrete type has `rank g' < bd`. `.pointer` / `.function` break the spine
because `sizeBound` returns 1 immediately on both. -/
inductive Concrete.Typ.SpineRefsBelow (rank : Global → Nat) (bd : Nat) :
    Concrete.Typ → Prop
  | unit    : SpineRefsBelow rank bd .unit
  | field   : SpineRefsBelow rank bd .field
  | pointer (t) : SpineRefsBelow rank bd (.pointer t)
  | function (ins out) : SpineRefsBelow rank bd (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, SpineRefsBelow rank bd t) :
      SpineRefsBelow rank bd (.tuple ts)
  | array {t n} (h : SpineRefsBelow rank bd t) :
      SpineRefsBelow rank bd (.array t n)
  | ref {g} (h : rank g < bd) : SpineRefsBelow rank bd (.ref g)

/-- Template correspondence: cd-dt at `g` originates from tds-dt
`templateDt` at `templateName`, via mangling
`concretizeName templateName args = g`. Used by
`concretize_preserves_direct_dag` to transport rank from source to cd. -/
def DirectDagBody.TemplateOf (tds : Typed.Decls) (cd : Concrete.Decls)
    (g : Global) (templateName : Global) (templateDt : DataType) : Prop :=
  tds.getByKey templateName = some (.dataType templateDt) ∧
  (∃ (cdt : Concrete.DataType), cd.getByKey g = some (.dataType cdt)) ∧
  ∃ (args : Array Typ), concretizeName templateName args = g

/-- Rank-transport predicate linking source-side rank to cd-side rank via
`templateOf`. -/
def DirectDagBody.RankTransport (tds : Typed.Decls) (cd : Concrete.Decls)
    (rank_src : Global → Nat) (rank_cd : Global → Nat) : Prop :=
  ∀ g templateName templateDt,
    DirectDagBody.TemplateOf tds cd g templateName templateDt →
    rank_cd g = rank_src templateName

end Aiur

end -- @[expose] section
end -- public section
