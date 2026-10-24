/-
  pass3-core-unit: the Pass 3 core without the driver (`Ix.Compile.Pass`).

  * the call-site rewrite (`Translate`): a full application is inlined, under
    a record with its placeholder and source; a bare occurrence stays; extra
    arguments stay applied; an unchanged term is returned as given; an
    exhausted bound is the error naming it; the memo is keyed exactly (a
    term that only shares a digest with a cached one is rewritten for
    itself) and by the definition site (one occurrence in a definition's
    type and value is two records, as in Rust); `rewriteBlock`'s overlay is
    exactly the changed members;
  * the side-car (`SideCar`): every registration with a display name moves
    to it, with its metadata renamed;
  * the memo shape (`Memo`): hit, miss, check mode, first entry wins;
  * the views' equality (`ImageView`): every field but the spec's naming.

  The views themselves (`buildView`, `BlockView.image`) need Pass 2's
  recursors, hence the driver: the `pass3` suite covers them; `image-gen`
  covers the generator underneath.
-/
import LSpec
import Ix.Compile.Pass.Translate
import Ix.Compile.Pass.ImageView
import Ix.Compile.Pass.SideCar
import Ix.Compile.Pass.Memo

namespace Tests.Ix.Compile.Pass3Core
open LSpec
open _root_.Ix (Name Expr Level ConstantInfo DataValue)
open _root_.Ix.Compile.Pass
open _root_.Ix.Compile.ExactKey (ExactName exprEq nameEq)

def nm (s : String) : Name := Name.mkStr Name.mkAnon s
def cst (s : String) : Expr := Expr.mkConst (nm s) #[]

/-- `h`: an image-kind head of arity 1 whose expansion is `fun x => x`. -/
def lookup (n : Name) : Except String (Option Expansion) :=
  .ok (if n == nm "h" then some {
    levelParams := #[], value := Expr.mkLam (nm "x") (cst "T") (Expr.mkBVar 0) .default
    arity := 1, needsRewrite := false
  } else none)

def run (m : RwM α) (cfg : RwConfig := {}) : Except String (α × RwState) :=
  (m.run cfg).run {}

def fullApp : Expr := Expr.mkApp (cst "h") (cst "a")

def rewrites (record : Bool) (e : Expr) (cfg : RwConfig := {}) : Except String ((Expr × Bool) × RwState) :=
  run (rw lookup rewriteFuel record e) cfg

def inlines : Bool :=
  match rewrites false fullApp with
  | .ok ((r, changed), st) => exprEq r (cst "a") && changed && st.sources.isEmpty
  | .error _ => false

def records : Bool :=
  match rewrites true fullApp { base := 5 } with
  | .ok ((r, changed), st) =>
    exprEq r (Expr.mkMData #[(inlineKey, .ofNat 5)] (cst "a")) && changed &&
      st.sources.size == 1 && (st.sources[0]?.map (exprEq · fullApp)).getD false
  | .error _ => false

def bareStays : Bool :=
  match rewrites true (cst "h") with
  | .ok ((r, changed), st) => exprEq r (cst "h") && !changed && st.sources.isEmpty
  | .error _ => false

def extraArgs : Bool :=
  match rewrites false (Expr.mkApp fullApp (cst "b")) with
  | .ok ((r, changed), _) => exprEq r (Expr.mkApp (cst "a") (cst "b")) && changed
  | .error _ => false

def unchanged : Bool :=
  let e := Expr.mkApp (cst "g") (cst "a")
  match rewrites true e with
  | .ok ((r, changed), st) => exprEq r e && !changed && st.sources.isEmpty
  | .error _ => false

def exhausted : Bool :=
  let deep := Expr.mkApp (cst "g") (Expr.mkApp (cst "g") (cst "a"))
  let atZero := match run (rw lookup 0 false fullApp) with
    | .error msg => msg == rewriteExhausted
    | .ok _ => false
  let atOne := match run (rw lookup 1 false deep) with
    | .error msg => msg == rewriteExhausted
    | .ok _ => false
  atZero && atOne

/-- A term forged with the digest of a rewritten one is rewritten for itself:
`h b` stored under `h a`'s digest gives `b`, never the cached `a`. -/
def exactMemo : Bool :=
  let forged : Expr := .app (cst "h") (cst "b") fullApp.getHash
  let both : RwM (Expr × Expr) := do
    let (x, _) ← rw lookup rewriteFuel false fullApp
    let (y, _) ← rw lookup rewriteFuel false forged
    pure (x, y)
  match run both with
  | .ok ((x, y), _) => exprEq x (cst "a") && exprEq y (cst "b")
  | .error _ => false

def defn (n : String) (value : Expr) : ConstantInfo :=
  .defnInfo { cnst := { name := nm n, levelParams := #[], type := cst "T" }, value,
              hints := .abbrev, safety := .safe, all := #[nm n] }

def overlayExact : Bool :=
  match rewriteBlock lookup #[(nm "m1", defn "m1" fullApp), (nm "m2", defn "m2" (cst "a"))]
      { base := 3 } with
  | .ok r =>
    r.overlay.size == 1 && (r.overlay[0]?.map (fun (n, _) => nameEq n (nm "m1"))).getD false &&
      r.sources.size == 1 && r.canon.isEmpty && r.pjForms.isEmpty &&
      (match r.overlay[0]? with
       | some (_, ConstantInfo.defnInfo v) => exprEq v.value (Expr.mkMData #[(inlineKey, .ofNat 3)] (cst "a"))
       | _ => false)
  | .error _ => false

/-- The memo is keyed by the definition site (`RwKey`): one occurrence in a
definition's type and value gets two placeholders (the type's is never the
value's record), as does one occurrence in two members' values; the members'
types share one. The Rust rewrite pins the same (`pass3::translate`'s
`definition_value_is_its_own_site`); a structural recursion functional
`T.size._f : (x : T) → T.below … x → Nat := fun x (f : T.below … x) => …` has
this shape. -/
def siteKeyed : Bool :=
  let ty := Expr.mkApp (cst "f") fullApp
  let member (n : String) : Name × ConstantInfo :=
    (nm n, .defnInfo { cnst := { name := nm n, levelParams := #[], type := ty }, value := ty,
                       hints := .abbrev, safety := .safe, all := #[nm n] })
  let ph (k : Nat) : Expr := Expr.mkApp (cst "f") (Expr.mkMData #[(inlineKey, .ofNat k)] (cst "a"))
  match rewriteBlock lookup #[member "m1", member "m2"] with
  | .ok r =>
    r.sources.size == 3 && r.sources.all (exprEq · fullApp) &&
      (match r.overlay with
       | #[(_, .defnInfo v1), (_, .defnInfo v2)] =>
         exprEq v1.cnst.type (ph 0) && exprEq v1.value (ph 1) &&
           exprEq v2.cnst.type (ph 0) && exprEq v2.value (ph 2)
       | _ => false)
  | .error _ => false

/-! ### The side-car -/

def leanRec : Name := Name.mkStr (nm "A") "rec"
def displayRec : Name := Name.mkStr (Name.mkStr (nm "A") ixComponent) "rec"
def addr (b : UInt8) : Address := ⟨⟨Array.replicate 32 b⟩⟩

def entry (self : Name) : _root_.Ixon.Named :=
  { addr := addr 1
    constMeta := { info := .defn self.getHash #[] #[self.getHash] #[]
                     { nodes := #[.ref leanRec.getHash] } 0 0 } }

def sideCarMoves : Bool :=
  let edit : SideCarEdit := { display := ({} : Std.HashMap ExactName Name).insert leanRec displayRec }
  let other := nm "other"
  let named := #[(leanRec, entry leanRec), (other, entry other)]
  let n2a : Std.HashMap ExactName Address := (({} : Std.HashMap ExactName Address).insert leanRec (addr 1)).insert other (addr 2)
  let extra : Std.HashSet Name := ({} : Std.HashSet Name).insert leanRec |>.insert other
  let (named', n2a', extra') := edit.apply named n2a extra
  let renamedSelf := match named'[0]? with
    | some (n, nd) => nameEq n displayRec &&
        nd.constMeta.info == .defn displayRec.getHash #[] #[displayRec.getHash] #[]
          { nodes := #[.ref displayRec.getHash] } 0 0
    | none => false
  let renamedRef := match named'[1]? with
    | some (n, nd) => nameEq n other &&
        nd.constMeta.info == .defn other.getHash #[] #[other.getHash] #[]
          { nodes := #[.ref displayRec.getHash] } 0 0
    | none => false
  renamedSelf && renamedRef && named'.size == 2 &&
    n2a'.get? displayRec == some (addr 1) && !n2a'.contains leanRec &&
    n2a'.get? other == some (addr 2) && !extra'.contains leanRec && extra'.contains other

/-! ### The memo shape -/

/-- `x` is `.ok n`. -/
def okIs (x : Except String Nat) (n : Nat) : Bool :=
  match x with
  | .ok m => m == n
  | .error _ => false

def memoShape : Bool :=
  let k : ExactName := nm "k"
  let j : ExactName := nm "j"
  let table : Std.HashMap ExactName Nat := ({} : Std.HashMap ExactName Nat).insert k 1
  let hit := okIs (memoLookup table false "t" k (fun _ => .ok 2)) 1
  let miss := okIs (memoLookup table false "t" j (fun _ => .ok 2)) 2
  let agree := okIs (memoLookup table true "t" k (fun _ => .ok 1)) 1
  let differ := match memoLookup table true "t" k (fun _ => .ok 2) with
    | .error _ => true
    | .ok _ => false
  let merged := memoMerge table #[(k, 5), (j, 3), (j, 4)]
  hit && miss && agree && differ && merged[k]? == some 1 && merged[j]? == some 3

/-! ### The views' equality -/

def emptyView (naming : _root_.Ix.Compile.Image.Naming) (back : Std.HashMap Name Name) : BlockView :=
  { all := #[nm "A"], canon := { all := #[nm "A"], components := #[] }
    spec := { block := { all := #[nm "A"], components := #[] }, tyMap := {}, ctorMap := {},
              canonInds := #[], decls := #[], naming }
    canonConsts := {}, back }

def viewEq : Bool :=
  let back := ({} : Std.HashMap Name Name).insert (nm "A._ix") (nm "A")
  (emptyView viewNaming back == emptyView _root_.Ix.Compile.Image.Naming.default back) &&
    !(emptyView viewNaming back == emptyView viewNaming {})

def suite : List TestSeq := [
  test "a full application is inlined" inlines,
  test "a recorded full application carries its placeholder and source" records,
  test "a bare occurrence stays as written" bareStays,
  test "arguments beyond the arity stay applied" extraArgs,
  test "an unchanged term is returned as given" unchanged,
  test "an exhausted bound is the error naming it" exhausted,
  test "the rewrite memo is keyed exactly" exactMemo,
  test "the overlay is exactly the changed members" overlayExact,
  test "the rewrite memo is keyed by the definition site" siteKeyed,
  test "the side-car moves every registration with a display name" sideCarMoves,
  test "memo lookup, check mode and merge" memoShape,
  test "views compare every field but the spec's naming" viewEq]

end Tests.Ix.Compile.Pass3Core
