module
public import Ix.Compile.Canon.NameTable
public section

namespace Ix.Compile.Canon

/-- A bound strictly above every numeric component. Only source names in
the block reference closure and previously allocated roots are read. -/
def nameNumeralBound : Lean.Name → Nat
  | .anonymous => 0
  | .str p _ => nameNumeralBound p
  | .num p n => max (nameNumeralBound p) (n + 1)

def numeralBound : List Lean.Name → Nat
  | [] => 0
  | n :: ns => max (nameNumeralBound n) (numeralBound ns)

def familyFree (names : List Lean.Name) (root : Lean.Name) : Bool :=
  names.all fun n => !root.isPrefixOf n

/-- Keep the historical string component when its entire suffix family
is unused. A collision uses a fresh numeric namespace under the same
block-local parent; the auxiliary itself still ends in the old string. -/
def freshFamily (names : List Lean.Name) (parent : Ix.Name) (label : String) : Ix.Name :=
  let candidate := Ix.Name.mkStr parent label
  if familyFree names (keyName candidate) then candidate
  else Ix.Name.mkStr (Ix.Name.mkNat parent (numeralBound names)) label

/-- Suffix families which auxiliary generation may install later. Protecting
these roots also protects their `go`, `eq`, constructor and cases suffixes. -/
def auxSuffixFamilies (aux : Ix.Name) : List Lean.Name :=
  ["rec", "recOn", "casesOn", "below", "brecOn"].map fun s => .str (keyName aux) s

/-- A constructor candidate must not enter or contain a future auxiliary
suffix family. Source spellings and previously allocated constructors are
forbidden by the separate `familyFree` check. -/
def ctorFamilyFree (forbidden : List Lean.Name) (aux candidate : Ix.Name)
    (ctorRoots : List Lean.Name := []) : Bool :=
  familyFree (keyName aux :: forbidden) (keyName candidate) &&
    (auxSuffixFamilies aux).all (fun root =>
      !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root) &&
    ctorRoots.all (fun root =>
      !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root)

/-- Keep the existing prefix-rewrite candidate when its family is available.
A non-prefix source constructor is already forbidden by the source closure,
so it receives a deterministic child family without a prefix premise. -/
def freshCtorFamily (forbidden : List Lean.Name) (aux candidate : Ix.Name) (index : Nat)
    (ctorRoots : List Lean.Name := []) : Ix.Name :=
  if ctorFamilyFree forbidden aux candidate ctorRoots then candidate
  else
    let reserved := keyName aux :: auxSuffixFamilies aux ++ ctorRoots ++ forbidden
    Ix.Name.mkStr (Ix.Name.mkNat aux (numeralBound reserved)) s!"_ctor_{index}"

end Ix.Compile.Canon
