/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.Literals

/-! # Ordinary fields after recursive fields

`E` has a constructor whose ordinary field follows a recursive one, as Lean's
`Linear.Expr.mulR` and the `.below` families do. It is admitted through its
canonical block and wrapper terms (`checkInterleavedC`). -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary Ix.Kernel.Inductive
open Tests.Ix.Kernel.Literals

namespace Tests.Ix.Kernel.Interleaved

abbrev E := VExpr String

def eC : E := .const (.member "E" 0) []
def leafC : E := .const (.ctor "E" 0 0) []
def nodeC : E := .const (.ctor "E" 0 1) []
def recC : E := .const (.member "E" 1) [.param 0]

/-- `node : E → Nat → E`: the recursive field comes first. -/
def family : Const String :=
  .induct 0 0 0 (.sort (.succ .zero))
    [⟨0, 0, 0, eC, .safe⟩, ⟨0, 0, 2, .forallE eC (.forallE natC eC), .safe⟩] .safe

def motiveT : E := .forallE eC (.sort (.param 0))
def leafT : E := .app (.bvar 0) leafC
def nodeT : E :=
  .forallE eC (.forallE natC (.forallE (.app (.bvar 3) (.bvar 1))
    (.app (.bvar 4) (.app (.app nodeC (.bvar 2)) (.bvar 1)))))
def recType : E :=
  .forallE motiveT (.forallE leafT (.forallE nodeT (.forallE eC (.app (.bvar 3) (.bvar 0)))))
def leafRule : E := .lam motiveT (.lam leafT (.lam nodeT (.bvar 1)))
def nodeRule : E :=
  .lam motiveT (.lam leafT (.lam nodeT (.lam eC (.lam natC
    (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.app recC (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)))))))

def recursor : Const String :=
  .recursor 1 0 0 1 2 recType [⟨0, leafRule⟩, ⟨2, nodeRule⟩] false .safe

def eDecl : Decl String := ⟨"E", ⟨[family, recursor]⟩⟩

def outcome (decls : List (Decl String)) : String :=
  match run decls with
  | .ok _ => "ok"
  | .error (.declined r) => s!"declined: {r}"
  | .error (.rejected r) => s!"rejected: {r}"

#guard outcome [natDecl, eDecl] == "ok"

/-- `size t` adds the `Nat` fields: iota through the declared recursor's rules. -/
def recC1 : E := .const (.member "E" 1) [.succ .zero]
def sizeDecl : Decl String := ⟨"size", ⟨[.defn 0 .definition (.forallE eC natC)
  (.lam eC (.app (.app (.app (.app recC1 (.lam eC natC)) (.natLit natRef 0))
    (.lam eC (.lam natC (.lam natC (app2 addC (.bvar 0) (.bvar 1)))))) (.bvar 0))) .safe]⟩⟩
def sizeC : E := .const (.member "size" 0) []
def node (a : E) (k : Nat) : E := .app (.app nodeC a) (.natLit natRef k)
def sizeFive : Decl String := thm "sizeFive"
  (eqNat (.app sizeC (node (node leafC 2) 3)) (.natLit natRef 5)) (reflNat (.natLit natRef 5))
def sizeWrong : Decl String := thm "sizeWrong"
  (eqNat (.app sizeC (node (node leafC 2) 3)) (.natLit natRef 6)) (reflNat (.natLit natRef 6))

#guard accepts [natDecl, eqDecl, addDecl, eDecl, sizeDecl, sizeFive]
#guard declines [natDecl, eqDecl, addDecl, eDecl, sizeDecl, sizeWrong]
  "body conversion: conversion search did not establish equality"

end Tests.Ix.Kernel.Interleaved
