import IxC.Kernel.Ixon.Shape

namespace Tests.Ix.Kernel.ReaderShape

open _root_.Ix.Kernel _root_.Ix.Kernel.Reader.Shape

private def ty : Ixon.Expr := .sort 0

-- A free variable substituted under a binder must be lifted.
#guard convert #[] (.leanLet false ty (.var 0) (.all ty (.var 1))) ==
  some (.forallE (.sort .zero) (.bvar 1) BinderMeta.leanNever)

-- The inserted value must not be captured by a different, inner let.
#guard convert #[] (.leanLet false ty (.var 0)
  (.leanLet false ty (.var 0) (.app (.var 1) (.var 2)))) ==
  some (.app (.bvar 0) (.bvar 0))

-- A bound variable above the removed let is decremented.
#guard convert #[] (.leanLet true ty (.nat 0) (.app (.var 2) (.var 1))) ==
  some (.app (.bvar 1) (.bvar 0))

-- Reference and recursive-member markers remain disjoint.
#guard head 20 (.const (refKey 7) []) == some (.ref 7)
#guard head 20 (.const (recurKey 7) []) == some (.recur 7)

-- Entries can refer only to earlier entries, with the same raw binder context.
#guard sharing #[.var 0, .share 0, .leanLet false ty (.share 1) (.var 0)] ==
  #[some (.bvar 0), some (.bvar 0), some (.bvar 0)]
#guard sharing #[.share 1, .var 0] == #[none, some (.bvar 0)]
#guard sharing #[.share 0] == #[none]
#guard convert (sharing #[.share 0, .ref 3 #[]]) (.share 1) ==
  some (.const (refKey 3) [])

private def recursor (body : Ixon.Expr) : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
    motives := 1, minors := 0,
    typ := .all (.all (.ref 0 #[]) (.sort 1)) (.all (.ref 0 #[]) body), rules := #[] }

private def record (r : Ixon.Recursor) (entries : Array Ixon.Expr := #[]) : Ixon.Constant :=
  ⟨.recr r, entries, #[], #[], #[]⟩

private def plain := recursor (.app (.var 1) (.var 0))
private def wrapped := recursor
  (.leanLet true (.ref 1 #[]) (.ref 2 #[]) (.app (.var 2) (.var 1)))
private def shared := recursor (.share 2)

#guard analyse 20 (record plain) plain == some (0, #[.ref 0], .ref 0)
#guard analyse 20 (record wrapped) wrapped == some (0, #[.ref 0], .ref 0)
#guard analyse 20 (record shared
  #[.app (.var 2) (.var 1), .leanLet true ty (.nat 0) (.share 0), .share 1]) shared ==
  some (0, #[.ref 0], .ref 0)

end Tests.Ix.Kernel.ReaderShape
