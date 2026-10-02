import Ix.Kernel.Ref
import Ix.Kernel.Search
import Ix.Kernel.Ingress.Records

/-! # Projection records from kernel references

The exact projection-record reading and writer that projection
reconstruction (`Ixon.Projection`) and canonical block order
(`Ixon.BlockOrder`) run: a projection record is its variant and the
member/constructor position of its owner block, with empty tables. -/

namespace Ix.Kernel.Egress

/-- Only the projection variant is layout; the block/member/constructor
identity is rebuilt from its kernel reference. -/
inductive ProjectionLayout where
  | definition
  | inductive
  | recursor
  | constructor
  deriving DecidableEq, Repr

/-- Structural projection reading. Owner existence and member kind are
validated against the supplied store by the record-level reader/writer. -/
inductive ProjectionReads : Ixon.Constant → ProjectionLayout → ConstRef Address → Prop where
  | definition (p : Ixon.DefinitionProj) :
      ProjectionReads ⟨.dPrj p, #[], #[], #[]⟩ .definition (.member p.block p.idx.toNat)
  | inductive (p : Ixon.InductiveProj) :
      ProjectionReads ⟨.iPrj p, #[], #[], #[]⟩ .inductive (.member p.block p.idx.toNat)
  | recursor (p : Ixon.RecursorProj) :
      ProjectionReads ⟨.rPrj p, #[], #[], #[]⟩ .recursor (.member p.block p.idx.toNat)
  | constructor (p : Ixon.ConstructorProj) :
      ProjectionReads ⟨.cPrj p, #[], #[], #[]⟩ .constructor (.ctor p.block p.idx.toNat p.cidx.toNat)

def readProjectionC (source : Ixon.Constant) : Search { value : ProjectionLayout × ConstRef Address //
    ProjectionReads source value.1 value.2 } :=
  if tables : Ingress.emptyTables source = true then
    match info : source.info with
    | .dPrj p => .ok ⟨(.definition, .member p.block p.idx.toNat), by
        have original : source = ⟨.dPrj p, #[], #[], #[]⟩ := by
          cases source; simp_all [Ingress.emptyTables]
        rw [original]; exact .definition p⟩
    | .iPrj p => .ok ⟨(.inductive, .member p.block p.idx.toNat), by
        have original : source = ⟨.iPrj p, #[], #[], #[]⟩ := by
          cases source; simp_all [Ingress.emptyTables]
        rw [original]; exact .inductive p⟩
    | .rPrj p => .ok ⟨(.recursor, .member p.block p.idx.toNat), by
        have original : source = ⟨.rPrj p, #[], #[], #[]⟩ := by
          cases source; simp_all [Ingress.emptyTables]
        rw [original]; exact .recursor p⟩
    | .cPrj p => .ok ⟨(.constructor, .ctor p.block p.idx.toNat p.cidx.toNat), by
        have original : source = ⟨.cPrj p, #[], #[], #[]⟩ := by
          cases source; simp_all [Ingress.emptyTables]
        rw [original]; exact .constructor p⟩
    | _ => .error (.malformed "record is not a projection")
  else .error (.malformed "projection record has nonempty tables")

def readProjection (source : Ixon.Constant) : Search (ProjectionLayout × ConstRef Address) :=
  (readProjectionC source).map Subtype.val

theorem readProjection_reading {source : Ixon.Constant} {value : ProjectionLayout × ConstRef Address}
    (h : readProjection source = .ok value) : ProjectionReads source value.1 value.2 := by
  obtain ⟨reading, _, same⟩ := Except.map_eq_ok h
  exact same ▸ reading.property

private def wordC (n : Nat) : Search { value : UInt64 // value.toNat = n } :=
  if h : (UInt64.ofNat n).toNat = n then .ok ⟨UInt64.ofNat n, h⟩
  else .error (.malformed "projection index exceeds UInt64")

def writeProjectionC (layout : ProjectionLayout) (reference : ConstRef Address) :
    Search { source : Ixon.Constant // ProjectionReads source layout reference } :=
  match layout, reference with
  | .definition, .member owner i => do
    let index ← wordC i
    return ⟨⟨.dPrj ⟨index.val, owner⟩, #[], #[], #[]⟩, by
      simpa only [index.property] using ProjectionReads.definition ⟨index.val, owner⟩⟩
  | .inductive, .member owner i => do
    let index ← wordC i
    return ⟨⟨.iPrj ⟨index.val, owner⟩, #[], #[], #[]⟩, by
      simpa only [index.property] using ProjectionReads.inductive ⟨index.val, owner⟩⟩
  | .recursor, .member owner i => do
    let index ← wordC i
    return ⟨⟨.rPrj ⟨index.val, owner⟩, #[], #[], #[]⟩, by
      simpa only [index.property] using ProjectionReads.recursor ⟨index.val, owner⟩⟩
  | .constructor, .ctor owner i c => do
    let index ← wordC i
    let ctor ← wordC c
    return ⟨⟨.cPrj ⟨index.val, ctor.val, owner⟩, #[], #[], #[]⟩, by
      simpa only [index.property, ctor.property] using ProjectionReads.constructor ⟨index.val, ctor.val, owner⟩⟩
  | _, _ => .error (.malformed "projection variant and kernel reference disagree")

def writeProjection (layout : ProjectionLayout) (reference : ConstRef Address) : Search Ixon.Constant :=
  (writeProjectionC layout reference).map Subtype.val

theorem writeProjection_reading {layout : ProjectionLayout} {reference : ConstRef Address}
    {source : Ixon.Constant} (h : writeProjection layout reference = .ok source) :
    ProjectionReads source layout reference := by
  obtain ⟨reading, _, same⟩ := Except.map_eq_ok h
  exact same ▸ reading.property

theorem writeProjection_of_reading {source : Ixon.Constant} {layout : ProjectionLayout}
    {reference : ConstRef Address} (h : ProjectionReads source layout reference) :
    writeProjection layout reference = .ok source := by
  cases h <;> simp [writeProjection, writeProjectionC, wordC,
    bind, pure, Except.bind, Except.pure, Except.map]

theorem writeProjection_roundtrip {source : Ixon.Constant} {value : ProjectionLayout × ConstRef Address}
    (h : readProjection source = .ok value) : writeProjection value.1 value.2 = .ok source :=
  writeProjection_of_reading (readProjection_reading h)

end Ix.Kernel.Egress
