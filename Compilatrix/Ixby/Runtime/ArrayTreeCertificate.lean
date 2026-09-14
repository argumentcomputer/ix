import Compilatrix.Ixby.Runtime.ArrayTreeCode
import Compilatrix.Ixby.Runtime.WordTruncate

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby ScalarFunction

/-- Evidence for complete function bodies, numeric dependencies, constructor
declarations, and every tag distinction used by tree dispatch. -/
structure Certificate (program : Program) (links : Links) : Type where
  arithmetic : NatArithmetic.Certificate program links.arithmetic
  usizeOfNat : Checked program links.usizeOfNat
    (Words.truncate links.arithmetic.conversions.natural links.arithmetic.conversions.lowWord
      links.arithmetic.conversions.cachedCtor 1 64)
  treeGet : Checked program links.treeGet (ArrayTrees.treeGet links)
  treeSet : Checked program links.treeSet (ArrayTrees.treeSet links)
  size : Checked program links.size (ArrayTrees.size links)
  usize : Checked program links.usize (ArrayTrees.usize links)
  empty : Checked program links.empty (ArrayTrees.empty links)
  mkEmpty : Checked program links.mkEmpty (ArrayTrees.empty links)
  get : Checked program links.get (ArrayTrees.get links)
  getBorrowed : Checked program links.getBorrowed (ArrayTrees.getAlias links)
  uget : Checked program links.uget (ArrayTrees.getAlias links)
  ugetBorrowed : Checked program links.ugetBorrowed (ArrayTrees.getAlias links)
  getBang : Checked program links.getBang (ArrayTrees.getBang links)
  getBangBorrowed : Checked program links.getBangBorrowed (ArrayTrees.getBang links)
  push : Checked program links.push (ArrayTrees.push links)
  set : Checked program links.set (ArrayTrees.set links)
  uset : Checked program links.uset (ArrayTrees.uset links)
  emptyCtor : program.getConstructor links.emptyCtor = .ok ⟨links.layout.empty, 0⟩
  leafCtor : program.getConstructor links.leafCtor = .ok ⟨links.layout.leaf, 1⟩
  nodeCtor : program.getConstructor links.nodeCtor = .ok ⟨links.layout.node, 2⟩
  arrayCtor : program.getConstructor links.arrayCtor = .ok ⟨links.layout.array, 3⟩
  bytesCtor : program.getConstructor links.bytesCtor = .ok ⟨links.layout.bytes, 2⟩
  ropeCtor : program.getConstructor links.ropeCtor = .ok ⟨links.layout.rope, 4⟩
  emptyNode : (links.layout.empty == links.layout.node) = false
  bytesArray : (links.layout.bytes == links.layout.array) = false
  bytesRope : (links.layout.bytes == links.layout.rope) = false
  arrayRope : (links.layout.array == links.layout.rope) = false

private structure ConstructorChecked (program : Program) (index : Constructor) (expected : CtorDecl) : Type where
  code : program.getConstructor index = .ok expected

private def checkConstructor (program : Program) (index : Constructor) (expected : CtorDecl) :
    Except String (ConstructorChecked program index expected) := do
  match found : program.getConstructor index with
  | .error _ => throw s!"missing array constructor {index}"
  | .ok actual =>
    if same : actual = expected then return ⟨same ▸ found⟩
    else throw s!"array constructor differs: {index}"

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let arithmetic ← NatArithmetic.certify program links.arithmetic
  let usizeOfNat ← check program links.usizeOfNat
    (Words.truncate links.arithmetic.conversions.natural links.arithmetic.conversions.lowWord
      links.arithmetic.conversions.cachedCtor 1 64)
  let treeGet ← check program links.treeGet (ArrayTrees.treeGet links)
  let treeSet ← check program links.treeSet (ArrayTrees.treeSet links)
  let size ← check program links.size (ArrayTrees.size links)
  let usize ← check program links.usize (ArrayTrees.usize links)
  let empty ← check program links.empty (ArrayTrees.empty links)
  let mkEmpty ← check program links.mkEmpty (ArrayTrees.empty links)
  let get ← check program links.get (ArrayTrees.get links)
  let getBorrowed ← check program links.getBorrowed (ArrayTrees.getAlias links)
  let uget ← check program links.uget (ArrayTrees.getAlias links)
  let ugetBorrowed ← check program links.ugetBorrowed (ArrayTrees.getAlias links)
  let getBang ← check program links.getBang (ArrayTrees.getBang links)
  let getBangBorrowed ← check program links.getBangBorrowed (ArrayTrees.getBang links)
  let push ← check program links.push (ArrayTrees.push links)
  let set ← check program links.set (ArrayTrees.set links)
  let uset ← check program links.uset (ArrayTrees.uset links)
  let emptyCtor ← checkConstructor program links.emptyCtor ⟨links.layout.empty, 0⟩
  let leafCtor ← checkConstructor program links.leafCtor ⟨links.layout.leaf, 1⟩
  let nodeCtor ← checkConstructor program links.nodeCtor ⟨links.layout.node, 2⟩
  let arrayCtor ← checkConstructor program links.arrayCtor ⟨links.layout.array, 3⟩
  let bytesCtor ← checkConstructor program links.bytesCtor ⟨links.layout.bytes, 2⟩
  let ropeCtor ← checkConstructor program links.ropeCtor ⟨links.layout.rope, 4⟩
  if emptyNode : (links.layout.empty == links.layout.node) = false then
    if bytesArray : (links.layout.bytes == links.layout.array) = false then
      if bytesRope : (links.layout.bytes == links.layout.rope) = false then
        if arrayRope : (links.layout.array == links.layout.rope) = false then
          return {
            arithmetic := arithmetic
            usizeOfNat := usizeOfNat
            treeGet := treeGet
            treeSet := treeSet
            size := size
            usize := usize
            empty := empty
            mkEmpty := mkEmpty
            get := get
            getBorrowed := getBorrowed
            uget := uget
            ugetBorrowed := ugetBorrowed
            getBang := getBang
            getBangBorrowed := getBangBorrowed
            push := push
            set := set
            uset := uset
            emptyCtor := emptyCtor.code
            leafCtor := leafCtor.code
            nodeCtor := nodeCtor.code
            arrayCtor := arrayCtor.code
            bytesCtor := bytesCtor.code
            ropeCtor := ropeCtor.code
            emptyNode := emptyNode
            bytesArray := bytesArray
            bytesRope := bytesRope
            arrayRope := arrayRope
          }
        else throw "array array and rope tags coincide"
      else throw "array bytes and rope tags coincide"
    else throw "array bytes and array tags coincide"
  else throw "array empty and node tags coincide"

end Compilatrix.Ixby.Runtime.ArrayTrees
