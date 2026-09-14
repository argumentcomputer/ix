import Compilatrix.Ixby.Runtime.NatArithmeticCertificate
import Compilatrix.Ixby.Runtime.ArrayTreeRepresentation

/-! Complete emitted code for the tree-backed array slice. Packed-byte and
rope branches retain their real named targets but are outside the tree
contracts. No fixed function index or constructor tag is assumed. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby Conversion

structure Links where
  arithmetic : NatArithmetic.Links
  layout : Layout
  emptyCtor : Constructor
  leafCtor : Constructor
  nodeCtor : Constructor
  arrayCtor : Constructor
  bytesCtor : Constructor
  ropeCtor : Constructor
  treeGet : FunctionId
  treeSet : FunctionId
  size : FunctionId
  usize : FunctionId
  empty : FunctionId
  mkEmpty : FunctionId
  get : FunctionId
  getBorrowed : FunctionId
  uget : FunctionId
  ugetBorrowed : FunctionId
  getBang : FunctionId
  getBangBorrowed : FunctionId
  push : FunctionId
  set : FunctionId
  uset : FunctionId
  usizeOfNat : FunctionId
  copyArray : FunctionId
  byteGet : FunctionId

def treeGet (links : Links) : Function := {
  arity := 3, blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 1, N 1]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .letOp (.project (.local 0) 0) 4⟩,
    ⟨4, .letOp (.primitive .natDiv [.local 1, N 2]) 5⟩,
    ⟨5, .ret (.local 4)⟩,
    ⟨5, .letOp (.primitive .natLt [.local 2, .local 4]) 6⟩,
    ⟨6, .branch (.local 5) 7 8⟩,
    ⟨6, .letOp (.project (.local 0) 0) 9⟩,
    ⟨6, .letOp (.project (.local 0) 1) 10⟩,
    ⟨7, .tailCall links.treeGet [.local 6, .local 4, .local 2]⟩,
    ⟨7, .letOp (.primitive .natSub [.local 2, .local 4]) 11⟩,
    ⟨8, .tailCall links.treeGet [.local 6, .local 4, .local 7]⟩] }

def treeSet (links : Links) : Function := {
  arity := 4, blocks := #[
    ⟨4, .letOp (.primitive .natEq [.local 1, N 1]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.construct links.leafCtor [.local 3]) 4⟩,
    ⟨5, .letOp (.primitive .natDiv [.local 1, N 2]) 5⟩,
    ⟨6, .ret (.local 5)⟩,
    ⟨6, .caseCtor (.local 0) [⟨links.emptyCtor, 6⟩, ⟨links.nodeCtor, 7⟩]⟩,
    ⟨6, .letOp (.construct links.emptyCtor []) 8⟩,
    ⟨8, .letOp (.primitive .natLt [.local 2, .local 5]) 17⟩,
    ⟨7, .letOp (.primitive .natLt [.local 2, .local 5]) 9⟩,
    ⟨8, .branch (.local 7) 10 11⟩,
    ⟨8, .letOp (.call links.treeSet [.local 6, .local 5, .local 2, .local 3]) 12⟩,
    ⟨8, .letOp (.primitive .natSub [.local 2, .local 5]) 14⟩,
    ⟨9, .letOp (.construct links.nodeCtor [.local 8, .local 6]) 13⟩,
    ⟨10, .ret (.local 9)⟩,
    ⟨9, .letOp (.call links.treeSet [.local 6, .local 5, .local 8, .local 3]) 15⟩,
    ⟨10, .letOp (.construct links.nodeCtor [.local 6, .local 9]) 16⟩,
    ⟨11, .ret (.local 10)⟩,
    ⟨9, .branch (.local 8) 18 19⟩,
    ⟨9, .letOp (.call links.treeSet [.local 6, .local 5, .local 2, .local 3]) 20⟩,
    ⟨9, .letOp (.primitive .natSub [.local 2, .local 5]) 22⟩,
    ⟨10, .letOp (.construct links.nodeCtor [.local 9, .local 7]) 21⟩,
    ⟨11, .ret (.local 10)⟩,
    ⟨10, .letOp (.call links.treeSet [.local 7, .local 5, .local 9, .local 3]) 23⟩,
    ⟨11, .letOp (.construct links.nodeCtor [.local 6, .local 10]) 24⟩,
    ⟨12, .ret (.local 11)⟩] }

def size (links : Links) : Function := {
  arity := 2, blocks := #[
    ⟨2, .caseCtor (.local 1) [⟨links.bytesCtor, 1⟩, ⟨links.arrayCtor, 2⟩, ⟨links.ropeCtor, 3⟩]⟩,
    ⟨4, .ret (.local 3)⟩,
    ⟨5, .ret (.local 2)⟩,
    ⟨6, .ret (.local 2)⟩] }

def usize (links : Links) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call links.size [.erased, .local 1]) 1⟩,
    ⟨3, .tailCall links.usizeOfNat [.local 2]⟩] }

def empty (links : Links) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.construct links.arithmetic.conversions.cachedCtor [N 0, W 0]) 1⟩,
    ⟨3, .letOp (.construct links.emptyCtor []) 2⟩,
    ⟨4, .letOp (.construct links.arrayCtor [.local 2, N 1, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

def get (links : Links) : Function := {
  arity := 4, blocks := #[
    ⟨4, .letOp (.call links.size [.erased, .local 1]) 1⟩,
    ⟨5, .letOp (.call links.arithmetic.less [.local 2, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .caseCtor (.local 1) [⟨links.bytesCtor, 5⟩, ⟨links.arrayCtor, 6⟩, ⟨links.ropeCtor, 7⟩]⟩,
    ⟨6, .caseCtor (.erased) []⟩,
    ⟨8, .letOp (.call links.arithmetic.conversions.lowWord [.local 2]) 8⟩,
    ⟨9, .letOp (.call links.arithmetic.conversions.natural [.local 2]) 10⟩,
    ⟨10, .tailCall links.byteGet [.local 1, .local 2]⟩,
    ⟨9, .letOp (.primitive .bytesGet [.local 6, .local 8]) 9⟩,
    ⟨10, .tailCall links.arithmetic.conversions.fromWord [.local 9]⟩,
    ⟨10, .tailCall links.treeGet [.local 8, .local 7, .local 9]⟩] }

def getAlias (links : Links) : Function := {
  arity := 4, blocks := #[
    ⟨4, .tailCall links.get [.erased, .local 1, .local 2, .erased]⟩] }

def getBang (links : Links) : Function := {
  arity := 4, blocks := #[
    ⟨4, .letOp (.call links.size [.erased, .local 2]) 1⟩,
    ⟨5, .letOp (.call links.arithmetic.less [.local 3, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .tailCall links.get [.erased, .local 2, .local 3, .erased]⟩,
    ⟨6, .ret (.local 1)⟩] }

def push (links : Links) : Function := {
  arity := 3, blocks := #[
    ⟨3, .letOp (.call links.size [.erased, .local 1]) 1⟩,
    ⟨4, .letOp (.construct links.arithmetic.conversions.cachedCtor [N 1, W 1]) 2⟩,
    ⟨5, .letOp (.call links.arithmetic.add [.local 3, .local 4]) 3⟩,
    ⟨6, .caseCtor (.local 1) [⟨links.bytesCtor, 4⟩, ⟨links.arrayCtor, 5⟩, ⟨links.ropeCtor, 6⟩]⟩,
    ⟨8, .letOp (.call links.copyArray [.local 1]) 7⟩,
    ⟨9, .letOp (.call links.arithmetic.conversions.natural [.local 3]) 8⟩,
    ⟨10, .letOp (.call links.copyArray [.local 1]) 19⟩,
    ⟨9, .tailCall links.push [.erased, .local 8, .local 2]⟩,
    ⟨10, .letOp (.primitive .natLt [.local 9, .local 7]) 9⟩,
    ⟨11, .branch (.local 10) 10 11⟩,
    ⟨11, .letOp (.call links.treeSet [.local 8, .local 7, .local 9, .local 2]) 12⟩,
    ⟨11, .letOp (.primitive .natAdd [.local 7, .local 7]) 14⟩,
    ⟨12, .letOp (.construct links.arrayCtor [.local 5, .local 7, .local 11]) 13⟩,
    ⟨13, .ret (.local 12)⟩,
    ⟨12, .letOp (.construct links.emptyCtor []) 15⟩,
    ⟨13, .letOp (.construct links.nodeCtor [.local 8, .local 12]) 16⟩,
    ⟨14, .letOp (.call links.treeSet [.local 13, .local 11, .local 9, .local 2]) 17⟩,
    ⟨15, .letOp (.construct links.arrayCtor [.local 5, .local 11, .local 14]) 18⟩,
    ⟨16, .ret (.local 15)⟩,
    ⟨11, .tailCall links.push [.erased, .local 10, .local 2]⟩] }

def set (links : Links) : Function := {
  arity := 4, blocks := #[
    ⟨4, .letOp (.call links.size [.erased, .local 1]) 1⟩,
    ⟨5, .letOp (.call links.arithmetic.less [.local 2, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .caseCtor (.local 1) [⟨links.bytesCtor, 5⟩, ⟨links.arrayCtor, 6⟩, ⟨links.ropeCtor, 7⟩]⟩,
    ⟨6, .ret (.local 1)⟩,
    ⟨8, .letOp (.call links.copyArray [.local 1]) 8⟩,
    ⟨9, .letOp (.call links.arithmetic.conversions.natural [.local 2]) 9⟩,
    ⟨10, .letOp (.call links.copyArray [.local 1]) 12⟩,
    ⟨9, .tailCall links.set [.erased, .local 8, .local 2, .local 3]⟩,
    ⟨10, .letOp (.call links.treeSet [.local 8, .local 7, .local 9, .local 3]) 10⟩,
    ⟨11, .letOp (.construct links.arrayCtor [.local 4, .local 7, .local 10]) 11⟩,
    ⟨12, .ret (.local 11)⟩,
    ⟨11, .tailCall links.set [.erased, .local 10, .local 2, .local 3]⟩] }

def uset (links : Links) : Function := {
  arity := 5, blocks := #[
    ⟨5, .letOp (.call links.size [.erased, .local 1]) 1⟩,
    ⟨6, .letOp (.call links.arithmetic.less [.local 2, .local 5]) 2⟩,
    ⟨7, .branch (.local 6) 3 4⟩,
    ⟨7, .tailCall links.set [.erased, .local 1, .local 2, .local 3]⟩,
    ⟨7, .caseCtor (.erased) []⟩] }

end Compilatrix.Ixby.Runtime.ArrayTrees
