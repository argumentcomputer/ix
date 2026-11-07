import Aiur.Modules

namespace Aiur.Library.List
open Aiur

def declarations : Modules.Program Nat := aiur% "
module Lists {
    enum Node<T> { Cons(T, List<T>), Nil }
    type List<T> = &Node<T>;
    fn is_empty<T>(list: List<T>) -> Field {
        match *list { Node::Nil => 1, Node::Cons(_, _) => 0 }
    }

fn length<T>(list: List<T>) -> Field {
    match (*(list)) {
      Lists::Node::Nil => {  0 } ,
      Lists::Node::Cons(_, rest) => {  length(rest) + 1 } ,
    }
  }

fn concat<T>(a: List<T>, b: List<T>) -> List<T> {
    match (*(a)) {
      Lists::Node::Nil => {  b } ,
      Lists::Node::Cons(v, rest) => {  (&(Lists::Node::Cons(v, concat(rest, b)))) } ,
    }
  }

fn lookup<T>(list: List<T>, idx: Field) -> T {
    let Lists::Node::Cons(v, _) = (*(drop(list, idx)));
    v
  }

fn lookup_or_default<T>(list: List<T>, idx: Field, default: T) -> T {
    match (*(drop(list, idx))) {
      Lists::Node::Nil => {  default } ,
      Lists::Node::Cons(v, _) => {  v } ,
    }
  }

fn drop<T>(list: List<T>, n: Field) -> List<T> {
    match n {
      0 => {  list } ,
      _ => {
        let Lists::Node::Cons(_, rest) = (*(drop(list, n - 1)));
        rest } ,
    }
  }

fn take<T>(list: List<T>, n: Field) -> List<T> {
    match n {
      0 => {  (&(Lists::Node::Nil)) } ,
      _ => {
        let Lists::Node::Cons(v, rest) = (*(list));
        (&(Lists::Node::Cons(v, take(rest, n - 1)))) } ,
    }
  }

fn snoc<T>(list: List<T>, v: T) -> List<T> {
    match (*(list)) {
      Lists::Node::Nil => {  (&(Lists::Node::Cons(v, (&(Lists::Node::Nil))))) } ,
      Lists::Node::Cons(head, rest) => {  (&(Lists::Node::Cons(head, snoc(rest, v)))) } ,
    }
  }

fn reverse<T>(list: List<T>) -> List<T> {
    reverse_acc(list, (&(Lists::Node::Nil)))
  }

fn reverse_acc<T>(list: List<T>, acc: List<T>) -> List<T> {
    match (*(list)) {
      Lists::Node::Nil => {  acc } ,
      Lists::Node::Cons(head, rest) => {
        reverse_acc(rest, (&(Lists::Node::Cons(head, acc)))) } ,
    }
  }
}"

end Aiur.Library.List
