import Ix.Aiur.Library.Core
import Ix.Aiur.Library.ByteStream
import Ix.Aiur.Library.Blake3
import Ix.Aiur.Compiler

/-!
Experimental direct Aiur frontend for the deliberately small grammar
  def IDENT (IDENT : Type) : Type := IDENT
with ASCII identifiers and whitespace. It builds syntax, resolves the body
against the binder, and constructs a De Bruijn lambda and its forall type.
The public result checks the declaration is named `id` and has the identity
type/value. This is a subset experiment, not an implementation of Ix.Frontend.
-/
namespace FrontendDirectBench

def frontend := ⟦
  enum Token {
    Ident(ByteStream), Def, Ty, LParen, RParen, Colon, Assign, Eof
  }

  enum Decl {
    Mk(ByteStream, ByteStream, ByteStream)
  }

  enum ExprNode {
    Universe(G), BVar(G), Lam(&ExprNode, &ExprNode), Forall(&ExprNode, &ExprNode)
  }

  fn is_letter(c: G) -> G {
    let lower = (1 - u32_less_than(c, 97)) * u32_less_than(c, 123);
    let upper = (1 - u32_less_than(c, 65)) * u32_less_than(c, 91);
    match c { 95 => 1, _ => lower + upper, }
  }

  fn is_ident(c: G) -> G {
    is_letter(c) + (1 - u32_less_than(c, 48)) * u32_less_than(c, 58)
  }

  fn skip_space(src: ByteStream) -> ByteStream {
    match load(src) {
      ListNode.Nil => src,
      ListNode.Cons(c, rest) => match to_field(c) {
        32 => skip_space(rest),
        9 => skip_space(rest),
        10 => skip_space(rest),
        13 => skip_space(rest),
        _ => src,
      },
    }
  }

  fn scan_ident(src: ByteStream) -> (ByteStream, ByteStream) {
    match load(src) {
      ListNode.Nil => (store(ListNode.Nil), src),
      ListNode.Cons(c, rest) => match is_ident(to_field(c)) {
        0 => (store(ListNode.Nil), src),
        1 =>
          let (word, tail) = scan_ident(rest);
          (store(ListNode.Cons(c, word)), tail),
      },
    }
  }

  fn next_token(src: ByteStream) -> (Token, ByteStream) {
    let src = skip_space(src);
    match load(src) {
      ListNode.Nil => (Token.Eof, src),
      ListNode.Cons(c, rest) => match to_field(c) {
        40 => (Token.LParen, rest),
        41 => (Token.RParen, rest),
        58 => match load(rest) {
          ListNode.Nil => (Token.Colon, rest),
          ListNode.Cons(d, tail) => match to_field(d) {
            61 => (Token.Assign, tail),
            _ => (Token.Colon, rest),
          },
        },
        _ =>
          assert_eq!(is_letter(to_field(c)), 1, "expected identifier");
          let (word, tail) = scan_ident(src);
          (ident_token(word), tail),
      },
    }
  }

  fn word_def() -> ByteStream {
    store(ListNode.Cons(100u8, store(ListNode.Cons(101u8,
      store(ListNode.Cons(102u8, store(ListNode.Nil)))))))
  }

  fn word_type() -> ByteStream {
    store(ListNode.Cons(84u8, store(ListNode.Cons(121u8,
      store(ListNode.Cons(112u8, store(ListNode.Cons(101u8, store(ListNode.Nil)))))))))
  }

  fn word_id() -> ByteStream {
    store(ListNode.Cons(105u8, store(ListNode.Cons(100u8, store(ListNode.Nil)))))
  }

  fn word_eq(a: ByteStream, b: ByteStream) -> G {
    match load(a) {
      ListNode.Nil => match load(b) { ListNode.Nil => 1, _ => 0, },
      ListNode.Cons(x, xs) => match load(b) {
        ListNode.Nil => 0,
        ListNode.Cons(y, ys) => match to_field(x) - to_field(y) {
          0 => word_eq(xs, ys), _ => 0,
        },
      },
    }
  }

  fn ident_token(word: ByteStream) -> Token {
    match word_eq(word, word_def()) {
      1 => Token.Def,
      0 => match word_eq(word, word_type()) {
        1 => Token.Ty, 0 => Token.Ident(word),
      },
    }
  }

  -- Positive interned equality: equal pointers imply equal contents. An
  -- adversarial duplicate allocation can only make an equality fail.
  fn parse_decl(src: ByteStream) -> Decl {
    let (Token.Def, src) = next_token(src);
    let (Token.Ident(name), src) = next_token(src);
    let (Token.LParen, src) = next_token(src);
    let (Token.Ident(binder), src) = next_token(src);
    let (Token.Colon, src) = next_token(src);
    let (Token.Ty, src) = next_token(src);
    let (Token.RParen, src) = next_token(src);
    let (Token.Colon, src) = next_token(src);
    let (Token.Ty, src) = next_token(src);
    let (Token.Assign, src) = next_token(src);
    let (Token.Ident(body), src) = next_token(src);
    let (Token.Eof, _) = next_token(src);
    Decl.Mk(name, binder, body)
  }

  fn elaborate(decl: Decl) -> (&ExprNode, &ExprNode) {
    let Decl.Mk(name, binder, body) = decl;
    assert_eq!(name, word_id(), "expected declaration id");
    assert_eq!(binder, body, "unbound variable");
    let sort = store(ExprNode.Universe(1));
    let value = store(ExprNode.Lam(sort, store(ExprNode.BVar(0))));
    let ty = store(ExprNode.Forall(sort, sort));
    (ty, value)
  }

  pub fn direct_frontend(digest: [U8; 32]) -> G {
    let (idx, len) = io_get_info(0, digest);
    let src = read_checked_byte_stream(0, idx, len);
    verify_bytes_against(src, digest);
    let (ty, value) = elaborate(parse_decl(src));
    let sort = store(ExprNode.Universe(1));
    assert_eq!(ty, store(ExprNode.Forall(sort, sort)), "wrong type");
    assert_eq!(value, store(ExprNode.Lam(sort, store(ExprNode.BVar(0)))), "wrong value");
    1
  }

  pub fn direct_hash(digest: [U8; 32]) -> G {
    let (idx, len) = io_get_info(0, digest);
    let src = read_checked_byte_stream(0, idx, len);
    verify_bytes_against(src, digest);
    1
  }
⟧

def toplevel : Except String Aiur.Source.Toplevel := do
  let tl ← (Aiur.Library.core.merge Aiur.Library.byteStream).mapError toString
  let tl ← (tl.merge Aiur.Library.blake3).mapError toString
  let tl ← (tl.merge frontend).mapError toString
  return tl.prune [`direct_frontend, `direct_hash]

end FrontendDirectBench
