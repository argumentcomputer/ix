use blake3::Hash;
use num_bigint::BigUint;

pub mod address;
pub mod claim;
pub mod constant;
pub mod meta;
pub mod name;
pub mod nat;
pub mod serialize;
pub mod univ;

use address::*;
use claim::*;
use constant::*;
use meta::*;
use name::*;
use nat::*;
use serialize::*;
use univ::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ixon {
    Vari(u64),                                   // 0x0X, variables
    Sort(Box<Univ>),                             // 0x90, universes
    Refr(Address, Vec<Univ>),                    // 0x1X, global reference
    Recr(u64, Vec<Univ>),                        // 0x2X, local const recursion
    Apps(Box<Ixon>, Box<Ixon>, Vec<Ixon>),       // 0x3X, applications
    Lams(Vec<Ixon>, Box<Ixon>),                  // 0x4X, lambdas
    Alls(Vec<Ixon>, Box<Ixon>),                  // 0x5X, foralls
    Proj(Address, u64, Box<Ixon>),               // 0x6X, structure projection
    Strl(String),                                // 0x7X, unicode string
    Natl(Nat),                                   // 0x8X, natural numbers
    LetE(bool, Box<Ixon>, Box<Ixon>, Box<Ixon>), // 0x91, 0x92, local binder
    List(Vec<Ixon>),                             // 0xA, list
    Defn(Definition),                            // 0xB0, definition
    Axio(Axiom),                                 // 0xB1, axiom
    Quot(Quotient),                              // 0xB2, quotient
    CPrj(ConstructorProj),                       // 0xB3, constructor projection
    RPrj(RecursorProj),                          // 0xB4, recursor projection
    IPrj(InductiveProj),                         // 0xB5, inductive projection
    DPrj(DefinitionProj),                        // 0xB6, definition projection
    Inds(Vec<Inductive>),                        // 0xCX, mutual inductive data
    Defs(Vec<Definition>),                       // 0xDX, mutual definition
    Meta(Metadata),                              // 0xE0, metadata
    Prof(Proof),                                 // 0xE1, zero-knowledge proof
    Eval(EvalClaim),                             // 0xE2, evaluation claim
    Chck(CheckClaim),                            // 0xE3, typechecking claim
    Comm(Comm),                                  // 0xE4, cryptographic commitment
    Envn(Env),                                   // 0xE5, multi-claim environment
}

impl Default for Ixon {
    fn default() -> Self {
        Self::Vari(0)
    }
}

impl Ixon {
    pub fn u64_byte_count(x: u64) -> u8 {
        match x {
            0 => 0,
            x if x < 0x0000000000000100 => 1,
            x if x < 0x0000000000010000 => 2,
            x if x < 0x0000000001000000 => 3,
            x if x < 0x0000000100000000 => 4,
            x if x < 0x0000010000000000 => 5,
            x if x < 0x0001000000000000 => 6,
            x if x < 0x0100000000000000 => 7,
            _ => 8,
        }
    }

    pub fn u64_put_trimmed_le(x: u64, buf: &mut Vec<u8>) {
        let n = Ixon::u64_byte_count(x) as usize;
        buf.extend_from_slice(&x.to_le_bytes()[..n])
    }

    pub fn u64_get_trimmed_le(len: usize, buf: &mut &[u8]) -> Result<u64, String> {
        let mut res = [0u8; 8];
        if len > 8 {
            return Err("get trimmed_le_64 len > 8".to_string());
        }
        match buf.split_at_checked(len) {
            Some((head, rest)) => {
                *buf = rest;
                res[..len].copy_from_slice(head);
                Ok(u64::from_le_bytes(res))
            }
            None => Err("get trimmed_le_u64 EOF".to_string()),
        }
    }

    pub fn pack_bools<I>(bools: I) -> u8
    where
        I: IntoIterator<Item = bool>,
    {
        let mut acc: u8 = 0;
        for (i, b) in bools.into_iter().take(8).enumerate() {
            if b {
                acc |= 1u8 << (i as u32);
            }
        }
        acc
    }

    pub fn unpack_bools(n: usize, b: u8) -> Vec<bool> {
        (0..8)
            .map(|i| (b & (1u8 << (i as u32))) != 0)
            .take(n.min(8))
            .collect()
    }

    fn put_tag(tag: u8, val: u64, buf: &mut Vec<u8>) {
        if val < 8 {
            buf.push((tag << 4) | (val as u8));
        } else {
            buf.push((tag << 4) | 0b1000 | (Ixon::u64_byte_count(val) - 1));
            Ixon::u64_put_trimmed_le(val, buf);
        }
    }

    fn get_size(is_large: bool, small: u8, buf: &mut &[u8]) -> Result<u64, String> {
        if is_large {
            Ixon::u64_get_trimmed_le((small + 1) as usize, buf)
        } else {
            Ok(small as u64)
        }
    }

    // put_array and get_array are separated from Ixon's serialize implementation
    // in order to create a generic Serialize impl for Vec<S>
    pub fn put_array<S: Serialize>(xs: &[S], buf: &mut Vec<u8>) {
        Self::put_tag(0xA, xs.len() as u64, buf);
        for x in xs {
            x.put(buf)
        }
    }

    pub fn get_array<S: Serialize>(buf: &mut &[u8]) -> Result<Vec<S>, String> {
        let tag_byte = u8::get(buf)?;
        let tag = tag_byte >> 4;
        let small_size = tag_byte & 0b111;
        let is_large = tag_byte & 0b1000 != 0;
        match tag {
            0xA => {
                let len = Self::get_size(is_large, small_size, buf)?;
                let mut vec = vec![];
                for _ in 0..len {
                    let s = S::get(buf)?;
                    vec.push(s);
                }
                Ok(vec)
            }
            x => Err(format!("get array invalid tag {x}")),
        }
    }
}

impl Serialize for Ixon {
    fn put(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Vari(x) => Self::put_tag(0x0, *x, buf),
            Self::Sort(x) => {
                u8::put(&0x90, buf);
                x.put(buf);
            }
            Self::Refr(addr, lvls) => {
                Self::put_tag(0x1, lvls.len() as u64, buf);
                addr.put(buf);
                for l in lvls {
                    l.put(buf);
                }
            }
            Self::Recr(x, lvls) => {
                Self::put_tag(0x2, lvls.len() as u64, buf);
                x.put(buf);
                for l in lvls {
                    l.put(buf);
                }
            }
            Self::Apps(f, a, args) => {
                Self::put_tag(0x3, args.len() as u64, buf);
                f.put(buf);
                a.put(buf);
                for x in args {
                    x.put(buf);
                }
            }
            Self::Lams(ts, b) => {
                Self::put_tag(0x4, ts.len() as u64, buf);
                for t in ts {
                    t.put(buf);
                }
                b.put(buf);
            }
            Self::Alls(ts, b) => {
                Self::put_tag(0x5, ts.len() as u64, buf);
                for t in ts {
                    t.put(buf);
                }
                b.put(buf);
            }
            Self::Proj(t, n, x) => {
                Self::put_tag(0x6, *n, buf);
                t.put(buf);
                x.put(buf);
            }
            Self::Strl(s) => {
                let bytes = s.as_bytes();
                Self::put_tag(0x7, bytes.len() as u64, buf);
                buf.extend_from_slice(bytes);
            }
            Self::Natl(n) => {
                let bytes = n.0.to_bytes_le();
                Self::put_tag(0x8, bytes.len() as u64, buf);
                buf.extend_from_slice(&bytes);
            }
            Self::LetE(nd, t, d, b) => {
                if *nd {
                    u8::put(&0x91, buf);
                } else {
                    u8::put(&0x92, buf);
                }
                t.put(buf);
                d.put(buf);
                b.put(buf);
            }
            Self::List(xs) => Ixon::put_array(xs, buf),
            Self::Defn(x) => {
                u8::put(&0xB0, buf);
                x.put(buf);
            }
            Self::Axio(x) => {
                u8::put(&0xB1, buf);
                x.put(buf);
            }
            Self::Quot(x) => {
                u8::put(&0xB2, buf);
                x.put(buf);
            }
            Self::CPrj(x) => {
                u8::put(&0xB3, buf);
                x.put(buf);
            }
            Self::RPrj(x) => {
                u8::put(&0xB4, buf);
                x.put(buf);
            }
            Self::IPrj(x) => {
                u8::put(&0xB5, buf);
                x.put(buf);
            }
            Self::DPrj(x) => {
                u8::put(&0xB6, buf);
                x.put(buf);
            }
            Self::Inds(xs) => {
                Self::put_tag(0xC, xs.len() as u64, buf);
                for x in xs {
                    x.put(buf);
                }
            }
            Self::Defs(xs) => {
                Self::put_tag(0xD, xs.len() as u64, buf);
                for x in xs {
                    x.put(buf);
                }
            }
            Self::Meta(x) => {
                u8::put(&0xE0, buf);
                x.put(buf);
            }
            Self::Prof(x) => {
                u8::put(&0xE1, buf);
                x.put(buf);
            }
            Self::Eval(x) => {
                u8::put(&0xE2, buf);
                x.put(buf);
            }
            Self::Chck(x) => {
                u8::put(&0xE3, buf);
                x.put(buf);
            }
            Self::Comm(x) => {
                u8::put(&0xE4, buf);
                x.put(buf);
            }
            Self::Envn(x) => {
                u8::put(&0xE5, buf);
                x.put(buf);
            }
        }
    }

    fn get(buf: &mut &[u8]) -> Result<Self, String> {
        let tag_byte = u8::get(buf)?;
        let small_size = tag_byte & 0b111;
        let is_large = tag_byte & 0b1000 != 0;
        match tag_byte {
            0x00..=0x0F => {
                let x = Ixon::get_size(is_large, small_size, buf)?;
                Ok(Self::Vari(x))
            }
            0x90 => {
                let u = Univ::get(buf)?;
                Ok(Self::Sort(Box::new(u)))
            }
            0x10..=0x1F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let a = Address::get(buf)?;
                let mut lvls = Vec::new();
                for _ in 0..n {
                    let l = Univ::get(buf)?;
                    lvls.push(l);
                }
                Ok(Self::Refr(a, lvls))
            }
            0x20..=0x2F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let x = u64::get(buf)?;
                let mut lvls = Vec::new();
                for _ in 0..n {
                    let l = Univ::get(buf)?;
                    lvls.push(l);
                }
                Ok(Self::Recr(x, lvls))
            }
            0x30..=0x3F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let f = Ixon::get(buf)?;
                let a = Ixon::get(buf)?;
                let mut args = Vec::new();
                for _ in 0..n {
                    let x = Ixon::get(buf)?;
                    args.push(x);
                }
                Ok(Self::Apps(Box::new(f), Box::new(a), args))
            }
            0x40..=0x4F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut ts = Vec::new();
                for _ in 0..n {
                    let x = Ixon::get(buf)?;
                    ts.push(x);
                }
                let b = Ixon::get(buf)?;
                Ok(Self::Lams(ts, Box::new(b)))
            }
            0x50..=0x5F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut ts = Vec::new();
                for _ in 0..n {
                    let x = Ixon::get(buf)?;
                    ts.push(x);
                }
                let b = Ixon::get(buf)?;
                Ok(Self::Alls(ts, Box::new(b)))
            }
            0x60..=0x6F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let t = Address::get(buf)?;
                let x = Ixon::get(buf)?;
                Ok(Self::Proj(t, n, Box::new(x)))
            }
            0x70..=0x7F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                match buf.split_at_checked(n as usize) {
                    Some((head, rest)) => {
                        *buf = rest;
                        match String::from_utf8(head.to_owned()) {
                            Ok(s) => Ok(Ixon::Strl(s)),
                            Err(e) => Err(format!("UTF8 Error: {e}")),
                        }
                    }
                    None => Err("get Ixon Strl EOF".to_string()),
                }
            }
            0x80..=0x8F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                match buf.split_at_checked(n as usize) {
                    Some((head, rest)) => {
                        *buf = rest;
                        Ok(Ixon::Natl(Nat(BigUint::from_bytes_le(head))))
                    }
                    None => Err("get Expr Natl EOF".to_string()),
                }
            }
            0x91..=0x92 => {
                let nd = tag_byte == 0x91;
                let t = Ixon::get(buf)?;
                let d = Ixon::get(buf)?;
                let b = Ixon::get(buf)?;
                Ok(Self::LetE(nd, Box::new(t), Box::new(d), Box::new(b)))
            }
            0xA0..=0xAF => {
                let len = Self::get_size(is_large, small_size, buf)?;
                let mut vec = vec![];
                for _ in 0..len {
                    let s = Ixon::get(buf)?;
                    vec.push(s);
                }
                Ok(Self::List(vec))
            }
            0xB0 => Ok(Self::Defn(Definition::get(buf)?)),
            0xB1 => Ok(Self::Axio(Axiom::get(buf)?)),
            0xB2 => Ok(Self::Quot(Quotient::get(buf)?)),
            0xB3 => Ok(Self::CPrj(ConstructorProj::get(buf)?)),
            0xB4 => Ok(Self::RPrj(RecursorProj::get(buf)?)),
            0xB5 => Ok(Self::IPrj(InductiveProj::get(buf)?)),
            0xB6 => Ok(Self::DPrj(DefinitionProj::get(buf)?)),
            0xC0..=0xCF => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut inds = Vec::new();
                for _ in 0..n {
                    let x = Inductive::get(buf)?;
                    inds.push(x);
                }
                Ok(Self::Inds(inds))
            }
            0xD0..=0xDF => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut defs = Vec::new();
                for _ in 0..n {
                    let x = Definition::get(buf)?;
                    defs.push(x);
                }
                Ok(Self::Defs(defs))
            }
            0xE0 => Ok(Self::Meta(Metadata::get(buf)?)),
            0xE1 => Ok(Self::Prof(Proof::get(buf)?)),
            0xE2 => Ok(Self::Eval(EvalClaim::get(buf)?)),
            0xE3 => Ok(Self::Chck(CheckClaim::get(buf)?)),
            0xE4 => Ok(Self::Comm(Comm::get(buf)?)),
            0xE5 => Ok(Self::Envn(Env::get(buf)?)),
            x => Err(format!("get Ixon invalid tag {x}")),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::ixon::nat::tests::arbitrary_nat;
    use crate::ixon::univ::tests::arbitrary_univ;
    use quickcheck::{Arbitrary, Gen};
    use std::ops::Range;
    use std::ptr;

    pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
        let res: usize = Arbitrary::arbitrary(g);
        if range.is_empty() {
            0
        } else {
            (res % (range.end - range.start)) + range.start
        }
    }

    pub fn gen_vec<A, F>(g: &mut Gen, size: usize, mut f: F) -> Vec<A>
    where
        F: FnMut(&mut Gen) -> A,
    {
        let len = gen_range(g, 0..size);
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(f(g));
        }
        vec
    }

    pub fn next_case<A: Copy>(g: &mut Gen, gens: &Vec<(usize, A)>) -> A {
        let sum: usize = gens.iter().map(|x| x.0).sum();
        let mut weight: usize = gen_range(g, 1..sum);
        for (n, case) in gens {
            if *n == 0 {
                continue;
            } else {
                match weight.checked_sub(*n) {
                    None | Some(0) => {
                        return *case;
                    }
                    _ => {
                        weight -= *n;
                    }
                }
            }
        }
        unreachable!()
    }

    #[test]
    fn unit_u64_trimmed() {
        fn test(input: u64, expected: Vec<u8>) -> bool {
            let mut tmp = Vec::new();
            let n = Ixon::u64_byte_count(input);
            Ixon::u64_put_trimmed_le(input, &mut tmp);
            if tmp != expected {
                return false;
            }
            match Ixon::u64_get_trimmed_le(n as usize, &mut tmp.as_slice()) {
                Ok(out) => input == out,
                Err(e) => {
                    println!("err: {e}");
                    false
                }
            }
        }
        assert!(test(0x0, vec![]));
        assert!(test(0x01, vec![0x01]));
        assert!(test(0x0000000000000100, vec![0x00, 0x01]));
        assert!(test(0x0000000000010000, vec![0x00, 0x00, 0x01]));
        assert!(test(0x0000000001000000, vec![0x00, 0x00, 0x00, 0x01]));
        assert!(test(0x0000000100000000, vec![0x00, 0x00, 0x00, 0x00, 0x01]));
        assert!(test(
            0x0000010000000000,
            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0001000000000000,
            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0100000000000000,
            vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
        ));
        assert!(test(
            0x0102030405060708,
            vec![0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        ));
    }

    #[quickcheck]
    fn prop_u64_trimmed_le_readback(x: u64) -> bool {
        let mut buf = Vec::new();
        let n = Ixon::u64_byte_count(x);
        Ixon::u64_put_trimmed_le(x, &mut buf);
        match Ixon::u64_get_trimmed_le(n as usize, &mut buf.as_slice()) {
            Ok(y) => x == y,
            Err(e) => {
                println!("err: {e}");
                false
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub enum IxonCase {
        Vari,
        Sort,
        Refr,
        Recr,
        Apps,
        Lams,
        Alls,
        Proj,
        Strl,
        Natl,
        LetE,
        List,
        Defn,
        Axio,
        Quot,
        CPrj,
        RPrj,
        IPrj,
        DPrj,
        Defs,
        Inds,
        Meta,
        Prof,
        Eval,
        Chck,
        Comm,
        Envn,
    }

    pub fn arbitrary_string(g: &mut Gen, cs: usize) -> String {
        let mut s = String::new();
        for _ in 0..cs {
            s.push(char::arbitrary(g));
        }
        s
    }

    // incremental tree generation without recursion stack overflows
    pub fn arbitrary_ixon(g: &mut Gen, ctx: u64) -> Ixon {
        let mut root = Ixon::Vari(0);
        let mut stack = vec![&mut root as *mut Ixon];

        while let Some(ptr) = stack.pop() {
            let gens: Vec<(usize, IxonCase)> = vec![
                (100, IxonCase::Vari),
                (100, IxonCase::Sort),
                (15, IxonCase::Refr),
                (15, IxonCase::Recr),
                (15, IxonCase::Apps),
                (15, IxonCase::Lams),
                (15, IxonCase::Alls),
                (20, IxonCase::LetE),
                (50, IxonCase::Proj),
                (100, IxonCase::Strl),
                (100, IxonCase::Natl),
                (10, IxonCase::List),
                (100, IxonCase::Defn),
                (100, IxonCase::Axio),
                (100, IxonCase::Quot),
                (100, IxonCase::CPrj),
                (100, IxonCase::RPrj),
                (100, IxonCase::IPrj),
                (100, IxonCase::DPrj),
                (15, IxonCase::Inds),
                (15, IxonCase::Defs),
                (100, IxonCase::Meta),
                (100, IxonCase::Prof),
                (100, IxonCase::Eval),
                (100, IxonCase::Chck),
                (100, IxonCase::Comm),
                (100, IxonCase::Envn),
            ];

            match next_case(g, &gens) {
                IxonCase::Vari => {
                    let x: u64 = Arbitrary::arbitrary(g);
                    unsafe {
                        ptr::replace(ptr, Ixon::Vari(x));
                    }
                }
                IxonCase::Sort => {
                    let u = arbitrary_univ(g, ctx);
                    unsafe {
                        ptr::replace(ptr, Ixon::Sort(Box::new(u)));
                    }
                }
                IxonCase::Refr => {
                    let addr = Address::arbitrary(g);
                    let mut lvls = vec![];
                    for _ in 0..gen_range(g, 0..9) {
                        lvls.push(arbitrary_univ(g, ctx));
                    }
                    unsafe {
                        ptr::replace(ptr, Ixon::Refr(addr, lvls));
                    }
                }
                IxonCase::Recr => {
                    let n = u64::arbitrary(g);
                    let mut lvls = vec![];
                    for _ in 0..gen_range(g, 0..9) {
                        lvls.push(arbitrary_univ(g, ctx));
                    }
                    unsafe {
                        ptr::replace(ptr, Ixon::Recr(n, lvls));
                    }
                }
                IxonCase::Apps => {
                    let mut f_box = Box::new(Ixon::default());
                    let f_ptr: *mut Ixon = &mut *f_box;
                    stack.push(f_ptr);

                    let mut a_box = Box::new(Ixon::default());
                    let a_ptr: *mut Ixon = &mut *a_box;
                    stack.push(a_ptr);

                    let n = gen_range(g, 0..9);
                    let mut xs: Vec<Ixon> = Vec::with_capacity(n);
                    xs.resize(n, Ixon::Vari(0));
                    for i in 0..n {
                        let p = unsafe { xs.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    unsafe {
                        std::ptr::replace(ptr, Ixon::Apps(f_box, a_box, xs));
                    }
                }
                IxonCase::Lams => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Vari(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    let mut b_box = Box::new(Ixon::default());
                    let b_ptr: *mut Ixon = &mut *b_box;
                    stack.push(b_ptr);
                    unsafe {
                        std::ptr::replace(ptr, Ixon::Lams(ts, b_box));
                    }
                }
                IxonCase::Alls => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Vari(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    let mut b_box = Box::new(Ixon::default());
                    let b_ptr: *mut Ixon = &mut *b_box;
                    stack.push(b_ptr);
                    unsafe {
                        std::ptr::replace(ptr, Ixon::Alls(ts, b_box));
                    }
                }
                IxonCase::LetE => {
                    let nd = bool::arbitrary(g);
                    let mut t_box = Box::new(Ixon::default());
                    let t_ptr: *mut Ixon = &mut *t_box;
                    stack.push(t_ptr);
                    let mut d_box = Box::new(Ixon::default());
                    let d_ptr: *mut Ixon = &mut *d_box;
                    stack.push(d_ptr);
                    let mut b_box = Box::new(Ixon::default());
                    let b_ptr: *mut Ixon = &mut *b_box;
                    stack.push(b_ptr);
                    unsafe {
                        ptr::replace(ptr, Ixon::LetE(nd, t_box, d_box, b_box));
                    }
                }
                IxonCase::Proj => {
                    let addr = Address::arbitrary(g);
                    let n = u64::arbitrary(g);
                    let mut t_box = Box::new(Ixon::default());
                    let t_ptr: *mut Ixon = &mut *t_box;
                    stack.push(t_ptr);
                    unsafe {
                        ptr::replace(ptr, Ixon::Proj(addr, n, t_box));
                    }
                }
                IxonCase::Strl => unsafe {
                    let size = gen_range(g, 0..9);
                    ptr::replace(ptr, Ixon::Strl(arbitrary_string(g, size)));
                },
                IxonCase::Natl => {
                    let size = gen_range(g, 0..9);
                    unsafe {
                        ptr::replace(ptr, Ixon::Natl(arbitrary_nat(g, size)));
                    }
                }
                IxonCase::List => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Vari(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    unsafe {
                        std::ptr::replace(ptr, Ixon::List(ts));
                    }
                }
                IxonCase::Quot => unsafe {
                    std::ptr::replace(ptr, Ixon::Quot(Quotient::arbitrary(g)));
                },
                IxonCase::Axio => unsafe {
                    std::ptr::replace(ptr, Ixon::Axio(Axiom::arbitrary(g)));
                },
                IxonCase::Defn => unsafe {
                    std::ptr::replace(ptr, Ixon::Defn(Definition::arbitrary(g)));
                },
                IxonCase::CPrj => unsafe {
                    std::ptr::replace(ptr, Ixon::CPrj(ConstructorProj::arbitrary(g)));
                },
                IxonCase::RPrj => unsafe {
                    std::ptr::replace(ptr, Ixon::RPrj(RecursorProj::arbitrary(g)));
                },
                IxonCase::DPrj => unsafe {
                    std::ptr::replace(ptr, Ixon::DPrj(DefinitionProj::arbitrary(g)));
                },
                IxonCase::IPrj => unsafe {
                    std::ptr::replace(ptr, Ixon::IPrj(InductiveProj::arbitrary(g)));
                },
                IxonCase::Inds => unsafe {
                    let inds = gen_vec(g, 9, Inductive::arbitrary);
                    std::ptr::replace(ptr, Ixon::Inds(inds));
                },
                IxonCase::Defs => unsafe {
                    let defs = gen_vec(g, 9, Definition::arbitrary);
                    std::ptr::replace(ptr, Ixon::Defs(defs));
                },
                IxonCase::Meta => unsafe {
                    std::ptr::replace(ptr, Ixon::Meta(Metadata::arbitrary(g)));
                },
                IxonCase::Prof => unsafe {
                    std::ptr::replace(ptr, Ixon::Prof(Proof::arbitrary(g)));
                },
                IxonCase::Eval => unsafe {
                    std::ptr::replace(ptr, Ixon::Eval(EvalClaim::arbitrary(g)));
                },
                IxonCase::Chck => unsafe {
                    std::ptr::replace(ptr, Ixon::Chck(CheckClaim::arbitrary(g)));
                },
                IxonCase::Comm => unsafe {
                    std::ptr::replace(ptr, Ixon::Comm(Comm::arbitrary(g)));
                },
                IxonCase::Envn => unsafe {
                    std::ptr::replace(ptr, Ixon::Envn(Env::arbitrary(g)));
                },
            }
        }
        root
    }

    impl Arbitrary for Ixon {
        fn arbitrary(g: &mut Gen) -> Self {
            let ctx: u64 = Arbitrary::arbitrary(g);
            arbitrary_ixon(g, ctx)
        }
    }

    #[quickcheck]
    fn prop_ixon_readback(x: Ixon) -> bool {
        let mut buf = Vec::new();
        Ixon::put(&x, &mut buf);
        match Ixon::get(&mut buf.as_slice()) {
            Ok(y) => x == y,
            Err(e) => {
                println!("err: {e}");
                false
            }
        }
    }
}

//}
