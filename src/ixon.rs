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
                Self::put_tag(0x2, *x, buf);
                Ixon::put_array(lvls, buf);
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
                let x = Ixon::get_size(is_large, small_size, buf)?;
                let lvls = Ixon::get_array(buf)?;
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
    use std::fmt::Write;
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

    /// Parse a hex string (optional `0x`/`0X` prefix, `_` separators OK) into bytes.
    pub fn parse_hex(s: &str) -> Result<Vec<u8>, String> {
        // Strip prefix, drop underscores, and require an even count of hex digits.
        let s = s.trim();
        let s = s
            .strip_prefix("0x")
            .or_else(|| s.strip_prefix("0X"))
            .unwrap_or(s);
        let clean: String = s.chars().filter(|&c| c != '_').collect();

        if clean.len() % 2 != 0 {
            return Err("odd number of hex digits".into());
        }

        // Parse each 2-char chunk as a byte.
        (0..clean.len())
            .step_by(2)
            .map(|i| {
                u8::from_str_radix(&clean[i..i + 2], 16)
                    .map_err(|_| format!("invalid hex at chars {}..{}", i, i + 2))
            })
            .collect()
    }

    /// Format bytes as a lowercase hex string with a `0x` prefix.
    pub fn to_hex(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(2 + bytes.len() * 2);
        out.push_str("0x");
        for b in bytes {
            // `{:02x}` = two lowercase hex digits, zero-padded.
            write!(&mut out, "{b:02x}").unwrap();
        }
        out
    }

    #[test]
    fn unit_ixon() {
        fn test(input: Ixon, expected: &str) -> bool {
            let mut tmp = Vec::new();
            let expect = parse_hex(expected).unwrap();
            Serialize::put(&input, &mut tmp);
            if tmp != expect {
                println!(
                    "serialied {input:?} as:\n {}\n test expects:\n {}",
                    to_hex(&tmp),
                    to_hex(&expect),
                );
                return false;
            }
            match Serialize::get(&mut tmp.as_slice()) {
                Ok(output) => {
                    if input != output {
                        println!(
                            "deserialized {} as {output:?}, expected {input:?}",
                            to_hex(&tmp)
                        );
                        false
                    } else {
                        true
                    }
                }
                Err(e) => {
                    println!("err: {e}");
                    false
                }
            }
        }
        assert!(test(Ixon::Vari(0x0), "0x00"));
        assert!(test(Ixon::Vari(0x7), "0x07"));
        assert!(test(Ixon::Vari(0x8), "0x0808"));
        assert!(test(Ixon::Vari(0xff), "0x08FF"));
        assert!(test(Ixon::Vari(0x0100), "0x090001"));
        assert!(test(Ixon::Vari(0xFFFF), "0x09FFFF"));
        assert!(test(Ixon::Vari(0x010000), "0x0A000001"));
        assert!(test(Ixon::Vari(0xFFFFFF), "0x0AFFFFFF"));
        assert!(test(Ixon::Vari(0x01000000), "0x0B00000001"));
        assert!(test(Ixon::Vari(0xFFFFFFFF), "0x0BFFFFFFFF"));
        assert!(test(Ixon::Vari(0x0100000000), "0x0C0000000001"));
        assert!(test(Ixon::Vari(0xFFFFFFFFFF), "0x0CFFFFFFFFFF"));
        assert!(test(Ixon::Vari(0x010000000000), "0x0D000000000001"));
        assert!(test(Ixon::Vari(0xFFFFFFFFFFFF), "0x0DFFFFFFFFFFFF"));
        assert!(test(Ixon::Vari(0x01000000000000), "0x0E00000000000001"));
        assert!(test(Ixon::Vari(0xFFFFFFFFFFFFFF), "0x0EFFFFFFFFFFFFFF"));
        assert!(test(Ixon::Vari(0x0100000000000000), "0x0F0000000000000001"));
        assert!(test(Ixon::Vari(0xFFFFFFFFFFFFFFFF), "0x0FFFFFFFFFFFFFFFFF"));
        // universes use 2-bit sub-tags
        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x0))), "0x9000"));
        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x1F))), "0x901F"));
        assert!(test(Ixon::Sort(Box::new(Univ::Const(0x20))), "0x902020"));
        assert!(test(Ixon::Sort(Box::new(Univ::Const(0xFF))), "0x9020FF"));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x0100))),
            "0x90210001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFF))),
            "0x9021FFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x010000))),
            "0x9022000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFF))),
            "0x9022FFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x01000000))),
            "0x902300000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFF))),
            "0x9023FFFFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x0100000000))),
            "0x90240000000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFF))),
            "0x9024FFFFFFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x010000000000))),
            "0x9025000000000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFF))),
            "0x9025FFFFFFFFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x01000000000000))),
            "0x902600000000000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFFFF))),
            "0x9026FFFFFFFFFFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0x0100000000000000))),
            "0x90270000000000000001"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Const(0xFFFFFFFFFFFFFFFF))),
            "0x9027FFFFFFFFFFFFFFFF"
        ));
        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x0))), "0x9040"));
        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x1F))), "0x905F"));
        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x20))), "0x906020"));
        assert!(test(Ixon::Sort(Box::new(Univ::Var(0xFF))), "0x9060FF"));
        assert!(test(Ixon::Sort(Box::new(Univ::Var(0x0100))), "0x90610001"));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Var(0xFFFFFFFFFFFFFFFF))),
            "0x9067FFFFFFFFFFFFFFFF"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(0x0, Box::new(Univ::Const(0x0))))),
            "0x908000"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(0x0, Box::new(Univ::Var(0x0))))),
            "0x908040"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(0x1F, Box::new(Univ::Var(0x0))))),
            "0x909F40"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(0x20, Box::new(Univ::Var(0x0))))),
            "0x90A02040"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(0xFF, Box::new(Univ::Var(0x0))))),
            "0x90A0FF40"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Add(
                0xFFFF_FFFF_FFFF_FFFF,
                Box::new(Univ::Var(0x0))
            ))),
            "0x90A7FFFFFFFFFFFFFFFF40"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Max(
                Box::new(Univ::Var(0x0)),
                Box::new(Univ::Var(0x0))
            ))),
            "0x90C04040"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Max(
                Box::new(Univ::Var(0x0)),
                Box::new(Univ::Var(0x1))
            ))),
            "0x90C04041"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Max(
                Box::new(Univ::Var(0x1)),
                Box::new(Univ::Var(0x0))
            ))),
            "0x90C04140"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::Max(
                Box::new(Univ::Var(0x1)),
                Box::new(Univ::Var(0x1))
            ))),
            "0x90C04141"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::IMax(
                Box::new(Univ::Var(0x0)),
                Box::new(Univ::Var(0x0))
            ))),
            "0x90C14040"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::IMax(
                Box::new(Univ::Var(0x0)),
                Box::new(Univ::Var(0x1))
            ))),
            "0x90C14041"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::IMax(
                Box::new(Univ::Var(0x1)),
                Box::new(Univ::Var(0x0))
            ))),
            "0x90C14140"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::IMax(
                Box::new(Univ::Var(0x1)),
                Box::new(Univ::Var(0x1))
            ))),
            "0x90C14141"
        ));
        assert!(test(
            Ixon::Sort(Box::new(Univ::IMax(
                Box::new(Univ::Var(0x1)),
                Box::new(Univ::Var(0x1))
            ))),
            "0x90C14141"
        ));
        assert!(test(
            Ixon::Refr(Address::hash(&[]), vec![]),
            "0x10af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Refr(Address::hash(&[]), vec![Univ::Var(0x0)]),
            "0x11af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326240"
        ));
        assert!(test(Ixon::Recr(0x0, vec![Univ::Var(0x0)]), "0x20A140"));
        assert!(test(
            Ixon::Recr(0x0, vec![Univ::Var(0x0), Univ::Var(0x1)]),
            "0x20A24041"
        ));
        assert!(test(
            Ixon::Recr(0x8, vec![Univ::Var(0x0), Univ::Var(0x1)]),
            "0x2808A24041"
        ));
        assert!(test(
            Ixon::Apps(Box::new(Ixon::Vari(0x0)), Box::new(Ixon::Vari(0x1)), vec![]),
            "0x300001"
        ));
        assert!(test(
            Ixon::Apps(
                Box::new(Ixon::Vari(0x0)),
                Box::new(Ixon::Vari(0x1)),
                vec![Ixon::Vari(0x2)]
            ),
            "0x31000102"
        ));
        assert!(test(
            Ixon::Apps(
                Box::new(Ixon::Vari(0x0)),
                Box::new(Ixon::Vari(0x1)),
                vec![
                    Ixon::Vari(0x2),
                    Ixon::Vari(0x3),
                    Ixon::Vari(0x4),
                    Ixon::Vari(0x5),
                    Ixon::Vari(0x6),
                    Ixon::Vari(0x7),
                    Ixon::Vari(0x8),
                    Ixon::Vari(0x9),
                ]
            ),
            "0x3808000102030405060708080809"
        ));
        assert!(test(
            Ixon::Lams(vec![Ixon::Vari(0x0)], Box::new(Ixon::Vari(0x1))),
            "0x410001"
        ));
        assert!(test(
            Ixon::Lams(
                vec![
                    Ixon::Vari(0x0),
                    Ixon::Vari(0x1),
                    Ixon::Vari(0x2),
                    Ixon::Vari(0x3),
                    Ixon::Vari(0x4),
                    Ixon::Vari(0x5),
                    Ixon::Vari(0x6),
                    Ixon::Vari(0x7)
                ],
                Box::new(Ixon::Vari(0x8))
            ),
            "0x480800010203040506070808"
        ));
        assert!(test(
            Ixon::Alls(vec![Ixon::Vari(0x0)], Box::new(Ixon::Vari(0x1))),
            "0x510001"
        ));
        assert!(test(
            Ixon::Alls(
                vec![
                    Ixon::Vari(0x0),
                    Ixon::Vari(0x1),
                    Ixon::Vari(0x2),
                    Ixon::Vari(0x3),
                    Ixon::Vari(0x4),
                    Ixon::Vari(0x5),
                    Ixon::Vari(0x6),
                    Ixon::Vari(0x7)
                ],
                Box::new(Ixon::Vari(0x8))
            ),
            "0x580800010203040506070808"
        ));
        assert!(test(
            Ixon::Proj(Address::hash(&[]), 0x0, Box::new(Ixon::Vari(0x0))),
            "0x60af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200"
        ));
        assert!(test(
            Ixon::Proj(Address::hash(&[]), 0x8, Box::new(Ixon::Vari(0x0))),
            "0x6808af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200"
        ));
        assert!(test(Ixon::Strl("".to_string()), "0x70"));
        assert!(test(Ixon::Strl("foobar".to_string()), "0x76666f6f626172"));
        assert!(test(Ixon::Natl(Nat::new_le(&[])), "0x8100"));
        assert!(test(Ixon::Natl(Nat::new_le(&[0x0])), "0x8100"));
        assert!(test(Ixon::Natl(Nat::new_le(&[0xFF])), "0x81FF"));
        assert!(test(Ixon::Natl(Nat::new_le(&[0x00, 0x01])), "0x820001"));
        assert!(test(
            Ixon::LetE(
                true,
                Box::new(Ixon::Vari(0x0)),
                Box::new(Ixon::Vari(0x1)),
                Box::new(Ixon::Vari(0x2))
            ),
            "0x91000102"
        ));
        assert!(test(Ixon::List(vec![]), "0xA0"));
        assert!(test(
            Ixon::List(vec![Ixon::Vari(0x0), Ixon::Vari(0x1), Ixon::Vari(0x2)]),
            "0xA3000102"
        ));
        assert!(test(
            Ixon::Defn(Definition {
                kind: DefKind::Definition,
                safety: DefSafety::Unsafe,
                lvls: 0u64.into(),
                typ: Address::hash(&[]),
                value: Address::hash(&[]),
            }),
            "0xB000008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Defn(Definition {
                kind: DefKind::Opaque,
                safety: DefSafety::Safe,
                lvls: 1u64.into(),
                typ: Address::hash(&[]),
                value: Address::hash(&[]),
            }),
            "0xB001018101af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Axio(Axiom {
                is_unsafe: true,
                lvls: 0u64.into(),
                typ: Address::hash(&[]),
            }),
            "0xB1018100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Quot(Quotient {
                kind: QuotKind::Type,
                lvls: 0u64.into(),
                typ: Address::hash(&[]),
            }),
            "0xB2008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::CPrj(ConstructorProj {
                idx: 0u64.into(),
                cidx: 0u64.into(),
                block: Address::hash(&[]),
            }),
            "0xB381008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::RPrj(RecursorProj {
                idx: 0u64.into(),
                ridx: 0u64.into(),
                block: Address::hash(&[]),
            }),
            "0xB481008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::IPrj(InductiveProj {
                idx: 0u64.into(),
                block: Address::hash(&[]),
            }),
            "0xB58100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::DPrj(DefinitionProj {
                idx: 0u64.into(),
                block: Address::hash(&[]),
            }),
            "0xB68100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(Ixon::Inds(vec![]), "0xC0"));
        assert!(test(
            Ixon::Inds(vec![Inductive {
                recr: false,
                refl: false,
                is_unsafe: false,
                lvls: 0u64.into(),
                params: 0u64.into(),
                indices: 0u64.into(),
                nested: 0u64.into(),
                typ: Address::hash(&[]),
                ctors: vec![],
                recrs: vec![],
            }]),
            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A0A0"
        ));
        assert!(test(
            Ixon::Inds(vec![Inductive {
                recr: false,
                refl: false,
                is_unsafe: false,
                lvls: 0u64.into(),
                params: 0u64.into(),
                indices: 0u64.into(),
                nested: 0u64.into(),
                typ: Address::hash(&[]),
                ctors: vec![],
                recrs: vec![],
            }]),
            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A0A0"
        ));
        assert!(test(
            Ixon::Inds(vec![Inductive {
                recr: false,
                refl: false,
                is_unsafe: false,
                lvls: 0u64.into(),
                params: 0u64.into(),
                indices: 0u64.into(),
                nested: 0u64.into(),
                typ: Address::hash(&[]),
                ctors: vec![Constructor {
                    is_unsafe: false,
                    lvls: 0u64.into(),
                    cidx: 0u64.into(),
                    params: 0u64.into(),
                    fields: 0u64.into(),
                    typ: Address::hash(&[])
                }],
                recrs: vec![Recursor {
                    k: false,
                    is_unsafe: false,
                    lvls: 0u64.into(),
                    params: 0u64.into(),
                    indices: 0u64.into(),
                    motives: 0u64.into(),
                    minors: 0u64.into(),
                    typ: Address::hash(&[]),
                    rules: vec![RecursorRule {
                        fields: 0u64.into(),
                        rhs: Address::hash(&[])
                    }]
                }],
            }]),
            "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A10081008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A18100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(Ixon::Defs(vec![]), "0xD0"));
        assert!(test(
            Ixon::Defs(vec![Definition {
                kind: DefKind::Definition,
                safety: DefSafety::Unsafe,
                lvls: 0u64.into(),
                typ: Address::hash(&[]),
                value: Address::hash(&[]),
            }]),
            "0xD100008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(Ixon::Meta(Metadata { map: vec![] }), "0xE0A0"));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![])]
            }),
            "0xE0A18100A0"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![Metadatum::Name(Name { parts: vec![] })])]
            }),
            "0xE0A18100A100A0"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Name(Name {
                        parts: vec![NamePart::Str("a".to_string())]
                    })]
                )]
            }),
            "0xE0A18100A100A17161"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Name(Name {
                        parts: vec![
                            NamePart::Str("a".to_string()),
                            NamePart::Str("b".to_string()),
                        ]
                    })]
                )]
            }),
            "0xE0A18100A100A271617162"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Name(Name {
                        parts: vec![
                            NamePart::Str("a".to_string()),
                            NamePart::Str("b".to_string()),
                            NamePart::Str("c".to_string()),
                        ]
                    })]
                )]
            }),
            "0xE0A18100A100A3716171627163"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Name(Name {
                        parts: vec![NamePart::Num(165851424810452359u64.into())]
                    })]
                )]
            }),
            "0xE0A18100A100A1880887C551FDFD384D02"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![Metadatum::Info(BinderInfo::Default)])]
            }),
            "0xE0A18100A10100"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![Metadatum::Link(Address::hash(&[]))])]
            }),
            "0xE0A18100A102af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![
                        Metadatum::Name(Name {
                            parts: vec![NamePart::Str("d".to_string())]
                        }),
                        Metadatum::Link(Address::hash(&[])),
                        Metadatum::Hints(ReducibilityHints::Regular(576554452)),
                        Metadatum::Link(Address::hash(&[]))
                    ]
                )]
            }),
            "0xe0a18100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Hints(ReducibilityHints::Opaque)]
                )]
            }),
            "0xE0A18100A10300"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![Metadatum::All(vec![])])]
            }),
            "0xE0A18100A104A0"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(0u64.into(), vec![Metadatum::MutCtx(vec![])])]
            }),
            "0xE0A18100A105A0"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![(
                    0u64.into(),
                    vec![Metadatum::Hints(ReducibilityHints::Regular(42))]
                )]
            }),
            "0xe0a18100a103022a000000"
        ));
        assert!(test(
            Ixon::Meta(Metadata {
                map: vec![
                    (
                        0u64.into(),
                        vec![
                            Metadatum::Name(Name {
                                parts: vec![NamePart::Str("d".to_string())]
                            }),
                            Metadatum::Link(Address::hash(&[])),
                            Metadatum::Hints(ReducibilityHints::Regular(576554452)),
                            Metadatum::Link(Address::hash(&[]))
                        ]
                    ),
                    (
                        1u64.into(),
                        vec![
                            Metadatum::Info(BinderInfo::InstImplicit),
                            Metadatum::Info(BinderInfo::InstImplicit),
                            Metadatum::Info(BinderInfo::StrictImplicit),
                        ]
                    ),
                    (
                        2u64.into(),
                        vec![
                            Metadatum::All(vec![Name {
                                parts: vec![NamePart::Num(165851424810452359u64.into())]
                            }]),
                            Metadatum::Info(BinderInfo::Default)
                        ]
                    ),
                    (3u64.into(), vec![]),
                    (4u64.into(), vec![]),
                    (
                        5u64.into(),
                        vec![Metadatum::Hints(ReducibilityHints::Opaque)]
                    ),
                    (
                        6u64.into(),
                        vec![Metadatum::Name(Name {
                            parts: vec![NamePart::Num(871843802607008850u64.into())]
                        })]
                    )
                ]
            }),
            "0xe0a78100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32628101a30103010301028102a204a1a1880887c551fdfd384d0201008103a08104a08105a103008106a100a18808523c04ba5169190c"
        ));
    }
}

//}
