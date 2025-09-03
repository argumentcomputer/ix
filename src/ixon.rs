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
    Var(u64),                                   // 0x0X, variables
    Sort(Box<Univ>),                            // 0xB0, universes
    Ref(Address, Vec<Univ>),                    // 0x1X, global reference
    Rec(u64, Vec<Univ>),                        // 0x2X, local const recursion
    App(Box<Ixon>, Box<Ixon>, Vec<Ixon>),       // 0x3X, applications
    Lam(Vec<Ixon>, Box<Ixon>),                  // 0x4X, lambdas
    All(Vec<Ixon>, Box<Ixon>),                  // 0x5X, foralls
    Proj(Address, u64, Box<Ixon>),              // 0x6X, structure projection
    Strl(String),                               // 0x7X, unicode string
    Natl(Nat),                                  // 0x8X, natural numbers
    Let(bool, Box<Ixon>, Box<Ixon>, Box<Ixon>), // 0xB1, 0xB2, local binder
    Array(Vec<Ixon>),                           // 0xA, array
    Defn(Definition),                           // 0xC0, definition
    Axio(Axiom),                                // 0xC1, axiom
    Quot(Quotient),                             // 0xC2, quotient
    CtorProj(ConstructorProj),                  // 0xC3, constructor projection
    RecrProj(RecursorProj),                     // 0xC4, recursor projection
    IndcProj(InductiveProj),                    // 0xC5, inductive projection
    DefnProj(DefinitionProj),                   // 0xC6, definition projection
    Meta(Metadata),                             // 0xC7, metadata
    Proof(Proof),                               // 0xC8, zero-knowledge proof
    Claim(Claim),                               // 0xC9, cryptographic claim
    Comm(Comm),                                 // 0xCA, cryptographic commitment
    Env(Env),                                   // 0xCB, multi-claim environment
    MutDef(Vec<Definition>),                    // 0xDX, mutual definition
    MutInd(Vec<Inductive>),                     // 0xEX, mutual inductive data
                                                // unused: 0x9, 0xB3..0xBF, 0xFX
}

impl Default for Ixon {
    fn default() -> Self {
        Self::Var(0)
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
            Self::Var(x) => Self::put_tag(0x0, *x, buf),
            Self::Sort(x) => {
                u8::put(&0xB0, buf);
                x.put(buf);
            }
            Self::Ref(addr, lvls) => {
                Self::put_tag(0x1, lvls.len() as u64, buf);
                addr.put(buf);
                for l in lvls {
                    l.put(buf);
                }
            }
            Self::Rec(x, lvls) => {
                Self::put_tag(0x2, lvls.len() as u64, buf);
                x.put(buf);
                for l in lvls {
                    l.put(buf);
                }
            }
            Self::App(f, a, args) => {
                Self::put_tag(0x3, args.len() as u64, buf);
                f.put(buf);
                a.put(buf);
                for x in args {
                    x.put(buf);
                }
            }
            Self::Lam(ts, b) => {
                Self::put_tag(0x4, ts.len() as u64, buf);
                for t in ts {
                    t.put(buf);
                }
                b.put(buf);
            }
            Self::All(ts, b) => {
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
            Self::Let(nd, t, d, b) => {
                if *nd {
                    u8::put(&0xB2, buf);
                } else {
                    u8::put(&0xB1, buf);
                }
                t.put(buf);
                d.put(buf);
                b.put(buf);
            }
            Self::Array(xs) => Ixon::put_array(xs, buf),
            Self::Defn(x) => {
                u8::put(&0xC0, buf);
                x.put(buf);
            }
            Self::Axio(x) => {
                u8::put(&0xC1, buf);
                x.put(buf);
            }
            Self::Quot(x) => {
                u8::put(&0xC2, buf);
                x.put(buf);
            }
            Self::CtorProj(x) => {
                u8::put(&0xC3, buf);
                x.put(buf);
            }
            Self::RecrProj(x) => {
                u8::put(&0xC4, buf);
                x.put(buf);
            }
            Self::IndcProj(x) => {
                u8::put(&0xC5, buf);
                x.put(buf);
            }
            Self::DefnProj(x) => {
                u8::put(&0xC6, buf);
                x.put(buf);
            }
            Self::Meta(x) => {
                u8::put(&0xC7, buf);
                x.put(buf);
            }
            Self::Proof(x) => {
                u8::put(&0xC8, buf);
                x.put(buf);
            }
            Self::Claim(x) => {
                u8::put(&0xC9, buf);
                x.put(buf);
            }
            Self::Comm(x) => {
                u8::put(&0xCA, buf);
                x.put(buf);
            }
            Self::Env(x) => {
                u8::put(&0xCB, buf);
                x.put(buf);
            }
            Self::MutDef(xs) => {
                Self::put_tag(0xD, xs.len() as u64, buf);
                for x in xs {
                    x.put(buf);
                }
            }
            Self::MutInd(xs) => {
                Self::put_tag(0xE, xs.len() as u64, buf);
                for x in xs {
                    x.put(buf);
                }
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
                Ok(Self::Var(x))
            }
            0xB0 => {
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
                Ok(Self::Ref(a, lvls))
            }
            0x20..=0x2F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let x = u64::get(buf)?;
                let mut lvls = Vec::new();
                for _ in 0..n {
                    let l = Univ::get(buf)?;
                    lvls.push(l);
                }
                Ok(Self::Rec(x, lvls))
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
                Ok(Self::App(Box::new(f), Box::new(a), args))
            }
            0x40..=0x4F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut ts = Vec::new();
                for _ in 0..n {
                    let x = Ixon::get(buf)?;
                    ts.push(x);
                }
                let b = Ixon::get(buf)?;
                Ok(Self::Lam(ts, Box::new(b)))
            }
            0x50..=0x5F => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut ts = Vec::new();
                for _ in 0..n {
                    let x = Ixon::get(buf)?;
                    ts.push(x);
                }
                let b = Ixon::get(buf)?;
                Ok(Self::All(ts, Box::new(b)))
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
            0xB1..=0xB2 => {
                let nd = tag_byte == 0xB2;
                let t = Ixon::get(buf)?;
                let d = Ixon::get(buf)?;
                let b = Ixon::get(buf)?;
                Ok(Self::Let(nd, Box::new(t), Box::new(d), Box::new(b)))
            }
            0xA0..=0xAF => {
                let len = Self::get_size(is_large, small_size, buf)?;
                let mut vec = vec![];
                for _ in 0..len {
                    let s = Ixon::get(buf)?;
                    vec.push(s);
                }
                Ok(Self::Array(vec))
            }
            0xC0 => Ok(Self::Defn(Definition::get(buf)?)),
            0xC1 => Ok(Self::Axio(Axiom::get(buf)?)),
            0xC2 => Ok(Self::Quot(Quotient::get(buf)?)),
            0xC3 => Ok(Self::CtorProj(ConstructorProj::get(buf)?)),
            0xC4 => Ok(Self::RecrProj(RecursorProj::get(buf)?)),
            0xC5 => Ok(Self::IndcProj(InductiveProj::get(buf)?)),
            0xC6 => Ok(Self::DefnProj(DefinitionProj::get(buf)?)),
            0xC7 => Ok(Self::Meta(Metadata::get(buf)?)),
            0xC8 => Ok(Self::Proof(Proof::get(buf)?)),
            0xC9 => Ok(Self::Claim(Claim::get(buf)?)),
            0xCA => Ok(Self::Comm(Comm::get(buf)?)),
            0xCB => Ok(Self::Env(Env::get(buf)?)),
            0xD0..=0xDF => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut defs = Vec::new();
                for _ in 0..n {
                    let x = Definition::get(buf)?;
                    defs.push(x);
                }
                Ok(Self::MutDef(defs))
            }
            0xE0..=0xEF => {
                let n = Ixon::get_size(is_large, small_size, buf)?;
                let mut inds = Vec::new();
                for _ in 0..n {
                    let x = Inductive::get(buf)?;
                    inds.push(x);
                }
                Ok(Self::MutInd(inds))
            }
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
        Var,
        Sort,
        Ref,
        Rec,
        App,
        Lam,
        All,
        Proj,
        Strl,
        Natl,
        Let,
        Array,
        Defn,
        Axio,
        Quot,
        CtorProj,
        RecrProj,
        IndcProj,
        DefnProj,
        Meta,
        Proof,
        Claim,
        Comm,
        Env,
        MutDef,
        MutInd,
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
        let mut root = Ixon::Var(0);
        let mut stack = vec![&mut root as *mut Ixon];

        while let Some(ptr) = stack.pop() {
            let gens: Vec<(usize, IxonCase)> = vec![
                (100, IxonCase::Var),
                (100, IxonCase::Sort),
                (15, IxonCase::Ref),
                (15, IxonCase::Rec),
                (15, IxonCase::App),
                (15, IxonCase::Lam),
                (15, IxonCase::All),
                (50, IxonCase::Let),
                (50, IxonCase::Proj),
                (100, IxonCase::Strl),
                (100, IxonCase::Natl),
                (10, IxonCase::Array),
                (100, IxonCase::Defn),
                (100, IxonCase::Axio),
                (100, IxonCase::Quot),
                (100, IxonCase::CtorProj),
                (100, IxonCase::RecrProj),
                (100, IxonCase::IndcProj),
                (100, IxonCase::DefnProj),
                (100, IxonCase::Meta),
                (100, IxonCase::Proof),
                (100, IxonCase::Claim),
                (100, IxonCase::Comm),
                (100, IxonCase::Env),
                (15, IxonCase::MutDef),
                (15, IxonCase::MutInd),
            ];

            match next_case(g, &gens) {
                IxonCase::Var => {
                    let x: u64 = Arbitrary::arbitrary(g);
                    unsafe {
                        ptr::replace(ptr, Ixon::Var(x));
                    }
                }
                IxonCase::Sort => {
                    let u = arbitrary_univ(g, ctx);
                    unsafe {
                        ptr::replace(ptr, Ixon::Sort(Box::new(u)));
                    }
                }
                IxonCase::Ref => {
                    let addr = Address::arbitrary(g);
                    let mut lvls = vec![];
                    for _ in 0..gen_range(g, 0..9) {
                        lvls.push(arbitrary_univ(g, ctx));
                    }
                    unsafe {
                        ptr::replace(ptr, Ixon::Ref(addr, lvls));
                    }
                }
                IxonCase::Rec => {
                    let n = u64::arbitrary(g);
                    let mut lvls = vec![];
                    for _ in 0..gen_range(g, 0..9) {
                        lvls.push(arbitrary_univ(g, ctx));
                    }
                    unsafe {
                        ptr::replace(ptr, Ixon::Rec(n, lvls));
                    }
                }
                IxonCase::App => {
                    let mut f_box = Box::new(Ixon::default());
                    let f_ptr: *mut Ixon = &mut *f_box;
                    stack.push(f_ptr);

                    let mut a_box = Box::new(Ixon::default());
                    let a_ptr: *mut Ixon = &mut *a_box;
                    stack.push(a_ptr);

                    let n = gen_range(g, 0..9);
                    let mut xs: Vec<Ixon> = Vec::with_capacity(n);
                    xs.resize(n, Ixon::Var(0));
                    for i in 0..n {
                        let p = unsafe { xs.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    unsafe {
                        std::ptr::replace(ptr, Ixon::App(f_box, a_box, xs));
                    }
                }
                IxonCase::Lam => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Var(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    let mut b_box = Box::new(Ixon::default());
                    let b_ptr: *mut Ixon = &mut *b_box;
                    stack.push(b_ptr);
                    unsafe {
                        std::ptr::replace(ptr, Ixon::Lam(ts, b_box));
                    }
                }
                IxonCase::All => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Var(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    let mut b_box = Box::new(Ixon::default());
                    let b_ptr: *mut Ixon = &mut *b_box;
                    stack.push(b_ptr);
                    unsafe {
                        std::ptr::replace(ptr, Ixon::All(ts, b_box));
                    }
                }
                IxonCase::Let => {
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
                        ptr::replace(ptr, Ixon::Let(nd, t_box, d_box, b_box));
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
                IxonCase::Array => {
                    let n = gen_range(g, 0..9);
                    let mut ts: Vec<Ixon> = Vec::with_capacity(n);
                    ts.resize(n, Ixon::Var(0));
                    for i in 0..n {
                        let p = unsafe { ts.as_mut_ptr().add(i) };
                        stack.push(p);
                    }
                    unsafe {
                        std::ptr::replace(ptr, Ixon::Array(ts));
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
                IxonCase::CtorProj => unsafe {
                    std::ptr::replace(ptr, Ixon::CtorProj(ConstructorProj::arbitrary(g)));
                },
                IxonCase::RecrProj => unsafe {
                    std::ptr::replace(ptr, Ixon::RecrProj(RecursorProj::arbitrary(g)));
                },
                IxonCase::DefnProj => unsafe {
                    std::ptr::replace(ptr, Ixon::DefnProj(DefinitionProj::arbitrary(g)));
                },
                IxonCase::IndcProj => unsafe {
                    std::ptr::replace(ptr, Ixon::IndcProj(InductiveProj::arbitrary(g)));
                },
                IxonCase::Meta => unsafe {
                    std::ptr::replace(ptr, Ixon::Meta(Metadata::arbitrary(g)));
                },
                IxonCase::Proof => unsafe {
                    std::ptr::replace(ptr, Ixon::Proof(Proof::arbitrary(g)));
                },
                IxonCase::Claim => unsafe {
                    std::ptr::replace(ptr, Ixon::Claim(Claim::arbitrary(g)));
                },
                IxonCase::Comm => unsafe {
                    std::ptr::replace(ptr, Ixon::Comm(Comm::arbitrary(g)));
                },
                IxonCase::Env => unsafe {
                    std::ptr::replace(ptr, Ixon::Env(Env::arbitrary(g)));
                },
                IxonCase::MutDef => unsafe {
                    let defs = gen_vec(g, 9, Definition::arbitrary);
                    std::ptr::replace(ptr, Ixon::MutDef(defs));
                },
                IxonCase::MutInd => unsafe {
                    let inds = gen_vec(g, 9, Inductive::arbitrary);
                    std::ptr::replace(ptr, Ixon::MutInd(inds));
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
