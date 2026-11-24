// How many distinct vectors a bottom-up encoder needs over all theorem
// statements when a bound variable's vector depends on its binder's type,
// against the count when a variable is its de Bruijn index alone.
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{BufRead, BufReader};

#[derive(Default)]
struct Fx(u64);
impl Fx { fn add(&mut self, w: u64) { self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517cc1b727220a95); } }
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, bytes: &[u8]) { for b in bytes { self.add(*b as u64); } }
    fn write_u32(&mut self, i: u32) { self.add(i as u64); }
    fn write_u64(&mut self, i: u64) { self.add(i); }
    fn write_usize(&mut self, i: usize) { self.add(i as u64); }
}
type Map<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;

struct St<'a> {
    nodes: &'a [[u32; 4]],
    lbr: Vec<u32>,
    memo: Map<(u32, u64), u32>,
    global: &'a mut Map<[u32; 4], u32>,
    env: Vec<u32>,
    visits: u64,
}
impl St<'_> {
    fn gid(&mut self, key: [u32; 4]) -> u32 {
        let next = self.global.len() as u32;
        *self.global.entry(key).or_insert(next)
    }
    fn sig(&self, n: u32) -> u64 {
        let l = (self.lbr[n as usize] as usize).min(self.env.len());
        let mut h = Fx::default();
        for x in &self.env[self.env.len() - l..] { h.add(*x as u64); }
        h.add(l as u64);
        h.0
    }
    fn go(&mut self, n: u32) -> u32 {
        let key = (n, if self.lbr[n as usize] == 0 { 0 } else { self.sig(n) });
        if let Some(&c) = self.memo.get(&key) { return c; }
        self.visits += 1;
        let [t, a, b, c] = self.nodes[n as usize];
        let id = match t {
            1 => {
                let ty = if (a as usize) < self.env.len() { self.env[self.env.len() - 1 - a as usize] } else { u32::MAX };
                self.gid([1, a, ty, 0])
            }
            7 => { let x = self.go(a); let y = self.go(b); self.gid([7, x, y, 0]) }
            8 | 9 => {
                let d = self.go(a); self.env.push(d); let body = self.go(b); self.env.pop();
                self.gid([t, d, body, 0])
            }
            10 => {
                let ty = self.go(a); let v = self.go(b); self.env.push(ty); let body = self.go(c); self.env.pop();
                self.gid([10, ty, v, body])
            }
            4 => { let v = self.go(c); self.gid([4, a, b, v]) }
            _ => self.gid([t, a, b, c | 0x8000_0000]),
        };
        self.memo.insert(key, id);
        id
    }
}

fn run() {
    let dir = std::env::args().nth(1).unwrap();
    let bytes = std::fs::read(format!("{dir}/nodes.bin")).unwrap();
    let w = |i: usize| u32::from_le_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]]);
    let mut global: Map<[u32; 4], u32> = Map::default();
    let mut plain: Map<[u32; 4], u32> = Map::default();
    let (mut graphs, mut total, mut visits) = (0u64, 0u64, 0u64);
    let mut fresh: Vec<(u32, u32)> = Vec::new();
    for line in BufReader::new(std::fs::File::open(format!("{dir}/consts.tsv")).unwrap()).lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split('\t').collect();
        let count: usize = f[9].parse().unwrap();
        if f[2] != "thm" || count == 0 { continue; }
        let start: usize = f[8].parse().unwrap();
        let root: u32 = f[10].parse().unwrap();
        let nodes: Vec<[u32; 4]> = (0..count).map(|i| [w(4 * (start + i)), w(4 * (start + i) + 1), w(4 * (start + i) + 2), w(4 * (start + i) + 3)]).collect();
        // unconditioned ids, for the baseline count
        let before_plain = plain.len();
        let mut local: Vec<u32> = Vec::with_capacity(count);
        let mut lbr: Vec<u32> = Vec::with_capacity(count);
        for &[t, a, b, c] in &nodes {
            let g = |x: u32| local[x as usize];
            let key = match t { 7 | 8 | 9 => [t, g(a), g(b), 0], 10 => [t, g(a), g(b), g(c)], 4 => [t, a, b, g(c)], _ => [t, a, b, c | 0x8000_0000] };
            let next = plain.len() as u32;
            local.push(*plain.entry(key).or_insert(next));
            let l = |x: u32| lbr[x as usize];
            lbr.push(match t { 1 => a + 1, 7 => l(a).max(l(b)), 8 | 9 => l(a).max(l(b).saturating_sub(1)),
                               10 => l(a).max(l(b)).max(l(c).saturating_sub(1)), 4 => l(c), _ => 0 });
        }
        let before = global.len();
        let mut st = St { nodes: &nodes, lbr, memo: Map::default(), global: &mut global, env: Vec::new(), visits: 0 };
        st.go(root);
        visits += st.visits;
        graphs += 1; total += count as u64;
        fresh.push(((plain.len() - before_plain) as u32, (global.len() - before) as u32));
    }
    let n = fresh.len(); let tail = &fresh[n - n / 10..];
    let mean = |f: &dyn Fn(&(u32, u32)) -> u32| tail.iter().map(|x| f(x) as f64).sum::<f64>() / tail.len() as f64;
    println!("statements {graphs}  nodes {total}");
    println!("distinct vectors, variable = index:                {}", plain.len());
    println!("distinct vectors, variable = index + binder type:  {}  ({:.2}x)", global.len(), global.len() as f64 / plain.len() as f64);
    println!("cell applications per statement with no cache at all: {:.1} (plain nodes {:.1})", visits as f64 / graphs as f64, total as f64 / graphs as f64);
    println!("new vectors per statement, last tenth processed: index {:.1}, with binder type {:.1}", mean(&|x| x.0), mean(&|x| x.1));
}
fn main() { std::thread::Builder::new().stack_size(4 << 30).spawn(run).unwrap().join().unwrap(); }
