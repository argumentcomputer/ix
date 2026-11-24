use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{BufRead, BufReader};

#[derive(Default)]
struct Fx(u64);
impl Fx {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517cc1b727220a95);
    }
}
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, bytes: &[u8]) { for b in bytes { self.add(*b as u64); } }
    fn write_u32(&mut self, i: u32) { self.add(i as u64); }
    fn write_u64(&mut self, i: u64) { self.add(i); }
    fn write_usize(&mut self, i: usize) { self.add(i as u64); }
}

fn pct(v: &mut Vec<u32>, ps: &[f64]) -> Vec<u32> {
    v.sort_unstable();
    ps.iter().map(|p| v[(((v.len() - 1) as f64) * p / 100.0) as usize]).collect()
}

fn main() {
    let dir = std::env::args().nth(1).unwrap();
    let bytes = std::fs::read(format!("{dir}/nodes.bin")).unwrap();
    let w = |i: usize| u32::from_le_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]]);
    // owners: (is_theorem, start, count)
    let mut owners: Vec<(bool, usize, usize)> = Vec::new();
    for line in BufReader::new(std::fs::File::open(format!("{dir}/consts.tsv")).unwrap()).lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split('\t').collect();
        let count: usize = f[9].parse().unwrap();
        if count > 0 {
            owners.push((f[2] == "thm", f[8].parse().unwrap(), count));
        }
    }
    let mut map: HashMap<[u32; 4], u32, BuildHasherDefault<Fx>> = HashMap::default();
    let mut height: Vec<u16> = Vec::new(); // binary height
    let mut depth: Vec<u16> = Vec::new(); // depth with an application spine as one level
    let mut lbr: Vec<u16> = Vec::new(); // loose bound variable range
    let mut mult: Vec<u32> = Vec::new();
    let mut isapp: Vec<bool> = Vec::new();
    let mut local: Vec<u32> = Vec::new();
    for phase in 0..2 {
        let mut total = 0u64;
        let mut fresh_per: Vec<u32> = Vec::new();
        let before = height.len();
        for &(thm, start, count) in &owners {
            if thm != (phase == 0) { continue; }
            local.clear();
            let mut fresh = 0u32;
            for i in 0..count {
                let (t, a, b, c) = (w(4 * (start + i)), w(4 * (start + i) + 1), w(4 * (start + i) + 2), w(4 * (start + i) + 3));
                let g = |x: u32| local[x as usize];
                let key = match t {
                    7 | 8 | 9 => [t, g(a), g(b), 0],
                    10 => [t, g(a), g(b), g(c)],
                    4 => [t, a, b, g(c)],
                    _ => [t, a, b, c],
                };
                let next = height.len() as u32;
                let id = *map.entry(key).or_insert(next);
                if id == next {
                    fresh += 1;
                    let (h, d, l) = match t {
                        7 => {
                            let (f, x) = (key[1] as usize, key[2] as usize);
                            let hf = if isapp[f] { depth[f] } else { depth[f] + 1 };
                            (1 + height[f].max(height[x]), hf.max(depth[x] + 1), lbr[f].max(lbr[x]))
                        }
                        8 | 9 => {
                            let (x, y) = (key[1] as usize, key[2] as usize);
                            (1 + height[x].max(height[y]), 1 + depth[x].max(depth[y]), lbr[x].max(lbr[y].saturating_sub(1)))
                        }
                        10 => {
                            let (x, y, z) = (key[1] as usize, key[2] as usize, key[3] as usize);
                            (1 + height[x].max(height[y]).max(height[z]), 1 + depth[x].max(depth[y]).max(depth[z]),
                             lbr[x].max(lbr[y]).max(lbr[z].saturating_sub(1)))
                        }
                        4 => { let z = key[3] as usize; (1 + height[z], 1 + depth[z], lbr[z]) }
                        1 => (1, 1, (a + 1).min(65535) as u16),
                        _ => (1, 1, 0),
                    };
                    height.push(h); depth.push(d); lbr.push(l); mult.push(0); isapp.push(t == 7);
                }
                mult[id as usize] += 1;
                local.push(id);
            }
            total += count as u64;
            fresh_per.push(fresh);
        }
        let uniq = height.len() - before;
        let name = if phase == 0 { "theorem statements" } else { "everything else (definitions with bodies, inductives, recursors, axioms)" };
        println!("== {name}");
        println!("graphs {}  nodes {}  new unique nodes {}  ({:.1}% of nodes)", fresh_per.len(), total, uniq, 100.0 * uniq as f64 / total as f64);
        let n = fresh_per.len();
        let tail: Vec<u32> = fresh_per[n - n / 10..].to_vec();
        let mean_tail = tail.iter().map(|x| *x as f64).sum::<f64>() / tail.len() as f64;
        let mut t2 = tail.clone();
        println!("new unique nodes per graph, last tenth processed: mean {:.1}  median/p90/p99 {:?}", mean_tail, pct(&mut t2, &[50.0, 90.0, 99.0]));
        if phase == 0 {
            let u = height.len();
            let closed = lbr.iter().filter(|l| **l == 0).count();
            println!("closed (no loose bound variable): {:.1}% of unique nodes", 100.0 * closed as f64 / u as f64);
            for (label, v) in [("binary height", &height), ("spine-aware depth", &depth)] {
                let max = *v.iter().max().unwrap() as usize;
                let mut hist = vec![0u64; max + 1];
                for x in v.iter() { hist[*x as usize] += 1; }
                let widest = hist.iter().enumerate().max_by_key(|(_, c)| **c).unwrap();
                let mut cum = 0u64; let mut l99 = 0; let mut l999 = 0;
                for (lv, c) in hist.iter().enumerate() {
                    cum += c;
                    if l99 == 0 && cum as f64 >= 0.99 * u as f64 { l99 = lv; }
                    if l999 == 0 && cum as f64 >= 0.999 * u as f64 { l999 = lv; }
                }
                println!("{label}: levels {max}, 99% of unique nodes within {l99}, 99.9% within {l999}; widest level {} holds {}", widest.0, widest.1);
                println!("  first levels: {:?}", &hist[1..hist.len().min(13)]);
            }
            let occ: u64 = mult.iter().map(|m| *m as u64).sum();
            for th in [2u32, 10, 100, 1000] {
                let k = mult.iter().filter(|m| **m >= th).count();
                let o: u64 = mult.iter().filter(|m| **m >= th).map(|m| *m as u64).sum();
                println!("unique nodes occurring in >= {th} statements: {k} ({:.1}% of unique), covering {:.1}% of occurrences", 100.0 * k as f64 / u as f64, 100.0 * o as f64 / occ as f64);
            }
        }
    }
    println!("== whole library: unique nodes {}", height.len());
}
