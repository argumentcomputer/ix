#!/usr/bin/env python3
"""Read and rewrite the reducibility-hint section (§3) of an `.ixe` environment.

§3 maps constant addresses to `ReducibilityHints` and is not covered by the consts
merkle root, so a copy with different hints is the same environment with different
untrusted advice. Layout (crates/ixon/src/serialize.rs, `Env::put`):

  header: TagN4(0xE, version) root[32] opt_addr n_assumptions addr[32]*n
          [version 5: binding_addr[32] len bytes]
  §1 blobs:  n (addr[32] len bytes)*n
  §2 consts: n (addr[32] len bytes)*n           ascending addresses
  §3 hints:  n (rank_delta fused_hint)*n         fused: 0 opaque, 1 abbrev, h+2 regular(h)
  §4.. rest, copied verbatim.

Usage:
  ixe_hints.py dump ENV.ixe OUT.tsv            address, hint (opaque|abbrev|<height>)
  ixe_hints.py patch ENV.ixe EDITS.tsv OUT.ixe  EDITS: address<TAB>hint; others unchanged
"""
import mmap
import sys


def end_rungs(f):
    e1 = 1 << (8 - f - 1)
    e2 = e1 + (1 << (8 - f - 2 + 8))
    e3 = e2 + (1 << 16)
    e4 = e3 + (1 << 24)
    e5 = e4 + (1 << 32)
    return e1, e2, e3, e4, e5


def get_tagn(buf, pos, f=0):
    head = buf[pos]
    pos += 1
    r = 8 - f
    flag = head >> r if f else 0
    p = head & ((1 << r) - 1)
    lead = 1 << (r - 1)
    mbit = 1 << (r - 2)
    e1, e2, e3, e4, e5 = end_rungs(f)
    if p < lead:
        return flag, p, pos
    if p - lead < mbit:
        return flag, e1 + (p - lead) * 256 + buf[pos], pos + 1
    code = p - lead - mbit
    n, base = {0: (2, e2), 1: (3, e3), 2: (4, e4), 3: (8, e5)}[code]
    x = int.from_bytes(buf[pos:pos + n], "little")
    return flag, base + x, pos + n


def put_tagn(value, f=0, flag=0):
    e1, e2, e3, e4, e5 = end_rungs(f)
    lead = 1 << (8 - f - 1)
    mbit = 1 << (8 - f - 2)
    hdr = lambda payload: bytes([((flag << (8 - f)) + payload) & 0xFF])
    if value < e1:
        return hdr(value)
    if value < e2:
        v = value - e1
        return hdr(lead + v // 256) + bytes([v & 0xFF])
    for code, (base, n) in enumerate([(e2, 2), (e3, 3), (e4, 4), (e5, 8)]):
        top = [e3, e4, e5, 1 << 64][code]
        if value < top:
            return hdr(lead + mbit + code) + (value - base).to_bytes(n, "little")
    raise ValueError(value)


def locate(buf):
    """Return (const addresses in §2 order, §3 start, §3 end, [(rank, fused)])."""
    _, version, pos = get_tagn(buf, 0, 4)
    pos += 32
    if buf[pos] == 1:
        pos += 33
    else:
        pos += 1
    _, n, pos = get_tagn(buf, pos)
    pos += 32 * n
    if version == 5:
        pos += 32
        _, ln, pos = get_tagn(buf, pos)
        pos += ln
    _, nblobs, pos = get_tagn(buf, pos)
    for _ in range(nblobs):
        pos += 32
        _, ln, pos = get_tagn(buf, pos)
        pos += ln
    _, nconsts, pos = get_tagn(buf, pos)
    addrs = []
    for _ in range(nconsts):
        addrs.append(bytes(buf[pos:pos + 32]).hex())
        pos += 32
        _, ln, pos = get_tagn(buf, pos)
        pos += ln
    start = pos
    _, nh, pos = get_tagn(buf, pos)
    entries = []
    cursor = 0
    for _ in range(nh):
        _, delta, pos = get_tagn(buf, pos)
        _, fused, pos = get_tagn(buf, pos)
        idx = cursor + delta - 1
        entries.append((idx, fused))
        cursor = idx + 1
    return addrs, start, pos, entries


def show(fused):
    return "opaque" if fused == 0 else "abbrev" if fused == 1 else str(fused - 2)


def parse(text):
    return 0 if text == "opaque" else 1 if text == "abbrev" else int(text) + 2


def main():
    cmd, path = sys.argv[1], sys.argv[2]
    with open(path, "rb") as fh:
        buf = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ)
        addrs, start, end, entries = locate(buf)
        if cmd == "dump":
            with open(sys.argv[3], "w") as out:
                for idx, fused in entries:
                    out.write(f"{addrs[idx]}\t{show(fused)}\n")
            print(f"{len(addrs)} consts, {len(entries)} hints, §3 at [{start}, {end})")
            return
        if cmd != "patch":
            sys.exit(__doc__)
        rank = {a: i for i, a in enumerate(addrs)}
        hints = dict(entries)
        for line in open(sys.argv[3]):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            addr, value = line.split("\t")[:2]
            hints[rank[addr]] = parse(value)
        section = bytearray(put_tagn(len(hints)))
        prev = 0
        for idx in sorted(hints):
            section += put_tagn(idx + 1 - prev)
            section += put_tagn(hints[idx])
            prev = idx + 1
        with open(sys.argv[4], "wb") as out:
            step = 1 << 26
            for lo in range(0, start, step):
                out.write(buf[lo:min(lo + step, start)])
            out.write(section)
            for lo in range(end, len(buf), step):
                out.write(buf[lo:min(lo + step, len(buf))])
        print(f"wrote {sys.argv[4]}: {len(hints)} hints")


if __name__ == "__main__":
    main()
