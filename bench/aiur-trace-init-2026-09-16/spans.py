#!/usr/bin/env python3
"""Aggregate an AIUR_PROFILE span JSONL: union wall time per span name and,
for spans carrying a `circuit`/`kind` field, per circuit."""
import json, sys
from collections import defaultdict

def load(path):
    """Completed spans, one record per `new` event. Span IDs are reused
    once a span closes, so the live record is retired to `done` before the
    ID is reassigned instead of being overwritten."""
    live = {}
    done = []
    for line in open(path):
        e = json.loads(line)
        if e['event'] == 'new':
            old = live.pop(e['id'], None)
            if old is not None: done.append(old)
            live[e['id']] = {'name': e['name'], 'fields': e.get('fields') or {}, 'enter': None, 'intervals': []}
        elif e['event'] == 'enter':
            s = live.get(e['id'])
            if s is not None: s['enter'] = e['ts_ns'] if 'ts_ns' in e else e.get('ts')
        elif e['event'] == 'exit':
            s = live.get(e['id'])
            if s is not None and s['enter'] is not None:
                t = e['ts_ns'] if 'ts_ns' in e else e.get('ts')
                s['intervals'].append((s['enter'], t)); s['enter'] = None
    done.extend(live.values())
    return done

def union(intervals):
    total = 0; cur = None
    for a, b in sorted(intervals):
        if cur is None: cur = [a, b]
        elif a <= cur[1]: cur[1] = max(cur[1], b)
        else: total += cur[1]-cur[0]; cur = [a, b]
    if cur: total += cur[1]-cur[0]
    return total

def main():
    spans = load(sys.argv[1])
    by_name = defaultdict(list); by_circuit = defaultdict(list); rows = defaultdict(int)
    for s in spans:
        by_name[s['name']].extend(s['intervals'])
        if s['name'] in ('aiur/cpu_circuit', 'aiur/codegen_seeds'):
            key = (s['name'], str(s['fields'].get('kind', '')), s['fields'].get('circuit'))
            by_circuit[key].extend(s['intervals'])
            rows[key] += int(s['fields'].get('rows', 0) or 0)
    print("## span unions (s)")
    for name, iv in sorted(by_name.items(), key=lambda kv: -union(kv[1])):
        print(f"  {name:32s} {union(iv)/1e9:9.3f}  n={len(iv)}")
    if by_circuit:
        print("## per circuit, union wall (s), rows")
        for key, iv in sorted(by_circuit.items(), key=lambda kv: -union(kv[1]))[:40]:
            print(f"  {key[0]:20s} {key[1]:10s} circuit={key[2]!s:5s} {union(iv)/1e9:8.3f}  rows={rows[key]}")

if __name__ == '__main__':
    main()
