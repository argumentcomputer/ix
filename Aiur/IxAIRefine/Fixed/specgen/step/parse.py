import re, json, sys
src = open('/home/sam/repos/ix.ixai-aiur/Aiur/IxAIRefine/Fixed/Obs/Fixed0.lean').read()
out = {}
for m in re.finditer(r'inductive «([^»]+)»\.Path(.*?)\n\n/--', src, re.S):
    name, body = m.group(1), m.group(2)
    run = body.split('| run', 1)[1]
    # top-level parenthesized binders
    binders = []
    depth = 0; cur = ''
    for ch in run:
        if ch == '(':
            if depth == 0: cur = ''
            else: cur += ch
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0: binders.append(cur)
            else: cur += ch
        elif depth > 0: cur += ch
    entries = []
    for b in binders:
        nm, ty = b.split(':', 1)
        entries.append((nm.strip(), ty.strip()))
    out[name] = entries
json.dump(out, open('paths.json', 'w'), indent=0)
for k, v in out.items(): print(k, len(v), [n for n, _ in v][:5])
