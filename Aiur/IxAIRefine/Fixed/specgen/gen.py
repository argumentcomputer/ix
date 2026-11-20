import json, re
P = json.load(open('paths.json'))

def names(fn):
    return [n for n, _ in P[fn]]

def pat(fn, drop=()):
    return '⟨' + ', '.join(('-' if n in drop else n) for n in names(fn)) + '⟩'

def wrap(items, first, cont, width=94):
    lines, cur = [], first
    for i, it in enumerate(items):
        piece = it + (', ' if i < len(items) - 1 else '')
        if len(cur) + len(piece) > width and cur.strip():
            lines.append(cur.rstrip())
            cur = cont
        cur += piece
    lines.append(cur.rstrip())
    return '\n'.join(lines)

def obtain(fn, src, indent='  '):
    ns = names(fn)
    items = ns[:]
    items[0] = '⟨' + items[0]
    items[-1] = items[-1] + '⟩'
    body = wrap(items, indent + 'obtain ', indent + '    ')
    return body + f' :=\n{indent}  «{fn}».obs {src}'

def destr(v, n, h):
    items = [f'{v}{i}' for i in range(n)] + ['rfl']
    items[0] = '⟨' + items[0]; items[-1] = items[-1] + '⟩'
    return wrap(items, '  obtain ', '    ') + f' :=\n    list_eq{n} {h}'

def wrap_text(text, first, cont, width=98):
    words = text.split(' ')
    lines, cur = [], first
    for w in words:
        piece = w if cur.endswith(' ') or cur == first and first.endswith(' ') else ' ' + w
        if len(cur) + len(piece) > width and cur.strip():
            lines.append(cur.rstrip())
            cur = cont + w
        else:
            cur += piece
    lines.append(cur)
    return '\n'.join(lines)

def list_eq(n):
    vs = ' '.join(f'x{i}' for i in range(n))
    lst = ', '.join(f'x{i}' for i in range(n))
    inner = f'_ | ⟨x{n}, l⟩'
    for i in reversed(range(n)):
        inner = f'_ | ⟨x{i}, {inner}⟩'
    unders = ', '.join(['_'] * n)
    return f'''/-- A list of length {n} is a literal of {n} elements. -/
theorem list_eq{n} {{α : Type}} {{l : List α}} (h : l.length = {n}) :
    ∃ {vs},
{wrap_text('l = [' + lst + '] := by', '      ', '        ')}
{wrap_text('rcases l with ' + inner.replace(' | ', '\u00a0| '), '  ', '      ').replace('\u00a0', ' ')}
  -- unverified: `simp only` with the default simprocs refutes the wrong lengths.
  all_goals first
    | exact ⟨{unders}, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)
'''

def chain_steps(fn, elem):
    """Steps substituting projections and field operations, in path order."""
    out = []
    for n, t in P[fn]:
        m = re.match(r'projectValue \((x_[ab]) : SourceValue F\) (\d+) = \.ok (\w+)$', t)
        if m:
            arr, i, v = m.groups()
            e = elem[arr] + i
            out.append(f'  obtain rfl : fxVal {e} = {v} := by\n'
                       f'    first | exact Except.ok.inj {n} | simpa using proj_ok {n}')
            continue
        m = re.match(r'evalBinOp \.(mul|add|sub) .* = \.ok (\w+)$', t)
        if m:
            out.append(f'  obtain rfl := {m.group(1)}_ff {n}')
    return '\n'.join(out)

def dot(n, fn):
    xs = ', '.join(f'a{i}' for i in range(n))
    ys = ', '.join(f'b{i}' for i in range(n))
    xa = ' '.join(f'a{i}' for i in range(n))
    yb = ' '.join(f'b{i}' for i in range(n))
    return f'''/-- **`{fn}`**: a dot product of length {n} is `Fx.dot`, the exact integer sum of the
products rounded once by `shr8`, provided that sum is below `2^55` in magnitude. -/
theorem dot{n}_spec {{xs ys : List IxAICore.Fx}} (hxs : xs.length = {n}) (hys : ys.length = {n})
    (hb : |IxAICore.Fx.dotRaw xs ys| < 2 ^ 55) {{h h' : Heap F}} {{r : SourceValue F}}
    {{calls : List (Call F)}}
    (ev : ObsFn W "{fn}" [.tuple (xs.map fxVal), .tuple (ys.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.dot xs ys) := by
{destr('a', n, 'hxs')}
{destr('b', n, 'hys')}
  simp only [List.map_cons, List.map_nil] at ev
{obtain(fn, 'ev')}
{chain_steps(fn, {'x_a': 'a', 'x_b': 'b'})}
  exact (shr8_spec
    (s := IxAICore.Fx.dotRaw
      [{xs}]
      [{ys}])
    (by simp only [dotRaw_cons, dotRaw_nil, Int.cast_add, Int.cast_mul, Int.cast_zero] <;> ring)
    hb ev6).trans (by simp only [fxVal, IxAICore.Fx.dot, shr8_eq])
'''

def sum20():
    fn = 'Fixed::sum20'
    n = 20
    return f'''/-- **`Fixed::sum20`**: the exact sum of 20 fixed-point numbers, `Fx.sum`. No rounding happens,
so no bound is needed. -/
theorem sum20_spec {{xs : List IxAICore.Fx}} (hxs : xs.length = 20) {{h h' : Heap F}}
    {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "{fn}" [.tuple (xs.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.sum xs) := by
{destr('a', n, 'hxs')}
  simp only [List.map_cons, List.map_nil] at ev
{obtain(fn, 'ev')}
{chain_steps(fn, {'x_a': 'a'})}
  simp only [fxVal, IxAICore.Fx.sum, sumRaw_cons, sumRaw_nil, Int.cast_add, Int.cast_zero]
  congr 1
  ring
'''

head = open('head.lean').read()
mid = open('mid.lean').read()
mid = mid.replace('@@SHR8_OBTAIN@@', obtain('Fixed::shr8', 'ev'))
mid = mid.replace('@@SIGN_OBTAIN@@', obtain('Fixed::sign_split', 'ev'))
parts = [head, ''.join(list_eq(k) + '\n' for k in (8, 11, 16, 20)), mid]
parts.append('/-! ## Dot products and sums -/\n\n')
for n, fn in [(8, 'Fixed::dot8'), (16, 'Fixed::dot16'), (11, 'Fixed::dot11'), (20, 'Fixed::dot20')]:
    parts.append(dot(n, fn) + '\n')
parts.append(sum20() + '\n')
parts.append('end IxAIStep.Fixed.Specs\n')
open('/home/sam/repos/ix.ixai-aiur/Aiur/IxAIRefine/Fixed/Specs.lean', 'w').write(''.join(parts))
