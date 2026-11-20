import re, sys
sys.setrecursionlimit(1000000)
import threading
threading.stack_size(512*1024*1024)
SRC = open('/home/sam/repos/ix.ixai-aiur/Aiur/IxAIStep.lean').read()
mod = SRC[SRC.index('module Fixed {'):SRC.index('⟧')]

def tokenize(s):
    toks = re.findall(r'[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*|\d+|->|[()\[\],;=+\-*:<>&{}!]|"[^"]*"', s)
    return toks

# extract functions
funcs = {}
for m in re.finditer(r'fn (\w+)\((.*?)\)\s*->\s*(.*?)\{', mod, re.S):
    name = m.group(1)
    params = [p.split(':')[0].strip() for p in re.split(r',\s*(?![^\[]*\])', m.group(2)) if p.strip()]
    # body: balance braces from m.end()
    i = m.end(); depth = 1; j = i
    while depth:
        if mod[j] == '{': depth += 1
        elif mod[j] == '}': depth -= 1
        j += 1
    funcs[name] = (params, mod[i:j-1])

class P:
    def __init__(s, toks): s.t = toks; s.i = 0
    def peek(s, k=0): return s.t[s.i+k] if s.i+k < len(s.t) else None
    def eat(s, x=None):
        t = s.t[s.i]
        if x is not None and t != x: raise Exception(f"expected {x} got {t} at {s.t[s.i-5:s.i+5]}")
        s.i += 1; return t
    def body(s):
        if s.peek() == 'let':
            s.eat('let'); pat = s.pat(); s.eat('=')
            x = s.expr(); s.eat(';')
            b = s.body()
            return ('let', pat, x, b)
        return s.expr()
    def pat(s):
        t = s.peek()
        if t == '(':
            s.eat('('); ps = [s.pat()]
            while s.peek() == ',': s.eat(','); ps.append(s.pat())
            s.eat(')'); return ('ptuple', ps)
        if t == '[':
            s.eat('['); ps = [s.pat()]
            while s.peek() == ',': s.eat(','); ps.append(s.pat())
            s.eat(']'); return ('parray', ps)
        s.eat(); return ('bind', t)
    def expr(s):
        e = s.term()
        while s.peek() in ('+', '-'):
            op = 'add' if s.eat() == '+' else 'sub'
            e = ('bin', op, e, s.term())
        return e
    def term(s):
        e = s.post()
        while s.peek() == '*':
            s.eat(); e = ('bin', 'mul', e, s.post())
        return e
    def post(s):
        e = s.prim()
        while s.peek() == '[':
            s.eat('['); n = s.eat(); s.eat(']'); e = ('index', e, int(n))
        return e
    def prim(s):
        t = s.peek()
        if t == '(':
            s.eat('('); es = [s.expr()]
            if s.peek() == ')': s.eat(); return es[0]
            while s.peek() == ',': s.eat(','); es.append(s.expr())
            s.eat(')'); return ('tuple', es)
        if t == '[':
            s.eat('['); es = [s.expr()]
            while s.peek() == ',': s.eat(','); es.append(s.expr())
            s.eat(']'); return ('array', es)
        if t.isdigit(): s.eat(); return ('lit', t)
        s.eat()
        if s.peek() == '(':
            s.eat('('); es = []
            if s.peek() != ')':
                es.append(s.expr())
                while s.peek() == ',': s.eat(','); es.append(s.expr())
            s.eat(')')
            name = t if '::' in t else 'Fixed::' + t
            return ('call', name, es)
        return ('var', t)

def resolve(sub, t, fuel=10000):
    if t[0] == 'v':
        if t[1] in sub and fuel > 0: return resolve(sub, sub[t[1]], fuel-1)
        return t
    if t[0] == 'field': return t
    if t[0] == 'tuple': return ('tuple', [resolve(sub, x, fuel) for x in t[1]])
def render(t):
    if t[0] == 'v': return t[1]
    if t[0] == 'field': return f'(.field {t[1]})'
    return '(.tuple [' + ', '.join(render(x) for x in t[1]) + '])'
def mentions(n, t):
    if t[0] == 'v': return t[1] == n
    if t[0] == 'tuple': return any(mentions(n, x) for x in t[1])
    return False

class G:
    def __init__(g, params):
        g.counter = 1; g.binders = []; g.sub = {}; g.facts = []; g.used = []
        g.params = params + ['h', 'r', "h'", 'calls']; g.lookups = 0; g.result = None
    def fresh(g, b):
        n = f'{b}{g.counter}'; g.counter += 1; return n
    def binder(g, b, ty='SourceValue F'):
        n = g.fresh(b); g.binders.append((n, ty)); g.used.append(n); return n
    def named(g, src):
        base = 'x_' + src
        n = g.fresh(base + '_') if (base in g.params or base in g.used) else base
        g.binders.append((n, 'SourceValue F')); g.used.append(n); return n
    def add(g, name, pieces): g.facts.append((name, pieces))
    def assign(g, dest, t):
        r = resolve(g.sub, dest)
        assert r[0] == 'v'
        if r[1] in g.params:
            f = g.fresh('he'); g.add(f, [f'{r[1]} = ', t])
        else:
            assert not mentions(r[1], resolve(g.sub, t)), 'cyclic'
            g.sub[r[1]] = t
    def unify(g, V, tmpl, hv):
        r = resolve(g.sub, V)
        assert r[0] == 'v'
        if r[1] in g.params: g.add(hv, [f'{r[1]} = ', tmpl])
        else: g.sub[r[1]] = tmpl
    def inv(g, e, env, hin, dv, dh, k):
        tag = e[0]
        if tag == 'var':
            t = dict(env)[e[1]] if False else next(t for n, t in env if n == e[1])
            g.lookups += len(env)
            g.fresh('l'); g.assign(dv, t); g.assign(dh, hin); return k([])
        if tag == 'lit':
            g.assign(dv, ('field', e[1])); g.assign(dh, hin); return k([])
        if tag in ('tuple', 'array'):
            g.fresh('vs'); g.fresh('a')
            items = [g.binder('v') for _ in e[1]]
            g.assign(dv, ('tuple', [('v', i) for i in items]))
            return g.invArgs(e[1], env, hin, items, dh, k)
        if tag == 'call':
            name, es = e[1], e[2]
            g.fresh('vs'); m = g.binder('m', 'Heap F'); g.fresh('c'); c2 = g.binder('cs', 'List (Call F)')
            g.fresh('a'); ev = g.fresh('ev')
            items = [g.binder('v') for _ in es]
            def cont(s1):
                g.add(ev, [f'ObsFn W "{name}" ['] + sum([[('v', i)] + ([', '] if j < len(items)-1 else []) for j, i in enumerate(items)], []) + ['] ', ('v', m), ' ', dv, ' ', dh, f' {c2}'])
                return k(s1 + [('call', name, items, m), ('sub', c2)])
            return g.invArgs(es, env, hin, items, ('v', m), cont)
        if tag == 'bin':
            x = g.binder('x'); y = g.binder('y'); m = g.binder('m', 'Heap F')
            g.fresh('c'); g.fresh('c'); g.fresh('d'); g.fresh('d'); o = g.fresh('op')
            def c1(s1):
                def c2(s2):
                    g.add(o, [f'evalBinOp .{e[1]} (', ('v', x), ' : SourceValue F) (', ('v', y), ' : SourceValue F) = .ok ', dv])
                    return k(s1 + s2)
                return g.inv(e[3], env, ('v', m), ('v', y), dh, c2)
            return g.inv(e[2], env, hin, ('v', x), ('v', m), c1)
        if tag == 'index':
            p = g.binder('p'); g.fresh('d'); pr = g.fresh('pr')
            def c(s):
                g.add(pr, ['projectValue (', ('v', p), f' : SourceValue F) {e[2]} = .ok ', dv]); return k(s)
            return g.inv(e[1], env, hin, ('v', p), dh, c)
        if tag == 'let':
            pat, x, b = e[1], e[2], e[3]
            v = g.binder('v'); m = g.binder('m', 'Heap F')
            g.fresh('bs'); g.fresh('c'); g.fresh('c'); g.fresh('d'); g.fresh('mt'); g.fresh('d')
            def c(s1):
                binds = g.patInv(('v', v), pat)
                return g.inv(b, binds + env, ('v', m), dv, dh, lambda s2: k(s1 + s2))
            return g.inv(x, env, hin, ('v', v), ('v', m), c)
        raise Exception(tag)
    def invArgs(g, es, env, hin, items, dh, k):
        if not es:
            g.assign(dh, hin); return k([])
        g.fresh('vs'); m = g.binder('m', 'Heap F'); g.fresh('c'); g.fresh('c'); g.fresh('d'); g.fresh('a')
        return g.inv(es[0], env, hin, ('v', items[0]), ('v', m),
                     lambda s1: g.invArgs(es[1:], env, ('v', m), items[1:], dh, lambda s2: k(s1 + s2)))
    def patInv(g, V, p):
        if p[0] == 'bind':
            if p[1] == '_': return []
            return [(p[1], V)]
        r = resolve(g.sub, V)
        assert r[0] == 'v', 'concrete'
        g.fresh('vs'); hv = g.fresh('hv'); g.fresh('ml')
        subs = [g.named(q[1]) if q[0] == 'bind' and q[1] != '_' else g.binder('w') for q in p[1]]
        g.unify(V, ('tuple', [('v', s) for s in subs]), hv)
        binds = []
        for q, w in zip(p[1], subs):
            g.fresh('vs'); g.fresh('b'); g.fresh('b'); g.fresh('mt'); g.fresh('ml')
            binds += g.patInv(('v', w), q)
        return binds

def renderPieces(sub, ps):
    return ''.join(x if isinstance(x, str) else render(resolve(sub, x)) for x in ps)

def gen(fname):
    params, body = funcs[fname]
    ast = P(tokenize(body)).body()
    ps = ['x_' + p for p in params]
    g = G(ps)
    env = list(zip(params, [('v', p) for p in ps]))
    def leaf(segs):
        hc = g.fresh('hc'); g.segs = segs; return []
    g.inv(ast, env, ('v', 'h'), ('v', 'r'), ('v', "h'"), leaf)
    bs = [(n, t) for n, t in g.binders if n not in g.sub]
    out = [f'-- «Fixed::{fname}».Path.run  (lookups {g.lookups}, facts {len(g.facts)+1}, binders {len(bs)})']
    out.append('--   binders: ' + ' '.join(n for n, _ in bs))
    for n, f in g.facts:
        out.append(f'--   ({n} : {renderPieces(g.sub, f)})')
    out.append('--   (hc : calls = …)')
    return '\n'.join(out)

def path(fname):
    params, body = funcs[fname]
    ast = P(tokenize(body)).body()
    ps = ['x_' + p for p in params]
    g = G(ps)
    env = list(zip(params, [('v', p) for p in ps]))
    def leaf(segs):
        g.hc = g.fresh('hc'); return []
    g.inv(ast, env, ('v', 'h'), ('v', 'r'), ('v', "h'"), leaf)
    bs = [n for n, t in g.binders if n not in g.sub]
    facts = [(n, renderPieces(g.sub, f)) for n, f in g.facts] + [(g.hc, 'calls = ...')]
    return bs, facts, g.lookups

if __name__ == '__main__':
    for f in sys.argv[1:]:
        print(gen(f)); print()
