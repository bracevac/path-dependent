#!/usr/bin/env python3
"""Differential test: Coq `step` (dot.v:130-212, levels + locally nameless)
versus Lean `Oopsla16.Step` (Structural.lean / Semantics.lean, intrinsic
de Bruijn indices), related by the level->index translation.

Both sides are transcribed by hand from the sources; this is a test of the
translation argument, not a proof.  Lean line numbers refer to
lean/Coercions/Oopsla16/.

Usage: python3 step_differential.py [SEED]

Each run generates 20,000 random configurations (store and closed term) from
the seed (default 0), runs both step relations side by side for up to 25
steps, and asserts after every step that the translated Coq configuration is
the Lean one.  It prints counts and exits with an AssertionError at the first
disagreement.  Seeds 0 to 7 together check 160,000 configurations.
"""
import random, sys

# ---------------------------------------------------------------- Coq side
# vr : ('TVar', b, x) | ('TVarB', k)
# ty : ('TBot',) ('TTop',) ('TFun',l,T1,T2) ('TTyp',l,T1,T2) ('TSel',vr,l)
#      ('TBind',T) ('TAnd',T1,T2) ('TOr',T1,T2)
# tm : ('tvar', b, x) | ('tobj', dms) | ('tapp', t1, l, t2)
# dm : ('dfun', OT1, OT2, t) | ('dty', T)      OT = None | ty
# dms: tuple of dm, head = newest (dcons d ds == (d,)+ds)
# venv: tuple of dms, head = newest

def c_index(n, l):                       # dot.v:77-81
    for i, a in enumerate(l):
        if n == len(l) - 1 - i:           # beq_nat n (length l')
            return a
    return None

def c_vr_open(k, u, p):                  # dot.v:130-134
    if p[0] == 'TVar': return p
    return u if k == p[1] else p

def c_open(k, u, T):                     # dot.v:135-145
    h = T[0]
    if h in ('TTop', 'TBot'): return T
    if h == 'TSel': return ('TSel', c_vr_open(k, u, T[1]), T[2])
    if h == 'TFun': return ('TFun', T[1], c_open(k, u, T[2]), c_open(k + 1, u, T[3]))
    if h == 'TTyp': return ('TTyp', T[1], c_open(k, u, T[2]), c_open(k, u, T[3]))
    if h == 'TBind': return ('TBind', c_open(k + 1, u, T[1]))
    return (h, c_open(k, u, T[1]), c_open(k, u, T[2]))

def c_vr_subst(u, X):                    # dot.v:150-157
    if X[0] == 'TVarB': return X
    if X[1] is True: return X
    i = X[2]
    return u if i == 0 else ('TVar', False, i - 1)

def c_subst(u, T):                       # dot.v:158-168
    h = T[0]
    if h in ('TTop', 'TBot'): return T
    if h == 'TSel': return ('TSel', c_vr_subst(u, T[1]), T[2])
    if h in ('TFun', 'TTyp'): return (h, T[1], c_subst(u, T[2]), c_subst(u, T[3]))
    if h == 'TBind': return ('TBind', c_subst(u, T[1]))
    return (h, c_subst(u, T[1]), c_subst(u, T[2]))

def c_subst_tm(u, t):                    # dot.v:172-178
    h = t[0]
    if h == 'tvar':
        if t[1] is True: return t
        i = t[2]
        return ('tvar', True, u) if i == 0 else ('tvar', False, i - 1)
    if h == 'tobj': return ('tobj', c_subst_dms(u, t[1]))
    return ('tapp', c_subst_tm(u, t[1]), t[2], c_subst_tm(u, t[3]))

def c_omap(f, o): return None if o is None else f(o)

def c_subst_dm(u, d):                    # dot.v:179-183
    if d[0] == 'dty': return ('dty', c_subst(('TVar', True, u), d[1]))
    return ('dfun', c_omap(lambda T: c_subst(('TVar', True, u), T), d[1]),
            c_omap(lambda T: c_subst(('TVar', True, u), T), d[2]), c_subst_tm(u, d[3]))

def c_subst_dms(u, ds):                  # dot.v:184-188
    return tuple(c_subst_dm(u, d) for d in ds)

def c_step(G, t):                        # dot.v:197-212, deterministic reading
    if t[0] == 'tobj':                   # ST_Obj
        return ((c_subst_dms(len(G), t[1]),) + G, ('tvar', True, len(G)))
    if t[0] == 'tapp':
        t1, l, t2 = t[1], t[2], t[3]
        if t1[0] == 'tvar' and t1[1] is True and t2[0] == 'tvar' and t2[1] is True:
            ds = c_index(t1[2], G)       # ST_AppAbs
            if ds is not None:
                d = c_index(l, ds)
                if d is not None and d[0] == 'dfun':
                    return (G, c_subst_tm(t2[2], d[3]))
            return None                  # variables do not step: no App1/App2
        r = c_step(G, t1)                # ST_App1
        if r is not None:
            return (r[0], ('tapp', r[1], l, t2))
        if t1[0] == 'tvar' and t1[1] is True:
            r = c_step(G, t2)            # ST_App2
            if r is not None:
                return (r[0], ('tapp', t1, l, r[1]))
        return None
    return None

def c_answer(G, t):                      # dot_soundness.v:1133
    return t[0] == 'tvar' and t[1] is True and c_index(t[2], G) is not None

# --------------------------------------------------------------- Lean side
# Vr : ('conc', i) | ('abs', i)          de Bruijn index, 0 = newest (.here)
# Ty/Tm/Dm as Coq, with Vr in place of vr / (b,x); Store: tuple, head = .here
# Subst: (conc: int->int, abs: int->Vr)

def l_weaken(v):                         # Structural.lean:32-34
    return v if v[0] == 'conc' else ('abs', v[1] + 1)

def l_lift(th):                          # Structural.lean:46-48
    c, a = th
    return (c, lambda y: ('abs', 0) if y == 0 else l_weaken(a(y - 1)))

def l_one(v):                            # Structural.lean:61-63
    return (lambda x: x, lambda y: v if y == 0 else ('abs', y - 1))

def l_ofStore(rho):                      # Structural.lean:56-58
    return (rho, lambda y: ('abs', y))

def l_vr_subst(v, th):                   # Structural.lean:69-71
    return ('conc', th[0](v[1])) if v[0] == 'conc' else th[1](v[1])

def l_ty_subst(T, th):                   # Structural.lean:73-81
    h = T[0]
    if h in ('TTop', 'TBot'): return T
    if h == 'TFun': return ('TFun', T[1], l_ty_subst(T[2], th), l_ty_subst(T[3], l_lift(th)))
    if h == 'TTyp': return ('TTyp', T[1], l_ty_subst(T[2], th), l_ty_subst(T[3], th))
    if h == 'TSel': return ('TSel', l_vr_subst(T[1], th), T[2])
    if h == 'TBind': return ('TBind', l_ty_subst(T[1], l_lift(th)))
    return (h, l_ty_subst(T[1], th), l_ty_subst(T[2], th))

def l_tm_subst(t, th):                   # Structural.lean:85-88
    h = t[0]
    if h == 'tvar': return ('tvar', l_vr_subst(t[1], th))
    if h == 'tobj': return ('tobj', l_dms_subst(t[1], l_lift(th)))
    return ('tapp', l_tm_subst(t[1], th), t[2], l_tm_subst(t[3], th))

def l_dm_subst(d, th):                   # Structural.lean:90-94
    if d[0] == 'dty': return ('dty', l_ty_subst(d[1], th))
    return ('dfun', None if d[1] is None else l_ty_subst(d[1], th),
            None if d[2] is None else l_ty_subst(d[2], l_lift(th)),
            l_tm_subst(d[3], l_lift(th)))

def l_dms_subst(ds, th):                 # Structural.lean:96-98
    return tuple(l_dm_subst(d, th) for d in ds)

def l_get(ds, l):                        # Syntax.lean:139-141
    for i, d in enumerate(ds):
        if l == len(ds) - 1 - i:          # if l = ds.length then some d
            return d
    return None

succ = lambda x: x + 1

def l_step(G, t):
    """Returns (k, G', t') with k = number of allocations (the Grows index)."""
    if t[0] == 'tobj':                   # ST_Obj, Semantics.lean:54-57
        D = l_dms_subst(t[1], l_ofStore(succ))          # D.weakenStore
        D = l_dms_subst(D, l_one(('conc', 0)))          # .substVr (.conc .here)
        Gw = tuple(l_dms_subst(e, l_ofStore(succ)) for e in G)  # G.weakenStore
        return (1, (D,) + Gw, ('tvar', ('conc', 0)))
    if t[0] == 'tapp':
        t1, l, t2 = t[1], t[2], t[3]
        if t1[0] == 'tvar' and t2[0] == 'tvar' and t1[1][0] == 'conc' and t2[1][0] == 'conc':
            d = l_get(G[t1[1][1]], l)    # ST_AppAbs, Semantics.lean:60-64
            if d is not None and d[0] == 'dfun':
                return (0, G, l_tm_subst(d[3], l_one(('conc', t2[1][1]))))
            return None
        r = l_step(G, t1)                # ST_App1, Semantics.lean:67-70
        if r is not None:
            k = r[0]
            rho = (lambda x, k=k: x + k)
            return (k, r[1], ('tapp', r[2], l, l_tm_subst(t2, l_ofStore(rho))))
        if t1[0] == 'tvar' and t1[1][0] == 'conc':
            r = l_step(G, t2)            # ST_App2, Semantics.lean:73-77
            if r is not None:
                k = r[0]
                return (k, r[1], ('tapp', ('tvar', ('conc', t1[1][1] + k)), l, r[2]))
        return None
    return None

def l_answer(t):                         # Semantics.lean:89-91
    return t[0] == 'tvar' and t[1][0] == 'conc'

# ------------------------------------------------------------ translation
def tr_vr_ty(p, n, d, k):
    if p[0] == 'TVarB':
        assert p[1] < k, p
        return ('abs', p[1])
    if p[1] is True:
        assert p[2] < n, p
        return ('conc', n - 1 - p[2])
    assert p[2] < d, (p, d)
    return ('abs', k + d - 1 - p[2])

def tr_ty(T, n, d, k):
    h = T[0]
    if h in ('TTop', 'TBot'): return T
    if h == 'TSel': return ('TSel', tr_vr_ty(T[1], n, d, k), T[2])
    if h == 'TFun': return ('TFun', T[1], tr_ty(T[2], n, d, k), tr_ty(T[3], n, d, k + 1))
    if h == 'TTyp': return ('TTyp', T[1], tr_ty(T[2], n, d, k), tr_ty(T[3], n, d, k))
    if h == 'TBind': return ('TBind', tr_ty(T[1], n, d, k + 1))
    return (h, tr_ty(T[1], n, d, k), tr_ty(T[2], n, d, k))

def tr_tm(t, n, d):
    h = t[0]
    if h == 'tvar':
        if t[1] is True:
            assert t[2] < n
            return ('tvar', ('conc', n - 1 - t[2]))
        assert t[2] < d
        return ('tvar', ('abs', d - 1 - t[2]))
    if h == 'tobj': return ('tobj', tr_dms(t[1], n, d + 1))
    return ('tapp', tr_tm(t[1], n, d), t[2], tr_tm(t[3], n, d))

def tr_dm(dm, n, d):                     # d = depth of the member (self included)
    if dm[0] == 'dty': return ('dty', tr_ty(dm[1], n, d, 0))
    return ('dfun', None if dm[1] is None else tr_ty(dm[1], n, d, 0),
            None if dm[2] is None else tr_ty(dm[2], n, d, 1), tr_tm(dm[3], n, d + 1))

def tr_dms(ds, n, d): return tuple(tr_dm(x, n, d) for x in ds)
def tr_store(G): return tuple(tr_dms(e, len(G), 0) for e in G)

# ------------------------------------------------------------- generators
R = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
NL = 3  # labels 0..2

def g_vr(n, d, k):
    opts = []
    if n: opts.append(lambda: ('TVar', True, R.randrange(n)))
    if d: opts.append(lambda: ('TVar', False, R.randrange(d)))
    if k: opts.append(lambda: ('TVarB', R.randrange(k)))
    return R.choice(opts)() if opts else None

def g_ty(n, d, k, sz):
    c = R.randrange(8 if sz > 0 else 3)
    if c == 0: return ('TTop',)
    if c == 1: return ('TBot',)
    if c == 2:
        p = g_vr(n, d, k)
        return ('TSel', p, R.randrange(NL)) if p else ('TTop',)
    if c == 3: return ('TFun', R.randrange(NL), g_ty(n, d, k, sz - 1), g_ty(n, d, k + 1, sz - 1))
    if c == 4: return ('TTyp', R.randrange(NL), g_ty(n, d, k, sz - 1), g_ty(n, d, k, sz - 1))
    if c == 5: return ('TBind', g_ty(n, d, k + 1, sz - 1))
    if c == 6: return ('TAnd', g_ty(n, d, k, sz - 1), g_ty(n, d, k, sz - 1))
    return ('TOr', g_ty(n, d, k, sz - 1), g_ty(n, d, k, sz - 1))

def g_dms(n, d, sz):                     # d = member depth (self included)
    out = []
    for _ in range(R.randrange(4)):
        if R.random() < 0.4:
            out.append(('dty', g_ty(n, d, 0, 2)))
        else:
            o1 = None if R.random() < 0.5 else g_ty(n, d, 0, 2)
            o2 = None if R.random() < 0.5 else g_ty(n, d, 1, 2)
            out.append(('dfun', o1, o2, g_tm(n, d + 1, sz - 1)))
    return tuple(out)

def g_tm(n, d, sz):
    c = R.randrange(10 if sz > 0 else 1)
    if c <= 3 or sz <= 0:
        opts = []
        if n: opts.append(('tvar', True, R.randrange(n)))
        if d: opts.append(('tvar', False, R.randrange(d)))
        if opts: return R.choice(opts)
        return ('tobj', ())
    if c <= 5: return ('tobj', g_dms(n, d + 1, sz - 1))
    return ('tapp', g_tm(n, d, sz - 1), R.randrange(NL), g_tm(n, d, sz - 1))

def g_config():
    n = R.randrange(4)
    G = tuple(g_dms(n, 0, 3) for _ in range(n))
    return G, g_tm(n, 0, 5)

# ----------------------------------------------------------------- driver
def run(trials=20000, maxsteps=25):
    stats = dict(steps=0, obj=0, appabs=0, stuck=0, answer=0, configs=0)
    for _ in range(trials):
        G, t = g_config()
        stats['configs'] += 1
        for _ in range(maxsteps):
            LG, Lt = tr_store(G), tr_tm(t, len(G), 0)
            assert c_answer(G, t) == l_answer(Lt), ('answer mismatch', G, t)
            rc, rl = c_step(G, t), l_step(LG, Lt)
            if rc is None or rl is None:
                assert rc is None and rl is None, ('step/nostep mismatch', G, t, rc, rl)
                stats['answer' if c_answer(G, t) else 'stuck'] += 1
                break
            G2, t2 = rc
            k, LG2, Lt2 = rl
            assert len(G2) - len(G) == k, ('grows mismatch', G, t)
            if k == 1: stats['obj'] += 1
            elif len(G2) == len(G) and t[0] == 'tapp' and t[1][0] == 'tvar' and t[3][0] == 'tvar':
                stats['appabs'] += 1
            assert tr_store(G2) == LG2, ('store mismatch', G, t, G2, LG2)
            assert tr_tm(t2, len(G2), 0) == Lt2, ('term mismatch', G, t, t2, Lt2)
            stats['steps'] += 1
            G, t = G2, t2
    return stats

if __name__ == '__main__':
    print(run())
