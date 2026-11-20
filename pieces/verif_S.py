# -*- coding: utf-8 -*-
"""Verification en arithmetique de boules (Arb, python-flint) du certificat de la classe S et des inegalites
du theoreme final.  Tout part de rationnels exacts lus dans certificat_S.json.  Chaque ligne « OK » est une
inegalite etablie avec encadrement rigoureux ; « ECHEC » signifie non etablie (pas : fausse).

Points verifies :
 0. auto-controle des formules de derivees (differences finies en haute precision) ;
 1. q(0) >= 1 ;
 2. q >= 0 sur [0, XA] (cellules, developpement de Taylor a l'ordre 2 avec reste encadre) ;
 3. q >= 0 sur [XA, +infini[ (forme periodique de periode 96, amplitudes encadrees) ;
 4. C(psi) (integrales doubles rigoureuses) -> V = 2 - C(psi) ;
 5. eps : 1 + nu^ >= 1 - eps sur [0, 1] ;
 6. majorant : C(u) >= 0 sur une periode, g >= w sur [0, 1/2] ;
 7. inegalites (IV) paires, (III) points lourds, (I) blocs, (II) paires de base.
Usage : python verif_S.py [points a executer, ex. 0123] [fichier json]
Relu le 19 nov. 2026 par un second modele (rapports/contradicteur_lemme_final.md) ; deux retouches en sont
sorties : le cas indecidable de la borne de Taylor (min_parabole) et le libelle du point 2."""
import sys, json, time
from fractions import Fraction
sys.path.append(r"C:\Users\kaisb\KRY\fiches\proportion\_outils")
from flint import arb, acb, fmpq, fmpq_poly, ctx

ctx.prec = 150
quoi = sys.argv[1] if len(sys.argv) > 1 else "01234567"
fichier = sys.argv[2] if len(sys.argv) > 2 else "certificat_S.json"
D = json.load(open(fichier))

def Q(s):
    f = Fraction(s)
    return fmpq(f.numerator, f.denominator)

def boule(c, r):
    """boule de centre c (rationnel ou arb) et de rayon >= r."""
    return arb(c) + arb(mid=0, rad=1) * arb(r)

def inf(x):
    return x.lower()

def sup(x):
    return x.upper()

PI = arb.pi()
A1 = Q(D["a"][0]); A2 = Q(D["a"][1])
KAPPA = 1 - A1 + A2
HINV = int(D["H_inv"]); H = fmpq(1, HINV)
assert HINV == 48
ATOMES = [(fmpq(int(k), 20), Q(s)) for k, s in D["s"]]          # (t_k, s_k), t_0 = 0
assert ATOMES[0][0] == 0
S0 = ATOMES[0][1]
PI0 = Q(D["pi0"])
SPL = [(fmpq(int(n), 96), Q(p)) for n, p in D["pi"]]             # (centre c_j = n/96, pi_j)
assert all(p >= 0 for _, p in SPL) and PI0 >= 0
NUM = sum((-s for t, s in ATOMES[1:] if s < 0), fmpq(0)) / S0     # nu-
NUP = sum((s for t, s in ATOMES[1:] if s > 0), fmpq(0)) / S0      # nu+
THETA = Q(D["theta"]); JM = int(D["J"]); HG = THETA / JM
CG = [Q(c) for c in D["cg"]]
LAM = CG[0]; P0 = 2 * LAM
CNIV = Q(D["c"])
DSEUIL = {(2, 2): Q(D["d22"]), (2, 1): Q(D["d21"]), (1, 1): Q(D["d11"])}

# ---------------------------------------------------------------- fonctions de base
NT = 45
_fact = [arb(1)]
for n in range(1, 2 * 64 + 4):
    _fact.append(_fact[-1] * n)
_cs = [(-1) ** n * PI ** (2 * n) / _fact[2 * n + 1] for n in range(NT + 1)]
_TAIL = arb(mid=0, rad=arb("1e-40"))

def sinc3(y):
    """(sinc, sinc', sinc'')(y), sinc(y) = sin(pi y)/(pi y), y boule reelle."""
    if y.abs_lower() > 0.5:
        s, c = y.sin_cos_pi()
        y2 = y * y
        return s / (PI * y), c / y - s / (PI * y2), -PI * s / y - 2 * c / y2 + 2 * s / (PI * y2 * y)
    assert y.abs_upper() < 1.7
    z = y * y
    f0 = arb(0); g1 = arb(0); g2 = arb(0)
    for n in range(NT, -1, -1):
        f0 = f0 * z + _cs[n]
    for n in range(NT, 0, -1):
        g1 = g1 * z + 2 * n * _cs[n]
        g2 = g2 * z + 2 * n * (2 * n - 1) * _cs[n]
    return f0 + _TAIL, y * g1 + _TAIL, g2 + _TAIL

def K3(x):
    out = list(sinc3(x))
    for j, aj in ((1, A1), (2, A2)):
        g1 = sinc3(x - j); g2 = sinc3(x + j)
        for d in range(3):
            out[d] = out[d] + (arb(aj) / 2) * (g1[d] + g2[d])
    return out

def k23(x):
    k0, k1, k2 = K3(x)
    return k0 * k0, 2 * k0 * k1, 2 * (k1 * k1 + k0 * k2)

def r3(x):
    acc = [arb(0), arb(0), arb(0)]
    for t, s in ATOMES:
        if t == 0:
            v = k23(x)
            for d in range(3):
                acc[d] += arb(s) * v[d]
        else:
            v1 = k23(x - arb(t)); v2 = k23(x + arb(t))
            for d in range(3):
                acc[d] += (arb(s) / 2) * (v1[d] + v2[d])
    return acc

def spl3(x):
    """somme des splines : sum_j pi_j 2 H sinc(H x)^3 cos(2 pi c_j x), et ses deux derivees."""
    s0, s1, s2 = sinc3(arb(H) * x)
    s1 = s1 * arb(H); s2 = s2 * arb(H) * arb(H)
    u = s0 ** 3; u1 = 3 * s0 * s0 * s1; u2 = 6 * s0 * s1 * s1 + 3 * s0 * s0 * s2
    c0 = arb(0); c1 = arb(0); c2 = arb(0)
    for c, p in SPL:
        si, co = (2 * arb(c) * x).sin_cos_pi()
        om = 2 * PI * arb(c)
        c0 += arb(p) * co; c1 -= arb(p) * om * si; c2 -= arb(p) * om * om * co
    f = 2 * arb(H)
    return f * u * c0, f * (u1 * c0 + u * c1), f * (u2 * c0 + 2 * u1 * c1 + u * c2)

# element de bord B0 : t = 48 (al - 1) ; 2t - 1.5 t^2 sur [1, 1+H] ; 0.5 (2 - t)^2 sur [1+H, 1+2H]
_al = fmpq_poly([0, 1])
_t = HINV * (_al - 1)
_B0 = [(fmpq(1), 1 + H, 2 * _t - fmpq(3, 2) * _t * _t), (1 + H, 1 + 2 * H, fmpq(1, 2) * (2 - _t) * (2 - _t))]
NE = 60
_mu = []
for m in range(2 * NE + 3):
    tot = fmpq(0)
    for (a_, b_, P) in _B0:
        F = (P * _al ** m).integral()
        tot += F(b_) - F(a_)
    _mu.append(tot)

def _ipp(P, a_, b_, om, cosinus):
    """int_a^b P(al) cos(om al) d al (cosinus=True) ou sin, par parties ; om boule > 0."""
    tot = arb(0)
    for (pt, sg) in ((b_, 1), (a_, -1)):
        si, co = (om * arb(pt)).sin_cos()
        Tc = [si, co, -si, -co]; Ts = [-co, si, co, -si]
        Pk = P; k = 0; acc = arb(0)
        while Pk.degree() >= 0:
            tr = (Tc if cosinus else Ts)[k % 4]
            acc += arb(Pk(pt)) * tr / om ** (k + 1)
            Pk = Pk.derivative(); k += 1
        tot += sg * acc
    return tot

def pe3(x):
    """element de bord : p_e(x) = 2 int B0(al) cos(2 pi x al) d al, et ses deux derivees."""
    if x.abs_upper() < 1.25:
        w2 = (2 * PI) ** 2
        z = x * x
        f0 = arb(0); g1 = arb(0); g2 = arb(0)
        cf = [(-1) ** n * w2 ** n * arb(_mu[2 * n]) / _fact[2 * n] for n in range(NE + 1)]
        for n in range(NE, -1, -1):
            f0 = f0 * z + cf[n]
        for n in range(NE, 0, -1):
            g1 = g1 * z + 2 * n * cf[n]
            g2 = g2 * z + 2 * n * (2 * n - 1) * cf[n]
        return 2 * f0 + _TAIL, 2 * x * g1 + _TAIL, 2 * g2 + _TAIL
    om = 2 * PI * x
    v0 = arb(0); v1 = arb(0); v2 = arb(0)
    for (a_, b_, P) in _B0:
        v0 += _ipp(P, a_, b_, om, True)
        v1 += _ipp(P * _al, a_, b_, om, False)
        v2 += _ipp(P * _al * _al, a_, b_, om, True)
    return 2 * v0, -2 * (2 * PI) * v1, -2 * (2 * PI) ** 2 * v2

def q3(x):
    r = r3(x); e = pe3(x); s = spl3(x)
    return [r[d] - arb(PI0) * e[d] - s[d] for d in range(3)]

def min_parabole(a0, b, c2, dm):
    """minorant rigoureux de a0 - b s + (c2/2) s^2 pour s dans [0, dm] (b >= 0).
    Une comparaison de boules n'est vraie que si elle est certaine ; trois cas :
    sommet certainement dans la cellule -> valeur au sommet ; sommet certainement au-dela du bord, ou
    parabole non convexe -> valeur au bord ; indecidable -> valeur au sommet, qui minore la parabole partout
    (retouche du 19 nov. 2026 apres relecture : l'ancien code prenait alors la valeur au bord)."""
    if c2 > 0:
        if b < c2 * dm:
            return inf(a0 - b * b / (2 * c2))
        if b > c2 * dm:
            return inf(a0 - b * dm + c2 * dm * dm / 2)
        return inf(a0 - b * b / (2 * c2))
    assert c2 <= 0
    return inf(a0 - b * dm + c2 * dm * dm / 2)

def borne_inf_q(lo, hi):
    """minorant rigoureux de q sur [lo, hi] (rationnels) : Taylor a l'ordre 2, derivee seconde encadree sur la cellule."""
    m = (lo + hi) / 2; dem = (hi - lo) / 2
    q0, q1, _ = q3(arb(m))
    Q2 = q3(boule(m, dem))[2]
    return min_parabole(inf(q0), q1.abs_upper(), inf(Q2), arb(dem))

def ok(nom, cond, detail=""):
    print(f"  [{'OK' if cond else 'ECHEC'}] {nom} {detail}", flush=True)
    return cond

bilan = {}
t00 = time.time()
print(f"certificat : fenetre a = ({D['a'][0]}, {D['a'][1]}), {len(ATOMES)} atomes, {len(SPL)} splines, pi_0 = {D['pi0']} ;"
      f" s0 = {float(S0):.6f}, nu- = {float(NUM):.6f}, nu+ = {float(NUP):.6f} ; theta = {D['theta']}, Lambda = {float(LAM):.6f}, p0 = {float(P0):.6f}, c = {D['c']}")

# ---------------------------------------------------------------- 0. auto-controle des derivees
if "0" in quoi:
    print("0. auto-controle des formules (differences finies, precision 400 bits)")
    ctx.prec = 400
    hh = arb("1e-12"); pire = 0.0
    for xs_ in ("0.37", "0.9991", "1.24", "1.26", "2.0003", "7.5", "23.113", "47.045", "96.5", "311.25"):
        x = arb(xs_)
        f = q3(x); fp = q3(x + hh); fm = q3(x - hh)
        d1 = (fp[0] - fm[0]) / (2 * hh); d2 = (fp[1] - fm[1]) / (2 * hh)
        e1 = abs(float((d1 - f[1]).mid())); e2 = abs(float((d2 - f[2]).mid()))
        pire = max(pire, e1, e2)
    ctx.prec = 150
    bilan["0"] = ok("derivees premiere et seconde de q coherentes", pire < 1e-16, f"(ecart maximal {pire:.1e})")

# ---------------------------------------------------------------- 1. q(0)
if "1" in quoi:
    print("1. normalisation")
    q0 = q3(arb(0))[0]
    bilan["1"] = ok("q(0) >= 1", inf(q0) >= 1, f"(q(0) dans {q0})")

# ---------------------------------------------------------------- 2. q >= 0 sur [0, XA]
XA = 480
if "2" in quoi:
    print(f"2. q >= 0 sur [0, {XA}] par cellules")
    t0 = time.time(); ncell = 0; echec = None; pire = None
    pile = []
    def largeur(x):
        return fmpq(1, 64) if x < 60 else fmpq(1, 32)
    x = fmpq(0)
    while x < XA and echec is None:
        wdt = largeur(x)
        pile = [(x, x + wdt)]
        while pile:
            lo, hi = pile.pop()
            lb = borne_inf_q(lo, hi); ncell += 1
            if lb > 0:
                v = float(lb) * (1 + float(lo) ** 2)
                if pire is None or v < pire[0]:
                    pire = (v, float(lo), float(hi - lo))
            elif hi - lo < fmpq(1, 2 ** 22):
                echec = (float(lo), float(hi), float(lb)); break
            else:
                mi = (lo + hi) / 2
                pile.append((mi, hi)); pile.append((lo, mi))
        x += wdt
        if ncell % 5000 < 3 and ncell > 3:
            print(f"     ... x = {float(x):.2f}, {ncell} cellules, {time.time()-t0:.0f}s", flush=True)
    bilan["2"] = ok(f"q > 0 sur [0, {XA}]", echec is None,
                    f"({ncell} cellules, {time.time()-t0:.0f}s ; minorant de cellule le plus bas : (1+x^2) q >= {pire[0]:.2e} pres de x = {pire[1]:.4f} ; c'est une borne, pas une valeur de q)" if echec is None
                    else f"(cellule non etablie : [{echec[0]:.8f}, {echec[1]:.8f}], minorant {echec[2]:.3e})")

# ---------------------------------------------------------------- 3. queue
if "3" in quoi:
    print(f"3. q >= 0 sur [{XA}, +infini[ : x = y + 96 n")
    t0 = time.time()
    xa = arb(XA)
    zmin = xa - 6
    etab = abs(arb(A1)) / (zmin * zmin - 1) + 4 * abs(arb(A2)) / (zmin * zmin - 4)
    kap = arb(KAPPA)
    def enc(lo, hi):
        return (lo + hi) / 2 + arb(mid=0, rad=1) * (hi - lo) / 2
    k2enc = enc((kap - etab) ** 2, (kap + etab) ** 2)
    inv_x = enc(arb(0), 1 / xa)
    amp = []
    for t, s in ATOMES:
        if t == 0:
            amp.append((t, s, k2enc, None))
        else:
            at = arb(t)
            assert at < 6.01
            amp.append((t, s, k2enc * enc(arb(1), (xa / (xa - at)) ** 2), k2enc * enc((xa / (xa + at)) ** 2, arb(1))))
    Hh = arb(H)
    def F(y):
        tot = arb(0)
        for t, s, am, ap in amp:
            if t == 0:
                si = y.sin_pi(); tot += arb(s) * si * si * am / PI ** 2
            else:
                s1 = (y - arb(t)).sin_pi(); s2 = (y + arb(t)).sin_pi()
                tot += (arb(s) / 2) * (s1 * s1 * am + s2 * s2 * ap) / PI ** 2
        # bord : x^2 pi0 p_e = pi0 2 [ -(2/H) cos(2 pi y)/(4 pi^2) + (1/x) (1/(8 pi^3 H^2)) (-3 sin w + 4 sin w(1+H) - sin w(1+2H)) ]
        e3 = -3 * (2 * y).sin_pi() + 4 * (2 * y * (1 + Hh)).sin_pi() - (2 * y * (1 + 2 * Hh)).sin_pi()
        tot -= arb(PI0) * 2 * (-(2 / Hh) * (2 * y).cos_pi() / (4 * PI ** 2) + inv_x * e3 / (8 * PI ** 3 * Hh ** 2))
        # splines : (2/(pi^3 H^2)) (1/x) sin^3(pi H y) C0(y)
        c0 = arb(0)
        for c, p in SPL:
            c0 += arb(p) * (2 * arb(c) * y).cos_pi()
        tot -= (2 / (PI ** 3 * Hh ** 2)) * inv_x * (Hh * y).sin_pi() ** 3 * c0
        return tot
    # auto-controle : la forme periodique encadre bien x^2 q(x) (comparaison directe en quelques points)
    for ys_, n_ in (("0.3", 5), ("24.005", 5), ("47.9", 7), ("77.7", 60), ("95.99", 400), ("12.5", 5)):
        yy = arb(ys_); xx = yy + 96 * n_
        val = xx * xx * q3(xx)[0]
        assert F(yy).contains(val), ("forme periodique incoherente", ys_, n_, F(yy), val)
    print("     auto-controle : la forme periodique contient x^2 q(x) aux 6 points d'essai", flush=True)
    ncell = 0; echec = None; pire = None
    pas = fmpq(1, 1024)
    y = fmpq(0)
    while y < 96 and echec is None:
        pile = [(y, y + pas)]
        while pile:
            lo, hi = pile.pop()
            v = F(boule((lo + hi) / 2, (hi - lo) / 2)); ncell += 1
            if inf(v) > 0:
                if pire is None or float(inf(v)) < pire[0]:
                    pire = (float(inf(v)), float(lo))
            elif hi - lo < fmpq(1, 2 ** 20):
                echec = (float(lo), float(inf(v))); break
            else:
                mi = (lo + hi) / 2
                pile.append((mi, hi)); pile.append((lo, mi))
        y += pas
        if ncell % 20000 < 2 and ncell > 2:
            print(f"     ... y = {float(y):.2f}, {ncell} cellules, {time.time()-t0:.0f}s", flush=True)
    bilan["3"] = ok(f"x^2 q(x) > 0 pour tout x >= {XA}", echec is None,
                    f"({ncell} cellules, {time.time()-t0:.0f}s ; minorant de x^2 q : {pire[0]:.3e} pres de y = {pire[1]:.3f})" if echec is None
                    else f"(cellule non etablie pres de y = {echec[0]:.6f}, minorant {echec[1]:.3e})")

# ---------------------------------------------------------------- 4. valeur
if "4" in quoi:
    print("4. C(psi) et V")
    t0 = time.time()
    ctx.prec = 100
    pi_c = acb.pi()
    a1c = acb(arb(A1)); a2c = acb(arb(A2))
    def wc(u):
        return 1 + a1c * (2 * pi_c * u).cos() + a2c * (4 * pi_c * u).cos()
    demi = acb(arb(fmpq(1, 2)))
    tol = arb(2) ** (-70)
    def Dt(t):
        tc = acb(arb(t))
        def interieur(u):
            f = lambda v, _: (u - v) * (2 * pi_c * tc * (u - v)).cos() * wc(v)
            return acb.integral(f, -demi, u, rel_tol=tol, abs_tol=tol) - acb.integral(f, u, demi, rel_tol=tol, abs_tol=tol)
        return acb.integral(lambda u, _: wc(u) * interieur(u), -demi, demi, rel_tol=tol, abs_tol=tol)
    intw2 = 1 + (arb(A1) ** 2 + arb(A2) ** 2) / 2
    Cpsi = arb(0)
    for t, s in ATOMES:
        d = Dt(t)
        assert d.imag.abs_upper() < 1e-15
        Cpsi += arb(s) * (intw2 + d.real)
    ctx.prec = 150
    Vinf = inf(2 - Cpsi)
    REC = arb("0.6780092")
    bilan["4"] = ok("V = 2 - C(psi) au-dessus du record 0,6780092", Vinf > REC,
                    f"(C(psi) dans {Cpsi} ; V >= {float(Vinf):.9f} ; ecart au record >= {float(inf(Vinf - REC)):.3e} ; (1+V)/2 >= {float(inf((1 + Vinf) / 2)):.9f} ; {time.time()-t0:.0f}s)")
    bilan["V"] = float(Vinf)

# ---------------------------------------------------------------- 5. eps
if "5" in quoi or "7" in quoi:
    print("5. eps")
    nus = [(t, s / S0) for t, s in ATOMES[1:]]
    N5 = 20000; mmin = None
    for i in range(N5):
        al = boule(fmpq(2 * i + 1, 2 * N5), fmpq(1, 2 * N5))
        v = arb(1)
        for t, nu in nus:
            v += arb(nu) * (2 * arb(t) * al).cos_pi()
        if mmin is None or inf(v) < mmin:
            mmin = inf(v)
    EPS = sup(1 - mmin)
    bilan["5"] = ok("1 + nu^ >= 1 - eps sur [0, 1]", mmin > 0, f"(eps <= {float(EPS):.6f})")

# ---------------------------------------------------------------- 6. majorant
if "6" in quoi:
    print("6. majorant du grand crible")
    t0 = time.time()
    hg = arb(HG); cga = [arb(c) for c in CG]
    def C3(u):
        c0 = cga[0] + arb(0); c1 = arb(0); c2 = arb(0)
        for j in range(1, JM):
            si, co = (2 * j * hg * u).sin_cos_pi()
            om = 2 * PI * j * hg
            c0 += 2 * cga[j] * co; c1 -= 2 * cga[j] * om * si; c2 -= 2 * cga[j] * om * om * co
        return c0, c1, c2
    def taylor_inf(f3, lo, hi):
        m = (lo + hi) / 2; dem = arb((hi - lo) / 2)
        f0, f1, _ = f3(arb(m)); F2 = f3(boule(m, (hi - lo) / 2))[2]
        return min_parabole(inf(f0), f1.abs_upper(), inf(F2), dem)
    def balaye(f3, lo, hi, pas, nom):
        n = 0; pire = None; x = lo
        while x < hi:
            pile = [(x, min(x + pas, hi))]
            while pile:
                a_, b_ = pile.pop(); lb = taylor_inf(f3, a_, b_); n += 1
                if lb > 0:
                    if pire is None or float(lb) < pire:
                        pire = float(lb)
                elif b_ - a_ < fmpq(1, 2 ** 22):
                    return False, f"(non etabli pres de {float(a_):.6f}, minorant {float(lb):.3e})"
                else:
                    mi = (a_ + b_) / 2; pile.append((mi, b_)); pile.append((a_, mi))
            x += pas
        return True, f"({n} cellules ; minimum >= {pire:.3e})"
    r1 = balaye(C3, fmpq(0), 1 / (2 * HG), fmpq(1, 128), "C")
    b1 = ok("C(u) > 0 sur une demi-periode [0, 1/(2h)]", r1[0], r1[1])
    def gw3(u):
        s0_, s1_, s2_ = sinc3(hg * u)
        s1_ = s1_ * hg; s2_ = s2_ * hg * hg
        e0 = s0_ * s0_; e1 = 2 * s0_ * s1_; e2 = 2 * (s1_ * s1_ + s0_ * s2_)
        c0, c1, c2 = C3(u)
        g0 = hg * e0 * c0; g1 = hg * (e1 * c0 + e0 * c1); g2 = hg * (e2 * c0 + 2 * e1 * c1 + e0 * c2)
        s_1, c_1 = (2 * u).sin_cos_pi(); s_2, c_2 = (4 * u).sin_cos_pi()
        w0 = 1 + arb(A1) * c_1 + arb(A2) * c_2
        w1 = -arb(A1) * 2 * PI * s_1 - arb(A2) * 4 * PI * s_2
        w2 = -arb(A1) * (2 * PI) ** 2 * c_1 - arb(A2) * (4 * PI) ** 2 * c_2
        return g0 - w0, g1 - w1, g2 - w2
    r2 = balaye(gw3, fmpq(0), fmpq(1, 2), fmpq(1, 512), "g-w")
    b2 = ok("g >= w sur [0, 1/2]", r2[0], r2[1])
    bilan["6"] = b1 and b2
    print(f"     ({time.time()-t0:.0f}s) ; g^ est lineaire par morceaux, nulle hors de ]-{D['theta']}, {D['theta']}[, g^(0) = Lambda = {float(LAM):.6f}")

# ---------------------------------------------------------------- 7. inegalites du theoreme
if "7" in quoi:
    print("7. inegalites du theoreme final")
    t0 = time.time()
    s0 = arb(S0); num = arb(NUM); nup = arb(NUP); p0 = arb(P0); c = arb(CNIV); lam = arb(LAM)
    a = s0 * (1 - EPS)                       # minorant de s0 (1 - eps) ; eps majore
    cp = c + s0 * num * p0 / a
    beta = s0 * (1 + nup) * p0 - a * c
    betap = beta if inf(beta) > 0 else (beta.union(arb(0)) if hasattr(beta, "union") else abs(beta))
    paire = 4 * a * c - a * cp * cp - betap * betap / a
    A1c = 2 * s0 * cp * num + (2 * betap * s0 / a) * (1 + nup)
    A2c = (s0 * s0 / a) * (num * num + (1 + nup) ** 2)
    print(f"     a >= {float(inf(a)):.6f} ; c' <= {float(sup(cp)):.6f} ; beta <= {float(sup(betap)):.6f} ; A1 <= {float(sup(A1c)):.6f} ; A2 <= {float(sup(A2c)):.6f}")
    b_iv = ok("(IV) paire simple : 4ac - ac'^2 - beta^2/a >= 2", inf(paire) > 2, f"(valeur >= {float(inf(paire)):.5f})")
    b_iv2 = ok("(IV) paires multiples : part(2) >= 8 et pente 4ac >= 6", inf(8 * a * c - a * cp * cp - betap * betap / a) > 8 and inf(4 * a * c) > 6,
               f"(part(2) >= {float(inf(8 * a * c - a * cp * cp - betap * betap / a)):.4f} ; pente >= {float(inf(4 * a * c)):.4f})")
    def psi_inf(r):
        quad = a * r * r - 2 * s0 * num * p0 * r
        lin = 2 * a * c * r - a * cp * cp
        if sup(r) < inf(cp):
            return inf(quad)
        return inf(lin)                      # la droite minore psi partout
    b_iii = ok("(III) points lourds : psi(3) >= 7 et pente 2ac >= 3", psi_inf(arb(3)) > 7 and inf(2 * a * c) > 3,
               f"(psi(3) >= {float(psi_inf(arb(3))):.4f} ; pente >= {float(inf(2 * a * c)):.4f})")
    tau = {1: 1, 2: 4}
    b_i = True; b_ii = True
    assert all(DSEUIL[k] > THETA / 2 for k in DSEUIL)
    for (m, mp) in ((2, 2), (2, 1), (1, 1)):
        ds = DSEUIL[(m, mp)]
        # (I) blocs sur ]0, ds]
        pas = fmpq(1, 512); x = fmpq(0); pire = None; bon = True
        while x < ds:
            hi = min(x + pas, ds)
            Kc = K3(boule((x + hi) / 2, (hi - x) / 2))[0]
            disc = ((m - mp) ** 2 + 4 * m * mp * Kc * Kc).sqrt()
            v = psi_inf((m + mp + disc) / 2) + psi_inf((m + mp - disc) / 2) - (tau[m] + tau[mp])
            if not (v > 0):
                bon = False; pire = (float(x), float(v)); break
            if pire is None or float(v) < pire[1]:
                pire = (float(x), float(v))
            x = hi
        b_i &= ok(f"(I) bloc ({m},{mp}) paye pour 0 < d <= {float(ds):.3f}", bon, f"(marge minimale {pire[1]:.4f} pres de d = {pire[0]:.3f})")
        # (II) paires de base sur [ds, theta[
        x = ds; pire = None; bon = True
        while x < THETA:
            hi = min(x + pas, THETA)
            qL = borne_inf_q(x, hi)
            # max de |g^| sur [x, hi] : noeuds j h et extremites
            def gh(d):
                jj = int(d / HG); jj = min(jj, JM - 1)
                c0_ = CG[jj]; c1_ = CG[jj + 1] if jj + 1 < JM else fmpq(0)
                return c0_ + (c1_ - c0_) * (d - jj * HG) / HG
            pts = [x, hi] + [j * HG for j in range(int(x / HG), int(hi / HG) + 2) if x <= j * HG <= hi]
            gmq = max(abs(gh(d)) for d in pts)            # rationnel exact
            gmax = arb(gmq)
            if (m, mp) == (2, 2):
                L = 2 * gmax
            elif (m, mp) == (2, 1):
                L = (lam / 4) * ((1 + 32 * (gmax / lam) ** 2).sqrt() - 1)
            else:
                L = arb(max(gmq - LAM / 2, fmpq(0)))        # (|g^| - Lambda/2)_+ en rationnels exacts
            v = 2 * m * mp * qL - sup(A1c) * L - 2 * sup(A2c) * L * L
            if not (v > 0):
                bon = False; pire = (float(x), float(inf(v))); break
            if pire is None or float(inf(v)) < pire[1]:
                pire = (float(x), float(inf(v)))
            x = hi
        b_ii &= ok(f"(II) paire de base ({m},{mp}) payee pour {float(ds):.3f} <= d < {float(THETA):.3f}", bon, f"(marge minimale {pire[1]:.5f} pres de d = {pire[0]:.3f})")
    bilan["7"] = b_iv and b_iv2 and b_iii and b_i and b_ii
    print(f"     ({time.time()-t0:.0f}s)")

print(f"BILAN ({time.time()-t00:.0f}s) : " + " ; ".join(f"{k} : {('OK' if v else 'ECHEC') if isinstance(v, bool) else v}" for k, v in bilan.items()))
