"""Proof-of-concept: pairing-free ABE (Lagrange interpolation over an access tree, ECC scalar mult).
Policy used: A AND B.  Curve: secp256k1.  Reference only - NOT constant-time, NOT production crypto.
Run: python3 scheme_poc.py
"""
import random
rnd = random.Random(2026)
p = 2**256 - 2**32 - 977
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    if P[0] == Q[0] and (P[1] + Q[1]) % p == 0: return None
    l = (3*P[0]*P[0]*pow(2*P[1], -1, p) if P == Q else (Q[1]-P[1])*pow(Q[0]-P[0], -1, p)) % p
    x = (l*l - P[0] - Q[0]) % p
    return (x, (l*(P[0]-x) - P[1]) % p)
def neg(P): return None if P is None else (P[0], (-P[1]) % p)
def mul(k, P):
    k %= n; R = None
    while k:
        if k & 1: R = add(R, P)
        P = add(P, P); k >>= 1
    return R
def inv(a): return pow(a, -1, n)
def lam(xs, i):                      # Lagrange coefficient at 0, scalar field
    r = 1
    for j, xj in enumerate(xs):
        if j != i: r = r * xj * inv(xj - xs[i]) % n
    return r
def interp0(pts):                    # q(0) from scalar points
    xs = [x for x, _ in pts]
    return sum(y * lam(xs, i) for i, (_, y) in enumerate(pts)) % n
def interp0_exp(xs, Ys):             # q(0)*G from points q(x_i)*G ("interpolation in the exponent")
    R = None
    for i, Y in enumerate(Ys): R = add(R, mul(lam(xs, i), Y))
    return R
def interp_at(pts, x0):
    xs = [x for x, _ in pts]; s = 0
    for i, (xi, yi) in enumerate(pts):
        t = yi
        for j, xj in enumerate(xs):
            if j != i: t = t * (x0 - xj) * inv(xi - xj) % n
        s += t
    return s % n
R = lambda: rnd.randrange(1, n)

# ---------- Attribute Authority: attribute secrets, users, a_j = S_j / d_i ----------
S = {"A": R(), "B": R()}
users = {1: {"A"}, 2: {"B"}, 3: {"A", "B"}, 4: {"A", "B"}}          # users 1,2 only partly satisfy A AND B
d = {i: R() for i in users}
D = {i: mul(d[i], G) for i in users}
a = {i: {j: S[j] * inv(d[i]) % n for j in users[i]} for i in users}

# ---------- Data Owner: polynomial through (0,k),(1,S_A),(2,S_B); aux point (3,q(3)) published per user ----------
k = R(); q3 = interp_at([(0, k), (1, S["A"]), (2, S["B"])], 3)
aux = {i: q3 * inv(d[i]) % n for i in users}
K = mul(k, G)
M = mul(R(), G)                      # message must be a curve point
ok = lambda b: "OK  " if b else "FAIL"

print("== ORIGINAL CONSTRUCTION ==")
q0 = interp0([(1, a[3]["A"]), (2, a[3]["B"]), (3, aux[3])])
print(ok(mul(q0, D[3]) == K), "authorised user 3 recovers K = kP")
print(ok(q0 == k * inv(d[3]) % n), "q'(0) = k/d_i (Eq. 6)")
print(ok(interp0([(1, a[1]["A"]), (3, aux[1])]) * 1 != q0), "user 1 alone (only attribute A) cannot interpolate")
Y1 = mul(a[1]["A"], D[1]); Y2 = mul(a[2]["B"], D[2]); Y3 = mul(aux[1], D[1])
Kc = interp0_exp([1, 2, 3], [Y1, Y2, Y3])
print("ATTACK", "SUCCEEDS" if Kc == K else "fails", ": users 1+2 (neither authorised) recover K = kP by pooling a_j*D_i = S_j*P")
Kx = K[0] % n
r = R(); C1 = mul(r, G); C2 = add(M, mul(r * Kx % n, mul(D[3][0] % n, G)))   # as written: P1 = Dx*P of ONE user's D
for u in (3, 4):
    Mx = add(C2, neg(mul(Kx * (D[u][0] % n) % n, C1)))
    print(ok(Mx == M) if u == 3 else "INCONSISTENT" if Mx != M else "ok", f"authorised user {u} decrypts ciphertext built with user 3's Dx")

print("\n== NAIVE FIX (common K, no blinding): attack still decrypts ==")
C2n = add(M, mul(Kx, C1))
print("ATTACK", "SUCCEEDS" if add(C2n, neg(mul(Kc[0] % n, C1))) == M else "fails", "(colluders decrypt)")

print("\n== REPAIRED CONSTRUCTION: per-user, per-ciphertext blinding  E_i = rho_i*D_i ==")
rho = {i: R() for i in users}
E = {i: mul(rho[i], D[i]) for i in users}
Ki = {i: mul(rho[i], K) for i in users}                           # DO knows k and rho_i
r = R(); C1 = mul(r, G)
C2 = {i: add(M, mul(Ki[i][0] % n, C1)) for i in users}
for u in (3, 4):
    q0 = interp0([(1, a[u]["A"]), (2, a[u]["B"]), (3, aux[u])])
    Ku = mul(q0, E[u])
    print(ok(Ku == Ki[u] and add(C2[u], neg(mul(Ku[0] % n, C1))) == M), f"authorised user {u} decrypts its own component")
# colluders 1 and 2: try every natural pooled combination, aimed at every user's component
Ys = {"a1*E1": mul(a[1]["A"], E[1]), "a2*E2": mul(a[2]["B"], E[2]), "aux1*E1": mul(aux[1], E[1]),
      "a1*D1": Y1, "a2*D2": Y2, "aux1*D1": Y3}
cands = [interp0_exp([1, 2, 3], [Ys["a1*E1"], Ys["a2*E2"], Ys["aux1*E1"]]),
         interp0_exp([1, 2, 3], [Ys["a1*E1"], Ys["a2*E2"], Ys["aux1*E1"]]),
         interp0_exp([1, 2, 3], [Ys["a1*D1"], Ys["a2*D2"], Ys["aux1*D1"]])]
for h in users:                                                    # also re-base onto every header entry
    for ca in (a[1]["A"], a[2]["B"], aux[1], aux[2]):
        cands.append(interp0_exp([1, 2, 3], [mul(a[1]["A"], E[h]), mul(a[2]["B"], E[h]), mul(aux[h], E[h])]))
broken = any(c == Ki[j] for c in cands for j in users) or any(c == K for c in cands)
print("ATTACK", "SUCCEEDS" if broken else "fails", f"({len(cands)} pooled combinations tried; none yields any K_j = rho_j*k*P)")
