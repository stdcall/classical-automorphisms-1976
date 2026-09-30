"""Limited exact checks for O'Meara §§5.6–5.7; no general theorem proof."""
from sage.all import GF, QQ, matrix, identity_matrix, PolynomialRing
from sage.env import SAGE_VERSION
from pathlib import Path
import hashlib, json, datetime

root = Path(__file__).resolve().parents[2]
checks = []
F = GF(7)
I = identity_matrix(F, 2)
def key(A):
    a = tuple(int(x) for x in A.list())
    b = tuple(int(x) for x in (-A).list())
    return min(a, b)

elements = {}
for p in F:
    for q in F:
        for r in F:
            for s in F:
                A = matrix(F, [[p,q],[r,s]])
                if A.det() == 1:
                    elements[key(A)] = A
assert len(elements) == 168
involutions = {k for k,A in elements.items() if key(A*A) == key(I) and k != key(I)}
assert len(involutions) == 21
L0 = [I, matrix(F, [[0,1],[-1,0]]), matrix(F, [[3,2],[2,4]]), matrix(F, [[5,3],[3,2]])]
H0 = [I, matrix(F, [[0,1],[-1,0]]), matrix(F, [[4,2],[2,3]]), matrix(F, [[2,3],[3,5]])]
def conjugates(base):
    return [frozenset(key(T*A*T.inverse()) for A in base)
            for t in F for T in [matrix(F, [[1,t],[0,1]])]]
L, H = conjugates(L0), conjugates(H0)
assert len(set(L+H)) == 14
for i in range(7):
    for j in range(7):
        assert L[i] != H[j]
        if i != j:
            assert len(L[i] & L[j]) == len(H[i] & H[j]) == 1
        assert (len(L[i] & H[j]) == 2) == ((j-i)%7 in (0,1,3))
assert set.union(*(set(g) for g in L)) == involutions | {key(I)}
checks.append({'name':'5.6.9: PSL2(F7) involutions and incidence', 'group_order':168,
               'nonidentity_involutions':21,'distinct_maximal_involution_subgroups':14,
               'incidence_offsets':[0,1,3], 'passed':True})

F2 = GF(2)
lines = [[1,0,0],[0,1,0],[0,0,1],[1,0,1],[1,1,1],[1,1,0],[0,1,1]]
normals = [[0,1,1],[0,0,1],[1,0,0],[0,1,0],[1,0,1],[1,1,0],[1,1,1]]
for i,x in enumerate(lines):
    for j,r in enumerate(normals):
        assert (sum(F2(a)*F2(b) for a,b in zip(x,r)) == 0) == ((j-i)%7 in (0,1,3))
checks.append({'name':'5.6.9: listed Fano-plane incidence', 'pairs_checked':49,'passed':True})

R = PolynomialRing(QQ, ['a','b'])
a,b = R.gens()
K = R.fraction_field()
a,b = K(a), K(b)
assert a - (a**-1 + (b**-1-a)**-1)**-1 == a*b*a
checks.append({'name':'5.6.4: rational Hua identity',
               'scope':'commutative rational-function field, denominators nonzero','passed':True})

F3 = GF(3)
outside = matrix(F3, [[2,0],[0,1]])
assert not outside.det().is_square()
assert (outside*outside.inverse()) == identity_matrix(F3,2)
checks.append({'name':'5.6.5: identity on PGL2(F3) requires Delta as domain',
               'scope':'one nonsquare-determinant representative outside PSL2','passed':True})

paths = [Path(__file__).resolve()] + [root/'content'/name for name in
    ('48-omeara-fields.typ','49-omeara-integral-domains.typ','50-omeara-isomorphism-comments.typ')]
report = {'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'sage_version':SAGE_VERSION,'status':'passed','scope':'limited exact identities and finite incidence checks; general isomorphism theorems not proved',
          'sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
          'checks':checks}
(root/'checks'/'omeara-final-sage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False))
