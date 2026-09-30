"""Cohn, pp.31–40: elementary identities and three missing hypotheses.

The (2.2)–(2.10) identities are tested over the noncommutative ring M_2(QQ).
The (5.2) continuant product is a polynomial identity in free variables for
lengths 2–7. Exact examples refute the unrestricted norm example (p.36)
and the omission of f(1)=1 in the three examples after Theorem 11.2 (p.40).
These checks do not prove universality, the full norm classification, or
the classification of GL2 isomorphisms.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

from sage.all import (QQ, ZZ, GF, FreeAlgebra, NumberField, PolynomialRing, block_matrix,
                      identity_matrix, matrix, version)

checks = 0
def verify(assertion):
    global checks
    assert assertion
    checks += 1

zero = matrix(QQ, 2, 2)
one = identity_matrix(QQ, 2)
def E(x):
    return block_matrix([[x, one], [-one, zero]])
def D(a, b):
    return block_matrix([[a, zero], [zero, b]])

x = matrix(QQ, [[2, 1], [0, -1]])
y = matrix(QQ, [[0, 3], [1, 1]])
z = matrix(QQ, [[-1, 0], [4, 2]])
a = matrix(QQ, [[1, 1], [0, 1]])
b = matrix(QQ, [[2, 0], [1, 1]])
verify(x*y != y*x)
verify(a*b != b*a)
verify(E(x)*E(zero)*E(y) == -E(x+y))
verify(E(a)*E(a.inverse())*E(a) == -D(a, a.inverse()))
verify(E(x)*D(a, b) == D(b, a)*E(b.inverse()*x*a))
verify(E(zero)**2 == -identity_matrix(QQ, 4))
verify(E(one)**3 == -identity_matrix(QQ, 4))
verify(E(-one)**3 == identity_matrix(QQ, 4))
verify(E(x).inverse() == E(zero)*E(-x)*E(zero))
verify(E(x)*E(y).inverse() == -E(x-y)*E(zero))
verify(E(x)*E(y).inverse()*E(z) == E(x-y+z))
verify(E(x)*E(a.inverse())*E(y)
       == E(x-a)*D(a.inverse(), a)*E(y-a))
verify(E(x)*E(a+one)*E(b+one)*E(y)
       == -E(x-a.inverse())*D(a, a.inverse())
       *E(-one-a.inverse()-b.inverse())*D(b, b.inverse())*E(y-b.inverse()))

A = FreeAlgebra(QQ, 7, names='t')
variables = A.gens()
def continuant(sequence):
    previous, current = A(0), A(1)
    for item in sequence:
        previous, current = current, current*item-previous
    return current
for length in range(2, 8):
    entries = variables[:length]
    product = identity_matrix(A, 2)
    for item in entries:
        product *= matrix(A, [[item, 1], [-1, 0]])
    expected = matrix(A, [
        [continuant(entries), continuant(entries[:-1])],
        [-continuant(entries[1:]), -continuant(entries[1:-1])],
    ])
    verify(product == expected)

# The printed unrestricted example already fails N.4 for Q: 1/2 is a unit.
verify(QQ(1)/2 != 1 and QQ(1)/2 < 1)
# It also fails for the ring of integers of a real quadratic field: a unit
# has absolute value different from 1 in either real embedding.
P = PolynomialRing(QQ, 't')
t = P.gen()
K = NumberField(t*t-2, 'r')
r = K.gen()
unit = 1+r
verify(unit*(r-1) == 1)
verify(unit*unit != 1)

# Precisely the five exceptions named in Cohn's original §6: these integral
# nonunits have squared absolute value 2 or 3, violating N.5.
for d, norm in ((1, 2), (2, 2), (3, 3), (7, 2), (11, 3)):
    K = NumberField(t*t+d, 's')
    s = K.gen()
    value = 1+s if d == 1 else s if d in (2, 3) else (1+s)/2
    verify(value in K.ring_of_integers())
    verify(value.norm() == norm and 1 < norm < 4)

# R=QQ[t] satisfies the degree/weak-algorithm hypotheses. The zero QQ-linear
# map does not preserve the elementary relation E(1)^3=-I: its proposed
# generator map would give E(0)^3=-E(0), not -I. Hence f(1)=1 is indispensable.
I = identity_matrix(QQ, 2)
e0 = matrix(QQ, [[0, 1], [-1, 0]])
e1 = matrix(QQ, [[1, 1], [-1, 0]])
verify(e1**3 == -I)
verify(e0**3 != -I)

# The rank-zero free algebra over F2 is F2 itself, whose GL2 has only six
# elements. Seven distinct determinant-one polynomial matrices refute the
# claimed isomorphism with GL2(F2[t]) when rank zero is allowed.
k = GF(2)
elements = [matrix(k, [[a, b], [c, d]])
            for a in k for b in k for c in k for d in k]
verify(len([M for M in elements if M.det() != 0]) == 6)
B = PolynomialRing(k, 'x')
z = B.gen()
witnesses = [matrix(B, [[1, z**r], [0, 1]]) for r in range(7)]
verify(all(M.det() == 1 for M in witnesses))
verify(all(M != N for i, M in enumerate(witnesses) for N in witnesses[i+1:]))

root = Path(__file__).resolve().parents[2]
Zx = PolynomialRing(ZZ, 'x'); x = Zx.gen()
def weighted(polynomial):
    return sum(abs(coefficient)*2**degree
               for degree, coefficient in enumerate(polynomial.list()))
verify(weighted(x-1) == weighted(x+1) == 3)
verify(weighted((x-1)*(x+1)) == 5)
verify(weighted((x-1)*(x+1)) != weighted(x-1)*weighted(x+1))
report = {
    'checked_at': datetime.now(timezone.utc).isoformat(),
    'sage': version(), 'checks': checks,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'text_sha256': {name: hashlib.sha256((root/'content'/name).read_bytes()).hexdigest()
                    for name in ('11-cohn-summary.typ', '12-cohn-homomorphisms.typ')},
    'passages': ['eq:cohn-addition-relation', 'eq:cohn-unit-relation',
                 'eq:cohn-diagonal-relation', 'eq:cohn-small-orders',
                 'eq:cohn-inverse-relation', 'eq:cohn-quotient-relation',
                 'eq:cohn-ternary-relation', 'eq:cohn-unit-reduction',
                 'eq:cohn-double-unit-reduction', 'eq:cohn-continuant-product',
                 'passage:cohn-norm-examples', 'passage:cohn-unital-linear-examples',
                 'passage:cohn-free-algebra-gl2',
                 'passage:cohn-polynomial-weighted-function'],
    'literature': 'P. M. Cohn, On the structure of the GL2 of a ring, '
                  'Publ. Math. IHES 30 (1966), §§5–6 and §11, Theorem 11.2.',
    'scope': 'Noncommutative sample identities, free continuants through length 7, '
             'exact counterexamples; no classification theorem is asserted.',
}
(root/'checks/cohn-elementary-sage.json').write_text(
    json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print(f'ok cohn-elementary: {checks} checks')
