"""Johnson, §§1,5,6, printed pp.11,27,29: three exact corrections.

The symbolic calculation proves a rank-one commutator identity. The exact
example over Q(i), with its nontrivial conjugation, disproves the printed
criterion when an identity quasisymmetry is allowed. It does not establish
the later automorphism theorem.
"""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

from sage.all import (QQ, GF, FunctionField, NumberField, PolynomialRing, identity_matrix,
                      matrix, vector, version)

R = PolynomialRing(QQ, names=('a', 'b', 'hxx', 'hxy', 'hyx', 'hyy'))
a, b, hxx, hxy, hyx, hyy = R.gens()
X = matrix(R, [[hxx, hyx], [0, 0]])
Y = matrix(R, [[0, 0], [hxy, hyy]])
I = identity_matrix(R, 2)
expected = a*b*matrix(R, [[hyx*hxy, hyx*hyy],
                         [-hxy*hxx, -hxy*hyx]])
assert (I+a*X)*(I+b*Y) - (I+b*Y)*(I+a*X) == expected

S = PolynomialRing(QQ, 't')
t = S.gen()
E = NumberField(t*t+1, 'i')
i = E.gen()
conjugate = E.hom([-i], E)
def star(M):
    return matrix(E, M.ncols(), M.nrows(),
                  lambda r, c: conjugate(M[c, r]))

H = identity_matrix(E, 3)
x = vector(E, [1, 0, 0])
y = vector(E, [1, 1, 0])
def q(v, w):
    return (v.row()*H*vector(E, [conjugate(z) for z in w]).column())[0, 0]
def quasisymmetry(v, epsilon):
    assert q(v, v) != 0
    assert epsilon*conjugate(epsilon) == 1
    row = (H*vector(E, [conjugate(z) for z in v]).column()).transpose()
    return identity_matrix(E, 3) + (epsilon-1)/q(v, v)*v.column()*row

A = quasisymmetry(x, E(1))
B = quasisymmetry(y, E(-1))
assert A == identity_matrix(E, 3)
assert B != A
assert star(A)*H*A == H and star(B)*H*B == H
assert A*B == B*A
assert matrix(E, [x, y]).rank() == 2
assert q(x, y) != 0

# §5 (5.4), printed p.27: when g1=g2=id and chi1=chi2=1,
# the printed left-hand side is B, whereas the right-hand side is I.
# B is noncentral, but the intended product Phi_g2(B) Phi_g1(B)^(-1)=I.
assert B != identity_matrix(E, 3)
assert B*B.inverse() == identity_matrix(E, 3)
assert not B.is_scalar()

# §6 (6.4), printed p.29. E must be infinite, and its involution nontrivial.
# Take E=F_16(t), *=coefficient Frobenius^2, mu=coefficient Frobenius.
# The usual hermitian form is regular on E^3; mu commutes with *.
K = GF(16, 'c')
L = FunctionField(K, 't')
u = L.gen()
mu = L.hom(u, base_morphism=K.frobenius_endomorphism(1))
mu_inverse = L.hom(u, base_morphism=K.frobenius_endomorphism(3))
involution = L.hom(u, base_morphism=K.frobenius_endomorphism(2))
epsilon = L(K.multiplicative_generator()**3)
assert epsilon**5 == 1 and epsilon != 1
assert epsilon*involution(epsilon) == 1
assert mu(epsilon) != mu_inverse(epsilon)
sigma = matrix(L, [[epsilon, 0, 0], [0, 1, 0], [0, 0, 1]])
def entrywise(automorphism, M):
    return M.apply_map(automorphism)
def adjoint(M):
    return entrywise(involution, M.transpose())
assert adjoint(sigma)*sigma == identity_matrix(L, 3)
# For arbitrary norm-one rational functions the t-adic valuation is zero,
# so residue at t=0 is a well-defined homomorphism to the five norm-one
# constants. Take chi(sigma) to be that residue of det(sigma), embedded in L.
# Our diagonal sigma has constant determinant, hence chi(sigma)=epsilon.
chi = sigma.det()
homothety_sigma = chi*sigma
actual = entrywise(mu, homothety_sigma)
corrected = mu(chi)*entrywise(mu, sigma)
printed = mu_inverse(chi)*entrywise(mu, sigma)
assert actual == corrected
assert actual != printed
# This finite-valued chi gives an automorphism P_chi: for scalar epsilon,
# chi(epsilon I)=epsilon^3, hence P_chi^2=id. Check the witness exactly.
assert homothety_sigma.det()*homothety_sigma == sigma

root = Path(__file__).resolve().parents[2]
passage = root/'content/02-johnson-basic-notions.typ'
report = {
    'checked_at': datetime.now(timezone.utc).isoformat(),
    'sage': version(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'text_sha256': {name: hashlib.sha256((root/'content'/name).read_bytes()).hexdigest()
                    for name in ('02-johnson-basic-notions.typ',
                                 '06-johnson-isomorphisms.typ',
                                 '07-johnson-automorphisms.typ')},
    'passages': ['passage:johnson-rank-one-commutation',
                 'passage:johnson-uniqueness-central-product',
                 'passage:johnson-main-decomposition'],
    'printed_pages': [11, 27, 29],
    'results': {
        'symbolic_rank_one_commutator': 'proved as a polynomial identity',
        'identity_exception': 'exact counterexample over Q(i), dimension 3',
        'uniqueness_product': 'printed left side refuted, intended central product verified',
        'semilinear_exponent': 'printed inverse exponent refuted over infinite F16(t)',
    },
    'scope': 'The identity exception and algebraic identity only; no general automorphism classification.',
}
target = root/'checks/johnson-rank-one-sage.json'
target.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print('ok johnson: rank-one identity and three admissible counterexamples')
