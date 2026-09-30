"""Solazzi, printed pp.190,205,207,209,212: exact boundary cases.

The unitary model is Q(i)^6 with three hyperbolic planes and nontrivial
conjugation: it meets the infinite-field and Witt-index hypotheses.
These witnesses refute omitted nonidentity/containment conditions and
the nonorthogonal choice in Lemma 2. They do not prove the automorphism
classification or all corrected general statements.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
from sage.all import QQ, NumberField, PolynomialRing, block_diagonal_matrix
from sage.all import identity_matrix, matrix, vector, version

checks = 0
def verify(value):
    global checks
    assert value
    checks += 1

T = PolynomialRing(QQ, 't')
t = T.gen()
F = NumberField(t*t+1, 'i')
i = F.gen()
conjugate = F.hom([-i], F)
J = matrix(F, [[0,1],[1,0]])
H = block_diagonal_matrix([J,J,J])
I = identity_matrix(F, 6)
e = [vector(F, [int(k==j) for k in range(6)]) for j in range(6)]
def star(M):
    return M.transpose().apply_map(conjugate)
def q(x,y):
    return (x.row()*H*y.apply_map(conjugate).column())[0,0]
def tau(a,lam):
    row = (H*a.apply_map(conjugate).column()).transpose()
    return I+lam*a.column()*row
def unitary(M):
    return star(M)*H*M==H

verify(H.det()!=0)
verify(all(q(a,a)==0 for a in e))
verify(all(q(e[2*j],e[2*j+1])==1 for j in range(3)))
a,b,c=e[0],e[2],e[1]
A,B,C=tau(a,i),tau(b,i),tau(c,i)
verify(all(unitary(M) and M.det()==1 and (M-I).rank()==1 for M in (A,B,C)))
verify(i+conjugate(i)==0)

# §1.2: tau(a,0)=tau(b,0), but independent nonzero a,b are not proportional.
verify(tau(a,0)==tau(b,0)==I)
verify(matrix(F,[a,b]).rank()==2)
# §1.3: identity times a transvection is a transvection even when its
# arbitrarily assigned proper line differs from that of the second factor.
verify((tau(a,0)*B-I).rank()==1)
# §1.4: a unitary permutation moves Fa, but commutes with tau(a,0).
perm=[2,3,0,1,4,5]
S=matrix(F,6,6,lambda r,s:int(r==perm[s]))
verify(unitary(S) and S*I==I*S)
verify(matrix(F,[a,S*a]).rank()==2)
# §1.5: identity commutes with tau(c,i), although Fa and Fc are not orthogonal.
verify(q(a,c)==1 and I*C==C*I)
# Two nontrivial orthogonal transvections commute; hyperbolic ones do not.
verify(A*B==B*A and A*C!=C*A)

# §1.10: P=<e1,e2,e3,e4> is regular, dim(P)=n-2, rad(P)=0.
# The isotropic line Fe5 lies in V and outside rad(P), but not in P;
# it cannot belong to any plane contained in P.
P=F**6
P=P.subspace(e[:4])
verify(P.dimension()==4 and H[:4,:4].det()!=0)
verify(q(e[4],e[4])==0 and e[4] not in P)

# §2.2: Sigma=iI is central, so lies in every double centralizer in U(V).
# For sigma=A, its restriction to its fixed space P is I, not iI.
fixed=(A-I).right_kernel()
Sigma=i*I
verify(unitary(Sigma) and Sigma*A==A*Sigma)
verify(all(A*v==v and Sigma*v==i*v for v in fixed.basis()))
verify(any(A*v!=i*v for v in fixed.basis()))

# Lemma 2: choosing (L2,L1)!=0 gives a regular hyperbolic plane,
# whereas choosing distinct orthogonal isotropic lines gives a totally
# degenerate plane, as the following paragraph requires.
hyperbolic=matrix(F,[[q(x,y) for y in (a,c)] for x in (a,c)])
degenerate=matrix(F,[[q(x,y) for y in (a,b)] for x in (a,b)])
verify(hyperbolic.det()!=0)
verify(degenerate==matrix(F,2,2) and matrix(F,[a,b]).rank()==2)

# Symplectic §1, p.190: residual space is Fa only for nonzero a,lambda.
Js=matrix(QQ,[[0,1],[-1,0]])
asym=vector(QQ,[1,0])
def symplectic_tau(lam):
    return identity_matrix(QQ,2)+lam*asym.column()*(asym.row()*Js)
verify((symplectic_tau(0)-identity_matrix(QQ,2)).rank()==0)
verify((symplectic_tau(1)-identity_matrix(QQ,2)).column_space()
       ==(QQ**2).subspace([asym]))

root=Path(__file__).resolve().parents[2]
names=('63-solazzi-symplectic-preliminaries.typ',
       '70-solazzi-unitary-preliminaries.typ',
       '71-solazzi-unitary-double-centralizers.typ',
       '72-solazzi-unitary-automorphisms.typ')
report={
 'checked_at':datetime.now(timezone.utc).isoformat(), 'sage':version(),
 'checks':checks,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'text_sha256':{n:hashlib.sha256((root/'content'/n).read_bytes()).hexdigest() for n in names},
 'passages':['prop:solazzi-unitary-transvection-equality',
             'prop:solazzi-unitary-transvection-product',
             'prop:solazzi-unitary-transvection-centralizer',
             'prop:solazzi-unitary-transvections-commute',
             'prop:solazzi-unitary-two-hyperbolic-planes',
             'prop:solazzi-unitary-cdc-residual-inclusion',
             'lem:solazzi-unitary-transvection-preservation'],
 'literature':'R. Solazzi, On the isomorphisms between certain congruence groups, II, '
              'Canad. J. Math. 25 (1973), 1006–1014, proof of 1.9.',
 'scope':'Exact counterexamples and linear algebra in Q(i)^6, Witt index 3; '
          'one 2-dimensional rational symplectic model; no classification proof.'
}
(root/'checks/solazzi-transvections-sage.json').write_text(
 json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(f'ok solazzi-transvections: {checks} checks')
