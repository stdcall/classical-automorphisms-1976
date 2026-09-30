"""Selected exact identities and counterexamples in Pomfret–McDonald and Yan.

The commutator convention here is [M,N]=M^-1 N^-1 M N; it reproduces
the first two rows of Pomfret's printed (6). Rational-function equalities
are identities, while the finite binomial checks only illustrate the
combinatorial formula. No classification theorem is proved here.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
from sage.all import QQ, ZZ, PolynomialRing, FreeAlgebra, matrix, identity_matrix, diagonal_matrix, block_matrix, binomial, version

root = Path(__file__).resolve().parents[2]
checks = []
def verify(name, assertion):
    assert assertion, name
    checks.append(name)

R = PolynomialRing(QQ, ['a', 'b', 'f']); a,b,f = R.gens()
K = R.fraction_field()
M = matrix(K, [[a,b,0],[0,a,0],[0,0,f]])
N = identity_matrix(K,3); N[1,2]=1
comm = M.inverse()*N.inverse()*M*N
expected = matrix(K,[[1,0,b*f/a**2],[0,1,1-f/a],[0,0,1]])
verify('pomfret-commutator-rational-function-identity', comm == expected)
printed = matrix(K,[[1,0,b*f/a**2],[0,1,1-f/a],[0,0,1/a**2]])
verify('pomfret-printed-bottom-right-fails', comm != printed)
T12=identity_matrix(QQ,3); T12[0,1]=1
T23=identity_matrix(QQ,3); T23[1,2]=2
T13=identity_matrix(QQ,3); T13[0,2]=2
verify('pomfret-commutator-target-13', T12.inverse()*T23.inverse()*T12*T23==T13)
rot=matrix(K,[[0,b],[-1/b,0]])
D=matrix(K,[[1,0],[0,-1]])
verify('signed-rotation-square-minus-one',rot**2==-identity_matrix(K,2))
verify('signed-rotation-involution-relation',(rot*D)**2==identity_matrix(K,2))

A=FreeAlgebra(QQ,4,names=('a','b','c','d')); aa,bb,cc,dd=A.gens()
U=matrix(A,[[aa,bb],[cc,dd]])
V=matrix(A,[[aa,-bb],[cc,-dd]])
verify('yan-noncommutative-square-top-left',(U**2)[0,0]==aa**2+bb*cc)
verify('yan-second-square-top-left',(V**2)[0,0]==aa**2-bb*cc)
verify('yan-square-bottom-right',(U**2)[1,1]==cc*bb+dd**2)
verify('yan-second-square-bottom-right',(V**2)[1,1]==-cc*bb+dd**2)
verify('yan-square-diagonal-sum-removes-products',
       all((U**2+V**2)[i,i]==2*z**2 for i,z in enumerate([aa,dd])))
old=matrix(K,[[0,-b],[b,0]])
verify('yan-printed-second-matrix-does-not-cover-rotations',old**2!=identity_matrix(K,2))
J23=matrix(QQ,[[1,0,0],[0,-1,0],[0,0,-1]])
verify('yan-correctly-parenthesized-square',(T12*J23)**2==identity_matrix(QQ,3))
verify('yan-unparenthesized-expression-fails',T12*J23**2!=identity_matrix(QQ,3))
verify('yan-zero-common-multiple-is-vacuous',ZZ(2)*0==ZZ(3)*0)
for ell in range(1,8):
    n=4*ell+1
    verify(f'yan-binomial-ell-{ell}',binomial(n,2*ell+2)==binomial(n,2*ell-1))
    verify(f'yan-distinct-adjacent-family-sizes-{ell}',binomial(n,2*ell+2)!=binomial(n,2*ell))

# Generic sandwich sign and simultaneous normalization of adjacent rotations.
S=PolynomialRing(QQ,['lambda','b','b1']); lam,bb,bb1=S.gens(); L=S.fraction_field()
T=identity_matrix(L,3); T[0,2]=lam
W=matrix(L,[[-1,0,0],[0,-1,0],[0,0,1]])
verify('yan-same-sign-sandwich-polynomial-identity',T*W*T==W)
verify('yan-printed-opposite-sign-sandwich-fails',T.inverse()*W*T!=W)
U12=identity_matrix(L,4); U12[0,0]=U12[1,1]=0; U12[0,1]=bb; U12[1,0]=-1/bb
U23=identity_matrix(L,4); U23[1,1]=U23[2,2]=0; U23[1,2]=bb1; U23[2,1]=-1/bb1
D=diagonal_matrix(L,[1/(bb1*bb),1/bb1,1,1])
oldD=diagonal_matrix(L,[1/(bb1*bb),1/bb,1,1])
verify('yan-two-rotation-normalization-rational-identity',
       (D*U12*D.inverse())[0,1]==1 and (D*U23*D.inverse())[1,2]==1)
verify('yan-printed-normalization-fails',
       (oldD*U12*oldD.inverse())[0,1]!=1 and (oldD*U23*oldD.inverse())[1,2]!=1)
# The diagonal duplication is a unital embedding, not a surjective isomorphism.
units=[]
for i in range(2):
    for j in range(2):
        E=matrix(QQ,2,2,0); E[i,j]=1; units.append(E)
duplicate=lambda E:block_matrix(QQ,[[E,matrix(QQ,2,2,0)],[matrix(QQ,2,2,0),E]])
verify('yan-diagonal-duplication-preserves-unit',duplicate(identity_matrix(QQ,2))==identity_matrix(QQ,4))
verify('yan-diagonal-duplication-preserves-multiplication',
       all(duplicate(E*F)==duplicate(E)*duplicate(F) for E in units for F in units))
verify('yan-diagonal-duplication-injective',matrix(QQ,[duplicate(E).list() for E in units]).rank()==4)
verify('yan-diagonal-duplication-not-surjective',len(units)<16)

files=['59-pomfret-automorphisms.typ','82-yan-inner-isomorphisms.typ',
       '83-yan-involutions.typ','84-yan-elementary-images.typ','86-yan-strengthening.typ']
report={
 'checked_at':datetime.now(timezone.utc).isoformat(),'sage':version(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'text_sha256':{name:hashlib.sha256((root/'content'/name).read_bytes()).hexdigest() for name in files},
 'passages':['passage:pomfret-permutation-inverse-sign','passage:pomfret-commutator-target','eq:pomfret-transvection-commutator-image','lem:yan-two-by-two-squares','passage:yan-elementary-involution-square','cond:yan-odd-dimension','th:yan-matrix-ring-isomorphisms','passage:yan-sandwich-sign','passage:yan-rotation-normalization'],
 'scope':__doc__.strip(),'checks':checks,'passed':True}
(root/'checks/pomfret-yan-matrices-sage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print('ok pomfret-yan-matrices:',len(checks),'checks')
