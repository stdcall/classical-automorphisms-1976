"""Limited exact checks of O'Meara 1.6.2, 4.4.1(1), 4.5.1(5), and diagrams.

This checks the printed rank-one formulas and selected finite-field specializations,
not generation, simplicity, projective geometry, or the isomorphism theorems.
"""
from pathlib import Path
from copy import copy
import hashlib, json
from datetime import datetime, timezone
from sage.all import matrix, identity_matrix, GF, ZZ, QQ, PolynomialRing, vector, version, QuadraticField

root = Path(__file__).resolve().parents[2]
checks = []
def transvection(field, a, rho):
    return identity_matrix(field, 2) + matrix(field, 2, 1, a) * matrix(field, 1, 2, rho)

for field in (ZZ, GF(2), GF(3), GF(5), GF(7)):
    first = transvection(field, [-2, 0], [0, 1])
    second = transvection(field, [0, 2], [1, 0])
    left = first * second
    right = -transvection(field, [1, -1], [2, 2])
    assert left == right
    if field == GF(2):
        assert first == second == identity_matrix(field, 2)
    else:
        assert first != identity_matrix(field, 2) and second != identity_matrix(field, 2)
    checks.append({'name': '1.6.2-example', 'ring': str(field), 'matrix': [str(x) for x in left.list()], 'passed': True})

# A polynomial rank-one specialization a=(u,v), rho=(-v,u) gives rho*a=0.
R = PolynomialRing(QQ, ['u', 'v'])
u,v = R.gens()
a = matrix(R, 2, 1, [u,v]); rho = matrix(R, 1, 2, [-v,u])
N = a*rho; I = identity_matrix(R, 2)
assert rho*a == matrix(R,1,1,[0]) and N*N == 0
assert (I+N)*(I-N) == I
assert (I-N).transpose() == I-rho.transpose()*a.transpose()
assert (I+N).transpose() == I+rho.transpose()*a.transpose()
checks.append({'name':'4.5.1-rank-one-polynomial-identity', 'ring':str(R), 'passed':True})
for field in (QQ, GF(2), GF(3), GF(5)):
    T = transvection(field,[1,0],[0,1])
    minus = transvection(field,[0,1],[-1,0])
    plus = transvection(field,[0,1],[1,0])
    assert T.inverse().transpose() == minus
    assert (minus == plus) == (field.characteristic() == 2)
    checks.append({'name':'4.5.1-contragredient-sign', 'ring':str(field), 'passed':True})

# Diagram model V=Q^3, H=ker rho, a=e1, rho=e3*.
a3 = vector(QQ,[1,0,0]); rho3 = vector(QQ,[0,0,1]); x = vector(QQ,[0,0,1])
T3 = identity_matrix(QQ,3)+a3.column()*rho3.row()
y = T3*x
assert y-x == a3 and rho3.dot_product(y-x) == 0
assert T3.det() == 1 and (T3-identity_matrix(QQ,3)).rank() == 1
projection = matrix(QQ, [[-QQ(3)/5,QQ(6)/5,0],[-QQ(17)/20,-QQ(3)/10,QQ(6)/5]])
assert projection*y - projection*x == projection*(y-x)
# Dilatation fixes H pointwise and has residual line Qe3 transverse to H.
D3 = matrix(QQ, [[1,0,0],[0,1,0],[0,0,2]])
assert (D3-identity_matrix(QQ,3)).rank()==1
assert D3*a3==a3 and D3*vector(QQ,[0,1,0])==vector(QQ,[0,1,0])
checks.append({'name':'diagram-models-and-projection', 'passed':True})
# Chapter 2 schematic vectors are also derived from exact linear maps.
S6=identity_matrix(QQ,6); S6[0,4]=1; S6[1,5]=1
b6=vector(QQ,[0,0,0,0,1,0]); d6=S6*b6-b6
assert d6==vector(QQ,[1,0,0,0,0,0])
assert (S6-identity_matrix(QQ,6)).rank()==2
assert all(S6.column(i)==identity_matrix(QQ,6).column(i) for i in range(4))
# H is x5=0: both b and sigma*b are outside, while delta is in H.
assert b6[4]!=0 and (S6*b6)[4]!=0 and d6[4]==0
Q6=matrix(QQ,[[-QQ(11)/20,QQ(7)/10,0,0,0,0],
 [-QQ(13)/20,-QQ(1)/10,0,0,QQ(29)/20,0]])
assert Q6*(S6*b6)-Q6*b6==Q6*d6
S=matrix(QQ,[[1,0,0],[0,2,0],[0,0,3]])
b=vector(QQ,[0,1,1]); d=S*b-b
assert d==vector(QQ,[0,1,2])
Q=matrix(QQ,[[QQ(9)/10,QQ(23)/10,-QQ(8)/5],[-QQ(3)/5,QQ(11)/5,-QQ(7)/5]])
assert Q*(S*b)-Q*b==Q*d
assert matrix(QQ,[vector(QQ,[1,0,0]),d,b]).rank()==3
checks.append({'name':'chapter-two-diagram-models-and-projections','passed':True})
# The induction diagram 5.2.4 uses a genuine three-dimensional residue.
I4=identity_matrix(QQ,4)
t13=copy(I4); t13[0,2]=1
t21=copy(I4); t21[1,0]=1
t32=copy(I4); t32[2,1]=1
s2=t32*t21
s0=t13*s2
e=I4.columns()
R0=matrix(QQ,[e[0],e[1],e[2]]).row_space()
R1=matrix(QQ,[e[0]]).row_space()
R2=matrix(QQ,[e[1],e[2]]).row_space()
P0=matrix(QQ,[e[3]]).row_space()
P1=matrix(QQ,[e[0],e[1],e[3]]).row_space()
P2=matrix(QQ,[e[2],e[3]]).row_space()
assert R1+R2==R0 and R1.intersection(R2).dimension()==0
assert P1.intersection(P2)==P0 and P1+P2==QQ**4
assert (t13-I4).column_space()==R1 and (t13-I4).right_kernel()==P1
assert (s2-I4).column_space()==R2 and (s2-I4).right_kernel()==P2
assert (s0-I4).column_space()==R0 and (s0-I4).right_kernel()==P0
assert s0.det()==s2.det()==1
checks.append({'name':'5.2.4-inductive-subspaces-and-transvection-product','ring':'QQ','passed':True})
projection=matrix(QQ,[[-QQ(7)/10,QQ(1)/10,-QQ(8)/5,2],
                      [-QQ(3)/5,-QQ(9)/10,QQ(1)/10,QQ(3)/5]])
M=projection.matrix_from_columns([0,1,2]); P=projection.matrix_from_columns([0,1,3])
common=projection.matrix_from_columns([0,1])
cm=M*M.transpose(); cp=P*P.transpose(); cc=common*common.transpose()
assert all((c-cc).is_positive_semidefinite() for c in (cm,cp))
k=projection.column(3)
assert k.dot_product(cm.inverse()*k)>1
checks.append({'name':'5.3.7-common-origin-projected-balls','ring':'QQ','passed':True})
files=['27-omeara-projective-transvections.typ','40-omeara-geometric-isomorphisms.typ',
       '41-omeara-contragredient.typ','44-omeara-rich-transvections.typ',
       'diagrams/omeara-transvections.typ','diagrams/omeara-rich-transvections.typ']
E=QuadraticField(-1,'i'); ii=E.gen()
g=ii*identity_matrix(E,2)
# The semilinear map is complex conjugation on Q(i)^2. Conjugation by
# iI sends it to -conjugation, though iI commutes with every linear map.
v=vector(E,[1,0])
conjugate=lambda v: v.apply_map(lambda z:z.conjugate())
assert g*conjugate(g.inverse()*v)==-v and conjugate(v)==v
assert g*matrix(E,[[1,1],[0,1]])*g.inverse()==matrix(E,[[1,1],[0,1]])
checks.append({'name':'4.4.1-restriction-to-linear-group','ring':str(E),'passed':True})

report={'checked_at':datetime.now(timezone.utc).isoformat(),'sage':version(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'text_sha256':{f:hashlib.sha256((root/'content'/f).read_bytes()).hexdigest() for f in files},
 'passages':['exm:omeara-projective-transvection-dimension-two','passage:omeara-contragredient-transvection-sign','prop:omeara-geometric-isomorphism-equality'],
 'scope':'Selected rank-one identities and exact diagram data only; no proof of general theorems.',
 'checks':checks, 'passed':True}
(root/'checks/omeara-transvections-sage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
