"""Selected exact projective-coordinate and ring counterexamples.

The general fundamental theorem is not proved here. The first check uses a
linear projectivity over Q(a), with the normalized image basis of the paper.
For the UFD counterexample, a rational scalar with relatively prime numerator
and denominator carrying (x,y,0) into Q[x,y]^3 has constant denominator:
that denominator must divide both x and y. Thus every polynomial
representative is a polynomial multiple of (x,y,0), and its coordinate ideal
is contained in the proper ideal (x,y); no representative is unimodular.
Over a PID, divide a cleared vector by the generator of its coordinate ideal;
Bezout then supplies a unimodular representative. The failure of reverse
incidence requires a nonzero nonunit, so the concluding extension excludes
fields. These arguments, not an enumeration, justify the restrictions.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
from sage.all import QQ, PolynomialRing, matrix, vector, version

root=Path(__file__).resolve().parents[2]
checks=[]
def verify(name, condition):
    assert condition, name
    checks.append(name)

R=PolynomialRing(QQ,'a'); a=R.gen(); F=R.fraction_field()
alpha=matrix(F,[[1,0,0],[0,2,0],[0,0,3]])
e=vector(F,[0,a,1]); f=alpha*e
verify('normalized-base-image',alpha*vector(F,[1,1,0])==vector(F,[1,2,0]))
verify('corrected-coordinate-equation',f==vector(F,[0,2*a,3]))
verify('printed-missing-alpha-fails',matrix(F,[e,f]).rank()==2)

A=PolynomialRing(QQ,['x','y']); x,y=A.gens(); B=A.fraction_field()
I=A.ideal([x,y])
verify('polynomial-ring-UFD',A.is_integral_domain() and x.gcd(y)==1)
verify('coordinate-ideal-proper',I.groebner_basis()==[x,y] and not A.one() in I)
verify('origin-annihilates-coordinate-ideal',x(0,0)==y(0,0)==0)
verify('target-is-a-valid-fraction-field-point',vector(B,[x,y,0])!=0)

T=PolynomialRing(QQ,'t'); t=T.gen(); K=T.fraction_field()
v=vector(T,[t**3,t**2+t,0]); d=v[0].gcd(v[1]); primitive=v.apply_map(lambda z:T(z/d))
verify('PID-coordinate-ideal-normalizes',primitive[0].gcd(primitive[1])==1)
verify('PID-projective-point-unchanged',matrix(K,[v,primitive]).rank()==1)
p2=vector(T,[t,1,0]); p3=vector(T,[0,1,0]); p1=vector(T,[1,0,0])
verify('all-three-vectors-unimodular',p2[0].gcd(p2[1])==1 and p3[1]==1 and p1[0]==1)
verify('fraction-field-incidence',K(1/t)*vector(K,p2)-K(1/t)*vector(K,p3)==vector(K,p1))
verify('reverse-incidence-needs-nonunit-inverse',not t.is_unit() and K(1/t).denominator()==t)

files=['54-ojanguren-theorem.typ','55-ojanguren-example.typ']
report={
 'checked_at':datetime.now(timezone.utc).isoformat(),'sage':version(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'text_sha256':{f:hashlib.sha256((root/'content'/f).read_bytes()).hexdigest() for f in files},
 'passages':['eq:ojanguren-two-coordinate-map','prop:ojanguren-collinearity-counterexample','passage:ojanguren-principal-domain-extension'],
 'scope':'Exact coordinate identity and ring counterexamples; no proof of the general fundamental theorem.',
 'checks':checks,'passed':True}
(root/'checks/ojanguren-projective-sage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print('ok ojanguren-projective:',len(checks),'checks')
