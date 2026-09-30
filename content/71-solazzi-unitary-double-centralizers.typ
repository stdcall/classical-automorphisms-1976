#import "main-defs.typ": *
#import "statements.typ": *

== Результаты о двойных централизаторах
<sec:solazzi-unitary-double-centralizers>

#numbered-paragraph[
  #source(206)
  Пусть подгруппа $S$ группы $U_n (V)$ имеет достаточно много трансвекций. Пусть
  $sigma$ — преобразование из $S inter SL_n (V)$ с неподвижным пространством $P$
  и вычетным пространством $R$, причем $R subset.not P$ и $sigma$ не инволюция.
  Предположим, что $n >= 2$ и $dim R=2$. Тогда $E(R) subset.eq C D C(sigma)$.
] <prop:solazzi-unitary-regular-cdc-inclusion>

#proof[
  Так как $R subset.not P$, то $sigma|_R != 1_R$. Если $sigma|_R in RL_2(R)$, то
  ввиду того, что $1=det sigma=det sigma|_R$, получаем $sigma|_R=-1_R$. Но
  $sigma$ не инволюция. Таким образом, $sigma|_R in GL_2(R)-RL_2(R)$. Ввиду
  @prop:solazzi-unitary-plane-centralizer группа $C_R (sigma|_R)$ абелева, где
  $C_R (sigma|_R)$ обозначает централизатор преобразования $sigma|_R$ в группе
  $GL_2(R)$. Если $sigma_1 in D C(sigma)$, то $sigma_1(R)=R$ и
  $ sigma_1|_R in D C(sigma)|_R subset.eq D C_R (sigma|_R)=1_R. $
  Значит, $sigma_1|_R=1_R$ и $R_1^*=P_1 supset.eq R$. Если $sigma_2 in E(R)$, то
  $R_2 subset.eq R subset.eq R_1^*$. В силу 1.5 из
  @bib:solazzi-unitary-OMeara1969 $sigma_1$ и $sigma_2$ перестановочны, т.~е.
  $E(R) subset.eq C D C(sigma)$.
]

#numbered-paragraph[
  Пусть $nu(V) >= 3$ и преобразование $sigma in Delta$ таково, что $dim R <= 2$.
  Тогда $C D C(overline(sigma)) subset.eq overline(E(R))$.
] <prop:solazzi-unitary-cdc-residual-inclusion>

#proof[
  Из условия следует, что $n >= 6$. Возьмем изотропную прямую $L=F a$ из $P$, не
  лежащую в $rad P$. В силу @prop:solazzi-unitary-two-hyperbolic-planes в $P$
  найдутся две различные гиперболические плоскости $F a+F b$ и $F a+F c$, где
  $b$ и $c$ — изотропные векторы. Пусть $tau_a,tau_b,tau_c$ — нетривиальные
  трансвекции из $Delta$ с собственными прямыми $F a,F b,F c$ соответственно,
  $f=[tau_a,tau_b]$ и $g=[tau_a,tau_c]$. Вычетными пространствами для $f$ и $g$
  являются $F a+F b$ и $F a+F c$ соответственно. Так как $sigma$ оставляет
  $a,b,c$ на месте, то $f$ и $g$ принадлежат $D C(sigma)$, откуда
  $overline(f),overline(g) in overline(D C(sigma)) subset.eq D
  C(overline(sigma))$.

  Если $overline(Sigma) in C D C(overline(sigma))$, то $overline(Sigma)$ и
  $overline(f)$ перестановочны. Так как $n >= 6$, то, согласно
  @prop:solazzi-unitary-projective-commutation-lift, $Sigma$ и $f$ тоже
  перестановочны. Следовательно, вычетное пространство преобразования $f$
  $Sigma$-инвариантно. То же верно и для вычетного пространства преобразования
  $g$, поэтому $Sigma$-инвариантно и пересечение этих вычетных пространств —
  прямая $F a$. Таким образом, $Sigma$ оставляет на месте все изотропные прямые
  пространства $P$, не лежащие в $rad P$. Допустим, что $rad P != 0$,
  $P=rad P perp W$ и прямая $K$ принадлежит $rad P$. Согласно
  @prop:solazzi-unitary-isotropic-complement, подпространство $W$ изотропно и
  регулярно. Пусть $L_0$ — изотропная прямая из $W$. Все прямые из $K ⊕ L_0$
  изотропны и, за исключением $K$, не лежат в $rad P$. По предыдущему
  преобразование $Sigma$ оставляет на месте все прямые из $K ⊕ L_0$, кроме, быть
  может, прямой $K$. Отсюда
  #source(207)
  $Sigma K=K$. Таким образом, $Sigma$ оставляет на месте все изотропные прямые
  пространства $P$.

  Поскольку $W$ изотропно и регулярно, то ввиду
  @prop:solazzi-unitary-isotropic-line-rigidity
  $ Sigma|_W=lambda, quad "где" lambda in RL(V) inter U(V). $
  Заметим, что $Sigma|_(rad P)=lambda$. В этом нетрудно убедиться, рассматривая
  действие $Sigma$ на $K ⊕ L_0$. Следовательно, $Sigma|_P=lambda dot 1_P$,
  $Sigma in lambda dot E(R)$ и
  $overline(Sigma) in overline(lambda dot E(R))=overline(E(R))$, что и
  утверждалось.
]

#numbered-paragraph[
  Пусть $nu(V) >= 3$, $sigma in Delta$. Если $sigma$ — трансвекция или вполне
  вырожденное плоское вращение, или квазисимметрия, то группа
  $C D C(overline(sigma))$ абелева. Если $sigma$ — гиперболическое вращение и
  $sigma^2 != 1_V$, то группа $C D C(overline(sigma))$ неабелева.
] <prop:solazzi-unitary-cdc-abelian-characterization>

#proof[
  Если $sigma$ — трансвекция, вполне вырожденное плоское вращение или
  квазисимметрия, то из @prop:solazzi-unitary-cdc-residual-inclusion следует,
  что $C D C(overline(sigma)) subset.eq overline(E(R))$. Так как либо $dim R=1$,
  либо $R$ — вполне вырожденная плоскость, то в силу 1.4 из
  @bib:solazzi-unitary-OMeara1969 группа $overline(E(R))$ абелева.

  Пусть $sigma$ — гиперболическое вращение, причем $sigma^2 != 1_V$. Согласно
  @prop:solazzi-unitary-regular-cdc-inclusion, $E(R) subset.eq C D C(sigma)$,
  откуда $overline(E(R)) subset.eq overline(C D C(sigma)) subset.eq C D
  C(overline(sigma))$, поскольку, ввиду
  @prop:solazzi-unitary-projective-commutation-lift,
  $overline(C(sigma))=C(overline(sigma))$. Так как $R$ — гиперболическая
  плоскость, а $G$ содержит достаточно много трансвекций, то нетрудно найти две
  неперестановочные трансвекции, принадлежащие $overline(E(R))$.
]
