#import "main-defs.typ": *
#import "statements.typ": *

== Вычисления с двойными централизаторами
<sec:solazzi-symplectic-double-centralizers>

#definition(numbered: false)[
  Пусть $sigma in Sp(V)$. Назовем $sigma$ _плоским вращением_, если вычетное
  пространство $R$ преобразования $sigma$ — плоскость; $sigma$ называется
  _регулярным_ или _вполне вырожденным плоским вращением_ соответственно, если
  такова плоскость $R$.
]

#definition(numbered: false)[
  Для подпространства $W$ из $V$ положим
  $E(W)={sigma in Delta | R subset.eq W}$, где $R$ — вычетное пространство для
  $sigma$. Очевидно, $E(W)$ — подгруппа группы $Delta$.
]

#proposition[
  Пусть $n >= 2$, а $sigma$ — регулярное плоское вращение из $Delta$ с вычетным
  пространством $R$. Если $chi(F) != 2$, то предположим дополнительно, что
  $sigma^2 != 1_V$. Тогда $E(R) subset.eq C D C(sigma)$.
] <prop:solazzi-symplectic-regular-cdc-inclusion>

#proof[
  Так как $R^*$ — неподвижное пространство для $sigma$ и $R inter R^*=0$, то
  $sigma|_R != 1_R$. Если $sigma|_R=-1_R$, то $sigma^2=1_V$ по предложению
  @prop:solazzi-symplectic-involution-residual, что невозможно. Обозначая через
  $RL_2(R)$ группу скалярных преобразований из $GL_2(R)$, видим, что
  $sigma|_R in Sp_2(R)-RL_2(R)$. Из предложения
  @prop:solazzi-symplectic-plane-centralizer теперь следует, что централизатор
  $C_R (sigma|_R)$ преобразования $sigma|_R$ в $GL_2(R)$ абелев.

  #source(192)
  Пусть $sigma_1 in D C(sigma)$. Тогда $sigma_1 R=R$ и, значит,
  $ sigma_1|_R in D C(sigma)|_R subset.eq D C_R (sigma|_R)=1_R. $
  Итак, $sigma_1|_R=1_R$; пусть $P_1$ и $R_1$ — неподвижное и вычетное
  пространства для $sigma_1$. Тогда $R_1^*=P_1 supset R$, так что
  $R subset.eq R_1^*$. Любое преобразование $sigma_2$ из $E(R)$ имеет вычетное
  пространство $R_2 subset.eq R subset.eq R_1^*$. Следовательно, $sigma_2$ и
  $sigma_1$ перестановочны (см.~@prop:solazzi-symplectic-orthogonal-residuals).
  Таким образом, $E(R) subset.eq C D C(sigma)$, что и требовалось доказать.
]

#proposition[
  Пусть $n >= 6$ и $sigma in Delta$ — нетривиальная трансвекция или плоское
  вращение. Тогда $C D C(overline(sigma)) subset.eq overline(E(R))$.
] <prop:solazzi-symplectic-cdc-residual-inclusion>

#proof[
  Пусть $P$ — неподвижное пространство для $sigma$ и $L=F a$ — прямая из $P$, не
  лежащая в $rad P$. Так как $a in.not rad P$, то существует вектор $b in P$,
  такой, что $(a,b) != 0$. Поскольку $dim[(F a)^* inter P] >= 3$, то найдется
  вектор $t in (F a)^* inter P$, линейно независимый с $a$ и $b$. Положим
  $c=t+b$. Тогда $(a,c) != 0$ и $a,b,c$ — три линейно независимых вектора из
  $P$.

  Выберем нетривиальные трансвекции $tau_(a,lambda)$, $tau_(b,beta)$ и
  $tau_(c,alpha)$ из $Delta$ с собственными прямыми $F a$, $F b$, $F c$. Положим
  $f=tau_(a,lambda)tau_(b,beta)tau_(a,lambda)^(-1)tau_(b,beta)^(-1)
  =tau_(a,lambda) dot tau_(tau_(b,beta)(a),-lambda)$. Теперь
  $(a,tau_(b,beta)(a))=(a,a+beta(b, a)b) != 0$. Значит, $tau_(a,lambda)$ и
  $tau_(tau_(b,beta)(a),-lambda)$ не перестановочны ввиду
  @prop:solazzi-symplectic-transvections-commute, так что $f$ имеет вычетное
  пространство $F a+F(tau_(b,beta)(a))=F a+F(a+beta(b, a)b)=F a+F b$.
  Аналогично, если положить
  $g=tau_(a,lambda)tau_(c,alpha)tau_(a,lambda)^(-1)tau_(c,alpha)^(-1)$, то $g$
  имеет вычетное пространство $F a+F c$. Так как $sigma a=a$, $sigma b=b$,
  $sigma c=c$, то $tau_(a,lambda)$, $tau_(b,beta)$, $tau_(c,alpha)$ лежат в
  $C(sigma)$. Значит, $f$ и $g$ принадлежат $D C(sigma)$,
  $overline(f),overline(g) in overline(D C(sigma)) subset.eq D
  C(overline(sigma))$.

  Пусть теперь $overline(Sigma) in C D C(overline(sigma))$. Преобразование
  $overline(Sigma)$ должно быть перестановочным с $overline(f)$. Поэтому ввиду
  @prop:solazzi-symplectic-projective-commutation-lift и условия, что $n >= 6$,
  $Sigma$ и $f$ перестановочны. Значит, вычетное пространство преобразования $f$
  инвариантно относительно $Sigma$. Те же рассуждения доказывают
  $Sigma$-инвариантность вычетного пространства для $g$. Тогда
  $Sigma$-инвариантно и их пересечение, т.~е. прямая $F a$.

  Итак, все прямые из $P$, не лежащие в $rad P$, $Sigma$-инвариантны. Если
  $rad P=0$, то мы заключаем, что $Sigma$-инвариантны все прямые из $P$. Пусть
  $rad P != 0$, $K$ — прямая из $rad P$. Отметим прямую $L_0$ из $P$, не
  принадлежащую $rad P$. Тогда $K$ — единственная прямая из плоскости $K ⊕ L_0$,
  лежащая в $rad P$. Поскольку все остальные прямые $Sigma$-инвариантны, то
  $Sigma K subset.eq K ⊕ L_0$, но $Sigma$ — взаимно однозначное преобразование
  прямых, поэтому $Sigma K=K$. Таким образом, все прямые из $P$
  $Sigma$-инвариантны. Так как $dim P >= n-2$ и $n >= 6$, то $P$ не является
  #source(193)
  вполне вырожденным. Значит, $Sigma|_P=plus.minus 1_P$ и
  $Sigma in plus.minus E(R)$. Поэтому
  $overline(Sigma) in overline(plus.minus E(R))=overline(E(R))$, что и
  требовалось доказать.
]

#proposition[
  Пусть $n >= 6$ и $sigma in Delta$ имеет вычетное пространство $R$. Тогда
  группа $C D C(overline(sigma))$ абелева, если $sigma$ — трансвекция или вполне
  вырожденное плоское вращение, и $C D C(overline(sigma))$ неабелева, если
  $sigma$ — регулярное плоское вращение, такое, что $sigma^2 != 1_V$.
] <prop:solazzi-symplectic-cdc-abelian-characterization>

#proof[
  Если $sigma$ — трансвекция или вполне вырожденное плоское вращение, то ввиду
  @prop:solazzi-symplectic-cdc-residual-inclusion
  $C D C(overline(sigma)) subset.eq overline(E(R))$. Так как $R$ вполне
  вырождено, то из @prop:solazzi-symplectic-orthogonal-residuals следует, что
  $E(R)$ — абелева группа, откуда и $overline(E(R))$ абелева.

  Если $sigma$ — регулярное плоское вращение и $sigma^2 != 1_V$, то ввиду
  @prop:solazzi-symplectic-regular-cdc-inclusion $E(R) subset.eq C D C(sigma)$.
  Значит, $overline(E(R)) subset.eq overline(C D C(sigma))
  subset.eq C D overline(C(sigma))=C D C(overline(sigma))$, так как
  $overline(C(sigma))=C(overline(sigma))$, согласно
  @prop:solazzi-symplectic-projective-commutation-lift. По условию $R$
  регулярно, а $Delta$ имеет достаточно много трансвекций, поэтому в $E(R)$
  существуют неперестановочные трансвекции $tau_1$ и $tau_2$. Тогда в силу
  @prop:solazzi-symplectic-projective-commutation-lift $overline(tau)_1$ и
  $overline(tau)_2$ — неперестановочные проективные трансвекции в
  $overline(E(R)) subset.eq C D C(overline(sigma))$.
]

#proposition[
  Пусть $n >= 6$ и $chi(F) != 2$. Пусть $overline(sigma)$ — проективная
  трансвекция из $G$, а $Lambda$ — автоморфизм группы $G$. Тогда
  $Lambda overline(sigma)$ — также проективная трансвекция.
] <prop:solazzi-symplectic-transvection-preservation>

#proof[
  Можно считать, что $overline(sigma) != overline(1)_V$. Пусть $L$ — собственная
  прямая для $overline(sigma)$ и $Lambda overline(sigma)=overline(Sigma)$. Так
  как $overline(Sigma) != 1$, то выберем прямую $L_1$, удовлетворяющую условию
  $Sigma L_1 != L_1$. Пусть $tau_(a,lambda)$ — нетривиальная трансвекция в
  $Delta$ с собственной прямой $L_1=F a$. Ввиду
  @prop:solazzi-symplectic-projective-noncommutation $overline(Sigma)$ и
  $overline(tau)_(a,lambda)overline(Sigma)^(-1)overline(tau)_(a,lambda)^(-1)$
  не перестановочны. Положим $T=tau_(a,lambda)$, $h=Sigma T Sigma^(-1)T^(-1)$.
  Будучи произведением двух трансвекций с разными собственными прямыми,
  преобразование $h$ имеет в качестве вычетного пространства плоскость
  $R=Sigma L_1+L_1$. Пусть $Lambda overline(tau)=overline(T)$ и
  $f=sigma tau sigma^(-1)tau^(-1)$. Ясно, что $Lambda overline(f)=overline(h)$,
  а поскольку $overline(Sigma)$ и
  $overline(T)overline(Sigma)^(-1)overline(T)^(-1)$ не перестановочны, то таковы
  и $overline(sigma)$, $overline(tau)overline(sigma)^(-1)overline(tau)^(-1)$.
  Следовательно, не перестановочны и $sigma$, $tau sigma^(-1)tau^(-1)$.

  Мы утверждаем, что $f$ — регулярное плоское вращение, не являющееся
  инволюцией. В самом деле, $f=sigma(tau sigma^(-1)tau^(-1))$ — произведение
  двух неперестановочных трансвекций, поэтому $f$ — регулярное плоское вращение.
  Его вычетным пространством является $L+tau L$. Далее, поскольку
  $Sigma T Sigma^(-1)=tau_(Sigma a,lambda)$ и $T^(-1)=tau_(a,-lambda)$, то
  $R=F a+Sigma F a$ инвариантно относительно $Sigma T Sigma^(-1)$ и $T^(-1)$.
  Поэтому $Sigma T Sigma^(-1)$ и $T^(-1)$ одновременно индуцируют на $R$ либо
  $1_R$, либо нетривиальные трансвекции с различными
  #source(194)
  собственными прямыми (в зависимости от того, какое из соотношений
  $(a,Sigma a)=0$, $(a,Sigma a) != 0$ выполняется). В любом случае
  $h|_R != -1|_R$, так как $chi(F) != 2$. Ввиду
  @prop:solazzi-symplectic-involution-residual $h^2 != 1_V$ и, конечно,
  $h^2 != -1_V$. Следовательно, $overline(h)^2 != overline(1)_V$, откуда
  $overline(f)^2 != overline(1)_V$ и $f^2 != 1_V$. Таким образом, $f$ —
  регулярное плоское вращение, не являющееся инволюцией.

  Теперь мы утверждаем, что $h$ — также регулярное плоское вращение. Прежде
  всего в силу указанных выше свойств $f$ и ввиду
  @prop:solazzi-symplectic-cdc-abelian-characterization получаем, что группа
  $C D C(overline(f))$ неабелева, так что и $C D C(overline(h))$ неабелева. Если
  $L_1+Sigma L_1=R$ — вырожденная плоскость, то из
  @prop:solazzi-symplectic-cdc-abelian-characterization следует, что
  $C D C(overline(h))$ абелева, и это противоречит доказанному. Таким образом,
  мы видим, что $R$ — регулярная плоскость, значит, $h$ — регулярное плоское
  вращение.

  Покажем, что $Lambda overline(sigma)$ — проективная трансвекция. Так как $f$ —
  неинволютивное регулярное плоское вращение, а собственная прямая $L$ для
  $sigma$ содержится в вычетном пространстве $L+tau L$ для $f$, то из
  @prop:solazzi-symplectic-regular-cdc-inclusion следует, что
  $overline(sigma) in overline(C D C(f)) subset.eq C D overline(C(f))$. Но
  $overline(C(f))=C(overline(f))$, если принять во внимание, что $f$ — плоское
  вращение, а также @prop:solazzi-symplectic-projective-commutation-lift.
  Поэтому $overline(sigma) in C D C(overline(f))$ и, значит,
  $Lambda overline(sigma) in C D C(Lambda overline(f))$, откуда
  $overline(Sigma) in C D C(overline(h)) subset.eq overline(E(R))$ в силу
  @prop:solazzi-symplectic-cdc-residual-inclusion, где $R$ — регулярная
  плоскость, совпадающая с вычетным пространством для $h$. Поскольку
  $overline(Sigma) in overline(E(R))$, то можно считать $Sigma$ регулярным
  плоским вращением или трансвекцией. Но $C D C(overline(sigma))$ абелева ввиду
  @prop:solazzi-symplectic-cdc-abelian-characterization, поэтому
  $C D C(Lambda overline(sigma))=C D C(overline(Sigma))$ тоже абелева. Кроме
  того, $Sigma^2 != 1_V$, потому что $overline(sigma)^2 != overline(1)_V$ при
  $chi(F) != 2$. Следовательно, $Sigma$ не может быть регулярным плоским
  вращением, иначе из @prop:solazzi-symplectic-cdc-abelian-characterization
  следовала бы неабелевость $C D C(overline(Sigma))$. Таким образом, $Sigma$ —
  трансвекция, а $Lambda overline(sigma)=overline(Sigma)$ — проективная
  трансвекция, что и утверждалось.
]
