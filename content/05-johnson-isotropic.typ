#import "main-defs.typ": *
#import "statements.typ": *

== $S_x$ в случае изотропного вектора $x$ <sec:johnson-isotropic>

#claim(family: "th")[
  *Теорема.* Пусть $x$ — изотропный вектор из $V$. Тогда $Lambda S_x = S_y$ для
  некоторого изотропного вектора $y$ из $V$.
] <th:johnson-isotropic-image>

#proof[
  Пусть $V = (E z + E x) perp U$, где $E z + E x approx.eq mat(0, 1; 1, 0)$ и
  $(E x)^perp = E x perp U$. Пусть также $U = E u_1 perp dots perp E u_(n-2)$,
  т.~е. ${u_1, dots, u_(n-2)}$ — ортогональная база пространства $U$. Возьмем
  $sigma in S_x - Z(Delta)$ и положим $sigma' = Lambda sigma$. Поскольку $E x$
  ортогонально $U$, то $S_u subset.eq C(sigma)$ для всех $u in U$. В частности,
  $S_(u_i) subset.eq C(sigma)$, $i = 1, 2, dots, n - 2$. По теореме
  @th:johnson-anisotropic-image существуют анизотропные векторы
  $u'_1, dots, u'_(n-2)$, такие, что $Lambda(S_(u_i)) = S_(u'_i)$. Очевидно,
  $S_(u_i) != S_(u_j)$ при $i != j$ и $S_(u_i) subset.eq C(S_(u_j))$,
  следовательно, $S_(u'_i) != S_(u'_j)$ и $S_(u'_i) subset.eq C(S_(u'_j))$. Это
  означает, что векторы $u'_1, dots, u'_(n-2)$ попарно ортогональны и потому
  линейно независимы. Пусть $U' = E u'_1 perp dots perp E u'_(n-2)$. Конечно,
  $S_(u'_i) subset.eq C(sigma')$ при $i = 1, 2, dots, n - 2$, так как
  $S_(u_i) subset.eq C(sigma)$. В частности, $sigma' u'_i in E u'_i$ для каждого
  $i$.

  При $n = 3$ ограничение $sigma'$ на $U'$ скалярно. Пусть теперь $n > 3$.
  <passage:johnson-isotropic-minimal-dimension>
  Выберем вектор $v = a_1 u_1 + dots + a_(n-2) u_(n-2)$, где все $a_i$
  ненулевые, $Q(v) != 0$. Снова $S_v subset.eq C(sigma)$. В то же время
  $S_v subset.not C(S_(u_i))$ при $i = 1, 2, dots, n - 2$. Положим
  $S_(v') = Lambda S_v$, тогда
  #source(23)
  $S_(v') subset.eq C(sigma')$, так что $sigma' v' in E v'$. Пусть
  $sigma' v' = xi v'$ и $sigma' u'_i = xi_i u'_i$. Ясно, что $q(v', u'_i) != 0$,
  так как $S_(v') subset.not C(S_(u'_i))$. Отсюда сразу вытекает, что
  $xi = xi_i$ для $i = 1, 2, dots, n - 2$ и $sigma'|_(U') in Z(U')$.

  Пусть $W$ — регулярное подпространство с ортогональной базой
  $x + u_1, u_2, dots, u_(n-2)$ и $V = (E z' + E x) perp W$. Заменив в
  предыдущем рассуждении $U'$ на подпространство $W'$, порожденное векторами
  $(x + u_1)', u'_2, dots, u'_(n-2)$, получим, что $sigma'|_(W') in Z(W')$.
  Теперь $(x + u_1)'$ и $u'_1$ ортогональны векторам $u'_2, dots, u'_(n-2)$ и
  линейно независимы, потому что из $S_(x+u_1) != S_(u_1)$ следует, что
  $S_((x+u_1)') != S_(u'_1)$. Значит, $dim(U' + W') = n - 1$. Так как
  $S_(x+u_1) subset.not C(S_(u_1))$, то $q((x + u_1)', u'_1) != 0$ и
  $sigma'|_(U'+W') in R(U' + W')$.

  Теперь воспользуемся тем, что $N C C(sigma) supset C(sigma)$. Имеем
  $N C C(sigma') supset C(sigma')$, поэтому $W' + U'$ нерегулярно.
  Действительно, в противном случае было бы $V = E y perp (W' + U')$, и
  $sigma' in S_y - Z(Delta)$, причем $y$ анизотропен. Но тогда, как мы уже
  видели в §~@sec:johnson-quasisymmetries, $N C C(sigma') = C(sigma')$.

  Поскольку $W' + U'$ вырождено, можно записать
  $E y = (W' + U')^perp subset.eq W' + U'$. Следовательно,
  $sigma'|_((E y)^perp) in R(E y^perp)$ и $sigma' in S_y - Z(Delta)$. Отсюда
  $ Lambda S_x = Lambda C C(sigma) = C C(sigma') = S_y, $
  что и требовалось доказать.
]
