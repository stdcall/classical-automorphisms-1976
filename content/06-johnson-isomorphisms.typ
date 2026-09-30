#import "main-defs.typ": *
#import "statements.typ": *

== Изоморфизмы $Phi_g$ и $P_chi$ <sec:johnson-isomorphisms>

В этом параграфе $g$ будет обозначать полулинейный изоморфизм пространства $V$
на себя, связанный с автоморфизмом $mu$ основного поля $E$. Будем говорить, что
$g$ _сохраняет ортогональность_, если из $q(x, y) = 0$ следует, что
$q(g x, g y) = 0$ для всех $x, y in V$.
#idx("изоморфизм, сохраняющий ортогональность")
Хорошо известно (см., например, @bib:johnson-Dieudonne1963, стр.~33–34), что $g$
сохраняет ортогональность тогда и только тогда, когда существует такой элемент
$alpha != 0$ из $E$, что $q(g x, g y) = alpha q(x, y)^mu$ для всех $x, y$ из
$V$. Таким образом, если $g$ сохраняет ортогональность, то и $g^(-1)$ сохраняет
ортогональность; $q(x, y) = 0$ в том и только том случае, когда
$q(g x, g y) = 0$ и $Q(g x) = alpha Q(x)^mu$ для всех $x$ из $V$.

Определим теперь автоморфизм $Phi_g: GL_n (V) arrow GL_n (V)$, полагая
$Phi_g (sigma) = g sigma g^(-1)$. Из определения непосредственно следует, что
$
  Phi_(g_1) compose Phi_(g_2) = Phi_(g_1 g_2),
  quad Phi_g^(-1) = Phi_(g^(-1))
$
и
$ det(Phi_g (sigma)) = (det sigma)^mu. $

#source(24)
#claim[
  Если $sigma$ и $Phi_g (sigma)$ принадлежат $U_n (V)$ и $sigma$ имеет
  собственное пространство $P$ и вычетное пространство $R$, то $Phi_g (sigma)$
  имеет собственное пространство $g P$ и вычетное пространство $g R$.
] <prop:johnson-semilinear-eigenspaces>

Доказательство очевидно.

#claim[
  Если для любых анизотропных векторов $x, y$ из $V$ равенство $q(x, y) = 0$
  влечет за собой равенство $q(g x, g y) = 0$, то $g$ сохраняет ортогональность.
] <prop:johnson-anisotropic-orthogonality>

#proof[
  См. утверждение 3.2 из работы О'Миры @bib:johnson-OMeara1968.
]

#claim[
  $Phi_g$ является автоморфизмом группы $U_n (V)$ в том и только том случае,
  когда $g$ сохраняет ортогональность.
] <prop:johnson-semilinear-unitary>

#proof[
  Пусть $g$ сохраняет ортогональность. Тогда
  $
    Q(Phi_g (sigma)(x)) & = Q(g sigma g^(-1) (x)) \
                        & = alpha Q(sigma g^(-1) (x))^mu \
                        & = alpha Q(g^(-1) (x))^mu
                          = alpha(alpha^(-1) Q(x))^(mu^(-1) mu) = Q(x)
  $
  для всех $x in V$. Значит, $Phi_g (sigma) in U_n (V)$.

  Теперь предположим, что $Phi_g$ — автоморфизм группы $U_n (V)$. Пусть
  $x_1, x_2$ — анизотропные векторы из $V$ и $q(x_1, x_2) = 0$. Возьмем
  изометрии $sigma_1 in S_(x_1) - Z(V)$ и $sigma_2 in S_(x_2) - Z(V)$. Тогда
  $Phi_g (sigma_1) in S_(g x_1) - Z(V)$ и $Phi_g (sigma_2) in S_(g x_2) - Z(V)$.
  Но $sigma_2 in C(sigma_1)$, значит, $Phi_g (sigma_2) in C(Phi_g (sigma_1))$ и
  $g x_2 in E g x_1 union E g x_1^perp$. Так как $C(sigma_1) != C(sigma_2)$, то
  и $C(Phi_g (sigma_1)) != C(Phi_g (sigma_2))$, $g x_2 in.not E g x_1$. Поэтому
  $q(g x_1, g x_2) = 0$, что и требовалось доказать.
]

Изоморфизм $Lambda: Delta arrow U_n (V)$ называется _гомотетией_, если
существует гомоморфизм $chi: Delta arrow Z_n (V)$, удовлетворяющий условию, что
$Lambda(sigma) = chi(sigma) dot sigma$ для всех $sigma in Delta$. Данная
гомотетия определяет единственный гомоморфизм $chi$, и мы обозначаем ее через
$P_chi$.#idx("гомотетия")

#claim[
  Пусть $g_1, g_2$ — полулинейные изоморфизмы пространства $V$ на себя,
  сохраняющие ортогональность. Пусть $P_(chi_1), P_(chi_2)$ — гомотетии $Delta$.
  Следующие условия равносильны:

  #condition-series[
    #condition[$Phi_(g_1) compose P_(chi_1) = Phi_(g_2) compose P_(chi_2)$.]
    <cond:johnson-decomposition-equality>
    #condition[$P_(chi_1) = P_(chi_2)$ и $Phi_(g_1) = Phi_(g_2)$.]
    <cond:johnson-factors-equality>
    #condition[$chi_1 = chi_2$ и $g_1 = alpha g_2$ для некоторого
      $alpha in E^*$.]
    <cond:johnson-scalar-equality>
  ]
] <prop:johnson-decomposition-uniqueness>

#source(25)
#proof[
  (@cond:johnson-scalar-equality) $arrow.double$
  (@cond:johnson-factors-equality). Заметим, что если $g_1 = alpha g_2$, то
  $g_1^(-1) = (alpha^(-1))^(mu^(-1)) g_2^(-1)$. Тогда
  $
    g_1 sigma g_1^(-1) (x) & = g_1 sigma(alpha^(-1))^(mu^(-1)) g_2^(-1) (x) \
                           & = alpha^(-1) g_1 sigma g_2^(-1) (x) \
                           & = (alpha^(-1))(alpha) g_2 sigma g_2^(-1) (x)
                             = g_2 sigma g_2^(-1) (x)
  $
  для всех $x in V$. Значит, $Phi_(g_1) = Phi_(g_2)$. Очевидно, что
  $P_(chi_1) = P_(chi_2)$.

  (@cond:johnson-factors-equality) $arrow.double$
  (@cond:johnson-decomposition-equality). Очевидно.

  (@cond:johnson-decomposition-equality) $arrow.double$
  (@cond:johnson-scalar-equality). Имеем
  $Phi_(g_1) compose P_(chi_1) = Phi_(g_2) compose P_(chi_2)$, или
  $
    Phi_(g_1) (chi_1(sigma) dot sigma)
    = Phi_(g_2) (chi_2(sigma) dot sigma),
  $
  поэтому
  $
    Phi_(g_2) (sigma) Phi_(g_1) (sigma)^(-1)
    = Phi_(g_2) (chi_2(sigma))^(-1)
    dot Phi_(g_1) (chi_1(sigma)) in Z_n (V)
  $
  <passage:johnson-uniqueness-central-product>
  для всех $sigma in Delta$. Отсюда
  $g_2 sigma g_2^(-1) g_1 sigma^(-1) g_1^(-1) (x) in E x$
  для всех $x in V$. В частности,
  $sigma g_2^(-1) g_1 (x) in E g_2^(-1) g_1 sigma(x)$. Пусть вектор $x$
  анизотропен и $V = E x perp U$. Пусть $g_2^(-1) g_1 (x) = alpha x + u$. Если
  $alpha = 0$, то $u$ анизотропен и можно записать $U = E u perp U'$. Возьмем
  $rho in U^+(U)$ с условием, что $rho u in.not E u$, и положим
  $sigma = 1_(E x) perp rho$. Тогда
  $sigma g_2^(-1) g_1 (x) = sigma u = rho u in.not E u$, но
  $g_2^(-1) g_1 sigma(x) = g_2^(-1) g_1 (x) = u$. Значит, $alpha != 0$.

  Теперь возьмем $sigma = eta tau_x^epsilon in S_x - Z(Delta)$. Тогда
  $
    sigma g_2^(-1) g_1 (x) = sigma(alpha x + u)
    = eta epsilon alpha x + eta u
  $
  и $g_2^(-1) g_1 sigma(x) = g_2^(-1) g_1 (eta epsilon x)
  = xi(alpha x + u)$ для некоторого $xi in E^*$. Следовательно,
  $ sigma g_2^(-1) g_1 (x) in E g_2^(-1) g_1 sigma(x) $
  только в том случае, когда $u = 0$. Отсюда $g_2^(-1) g_1 (x) = alpha x$ и
  $g_2^(-1) g_1$ — полулинейный изоморфизм пространства $V$, оставляющий на
  месте все анизотропные прямые. Значит, существует элемент $alpha in E^*$,
  такой, что $g_2^(-1) g_1 (x) = alpha x$ для всех $x in V$. Поэтому
  $g_1(x) = g_2(alpha x) = alpha^mu g_2(x)$ для всех $x in V$, откуда
  $g_1 = alpha^mu g_2$.

  Из равенства $g_1 = alpha^mu g_2$ следует, что $Phi_(g_1) = Phi_(g_2)$, а это
  вместе с (@cond:johnson-decomposition-equality) дает $P_(chi_1) = P_(chi_2)$ и
  $chi_1 = chi_2$. Тем самым утверждение
  (@prop:johnson-decomposition-uniqueness) доказано.
]
