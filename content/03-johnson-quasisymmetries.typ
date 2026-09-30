#import "main-defs.typ": *
#import "statements.typ": *

== Свойства квазисимметрий и трансвекций <sec:johnson-quasisymmetries>

Пусть $U$ — некоторое подпространство из $V$. Для любого ненулевого элемента
$alpha$ из $E$ линейное преобразование $r_alpha$ на $U$, определенное правилом
$r_alpha (u) = alpha u$ для всех $u$ из $U$, называется _растяжением_ на
$U$.#idx("растяжение") Пусть $R(U)$ — группа всех растяжений на $U$.

#source(10)
Для ненулевого вектора $x in V$ положим
$S_x = {sigma in Delta | sigma|_(E x^perp) in R(E x^perp)}$ и назовем $S_x$
множеством всех изометрий, _ассоциированных_ с $x$. С этого момента мы
предполагаем, что $n = dim V >= 3$. В настоящем параграфе изучаются некоторые
свойства множества $S_x$. Нас интересуют два случая, а именно когда вектор $x$
анизотропен и когда он изотропен. Сначала найдем теоретико-групповые свойства,
общие для того и другого случая, а затем — характерные для каждого.

#claim[
  Если $x$ анизотропен, то
  $
    S_x = {eta tau_x^epsilon in Delta | eta, epsilon in cal(U)}
    supset Z(Delta).
  $
  Если $x$ изотропен, то
  $
    S_x = {eta tau_x^alpha in Delta | eta in cal(U), T(alpha) = 0}
    supset Z(Delta).
  $
] <prop:johnson-associated-isometries>

#proof[
  Если $rho in S_x$, можно найти $eta in cal(U)$, такое, что $rho y = eta y$ для
  всех $y in E x^perp$. Значит, $eta^* rho$ оставляет точки гиперплоскости
  $E x^perp$ на месте. Если вектор $x$ анизотропен, то $E x^perp$ регулярна и
  $eta^* rho = tau_x^epsilon$ — квазисимметрия. В этом случае
  $rho = eta tau_x^epsilon$ для некоторых $eta, epsilon in cal(U)$. Если $x$
  изотропен, то $E x^perp$ — вырожденная гиперплоскость, причем
  $rad E x^perp = E x$, поэтому $eta^* rho = tau_x^alpha$ — трансвекция. Таким
  образом, $rho = eta tau_x^alpha$ для некоторого $eta in cal(U)$ и некоторого
  $alpha$, удовлетворяющего условию $T(alpha) = 0$.

  Осталось показать, что $S_x supset Z(Delta)$ в каждом случае. При изотропном
  $x$ трансвекция $tau_x^alpha$ с $alpha != 0$ имеет определитель 1 и, значит,
  лежит в $U_n^+ (V) subset.eq Delta$. Таким образом,
  $tau_x^alpha in S_x - Z(Delta)$.

  Предположим теперь, что $x$ анизотропен. Мы можем отыскать подходящие
  $epsilon, eta in cal(U)$, такие, что $epsilon != eta$ и
  $rho = epsilon perp eta in U_n^+ (V) subset.eq Delta$ для разложения
  $V = E x perp W$. Тогда
  $eta^* rho = eta^* epsilon perp 1 = tau_x^(eta^* epsilon)$. Следовательно,
  $rho = eta tau_x^(eta^* epsilon) in S_x - Z(Delta)$, что и требовалось
  доказать.
]

Теперь ясно, что $S_x = S_y$ для ненулевых векторов $x$ и $y$ из $V$ тогда и
только тогда, когда $y in E x$.

#claim[
  $C(S_x) = {rho in Delta | rho x = xi x
    "для некоторого" xi in cal(U)}$.
] <prop:johnson-associated-centralizer>

#proof[
  Пусть $rho in Delta$ и $rho x = xi x$. Тогда
  $rho (eta tau_x^alpha) rho^(-1) = eta tau_(xi x)^alpha
  = eta tau_x^alpha$, где $tau_x^alpha$ — трансвекция или квазисимметрия в
  зависимости от того, является $x$ изотропным или анизотропным вектором.

  Теперь возьмем $eta tau_x^alpha in S_x - Z(Delta)$. Если $rho in C(S_x)$, то
  $rho (eta tau_x^alpha) rho^(-1) = eta tau_(rho x)^alpha
  = eta tau_x^alpha$, так что $tau_(rho x)^alpha = tau_x^alpha$. Значит,
  $rho x = xi x$ для некоторого $xi$ из $cal(U)$, и
  (@prop:johnson-associated-centralizer) доказано.
]

#source(11)
Очевидно, $S_x$ — абелева подгруппа группы $Delta$. Отсюда следует, что
$S_x subset.eq C C(S_x) subset.eq C(S_x)$.

#claim[
  $S_x = C C(S_x)$.
] <prop:johnson-associated-double-centralizer>

#proof[
  Предположим сначала, что вектор $x$ анизотропен. Тогда
  $
    U(E x) perp U(W) supset.eq C(S_x)
    supset.eq {(det tau)^* perp tau | tau in U(W)},
  $
  где $W = E x^perp$. Если $rho$ — изометрия, принадлежащая $C C(S_x)$, то она
  перестановочна со всеми изометриями вида $(det tau)^* perp tau$, где $tau$
  пробегает $U(W)$. Значит, $E x$ и $W$ инвариантны относительно $rho$.
  Поскольку $rho|_W$ коммутирует со всеми $tau in U(W)$, то $rho|_W in Z(W)$ и,
  согласно определению, $rho in S_x$.

  Пусть вектор $x$ изотропен. Можно считать, что $V = (E x + E y) perp W$, где
  $E x perp W = E x^perp$ и $E x + E y approx.eq mat(0, 1; 1, 0)$. (Здесь $E y$
  и $W$ не определяются единственным образом.) Пусть
  $rho in C C(S_x) subset.eq C(S_x)$. Тогда $rho x = epsilon x$ для некоторого
  $epsilon in cal(U)$ и $rho(E x perp W) = E x perp W$.

  Возьмем $epsilon, eta in cal(U)$, удовлетворяющие условиям $epsilon != eta$ и
  $tau = epsilon perp eta in U_n^+ (V) subset.eq Delta$ для разложения
  $V = (E y + E x) perp W$. Конечно, $tau in C(S_x)$. Поскольку $rho$
  перестановочна с $tau$, то $W$ и $E y + E x$ инвариантны относительно $rho$.
  Все изометрии вида $1 perp tau$, где $tau in U^+(W)$, лежат в $C(S_x)$, и
  $rho$ перестановочна с ними, поэтому $rho|_W in Z(W)$.

  Теперь $rho x = epsilon x$ и $rho w = eta w$ для всех $w in W$ и некоторых
  $epsilon, eta$ из $cal(U)$. Покажем, что $epsilon = eta$. Пусть
  $w_1, w_2, dots, w_(n-2)$ — база $W$. Тогда $x + w_1, dots, w_(n-2)$ — база
  другого регулярного подпространства $W'$ из $E x^perp$. Пусть
  $V = (E y' + E x) perp W'$ и $(E y' + E x) approx.eq mat(0, 1; 1, 0)$.
  Предыдущие рассуждения показывают, что $rho x = epsilon x$ и $rho(w') = xi w'$
  для всех $w' in W'$, где $xi in cal(U)$. Тогда
  $rho(x + w_1) = epsilon x + eta w_1 = xi(x + w_1)$, откуда
  $eta = epsilon = xi$.

  Итак, $rho|_(E x^perp) in R(E x^perp)$ и, значит, $rho in S_x$, что и
  требовалось доказать.
]

#claim[
  Если $C(tau) supset C(S_x)$, то $tau in Z(Delta)$. Значит, если
  $tau in S_x - Z(Delta)$, то $C(tau) = C(S_x)$.
] <prop:johnson-centralizer-maximality>

#proof[
  Из включения $C(S_x) subset C(tau)$ следует перестановочность всех элементов
  из $C(S_x)$ с $tau$, т.~е. $tau in C C(S_x) = S_x$. Если $tau$ не лежит в
  $Z(Delta)$, то $tau$ имеет вид $tau = eta tau_x^alpha$, где $tau_x^alpha$ —
  нетривиальная трансвекция или квазисимметрия. Как и в доказательстве
  утверждения (@prop:johnson-associated-centralizer), любой
  #source(12)
  элемент $rho$ из $C(tau)$ должен удовлетворять равенству $rho x = xi x$ для
  некоторого $xi in cal(U)$. Поэтому $rho in C(S_x)$, что противоречит строгости
  включения $C(S_x) subset C(tau)$. Итак, $tau in Z(Delta)$, что и требовалось
  доказать.
]

На этом мы закончим перечисление общих свойств множеств $S_x$ при изотропном и
анизотропном $x$ и перейдем к специфическим свойствам для каждого случая.

#claim[
  Если вектор $x$ анизотропен, то $N(S_x) = C(S_x)$.
] <prop:johnson-anisotropic-normalizer>

#proof[
  Ясно, что $C(S_x) subset.eq N(S_x)$. Пусть $rho in N(S_x)$,
  $eta tau_x^epsilon in S_x - Z(Delta)$. Тогда
  $rho (eta tau_x^epsilon) rho^(-1) = eta tau_(rho x)^epsilon in S_x$. Значит,
  $rho x in E x$, и поскольку $x$ анизотропен, то $rho x = xi x$ для некоторого
  $xi in cal(U)$. Таким образом, $rho in C(S_x)$, и
  (@prop:johnson-anisotropic-normalizer) доказано.
]

#claim[
  Если вектор $x$ изотропен, то $N(S_x) supset C(S_x)$.
] <prop:johnson-isotropic-normalizer>

#proof[
  Пусть $V = (E y + E x) perp W$, где $E y + E x approx.eq mat(0, 1; 1, 0)$ и
  $E x^perp = E x perp W$. Пусть $W = E z perp W'$ для некоторого анизотропного
  $z in W$. Возьмем $gamma in E^* - cal(U)$ и определим $rho y = gamma^* y$,
  $rho x = gamma^(-1) x$, $rho z = (gamma slash gamma^*) z$,
  $rho|_(W') = 1_(W')$. Тогда $rho in U_n^+ (V) subset.eq Delta$ и
  $rho in.not C(S_x)$, так как $gamma^(-1) in.not cal(U)$.

  Пусть $eta tau_x^alpha$ — произвольный элемент из $S_x$. Тогда
  $rho (eta tau_x^alpha) rho^(-1) = eta tau_(rho x)^alpha
  = eta tau_(gamma^(-1) x)^alpha = eta tau_x^(N(gamma^(-1)) alpha)$
  принадлежит $S_x$. Таким образом, $rho in N(S_x) - C(S_x)$, и
  (@prop:johnson-isotropic-normalizer) доказано.
]

Очевидно, что из $q(x, y) = 0$ следует включение $S_x subset.eq C(S_y)$. Если
$S_x subset.eq C(S_y)$ и $S_x != S_y$, то $q(x, y) = 0$. Действительно, из
соотношения $S_x != S_y$ следует, что $x in.not E y$, а тогда включение
$S_x subset.eq C(S_y)$ влечет за собой $q(x, y) = 0$.
