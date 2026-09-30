#import "main-defs.typ": *
#import "statements.typ": *

== $S_x$ в случае анизотропного вектора $x$ <sec:johnson-anisotropic>

В этом параграфе мы предположим анизотропность вектора $x in V$ и покажем, что
$Lambda(S_x) = S_y$ для некоторого анизотропного вектора $y in V$.

#claim(family: "th")[
  *Теорема.* Пусть $tau in Delta$ таково, что $rho tau rho^(-1) in C(tau)$ для
  всех $rho in C(S_x)$. Тогда $tau in S_x$.
] <th:johnson-commuting-conjugates>

#proof[
  Имеем $V = E x perp W$, где $W = E x^perp$. Ясно, что
  $
    U(E x) perp U(W) supset.eq C(S_x)
    supset.eq {(det rho)^* perp rho | rho in U(W)}.
  $

  #source(13)
  Пусть $tau x = alpha x + w$ для некоторых $alpha in E$, $w in W$. Покажем
  сначала, что $w = 0$.

  Возьмем $overline(rho) in U(W)$, и пусть $epsilon^* = det overline(rho)$.
  Тогда $rho = epsilon perp overline(rho) in C(S_x)$ и должно быть
  $tau rho tau rho^(-1) = rho tau rho^(-1) tau$ для всех таких $rho$. Применим
  обе стороны этого равенства к вектору $x$ и сравним результаты:
  $
    tau rho tau rho^(-1) (x)
    &= epsilon^* tau rho(alpha x + w)
    = tau(alpha x + epsilon^* rho w) \
    &= alpha^2 x + alpha w + epsilon^* tau rho w, \
    rho tau rho^(-1) tau(x)
    &= rho tau(alpha epsilon^* x + rho^(-1) w) \
    &= rho(alpha^2 epsilon^* x + alpha epsilon^* w + tau rho^(-1) w) \
    &= alpha^2 x + alpha epsilon^* rho w + rho tau rho^(-1) w.
  $
  Из сравнения видно, что
  $
    (det overline(rho))(tau rho w - alpha rho w)
    &= rho tau rho^(-1) w - alpha w \
    &= rho(tau rho^(-1) w - alpha rho^(-1) w).
  $
  <eq:johnson-commutation-comparison>

  Если положить $overline(rho) = eta dot 1_W$, где $eta in cal(U)$,
  $eta^n != plus.minus 1$, то $rho = (eta^*)^(n-1) perp eta$, так как
  $det overline(rho) = eta^(n-1)$. Используя равенство
  @eq:johnson-commutation-comparison, получаем
  $
    eta^(n-1) (eta tau w - alpha eta w) & = eta^n (tau w - alpha w) \
                                        & = rho(eta^* tau w - alpha eta^* w)
                                          = eta^* rho(tau w - alpha w),
  $
  так что
  $ eta^(n+1) (tau w - alpha w) = rho(tau w - alpha w). $
  По предположению $eta^n != 1$, значит, $(eta^*)^(n-1) != eta$. Поэтому, если
  прямая $E z$ инвариантна относительно $rho$, то $E z subset.eq E x union W$.
  При $tau w - alpha w in E x$ справедливо равенство
  $
    eta^(n+1) (tau w - alpha w) = rho(tau w - alpha w)
    = (eta^*)^(n-1) (tau w - alpha w),
  $
  откуда $eta^(2n) (tau w - alpha w) = tau w - alpha w$. Но
  $eta^n != plus.minus 1$, значит, $tau w - alpha w = 0$. Если
  $tau w - alpha w in W$, то
  $
    eta^(n+1) (tau w - alpha w) = rho(tau w - alpha w)
    = eta(tau w - alpha w)
  $
  и, поскольку $eta^n != 1$, то снова $tau w - alpha w = 0$. Значит,
  $tau w = alpha w$.

  Пусть вектор $w$ анизотропен. Тогда $Q(w) = Q(tau w) = N(alpha) Q(w)$ и
  $N(alpha) = 1$. Следовательно,
  $Q(tau x) = Q(alpha x + w) = Q(x) + Q(w) != Q(x)$, что невозможно. Таким
  образом, $Q(w) = 0$ и $Q(tau x) = N(alpha) Q(x) + Q(w)$, откуда
  $N(alpha) = 1$. Пусть $w != 0$ и $V = E x perp (E w + E z) perp W'$, где
  $E w + E z approx.eq mat(0, 1; 1, 0)$. Тогда
  $tau(E x perp E w) = E x perp E w$ и $(E x perp E w)^perp = E w perp W'$
  инвариантно относительно $tau$. Если мы убедимся, что $tau z in W$, то $W$ и,
  следовательно, $W^perp = E x$ окажутся инвариантными относительно $tau$, что
  противоречит предположению $w != 0$.

  #source(14)
  Возьмем $eta in cal(U)$, такой, что $eta^(2n) != plus.minus 1$. Определим
  $rho$ по правилу $rho x = eta^(n-1) x$, $rho w' = eta^* w'$ для всех
  $w' in W'$, $rho w = -eta^* z$ и $rho z = eta^* w$. Тогда $det rho = 1$ и
  $rho in C(S_x)$. Обращаясь снова к равенству
  @eq:johnson-commutation-comparison, получим
  $
    (eta^*)^(n-1) (tau rho w - alpha rho w)
    = rho(tau rho^(-1) w - alpha rho^(-1) w),
  $
  или
  $ -(eta^*)^n (tau z - alpha z) = eta rho(tau z - alpha z). $
  Пусть $tau z - alpha z = beta x + u$ для некоторых $beta in E$, $u in W$.
  Тогда
  $ -(eta^*)^n (beta x + u) = eta(eta^(n-1) beta x + rho u). $
  Значит,
  $
    beta(eta^n + (eta^*)^n) x
    = -(eta rho u + (eta^*)^n u) in W.
  $
  Если $eta^n = -(eta^*)^n$, то $eta^(2n) = -1$, что противоречит выбору $eta$.
  Отсюда $beta = 0$ и $tau z = alpha z + u in W$.

  Итак, мы показали, что $tau x = alpha x$, если $rho tau rho^(-1) in C(tau)$
  для всех $rho in C(S_x)$. Поэтому $tau$ имеет вид
  $tau = alpha perp overline(tau)$, где $overline(tau) in U(W)$. Так как
  $ C(S_x) supset.eq {(det rho)^* perp rho | rho in U(W)}, $
  то $rho overline(tau) rho^(-1) in C(overline(tau))
  = {sigma in U(W) | sigma overline(tau) = overline(tau) sigma}$ для всех $rho$
  из $U(W)$. Значит, $overline(tau)$ удовлетворяет предположениям теоремы при
  $Delta = U(W)$ и любом анизотропном векторе $y in W$, т.~е. если $y$ —
  анизотропный вектор из $W$, $S_y$ и $C(S_y)$ взяты относительно
  $Delta = U(W)$, то
  $rho overline(tau) rho^(-1) in C(overline(tau))$
  для всех $rho in C(S_y)$. (Заметим, что в доказательстве соотношения
  $tau x = alpha x$ не делается никаких ограничений на $n = dim V$, исключается
  только случай $n = 0$.) Поэтому $overline(tau)$ оставляет на месте все
  анизотропные прямые и, следовательно, принадлежит $Z(W)$.

  Итак, $tau$ имеет вид $tau = alpha 1_(E x) perp eta 1_W$,
  $alpha, eta in cal(U)$, откуда $tau = eta tau_x^(alpha eta^*) in S_x$, что и
  требовалось доказать.
]

#claim(family: "cor")[
  *Следствие.* Каждая абелева нормальная подгруппа из $Delta$ содержится в
  $Z(Delta)$.
] <cor:johnson-abelian-normal-central>

#proof[
  Предположим, что $G$ нормальна в $Delta$ и абелева. Возьмем $tau in G$. Тогда
  $rho tau rho^(-1) in G$ для всех $rho in Delta$ и, значит,
  $rho tau rho^(-1) in C(tau)$ для всех $rho in Delta$. По теореме
  @th:johnson-commuting-conjugates преобразование $tau$ должно оставлять все
  анизотропные прямые на месте, откуда $tau in Z(Delta)$.
]

Все изометрии из $S_x$ регулярны. Покажем, что их образы при $Lambda$ также
регулярны. Очевидно, $Lambda(Z(Delta)) = Z(Delta)$. Возьмем
$sigma in S_x - Z(Delta)$ и покажем, что $Lambda sigma$ регулярна.

#source(15)
#claim[
  Если $sigma in S_x - Z(Delta)$, то $sigma' = Lambda sigma$ — регулярная
  изометрия из $Delta$.
] <prop:johnson-regular-image>

#proof[
  Пусть $P'$ и $R'$ — собственное и вычетное пространства для
  $sigma' = Lambda sigma$. Допустим, что $P'$ вырождено. Возьмем ненулевой
  вектор $y in rad P'$ и трансвекцию $tau_y^alpha$, $alpha != 0$. Конечно,
  $tau_y^alpha in Delta$, и если $rho in C(sigma')$, то $rho(P') = P'$. Значит,
  $rho tau_y^alpha rho^(-1) = tau_(rho y)^alpha in C(tau_y^alpha)$, так как
  $q(y, rho y) = 0$. Поэтому
  $
    Lambda^(-1) rho Lambda^(-1) tau_y^alpha Lambda^(-1) rho^(-1)
    in C(Lambda^(-1) tau_y^alpha)
  $
  для всех $rho in C(sigma')$. Но когда $rho$ пробегает $C(sigma')$, его
  прообраз $Lambda^(-1) rho$ пробегает
  $C(Lambda^(-1) sigma') = C(sigma) = C(S_x)$. Таким образом,
  $Lambda^(-1) tau_y^alpha$ удовлетворяет условиям теоремы
  @th:johnson-commuting-conjugates и, значит, $Lambda^(-1) tau_y^alpha in S_x$.
  Так как $tau_y^alpha in.not Z(Delta)$, то
  $Lambda^(-1) tau_y^alpha in S_x - Z(Delta)$, откуда
  $C(Lambda^(-1) tau_y^alpha) = C(sigma) = C(S_x)$. Поэтому
  $C(tau_y^alpha) = C(sigma') = C(S_y)$. Далее,
  $
    Lambda S_x = Lambda C C(Lambda^(-1) tau_y^alpha)
    = C C(tau_y^alpha) = S_y.
  $
  Значит, $Lambda(N(S_x)) = N(Lambda S_x) = N(S_y)$. Но $N(S_x) = C(S_x)$ и
  $N(S_y) supset C(S_y)$, откуда
  $C(sigma') = Lambda C(sigma) = Lambda N(S_x) = N(S_y) supset C(sigma')$,
  противоречие. Значит, изометрия $Lambda sigma = sigma'$ должна быть
  регулярной, что и требовалось показать.
]

Итак, для любого $sigma in S_x - Z(Delta)$ преобразование
$sigma' = Lambda sigma$ регулярно, поэтому можно записать $V = P' perp R'$, где
$
  P' = P_(epsilon_1) perp dots perp P_(epsilon_k)
  perp (P_(alpha_1^*) + P_(alpha_1^(-1))) perp dots
  perp (P_(alpha_r^*) + P_(alpha_r^(-1))).
$
Предположим временно, что $P' != {0}$. Тогда

#claim[
  $V = P' = P_(epsilon_1) perp P_(epsilon_2)$.
] <prop:johnson-two-eigenspaces>

#proof[
  Заметим сначала, что $R' = {0}$. Как мы знаем, $sigma'$ не оставляет на месте
  ни одну прямую из $R'$, значит, $dim R' >= 2$, если $R' != {0}$. Очевидно,
  $1_(P') perp U^+(R')$ — подгруппа из $Delta$, содержащая изометрию, не
  перестановочную с $sigma'$, поскольку $sigma'|_(R') in.not Z(R')$. При
  подходящем выборе $xi, eta in cal(U)$, $xi != eta$, изометрия
  $tau = xi perp eta$, согласованная с разложением $V = P' perp R'$, лежит в
  $Delta$ и, значит, в $C(sigma')$. Но $tau in.not Z(Delta)$ и
  $tau in C C(sigma')$, так как $P'$ и $R'$ инвариантны относительно каждой
  изометрии из $C(sigma')$. Поэтому $C(tau) supset.eq C(sigma')$. Однако
  $C(tau) supset.eq 1_(P') perp U^+(R')$ и $C(tau) supset C(sigma')$. С другой
  стороны, $C(Lambda^(-1) tau) = C(sigma)$, противоречие.

  #source(16)
  Используя те же рассуждения и утверждение (@prop:johnson-line-displacement),
  можно показать, что разложение пространства $P'$ содержит не более двух
  слагаемых. Очевидно, $P'$ не может иметь вид $P' = P_(epsilon_1)$, поскольку
  тогда $sigma' in Z(Delta)$.

  Наконец, исключим возможность слагаемого $P_(alpha^*) + P_(alpha^(-1))$ в
  разложении $P'$. При доказательстве этого по существу повторяются рассуждения
  из (@prop:johnson-regular-image).

  Элемент $alpha$ не лежит в $cal(U)$, поэтому $P_(alpha^*)$ вполне изотропно.
  Пусть $y in P_(alpha^*)$, а $tau_y^beta$ — трансвекция, причем $beta != 0$.
  Любая изометрия $rho$ из $C(sigma')$ оставляет на месте $P_(alpha^*)$ и
  $P_(alpha^(-1))$. Значит, $q(y, rho y) = 0$ и
  $rho tau_y^beta rho^(-1) = tau_(rho y)^beta in C(tau_y^beta)$ для всех
  $rho in C(sigma')$. Поэтому $Lambda^(-1) tau_y^beta$ удовлетворяет условиям
  теоремы (@th:johnson-commuting-conjugates) и лежит в
  $S_x = C C(S_x) = C C(sigma)$. Отсюда $tau_y^beta in C C(sigma')$, что
  противоречит неинвариантности $P_(alpha^(-1))$ относительно $tau_y^beta$. В
  самом деле, если $z in P_(alpha^(-1))$ и $q(z, y) != 0$, то
  $ tau_y^beta (z) = z + beta q(z, y) y in.not P_(alpha^(-1)). $
  Утверждение (@prop:johnson-two-eigenspaces) доказано.
]

Теперь можно написать
$ V = P' = P_(epsilon_1) perp P_(epsilon_2), $
где $0 < dim P_(epsilon_1) <= dim P_(epsilon_2)$. Наша задача — показать, что
$dim P_(epsilon_1) = 1$. Используем для этого метод, введенный в
@bib:johnson-Johnson1971. Его суть заключается в лемме (4.3) из
@bib:johnson-Johnson1971, которая воспроизводится здесь с небольшой модификацией
доказательства, позволяющей применять ее в более общей ситуации.

#claim(family: "th")[
  *Теорема.* Пусть $x$ — анизотропный вектор из $V$, $sigma in S_x - Z(Delta)$.
  Пусть $sigma_1, dots, sigma_k$ и $sigma_(k')$ сопряжены с $sigma$ в $Delta$ и
  не лежат в $C(sigma)$. Предположим, что
  $
    C(sigma) supset C(sigma, sigma_1) supset dots
    supset C(sigma, dots, sigma_k)
    supset.eq C(sigma, sigma_1, dots, sigma_(k-1), sigma_(k')).
  $
  Тогда $C(sigma, dots, sigma_k)
  = C(sigma, sigma_1, dots, sigma_(k-1), sigma_(k'))$.
] <th:johnson-centralizer-chain>

#proof[
  Пусть $sigma_(k') = rho_(k') sigma rho_(k')^(-1)$ и
  $sigma_i = rho_i sigma rho_i^(-1)$ для $1 <= i <= k$, $rho_(k')$ и $rho_i$
  принадлежат $Delta$. Если $tau in C(sigma, sigma_1, dots, sigma_k)$, то
  $tau x in E x$ и $tau(rho_i x) in E rho_i x$, $1 <= i <= k$. Пусть
  $tau x = xi x$ и $tau(rho_i x) = xi_i rho_i x$, $1 <= i <= k$. Так как
  $sigma_i in.not C(sigma)$, то
  $0 != q(x, rho_i x) = q(tau x, tau rho_i x) = xi xi_i^* q(x, rho_i x)$
  и $xi = xi_i$, $1 <= i <= k$. Положим
  $W = E x + E rho_1 x + dots + E rho_k x$. Так как $tau$ централизует
  $sigma, sigma_1, dots, sigma_k$, то $tau|_W in R(W)$. Обратное тоже верно,
  поэтому
  $
    C(sigma, sigma_1, dots, sigma_k)
    = {tau in Delta | tau|_W in R(W)}.
  $

  #source(17)
  Покажем теперь, что для $y in V - W$ существует
  $tau in C(sigma, sigma_1, dots, sigma_k)$ и $xi in cal(U)$, такие, что
  $tau x = xi x$, $tau y != xi y$. Пусть сначала $q(y, W) = 0$. Если
  $Q(y) != 0$, то возьмем $tau in S_y - Z(Delta)$. Пусть $Q(y) = 0$. Тогда
  $q(y, W^perp) != 0$, поскольку $y in.not W = W^(perp perp)$. Теперь можно
  выбрать $z in W^perp$ так, чтобы $E y + E z approx.eq mat(0, 1; 1, 0)$, и
  взять $tau in S_z - Z(Delta)$.

  При $q(y, W) != 0$ надо действовать несколько тоньше. Пусть $W$ регулярно,
  тогда $y = w + y'$ для некоторых $w in W$ и $y' in W^perp$, $y' != 0$. По
  предыдущему существует $tau in C(sigma, dots, sigma_k)$, удовлетворяющий
  условиям $tau x = xi x$, $tau y' != xi y'$. Тогда
  $tau y = tau(w + y') = xi w + tau y' != xi y$. Будем считать, что
  $rad W != {0}$. Пусть
  $ V = W' perp (rad W + U) perp U', $
  где $rad W + U$ — гиперболическое пространство, т.~е. ортогональная сумма
  гиперболических плоскостей, $W = W' perp rad W$. Если $q(y, rad W) != 0$, то
  возьмем $z in rad W$, такое, что $q(y, z) != 0$, и выберем
  $tau in S_z - Z(Delta)$. Можно считать, что $y = w + u'$, где $w in W$ и
  $u' != 0$, $u' in U'$. По предыдущему найдется
  $tau in C(sigma, dots, sigma_k)$, такое, что $tau x = xi x$ и
  $tau u' != xi u'$. Тогда $tau y != xi y$.

  Допустим теперь, что существует $rho_(k') in Delta$, такое, что
  $
    C(sigma, sigma_1, dots, sigma_(k-1), sigma_(k'))
    subset.eq C(sigma, sigma_1, dots, sigma_k).
  $
  Если $rho_k x$ не принадлежит
  $W' = E x + E rho_1 x + dots + E rho_(k-1) x + E rho_(k') x$, то существует
  $tau in C(sigma, sigma_1, dots, sigma_(k-1), sigma_(k'))$, такое, что
  $tau x = xi x$ и $tau(rho_k x) != xi rho_k x$. Поэтому $tau$ не лежит в
  $C(sigma, sigma_1, dots, sigma_k)$, что противоречит включению
  $
    C(sigma, sigma_1, dots, sigma_(k'))
    subset.eq C(sigma, sigma_1, dots, sigma_k).
  $
  Таким образом, $rho_k x in W'$. Так как $C(sigma, sigma_1, dots, sigma_k)
  subset C(sigma, sigma_1, dots, sigma_(k-1))$, то
  $rho_k x in.not E x + E rho_1 x + dots + E rho_(k-1) x$. Следовательно,
  $ W = E x + E rho_1 x + dots + E rho_(k-1) x + E rho_k x = W' $
  и $C(sigma, sigma_1, dots, sigma_(k-1), sigma_(k'))
  = C(sigma, sigma_1, dots, sigma_k)
  = {tau in Delta | tau|_W in R(W)}$. Теорема (@th:johnson-centralizer-chain)
  доказана.
]

Для разложения $V = P' = P_(epsilon_1) perp P_(epsilon_2)$, где
$0 < dim P_(epsilon_1) <= dim P_(epsilon_2)$, предположим дополнительно, что
$dim P_(epsilon_1) >= 2$. Покажем, что в этом случае свойство, описанное в
теореме (@th:johnson-centralizer-chain), не имеет места для
$Lambda sigma = sigma'$.

Заметим, что если $sigma'$ соответствует разложению
$V = P_(epsilon_1) perp P_(epsilon_2)$, то некоторая изометрия $tau$
перестановочна с $sigma'$
#source(18)
тогда и только тогда, когда $tau$ оставляет на месте $P_(epsilon_1)$ и
$P_(epsilon_2)$. Если $rho sigma' rho^(-1)$ сопряжена с $sigma'$, то она
соответствует разложению $V = rho P_(epsilon_1) perp rho P_(epsilon_2)$.

#claim[
  В разложении $V = P_(epsilon_1) perp P_(epsilon_2)$ размерность
  $P_(epsilon_1)$ равна 1.
] <prop:johnson-eigenline>

#proof[
  Предположим, что $dim P_(epsilon_1) >= 2$, и пусть
  $
    P_(epsilon_1) = P'_(epsilon_1) perp E x_1 perp E y_1
    quad "и" quad P_(epsilon_2) = E x_2 perp E y_2 perp P'_(epsilon_2).
  $
  Построим сначала три изометрии $rho_1, rho_2, rho_3$, принадлежащие
  $U_n^+ (V) subset.eq Delta$, не удовлетворяющие цепному условию из теоремы
  (@th:johnson-centralizer-chain).

  Определим $rho_1$ по правилу $rho_1|_((E x_1 perp E x_2)^perp) = 1$,
  $rho_1 x_1 = alpha x_1 + beta x_2$, где $alpha != 0$, $beta != 0$, и продолжим
  $rho_1$ до преобразования из $U_n^+ (V)$. Это возможно ввиду
  (@prop:johnson-line-displacement). Аналогично определим $rho_2$:
  $rho_2|_((E y_1 perp E y_2)^perp) = 1$, $rho_2 y_1 = gamma y_1 + delta y_2$,
  где $gamma != 0$, $delta != 0$, и продолжим $rho_2$ до элемента из
  $U_n^+ (V)$. Наконец, определим $rho_3$:
  $rho_3|_(P'_(epsilon_1) perp P'_(epsilon_2)) = 1$,
  $rho_3 x_1 = alpha' x_1 + beta' y_2$, где $alpha' != 0$, $beta' != 0$,
  продолжим $rho_3$ до изометрии из $U_2^+ (E x_1 perp E y_2)$, затем положим
  $rho_3 y_1 = gamma' y_1 + delta' x_2$, где $gamma' != 0$, $delta' != 0$, и
  продолжим $rho_3$ до элемента из $U_2^+ (E y_1 perp E x_2)$. Тогда
  $rho_3 in U_n^+ (V)$. Пусть $sigma_i = rho_i sigma' rho_i^(-1)$,
  $i = 1, 2, 3$. Конечно, $sigma_i in.not C(sigma')$ при $i = 1, 2, 3$,
  поскольку $rho_i P_(epsilon_1)$ неинвариантно относительно $sigma'$.

  Рассмотрим цепь $C(sigma') supset C(sigma', sigma_1)
  supset C(sigma', sigma_1, sigma_2)$. Первое включение строгое, так как
  $sigma' in.not C(sigma', sigma_1)$. Если взять $tau$, удовлетворяющее
  условиям, что $tau|_(P_(epsilon_1) perp E x_2) = epsilon$ и
  $tau|_(E y_2 perp P'_(epsilon_2)) = eta$ для подходящих
  $epsilon, eta in cal(U)$, то $tau in Delta - Z(Delta)$ и
  $tau in C(sigma', sigma_1)$. Заметим, что $sigma_1$ соответствует разложению
  $V = rho_1 P_(epsilon_1) perp rho_1 P_(epsilon_2)$,
  $tau P_(epsilon_1) = P_(epsilon_1)$ и
  $tau(rho_1 P_(epsilon_1)) = rho_1 P_(epsilon_1)$. Но
  $tau in.not C(sigma', sigma_1, sigma_2)$, так как
  $
    rho_2 P_(epsilon_1)
    = P'_(epsilon_1) perp E x_1 perp E(gamma y_1 + delta y_2)
  $
  и $tau(gamma y_1 + delta y_2) = gamma epsilon y_1 + delta eta y_2
  = epsilon(gamma y_1 + delta y_2) + (eta - epsilon) delta y_2$, где
  $eta - epsilon != 0$, $delta != 0$. Значит,
  $tau rho_2(y_1) in.not rho_2 P_(epsilon_1)$. Итак, все включения в цепочке
  строгие.

  Теперь мы покажем, что
  $C(sigma', sigma_1, sigma_3) subset C(sigma', sigma_1, sigma_2)$. Заметим, что
  $rho_3 P_(epsilon_1) = P'_(epsilon_1)
  perp E(alpha' x_1 + beta' y_2) perp E(gamma' y_1 + delta' x_2)$. Если
  $tau in C(sigma', sigma_1)$, то $tau(P_(epsilon_1)) = P_(epsilon_1)$ и
  $tau(rho_1 P_(epsilon_1)) = rho_1 P_(epsilon_1)
  = P'_(epsilon_1) perp E y_1 perp E(alpha x_1 + beta x_2)$. Значит,
  $
    tau(P_(epsilon_1) inter rho_1 P_(epsilon_1))
    = P_(epsilon_1) inter rho_1 P_(epsilon_1)
    = P'_(epsilon_1) perp E y_1.
  $
  Таким образом, $tau x_1 in E x_1$ и
  $tau(alpha x_1 + beta x_2) in E(alpha x_1 + beta x_2)$. Поскольку
  $q(x_1, alpha x_1 + beta x_2) != 0$, то
  $tau|_(E x_1 perp E x_2) in Z(E x_1 perp E x_2)$.

  #source(19)
  Если $tau in C(sigma', sigma_1, sigma_2)$, то $tau$ должно отображать
  $rho_2 P_(epsilon_1)$ в $rho_2 P_(epsilon_1)$. Предыдущие рассуждения
  показывают, что из включения $tau in C(sigma', sigma_1, sigma_2)$ следуют
  включения $tau|_(E x_1 perp E x_2) in Z(E x_1 perp E x_2)$ и
  $tau|_(E y_1 perp E y_2) in Z(E y_1 perp E y_2)$.

  Пусть теперь $tau in C(sigma', sigma_1, sigma_3)$. Тогда
  $tau|_(E x_1 perp E x_2) in Z(E x_1 perp E x_2)$ и
  $tau(rho_3 P_(epsilon_1)) = rho_3 P_(epsilon_1)$. Но
  $tau(P_(epsilon_i) inter rho_3 P_(epsilon_i))
  = P_(epsilon_i) inter rho_3 P_(epsilon_i) = P'_(epsilon_i)$
  для $i = 1, 2$. Значит, $tau(E x_1 perp E y_1) = E x_1 perp E y_1$ и
  $tau(E x_2 perp E y_2) = E x_2 perp E y_2$. Так как $tau x_1 in E x_1$ и
  $tau x_2 in E x_2$, то $tau y_1 in E y_1$ и $tau y_2 in E y_2$. Пусть
  $tau x_1 = xi x_1$ и $tau y_2 = zeta y_2$. Так как
  $tau P'_(epsilon_1) = P'_(epsilon_1)$ и
  $tau rho_3 P_(epsilon_1) = rho_3 P_(epsilon_1)$, то
  $
    tau(alpha' x_1 + beta' y_2) = alpha' xi x_1 + beta' zeta y_2
    in E(alpha' x_1 + beta' y_2),
  $
  откуда $zeta = xi$. Аналогично, $tau y_1 = xi y_1$, поэтому
  $
    tau|_(E x_1 perp E y_1 perp E x_2 perp E y_2)
    in Z(E x_1 perp E y_1 perp E x_2 perp E y_2).
  $

  Чтобы доказать включение
  $C(sigma', sigma_1, sigma_3) subset.eq C(sigma', sigma_1, sigma_2)$, положим
  $V = P'_(epsilon_1) perp U perp P'_(epsilon_2)$, где
  $U = E x_1 perp E x_2 perp E y_1 perp E y_2$. Любой элемент $tau$ из
  $C(sigma', sigma_1, sigma_3)$ перестановочен с $sigma'$ и $sigma_1$, поэтому
  остается проверить его перестановочность с $sigma_2$. Поскольку
  $tau in C(sigma', sigma_1, sigma_3)$, то $P'_(epsilon_1)$ и $U$ инвариантны
  относительно $tau$. Но $tau|_U in Z(U)$, значит, $tau$ оставляет на месте
  $
    rho_2 P_(epsilon_1)
    = P'_(epsilon_1) perp E x_1 perp E(gamma y_1 + delta y_2).
  $
  Таким образом, $tau in C(sigma_2)$ и
  $C(sigma', sigma_1, sigma_3) subset.eq C(sigma', sigma_1, sigma_2)$.

  Пусть теперь $tau in U_n^+ (V)$ определяется правилом
  $
    tau(y) = cases(
      y & "при" y in P'_(epsilon_1) perp P'_(epsilon_2),
      eta y & "при" y in E x_1 perp E x_2,
      eta^* y & "при" y in E y_1 perp E y_2,
    ),
  $
  где $eta in cal(U) - {plus.minus 1}$. Ясно, что
  $tau in.not C(sigma', sigma_1, sigma_3)$, так как $tau|_U in.not Z(U)$. Столь
  же очевидно, что $P_(epsilon_1)$, $rho_1 P_(epsilon_1)$ и
  $rho_2 P_(epsilon_1)$ инвариантны относительно $tau$. Значит,
  $tau in C(sigma', sigma_1, sigma_2)$.

  Таким образом,
  $
    C(sigma') supset C(sigma', sigma_1)
    supset C(sigma', sigma_1, sigma_2)
    supset C(sigma', sigma_1, sigma_3).
  $
  Применяя $Lambda^(-1)$, получим
  $
    C(sigma) supset C(sigma, Lambda^(-1) sigma_1)
    supset C(sigma, Lambda^(-1) sigma_1, Lambda^(-1) sigma_2)
    supset C(sigma, Lambda^(-1) sigma_1, Lambda^(-1) sigma_3),
  $
  где $Lambda^(-1) sigma_1$, $Lambda^(-1) sigma_2$ и $Lambda^(-1) sigma_3$
  сопряжены с изометрией $sigma$, но не перестановочны с ней. Это противоречит
  теореме (@th:johnson-centralizer-chain). Следовательно,
  $dim P_(epsilon_1) = 1$, что и требовалось доказать.
]

#source(20)
Теперь покажем, что предположение, сделанное перед
(@prop:johnson-two-eigenspaces), всегда верно:

#claim[
  $P' != {0}$.
] <prop:johnson-nonzero-eigenspace>

#proof[
  Пусть, напротив, $P' = {0}$, т.~е. $V = R'$ и $sigma'$ не имеет инвариантных
  прямых в $V$.

  Если пространство $V$ $sigma'$-циклическое, т.~е. существует такой вектор $x$,
  что $x, sigma' x, dots, (sigma')^(n-1) x$ порождают $V$, то, как показывают
  прямые вычисления, централизатор $C(sigma')$ должен быть абелев. Но он не
  абелев, поэтому $V$ не может быть $sigma'$-циклическим.

  Через $U_y$ обозначим $sigma'$-циклическое подпространство из $V$, порожденное
  вектором $y$. Утверждается, что существуют такие $y_1, dots, y_k$ из $V$, для
  которых
  $ V = U_(y_1) perp dots perp U_(y_k). $
  Пусть уже найдены такие $y_1, dots, y_j$, что
  $V = U_(y_1) perp dots perp U_(y_j) perp W$. Тогда $U_(y_1), dots, U_(y_j)$ и
  $W$ инвариантны относительно $sigma'$. Выберем такой $z in W$, $z != 0$, чтобы
  $dim U_z$ была минимальна. Пространство $U_z$ или вполне изотропно, или
  регулярно. Мы утверждаем, что $U_z$ можно считать регулярным. В самом деле,
  пусть $dim U_z$ минимальна и $U_z$ вполне изотропно.

  Если $q(z, rho z) = 0$ для всех $rho in C(sigma')$, то рассмотрим трансвекцию
  $tau_z^alpha$, $alpha != 0$. Имеем
  $rho tau_z^alpha rho^(-1) = tau_(rho z)^alpha in C(tau_z^alpha)$
  для всех $rho in C(sigma')$. Значит,
  $Lambda^(-1) tau_z^alpha in C C(sigma) = S_x$ ввиду
  (@th:johnson-commuting-conjugates) и
  $tau_z^alpha in C C(sigma') subset.eq C(sigma')$. Но тогда $sigma' z in E z$,
  что противоречит условию $P' = {0}$.

  Итак, существует изометрия $rho in C(sigma')$, такая, что $q(z, rho z) != 0$.
  Пусть $rho z = u + w$, где $u in U_(y_1) perp dots perp U_(y_j)$, $w in W$.
  Тогда $q(z, w) != 0$ и $Q(beta z + w) != 0$ при подходящем $beta in F$.

  Пусть $dim U_z = l + 1$ и
  $(sigma')^(l+1) z = sum_(mu=0)^l a_mu (sigma')^mu z$. Поскольку
  $rho in C(sigma')$, справедливо равенство
  $(sigma')^(l+1) rho z = sum_(mu=0)^l a_mu (sigma')^mu rho z$. Подставляя
  вместо $rho z$ вектор $u + w$, получаем
  $
    (sigma')^(l+1) u + (sigma')^(l+1) w
    = sum_(mu=0)^l a_mu (sigma')^mu u
    + sum_(mu=0)^l a_mu (sigma')^mu w.
  $
  Значит,
  $ (sigma')^(l+1) w = sum_(mu=0)^l a_mu (sigma')^mu w. $

  #source(21)
  Отсюда следует, что
  $
    (sigma')^(l+1) (beta z + w)
    = sum_(mu=0)^l a_mu (sigma')^mu (beta z + w),
  $
  и, поскольку размерность $U_z$ минимальна, $dim U_(beta z + w)$ также
  минимальна. Так как $Q(beta z + w) != 0$, то подпространство $U_(beta z + w)$
  регулярно.

  Итак, мы можем выбрать вектор $y_(j+1)$ из $W$, такой, что $U_(y_(j+1))$
  регулярно. Отсюда
  $ V = U_(y_1) perp dots perp U_(y_j) perp U_(y_(j+1)) perp W'. $
  Продолжая таким образом дальше, получим требуемое разложение:
  $ V = U_(y_1) perp dots perp U_(y_k). $
  При этом $dim U_(y_i) >= 2$, $i = 1, 2, dots, k$. Значит, $k <= n slash 2$ и
  $dim V >= 4$. Можно считать, что векторы $y_i$ анизотропны.

  Для подходящих $eta, epsilon$ из $cal(U)$ изометрия
  $rho'_i = eta tau_(y_i)^epsilon$ принадлежит $Delta - Z(Delta)$,
  $i = 1, 2, dots, k - 1$. Пусть $sigma'_i = rho'_i sigma' rho'_i^(-1)$, тогда
  любая изометрия $tau in C(sigma', sigma'_1, dots, sigma'_(k-1))$ оставляет на
  месте каждое подпространство $U_(y_i)$, $i = 1, 2, dots, k - 1$, а значит, и
  $U_(y_k)$. В самом деле, если $tau y_i = u_i + v_i$, $u_i in U_(y_i)$,
  $v_i in U_(y_i)^perp$, то $sigma' v_i = sigma'_i v_i$ и
  $sigma' y_i != sigma'_i y_i$. Значит, $tau(sigma' y_i - sigma'_i y_i)
  = sigma' u_i - sigma'_i u_i in U_(y_i)$ и $tau$ отображает некоторый ненулевой
  вектор из $U_(y_i)$ в $U_(y_i)$. Из минимальности $dim U_(y_i)$ следует
  инвариантность подпространства $U_(y_i)$ относительно $tau$.

  Поскольку любое $tau$ из $C(sigma', sigma'_1, dots, sigma'_(k-1))$ оставляет
  на месте каждое $U_(y_i)$, то централизатор
  $C(sigma', sigma'_1, dots, sigma'_(k-1))$ абелев. Положим
  $sigma_i = Lambda^(-1) sigma'_i$ и $rho_i = Lambda^(-1) rho'_i$. Тогда
  $C(sigma, sigma_1, dots, sigma_(k-1))$ также абелев. Пусть
  $W = E x + E rho_1 x + dots + E rho_(k-1) x$. Если $tau in Delta$ и
  $tau|_W in R(W)$, то $tau in C(sigma, sigma_1, dots, sigma_(k-1))$. Кроме
  того, $dim W <= k <= n slash 2$ и, значит, $dim W^perp >= n slash 2 >= 2$.

  Подпространство $W$ не является вполне изотропным, так как $Q(x) != 0$.
  Значит,
  $ V = W_1 perp (rad W + U_1) perp U_2, $
  где $W = W_1 perp rad W$ и $rad W + U_1$ — гиперболическое пространство,
  причем $U_1$ вполне изотропно. При этом $dim U_2 >= 1$, потому что
  $dim U_1 = dim rad W <= k - 1$. Если $rad W = {0}$,
  #source(22)
  имеем включение
  $
    1_W perp U^+(W^perp)
    subset.eq C(sigma, sigma_1, dots, sigma_(k-1)),
  $
  что противоречит коммутативности $C(sigma, sigma_1, dots, sigma_(k-1))$.
  Следовательно, $rad W != {0}$ и существуют $y != 0$ в $rad W$ и $z in U_2$,
  такой, что $Q(z) != 0$. При подходящих $eta, epsilon in cal(U)$ изометрии
  $eta tau_z^epsilon$ и $eta tau_(z+y)^epsilon$ лежат в
  $C(sigma, sigma_1, dots, sigma_(k-1)) - Z(Delta)$, поскольку $z$ и $z + y$
  ортогональны подпространству $W$. Это снова противоречит коммутативности
  $C(sigma, sigma_1, dots, sigma_(k-1))$.

  Итак, $P' != {0}$, что и требовалось доказать.
]

#claim(family: "th")[
  *Теорема.* Пусть $x$ — анизотропный вектор из $V$. Тогда $Lambda S_x = S_y$
  для некоторого анизотропного вектора $y$ из $V$.
] <th:johnson-anisotropic-image>

#proof[
  Возьмем $sigma in S_x - Z(Delta)$, тогда $C(sigma) = C(S_x)$ и
  $Lambda sigma in S_y - Z(Delta)$ для некоторого анизотропного $y$ из $V$.
  Следовательно,
  $
    Lambda(S_x) = Lambda C C(S_x) = Lambda C C(sigma)
    = C C(Lambda sigma) = S_y,
  $
  что и требовалось доказать.
]
