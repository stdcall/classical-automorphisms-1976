#import "main-defs.typ": *
#import "statements.typ": *

#source(100)
=== Контраградиент <sec:omeara-contragredient>

Рассмотрим полулинейное отображение $k: V -> V_1$ относительно изоморфизма полей
$mu: F arrow.r.twohead.tail F_1$. Ясно, что $mu^(-1) rho_1 k in V'$ для каждого
$rho_1 in V'_1$. Это позволяет с каждым полулинейным отображением $k$ связать
_транспонированное отображение_
$ attach(k, tl: t): V'_1 -> V', $
определяемое формулой
$ attach(k, tl: t)(rho_1) = mu^(-1) rho_1 k, quad rho_1 in V'_1. $
Другими словами, каждому $k$ соответствует точно одно отображение
$attach(k, tl: t)$, такое, что
$
  chevron.l x, attach(k, tl: t) rho_1 chevron.r^mu
  = chevron.l k x, rho_1 chevron.r
  "для всех" x in V, quad rho_1 in V'_1.
$
Это равенство является определяющим для $attach(k, tl: t)$.
#idx("отображение", "транспонированное")
#idx("транспонированное отображение")

Ясно, что $attach(k, tl: t): V'_1 -> V'$ — полулинейное отображение относительно
$mu^(-1): F_1 arrow.r.twohead.tail F$. Для любых двух полулинейных отображений
$k$ и $l$ пространства $V$ в пространство $V_1$ имеем
$
  attach(k, tl: t) = 0 <=> k = 0, quad
  attach(k, tl: t) = attach(l, tl: t) <=> k = l.
$
Если $k: V -> V_1$ и $k_1: V_1 -> V_2$ полулинейны, то их композиция
$k_1 k: V -> V_2$ тоже полулинейна и
$ attach((k_1 k), tl: t) = attach(k, tl: t) attach(k_1, tl: t). $

Пусть зафиксированы базы $frak(X)$ и $frak(Y)$ пространств $V$ и $V_1$
соответственно. Обозначим через $frak(X)'$ и $frak(Y)'$ сопряженные с ними базы
пространств $V'$ и $V'_1$. Если $A$ — матрица отображения $k$ относительно баз
$frak(X)$ и $frak(Y)$, а $B$ — матрица отображения $attach(k, tl: t)$
относительно баз $frak(Y)'$, $frak(X)'$, то
$ B^mu = attach(A, tl: t). $
В самом деле,
$
  a_(i j) = chevron.l sum_lambda a_(lambda j) y_lambda, y'_i chevron.r
  = chevron.l k x_j, y'_i chevron.r
  = chevron.l x_j, attach(k, tl: t) y'_i chevron.r^mu
  = \
  = chevron.l x_j, sum_lambda b_(lambda i) x'_lambda chevron.r^mu = b_(j i)^mu.
$
В частности, $k$ тогда и только тогда будет взаимно однозначным отображением
_на_, когда таково транспонированное отображение $attach(k, tl: t)$. Если
$k: V arrow.r.twohead.tail V_1$ взаимно однозначно _на_, то #source(
  101,
)$attach((k^(-1)), tl: t)$ и $(attach(k, tl: t))^(-1)$ — полулинейные
относительно $mu: F arrow.r.twohead.tail F_1$ взаимно однозначные отображения
пространства $V'$ на пространство $V'_1$, поэтому
$ attach((k^(-1)), tl: t) = (attach(k, tl: t))^(-1). $

Для произвольной коллинеации $k$ определим _контраградиентную_ к ней коллинеацию
$caron(k)$, полагая
$ caron(k) = attach(k, tl: t)^(-1). $
Ассоциированный изоморфизм полей для $caron(k)$ и $k$ одинаков, и мы имеем
диаграммы
$
  k: V arrow.r.twohead.tail V_1, quad mu: F arrow.r.twohead.tail F_1,
  quad caron(k): V' arrow.r.twohead.tail V'_1.
$
_Контраградиент_ $caron(quad)$ связан с композицией и обращением следующим
образом:
$
  caron(k_1 dots k_t) = caron(k)_1 dots caron(k)_t,
  quad caron(k^(-1)) = (caron(k))^(-1).
$
#idx("контраградиент")
#idx("контраградиентная коллинеация")
#idx("коллинеация", "контраградиентная")

Зафиксируем $V$ и рассмотрим действие контраградиента на коллинеациях
пространства $V$, т. е. на $GammaL_n (V)$. Легко видеть, что контраградиент —
это изоморфизм
$ caron(quad): GammaL_n (V) arrow.r.twohead.tail GammaL_n (V'), $
сохраняющий ассоциированные автоморфизмы поля. Он индуцирует изоморфизмы
$
  caron(quad): GL_n (V) arrow.r.twohead.tail GL_n (V'), \
  caron(quad): SL_n (V) arrow.r.twohead.tail SL_n (V'), \
  caron(quad): RL_n (V) arrow.r.twohead.tail RL_n (V').
$
Далее,
$
  upright("mat")_(frak(X)) k = A <=> upright("mat")_(frak(X)') caron(k) =
  caron(A),
$
где $frak(X)'$ — база, сопряженная с $frak(X)$, а матрица $caron(A)$
определяется для обратимой матрицы $A$ равенством
$ caron(A) = attach(A, tl: t)^(-1). $
Кроме того, для любого $k$ из $GammaL_n (V)$ и любого подпространства $U$
пространства $V$ имеем
$ caron(k) U^0 = (k U)^0. $

#source(102)Назовем изоморфизм
$caron(quad): GammaL_n (V) arrow.r.twohead.tail GammaL_n (V')$
_контраградиентным изоморфизмом_ над пространством $V$.
#idx("изоморфизм", "контраградиентный")
#idx("контраградиентный изоморфизм")

#numbered-paragraph[
  Пусть $caron(quad)$ — контраградиентный изоморфизм над пространством $V$, а
  $sigma$ — произвольный элемент из $GL_n (V)$. Тогда
  + вычетным пространством преобразования $caron(sigma)$ является $P^0$,
  + неподвижным пространством преобразования $caron(sigma)$ является $R^0$,
  + $upright("res") caron(sigma) = upright("res") sigma$,
  + $caron(quad)$ отображает множество трансвекций с пространствами
    $L subset.eq H$ на множество трансвекций с пространствами
    $H^0 subset.eq L^0$,
  + если $sigma$ — трансвекция $sigma = tau_(a,rho)$, то
    $caron(tau)_(a,rho) = tau_(rho,-tilde(a))$, где элемент $tilde(a)$ из $V''$
    определен равенством
    $chevron.l phi, tilde(a) chevron.r = chevron.l a, phi chevron.r$.
    <passage:omeara-contragredient-transvection-sign>
] <prop:omeara-contragredient>

#proof[
  Достаточно доказать 1)–4) с заменой $caron(sigma)$ на $attach(sigma, tl: t)$,
  а вместо 5) доказать, что $attach(tau_(a,rho), tl: t) = tau_(rho,tilde(a))$.
  Обозначим через $R_t$, $P_t$ вычетное и неподвижное пространства
  преобразования $attach(sigma, tl: t)$. Если $rho in R^0$, то для любого $x$ из
  $V$ имеем
  $
    chevron.l x, attach(sigma, tl: t) rho - rho chevron.r
    = chevron.l sigma x - x, rho chevron.r
    in chevron.l R, R^0 chevron.r = 0.
  $
  Отсюда $attach(sigma, tl: t) rho = rho$, $R^0 subset.eq P_t$. С другой
  стороны, если $rho in P_t$, то для произвольного $x$ из $V$
  $
    chevron.l sigma x - x, rho chevron.r
    = chevron.l x, attach(sigma, tl: t) rho - rho chevron.r = 0,
  $
  откуда $P_t subset.eq R^0$. Следовательно, $P_t = R^0$. Утверждение 2), а
  вместе с ним и 3) доказаны. Далее, для любых $p in P$, $rho in V'$
  $
    chevron.l p, attach(sigma, tl: t) rho - rho chevron.r
    = chevron.l sigma p - p, rho chevron.r = 0.
  $
  Поэтому $R_t subset.eq P^0$ и из соображений размерности $R_t = P^0$. Итак, мы
  доказали 1), 2) и 3). Утверждение 4) следует из 1) и 2). Докажем 5):
  $
    chevron.l x, attach(tau_(a,rho), tl: t) phi chevron.r
    = chevron.l x + (rho x) a, phi chevron.r
    = chevron.l x, phi chevron.r + chevron.l x, rho chevron.r chevron.l a, phi
    chevron.r = \
    = chevron.l x, phi chevron.r + tilde(a)(phi) chevron.l x, rho chevron.r
    = chevron.l x, phi + tilde(a)(phi) rho chevron.r
    = chevron.l x, tau_(rho,tilde(a)) phi chevron.r.
  $
  Предложение полностью доказано.
]

Так как контраградиентный изоморфизм отображает $RL_n (V)$ на $RL_n (V')$, то
можно определить изоморфизм
$ caron(quad): PGammaL_n (V) arrow.r.twohead.tail PGammaL_n (V'), $
#source(103)полагая
$
  caron(overline(k)) = overline(caron(k)) "для всех" overline(k) "из"
  PGammaL_n (V).
$
Мы будем называть его _проективным контраградиентным изоморфизмом_ над
пространством $V$. Ясно, что он индуцирует изоморфизмы
$
  caron(quad): PGL_n (V) arrow.r.twohead.tail PGL_n (V'), \
  caron(quad): PSL_n (V) arrow.r.twohead.tail PSL_n (V')
$
и отображает проективные трансвекции с пространствами $L subset.eq H$ на
проективные трансвекции с пространствами $H^0 subset.eq L^0$. Если $S$ —
произвольное подмножество из $PGammaL_n (V)$, то $caron(S)$ имеет обычный
функциональный смысл, т. е. $caron(S) = brace(caron(s) | s in S)$.
#idx("изоморфизм", "проективный контраградиентный")
#idx("проективный контраградиентный изоморфизм")
