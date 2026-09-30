#import "main-defs.typ": *
#import "statements.typ": *

=== Основная теорема проективной геометрии <sec:omeara-projective-geometry>

#numbered-paragraph[
  Пусть $pi$ — взаимно однозначное отображение множества прямых пространства $V$
  на множество прямых пространства $V_1$, т. е.
  $pi: P^1 (V) arrow.r.twohead.tail P^1 (V_1)$. Если
  $ L_1 subset.eq L_2 + L_3 <=> pi L_1 subset.eq pi L_2 + pi L_3 $
  для всех $L_1$, $L_2$, $L_3$ из $P^1 (V)$, то $pi$ единственным образом
  продолжается до проективности $Pi: P(V) arrow.r.twohead.tail P(V_1)$.
] <prop:omeara-projectivity-extension>

#proof[
  Единственность следует из @prop:omeara-projectivity-preservation. Докажем
  существование. Легко проверить индукцией по $r$, что
  $ L subset.eq L_1 + dots + L_r <=> pi L subset.eq pi L_1 + dots + pi L_r. $
  Положим $Pi 0 = 0$. Произвольное ненулевое подпространство $U$ из $P(V)$
  разложим в сумму прямых
  $ U = L_1 + dots + L_r $
  и положим
  $ Pi U = pi L_1 + dots + pi L_r. $
  Ясно, что $Pi$ — корректно определенное взаимно однозначное отображение
  множества $P(V)$ на множество $P(V_1)$, сохраняющее порядок и индуцирующее
  $pi$ на прямых.
]

#source(92)
#numbered-paragraph[
  Пусть $pi: P(V) arrow.r.twohead.tail P(V_1)$ — такое взаимно однозначное
  отображение _на_, что
  $ U subset.eq W => pi U subset.eq pi W. $
  Если $dim_F V = dim_(F_1) V_1$, то $pi$ — проективность.
] <prop:omeara-projectivity-order>

#proof[
  Включив произвольное подпространство пространства $V$ в строго возрастающую
  цепочку из $n + 1$ подпространств, мы видим, что $pi$ сохраняет размерность.
  Докажем, что
  $ pi U subset.eq pi W => U subset.eq W. $
  Пусть $pi W = pi U plus.o pi T$. Тогда
  $ pi(U inter T) subset.eq pi U inter pi T = 0. $
  Следовательно, $U inter T = 0$, $U + T = U plus.o T$ и
  $ pi(U plus.o T) supset.eq pi U plus.o pi T = pi W. $
  Из размерностных соображений $pi(U plus.o T) = pi W$, откуда
  $U subset.eq U plus.o T = W$.
]

#numbered-paragraph[
  Пусть $pi$ — взаимно однозначное отображение множества прямых пространства $V$
  на множество прямых пространства $V_1$. Предположим, что
  $dim_F V = dim_(F_1) V_1$ и
  $ L_1 subset.eq L_2 + L_3 => pi L_1 subset.eq pi L_2 + pi L_3. $
  Тогда $pi$ можно однозначно продолжить до проективности
  $Pi: P(V) arrow.r.twohead.tail P(V_1)$.
] <prop:omeara-projectivity-one-sided>

#proof[
  1) По индукции
  $ L subset.eq L_1 + dots + L_r => pi L subset.eq pi L_1 + dots + pi L_r, $
  поэтому
  $ V = L_1 + dots + L_n => V_1 = pi L_1 + dots + pi L_n. $
  Следовательно,
  $ L_1, dots, L_r "независимы" => pi L_1, dots, pi L_r "независимы". $

  2) Положим $Pi 0 = 0$. Произвольное подпространство $U != 0$ из $P(V)$
  разложим в сумму
  $ U = L_1 + dots + L_r $
  и положим
  $ Pi U = pi L_1 + dots + pi L_r. $
  #source(93)В силу 1) $Pi$ — корректно определенное продолжение отображения
  $pi$ на $P(V)$. Очевидно, $Pi$ сохраняет $+$ и $dim$. Легко проверяется, что
  $Pi$ — отображение _на_ и
  $ U subset.eq W => Pi U subset.eq Pi W. $
  Ввиду @prop:omeara-projectivity-order остается доказать взаимную однозначность
  этого отображения, т. е. что из $Pi U = Pi W$ следует $U = W$. Достаточно
  показать, что из $Pi L subset.eq Pi W$ следует $L subset.eq W$. Но это
  действительно так, поскольку
  $
    dim(W + L) = dim Pi(W + L) = dim(Pi W + Pi L)
    = dim Pi W = dim W.
  $
]

#numbered-paragraph[
  Пусть $pi$ — взаимно однозначное отображение множества прямых пространства $V$
  на множество прямых пространства $V_1$ и $dim_F V = dim_(F_1) V_1$. Если
  существует такое фиксированное $p$ ($2 <= p <= n - 1$), что для каждого
  $p$-мерного подпространства $U$ пространства $V$ все прямые $pi L$ (где
  $L subset.eq U$) попадают в некоторое $p$-мерное подпространство пространства
  $V_1$, то $pi$ можно единственным образом продолжить до проективности
  $ Pi: P(V) arrow.r.twohead.tail P(V_1). $
] <prop:omeara-projectivity-fixed-dimension>

#proof[
  1) Если $p = 2$, то утверждение легко следует из
  @prop:omeara-projectivity-one-sided. Пусть $3 <= p <= n - 1$. Мы будем
  доказывать, что аналогичное свойство имеет место для $p - 1$ и, значит, в
  конечном счете для $p = 2$, чем все будет доказано.

  2) Для произвольного подпространства $X$ пространства $V$ обозначим через
  $X_*$ подпространство пространства $V_1$, порожденное прямыми $pi L$,
  $L subset.eq X$. Ясно, что
  $ dim X <= p => dim X_* <= p. $
  Нужно показать, что
  $ dim U = p - 1 => dim U_* <= p - 1. $
  Пусть, напротив, существует такое подпространство $U$ размерности $p - 1$, что
  $dim U_* = p$. Возьмем прямую $K subset.eq V$, для которой
  $K_* subset.eq.not U_*$. Тогда $K subset.eq.not U$, $dim(K + U) = p$ и,
  значит,
  $ dim(K + U)_* >= dim(K_* + U_*) = p + 1. $
  Противоречие.
]

#theorem[
  Если $dim_F V >= 3$, то всякая проективность пространства $V$ на пространство
  $V_1$ является проективной коллинеацией.
] <th:omeara-projective-geometry>

#proof[
  #source(94)1) Для произвольных $a$ из $dot(V)$ и $a'$ из $dot(V)_1$ будем
  обозначать через $chevron.l a chevron.r$ и $chevron.l a' chevron.r$ прямые
  $F a$ и $F a'$ соответственно. Пусть задана проективность
  $pi: P(V) arrow.r.twohead.tail P(V_1)$ пространства $V$ на $V_1$. Зафиксируем
  базу $x_1, dots, x_n$ пространства $V$. Очевидно, существует такая база
  $x'_1, dots, x'_n$ пространства $V_1$, что
  $
    pi chevron.l x_i chevron.r = chevron.l x'_i chevron.r, quad 1 <= i <= n, \
    pi chevron.l x_1 + x_i chevron.r = chevron.l x'_1 + x'_i chevron.r,
    quad 2 <= i <= n.
  $

  2) Так как $pi$ — проективность, то каждый элемент $alpha$ из $F$ определяет
  такой элемент $alpha'$ из $F_1$, что $pi chevron.l x_1 + alpha x_2 chevron.r =
  chevron.l x'_1 + alpha' x'_2 chevron.r$. Ясно, что $0 = 0'$, $1 = 1'$ и из
  $alpha' = beta'$ следует $alpha = beta$. Таким образом, мы имеем взаимно
  однозначное отображение (очевидно, _на_)
  $ ': F arrow.r.twohead.tail F_1. $

  3) Докажем, что $pi chevron.l x_1 + alpha x_i chevron.r =
  chevron.l x'_1 + alpha' x'_i chevron.r$ для $2 <= i <= n$. В силу 2)
  существует такое отображение $tilde(quad): F arrow.r.twohead.tail F_1$, что
  $pi chevron.l x_1 + alpha x_i chevron.r =
  chevron.l x'_1 + tilde(alpha) x'_i chevron.r$, $tilde(0) = 0$ и
  $tilde(1) = 1$. Далее,
  $
    chevron.l alpha x_2 - alpha x_i chevron.r subset.eq
    cases(
      chevron.l x_2 chevron.r + chevron.l x_i chevron.r,
      chevron.l x_1 + alpha x_2 chevron.r + chevron.l x_1 + alpha x_i chevron.r
    ),
  $
  поэтому
  $
    pi chevron.l alpha x_2 - alpha x_i chevron.r subset.eq
    cases(
      chevron.l x'_2 chevron.r + chevron.l x'_i chevron.r,
      chevron.l x'_1 + alpha' x'_2 chevron.r
      + chevron.l x'_1 + tilde(alpha) x'_i chevron.r
    ).
  $
  Отсюда $pi chevron.l alpha x_2 - alpha x_i chevron.r =
  chevron.l alpha' x'_2 - tilde(alpha) x'_i chevron.r$. В частности,
  $pi chevron.l x_2 - x_i chevron.r = chevron.l x'_2 - x'_i chevron.r$. Но
  $pi chevron.l alpha x_2 - alpha x_i chevron.r =
  pi chevron.l x_2 - x_i chevron.r$, значит, $alpha' = tilde(alpha)$.

  4) Заметим, что
  $
    pi chevron.l x_1 + alpha_2 x_2 + dots + alpha_n x_n chevron.r =
    chevron.l x'_1 + alpha'_2 x'_2 + dots + alpha'_n x'_n chevron.r.
  $
  В самом деле,
  $
    pi chevron.l x_1 + alpha_2 x_2 + dots + alpha_n x_n chevron.r =
    chevron.l x'_1 + *_2 x'_2 + dots + *_n x'_n chevron.r
  $
  и
  $
    pi chevron.l x_1 + alpha_2 x_2 + dots + alpha_n x_n chevron.r subset.eq
    chevron.l x'_1 + alpha'_i x'_i chevron.r
    + chevron.l x'_2 chevron.r + dots + chevron.l x'_n chevron.r,
  $
  где $chevron.l x'_i chevron.r$ пропущено. Отсюда $*_i = alpha'_i$.

  5) Имеем также
  $
    pi chevron.l alpha_2 x_2 + dots + alpha_n x_n chevron.r =
    chevron.l alpha'_2 x'_2 + dots + alpha'_n x'_n chevron.r.
  $
  #source(95)В самом деле,
  $
    pi chevron.l alpha_2 x_2 + dots + alpha_n x_n chevron.r =
    chevron.l *_2 x'_2 + dots + *_n x'_n chevron.r
  $
  и
  $
    pi chevron.l alpha_2 x_2 + dots + alpha_n x_n chevron.r subset.eq
    chevron.l x'_1 + alpha'_2 x'_2 + dots + alpha'_n x'_n chevron.r
    + chevron.l x'_1 chevron.r,
  $
  откуда $*_i = alpha'_i$.

  6) Взаимно однозначное отображение $': F arrow.r.twohead.tail F_1$ поля $F$ на
  поле $F_1$ в действительности является изоморфизмом полей. В самом деле,
  $
    chevron.l x'_1 + (alpha + beta)' x'_2 + x'_3 chevron.r
    = pi chevron.l x_1 + (alpha + beta) x_2 + x_3 chevron.r subset.eq \
    subset.eq chevron.l x'_1 + alpha' x'_2 chevron.r
    + chevron.l beta' x'_2 + x'_3 chevron.r,
  $
  поэтому $(alpha + beta)' = alpha' + beta'$. С другой стороны,
  $
    chevron.l x'_1 + (alpha beta)' x'_2 + beta' x'_3 chevron.r
    = pi chevron.l x_1 + alpha beta x_2 + beta x_3 chevron.r subset.eq \
    subset.eq chevron.l x'_1 chevron.r + chevron.l alpha' x'_2 + x'_3 chevron.r,
  $
  поэтому $(alpha beta)' = alpha' beta'$.

  7) Имея в виду @prop:omeara-semilinear-basis, определим коллинеацию
  $k: V arrow.r.twohead.tail V_1$ относительно изоморфизма $'$ следующим
  равенством:
  $
    k(alpha_1 x_1 + dots + alpha_n x_n) =
    (alpha'_1 x'_1 + dots + alpha'_n x'_n).
  $
  Легко убедиться, что $overline(k)$ и $pi$ совпадают на прямых. Поэтому
  $pi = overline(k)$, т. е. $pi$ — проективная коллинеация. Теорема доказана.
]
