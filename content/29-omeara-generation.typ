#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/omeara-transvections.typ": (
  generation-intersecting, generation-nested, large-dilatation,
)

== Теоремы о порождении <ch:omeara-generation>
=== Порождение трансвекциями <sec:omeara-generation>

#theorem[
  При $n >= 2$ группа $SL_n (F)$ порождается элементарными матрицами. При
  $n >= 2$ группа $SL_n (V)$ порождается элементарными трансвекциями
  относительно любой заданной базы. Группа $GL_n (V)$ порождается трансвекциями
  и дилатациями.
] <th:omeara-elementary-generation>

#proof[
  Первая часть доказывается общеизвестными манипуляциями над строками и
  столбцами. Вторая следует из первой в силу матричного изоморфизма. Третья
  следует из второй, если учесть, что каждый элемент из $dot(F)$ является
  определителем некоторой дилатации. Теорема доказана.
]

В этой главе нас будет интересовать вопрос о наименьшем числе трансвекций,
необходимом для представления заданного $sigma$ из $SL_n (V)$ в виде
произведения трансвекций. В действительности мы рассмотрим более общий случай,
когда $sigma in GL_n (V)$. Такой элемент $sigma$ является произведением
$ sigma = tau_1 dots tau_k Sigma_0, $
где $tau_i$ — трансвекции, а $Sigma_0$ — трансвекция или дилатация в зависимости
от того, лежит ли $sigma$ в $SL_n (V)$ или нет. Другими словами, каждое
$sigma != 1_V$ может быть представлено как произведение нескольких трансвекций —
скажем, $k$ штук — и элемента с вычетом $1$, и мы хотим найти зависимость числа
$k$ #source(72)от $sigma$. Равенство
$
  tau_1 dots tau_i Sigma tau_(i+1) dots tau_k
  = tau_1 dots tau_i tau_(i+1) (tau_(i+1)^(-1) Sigma tau_(i+1)) dots tau_k
$
показывает, что в этом рассмотрении несущественно, где в произведении находится
элемент $Sigma$ вычета $1$, — он может изменяться, но все $tau_i$ остаются
прежними.

#numbered-paragraph[
  Если преобразование $sigma$ из $GL_n (V)$ представлено в виде
  $ sigma = sigma_1 dots sigma_t, $
  где $sigma_i in GL_n (V)$, $upright("res") sigma_i = 1$ для $1 <= i <= t$, то
  $t >= upright("res") sigma$. Если $t = upright("res") sigma$, то
  $ R = R_1 + dots + R_t, quad P = P_1 inter dots inter P_t. $
] <prop:omeara-generation-residue-bound>

#proof[
  Ввиду @prop:omeara-residue-product $upright("res") sigma <= t$, и первое
  утверждение доказано. Допустим, что $upright("res") sigma = t$. Положим
  $ sigma'_i = sigma_1 dots sigma_i $
  для $1 <= i <= t$. Имеем $upright("res") sigma'_i <= i$. Если бы было
  $upright("res") sigma'_i < i$, то получили бы $upright("res") sigma'_t < t$,
  что противоречит предположению, поэтому $upright("res") sigma'_i = i$ для
  $1 <= i <= t$. Утверждается, что
  $ R'_i = R_1 + dots + R_i, quad P'_i = P_1 inter dots inter P_i $
  для $1 <= i <= t$. (Этим, конечно, предложение будет доказано.) При $i = 1$
  доказывать нечего. Перейдем от $i$ к $i + 1$. Так как
  $sigma'_(i+1) = sigma'_i sigma_(i+1)$, то $R'_(i+1) subset.eq R'_i + R_(i+1)$,
  поэтому из размерностных соображений $R'_(i+1) = R'_i + R_(i+1)$, т. е. для
  вычетных пространств утверждение доказано. Сравнивая размерности в равенстве
  $R'_(i+1) = R'_i + R_(i+1)$, получаем, что $R'_i inter R_(i+1) = 0$. Отсюда в
  силу @prop:omeara-residue-product-equality $P'_(i+1) = P'_i inter P_(i+1)$, т.
  е. и для неподвижных пространств утверждение доказано.
]

Пусть $U$ — подпространство пространства $V$. Поставим ему в соответствие
подгруппу
$ G(U) = brace(sigma in GL_n (V) | P supset.eq U), $
т. е.
$ G(U) = brace(sigma in GL_n (V) | sigma x = x "для всех" x in U). $
Рассмотрим векторное пространство $V \/ U$ над $F$. Напомним (из линейной
алгебры) смысл этого понятия: берутся аддитивные группы $V$, $U$, $V \/ U$ и
естественный аддитивный гомоморфизм
$ tilde(quad): V -> V \/ U, $
#source(73)затем определяется $alpha tilde(x)$ по правилу
$
  alpha tilde(x) = tilde(alpha x) "для всех" alpha in F "и всех" tilde(x) in V
  \/ U.
$
Это превращает $tilde(quad)$ в $F$-линейное отображение, так что
$ dim V \/ U + dim U = dim V. $
Для каждого $sigma$ из $G(U)$ определяется отображение $tilde(sigma)$
пространства $V \/ U$ на себя по правилу
$ tilde(sigma) tilde(x) = tilde(sigma x) "для всех" tilde(x) in V \/ U. $
Заметим, что преобразование $tilde(sigma)$ является $F$-линейным, лежит в
$GL_r (V \/ U)$, $det tilde(sigma) = det sigma$,
$tilde(sigma_1 sigma_2) = tilde(sigma)_1 tilde(sigma)_2$ и всякий элемент из
$GL_r (V \/ U)$ имеет вид $tilde(sigma)$. Другими словами, естественный
гомоморфизм
$ tilde(quad): V -> V \/ U $
определяет отображение
$ tilde(quad): G(U) -> GL_r (V \/ U), $
которое сохраняет определитель и является гомоморфизмом _на_. Будем называть эти
два отображения _тильда-отображениями, сопровождающими редукцию по модулю_ $U$.
#idx("тильда-отображение")
Ясно, что если $sigma$ — элемент из $GL_n (V)$, для которого $P supset.eq U$, то
вычетное пространство элемента $tilde(sigma)$ равно $tilde(R)$. В частности,
$
  upright("res") tilde(sigma) <= upright("res") sigma, \
  upright("res") tilde(sigma) = upright("res") sigma <=> R inter U = 0
$
и
$ tilde(sigma) = 1_(V \/ U) <=> R subset.eq U. $

Элемент $sigma$ из $GL_n (V)$ будем называть _большой дилатацией_, если
существует такое разложение $V = U plus.o W$, что $W != 0$ и
$sigma = (1_U) plus.o (alpha 1_W)$ для некоторого $alpha != 1$. Большую
дилатацию можно нарисовать так:
#align(center, large-dilatation())
#idx("дилатация", "большая")
#idx("большая дилатация")

#source(74)Если $sigma$ — большая дилатация и, как выше,
$sigma = (1_U) plus.o (alpha 1_W)$, то в силу @exm:omeara-residue-product
$ R = W, quad P = U. $
Заметим, что каждая дилатация является большой дилатацией, однако не каждая
большая дилатация является дилатацией. Нетривиальное растяжение является большой
дилатацией, а $1_V$ — нет. Большая дилатация может лежать в $SL_n (V)$.

#numbered-paragraph[
  Пусть $sigma$ — неединичный элемент из $GL_n (V)$ и $tilde(quad)$ является
  тильда-отображением, сопровождающим редукцию по модулю неподвижного
  пространства $P$ элемента $sigma$. Тогда равносильны следующие утверждения:
  + $sigma$ — большая дилатация,
  + $tilde(sigma)$ — нетривиальное растяжение,
  + $sigma |_R$ — нетривиальное растяжение.
] <prop:omeara-large-dilatation-characterization>

#proof[
  1) $=>$ 2). Имеем $V = U plus.o W$, где $W != 0$,
  $sigma = (1_U) plus.o (alpha 1_W)$ для некоторого скаляра $alpha != 0, 1$.
  Кроме того, $P = U$ и $R = W$. Тогда
  $
    tilde(sigma) tilde(w) = tilde(sigma w) = tilde(alpha w) = alpha tilde(w)
    "для всех" w in W.
  $
  Так как $tilde(w)$ — произвольный элемент из $V \/ P$, то $tilde(sigma)$ —
  нетривиальное растяжение $alpha 1_(V \/ P)$.

  2) $=>$ 3). Пусть $tilde(sigma)$ — нетривиальное растяжение. Тогда
  $
    upright("res") tilde(sigma) = dim V \/ P = dim V - dim P
    = upright("res") sigma,
  $
  поэтому $R inter P = 0$ и, следовательно, $V = P plus.o R$. Пусть
  $tilde(sigma) = alpha 1_(V \/ P)$, где $alpha$ — скаляр $!= 0, 1$. Для
  произвольного $r$ из $R$ имеем $tilde(sigma) tilde(r) = alpha tilde(r)$,
  откуда $sigma r - alpha r in P$. Но $sigma R = R$, поэтому
  $sigma r - alpha r in R$. Значит, $sigma r - alpha r in R inter P = 0$.
  Окончательно, $sigma |_R = alpha 1_R$.

  3) $=>$ 1). Ясно, что $R inter P = 0$, поэтому $V = P plus.o R$ и
  $sigma = (1_P) plus.o (alpha 1_R)$ для некоторого скаляра $alpha != 0, 1$.
  Предложение доказано.
]

#numbered-paragraph[
  Пусть $sigma$ — большая дилатация, а $tau$ — нетривиальная трансвекция с
  вычетной прямой $L$ и неподвижной гиперплоскостью $H$. Если $H supset.eq P$ и
  $L subset.eq.not P$, то $tau sigma$ не является большой дилатацией.
] <prop:omeara-large-dilatation-transvection>

#proof[
  Пусть, напротив, $sigma_1 = tau sigma$ — большая дилатация. Пусть
  $tilde(quad)$ обозначает тильда-отображение, #source(75)сопровождающее
  редукцию по модулю $P$. Элементы $sigma_1$, $sigma$, $tau$ лежат в $G(P)$,
  поэтому к ним можно применить тильда-отображение. Мы знаем, что $tilde(tau)$ —
  нетривиальная трансвекция, так как $L inter P = 0$. Ввиду
  @prop:omeara-large-dilatation-characterization $tilde(sigma)$ — нетривиальное
  растяжение, причем существует такой скаляр $alpha != 0, 1$, что
  $sigma_1 r_1 = alpha r_1$ для всех $r_1 in R_1$. Значит,
  $tilde(sigma)_1 |_(tilde(R)_1) = alpha 1_(tilde(R)_1)$. Но $R_1 != 0$ и
  $R_1 inter P_1 = 0$, так как $sigma_1$ — большая дилатация. В частности,
  $R_1 inter P = 0$, где $R_1 != 0$, откуда $tilde(R)_1 != 0$. Поскольку
  $tilde(R)_1$ — вычетное пространство элемента $tilde(sigma)_1$ и
  $tilde(sigma)_1 |_(tilde(R)_1)$ — нетривиальное растяжение, то из
  @prop:omeara-large-dilatation-characterization следует, что $tilde(sigma)_1$ —
  большая дилатация. Равенство $tilde(sigma)_1 = tilde(tau) tilde(sigma)$
  показывает, что нетривиальная трансвекция $tilde(tau)$ является произведением
  большой дилатации и нетривиального растяжения, что невозможно (рассмотреть
  характеристические корни).
]

#numbered-paragraph[
  Любое нетривиальное преобразование $sigma$ из $GL_n (V)$, не являющееся
  большой дилатацией, можно представить в виде произведения линейного
  преобразования с вычетом $1$ и $(upright("res") sigma) - 1$ трансвекций.
] <prop:omeara-generation-not-large-dilatation>

#proof[
  1) Индукция по $r = upright("res") sigma$. Если $r = 1$, то доказывать нечего.
  Пусть $r > 1$ и предложение доказано для всех $sigma$ с вычетом
  $upright("res") sigma < r$. Докажем его для элемента $sigma$ с вычетом
  $upright("res") sigma = r$. Ясно, что $P subset V$, поскольку
  $dim P = n - r <= n - 2$.

  2) Предположим сначала, что $R subset.eq P$. Зафиксируем $b in V - P$. Пусть
  $H$ — гиперплоскость, содержащая $P$, но не содержащая $b$. Тогда $sigma b$ и
  $b$ — различные векторы в $V$, причем $b - sigma b$ лежит в $H$, а $sigma b$ —
  нет, поэтому, согласно
  #align(center, generation-nested())
  @prop:omeara-transvection-vector-action, существует трансвекция $tau$ с
  неподвижной гиперплоскостью $H$ и вычетной прямой $F(b - sigma b)$, такая, что
  $tau sigma b = b$. Неподвижное пространство элемента $tau sigma$ содержит
  $P + F b$, поэтому $upright("res") tau sigma <= r - 1$. Так как
  $sigma = tau^(-1) (tau sigma)$, то ввиду @prop:omeara-residue-product #source(
    76,
  )получаем равенство $upright("res") tau sigma = r - 1$. Следовательно,
  неподвижное пространство элемента $tau sigma$ — это в точности $P + F b$. Но
  $ F(b - sigma b) + R = R subset.eq P subset.eq P + F b, $
  поэтому вычетное пространство элемента $tau sigma$ содержится в его
  неподвижном пространстве, в частности, ввиду
  @prop:omeara-large-dilatation-characterization $tau sigma$ не является большой
  дилатацией. Остается применить индукцию к $tau sigma$.

  3) Предположим теперь, что $R subset.eq.not P$. Пусть $tilde(quad)$ обозначает
  тильда-отображение, сопровождающее редукцию по модулю $P$. Ввиду
  @prop:omeara-large-dilatation-characterization элемент $tilde(sigma)$ не
  является нетривиальным растяжением, а так как $R subset.eq.not P$, то он
  отличен и от $1_(V \/ P)$. Таким образом, $tilde(sigma)$ вообще не является
  растяжением. Согласно @prop:omeara-dilatation-lines, существует элемент $b$ из
  $V$, для которого $sigma b in.not P + F b$. Отсюда
  $ sigma b - b in.not P + F b, quad b in.not P + F(sigma b - b). $
  Значит, можно найти гиперплоскость $H$, которая содержит $P + F(sigma b - b)$,
  но не содержит $b$. Ввиду @prop:omeara-transvection-vector-action существует
  трансвекция $tau$ с неподвижной гиперплоскостью $H$ и вычетной прямой
  $F(b - sigma b)$, такая, что $tau sigma b = b$. Рассуждая, как
  #align(center, generation-intersecting())
  в пункте 2), найдем, что $upright("res") tau sigma = r - 1$ и неподвижное
  пространство элемента $tau sigma$ есть в точности $P + F b$. Если $tau sigma$
  не является большой дилатацией, то применяем индукцию. Если $r = 2$, то все
  доказано. Предположим поэтому, что $tau sigma$ — большая дилатация и $r >= 3$.
  Тогда $dim P <= n - 3$ и существует гиперплоскость $H_1$, для которой
  $ H_1 supset.eq P + F b + F(b - sigma b). $
  Пусть $tau_1$ — трансвекция с неподвижной гиперплоскостью $H_1$ и вычетной
  прямой $F(b - sigma b)$. Неподвижное пространство преобразования
  $tau_1 tau sigma$ содержит $P + F b$, причем $T = tau_1 tau$ — транс#source(
    77,
  )векция, так как $tau_1$ и $tau$ имеют общую вычетную прямую, и ввиду
  @prop:omeara-large-dilatation-transvection $T sigma = tau_1 (tau sigma)$ не
  является большой дилатацией. Остается применить индукцию к $T sigma$.
]

#numbered-paragraph[
  Каждая большая дилатация $sigma$ из $GL_n (V)$, для которой
  $upright("res") sigma >= 2$, представима в виде произведения линейного
  преобразования с вычетом $1$ и $upright("res") sigma$ трансвекций, причем
  меньшего числа трансвекций недостаточно.
] <prop:omeara-generation-large-dilatation>

#proof[
  1) Сначала докажем, что при $n >= 2$ нетривиальное растяжение нельзя
  представить в виде $sigma = sigma_1 dots sigma_n$, где
  $upright("res") sigma_i = 1$ для $1 <= i <= n$ и $det sigma_i = 1$ для
  $2 <= i <= n$. Пусть, напротив, такое представление существует. Положим
  $sigma_0 = sigma_1 dots sigma_(n-1)$. Таким образом,
  $sigma = sigma_0 sigma_n$. В частности, $upright("res") sigma_0 = n - 1$ и
  $P_0$ — прямая. Так как $upright("res") sigma = n$, то $P_0 inter P_n = 0$,
  откуда $V = P_0 plus.o P_n$. Очевидно, $sigma_0 |_(P_0) = 1_(P_0)$. Равенство
  $sigma_0 = sigma sigma_n^(-1)$ показывает, что
  $sigma_0 |_(P_n) = alpha 1_(P_n)$, так что $sigma_0$ — большая дилатация.
  Следовательно, трансвекция $sigma_n$ является произведением
  $sigma_n = sigma_0^(-1) sigma$ большой дилатации и растяжения. Рассмотрение
  характеристических корней приводит к противоречию.

  2) Теперь докажем, что большую дилатацию $sigma$ с $upright("res") sigma >= 2$
  нельзя представить в виде $sigma = sigma_1 dots sigma_r$, где
  $upright("res") sigma = r$, $upright("res") sigma_i = 1$ для $1 <= i <= r$ и
  $det sigma_i = 1$ для $2 <= i <= r$. Пусть, напротив, такое представление
  существует. Тогда ввиду @prop:omeara-generation-residue-bound
  $P = P_1 inter dots inter P_r$. В частности, $P subset.eq P_i$ для
  $1 <= i <= r$. Применяя тильда-отображение, сопровождающее редукцию по модулю
  $P$, получим $tilde(sigma) = tilde(sigma)_1 dots tilde(sigma)_r$. Мы знаем из
  @prop:omeara-large-dilatation-characterization, что $tilde(sigma)$ —
  нетривиальное растяжение $r$-мерного векторного пространства $V \/ P$, где
  $r >= 2$. Но $upright("res") tilde(sigma)_i <= 1$, поэтому
  $upright("res") tilde(sigma)_i = 1$ для $1 <= i <= r$ и
  $det tilde(sigma)_i = 1$ для $2 <= i <= r$. Это противоречит пункту 1).

  3) Вторая часть предложения следует из пункта 2). Докажем первую часть. Так
  как $dim P <= n - 2$, то можно выбрать прямую $L$ и гиперплоскость $H$ так,
  чтобы было $H supset.eq P + L$, $L subset.eq.not P$. Согласно
  @prop:omeara-transvection-spaces-existence, существует трансвекция $tau$ с
  вычетной прямой $L$ и неподвижной гиперплоскостью $H$. В силу
  @prop:omeara-large-dilatation-transvection $tau sigma$ не является большой
  дилатацией. Неподвижное пространство преобразования $tau sigma$ содержит $P$,
  а потому $upright("res") tau sigma <= upright("res") sigma$, следовательно,
  либо $upright("res") tau sigma = upright("res") sigma$, либо
  $upright("res") tau sigma = (upright("res") sigma) - 1$. Ввиду
  @prop:omeara-generation-not-large-dilatation элемент $tau sigma$ является
  произведением линейного преобразования с вычетом $1$ и
  $(upright("res") sigma) - 1$ или $(upright("res") sigma) - 2$ трансвекций, но
  последнее невозможно в силу второй части нашего предложения и равенства
  $sigma = tau^(-1) (tau sigma)$. Следовательно, верно первое, т. е. $sigma$
  является произведением линейного преобразования с вычетом $1$ и
  $upright("res") sigma$ трансвекций. Предложение доказано.
]

#source(78)
#theorem[
  Каждое нетривиальное преобразование $sigma$ из $GL_n (V)$ является
  произведением $upright("res") sigma$ линейных преобразований с вычетом $1$.
  Никакое $sigma$ из $GL_n (V)$ не разлагается в произведение менее чем
  $upright("res") sigma$ линейных преобразований с вычетом $1$.
] <th:omeara-generation-residue>

#numbered-paragraph[
  *Теорема.* Каждое нетривиальное преобразование $sigma$ из $SL_n (V)$, не
  являющееся большой дилатацией, представимо в виде произведения
  $upright("res") sigma$ трансвекций. Большая дилатация $sigma$ из $SL_n (V)$
  представима в виде произведения $(upright("res") sigma) + 1$ трансвекций,
  причем это число нельзя уменьшить. Никакое $sigma$ из $SL_n (V)$ не
  разлагается в произведение менее чем $upright("res") sigma$ трансвекций.
] <prop:omeara-generation-2-1-8>
