#import "main-defs.typ": *
#import "statements.typ": *

=== Теоремы об изоморфизмах над областями целостности
<sec:omeara-domain-isomorphisms>

Рассмотрим теперь произвольную коммутативную область целостности $frak(o)$ с
полем частных $F$. Аналогично, пусть $frak(o)_1$ — область целостности с полем
частных $F_1$.

#idx("дробный идеал")
#idx("идеал")
#idx("идеал дробный")
Под _(дробным) идеалом_ относительно области $frak(o)$ мы подразумеваем
ненулевое подмножество $frak(a)$ поля $F$, являющееся $frak(o)$-модулем и
удовлетворяющее условию $lambda frak(a) subset.eq frak(o)$ для некоторого
#source(155)ненулевого
$lambda in frak(o)$. <passage:omeara-nonzero-fractional-ideal> Здесь
$lambda frak(a)$ обозначает $frak(o)$-модуль
$ lambda frak(a) = brace(lambda x | x in frak(a)). $
Очевидно, что $alpha frak(o)$ — дробный идеал при любом $alpha in dot(F)$.
#idx("главный идеал")
#idx("идеал главный")
Всякий дробный идеал, который можно записать в виде $alpha frak(o)$ для
некоторого $alpha in dot(F)$, будем называть _главным_ идеалом. Если $frak(a)$ —
дробный идеал, то и $alpha frak(a)$ — дробный идеал для любого
$alpha in dot(F)$. Каждый конечно порожденный ненулевой $frak(o)$-модуль,
содержащийся в $F$, является дробным идеалом. Легко видеть, что для любых двух
дробных идеалов $frak(a)$ и $frak(b)$ существует такой ненулевой элемент
$lambda in frak(o)$, что $lambda frak(a) subset.eq frak(b)$. Если $frak(o) = F$,
то $F$ — единственный дробный идеал относительно $frak(o)$.

#idx("целый идеал")
#idx("идеал целый")
_Целым идеалом_ называется дробный идеал, содержащийся в $frak(o)$. Таким
образом, целые идеалы — это обычные идеалы кольца $frak(o)$, за исключением
нулевого идеала. Всякий целый идеал удовлетворяет условию
$0 subset frak(a) subset.eq frak(o)$. Для любых двух дробных идеалов $frak(a)$ и
$frak(b)$ определим
$
  "н. о. д.:" quad frak(a) + frak(b)
  = brace(alpha + beta | alpha in frak(a) comma beta in frak(b)), \
  "н. о. к.:" quad frak(a) inter frak(b), \
  "произведение:" quad frak(a) frak(b)
  = brace(sum_("конечная") alpha beta | alpha in frak(a) comma beta in frak(b)).
$
Легко проверить, что $frak(a) + frak(b)$, $frak(a) inter frak(b)$,
$frak(a) frak(b)$ — снова дробные идеалы. Следующие тождества очевидны:
$
  frak(a) (frak(b) + frak(c)) = frak(a) frak(b) + frak(a) frak(c), quad
  (alpha frak(a)) (beta frak(b)) = (alpha beta) (frak(a) frak(b)), \
  frak(a) (frak(b) frak(c)) = (frak(a) frak(b)) frak(c), quad
  frak(a) frak(b) = frak(b) frak(a), quad frak(a) frak(o) = frak(a).
$
Под $frak(o)$-модулем $M$ _в_ векторном пространстве $V$ мы подразумеваем
подмножество $M$ в $V$, являющееся $frak(o)$-модулем. Мы говорим, что
$frak(o)$-модуль $M$ является модулем _на_ $V$, если он порождает $V$ над $F$.
Легко видеть, что если $M$ — модуль в $V$, то он является модулем на $V$ тогда и
только тогда, когда он содержит базу пространства $V$.

Рассмотрим $frak(o)$-модуль $M$ в $V$. Положим
$ F M = brace(alpha x | alpha in F comma x in M). $
Очевидно,
$ F M = brace(alpha^(-1) x | alpha in frak(o) comma alpha != 0 comma x in M), $
так как $F$ — поле частных для $frak(o)$. Следовательно, $F M$ — подпространство
пространства $V$, точнее, подпространство, порожденное модулем $M$. Таким
образом, $M$ есть модуль на $V$ тогда и только тогда, когда $F M = V$.

#source(156)Для любых $alpha in F$, дробного идеала $frak(a)$ и модуля $M$ в $V$
определим
$
  alpha M = brace(alpha x | x in M), \
  frak(a) M = brace(sum_("конечная") beta x | beta in frak(a) comma x in M).
$
Как $alpha M$, так и $frak(a) M$ — снова модули в $V$, а на самом деле в $F M$.
Легко проверить, что выполняются следующие тождества:
$
  alpha (M inter N) = (alpha M) inter (alpha N), quad
  alpha (M + N) = alpha M + alpha N, \
  alpha (frak(a) M) = (alpha frak(a)) M = frak(a) (alpha M), \
  (frak(a) + frak(b)) M = frak(a) M + frak(b) M, quad
  (frak(a) frak(b)) M = frak(a) (frak(b) M), \
  frak(a) (M + N) = frak(a) M + frak(a) N, \
  F(M + N) = F M + F N.
$
Подмножество векторов из $V$ независимо над $frak(o)$ тогда и только тогда,
когда оно независимо над $F$. В частности, $frak(o)$-модуль $M$ на $V$ свободен
тогда и только тогда, когда существует такая база $x_1$, …, $x_n$ пространства
$V$, что $M = frak(o) x_1 + dots + frak(o) x_n$.

#idx("ограниченный модуль")
#idx("модуль ограниченный")
Будем говорить, что $frak(o)$-модуль $M$ на $V$ _ограничен_, если он содержится
в свободном $frak(o)$-модуле на $V$. Таким образом, свободные $frak(o)$-модули
на $V$ ограничены. Кроме того, всякий ограниченный модуль на $V$ содержит
некоторый свободный модуль на $V$ и содержится в некотором свободном модуле на
$V$. Подмодуль ограниченного модуля ограничен, если он является модулем на $V$.

#numbered-paragraph[
  Пусть $M$ и $N$ суть $frak(o)$-модули на $V$, причем $N$ свободен. Модуль $M$
  ограничен тогда и только тогда, когда $alpha M subset.eq N$ для некоторого
  ненулевого $alpha in frak(o)$.
] <prop:omeara-bounded-free-module>

#proof[
  Если $alpha M subset.eq N$, то $M$ содержится в свободном модуле
  $alpha^(-1) N$, поэтому $M$ ограничен. Обратно, предположим, что $M$
  ограничен. Тогда $M subset.eq P$, где модуль $P$ свободен на $V$. Возьмем
  базы, в которых
  $
    N = frak(o) x_1 + dots + frak(o) x_n, quad
    P = frak(o) y_1 + dots + frak(o) y_n,
  $
  и запишем
  $ y_j = sum_(i=1)^n a_(i j) x_i, quad a_(i j) in F. $
  Пусть $alpha$ — произведение всех знаменателей элементов $a_(i j)$. Тогда
  $alpha$ — ненулевой элемент из $frak(o)$ и $alpha a_(i j) in frak(o)$ для всех
  $i$, $j$. #source(157)Имеем
  $ alpha M subset.eq alpha P subset.eq N. $
]

#numbered-paragraph[
  Пусть $M$ и $N$ — два $frak(o)$-модуля на $V$, причем $N$ ограничен. Модуль
  $M$ ограничен тогда и только тогда, когда $alpha M subset.eq N$ для некоторого
  ненулевого $alpha in frak(o)$.
] <prop:omeara-bounded-module-comparison>

Из приведенных результатов следует, что если $M$ и $N$ — ограниченные
$frak(o)$-модули на $V$, то
$ alpha M, quad frak(a) M, quad M inter N, quad M + N $
также ограниченные $frak(o)$-модули на $V$ для ненулевого $alpha$.
<passage:omeara-bounded-scalar-nonzero>

Для любого ограниченного $frak(o)$-модуля $M$ на $V$ и любого ненулевого
$x in V$ определим _коэффициент_ $frak(c)_x$ вектора $x$ относительно $M$ как
множество
$ frak(c)_x = brace(alpha in F | alpha x in M). $
Очевидно, $frak(c)_x x = M inter F x$. Используя
@prop:omeara-bounded-free-module, видим, что $frak(c)_x$ — дробный идеал.
<passage:omeara-vector-coefficient>

Рассмотрим ограниченный $frak(o)$-модуль $M$ на $V$. Определим линейные группы
(над областью целостности $frak(o)$)
$
  GL_n (M) = brace(sigma in GL_n (V) | sigma M = M), \
  SL_n (M) = GL_n (M) inter SL_n (V).
$
Будем говорить, что линейное преобразование $sigma$ _сохраняет_ $M$, если
$sigma in GL_n (M)$, т. е. $sigma M = M$. Для всякого ненулевого целого идеала
$frak(a)$ определим линейные конгруэнц-группы
$
  GL_n (M, frak(a)) = brace(
    sigma in GL_n (M) |
    (sigma - 1_V) M subset.eq frak(a) M
  ), \
  SL_n (M, frak(a)) = GL_n (M, frak(a)) inter SL_n (V).
$
Очевидно, $SL_n (M, frak(a))$, $GL_n (M, frak(a))$ — нормальные подгруппы в
$GL_n (M)$. Имеем
$ GL_n (M, frak(o)) = GL_n (M), quad SL_n (M, frak(o)) = SL_n (M). $
Проективные линейные группы $PGL_n (M)$, $PSL_n (M)$ и проективные линейные
конгруэнц-группы $PGL_n (M, frak(a))$, $PSL_n (M, frak(a))$ определяются как
образы относительно гомоморфизма $P$.

Если взять произвольную нетривиальную трансвекцию $tau$ и записать ее в виде
$tau_(a,rho)$, то получим
$ tau M = M <=> tau M subset.eq M <=> (rho M) a subset.eq M $
и
$ tau in SL_n (M, frak(a)) <=> (rho M) a subset.eq frak(a) M. $

#source(158)
#numbered-paragraph[
  Если $M$ — ограниченный $frak(o)$-модуль на $V$, $frak(a)$ — ненулевой целый
  идеал и $n >= 2$, то группа $SL_n (M, frak(a))$ богата трансвекциями.
] <prop:omeara-congruence-rich-transvections>

#proof[
  Для данных $a in V$, $rho in V'$, таких, что $rho a = 0$, мы должны найти
  такой элемент $lambda in F$, что $tau_(lambda a,rho)$ лежит в
  $SL_n (M, frak(a))$. Легко проверить, что $rho M$ — дробный идеал. Поэтому
  существует такой ненулевой элемент $lambda in frak(o)$, что
  $lambda (rho M) subset.eq frak(a) frak(c)_a$, где $frak(c)_a$ — коэффициент
  вектора $a$. Тогда
  $
    (rho M) (lambda a) subset.eq (lambda (rho M)) a
    subset.eq (frak(a) frak(c)_a) a subset.eq frak(a) M.
  $
  Таким образом, $tau_(lambda a,rho) in SL_n (M, frak(a))$, что и требовалось
  доказать.
]

Отсюда следует, что $SL_n (M, frak(a))$, $GL_n (M, frak(a))$ и вообще любая
подгруппа из $GammaL_n (V)$, содержащая линейную конгруэнц-группу
$SL_n (M, frak(a))$, богата трансвекциями. Аналогично, любая подгруппа из
$PGammaL_n (V)$, содержащая проективную линейную конгруэнц-группу
$PSL_n (M, frak(a))$, богата проективными трансвекциями. Значит, к таким группам
применимы все теоремы
@th:omeara-projective-isomorphisms–@prop:omeara-perfect-collineation-isomorphisms
об изоморфизмах. В частности, получаем следующие результаты.

#theorem[
  Пусть $frak(o)$ — область целостности с полем частных $F$, $M$ — ограниченный
  $frak(o)$-модуль на $V$, $frak(a)$ — ненулевой целый идеал и $Delta$ — группа,
  удовлетворяющая условию
  $ PSL_n (M, frak(a)) subset.eq Delta subset.eq PGammaL_n (V), $
  $n >= 3$. Пусть $frak(o)_1$, $F_1$, $M_1$, $V_1$, $frak(a)_1$, $Delta_1$,
  $n_1$ — второй набор объектов с аналогичными условиями. Всякий изоморфизм
  $Lambda: Delta arrow.r.double.bar Delta_1$ имеет точно одну из двух форм: либо
  $ Lambda k = g k g^(-1), quad k in Delta, $
  для некоторой единственной проективной коллинеации $g$ пространства $V$ на
  $V_1$, либо
  $ Lambda k = h caron(k) h^(-1), quad k in Delta, $
  для некоторой единственной проективной коллинеации $h$ пространства $V'$ на
  $V_1$. Кроме того, $n = n_1$, $F ≃ F_1$.
] <th:omeara-congruence-projective-isomorphisms>

#theorem[
  Пусть $frak(o)$ — область целостности с полем частных $F$, $M$ — ограниченный
  $frak(o)$-модуль на $V$, $frak(a)$ — ненулевой целый идеал, $G$ — такая
  группа, что
  $ SL_n (M, frak(a)) subset.eq G subset.eq GammaL_n (V), $
  #source(159)$n >= 3$. Пусть $frak(o)_1$, $F_1$, $M_1$, $V_1$, $frak(a)_1$,
  $G_1$, $n_1$ — второй набор объектов с аналогичными условиями. Всякий
  изоморфизм $Psi: G arrow.r.double.bar G_1$ имеет точно одну из двух форм: либо
  $ Psi k = chi(k) g k g^(-1), quad k in G, $
  где $chi$ — отображение из $G$ в $RL_(n_1) (V_1)$, $g$ — коллинеация
  пространства $V$ на $V_1$, либо
  $ Psi k = chi(k) h caron(k) h^(-1), quad k in G, $
  где $chi$ — отображение группы $G$ в $RL_(n_1) (V_1)$, $h$ — коллинеация
  пространства $V'$ на $V_1$. Кроме того, $n = n_1$, $F ≃ F_1$.
] <th:omeara-congruence-linear-isomorphisms>

Матрица порядка $n$ над полем $F$ называется _целой_ (относительно данной
области целостности $frak(o)$), если ее коэффициенты лежат в $frak(o)$, и
_унимодулярной_, если она целая и ее определитель обратим в $frak(o)$. Легко
видеть, что целая матрица $A$ унимодулярна тогда и только тогда, когда она
обратима и матрица $A^(-1)$ целая. Пусть $GL_n (frak(o))$ обозначает подгруппу
всех унимодулярных матриц из $GL_n (F)$ и
$ SL_n (frak(o)) = GL_n (frak(o)) inter SL_n (F). $
Группы $GL_n (frak(o))$ и $SL_n (frak(o))$ называются _матричными группами_ над
областью целостности $frak(o)$. Для всякого ненулевого целого идеала
#idx("матрица целая")
#idx("целая матрица")
#idx("матрица унимодулярная")
#idx("унимодулярная матрица")
$frak(a)$ определим матричные конгруэнц-группы
$
  GL_n (frak(o), frak(a)) =
  brace(X in GL_n (frak(o)) | X equiv I mod frak(a)), \
  SL_n (frak(o), frak(a)) = GL_n (frak(o), frak(a)) inter SL_n (F),
$
где сравнимость по модулю $frak(a)$ двух матриц порядка $n$ означает их
поэлементную сравнимость по модулю $frak(a)$. Очевидно, что
$SL_n (frak(o), frak(a))$ и $GL_n (frak(o), frak(a))$ — нормальные подгруппы в
$GL_n (frak(o))$. Имеем
$
  GL_n (frak(o), frak(o)) = GL_n (frak(o)), quad
  SL_n (frak(o), frak(o)) = SL_n (frak(o)).
$
Проективные матричные группы $PGL_n (frak(o))$, $PSL_n (frak(o))$ и проективные
матричные конгруэнц-группы $PGL_n (frak(o), frak(a))$,
$PSL_n (frak(o), frak(a))$ определяются как образы относительно гомоморфизма
$P$.

Предположим теперь, что $M$ — свободный модуль на $V$, скажем,
$ M = frak(o) x_1 + dots + frak(o) x_n, $
где $x_1$, …, $x_n$ — база пространства $V$. Пусть $rho_1$, …, $rho_n$ —
сопряженная база. Если линейное преобразование $sigma in GL_n (V)$ имеет в этой
базе матрицу $S$, то легко видеть, что
$ sigma M subset.eq M <=> S "целая" $
#source(160)и
$ sigma M = M <=> S "унимодулярная." $
В частности, элементарная трансвекция $tau_(lambda x_i,rho_j)$ сохраняет $M$
тогда и только тогда, когда $lambda in frak(o)$, т. е.
$ tau_(lambda x_i,rho_j) in SL_n (M) <=> lambda in frak(o). $
Так как унимодулярная матрица имеет обратимый определитель, то легко видеть, что
в свободном случае группа $GL_n (M) \/ SL_n (M)$ изоморфна группе единиц кольца
$frak(o)$. Ясно, что матричный изоморфизм, отвечающий выбору базы $x_1$, …,
$x_n$ (для $M$ и $V$), индуцирует изоморфизмы
$
  GL_n (M) arrow.r.double.bar GL_n (frak(o)), quad
  GL_n (M, frak(a)) arrow.r.double.bar GL_n (frak(o), frak(a)), \
  SL_n (M) arrow.r.double.bar SL_n (frak(o)), quad
  SL_n (M, frak(a)) arrow.r.double.bar SL_n (frak(o), frak(a)).
$
Мы уже знаем, что он индуцирует также изоморфизм групп
$ RL_n (V) arrow.r.double.bar RL_n (F), $
поэтому
$
  PGL_n (M) ≃ PGL_n (frak(o)), quad
  PGL_n (M, frak(a)) ≃ PGL_n (frak(o), frak(a)), \
  PSL_n (M) ≃ PSL_n (frak(o)), quad
  PSL_n (M, frak(a)) ≃ PSL_n (frak(o), frak(a)).
$
Следующая теорема об изоморфизмах для матричных конгруэнц-групп получается
переводом теоремы @th:omeara-congruence-linear-isomorphisms на матричный язык.
(_Вопрос:_ в какой мере справедлива единственность?)

#theorem[
  Пусть $frak(o)$ — область целостности с полем частных $F$, $frak(a)$ —
  ненулевой целый идеал, $G$ — группа, удовлетворяющая условию
  $ SL_n (frak(o), frak(a)) subset.eq G subset.eq GL_n (F), $
  и $n >= 3$. Пусть, далее, $frak(o)_1$, $F_1$, $frak(a)_1$, $G_1$, $n_1$ —
  другой набор объектов с аналогичными свойствами и
  $Psi: G arrow.r.double.bar G_1$ — изоморфизм. Тогда $n = n_1$ и
  $ Psi X = chi(X) A X^mu A^(-1), quad X in G, $
  или
  $ Psi X = chi(X) A caron(X)^mu A^(-1), quad X in G, $
  где $mu: F arrow.r.double.bar F_1$ — изоморфизм полей, $A$ — некоторая матрица
  из $GL_(n_1) (F_1)$, $chi$ — некоторый гомоморфизм группы $G$ в
  $RL_(n_1) (F_1)$.
] <th:omeara-matrix-congruence-isomorphisms>

Определим модуль $M^sharp$ для свободного модуля $M$ на $V$, полагая
$ M^sharp = brace(rho in V' | rho M subset.eq frak(o)). $
#source(161)Тогда
$ M^sharp = frak(o) rho_1 + dots + frak(o) rho_n. $
Контраградиентный изоморфизм $caron(quad)$ групп $GammaL_n (V)$ и
$GammaL_n (V')$ индуцирует изоморфизмы
$
  caron(quad): GL_n (M) arrow.r.double.bar GL_n (M^sharp), \
  caron(quad): SL_n (M) arrow.r.double.bar SL_n (M^sharp),
$
а контраградиентный изоморфизм $caron(quad)$ групп $PGammaL_n (V)$ и
$PGammaL_n (V')$ индуцирует изоморфизмы
$
  caron(quad): PGL_n (M) arrow.r.double.bar PGL_n (M^sharp), \
  caron(quad): PSL_n (M) arrow.r.double.bar PSL_n (M^sharp).
$

#theorem[
  Пусть $n$, $n_1$ — натуральные числа $>= 3$, а $frak(o)$, $frak(o)_1$ —
  произвольные области целостности. Следующие утверждения равносильны:
  #enum(
    start: 0,
    [$n = n_1$, $frak(o) ≃ frak(o)_1$,],
    [$SL_n (frak(o)) ≃ SL_(n_1) (frak(o)_1)$,],
    [$GL_n (frak(o)) ≃ GL_(n_1) (frak(o)_1)$,],
    [$PGL_n (frak(o)) ≃ PGL_(n_1) (frak(o)_1)$,],
    [$PSL_n (frak(o)) ≃ PSL_(n_1) (frak(o)_1)$.],
  )
] <th:omeara-integral-domains-classification>

#proof[
  Из определений следуют импликации 0) $=>$ 1), 0) $=>$ 2). Далее, в силу
  @prop:omeara-congruence-rich-transvections, группа $SL_n (M)$ богата
  трансвекциями, поэтому, в силу @prop:omeara-rich-linear-centralizer, группа
  $SL_n (M) inter RL_n (V)$ является центром группы $SL_n (M)$. Значит,
  $PSL_n (frak(o)) ≃ SL_n (frak(o)) \/ upright("cen") SL_n (frak(o))$
  и 1) $=>$ 4). Аналогично, 2) $=>$ 3). Осталось доказать импликации 4) $=>$ 0),
  3) $=>$ 0). Другими словами, для свободного модуля $M$ на $V$ мы должны
  показать, что
  $ PSL_n (M) ≃ PSL_(n_1) (M_1) => frak(o) ≃ frak(o)_1 $
  и
  $ PGL_n (M) ≃ PGL_(n_1) (M_1) => frak(o) ≃ frak(o)_1. $
  Заменяя, если необходимо, модуль $M$ на $V$ модулем $M^sharp$ на $V'$ и
  применяя теорему @th:omeara-congruence-projective-isomorphisms, можно считать,
  что данный изоморфизм $PSL_n (M) arrow.r.double.bar PSL_(n_1) (M_1)$ или
  $PGL_n (M) arrow.r.double.bar PGL_(n_1) (M_1)$ есть $Phi_(overline(g))$ для
  некоторой коллинеации $g$ пространства $V$ на $V_1$. Тогда достаточно
  показать, что если существует коллинеация #source(162)$g$ пространства $V$ на
  $V_1$ со свойством $Phi_(overline(g)) Delta = Delta_1$, где либо
  $ Delta = PSL_n (M), quad Delta_1 = PSL_(n_1) (M_1), $
  либо
  $ Delta = PGL_n (M), quad Delta_1 = PGL_(n_1) (M_1), $
  то
  $ frak(o)^mu = frak(o)_1, $
  где $mu$ — изоморфизм полей, ассоциированный с $g$. Возьмем базу $x_1$, …,
  $x_n$ пространства $V$, в которой
  $ M = frak(o) x_1 + dots + frak(o) x_n, $
  и пусть $rho_1$, …, $rho_n$ — сопряженная база. Положим $y_i = g x_i$,
  $1 <= i <= n$, $phi_j = mu rho_j g^(-1)$, $1 <= j <= n$. Тогда $y_1$, …, $y_n$
  — база пространства $V_1$ (в частности, $n = n_1$) и $phi_1$, …, $phi_n$ —
  сопряженная с ней база. Трансвекция $tau_(x_i,rho_j)$ сохраняет $M$, поэтому
  $overline(tau)_(x_i,rho_j)$ лежит в $Delta$, откуда
  $Phi_(overline(g)) overline(tau)_(x_i,rho_j) in Delta_1$, т. е.
  $overline(tau)_(y_i,phi_j) in Delta_1$, и, значит, $overline(tau)_(y_i,phi_j)$
  имеет представитель $alpha tau_(y_i,phi_j)$ ($alpha in dot(F)_1$), сохраняющий
  $M_1$. Но коммутаторное соотношение
  $ tau_(y_i,phi_j) = [beta tau_(y_i,phi_k), gamma tau_(y_k,phi_j)] $
  показывает, что $tau_(y_i,phi_j)$ сохраняет $M_1$. Следовательно,
  $phi_j (M_1) y_i subset.eq M_1$, откуда $phi_j (M_1) lambda y_i subset.eq M_1$
  для всех $lambda in frak(o)_1$. Значит, $tau_(lambda y_i,phi_j)$ сохраняет
  $M_1$ для всех $lambda in frak(o)_1$. Далее, для всех $lambda in frak(o)_1$
  имеем
  $ overline(tau)_(lambda y_i,phi_j) in Delta_1, $
  поэтому
  $ overline(g)^(-1) overline(tau)_(lambda y_i,phi_j) overline(g) in Delta, $
  т. е. $xi tau_(eta x_i,rho_j)$ сохраняет $M$ для некоторого $xi in dot(F)$,
  где
  $
    tau_(eta x_i,rho_j) = g^(-1) tau_(lambda y_i,phi_j) g
    quad "и" quad eta = lambda^(mu^(-1)).
  $
  Следовательно,
  $ tau_(eta x_i,rho_k) = [xi tau_(eta x_i,rho_j), tau_(x_j,rho_k)] $
  сохраняет $M$, откуда $eta in frak(o)$. Таким образом,
  $frak(o)_1^(mu^(-1)) subset.eq frak(o)$, откуда
  $frak(o)_1 subset.eq frak(o)^mu$. Точно так же из рассмотрения изоморфизма
  $Phi_(overline(g))^(-1)$ группы $Delta_1$ на $Delta$ получим
  $frak(o) subset.eq frak(o)_1^(mu^(-1))$. Следовательно,
  $frak(o)_1 = frak(o)^mu$, что и требовалось доказать.
]
