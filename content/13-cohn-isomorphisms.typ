#import "main-defs.typ": *
#import "statements.typ": *

== Анализ изоморфизмов общих линейных групп <sec:cohn-isomorphisms>

Теперь мы рассмотрим обратную задачу: когда данный изоморфизм между $GL_n (R)$ и
$GL_n (S)$ индуцируется отображением $f: R -> S$? Наша цель — показать, что
такое отображение $f$ существует, если данный изоморфизм домножить на подходящий
внутренний автоморфизм и центральную гомотетию, причем в качестве $f$ можно
взять некоторый (анти)изоморфизм, а при $n = 2$ $U$-(анти)изоморфизм. Мы
ограничимся рассмотрением остепененных $k$-колец и предположим сначала, что
$n = 2$. Как и для тел, случай характеристики 2 будет изучен отдельно. С другой
стороны, теперь нет #source(39)необходимости ограничиваться рассмотрением
$upright("GE")_2$-колец, наряду с ними будут рассмотрены кольца, над которыми
все проективные модули свободны.

#lemma[
  Пусть $R$ — остепененное $k$-кольцо, где $k$ — тело характеристики $!= 2$,
  причем выполнено одно из следующих условий:

  + $R$ есть $upright("GE")_2$-кольцо,
  + каждый проективный (правый) $R$-модуль с двумя порождающими свободен.

  Тогда любая пара антикоммутирующих инволюций из $GL_2 (R)$ некоторым
  внутренним автоморфизмом переводится в пару $[1, -1]$,
  $P(0) = mat(0, 1; 1, 0)$.
] <lem:cohn-anticommuting-involutions>

#proof[
  Пусть $A$, $B$ — антикоммутирующие инволюции. Если выполнено условие 1), то по
  теореме @th:cohn-involution-standard-form инволюция $A$ сопряжена с матрицей
  $[1, -1]$, поскольку $A$ нецентральна. Если же выполнено условие 2), то мы
  рассмотрим $E = 1/2 (I + A)$. Очевидно, $E$ — идемпотент и, так как
  $A != plus.minus I$, то $E != 0, I$. Идемпотент $E$ определяет разложение
  пространства $R^2$ в прямую сумму ядра и образа, которые по условию 2)
  являются свободными $R$-модулями. В базе, согласованной с этим разложением,
  $E$ имеет диагональный вид $E = mat(1, 0; 0, 0)$, значит, в этой базе
  $A = [1, -1]$. Таким образом, при условии 1) или 2) $A$ приводится к виду
  $[1, -1]$. Пусть теперь $B = mat(a, b; c, d)$, тогда
  $A^(-1) B A = mat(a, -b; -c, d)$. По предположению $A^(-1) B A = -B$, поэтому
  $a = d = 0$. Но $B^2 = I$, откуда $b c = 1$, т.~е. $b, c in U(R)$. Сопрягая
  $B$ матрицей $[b, 1]$, перестановочной с $A$, получим
  $[c, 1] B [b, 1] = P(0)$.
]

Теперь пусть $R$ — остепененное $k$-кольцо, $S$ — остепененное $k'$-кольцо,
причем $k$ и $k'$ — тела характеристики $!= 2$. Предположим также, что одно из
колец $R$, $S$, скажем $S$, либо является $upright("GE")_2$-кольцом, либо все
проективные модули над ним свободны. Пусть
$ f: GL_2 (R) -> GL_2 (S) $ <eq:cohn-groups-isomorphism>
— изоморфизм. Обозначим для краткости через $D_0$ инволюцию $[1, -1]$ (над $R$
или $S$). Над любой областью целостности $-I$ характеризуется как единственная
центральная инволюция, поэтому $(-I) f = -I$. Так как $D_0$ и $P(0)$ —
антикоммутирующие инволюции из $GL_2 (R)$, то их образы #source(40)относительно
$f$ — антикоммутирующие инволюции в $GL_2 (S)$. Это верно и для $eta (D_0 f)$,
$eta (P(0) f)$, где $eta$ — одно из чисел $plus.minus 1$. Сделаем для $eta$
определенный выбор, тогда, взяв композицию $f$ с некоторым внутренним
автоморфизмом группы $GL_2 (S)$, можно считать (по лемме
@lem:cohn-anticommuting-involutions), что
$ D_0 f = eta D_0, quad P(0) f = eta P(0). $ <eq:cohn-involution-images>

Ввиду @eq:cohn-involution-images централизатор матрицы $D_0$ в $GL_2 (R)$
отображается на централизатор $D_0$ в $GL_2 (S)$. Но он совпадает с множеством
диагональных матриц, поэтому $f$ отображает $D_2 (R)$ на $D_2 (S)$. Наша
ближайшая задача — получить характеризацию треугольных матриц
$T(h) = mat(1, h; 0, 1)$. Полагая $T = T(h)$, $T^D = D^(-1) T D$, имеем
$ (T D_0)^2 = I, $ <eq:cohn-triangular-involution>
$ T^D T = T T^D "для всех" D in D_2 (R). $
<eq:cohn-diagonal-conjugates-commute>

Матрица $U = T f$ удовлетворяет тем же уравнениям. Положим
$U = mat(a, b; c, d)$, $D = [1, delta]$. Приравнивая элементы на месте $(1, 1)$
в равенстве $U^D U = U U^D$, получим
$ b (delta - delta^(-1)) c = 0. $ <eq:cohn-offdiagonal-product>

Если тело $k'$ содержит больше, чем 3 элемента, то существует $delta in k'$,
такой, что $delta != 0$, $delta^2 != 1$. Используя @eq:cohn-offdiagonal-product,
видим, что в этом случае $b = 0$ или $c = 0$. Поскольку характеристика тела $k'$
не равна 2, то остается рассмотреть случай, когда $k'$ — тело из трех элементов.
Приравнивая коэффициенты матриц в равенстве $(U D_0)^2 = I$, вытекающем из
@eq:cohn-triangular-involution, получим
$ a b = b d, quad c a = d c, quad a^2 - b c = d^2 - c b = 1. $
<eq:cohn-triangular-coefficients>

Кроме того, в этом случае $T^3 = I$, значит, $U^3 = I$. Но
$
  U^2 = mat(a^2 + b c, a b + b d; c a + d c, d^2 + c b)
  = mat(2 a^2 - 1, 2 a b; 2 d c, 2 d^2 - 1), \
  I = U^3 = mat(2 a^3 - a + 2 a b c, *; *, 2 d^3 - d + 2 d c b),
$
откуда $a (2 a^2 - 1 + 2 b c) = 1$, $d (2 d^2 - 1 + 2 c b) = 1$. Это означает,
что $a, d in U(S) subset.eq k'$, т.~е. $a, d = plus.minus 1$. Следовательно,
#source(41)$a^2 = d^2 = 1$, и из последнего равенства в
@eq:cohn-triangular-coefficients получается, что $b c = 0$. Мы снова заключаем,
что либо $b = 0$, либо $c = 0$.

Пусть $b != 0$, тогда $c = 0$. Из равенств @eq:cohn-triangular-coefficients,
которые всегда справедливы, следует, что $a^2 = d^2 = 1$, т.~е.
$(a + 1)(a - 1) = 0$. Так как $S$ — область целостности, то $a = plus.minus 1$ и
аналогично $d = plus.minus 1$. Более того, первое равенство в
@eq:cohn-triangular-coefficients показывает, что $a = d$. Итак, $U$ имеет вид
$ U = plus.minus mat(1, b; 0, 1), $ <eq:cohn-upper-triangular-image>
и, очевидно, каждая такая матрица удовлетворяет условиям
@eq:cohn-triangular-involution и @eq:cohn-diagonal-conjugates-commute для $T$.
Точно так же при $b = 0$, $c != 0$ заключаем, что $U$ имеет вид
$ U = plus.minus mat(1, 0; c, 1), $ <eq:cohn-lower-triangular-image>
и эта матрица опять удовлетворяет условиям @eq:cohn-triangular-involution и
@eq:cohn-diagonal-conjugates-commute. Наконец, при $b = c = 0$ легко видеть, что
$a = d = plus.minus 1$ и $U$ равно $plus.minus I$ или $plus.minus D_0$. На этом
все возможности для $U$ исчерпаны.

Изоморфизм $f$ отображает диагональные матрицы на диагональные, поэтому он
отображает каждую матрицу $T(h)$ в матрицу вида @eq:cohn-upper-triangular-image
или @eq:cohn-lower-triangular-image. Рассмотрим $T(1)$. Если $T(1) f = T(s)$,
$s in S$, то $s != 0$, поскольку $f$ инъективно. Так как $T(h) f$ перестановочно
с $T(s) = T(1) f$ для любого $h in R$, то $T(h) f$ имеет вид
@eq:cohn-upper-triangular-image. Значит, $f$ отображает подгруппу
$bold(B)_12 (R) = {B_12 (a) | a in R}$ в подгруппу $plus.minus bold(B)_12 (S)$.
Если $T(1) f = B_21 (s)$, то возьмем композицию $f$ с внутренним автоморфизмом,
порождаемым элементом $E(0) = D_0 P(0)$. Новый изоморфизм $f$ оставляет
@eq:cohn-involution-images без изменения с точностью до замены $eta$ на $-eta$,
но теперь $T(1) f = E(0)^(-1) B_21 (s) E(0) = T(-s)$, так что этот случай по
существу сводится к предыдущему. Более точно, мы показали, что композиция $f$ с
подходящим внутренним автоморфизмом удовлетворяет формулам
@eq:cohn-involution-images при $eta = plus.minus 1$ и отображает
$bold(B)_12 (R)$ в $plus.minus bold(B)_12 (S)$. Итак, можно записать, что
$ T(x) f = epsilon(x) T(x^sigma), $ <eq:cohn-signed-additive-map>
где $x |-> x^sigma$ — отображение $R$ в $S$, а $x |-> epsilon(x)$ — отображение
$R$ в ${plus.minus 1}$. Поскольку $T(x) T(y) = T(x + y)$, то
$
  & epsilon(x + y) T((x + y)^sigma)
    = epsilon(x) epsilon(y) T(x^sigma) T(y^sigma) = \
  & = epsilon(x) epsilon(y) T(x^sigma + y^sigma).
$
#source(42)Отсюда
$ (x + y)^sigma = x^sigma + y^sigma, $ <eq:cohn-sigma-additive>
$ epsilon(x) epsilon(y) = epsilon(x + y). $ <eq:cohn-sign-additive>
Полагая в @eq:cohn-sign-additive $y = x$, найдем, что
$epsilon(2x) = epsilon(x)^2 = 1$, значит, $epsilon(x) = 1$ для всех $x in R$.
Уже отмечалось, что $x^sigma != 0$ при $x != 0$, поэтому из
@eq:cohn-sigma-additive следует инъективность отображения $sigma$.

Повторяя те же рассуждения для $f^(-1)$ вместо $f$ (и читая
@eq:cohn-involution-images справа налево), получим, что $sigma$ — изоморфизм
аддитивных групп $R$ и $S$. Теперь рассмотрим $E(x)$:
$ E(x) = D_0 T(x) P(0). $
Применяя $f$, видим, что $E(x) f = eta^2 D_0 T(x^sigma) P(0)$, откуда
$ E(x) f = E(x^sigma). $ <eq:cohn-elementary-sigma-image>
Если подействовать отображением $f$ на соотношение @eq:cohn-unit-relation и с
помощью @eq:cohn-elementary-sigma-image упростить результат, то получится
$
  E((alpha^(-1))^sigma) E(alpha^sigma) E((alpha^(-1))^sigma)
  = -D(alpha^(-1)) f.
$
Правая часть этого равенства принадлежит $D_2 (S)$, следовательно, такова и
левая часть, но это возможно лишь при $alpha^sigma in U_0 (S)$. Учитывая, что
$alpha^sigma != 0$, применим @eq:cohn-unit-reduction и получим
$
  D(alpha^(-1)) f = -E((alpha^(-1))^sigma - (alpha^sigma)^(-1))
  D(alpha^sigma) E((alpha^(-1))^sigma - (alpha^sigma)^(-1)).
$
Приравнивая коэффициенты на местах $(1, 2)$, получим
$ (alpha^(-1))^sigma = (alpha^sigma)^(-1). $
<eq:cohn-sigma-preserves-inverses>
Обе части этого равенства будем обозначать через $alpha^(-sigma)$. Применив
@eq:cohn-sigma-preserves-inverses к предшествующему равенству, получим
$D(alpha^(-1)) f = D((alpha^sigma)^(-1))$. Заменяя $alpha$ на $alpha^(-1)$ и
снова используя @eq:cohn-sigma-preserves-inverses, получим
$ D(alpha) f = D(alpha^sigma). $ <eq:cohn-special-diagonal-image>
В частности, при $alpha = 1$ имеем
$ 1^sigma = 1. $ <eq:cohn-sigma-preserves-unit>
По теореме Хуа Ло-гена (см., например, @bib:cohn-Artin1957, стр. 58–59) из
@eq:cohn-sigma-additive, @eq:cohn-sigma-preserves-inverses и
@eq:cohn-sigma-preserves-unit следует, что $sigma$ — гомоморфизм или
антигомоморфизм тела $k$ в $k'$. Те же рассуждения для $f^(-1)$ вместо $f$
показывают, что в действительности $sigma$ — биекция между $k$ и $k'$, а потому
изоморфизм или антиизоморфизм.

#source(43) Если мы применим $f$ к @eq:cohn-diagonal-relation, то получим
$
  D(alpha^(-sigma)) E(alpha^sigma x^sigma alpha^sigma)
  = E(x^sigma) D(alpha^sigma)
  = D(alpha^(-sigma)) E((alpha x alpha)^sigma)
$
и, значит,
$
  (alpha x alpha)^sigma = alpha^sigma x^sigma alpha^sigma
  quad (x in R, alpha in U(R)).
$ <eq:cohn-sigma-unit-sandwich>
В действительности это соотношение можно использовать в доказательстве теоремы
Хуа Ло-гена. Более общо, с помощью этого соотношения, следуя в точности
доказательству теоремы Хуа Ло-гена, можно показать, что либо
$ (alpha x beta)^sigma = alpha^sigma x^sigma beta^sigma, $
<eq:cohn-sigma-unit-bilinearity>
либо
$ (alpha x beta)^sigma = beta^sigma x^sigma alpha^sigma $
<eq:cohn-sigma-unit-antibilinearity>
для всех $x in R$, $alpha, beta in U(R)$. Таким образом, $sigma$ есть
$U$-изоморфизм или $U$-антиизоморфизм.

Рассмотрим действие $f$ на диагональные матрицы. Каждую такую матрицу можно
привести к виду $[1, alpha]$ умножением на матрицу $D(beta)$ при подходящем
$beta$. Но $D(beta) f$ определяется формулой @eq:cohn-special-diagonal-image, а
образ $[1, alpha]$ при изоморфизме $f$ диагонален. Пусть
$ [1, alpha] f = [alpha^lambda, alpha^mu]. $
<eq:cohn-diagonal-component-maps>
Так как $P(0) [1, alpha] P(0) = [alpha, 1]
= [alpha, alpha^(-1)] [1, alpha]$, то имеем
$[alpha^sigma, alpha^(-sigma)] [alpha^lambda, alpha^mu]
= P(0) [alpha^lambda, alpha^mu] P(0) = [alpha^mu, alpha^lambda]$, откуда
$ alpha^mu = alpha^sigma alpha^lambda. $ <eq:cohn-diagonal-component-relation>
Ввиду этого равенства
$
  [alpha, beta] f = ([alpha, alpha^(-1)] [1, alpha beta]) f
  = [alpha^sigma, alpha^(-sigma)]
  [(alpha beta)^lambda, (alpha beta)^sigma (alpha beta)^lambda],
$
т.~е.
$
  [alpha, beta] f = [alpha^sigma, alpha^(-sigma) (alpha beta)^sigma]
  (alpha beta)^lambda.
$ <eq:cohn-general-diagonal-image>
Предположим теперь, что $sigma$ есть $U$-изоморфизм. Тогда
$ [alpha, beta] f = [alpha^sigma, beta^sigma] (alpha beta)^lambda. $
Отсюда и из равенства
$ [1, alpha beta] = [1, alpha] [1, beta] $ <eq:cohn-diagonal-multiplication>
получим
$
  [1, alpha^sigma beta^sigma] (alpha beta)^lambda
  = [1, alpha^sigma] alpha^lambda [1, beta^sigma] beta^lambda,
$
т.~е.
$
  (alpha beta)^lambda = [1, beta^(-sigma)] alpha^lambda
  [1, beta^sigma] beta^lambda.
$

#source(44) Сравнивая коэффициенты на месте $(1, 1)$ в последнем соотношении,
найдем, что
$ (alpha beta)^lambda = alpha^lambda beta^lambda, $
а сравнивая коэффициенты на месте $(2, 2)$ и пользуясь последним равенством,
получим
$ beta^sigma alpha^lambda = alpha^lambda beta^sigma. $
<eq:cohn-centralizes-unit-images>
Таким образом, $lambda$ — гомоморфизм группы $U(R)$ в $U(S)$, а поскольку
$sigma$ отображает $U(R)$ на $U(S)$, то из @eq:cohn-centralizes-unit-images
следует, что $alpha^lambda$ централизует $U(S)$. В силу
@eq:cohn-diagonal-relation
$
  & [beta^sigma, alpha^sigma] (alpha beta)^lambda
    E((beta^(-1) x alpha)^sigma)
    = E(x^sigma) [alpha^sigma, beta^sigma] (alpha beta)^lambda = \
  & = [beta^sigma, alpha^sigma]
    E(beta^(-sigma) x^sigma alpha^sigma) (alpha beta)^lambda.
$
Отсюда снова получаем, что
$(alpha x beta)^sigma = alpha^sigma x^sigma beta^sigma$. Пусть $beta = 1$,
$x = y alpha^(-1)$, тогда $alpha^lambda E(y^sigma) = E(y^sigma) alpha^lambda$,
и, следовательно, $alpha^lambda$ лежит в центре кольца $S$. Таким образом,
$lambda$ — центральная гомотетия, а $f$, согласно
@eq:cohn-elementary-sigma-image и @eq:cohn-general-diagonal-image, — композиция
изоморфизма, индуцированного $U$-изоморфизмом $sigma$, и центральной гомотетии
$lambda$. Наконец, из @eq:cohn-general-diagonal-image и
@eq:cohn-involution-images получаем $eta = (-1)^lambda$.

Пусть теперь $sigma$ есть $U$-антиизоморфизм, тогда ввиду
@eq:cohn-general-diagonal-image
$
  [alpha, beta] f
  = [alpha^sigma, alpha^(-sigma) beta^sigma alpha^sigma] (alpha beta)^lambda.
$
Если выразить $lambda$ через $sigma$ и $mu$ с помощью
@eq:cohn-diagonal-component-relation, то это соотношение перепишется в виде
$ [alpha, beta] f = [beta^(-sigma), alpha^(-sigma)] (alpha beta)^mu. $
Применяя его к равенству @eq:cohn-diagonal-multiplication, найдем, что $mu$ —
гомоморфизм группы $U(R)$ в центр группы $U(S)$. С помощью
@eq:cohn-diagonal-relation доказывается, как и выше, что на самом деле
$alpha^mu$ лежит в центре $S$. Таким образом, $f$ — композиция изоморфизма,
индуцированного $U$-антиизоморфизмом $sigma$, и центральной гомотетии $mu$.

Эти результаты можно суммировать в виде следующей теоремы.

#theorem[
  #footnote[Формулировка исправлена. — Прим. ред.]
  Пусть $R$ — остепененное $k$-кольцо, $S$ — остепененное $k'$-кольцо, где $k$ и
  $k'$ — тела характеристики $!= 2$. Пусть либо $S$ есть
  $upright("GE")_2$-кольцо, либо все проективные 2-порожденные $S$-модули
  свободны. Тогда любой изоморфизм из $GL_2 (R)$ в $GL_2 (S)$ совпадает на
  группе $upright("GE")_2 (R)$ с композицией #source(45)изоморфизма,
  индуцированного некоторым $U$-изоморфизмом или $U$-антиизоморфизмом,
  центральной гомотетии и внутреннего автоморфизма.
] <th:cohn-isomorphisms-odd-characteristic>

Эта теорема включает в себя результат Райнера @bib:cohn-Reiner1957b для
$R = S = k[x]$ и более ранние результаты Шрайера — ван дер Вардена и Хуа Ло-гена
(см.~@bib:cohn-Dieudonne1955 и содержащиеся там ссылки). Если $R$ — некоторое
$k$-кольцо, то характеристика тела $k$ отлична от 2 тогда и только тогда, когда
$GL_2 (R)$ содержит центральную инволюцию. Значит, если дан изоморфизм
$ f: GL_2 (R) approx.eq GL_2 (S), $
где $R$ есть $k$-кольцо, а $S$ есть $k'$-кольцо, то характеристики $k$ и $k'$
равны или не равны 2 одновременно. Чтобы разобрать оставшийся случай, нам нужна
лемма, аналогичная лемме @lem:cohn-anticommuting-involutions. Если лемма
@lem:cohn-anticommuting-involutions утверждает в характеристике $!= 2$ (и при
указанных выше предположениях) сопряженность диэдральных подгрупп порядка 8
группы $GL_2 (R)$, то следующая лемма утверждает в характеристике 2
сопряженность подгрупп типа симметрической группы степени 3.

#lemma[
  Пусть $R$ — остепененное $k$-кольцо, где $k$ — тело характеристики 2.
  Предположим, далее, что $R$ есть $upright("GE")_2$-кольцо. Тогда любая пара
  инволюций из $GL_2 (R)$, произведение которых имеет порядок 3, подходящим
  внутренним автоморфизмом переводится в пару $T(1) (= B_12 (1))$, $P(0)$.
] <lem:cohn-symmetric-involutions>

#proof[
  Пусть $A, B in GL_2 (R)$ — данные инволюции и $C = A B$. По предложению
  @prop:cohn-finite-order-standard-form и следующему за ним замечанию $C$ можно
  привести к виду
  $ [1, beta] E(a) quad "или" quad [alpha, beta] E(0) E(b). $
  <eq:cohn-order-three-standard-forms>
  Предположим, что $C$ имеет второй вид. Сравнивая коэффициенты матриц в обеих
  частях равенства $C^3 = I$, найдем, что $alpha^3 = beta^3 = 1$,
  $b alpha^2 + beta b alpha + beta^2 b = 0$. Сопрягая $C$ матрицей
  $E(beta^2 b alpha)^(-1)$, получим
  $
    & E(beta^2 b alpha) [alpha, beta] E(0) E(b)
      E(0) E(beta^2 b alpha) E(0) = \
    & = [beta, alpha] E(beta b alpha^2) E(0) E(b)
      E(0) E(beta^2 b alpha) E(0) = \
    & = [beta, alpha] E(b + beta^2 b alpha + beta b alpha^2) E(0) = \
    & = [beta, alpha].
  $
  Таким образом, $C$ можно привести к диагональному виду. Если $C$ имеет первый
  вид @eq:cohn-order-three-standard-forms, то из уравнения $C^3 = I$ следует,
  что $beta = a^2$, $a^3 = 1$. Если $a != 1$, то $a^2 + a + 1 = 0$, #source(
    46,
  )и, сопрягая $C$ с матрицей $mat(1, 1; 1, beta)$, получим $[beta, 1]$.
  Следовательно, $C$ приводится сопряжением к одной из матриц
  $ mat(1, 1; 1, 0), quad [alpha, beta]. $ <eq:cohn-order-three-models>
  Мы утверждаем, что на самом деле $C$ сопряжена с первой из этих матриц.
  Поскольку $C$ имеет порядок 3, то из подобия $C$ второй матрице следовало бы,
  что $alpha^3 = beta^3 = 1$ и $alpha$, $beta$ не равны 1 одновременно. Пусть
  $alpha = 1$ и $A = mat(a, b; c, d)$. Сравнивая коэффициенты на месте $(1, 1)$
  в равенствах $A^2 = (A C)^2 = I$, видим, что $a^2 + b c = a^2 + b beta c = 1$,
  откуда $b (beta - 1) c = 0$ и $b$ или $c$ равно нулю. Пусть $b = 0$. Тогда
  $a = d = 1$, и, сравнивая коэффициенты на месте $(2, 2)$ в равенстве
  $(A C)^2 = I$, получим $beta^2 = 1$, т.~е. $beta = 1$ — противоречие.
  Аналогичные рассуждения проходят при $c = 0$. Следовательно, ни $alpha$, ни
  $beta$ в @eq:cohn-order-three-models не равны 1, т.~е. $alpha$, $beta$ — корни
  уравнения
  $ x^2 + x + 1 = 0. $ <eq:cohn-cubic-root-polynomial>

  Предположим сначала, что это уравнение имеет корень $omega$ в центре тела $k$.
  Тогда $(alpha - omega)(alpha - omega^2) = 0$, откуда $alpha = omega$ или
  $alpha = omega^2$. То же справедливо и для $beta$. При $beta = alpha$ матрица
  $C$ скалярна, оставим этот случай на время в стороне и, не прерывая
  рассуждений, будем считать, что $beta != alpha$. Тогда $beta = alpha^(-1)$ и,
  сопрягая $C$ с матрицей $mat(1, beta; 1, alpha)$, получим для $C$ первый вид
  из @eq:cohn-order-three-models. Если уравнение @eq:cohn-cubic-root-polynomial
  не имеет корней в центре $Z$ тела $k$, то оно неразложимо над $Z$ и, значит,
  все его корни в $k$ сопряжены @bib:cohn-Herstein1954. Поэтому существует
  элемент $gamma in k$, такой, что $gamma^(-1) beta gamma = alpha^(-1)$.
  Сопрягая $[alpha, beta]$ матрицей $[1, gamma]$, мы сведем этот случай к
  предыдущему.

  Итак, $C$ можно привести к виду $mat(1, 1; 1, 0)$ (с отмеченным выше
  исключением). По предположению $C = A B$, $C^(-1) = B A$, откуда
  $ C B = A = B C^(-1). $ <eq:cohn-involution-intertwining>
  Полагая $B = mat(u, v; w, z)$ и используя выражение, найденное для $C$,
  сравним коэффициенты в @eq:cohn-involution-intertwining. После упрощения
  получим
  $ z = u, quad u + v + w = 0. $

  #source(47)Сравнив коэффициенты матриц в равенстве $B^2 = I$, найдем, что
  $u v = v u$, $u^2 + v w = 1$. Кроме того, $A = mat(v, w; u, v)$. По теореме
  @th:cohn-involution-standard-form матрица $A$ подобна $T(h)$ при подходящем
  $h in R$, т.~е. существует обратимая матрица $P = mat(a, b; c, d)$, такая, что
  $ A P = P T(h). $ <eq:cohn-triangularizing-intertwiner>
  Снова сравнивая коэффициенты, получаем
  $
    v a + w c = a, quad v b + w d = a h + b, \
    u a + v c = c, quad u b + v d = b h + d,
  $
  или, после упрощения,
  $
    (v + 1) a = w c, quad (v + 1) b + w d = a h, \
    u a = (v + 1) c, quad u b + (v + 1) d = b h.
  $ <eq:cohn-intertwiner-coefficients>
  Перепишем @eq:cohn-triangularizing-intertwiner в виде
  $ (A + I) P = P mat(0, h; 0, 0). $
  Для первых строк этого матричного уравнения имеем
  $ (v + 1, w) P = (0, a h), $ <eq:cohn-intertwiner-row>
  значит,
  $ (v + 1, w) = (0, a h) P^(-1). $ <eq:cohn-intertwiner-row-inverse>
  Из первых двух равенств @eq:cohn-intertwiner-coefficients следует, что
  $ (v + 1) c + w (a + c) = a, $ <eq:cohn-left-divisor-identity>
  а из @eq:cohn-intertwiner-row-inverse получается, что $a h$ — общий левый
  делитель для $v + 1$ и $w$. Поэтому $a = a h k$, и $h$ — единица, скажем,
  $h = eta$. Комбинируя @eq:cohn-left-divisor-identity и третье равенство из
  @eq:cohn-intertwiner-coefficients, получим
  $ (v + 1, w) mat(b + c eta; d + (a + c) eta) = 0. $
  Используя @eq:cohn-intertwiner-row, перепишем это в виде
  $ (0, a eta) P^(-1) mat(b + c eta; d + (a + c) eta) = 0. $

  #source(48)Если $a = 0$, то $c != 0$, и первые два равенства из
  @eq:cohn-intertwiner-coefficients показывают, что $w = 0$, $v = 1$, а тогда
  $u = 1$. В этом случае сопряжение с помощью $C^(-1)$ приводит к требуемому
  виду. Если $a != 0$, то $a eta != 0$, и из последнего равенства следует, что
  $
    P^(-1) mat(b + c eta; d + (a + c) eta) = mat(k; 0)
    "для некоторого" k in R.
  $
  Поэтому
  $ mat(b + c eta; d + (a + c) eta) = P mat(k; 0), $
  откуда $b = c eta + a k$, $d = (a + c) eta + c k$. Подставим эти значения в
  $P$:
  $
    P = mat(a, b; c, d) = mat(a, a k + c eta; c, c k + (a + c) eta)
    = mat(a, c; c, a + c) mat(1, k; 0, eta).
  $
  Отсюда видно, что матрица $P_1 = mat(a, c; c, a + c)$ обратима. Ясно, что
  $P_1$ перестановочна с $C = mat(1, 1; 1, 0)$ и, сопрягая $A$ с помощью $P_1$,
  мы получим $T(1)$. То же самое сопряжение приводит матрицу $B = A C$ к виду
  $P(0)$, что мы и хотели показать.

  Осталось лишь заметить, что случай $C = omega I$, где $omega$ — корень
  уравнения @eq:cohn-cubic-root-polynomial из центра тела $k$, невозможен.
  Предположим противное и введем обозначения
  $
    R^+ = {x in R | x omega = omega x}, quad
    R^- = {x in R | x omega = omega^2 x}.
  $
  Для краткости элементы из $R^+$ будем называть _симметричными_, а элементы из
  $R^-$ — _кососимметричными_. #idx("симметричный элемент")#idx(
    "элемент симметричный",
  )#idx("кососимметричный элемент")#idx("элемент кососимметричный") По
  предположению каждый элемент из $k$ симметричен. Покажем, что каждый элемент
  из $R$ выражается в виде суммы симметричного и кососимметричного элементов,
  причем единственным образом. В самом деле, если
  $
    x = x^+ + x^-, quad x^epsilon in R^epsilon,
    quad epsilon = plus.minus,
  $ <eq:cohn-symmetric-decomposition>
  то
  $ omega x = x^+ omega + x^- omega^2. $ <eq:cohn-omega-decomposition>
  Решая эти два уравнения, найдем, что
  $ x^+ = x omega^2 + omega x, quad x^- = x omega + omega x, $
  #source(49)Итак, для $x^+$ и $x^-$ возможен единственный выбор, и ясно, что он
  удовлетворяет @eq:cohn-symmetric-decomposition. Из равенства
  @eq:cohn-involution-intertwining имеем
  $ omega B = B omega^2, $
  поэтому все элементы в $B$ кососимметричны. Матрица $B$ обратима, поэтому
  имеет вид
  $ [alpha, beta] E(q_1) dots E(q_r). $
  Обозначая первую строку матрицы $B$ через $(a, b)$ и используя лемму
  @lem:cohn-continuant-growth, получим
  $ a = b q_r + a', $ <eq:cohn-reduced-row>
  где $d(a') < d(b)$. Сравним здесь симметричные компоненты:
  $ b (q_r)^- + (a')^+ = 0. $
  Но $d((a')^+) <= d(a') < d(b)$, значит, $(a')^+ = (q_r)^- = 0$, т.~е. $a'$
  кососимметричен, а $q_r$ симметричен. Следовательно, элементы матрицы
  $B E(q_r)^(-1)$ кососимметричны. Используя индукцию по $r$, заключаем, что
  $[alpha, beta]$ состоит из кососимметричных элементов, но это противоречит
  включению $k subset.eq R^+$. Тем самым лемма @lem:cohn-symmetric-involutions
  полностью доказана.
]

С помощью этой леммы легко получить в характеристике 2 теорему, подобную теореме
@th:cohn-isomorphisms-odd-characteristic. Пусть
$ f: GL_2 (R) -> GL_2 (S) $
— изоморфизм, причем $R$ — остепененное $k$-кольцо, $S$ — остепененное
$k'$-кольцо, $k$ и $k'$ — тела характеристики 2, а $S$ есть
$upright("GE")_2$-кольцо. В группе $GL_2 (R)$ матрицы $T(1)$, $P(0)$ образуют
пару инволюций, произведение которых имеет порядок 3, следовательно, таковы и их
образы в $GL_2 (S)$. По лемме @lem:cohn-symmetric-involutions можно считать
(домножив $f$ на подходящий внутренний автоморфизм группы $GL_2 (S)$), что
$ T(1) f = T(1), quad P(0) f = P(0). $ <eq:cohn-characteristic-two-models>
Подгруппа $bold(B)_12 (R)$ из $GL_2 (R)$ может быть охарактеризована как
максимальная абелева подгруппа периода 2 из централизатора матрицы $T(1)$ в
$GL_2 (R)$.#footnote[
  А также как множество всех инволюций из централизатора матрицы $T(1)$ с
  добавленной к ним единичной матрицей.
] Поэтому она отображается #source(50)на $bold(B)_12 (S)$ — максимальную абелеву
подгруппу периода 2 из централизатора $T(1)$ в $GL_2 (S)$. Таким образом,
существует отображение $sigma: R -> S$, такое, что
$ T(x) f = T(x^sigma), quad x in R. $
Из соотношения @eq:cohn-addition-relation имеем
$ (x + y)^sigma = x^sigma + y^sigma, $
<eq:cohn-characteristic-two-additivity>
а ввиду @eq:cohn-characteristic-two-models
$ 1^sigma = 1. $ <eq:cohn-characteristic-two-unit>

Диагональная матрица $D$ из $GL_2 (R)$ характеризуется тем, что $D$ и
$P(0) D P(0)$ нормализуют $bold(B)_12 (R)$. Следовательно, $f$ отображает
диагональные матрицы над $R$ в диагональные матрицы над $S$. Далее можно в
точности повторить рассуждения из доказательства теоремы
@th:cohn-isomorphisms-odd-characteristic и заключить, что справедлива

#theorem[
  Пусть $R$ — остепененное $k$-кольцо, $S$ — остепененное $k'$-кольцо, $k$ и
  $k'$ — тела характеристики 2, а $S$ есть $upright("GE")_2$-кольцо. Тогда
  каждый изоморфизм между $GL_2 (R)$ и $GL_2 (S)$ является композицией
  изоморфизма, индуцированного $U$-изоморфизмом или $U$-антиизоморфизмом,
  центральной гомотетии и внутреннего автоморфизма.
] <th:cohn-isomorphisms-characteristic-two>

В заключение мы коротко обсудим изоморфизмы группы $GL_n (R)$. Оказывается, что
методом, подобным использованному при доказательстве теоремы
@th:cohn-isomorphisms-odd-characteristic, получается

#theorem[
  Пусть $R$ — остепененное $k$-кольцо, $S$ — остепененное $k'$-кольцо, $k$ и
  $k'$ — тела характеристики $!= 2$. Предположим также, что любой конечно
  порожденный проективный $S$-модуль свободен. Тогда каждый изоморфизм между
  $GL_n (R)$ и $GL_n (S)$ при $n >= 3$ является композицией изоморфизма,
  индуцированного некоторым изоморфизмом или антиизоморфизмом из $R$ в $S$,
  центральной гомотетии и внутреннего автоморфизма.
] <th:cohn-higher-rank-isomorphisms>

#proof[
  Группа $GL_n (R)$ содержит систему $J$ из $2^n$ перестановочных инволюций
  $[plus.minus 1, dots, plus.minus 1]$, причем симметрическая группа $Sigma$
  степени $n$ естественно действует на $J$. Каждая орбита относительно этого
  действия состоит из $binom(n, k)$ элементов, где $k = 0, 1, dots, n$. Всего
  имеется $n + 1$ орбит. Изоморфизм $f$ переводит $J$ в множество из $2^n$
  перестановочных инволюций, лежащих в $GL_n (S)$. Если $P$ — #source(
    51,
  )инволюция, то $E = 1/2 (I + P)$ — идемпотент, и мы получаем $2^n$
  перестановочных идемпотентов в матричном кольце $S_n$. Поскольку по условию
  проективные $S$-модули свободны, то каждый идемпотент диагонализируем, а
  множество перестановочных идемпотентов можно одновременно привести к
  диагональному виду с элементами 0, 1 на диагонали. Подходящим сопряжением
  приведем $2^n$ перестановочных идемпотентов к виду $E = [e_1, dots, e_n]$, где
  $e_i = 0$ или 1. Но $P = 2 E - I$ — снова инволюция, так что мы имеем в
  $GL_n (S)$ систему из $2^n$ перестановочных инволюций диагонального вида.
  Более точно, применяя подходящий внутренний автоморфизм, можно считать, что
  для любой инволюции $P = [epsilon_1, dots, epsilon_n]$,
  $epsilon_i = plus.minus 1$, матрица $P f$ диагональная, причем на диагонали
  стоят элементы $plus.minus 1$. Если $r$ — число тех $epsilon_i$, которые равны
  $+1$, то назовем $P$ _инволюцией типа_ $(r, n - r)$, или, короче,
  _$(r, n - r)$-инволюцией_. #idx("инволюция", "типа (r, n − r)")#idx(
    "(r, n − r)-инволюция",
  ) Подгруппа группы $Sigma$, централизующая $(r, n - r)$-инволюцию, имеет вид
  $Sigma_r times Sigma_(n-r)$, поэтому, если $P$ имеет тип $(r, n - r)$, то
  $P f$ будет типа $(r, n - r)$ или $(n - r, r)$, т.~е. $P f$ или $-P f$ имеет
  тип $(r, n - r)$. Инволюции $P_1, dots, P_n$ типа $(1, n - 1)$ составляют одну
  орбиту относительно $Sigma$, значит, $P_1 f, dots, P_n f$ сопряжены и,
  следовательно, все имеют тип $(1, n - 1)$ или $(n - 1, 1)$. Домножив $f$ на
  подходящий внутренний автоморфизм, можно считать, что
  $ P_i f = eta P_i, $ <eq:cohn-higher-involution-images>
  где $eta = plus.minus 1$, $i = 1, dots, n$. Так как любая инволюция $P$ из $J$
  есть произведение инволюций $P_i$, то $P f = eta_P P$, где $eta_P = eta^r$,
  если $P$ имеет тип $(r, n - r)$. Пусть $S_sigma$ — подстановочная матрица,
  соответствующая подстановке $sigma in Sigma$. Тогда
  $S_sigma^(-1) P_i S_sigma = P_(i sigma)$. Применяя $f$, получим, согласно
  @eq:cohn-higher-involution-images, что
  $(S_sigma f)^(-1) P_i (S_sigma f) = P_(i sigma)$. Следовательно, матрица
  $S_sigma (S_sigma f)^(-1)$ перестановочна с $P_1, dots, P_n$, а потому
  диагональна и
  $ S_sigma f = D_sigma S_sigma. $ <eq:cohn-permutation-images>

  Пусть $rho = (1 2 dots n)$ — цикл длины $n$,
  $D_rho = [alpha_1, dots, alpha_n]$. Из равенства $S_rho^n = I$ следует, что
  $ alpha_n alpha_(n-1) dots alpha_1 = 1. $
  <eq:cohn-cycle-coefficient-product>
  Если сопрячь образы относительно $f$ одной и той же диагональной матрицей
  $T = [gamma_1, dots, gamma_n]$, то матрицы из $J$ не изменятся, а
  @eq:cohn-permutation-images примет вид
  $
    S_sigma f = D'_sigma S_sigma, quad
    "где" quad D'_sigma = T^(-1) D_sigma S_sigma T S_sigma^(-1).
  $

  #source(52)В частности,
  $
    D'_rho = [gamma_1^(-1) alpha_1 gamma_n,
      gamma_2^(-1) alpha_2 gamma_1, dots, gamma_n^(-1) alpha_n gamma_(n-1)].
  $
  Наша цель — выбрать $xi = plus.minus 1$ и $gamma_i$ ($i = 1, dots, n$) так,
  чтобы было
  $ gamma_i^(-1) alpha_i gamma_(i-1) = xi, $
  <eq:cohn-cycle-normalization>
  где $i = 1, dots, n$ и $gamma_0 = gamma_n = 1$. Если это сделано, то в силу
  @eq:cohn-cycle-coefficient-product будем иметь
  $
    & gamma_1 = alpha_1 xi, quad gamma_2 = alpha_2 gamma_1 xi
      = alpha_2 alpha_1 xi^2, dots \
    & dots, gamma_(n-1) = alpha_(n-1) dots alpha_1 xi^(n-1),
      quad gamma_n = xi^n = 1.
  $
  Обратно, если выполнены последние равенства, то справедливы и равенства
  @eq:cohn-cycle-normalization. Но последние уравнения всегда разрешимы при
  четном $n$, а если $n$ нечетно, то они разрешимы при условии, что $xi = 1$.
  Применяя подходящий внутренний автоморфизм (индуцированный диагональной
  матрицей), можно считать, что для $rho = (1 2 dots n)$ равенство
  @eq:cohn-permutation-images имеет вид
  $ S_rho f = chi(rho) S_rho, $ <eq:cohn-cycle-character>
  где $chi$ — линейный характер группы $Sigma$.

  Пусть $tau = (1 2)$ — транспозиция, $D_tau = [beta_1, dots, beta_n]$. Из
  соотношения $S_tau^2 = I$ следует, что $beta_1 beta_2 = 1$, $beta_i^2 = 1$
  ($i >= 3$). Диагонализируя $S_tau$, легко убедиться, что $S_tau$ — инволюция
  типа $(1, n - 1)$, а $S_tau f$ имеет тип $(1, n - 1)$ или $(n - 1, 1)$. Отсюда
  следует, что $beta_3 = beta_4 = dots = beta_n (= plus.minus 1)$. Таким
  образом,
  $
    D_tau = [beta, beta^(-1), delta, dots, delta],
    quad delta = plus.minus 1.
  $
  Теперь равенство $(1 2 dots n) = (n n-1)(n-1 n-2) dots (3 2)(2 1)$ показывает,
  что
  $ S_rho = S_tau^(rho^(n-2)) S_tau^(rho^(n-3)) dots S_tau, $
  где $S^rho$ обозначает матрицу, сопряженную с $S$ с помощью $S_rho$. Применяя
  $f$ и сравнивая диагональные члены, получим
  $ beta delta^(n-2) = chi(rho), quad beta^(n-1) = chi(rho). $
  <eq:cohn-transposition-character-relations>
  При $n$ нечетном $chi(rho) = 1$, и все сводится к равенству
  $ beta = delta. $
  Следовательно, в этом случае $D_tau = delta I$ — скалярная матрица, а
  поскольку $rho$ и $tau$ порождают группу $Sigma$, то каждая матрица $D_sigma$
  #source(53)скалярна, точнее,
  $ S_sigma f = chi(sigma) S_sigma, $ <eq:cohn-permutation-character>
  где $chi$ — линейный характер группы $Sigma$, единичный или знакопеременный в
  соответствии с равенством $delta = 1$ или $delta = -1$. Если же $n$ четно, то
  равенства @eq:cohn-transposition-character-relations принимают вид
  $ beta = chi(rho) (= chi(tau)), $
  и выбор $xi$ находится в нашем распоряжении. Возьмем $xi = chi(rho)$, тогда
  матрица $D_tau$ снова будет скалярна и равенство
  @eq:cohn-permutation-character снова будет справедливо.

  Диагональные матрицы можно охарактеризовать тем, что они централизуют
  $P_1, dots, P_n$. Рассмотрим теперь централизатор множества
  $ [1, 1, epsilon_3, dots, epsilon_n], quad epsilon_i = plus.minus 1. $
  <eq:cohn-block-centralizer-involutions>
  Ясно, что это будут в точности матрицы вида $A ⊕ [d_3, dots, d_n]$, где
  $A in GL_2 (R)$, поэтому централизатор множества
  @eq:cohn-block-centralizer-involutions и всех подстановок, действующих на 1 и
  2 тождественно, состоит из матриц вида $A ⊕ lambda I_(n-2)$ ($lambda in k$).
  Таким образом, $f$ индуцирует отображение
  $A ⊕ I_(n-2) |-> A^overline(f) ⊕ lambda(A) I_(n-2)$, где $overline(f)$ —
  изоморфизм $GL_2 (R) |-> GL_2 (S)$. Сопрягая обе части матрицей $S_sigma$,
  $sigma in Sigma$, видим, что аналогичная формула справедлива и для других
  строк и столбцов. По теореме @th:cohn-isomorphisms-odd-characteristic
  изоморфизм $overline(f)$ имеет вид $f_1 f_2 f_3$, где $f_1$ индуцирован
  $U$-изоморфизмом или $U$-антиизоморфизмом $phi$, $f_2$ — центральная
  гомотетия, $f_3$ — внутренний автоморфизм. Пусть $phi$ есть $U$-изоморфизм.
  Поскольку $f_1$ отображает $B_(i j)(x)$ в $B_(i j)(x^phi)$ и
  $(B_12 (x), B_23 (y)) = B_13 (x y)$, где $(A, B) = A^(-1) B^(-1) A B$, то
  $(B_12 (x^phi), B_23 (y^phi)) = B_13 ((x y)^phi)$, т.~е.
  $(x y)^phi = x^phi y^phi$. Значит, $phi$ — на самом деле обычный изоморфизм.
  Аналогично доказывается, что $phi$ будет обычным антиизоморфизмом, если $phi$
  есть $U$-антиизоморфизм. Беря коммутаторы элементов
  $A^overline(f) ⊕ lambda(A) I_(n-2)$ с элементами вида $I_2 ⊕ B$, легко
  убедиться, что $lambda(A)$ лежит в центре $S$. Разделив на $lambda(A)$,
  получим гомоморфизм
  $ A ⊕ I_(n-2) |-> theta(A) A^phi ⊕ I_(n-2), $
  причем по определению $theta(A) = I$, если $A$ — инволюция. Так как
  $
    [alpha, 1, 1, dots, 1]
    |-> [theta(alpha) alpha^phi, theta(alpha), 1, dots, 1],
  $
  то, переставляя вторую и третью строки и аналогичные столбцы (это не меняет
  левой части), получаем $theta([alpha, 1]) = 1$. Следовательно, $theta = 1$, и
  все доказано.
]
