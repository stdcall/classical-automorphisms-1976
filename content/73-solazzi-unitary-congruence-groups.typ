#import "main-defs.typ": *
#import "statements.typ": *

== Автоморфизмы унитарных конгруэнц-групп
<sec:solazzi-unitary-congruence-groups>

Пусть $frak(o)$ — область целостности произвольной характеристики, а отображение
$alpha arrow.r.bar alpha^*$, $alpha in frak(o)$, — нетривиальный автоморфизм
порядка 2 кольца $frak(o)$. Пусть $F$ — поле частных для $frak(o)$. Автоморфизм
$*$ естественным образом продолжается до автоморфизма поля $F$, который мы снова
обозначим $*$.

Пусть $V$ есть $n$-мерное векторное пространство над $F$, $(x,y)$ —
невырожденная эрмитова форма на $V$ со значениями в $F$. Пусть $E$ — неподвижное
поле автоморфизма $*$.

#numbered-paragraph[
  Пусть $frak(a)$ и $frak(b)$ — дробные идеалы области целостности $frak(o)$.
  Тогда в поле $F$ найдется такой ненулевой элемент $lambda$ с нулевым следом,
  что $lambda frak(a) subset.eq frak(b)$.
] <prop:solazzi-unitary-trace-zero-scalar>

#proof[
  Достаточно доказать это в предположении, что $frak(a) subset.eq frak(o)$,
  $frak(b) subset.eq frak(o)$. Пусть $beta$ — ненулевой элемент из $frak(b)$.
  Так как $frak(o)^*=frak(o)$, то $beta beta^* in frak(b)$. Ясно, что в
  $frak(o)$ существует ненулевой элемент $t$ с нулевым следом. В качестве
  искомого $lambda$ можно взять $beta beta^* t$.
]

#definition(numbered: false)[
  $frak(o)$-модуль $M$ называется _ограниченным_, если существует
  $frak(o)$-линейный изоморфизм модуля $M$ в некоторый свободный
  $frak(o)$-модуль конечной размерности.
]
#idx("модуль", "ограниченный")

Пусть $M$ — ограниченный $frak(o)$-модуль, содержащийся в $V$ и такой, что
$F M=V$, где $F M={alpha x | alpha in F,x in M}$.

Для произвольного вектора $a in V$ определим его коэффициент $frak(c)_a$ как
множество всех $alpha in F$, таких, что $alpha a in M$. Очевидно, $frak(c)_a$ —
дробный идеал кольца $frak(o)$. Если $rho$ — ненулевой линейный функционал на
$V$, то $rho(M)$ — дробный идеал кольца $frak(o)$. Определим три унитарные
группы $TL_n (M)$, $U_n^+(M)$, $U_n (M)$ следующим образом:
$
  U_n (M)={sigma in U_n (V) | sigma M=M}, quad U_n^+(M)=U_n (M) inter SL_n (V),
$
$TL_n (M)$ — группа, порожденная всеми трансвекциями из $U_n (M)$.

Пусть $frak(a)$ — ненулевой идеал кольца $frak(o)$. Положим
$ frak(a) dot M={sum_i a_i x_i | a_i in frak(a),x_i in M} $
#source(214)
и определим унитарные конгруэнц-группы
$ U_n (M;frak(a))={sigma in U_n (M) | (sigma-1_V)M subset.eq frak(a) dot M}, $
$ U_n^+(M;frak(a))=U_n (M;frak(a)) inter SL_n (V), $
$TL_n (M;frak(a))$ — группа, порожденная всеми трансвекциями из
$U_n (M;frak(a))$.#idx("унитарная конгруэнц-группа")
#idx("конгруэнц-группа", "унитарная")

Ясно, что $TL_n (M;frak(a)) subset.eq U_n^+(M;frak(a)) subset.eq
U_n (M;frak(a))$ — нормальные подгруппы группы $U_n (M)$,
$TL_n (M;frak(o))=TL_n (M)$, $U_n^+(M;frak(o))=U_n^+(M)$,
$U_n (M;frak(o))=U_n (M)$.

Проективные унитарные конгруэнц-группы
$ PTL_n (M;frak(a)), quad PU_n^+(M;frak(a)), quad PU_n (M;frak(a)) $
определяются как образы групп $TL_n (M;frak(a))$, $U_n^+(M;frak(a))$,
$U_n (M;frak(a))$ соответственно при отображении $macron$ группы $U_n (V)$ на ее
факторгруппу по центру.#idx("проективная унитарная конгруэнц-группа")
#idx("конгруэнц-группа", "проективная унитарная")

Если $tau_(a,lambda) in U_n (V)$, то легко видеть, что
$
  lambda(M, a) subset.eq frak(c)_a dot frak(a)
  arrow.r.double lambda(M, a)a subset.eq frak(a) dot M
  arrow.r.double tau_(a,lambda) in TL_n (M;frak(a)).
$

#numbered-paragraph[
  При $n >= 2$ группа $TL_n (M;frak(a))$ имеет достаточно много трансвекций.
] <prop:solazzi-unitary-congruence-transvections>

#proof[
  Пусть $L=F a$ — изотропная прямая пространства $V$. Отображение
  $x arrow.r.bar (x,a)$, $x in V$, — ненулевой линейный функционал на $V$,
  поэтому $(M,a)$ — дробный идеал кольца $frak(o)$. Используя
  @prop:solazzi-unitary-trace-zero-scalar, выберем в $F$ ненулевой элемент
  $lambda$ с нулевым следом, такой, что
  $lambda(M, a) subset.eq frak(c)_a dot frak(a)$. Поскольку след $lambda$ равен
  нулю, то $tau_(a,lambda) in U_n (V)$. Сделанные выше замечания показывают, что
  $tau_(a,lambda) in TL_n (M;frak(a))$.
]

#numbered-paragraph[
  Пусть $nu(V) >= 3$, $chi(F) != 2$, $G$ — одна из групп
  $ PU_n (M;frak(a)), quad PU_n^+(M;frak(a)), quad PTL_n (M;frak(a)). $
  Для всякого автоморфизма $Lambda$ группы $G$ существует такой унитарный
  полулинейный изоморфизм $g$ пространства $V$ на себя, что
  $Lambda=overline(Lambda)_g|_G$.
] <prop:solazzi-unitary-projective-congruence-automorphisms>

#proof[
  Из @prop:solazzi-unitary-congruence-transvections следует, что $G$ имеет
  достаточно много проективных трансвекций. Применив теорему
  @th:solazzi-unitary-projective-automorphisms, получим требуемое.
]

#numbered-paragraph(family: "th")[
  *Теорема.* Пусть $nu(V) >= 3$, $chi(F) != 2$ и $S$ — одна из унитарных
  конгруэнц-групп
  $ U_n (M;frak(a)), quad U_n^+(M;frak(a)), quad TL_n (M;frak(a)), $
  #source(215)
  пусть $Lambda$ — автоморфизм группы $S$. Тогда существуют гомоморфизм $chi$
  группы $S$ в $RL(V) inter U_n (V)$ и унитарный полулинейный изоморфизм $g$
  пространства $V$ на себя, такие, что
  $Lambda sigma=chi(sigma) dot Lambda_g (sigma)$ для всех $sigma in S$.
] <th:solazzi-unitary-congruence-automorphisms>

#proof[
  Применить @cor:solazzi-unitary-linear-automorphisms и
  @prop:solazzi-unitary-congruence-transvections.
]
