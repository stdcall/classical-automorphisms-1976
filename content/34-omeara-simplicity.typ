#import "main-defs.typ": *
#import "statements.typ": *

=== Теоремы о простоте <sec:omeara-simplicity>

#theorem[
  Для любого натурального $n >= 2$ и любого поля $F$ группа $PSL_n (F)$ проста,
  за исключением двух случаев: $PSL_2 (bb(F)_3)$ и $PSL_2 (bb(F)_2)$.
] <th:omeara-projective-simplicity>

#proof[
  Тот факт, что группы $PSL_2 (bb(F)_3)$ и $PSL_2 (bb(F)_2)$ не просты, следует
  из @prop:omeara-projective-commutators, поэтому будем предполагать, что либо
  $n >= 3$, либо $n = 2$ и $upright("card") F >= 4$. Вместо проективной группы
  мы будем иметь дело с группой $SL_n$. #source(83)Достаточно рассмотреть
  нормальную подгруппу $G$ группы $SL_n$, не лежащую в $RL_n$, и доказать, что
  $G = SL_n$.

  1) Сначала предположим, что $n >= 3$. Мы проведем доказательство, оперируя
  только с элементами группы линейных преобразований $SL_n = SL_n (V)$. Если
  удастся найти в $G$ хотя бы одну неединичную трансвекцию, то и все трансвекции
  в силу @prop:omeara-transvections-conjugate будут лежать в $G$, откуда по
  теореме @th:omeara-elementary-generation получим $G = SL_n$. Пусть
  $Sigma in G$, $Sigma in.not RL_n$. Тогда $Sigma in.not upright("cen") SL_n$,
  следовательно, существует такая трансвекция $T$ из $SL_n$, что
  $Sigma T != T Sigma$. Положим $sigma = Sigma T Sigma^(-1) T^(-1) != 1_V$. Из
  равенства
  $ sigma = Sigma(T Sigma^(-1) T^(-1)) = (Sigma T Sigma^(-1)) T^(-1) $
  следует, что $sigma in G$ и $upright("res") sigma <= 2$. Таким образом,
  описанная процедура, которую мы назовем _первым трюком для доказательства
  простоты_, позволяет найти в группе $G$ элемент $sigma$ с вычетом $1$ или $2$.
  #idx("первый трюк для доказательства простоты")
  #idx("трюк для доказательства простоты", "первый")
  Если $upright("res") sigma = 1$, то все доказано. Пусть
  $upright("res") sigma = 2$. Опишем теперь вторую процедуру — _второй трюк для
  доказательства простоты_, в результате которой элемент $sigma$ с вычетом $2$
  #idx("второй трюк для доказательства простоты")
  #idx("трюк для доказательства простоты", "второй")
  заменяется элементом с вычетом $1$. Так как $upright("res") sigma = 2$, то
  найдется гиперплоскость $H$ пространства $V$, содержащая $R$. Снова используя
  то, что $upright("res") sigma = 2$, найдем такой вектор $a$ из $H$, для
  которого $sigma a != a$. Пусть $rho$ — нетривиальный линейный функционал и
  $rho H = 0$. Тогда
  $ rho(sigma^(-1) x - x) in rho R subset.eq rho H = 0 $
  для всех $x$ из $V$, поэтому $rho sigma^(-1) = rho$. Следовательно, группа $G$
  содержит элемент
  $
    sigma(tau_(a,rho) sigma^(-1) tau_(a,rho)^(-1))
    = (sigma tau_(a,rho) sigma^(-1)) tau_(a,rho)^(-1) = \
    = tau_(sigma a,rho sigma^(-1)) tau_(-a,rho) = tau_(sigma a-a,rho),
  $
  который является нетривиальной трансвекцией. Для $n >= 3$ доказательство
  закончено.

  2) Теперь пусть $n = 2$. Так как $G subset.eq.not RL_2$, то хотя бы один
  элемент $sigma$ из $G$ перемещает некоторую прямую. Возьмем вектор $x$,
  коллинеарный этой прямой. Векторы $x$ и $sigma x$ составляют базу пространства
  $V$. Матрица преобразования $sigma$ в этой базе имеет вид
  $ mat(0, -1; 1, alpha) $
  для некоторого $alpha$ из $F$. Используя указанную базу, перейдем от группы
  линейных преобразований $SL_2 (V)$ к группе матриц $SL_2 (F) = SL_2$. Тогда
  $G lt.closed SL_2$ и
  $ mat(0, -1; 1, alpha) in G $ <eq:omeara-simplicity-initial>
  #source(84)для некоторого $alpha$ из $F$. Нужно доказать, что $G = SL_2$.
  Рассмотрим произвольные $lambda$ из $dot(F)$ и $mu$ из $F$. В силу
  нормальности группы $G$ матрица
  $
    mat(lambda^(-1), 0; 0, lambda) mat(0, -1; 1, alpha)
    mat(lambda^(-1), 0; 0, lambda)^(-1) mat(0, -1; 1, alpha)^(-1)
  $
  лежит в $G$, т. е.
  $ mat(lambda^(-2), 0; alpha(lambda^2 - 1), lambda^2) in G. $
  <eq:omeara-simplicity-diagonal>
  Снова ввиду нормальности $G$ матрица
  $
    mat(1, 0; mu, 1) mat(lambda^(-2), 0; alpha(lambda^2 - 1), lambda^2)
    mat(1, 0; mu, 1)^(-1)
    mat(lambda^(-2), 0; alpha(lambda^2 - 1), lambda^2)^(-1)
  $
  лежит в $G$, т. е.
  $ mat(1, 0; mu(1 - lambda^4), 1) in G. $
  <eq:omeara-simplicity-lower>
  Сопрягая @eq:omeara-simplicity-lower матрицей
  $ mat(0, -1; 1, 0), $
  получаем, что
  $ mat(1, -mu(1 - lambda^4); 0, 1) in G. $
  <eq:omeara-simplicity-upper>
  Если $F != bb(F)_5$, то либо $upright("card") F > 5$, либо
  $upright("card") F = 4$, а потому существует такое $lambda$ из $dot(F)$, что
  $lambda^4 != 1$, т. е. $lambda^4 - 1 != 0$. Так как $mu$ произвольно, то ввиду
  @eq:omeara-simplicity-lower, @eq:omeara-simplicity-upper все элементарные
  матрицы лежат в $G$ и $G = SL_2$. Пусть поэтому $F = bb(F)_5$. Если в
  соотношении @eq:omeara-simplicity-initial $alpha = 0$, то, сопрягая его
  матрицей
  $ mat(1, 3; 0, 1), $
  получим, что
  $ mat(3, 0; 1, 2) in G. $
  Далее,
  $
    mat(1, 0; 2, 1) = mat(1, 0; 1, 1) mat(3, 0; 1, 2)
    mat(1, 0; 1, 1)^(-1) mat(3, 0; 1, 2)^(-1) in G.
  $
  #source(85)Если $alpha != 0$, то ввиду @eq:omeara-simplicity-diagonal матрица
  $ mat(4, 0; 3 alpha, 4), $
  а потому и ее квадрат
  $ mat(1, 0; 4 alpha, 1) $
  лежат в $G$. Так или иначе, матрица $t_(2 1) (beta)$ лежит в $G$ для
  некоторого $beta$ из $dot(F)$. Возводя в квадрат, куб и $4$-ю степень,
  получим, что $t_(2 1) (F) subset.eq G$. После сопряжения матрицей
  $ mat(0, -1; 1, 0) $
  получим еще включение $t_(1 2) (F) subset.eq G$. Предложение полностью
  доказано.
]

#numbered-paragraph[
  Пусть $X$ — подгруппа группы $PGL_n$. Если $X$ инвариантна относительно
  сопряжения элементами из $PSL_n$, то $X = 1$ или $X supset.eq PSL_n$, за
  исключением двух случаев, когда $n = 2$ и $F = bb(F)_2$, $bb(F)_3$.
] <prop:omeara-projective-normal-subgroups>

#proof[
  Допустим, что $X != 1$. Пусть $sigma$ — неединичный элемент из $X$. Ввиду
  @prop:omeara-centres он не содержится в централизаторе группы $PSL_n$, которая
  порождена проективными трансвекциями, поэтому в $PSL_n$ существует проективная
  трансвекция $tau$, для которой $sigma tau != tau sigma$. Таким образом,
  $sigma(tau sigma^(-1) tau^(-1)) =
  (sigma tau sigma^(-1)) tau^(-1)$ — неединичный элемент из $X inter PSL_n$ и,
  значит, $1 subset X inter PSL_n lt.closed PSL_n$. Остается применить
  @th:omeara-projective-simplicity.
]

#numbered-paragraph[
  Пусть $X$ — подгруппа группы $GL_n$. Если $X$ инвариантна относительно
  сопряжений элементами из $SL_n$, то $X subset.eq RL_n$ или $X supset.eq SL_n$,
  за исключением двух случаев, когда $n = 2$ и $F = bb(F)_2$, $bb(F)_3$.
] <prop:omeara-linear-normal-subgroups>

#proof[
  По поводу исключений см. @prop:omeara-commutators-3-3-3. Далее, применяя
  @prop:omeara-projective-normal-subgroups к $P X$, получим, что
  $X subset.eq RL_n$ или $X dot RL_n supset.eq SL_n$. Допустим последнее. Тогда
  $ X supset.eq D X = D(X dot RL_n) supset.eq D SL_n = SL_n. $
]
