
#import "diagrams/omeara-rich-transvections.typ": *
#import "main-defs.typ": *
#import "statements.typ": *

=== Теоремы об изоморфизмах в общем случае <sec:omeara-integral-domains>

Вернемся к общей ситуации, т.~е. когда $G$ — произвольная подгруппа в
$XiL_n (V)$, богатая трансвекциями, а $Delta$ — произвольная подгруппа в
$PXiL_n (V)$, богатая проективными трансвекциями. Аналогичные условия
налагаются, когда речь идет о $V_1$, $n_1$, $F_1$, $G_1$, $Delta_1$. Пусть
$Psi: G arrow.r.double G_1$, $Lambda: Delta arrow.r.double Delta_1$ —
изоморфизмы групп.

Обозначим через $cal(L)$, $cal(H)$, $cal(X)$ подмножества
$ cal(L) = P^1(V), quad cal(H) = P^(n-1)(V), quad cal(X) = cal(L) union cal(H) $
проективного пространства $P(V)$, т.~е. $cal(L)$ — множество прямых из $V$,
$cal(H)$ — множество гиперплоскостей, $cal(X)$ — объединение этих множеств.
Очевидно, $cal(L) inter cal(H) = emptyset$ при $n >= 3$ и $cal(L) = cal(H)$ при
$n = 2$. Мы не рассматриваем случай $n = 1$, когда богатые группы не определены.

Для всяких $L in cal(L)$, $H in cal(H)$, таких, что $L subset.eq H$, определим
$Delta(L, H)$ как группу, состоящую из 1 и всех проективных трансвекций из
$Delta$ с пространствами $L$, $H$. Это согласуется с использованием обозначения
$Delta(L, H)$ в более частной ситуации §~@sec:omeara-cdc и
@sec:omeara-transvection-preservation.

Для всякого $L in cal(L)$ определим $Delta(L)$ как группу, состоящую из 1 и всех
проективных трансвекций из $Delta$ с вычетной прямой $L$. Пусть $Delta(H)$ —
группа, состоящая из 1 и всех проективных трансвекций из $Delta$ с неподвижной
гиперплоскостью $H$. Для всякого $X in cal(X)$ определим $Delta(X)$ так: если
$X = L in cal(L)$, то $Delta(X) = Delta(L)$, а если $X = H in cal(H)$, то
$Delta(X) = Delta(H)$. Очевидно, эти два определения для $Delta(X)$ совпадают
при $n = 2$.

#source(127)Придерживаясь соглашения, введенного в §~@sec:omeara-cdc и
@sec:omeara-transvection-preservation, мы обозначаем через $C$ централизатор
$C_Delta$, $C_G$, $C_(breve(Delta))$, $C_(breve(G))$, когда мы имеем дело с
группами $Delta$, $G$, $breve(Delta)$, $breve(G)$ соответственно.

Множества $cal(L)_1$, $cal(H)_1$, $cal(X)_1$, $Delta_1 (L_1,H_1)$,
$Delta_1 (L_1)$, $Delta_1 (H_1)$, $Delta_1 (X_1)$, $C$ определяются аналогично в
случае группы $Delta_1$.

Если $overline(sigma)_1$, $overline(sigma)_2$ — нетривиальные проективные
трансвекции из $Delta$, то, применяя
@prop:omeara-transvection-centralizer-equality к богатой группе
$Delta inter PGL_n (V)$, получаем, что
$
  C(overline(sigma)_1) = C(overline(sigma)_2)
  => R_1 = R_2 quad "и" P_1 = P_2.
$

#numbered-paragraph[
  Предположим, что $n >= 3$. Если $Delta^*$ — подгруппа из
  $Delta inter PGL_n (V)$, богатая проективными трансвекциями, и
  $overline(sigma)$ — нетривиальная проективная трансвекция из $Delta^*$, то
  $C_Delta C_(Delta^*) (overline(sigma)) = Delta(R, P)$. В частности,
  $C C(overline(sigma)) subset.eq Delta(R, P)$ для всякой нетривиальной
  проективной трансвекции из $Delta$.
] <prop:omeara-general-double-centralizer>
#proof[
  Положим $Delta^(**) = Delta inter PGL_n (V)$. Тогда $Delta^(**)$ богата
  проективными трансвекциями и $Delta^* subset.eq Delta^(**)$. Поэтому ввиду
  @prop:omeara-transvection-double-centralizer
  $
    Delta(R, P) = Delta^(**)(R,P)
    = C_(Delta^(**)) C_(Delta^(**))(overline(sigma)) \
    subset.eq C_Delta C_(Delta^(**))(overline(sigma))
    subset.eq C_Delta C_(Delta^*) (overline(sigma)).
  $
  Для доказательства обратного включения поступаем, как при доказательстве
  @prop:omeara-transvection-double-centralizer, используя
  @prop:omeara-semilinear-scalar-kernel и результаты
  §~@sec:omeara-geometric-isomorphisms. Наконец, если $overline(sigma)$ —
  произвольная нетривиальная проективная трансвекция из $Delta$, то
  $overline(sigma) in Delta^(**)$ и
  $C(overline(sigma)) supset.eq C_(Delta^(**))(overline(sigma))$, поэтому
  $
    C C(overline(sigma)) subset.eq C_Delta C_(Delta^(**))(overline(sigma))
    = Delta(R, P).
  $
]

#example[
  Покажем, что утверждения
  $
    C(overline(sigma)_1) = C(overline(sigma)_2)
    <=> R_1 = R_2 quad "и" P_1 = P_2
  $
  и
  $ C C(overline(sigma)) = Delta(R, P), $
  справедливые для проективных трансвекций в частной ситуации §~@sec:omeara-cdc
  и @sec:omeara-transvection-preservation, уже не выполняются здесь. Для этого
  рассмотрим группу $Delta = PXiL_n (V)$ при $n >= 3$ над полем $F$, допускающим
  нетривиальный автоморфизм $mu$. Пусть элемент $alpha in F$ таков, что
  $alpha^mu != alpha$. Пусть $x_1, dots, x_n$ — база пространства $V$,
  $rho_1, dots, rho_n$ — сопряженная база, $k$ — элемент группы $XiL_n (V)$ с
  ассоциированным автоморфизмом поля $mu$ и матрицей
  $ upright("diag")(alpha,1,dots,1,alpha) $
  в базе $x_1, dots, x_n$. Легко проверить, что
  $ mu rho_n k^(-1) = alpha^(-1) rho_n. $
  #source(128)Поэтому, согласно §~@sec:omeara-geometric-isomorphisms,
  $ k tau_(x_1,rho_n) k^(-1) = tau_(x_1,rho_n) $
  и
  $
    k tau_(alpha x_1,rho_n) k^(-1)
    = tau_(alpha^mu x_1,rho_n) != tau_(alpha x_1,rho_n).
  $
  Другими словами, $overline(k)$ перестановочно с $overline(tau_(x_1,rho_n))$,
  но не перестановочно с $overline(tau_(alpha x_1,rho_n))$. В частности, $Delta$
  содержит две проективные трансвекции с одинаковыми пространствами, но с
  различными централизаторами. Более того, $overline(tau_(alpha x_1,rho_n))$
  лежит в $Delta(R, P)$ (где $overline(sigma) = overline(tau_(x_1,rho_n))$), но
  не лежит в $C C(overline(sigma))$, так как не перестановочно с
  $overline(k) in C(overline(sigma))$.
] <exm:omeara-semilinear-centralizer-failure>

#numbered-paragraph[
  Если $n >= 3$, $n_1 >= 2$, то существует подгруппа $Delta^0$ группы $Delta$,
  богатая проективными трансвекциями и удовлетворяющая условиям
  $
    Delta^0 subset.eq PSL_n (V), quad Lambda Delta^0 subset.eq PSL_(n_1) (V_1).
  $
] <prop:omeara-common-projective-rich-subgroup>
#proof[
  1) Покажем сначала, что $Lambda$ отображает в $PSL_(n_1) (V_1)$ по крайней
  мере одну нетривиальную проективную трансвекцию из $Delta$. Начнем с
  произвольной нетривиальной проективной трансвекции $overline(tau) in Delta$.
  Так как $Lambda Delta = Delta_1$ и $Delta_1$ богата, то существует такой
  элемент $overline(psi) in Delta$, что $Lambda overline(psi)$ лежит в
  $PSL_(n_1) (V_1)$ (на самом деле $Lambda overline(psi)$ — проективная
  трансвекция из $Delta_1$) и не перестановочен с $Lambda overline(tau)$
  (применить @prop:omeara-rich-projective-centralizer к группе, порожденной
  всеми проективными трансвекциями из $Delta_1$). Пусть
  $overline(sigma) = overline(psi) overline(tau) overline(psi)^(-1)
  overline(tau)^(-1) in Delta$. Тогда $overline(sigma) in PSL_n (V)$ и
  $Lambda overline(sigma) in PSL_(n_1) (V_1)$ в силу
  @prop:omeara-semilinear-normality. Кроме того, $overline(sigma)$ и
  $Lambda overline(sigma)$ нетривиальны по выбору $Lambda overline(psi)$.
  Очевидно, $overline(sigma)$ имеет представитель $sigma in SL_n (V)$, для
  которого $1 <= upright("res") sigma <= 2$. Если $upright("res") sigma = 1$, то
  все доказано. Пусть $upright("res") sigma = 2$. Используя «второй трюк» из
  доказательства теоремы @th:omeara-projective-simplicity, найдем такую
  проективную трансвекцию $overline(tau_(a,rho)) in Delta$, что
  $overline(sigma) overline(tau_(a,rho)) overline(sigma)^(-1)
  overline(tau_(a,rho))^(-1)$ — нетривиальная проективная трансвекция из
  $Delta$. Тогда
  $
    Lambda(
      overline(sigma) overline(tau_(a,rho)) overline(sigma)^(-1)
      overline(tau_(a,rho))^(-1)
    ) in PSL_(n_1) (V_1),
  $
  и снова все доказано.

  2) Заметим теперь, что если $Lambda$ отображает нетривиальную проективную
  трансвекцию $overline(sigma) in Delta$ в группу $PSL_(n_1) (V_1)$, то для
  каждой прямой $L subset.eq P$ существует по крайней мере одна нетривиальная
  проективная трансвекция $overline(tau) in Delta$ с пространствами
  $L subset.eq P$, такая, что $Lambda overline(tau)$ лежит в $PSL_(n_1) (V_1)$.
  При #source(129)доказательстве этого утверждения можно считать, что
  $L != F x_1$. Выберем базу $x_1, dots, x_n$ пространства $V$ и сопряженную
  базу $rho_1, dots, rho_n$ так, чтобы было
  $overline(sigma) = overline(tau_(x_1,rho_n))$, $L = F x_2$. Пусть элемент
  $alpha in dot(F)$ таков, что $overline(tau_(alpha x_2,rho_1)) in Delta$. Тогда
  наше утверждение следует из коммутаторного соотношения
  $
    overline(tau_(alpha x_2,rho_n))
    = [overline(tau_(alpha x_2,rho_1)), overline(tau_(x_1,rho_n))].
  $

  3) В силу двойственности, если $Lambda$ отображает нетривиальную проективную
  трансвекцию $overline(sigma) in Delta$ в $PSL_(n_1) (V_1)$, то для каждой
  гиперплоскости $H$, содержащей $R$, существует по крайней мере одна
  нетривиальная проективная трансвекция $overline(tau) in Delta$ с
  пространствами $R subset.eq H$, такая, что $Lambda overline(tau)$ лежит в
  $PSL_(n_1) (V_1)$.

  4) Утверждение теперь легко доказывается при помощи рассуждений п. 5)
  доказательства @prop:omeara-linear-transvection-preservation.
]

#numbered-paragraph[
  Если $n >= 3$, $n_1 >= 2$, то существует подгруппа $G^0$ группы $G$, богатая
  трансвекциями и удовлетворяющая условию
  $ G^0 subset.eq SL_n (V), quad Psi G^0 subset.eq SL_(n_1) (V_1). $
] <prop:omeara-common-linear-rich-subgroup>
#proof[
  Аналогично доказательству @prop:omeara-common-projective-rich-subgroup. Нужно
  только проследить в начале п. 1) за выбором нетривиальной трансвекции
  $tau in G$ условием $Psi tau in.not RL_(n_1) (V_1)$. Существование такой
  трансвекции $tau$ легко следует из коммутаторных соотношений для элементарных
  трансвекций.
]

#numbered-paragraph[
  При $n >= 3$, $n_1 >= 3$ изоморфизм $Lambda$ сохраняет проективные
  трансвекции.
] <prop:omeara-general-transvection-preservation>
#proof[
  1) Применение @prop:omeara-common-projective-rich-subgroup к $Lambda$ дает
  подгруппу $Delta^0$ группы $Delta inter PSL_n (V)$, богатую проективными
  трансвекциями и такую, что
  $Lambda Delta^0 subset.eq Delta_1 inter PSL_(n_1) (V_1)$. Применение
  @prop:omeara-common-projective-rich-subgroup к $Lambda^(-1)$ дает подгруппу
  $Delta_1^0$ группы $Delta_1 inter PSL_(n_1) (V_1)$, богатую проективными
  трансвекциями и такую, что
  $Lambda^(-1) Delta_1^0 subset.eq Delta inter PSL_n (V)$. Тогда группы
  $
    Delta^* = ⟨Delta^0, Lambda^(-1) Delta_1^0⟩, quad
    Delta_1^* = ⟨Lambda Delta^0, Delta_1^0⟩
  $
  удовлетворяют условиям
  $
    Delta^0 subset.eq Delta^* subset.eq Delta inter PSL_n (V), \
    Delta_1^0 subset.eq Delta_1^* subset.eq Delta_1 inter PSL_(n_1) (V_1)
  $
  и, в частности, богаты проективными трансвекциями. Кроме того,
  $Lambda: Delta^* arrow.r.double Delta_1^*$.

  #source(130)2) Рассмотрим теперь произвольную проективную трансвекцию
  $overline(sigma) in Delta$. Пусть $overline(sigma)^*$ — проективная
  трансвекция в $Delta^*$ с теми же пространствами $R subset.eq P$, что и
  $overline(sigma)$. Ввиду @prop:omeara-linear-transvection-preservation
  $overline(sigma)_1^* = Lambda overline(sigma)^*$ является проективной
  трансвекцией. В силу @prop:omeara-general-double-centralizer
  $
    Lambda overline(sigma) in Lambda Delta(R, P)
    = Lambda C_Delta C_(Delta^*) (overline(sigma)^*) \
    = C_(Delta_1) C_(Delta_1^*) (overline(sigma)_1^*) = Delta_1 (R_1^*,P_1^*),
  $
  поэтому $Lambda overline(sigma)$ — также проективная трансвекция. Значит,
  $Lambda$ сохраняет все проективные трансвекции из $Delta$. По симметрии
  $Lambda^(-1)$ сохраняет все проективные трансвекции из $Delta_1$.
  Следовательно, $Lambda$ сохраняет проективные трансвекции.
]

#numbered-paragraph[
  При $n >= 3$, $n_1 >= 3$ имеем
  $Psi(G inter RL_n (V)) = G_1 inter RL_(n_1) (V_1)$.
] <prop:omeara-isomorphism-preserves-scalars>
#proof[
  Поступая, как в п. 1) доказательства
  @prop:omeara-general-transvection-preservation, можно найти подгруппы
  $G^* subset.eq G inter SL_n (V)$ и $G_1^* subset.eq G_1 inter SL_(n_1) (V_1)$,
  богатые трансвекциями и такие, что $Psi: G^* arrow.r.double G_1^*$. Далее, для
  всякого $sigma in G inter RL_n (V)$ имеем $sigma in C(G^*)$, откуда
  $Psi sigma in C(G_1^*)$, поэтому $Psi sigma$ лежит в централизаторе группы
  $G_1^*$ в $XiL_(n_1) (V_1)$. Но группа $G_1^*$ богата трансвекциями, поэтому,
  согласно @prop:omeara-rich-projective-centralizer,
  $Psi sigma in RL_(n_1) (V_1)$. Следовательно,
  $Psi(G inter RL_n (V)) subset.eq G_1 inter RL_(n_1) (V_1)$. Равенство следует
  из рассмотрения $Psi^(-1)$ вместо $Psi$.
]

На протяжении этих лекций $V$ обозначает $n$-мерное векторное пространство над
полем $F$, $1 <= n < infinity$, и $Delta$ — подгруппа из $PXiL_n (V)$ (или из
$PGL_n (V)$ в §~@sec:omeara-cdc и @sec:omeara-transvection-preservation),
богатая проективными трансвекциями. Чтобы упростить формулировки исключительных
ситуаций, мы будем говорить, например, что $Delta$ есть $PSL_2$ над $FF_7$, если
$F = FF_7$, $n = 2$ и $Delta = PSL_2 (V)$. Аналогично для $PSL_3$ над $FF_2$ и
т.~д.

#numbered-paragraph[
  При $n >= 3$, $n_1 = 2$ не существует изоморфизма
  $Lambda: Delta arrow.r.double Delta_1$, за исключением, возможно, случая,
  когда $Delta$ есть $PSL_3$ над $FF_2$, а $Delta_1$ есть $PSL_2$ над $FF_7$.
] <prop:omeara-dimension-two-exception>
#proof[
  Предположим, что имеется изоморфизм $Lambda: Delta arrow.r.double Delta_1$ при
  $n >= 3$, $n_1 = 2$. В силу @prop:omeara-common-projective-rich-subgroup
  существует подгруппа $Delta^0$ группы $Delta inter PSL_n (V)$, богатая
  трансвекциями и такая, что $Lambda Delta^0 subset.eq PSL_2 (V_1)$.

  1) Предположим, что характеристика поля $F$ отлична от 2. Ввиду
  @prop:omeara-self-derived-transvection (проективного варианта) существует
  нетривиальная проективная трансвекция $overline(sigma) in Delta^0$, такая, что
  $D C_(Delta^0) (overline(sigma)) != 1$. Так как
  $Lambda Delta^0 subset.eq PSL_2 (V_1)$, то существует элемент
  $sigma_1 in SL_2 (V_1)$, такой, что
  $Lambda overline(sigma) = overline(sigma)_1$ и
  $D C_(V_1) (overline(sigma)_1) != 1$. В силу
  @prop:omeara-projective-commutation-power имеем
  $C_(V_1) (overline(sigma)_1) subset.eq C_(V_1) (sigma_1^2)$, поэтому
  $D C_(V_1) (overline(sigma)_1) subset.eq overline(D C_(V_1) (sigma_1^2))$. Но
  $overline(sigma)_1^2 != 1$, так как $overline(sigma)$ — проективная
  трансвекция и характеристика поля $F$ отлична от 2. Поэтому
  $sigma_1^2 in GL_2 (V_1) - RL_2 (V_1)$, откуда ввиду #source(
    131,
  )@prop:omeara-two-dimensional-centralizer $D C_(V_1) (sigma_1^2) = 1$ и,
  значит, $D C_(V_1) (overline(sigma)_1) = 1$. Противоречие. Следовательно,
  характеристика поля $F$ должна равняться 2.

  2) Предположим, что характеристика полей $F$ и $F_1$ равна 2. Пусть снова
  $overline(sigma)$ — нетривиальная проективная трансвекция из $Delta^0$, такая,
  что $D C_(Delta^0) (overline(sigma)) != 1$. Снова имеем
  $Lambda Delta^0 subset.eq PSL_2 (V_1)$, и существует $sigma_1 in SL_2 (V_1)$ с
  $Lambda overline(sigma) = overline(sigma)_1$. Но в нашем случае
  $overline(sigma)^2 = 1$, поэтому $sigma_1^2 = alpha 1_(V_1)$ с
  $alpha^2 = (det sigma_1)^2 = 1$. Следовательно, $sigma_1$ — нетривиальный
  элемент из $SL_2 (V_1)$ с $sigma_1^2 = 1_(V_1)$. Так как $F_1$ имеет
  характеристику 2, то элемент $sigma_1$ унипотентен и поэтому является
  трансвекцией. В силу @prop:omeara-projective-centralizer-image и
  @prop:omeara-two-dimensional-centralizer
  $
    D C_(Lambda Delta^0) (overline(sigma)_1)
    subset.eq D C_(V_1) (overline(sigma)_1)
    = overline(D C_(V_1) (sigma_1)) = 1,
  $
  что противоречит соотношению $D C_(Delta^0) (overline(sigma)) != 1$.
  Следовательно, рассматриваемый случай также невозможен.

  3) Предположим, что характеристика поля $F$ равна 2, а характеристика поля
  $F_1$ отлична от 2, но исключим случай $n = 3$, $F = FF_2$. Рассмотрим
  произвольную нетривиальную проективную трансвекцию
  $overline(sigma) in Delta^0$. Тогда $overline(sigma)^2 = 1$ и
  $overline(sigma) != 1$. Имеем $Lambda overline(sigma) = overline(sigma)_1$,
  где $sigma_1$ — некоторый элемент из $SL_2 (V_1)$. Далее,
  $overline(sigma)_1^2 = 1$ и $overline(sigma)_1 != 1$. Таким образом,
  $sigma_1^2 = alpha 1_(V_1)$ для некоторого $alpha in dot(F)_1$. Но
  $det sigma_1 = 1$, поэтому $alpha^2 = 1$, т.~е. $alpha = plus.minus 1$.
  Значит, $sigma_1^2 = plus.minus 1_(V_1)$. Равенство $sigma_1^2 = 1_(V_1)$ не
  может выполняться, так как из него, предложения
  @prop:omeara-commuting-involutions и равенства $det sigma_1 = 1$ следовало бы
  $overline(sigma)_1 = 1$. Поэтому $sigma_1^2 = -1_(V_1)$. Другими словами,
  каждой нетривиальной проективной трансвекции $overline(sigma) in Delta^0$
  можно сопоставить такой элемент $sigma_1 in SL_2 (V_1)$, что
  $
    overline(sigma)_1 = Lambda overline(sigma) != 1, \
    sigma_1^2 = -1_(V_1), quad det sigma_1 = 1.
  $
  Далее, всякая гиперплоскость пространства $V$ содержит по крайней мере пять
  различных прямых, поэтому в $Delta^0$ имеется пять различных нетривиальных
  попарно перестановочных проективных трансвекций. Таким образом, в группе
  $SL_2 (V_1)$ существуют такие элементы $sigma_1$, $sigma_2$, $sigma_3$,
  $sigma_4$, $sigma_5$, что соответствующие им элементы $overline(sigma)_i$
  различны, нетривиальны, попарно перестановочны и
  $ sigma_i^2 = -1_(V_1), quad det sigma_i = 1, quad 1 <= i <= 5. $
  Ввиду проективной перестановочности
  $ sigma_i sigma_j = plus.minus sigma_j sigma_i $
  #source(132)для всех $i$, $j$. Поэтому существует такая база пространства
  $V_1$, в которой $sigma_1$ имеет матрицу
  $ mat(0, -1; 1, 0), $
  а $sigma_i$ — матрицы
  $ mat(p_i, q_i; q_i, -p_i) $
  для подходящих скаляров из $F_1$, $2 <= i <= 5$. Так как $overline(sigma)_i$
  различны, то самое большее один из элементов $p_i$ $(2 <= i <= 5)$ может
  равняться нулю, поэтому можно считать, что $overline(sigma)_2$,
  $overline(sigma)_3$, $overline(sigma)_4$ имеют представители $sigma'_2$,
  $sigma'_3$, $sigma'_4$ с матрицами
  $
    mat(1, alpha; alpha, -1), quad mat(1, beta; beta, -1), quad
    mat(1, gamma; gamma, -1),
  $
  где $alpha$, $beta$, $gamma$ различны. Кроме того, можно считать, что
  $1 + alpha beta != 0$. Но тогда $overline(sigma)_2$ и $overline(sigma)_3$ не
  перестановочны. Противоречие. Поэтому рассматриваемый случай также невозможен.

  4) Наконец, предположим, что $n = 3$, $F = FF_2$ и характеристика поля $F_1$
  отлична от 2. Тогда, очевидно, $PXiL_3 (V) = PSL_3 (V) = Delta = Delta^0$. В
  частности, $upright("card") Delta = 168$ ввиду @th:omeara-finite-orders. Кроме
  того, $Lambda Delta = Delta_1$ — подгруппа в $PSL_2 (V_1)$, богатая
  проективными трансвекциями. Пусть $p$ — характеристика поля $F_1$,
  $q = upright("card") F_1$. Очевидно, $q < infinity$, поэтому $p > 0$. Пусть
  $G_1$ — подгруппа из $SL_2 (V_1)$, богатая трансвекциями, для которой
  $P G_1 = Delta_1$. Пространство $V_1$ содержит $q + 1$ различных прямых, и мы
  видим, рассматривая подходящие степени, что существует по крайней мере $p - 1$
  различных нетривиальных трансвекций в $G_1$ с данной прямой, поэтому $G_1$
  содержит по крайней мере $(p-1)(q+1)$ различных нетривиальных трансвекций.
  Далее, если зафиксировать прямую $L$ и рассмотреть произведения $tau_L tau_K$,
  где $tau_L$ пробегает все нетривиальные трансвекции в $G_1$ с прямой $L$, а
  $tau_K$ пробегает все нетривиальные трансвекции в $G_1$ с прямыми $K$,
  отличными от $L$, то мы получим по крайней мере $(p-1)^2 q$ различных
  элементов, не являющихся трансвекциями (применить
  @prop:omeara-transvection-product). Поэтому
  $ upright("card") G_1 >= (p-1)(q+1) + (p-1)^2 q + 1. $
  Но ядро $P|_(SL_2 (V_1))$ имеет 2 элемента, поэтому
  $ upright("card") Delta_1 >= p/2 ((p-1)q + 1). $
  В частности, $p <= 7$, так как $upright("card") Delta_1 = 168$. Таким образом,
  $F_1$ может быть только одним из полей $FF_3$, $FF_5$, $FF_7$, $FF_9$,
  $FF_27$. Но число $upright("card") Delta_1$ должно делить
  $upright("card") PSL_2 (V_1)$, а из чисел 12, 60, 168, 360, 9828 на 168
  делится только само это число.

  #source(133)5) Итак, мы показали, что если существует изоморфизм
  $Lambda: Delta arrow.r.double Delta_1$, то $n = 3$, $F = FF_2$ и $F_1 = FF_7$.
  Напомним, что по исходному предположению $n_1 = 2$. Далее, $PSL_3 (V)$ —
  единственная 3-мерная группа над $FF_2$, богатая трансвекциями, поэтому
  $Delta = PSL_3$ над $FF_2$. В частности, $upright("card") Delta = 168$, откуда
  $upright("card") Delta_1 = 168$. С другой стороны, всякая богатая двумерная
  группа над $FF_7$ должна содержать $PSL_2 (V_1)$, так как $FF_7$ — простое
  поле. Следовательно, $Delta_1 supset.eq PSL_2 (V_1)$. Но
  $upright("card") Delta_1 = 168 = upright("card") PSL_2 (V_1)$, поэтому
  $Delta_1 = PSL_2$ над $FF_7$, что и требовалось доказать.
]

#numbered-paragraph[
  При $n >= 3$, $n_1 = 2$ не существует изоморфизма $Psi: G arrow.r.double G_1$.
] <prop:omeara-linear-dimension-two-exclusion>
#proof[
  Пусть, напротив, такой изоморфизм $Psi$ существует. Ввиду
  @prop:omeara-common-linear-rich-subgroup в $G inter SL_n (V)$ существует
  подгруппа $G^0$, богатая трансвекциями и такая, что
  $Psi G^0 subset.eq SL_2 (V_1)$. Рассматривая две неперестановочные трансвекции
  из $G^0$, мы видим, что должна существовать нетривиальная трансвекция
  $sigma in G^0$, такая, что $Psi sigma in.not RL_2 (V_1)$. Применяя
  коммутаторное соотношение для элементарных трансвекций, получим
  $D C_(G^0) (sigma) != 1_V$. Далее, $sigma_1 = Psi sigma$ лежит в $SL_2 (V_1)$
  и $D C_(Psi G^0) (sigma_1) != 1_(V_1)$, т.~е.
  $sigma_1 in GL_2 (V_1) - RL_2 (V_1)$ и $D C_(V_1) (sigma_1) != 1_(V_1)$, а это
  невозможно ввиду @prop:omeara-two-dimensional-centralizer.
]

#numbered-paragraph[
  Пусть $X$, $Y in cal(X)$, $L$, $K in cal(L)$, $H$, $J in cal(H)$, причем
  $L subset.eq H$, $K subset.eq J$. Тогда
  + $Delta(X) = Delta(Y) <=> X = Y$,
  + $Delta(L, H) = Delta(K, J) <=> L = K$ и $H = J$,
  + $breve(Delta(X)) = breve(Delta)(X^0)$,
  + $breve(Delta(L, H)) = breve(Delta)(H^0,L^0)$,
  + $Delta(X) inter Delta(Y) supset 1 <=> X subset.eq Y$ или $Y subset.eq X$,
  + $Delta(X)$ — максимальная подгруппа в $Delta$, состоящая из проективных
    трансвекций,
  + всякая максимальная подгруппа проективных трансвекций из $Delta$ имеет вид
    $Delta(X)$.
] <prop:omeara-maximal-transvection-subgroups>

При $n >= 3$, $n_1 >= 3$ изоморфизм $Lambda$ определяет следующее отображение
$pi: cal(X) -> cal(X)_1$. Для любого $X in cal(X)$ в силу
@prop:omeara-maximal-transvection-subgroups $Delta(X)$ является максимальной
подгруппой проективных трансвекций группы $Delta$, поэтому, согласно
@prop:omeara-general-transvection-preservation, $Lambda Delta(X)$ является
максимальной подгруппой проективных трансвекций группы $Delta_1$. Следовательно,
ввиду @prop:omeara-maximal-transvection-subgroups,
$ Lambda Delta(X) = Delta_1 (X_1) $
для некоторого единственного $X_1 in cal(X)_1$. Полагаем
$ pi X = X_1. $

#numbered-paragraph[
  #source(134)При $n >= 3$, $n_1 >= 3$ отображение $pi$ обладает следующими
  свойствами:
  + $pi: cal(X) arrow.r.double cal(X)_1$ биективно,
  + $pi$ определяется равенствами $Lambda Delta(X) = Delta_1 (pi X)$ для всех
    $X in cal(X)$,
  + $(X subset.eq Y$ или $Y subset.eq X) <=> (pi X subset.eq pi Y$ или
    $pi Y subset.eq pi X)$,
  + $(pi cal(L) = cal(L)_1$ и $pi cal(H) = cal(H)_1)$ или
    $(pi cal(L) = cal(H)_1$ и $pi cal(H) = cal(L)_1)$.
] <prop:omeara-induced-incidence-bijection>
#proof[
  Первые два утверждения очевидны, третье следует из п. 5) утверждения
  @prop:omeara-maximal-transvection-subgroups. Докажем четвертое утверждение.

  Предположим, что $pi L in cal(L)_1$ для некоторой прямой $L in cal(L)$, тогда
  ввиду 3) для всякой гиперплоскости $H supset.eq L$ либо $pi L subset.eq pi H$,
  либо $pi L supset.eq pi H$. Но $pi L != pi H$ в силу инъективности, поэтому
  $pi L subset pi H$, так как $pi L$ — прямая. Другими словами, если
  $pi L in cal(L)_1$ для некоторой прямой $L in cal(L)$, то $pi H in cal(H)_1$
  для всех гиперплоскостей $H$, содержащих $L$. Двойственное рассуждение
  показывает, что если $pi H in cal(H)_1$ для некоторой гиперплоскости $H$, то
  $pi L in cal(L)_1$ для всех прямых $L subset.eq H$. Аналогично, если
  $pi L in cal(H)_1$ для некоторой прямой $L in cal(L)$, то $pi H in cal(L)_1$
  для всех гиперплоскостей $H$, содержащих $L$. Кроме того, если
  $pi H in cal(L)_1$ для некоторого $H in cal(H)$, то $pi L in cal(H)_1$ для
  всех прямых $L$, содержащихся в $H$.

  Предположим теперь, что существует такая прямая $L_0$, что
  $pi L_0 in cal(L)_1$. Тогда, включив $L_0$ и произвольную прямую $L$ из $V$ в
  гиперплоскость и применяя полученные выше результаты, видим, что
  $pi cal(L) subset.eq cal(L)_1$. Применяя доказанное выше к произвольной
  гиперплоскости и одной из ее прямых, получаем $pi cal(H) subset.eq cal(H)_1$.
  Но $pi(cal(L) union cal(H)) = cal(L)_1 union cal(H)_1$. Значит,
  $pi cal(L) = cal(L)_1$ и $pi cal(H) = cal(H)_1$.

  Таким образом, можно предполагать, что $pi cal(L) subset.eq cal(H)_1$. Тогда
  по указанной выше причине $pi cal(H) subset.eq cal(L)_1$. Значит,
  $pi cal(L) = cal(H)_1$ и $pi cal(H) = cal(L)_1$, что и требовалось показать.
]

#numbered-paragraph[
  При $n >= 2$, $n_1 >= 2$ из существования изоморфизма
  $Lambda: Delta arrow.r.double Delta_1$ следует, что $n = n_1$, за исключением,
  возможно, случая, когда одна из групп $Delta$, $Delta_1$ есть $PSL_3$ над
  $FF_2$, а другая — $PSL_2$ над $FF_7$.
] <prop:omeara-projective-dimension-invariance>
#proof[
  Ввиду @prop:omeara-dimension-two-exception можно считать, что $n >= 3$,
  $n_1 >= 3$. Рассматривая, если необходимо, изоморфизм $Lambda^(-1)$, можно
  считать, что $n >= n_1 >= 3$. В частности, отображение
  $pi: cal(X) arrow.r.double cal(X)_1$ существует. Переходя, если нужно, к
  композиции
  $
    Delta arrow.r.double^Lambda Delta_1 arrow.r.double^(breve(quad))
    breve(Delta)_1,
  $
  можно считать, что
  $ pi cal(L) = cal(L)_1, quad pi cal(H) = cal(H)_1. $

  #source(135)Для произвольного подпространства $U$ из $V$ положим
  $ Pi U = sum_(L subset.eq U) pi L. $
  В силу @prop:omeara-induced-incidence-bijection отображение $Pi$ согласовано с
  $pi$ на $cal(X) = cal(L) union cal(H)$. Кроме того,
  $ U subset.eq W => Pi U subset.eq Pi W. $
  Рассматривая строго возрастающую цепочку $n + 1$ подпространств из $V$, видим,
  что все будет доказано, если убедиться, что
  $ U subset W => Pi U subset Pi W. $
  Рассмотрим для этого в пространстве $V$ пару $U subset W$ и выберем прямую $L$
  и гиперплоскость $H$, такие, что
  $ L subset.eq W, quad U subset.eq H, quad L ⊈ H. $
  Тогда
  $ Pi L subset.eq Pi W, quad Pi U subset.eq Pi H, quad Pi L ⊈ Pi H, $
  так как $Pi$ согласуется с $pi$ на $L$ и $H$. Если $Pi U = Pi W$, то будем
  иметь
  $ Pi L subset.eq Pi W = Pi U subset.eq Pi H, $
  чего не может быть. Значит, $Pi U subset Pi W$, что и требовалось доказать.
]

#numbered-paragraph[
  Предположим, что $n >= 3$, $n_1 >= 3$ и отображение $pi$, ассоциированное с
  $Lambda$, удовлетворяет условию
  $ pi cal(L) = cal(L)_1 quad "и" quad pi cal(H) = cal(H)_1. $
  Пусть $Phi$ — изоморфизм группы $Delta$ в группу $PXiL_(n_1) (V_1)$, такой,
  что каждый элемент из $Phi Delta(L)$ является проективной трансвекцией с
  вычетной прямой $pi L$ для всех $L in cal(L)$. Тогда $Phi = Lambda$.
] <prop:omeara-incidence-determines-isomorphism>
#proof[
  Пусть $k$ — произвольный элемент из $Delta$. Мы должны показать, что
  $Phi k = Lambda k$. Рассмотрим произвольную прямую $L$ из $V$. Тогда $pi L$ —
  произвольная прямая из $V_1$. Пусть $tau_L$ — проективная трансвекция из
  $Delta$ с вычетной прямой $L$. Тогда, согласно
  §~@sec:omeara-geometric-isomorphisms, $k tau_L k^(-1)$ — проективная
  трансвекция из $Delta$ с вычетной прямой $k L$. Обозначим ее через
  $tau_(k L)$. Далее, $Phi tau_L$ — проективная трансвекция из
  $PXiL_(n_1) (V_1)$ с вычетной прямой $pi L$. Обозначим ее через $tau_(pi L)$.
  Аналогично $Phi tau_(k L)$ — проективная трансвекция из $PXiL_(n_1) (V_1)$ с
  вычетной прямой $pi(k L)$ и, значит, можно написать
  $Phi tau_(k L) = tau_(pi(k L))$. Имеем
  $
    tau_(pi(k L)) = Phi(tau_(k L)) = Phi(k tau_L k^(-1))
    = (Phi k)(tau_(pi L))(Phi k)^(-1)
  $
  и поэтому
  $ (Phi k)(pi L) = pi(k L), $

  #source(136)согласно §~@sec:omeara-geometric-isomorphisms. Для $Lambda$ также
  имеем
  $ (Lambda k)(pi L) = pi(k L). $
  Следовательно,
  $ (Phi k)(pi L) = (Lambda k)(pi L). $
  Другими словами, $Phi k$ и $Lambda k$ согласованы на прямых из $V_1$. Поэтому
  $Phi k = Lambda k$ ввиду @prop:omeara-projectivity-preservation, т.~е.
  $Phi = Lambda$.
]

#theorem[
  Пусть $Delta$, $Delta_1$ — подгруппы из $PXiL_n (V)$, $PXiL_(n_1) (V_1)$
  соответственно, богатые трансвекциями, и $n >= 3$, $n_1 >= 3$. Тогда всякий
  изоморфизм $Lambda: Delta arrow.r.double Delta_1$ имеет точно одну из
  следующих двух форм: либо
  $ Lambda k = g k g^(-1), quad k in Delta, $
  для некоторой единственной проективной коллинеации $g$ пространства $V$ на
  $V_1$, либо
  $ Lambda k = h breve(k) h^(-1), quad k in Delta, $
  для некоторой единственной проективной коллинеации $h$ пространства $V'$ на
  $V_1$.
] <th:omeara-projective-isomorphisms>
#proof[
  Ввиду @prop:omeara-projective-dimension-invariance имеем $n = n_1 >= 3$.

  1) Как показывает рассмотрение двойственной ситуации

  #align(center, duality-triangle())

  в вопросе о существовании можно считать, что отображение $pi$ из
  @prop:omeara-induced-incidence-bijection удовлетворяет условию
  $ pi cal(L) = cal(L)_1 quad "и" quad pi cal(H) = cal(H)_1, $
  и достаточно доказать существование такого $g$, что $Lambda k = g k g^(-1)$
  для всех $k in Delta$.

  Ввиду @prop:omeara-induced-incidence-bijection для любых $L in cal(L)$,
  $H in cal(H)$ с $L subset.eq H$ имеем $pi L subset.eq pi H$. Поэтому применимо
  @prop:omeara-projectivity-fixed-dimension и $pi$ можно единственным образом
  продолжить до проективности $g: PP(V) arrow.r.double PP(V_1)$. По основной
  теореме проективной геометрии $g$ является проективной коллинеацией. Далее,
  сужение
  $ Phi_g k = g k g^(-1), quad k in Delta, $
  отображения $Phi_g$ из §~@sec:omeara-geometric-isomorphisms является
  изоморфизмом группы $Delta$ в группу $PXiL_(n_1) (V_1)$. Кроме того, снова
  согласно §~@sec:omeara-geometric-isomorphisms, для #source(137)любой прямой
  $L$ из $V$ группа $Phi_g (Delta(L))$ состоит из проективных трансвекций группы
  $PXiL_(n_1) (V_1)$ с вычетной прямой $g L = pi L$. Следовательно, согласно
  @prop:omeara-incidence-determines-isomorphism, $Phi_g = Lambda$, т.~е.
  <passage:omeara-projective-isomorphism-uniqueness-reference>
  $ Lambda k = g k g^(-1), quad k in Delta, $
  что и требовалось доказать.

  2) Теперь рассмотрим вопрос о единственности. Если имеются две проективные
  коллинеации $g$ и $j$ пространства $V$ на $V_1$, такие, что
  $ g k g^(-1) = Lambda k = j k j^(-1), quad k in Delta, $
  то для любой прямой $L in cal(L)$ имеем
  $ g tau_L g^(-1) = j tau_L j^(-1), $
  где $tau_L in Delta$ — произвольная нетривиальная проективная трансвекция с
  вычетной прямой $L$. Поэтому, согласно §~@sec:omeara-geometric-isomorphisms,
  $g L = j L$. Но $g$ и $j$, будучи проективностями, ввиду
  @prop:omeara-projectivity-preservation полностью определяются своими
  значениями на прямых, откуда $g = j$. Единственность $h$ получается теперь из
  единственности $g$ для изоморфизма $breve(Delta) arrow.r.double Delta_1$.
  Наконец, равенство
  $ g k g^(-1) = h breve(k) h^(-1) quad "для всех" quad k in Delta $
  невозможно. В самом деле, рассмотрим проективные трансвекции $tau_1$, $tau_2$
  из $Delta$ с одинаковыми вычетными прямыми, но различными неподвижными
  гиперплоскостями. Тогда этим же свойством обладают $g tau_1 g^(-1)$ и
  $g tau_2 g^(-1)$, в то время как $h breve(tau)_1 h^(-1)$ и
  $h breve(tau)_2 h^(-1)$ не обладают им.
]

#theorem(base: [@th:omeara-projective-isomorphisms], suffix: "A")[
  Изоморфные проективные группы коллинеаций, богатые проективными трансвекциями,
  имеют одинаковые размерности, за исключением, возможно, случая, когда одна из
  групп есть $PSL_3$ над $FF_2$, а другая $PSL_2$ над $FF_7$.
] <th:omeara-projective-dimension-corollary>
#theorem(base: [@th:omeara-projective-isomorphisms], suffix: "B")[
  Изоморфные проективные группы коллинеаций, богатые проективными трансвекциями
  и имеющие общую размерность $>= 3$, имеют изоморфные основные поля.
] <th:omeara-projective-field-corollary>
#theorem(base: [@th:omeara-projective-isomorphisms], suffix: "C")[
  При $n >= 3$ изоморфизмы между подгруппами, богатыми трансвекциями, группы
  $PXiL_n (V)$ индуцируются ее автоморфизмами.
] <th:omeara-projective-extension-corollary>
#theorem(base: [@th:omeara-projective-isomorphisms], suffix: "D")[
  При $n >= 3$ имеем $|Aut PXiL_n (V) : upright("Int") PXiL_n (V)| = 2$.
] <th:omeara-projective-outer-corollary>

#source(138)Здесь $Aut X$ обозначает группу автоморфизмов произвольной группы
$X$, а $upright("Int") X$ обозначает нормальную подгруппу группы $Aut X$,
состоящую из всех внутренних автоморфизмов группы $X$.

#theorem[
  Пусть $G$, $G_1$ — подгруппы из $XiL_n (V)$, $XiL_(n_1) (V_1)$ соответственно,
  богатые трансвекциями. Пусть $n >= 3$, $n_1 >= 3$. Тогда всякий изоморфизм
  $Psi: G arrow.r.double G_1$ имеет точно одну из двух форм: либо
  $ Psi k = chi(k) g k g^(-1), quad k in G, $
  где $chi$ — отображение группы $G$ в $RL_(n_1) (V_1)$, а $g$ — коллинеация
  пространства $V$ на $V_1$, либо
  $ Psi k = chi(k) h breve(k) h^(-1), quad k in G, $
  где $chi$ — отображение группы $G$ в $RL_(n_1) (V_1)$, а $h$ — коллинеация
  пространства $V'$ на $V_1$.
] <th:omeara-collineation-isomorphisms>
#proof[
  Очевидно, группы $overline(G)$ и $overline(G)_1$ богаты проективными
  трансвекциями. Если положить
  $
    overline(Psi) overline(k) = overline(Psi k)
    quad "для" quad overline(k) in overline(G),
  $
  то, ввиду @prop:omeara-isomorphism-preserves-scalars, $overline(Psi)$ —
  корректно определенный изоморфизм группы $overline(G)$ на $overline(G)_1$. По
  теореме @th:omeara-projective-isomorphisms $overline(Psi)$ имеет точно одну из
  двух форм: либо
  $ overline(Psi) overline(k) = overline(g) overline(k) overline(g)^(-1), $
  для некоторой проективной коллинеации $overline(g)$ пространства $V$ на $V_1$,
  либо
  $
    overline(Psi) overline(k) = overline(h) breve(overline(k)) overline(h)^(-1),
  $
  для некоторой проективной коллинеации $overline(h)$ пространства $V'$ на
  $V_1$. В первом случае имеем коллинеацию $g$ пространства $V$ на $V_1$, такую,
  что элементы $Psi k$ и $g k g^(-1)$ группы $XiL_(n_1) (V_1)$ удовлетворяют
  условию
  $ overline(Psi k) = overline(g k g^(-1)). $
  Стало быть, в ядре $RL_(n_1) (V_1)$ существует элемент $chi(k)$, зависящий от
  $k$ и такой, что
  $ Psi k = chi(k) g k g^(-1). $

  #source(139)Аналогично в случае $h$. Применяя $breve(quad)$ и используя
  теорему @th:omeara-projective-isomorphisms, находим, что $Psi$ не может
  одновременно иметь $g$-вид и $h$-вид.
]
#theorem(base: [@th:omeara-collineation-isomorphisms], suffix: "A")[
  Изоморфные группы коллинеаций, богатые трансвекциями, имеют одинаковые
  размерности, если обе эти размерности $>= 2$.
] <th:omeara-collineation-dimension-corollary>
#theorem(base: [@th:omeara-collineation-isomorphisms], suffix: "B")[
  Изоморфные группы коллинеаций, богатые трансвекциями, имеют изоморфные
  основные поля, если их (общая) размерность $>= 3$.
] <th:omeara-collineation-field-corollary>
#remark[
  Если группы $G$ и $G_1$ из теоремы @th:omeara-collineation-isomorphisms
  являются группами линейных преобразований, т.~е. содержатся в $GL_n (V)$ и
  $GL_(n_1) (V_1)$ соответственно, то $chi$ — групповой гомоморфизм, однозначно
  определенный изоморфизмом $Psi$, а коллинеация $g$ (соответственно $h$)
  определена однозначно с точностью до растяжения пространства $V_1$.
] <prop:omeara-linear-character-uniqueness>
#remark[
  Если группы $G$ и $G_1$ из теоремы @th:omeara-collineation-isomorphisms не
  только линейны, но и удовлетворяют условию $D G = G$ и $D G_1 = G_1$
  (например, если $G = SL_n (V)$ и $G_1 = SL_(n_1) (V_1)$), то функция $chi$
  тривиальна, т.~е.
  $ Psi k = g k g^(-1), quad k in G, $
  или
  $ Psi k = h breve(k) h^(-1), quad k in G. $
] <prop:omeara-perfect-collineation-isomorphisms>
