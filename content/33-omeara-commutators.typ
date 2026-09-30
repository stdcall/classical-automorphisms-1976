#import "main-defs.typ": *
#import "statements.typ": *

=== Коммутанты <sec:omeara-commutators>

#numbered-paragraph[
  Любые две неединичные трансвекции на $V$ сопряжены относительно $GL_n$ при
  произвольном $n$ и относительно $SL_n$ при $n >= 3$.
] <prop:omeara-transvections-conjugate>

#proof[
  Будем предполагать, что $n >= 2$. Запишем данные трансвекции в виде
  $tau_(a,rho)$ и $tau_(a',rho')$, где $rho a = rho' a' = 0$. Возьмем базу
  $x_1, dots, x_n$ пространства $V$, в которой $x_1 = a$ и
  $ rho x_1 = dots = rho x_(n-1) = 0, quad rho x_n = 1; $
  аналогично, возьмем базу $x'_1, dots, x'_n$, где $x'_1 = a'$ и
  $ rho' x'_1 = dots = rho' x'_(n-1) = 0, quad rho' x'_n = 1. $
  #source(81)Возьмем преобразование $sigma$ из $GL_n (V)$, для которого
  $sigma x_i = x'_i$, $1 <= i <= n$. Тогда $sigma a = a'$ и
  $rho sigma^(-1) = rho'$, поэтому
  $
    sigma tau_(a,rho) sigma^(-1) = tau_(sigma a,rho sigma^(-1)) = tau_(a',rho').
  $
  Если $n >= 3$, то определим $sigma$, полагая $sigma x_i = x'_i$ при $i != 2$ и
  $sigma x_2 = lambda x'_2$, где $lambda$ выбрано так, что $det sigma = 1$.
]

#numbered-paragraph[
  Если $L$ и $L'$ — две произвольные прямые в $V$, то множество трансвекций с
  вычетной прямой $L$ и множество трансвекций с вычетной прямой $L'$ сопряжены
  относительно $SL_n$.
] <prop:omeara-transvection-sets-conjugate>

#proof[
  Можно считать, что $n >= 2$. В группе $SL_n$ существует такой элемент $Sigma$,
  что $Sigma L = L'$. Указанные множества сопряжены посредством $Sigma$.
]

#numbered-paragraph[
  Всегда $SL_n = D GL_n = D SL_n$, кроме следующих двух исключений:
  $
    SL_2 (bb(F)_3) = D GL_2 (bb(F)_3) supset D SL_2 (bb(F)_3), \
    SL_2 (bb(F)_2) supset D GL_2 (bb(F)_2) = D SL_2 (bb(F)_2).
  $
  При $n > 1$ во всех случаях $D SL_n supset.eq SL_n inter RL_n$.
] <prop:omeara-commutators-3-3-3>

#proof[
  Можно считать, что $n >= 2$. Заметим, что во всех случаях
  $SL_n supset.eq D GL_n supset.eq D SL_n$.

  1) Если $n >= 3$, то для двух различных индексов $i$, $j$ можно найти третий
  индекс $k$, отличный от $i$ и $j$. Из @sec:omeara-matrices получаем, что
  $ t_(i j) (lambda) = [t_(i k) (lambda), t_(k j) (1)] in D SL_n, $
  следовательно, все элементарные матрицы принадлежат группе $D SL_n$. По
  теореме @th:omeara-elementary-generation $SL_n subset.eq D SL_n$, откуда
  $SL_n = D GL_n = D SL_n$.

  2) Допустим, что $n = 2$ и $upright("card") F >= 4$. Найдется такое $lambda$
  из $dot(F)$, что $lambda^2 != 1$. Для любого $mu$ из $F$
  $
    mat(lambda, 0; 0, lambda^(-1)) mat(1, mu; 0, 1)
    mat(lambda, 0; 0, lambda^(-1))^(-1) mat(1, mu; 0, 1)^(-1)
    = mat(1, mu(lambda^2 - 1); 0, 1),
  $
  поэтому $t_(1 2) (F) subset.eq D SL_2$. Аналогично,
  $t_(2 1) (F) subset.eq D SL_2$. Дальнейшее очевидно.

  3) Пусть теперь $n = 2$ и $F = bb(F)_3$. Равенство $SL_2 = D GL_2$
  доказывается так же, как в пункте 2), только вместо матрицы
  $mat(lambda, 0; 0, lambda^(-1))$ надо взять $mat(lambda, 0; 0, 1)$, где
  $lambda != 0, 1$.

  #source(82)Пусть по определению
  $
    G = plus.minus brace(
      mat(1, 0; 0, 1) comma mat(-1, 1; 1, 1) comma
      mat(1, 1; 1, -1) comma mat(0, -1; 1, 0)
    ).
  $
  Легко видеть, что $G$ — нормальная подгруппа в $SL_2$. (Достаточно проверить
  инвариантность $G$ относительно сопряжений элементарными матрицами.) По
  теореме @th:omeara-finite-orders группа $SL_2 (bb(F)_3)$ имеет порядок $24$,
  следовательно, факторгруппа $SL_2 \/ G$ имеет порядок $3$, а потому абелева.
  Значит, $D SL_2 subset.eq G$. Подходящими подстановками в равенстве
  $
    mat(1, lambda; 0, 1) mat(1, 0; mu, 1)
    mat(1, lambda; 0, 1)^(-1) mat(1, 0; mu, 1)^(-1) = \
    = mat(
      1 + lambda mu + lambda^2 mu^2, -lambda^2 mu;
      lambda mu^2, 1 - lambda mu
    )
  $
  легко показать, что $D SL_2 = G$.

  4) Наконец, пусть $n = 2$ и $F = bb(F)_2$. Ясно, что $GL_2 = SL_2$, откуда
  $D GL_2 = D SL_2$. Пусть по определению
  $ G = brace(mat(1, 0; 0, 1) comma mat(1, 1; 1, 0) comma mat(0, 1; 1, 1)). $
  Тогда $G$ — подгруппа в $SL_2$. По теореме @th:omeara-finite-orders порядок
  группы $SL_2 (bb(F)_2)$ равен $6$. Следовательно, $G$ — нормальная подгруппа
  индекса $2$ в $SL_2$. Так как факторгруппа $SL_2 \/ G$ абелева, то
  $D SL_2 subset.eq G$. Из @sec:omeara-centres следует, что группа $SL_2$
  неабелева, поэтому $D SL_2 = G$.
]

#numbered-paragraph[
  Имеем $PSL_n = D PGL_n = D PSL_n$, кроме двух следующих исключений:
  $
    PSL_2 (bb(F)_3) = D PGL_2 (bb(F)_3) supset D PSL_2 (bb(F)_3), \
    PSL_2 (bb(F)_2) supset D PGL_2 (bb(F)_2) = D PSL_2 (bb(F)_2).
  $
  Во всех случаях при $n > 1$ имеем $D PSL_n != 1$.
] <prop:omeara-projective-commutators>

#proof[
  Применить предложение @prop:omeara-commutators-3-3-3, учитывая теоремы о
  гомоморфизмах и равенство $f(D G) = D(f G)$, справедливое для любого
  гомоморфизма $f$ группы $G$.
]
