#import "main-defs.typ": *
#import "statements.typ": *

== Автоморфизмы группы $GL_n (R)$ <sec:pomfret-automorphisms>

Пусть $J_(i j)$ обозначает диагональную матрицу с $-1$ на местах $(i, i)$,
$(j, j)$ и с 1 на остальных местах. Матрица $J_(i j)$ является инволюцией типа
$(2, n - 2)$, $J_(i j) J_(j k) = J_(i k)$ и множество
${J_(i j) | 1 <= i < j <= n}$ содержит $binom(n, 2)$ попарно перестановочных
инволюций.

Очень полезна

#theorem[
  Пусть $R$ — локальное кольцо. Тогда матрица $A in GL_n (R)$ имеет обратимый
  элемент в каждой строке и в каждом столбце.
] <th:pomfret-invertible-row-entry>
#proof[
  Определитель матрицы $A$ обратим и может быть получен разложением Лапласа по
  строке или столбцу, поэтому каждая строка и каждый столбец должны содержать
  обратимый элемент.
]

#remark(numbered: false)[
  Мы предполагаем в этом параграфе, что $n >= 3$, $R$ — локальное кольцо и
  характеристика поля $R / frak(m)$ отлична от 2.
]

#theorem[
  Пусть $Lambda$ — автоморфизм группы $GL_n (R)$. Тогда в $GL_n (R)$ найдется
  такая матрица $Q$, что $Lambda J_(i j) = Q^(-1) J_(i j) Q$ для всех $i != j$.
] <th:pomfret-double-sign-involutions>
#proof[
  Рассмотрим сначала инволюции типа $(1, n - 1)$, скажем $P_1, dots, P_n$. Всего
  их $n$, они попарно сопряжены и попарно перестановочны. Поэтому $n$ инволюций
  $Lambda P_1, dots, Lambda P_n$ также сопряжены, перестановочны и имеют один
  тип, скажем $(t, n - t)$. Мы хотим доказать, что $t = 1$ или $t = n - 1$.
  Очевидно, $t != 0$ и $t != n$. Допустим, что $1 < t < n - 1$ (можно считать
  также, что $n > 3$, поскольку случай $n = 3$ тривиален). Так как
  $binom(n, 1) < binom(n, t)$, то существует по крайней мере одна инволюция типа
  $(t, n - t)$, которая не #source(178)лежит в множестве
  $Lambda P_1, dots, Lambda P_n$, но сопряжена и перестановочна со всеми
  $Lambda P_i$. Тогда $Lambda^(-1) B$ перестановочна со всеми $P_i$, но отлична
  от них и сопряжена с ними. Это, однако, невозможно, так как ${P_i}$ —
  максимальное коммутативное множество инволюций типа $(1, n - 1)$. Таким
  образом, $t = 1$ или $t = n - 1$. Поэтому существует обратимая матрица $Q$,
  такая, что $Q (Lambda P_i) Q^(-1) = a P_i$, $1 <= i <= n$,
  $a = plus.minus I_n$.

  Теперь заметим, что $J_(i j) = P_i P_j$, поэтому
  $
    Lambda J_(i j) = Lambda(P_i P_j) = Lambda P_i Lambda P_j
    = Q^(-1) (a P_i) (a P_j) Q = Q^(-1) J_(i j) Q.
  $
]

Если $Lambda$ — автоморфизм группы $GL_n (R)$, то отображение
$overline(Lambda)$, определенное равенством
$overline(Lambda)(A) = Q Lambda(A) Q^(-1)$, также является автоморфизмом и
$overline(Lambda)(J_(i j)) = J_(i j)$. Можно заменить в нашем исследовании
$Lambda$ на $overline(Lambda)$ и считать, что $Lambda(J_(i j)) = J_(i j)$.

Из теоремы @th:pomfret-invertible-row-entry сразу следует

#lemma[
  Если $a, b, c, d$ — элементы локального кольца $R$ и
  $ mat(a, b; c, d)^2 = -I, quad mat(a, -b; c, -d)^2 = I, $
  то $a = d = 0$ и $c = -b^(-1)$.
] <lem:pomfret-two-dimensional-block>

Пусть $S_(i, i+1)$ обозначает подстановочную матрицу
$ S_(i, i+1) = I_(i-1) ⊕ mat(0, 1; -1, 0) ⊕ I_(n-i-1). $
Заметим, что если $D S_(i, i+1) = S_(i, i+1) D$, где $D = diag(a_1, dots, a_n)$,
то $a_i = a_(i+1)$.

#theorem[
  Пусть $Lambda$ — автоморфизм группы $GL_n (R)$. Тогда в $GL_n (R)$ существует
  такая матрица $Q$, что
  $
    Q Lambda(S_(i, i+1)) Q^(-1)
    = e I_(i-1) ⊕ mat(0, 1; -1, 0) ⊕ e I_(n-i-1),
    quad 1 <= i <= n - 1,
  $
  где $e = plus.minus 1$.
] <th:pomfret-signed-permutation-images>
#proof[
  Мы считаем, что $Lambda J_(i, i+1) = J_(i, i+1)$. Так как $J_(i, i+1)$
  перестановочна с $S_(1 2)$ при $i = 1$ или $i >= 3$, то
  $J_(i, i+1) = Lambda J_(i, i+1)$ перестановочна с $Lambda S_(1 2)$. Таким
  образом, если $n = 3$ или $n >= 5$, то
  $Lambda S_(1 2) = mat(a, b; c, d) ⊕ diag(a_3, dots, a_n)$, а если $n = 4$, то
  $Lambda S_(1 2) = mat(a, b; c, d) ⊕ mat(w, x; y, z)$. При $n = 4$ из
  соотношений
  $
    (Lambda S_(1 2))^2 = Lambda J_(1 2) = J_(1 2), quad
    (Lambda S_(1 2) Lambda J_(2 3))^2 = I
  $ <eq:pomfret-permutation-involution-relations>
  #source(179)следует $x = y = 0$, $w^2 = z^2 = 1$. Итак, при $n >= 3$
  $Lambda S_(1 2) = mat(a, b; c, d) ⊕ diag(a_3, dots, a_n)$. Снова применяя
  соотношения @eq:pomfret-permutation-involution-relations, получаем
  $c = -b^(-1)$, $a = d = 0$, $a_i = plus.minus 1$.
  <passage:pomfret-permutation-inverse-sign>

  Вообще, для $i = 1, dots, n - 1$
  $
    Lambda S_(i, i+1) = diag(a_1^((i)), dots, a_(i-1)^((i)))
    ⊕ mat(0, b_i; -b_i^(-1), 0)
    ⊕ diag(a_(i+2)^((i)), dots, a_n^((i))),
  $
  где $a_j^((i)) = plus.minus 1$. Положим
  $
    Q = diag(
      product_(t=1)^(n-1) b_t^(-1),
      product_(t=2)^(n-1) b_t^(-1), dots, b_(n-1)^(-1), 1
    )
  $
  и заметим, что $Q J_(i, i+1) Q^(-1) = J_(i, i+1)$. Таким образом, матрица
  $J_(i, i+1)$ неподвижна при сопряжении матрицей $Q$. Легко видеть, что
  $
    Q Lambda S_(i, i+1) Q^(-1)
    = diag(a_1^((i)), dots, a_(i-1)^((i)))
    ⊕ mat(0, 1; -1, 0) ⊕ diag(a_(i+2)^((i)), dots, a_n^((i))).
  $
  Довольно простые вычисления показывают, что $S_(j, j+1)$ перестановочна с
  $S_(i, i+1)$ при $1 <= j <= i - 2$, $i + 2 <= j <= n - 1$, и поэтому
  $Q Lambda(S_(i, i+1)) Q^(-1)$ перестановочна с $Q Lambda(S_(j, j+1)) Q^(-1)$
  при $1 <= j <= i - 2$, $i + 2 <= j <= n - 1$, откуда
  $a_1^((i)) = dots = a_(i-1)^((i))$ и $a_(i+2)^((i)) = dots = a_n^((i))$. Так
  как $(S_(i-1, i) S_(i, i+1))^3 = I$, то
  $(Q Lambda(S_(i-1, i)) Lambda(S_(i, i+1)) Q^(-1))^3 = I$, и повторное
  вычисление дает $a_(i-1)^((i)) = a_(i+2)^((i))$. Этим заканчивается
  доказательство.
]

Так как сопряжение матрицей $Q$ оставляет на месте инволюции $J_(i j)$, то можно
считать (ср. с замечанием перед леммой @lem:pomfret-two-dimensional-block), что
автоморфизм $Lambda$ удовлетворяет условию $Lambda J_(i j) = J_(i j)$ и
$Lambda S_(i, i+1) = e I_(i-1) ⊕ mat(0, 1; -1, 0) ⊕ e I_(n-i-1)$, где $e = 1$
или $e = -1$.

Наиболее сложным шагом в описании автоморфизма $Lambda$ является

#theorem[
  Если $Lambda$ — автоморфизм группы $GL_n (R)$, удовлетворяющий указанным выше
  условиям, то либо $Lambda B_(i j) (1) = B_(i j) (1)$ для всех $(i, j)$, либо
  $Lambda B_(i j) (1) = B_(j i) (-1)$ для всех $(i, j)$.
] <th:pomfret-elementary-unit-images>
#proof[
  #source(180)Так как матрица $B_(1 2) (1)$ перестановочна с $J_(1 2)$ и
  $J_(i, i+1)$ при $i >= 3$, то при $n != 4$ должно быть
  $ Lambda B_(1 2) (1) = mat(a, b; c, d) ⊕ diag(a_3, dots, a_n), $
  а если $n = 4$, то
  $ Lambda B_(1 2) (1) = mat(a, b; c, d) ⊕ mat(w, x; y, z). $
  Сначала покажем, что если $n != 4$, то $a_3 = dots = a_n$. Так как
  $B_(1 2) (1)$ перестановочна с $S_(i, i+1)$ при $i >= 3$, то
  $Lambda B_(1 2) (1)$ перестановочна с $Lambda S_(i, i+1)$ при $i >= 3$. В
  частности, из соотношения
  $Lambda B_(1 2) (1) Lambda S_(3 4) = Lambda S_(3 4) Lambda B_(1 2) (1)$
  имеем
  $
    e mat(a, b; c, d) ⊕ mat(0, a_3; -a_4, 0)
    ⊕ e diag(a_5, dots, a_n) \
    = e mat(a, b; c, d) ⊕ mat(0, a_4; -a_3, 0)
    ⊕ e diag(a_5, dots, a_n),
  $
  и, следовательно, $a_3 = a_4$. Аналогично заключаем, что
  $a_3 = a_4 = dots = a_n$.

  Итак, $Lambda B_(1 2) (1) = mat(a, b; c, d) ⊕ f I_(n-2)$. Покажем, что
  $f = e$. Для этого заметим, что
  $
    Lambda(B_(1 2) (1) J_(2 3))^2 = I,
  $ <eq:pomfret-transvection-involution-relation>
  $
    Lambda(S_(1 2) B_(1 2) (1))^3 = I,
  $ <eq:pomfret-transvection-permutation-relation>
  $
    Lambda(S_(2 3)^(-1) B_(1 2) (1) S_(2 3))
    = Lambda B_(1 3) (1).
  $ <eq:pomfret-transvection-conjugation>
  Из @eq:pomfret-transvection-involution-relation следует равенство $f^2 = 1$, а
  из @eq:pomfret-transvection-permutation-relation — равенство $(e f)^3 = 1$.
  Следовательно, $e f = 1$ и, так как $e = plus.minus 1$, то $f = plus.minus 1$,
  $e = f$.

  Соотношения @eq:pomfret-transvection-involution-relation,
  @eq:pomfret-transvection-permutation-relation,
  @eq:pomfret-transvection-conjugation определяют матрицу $mat(a, b; c, d)$. Из
  @eq:pomfret-transvection-involution-relation получаем, что
  $mat(a, -b; c, -d)^2 = I$, а @eq:pomfret-transvection-conjugation дает
  $
    Lambda B_(1 2) (1) Lambda(S_(2 3)^(-1) B_(1 2) (1) S_(2 3)) \
    = Lambda(S_(2 3)^(-1) B_(1 2) (1) S_(2 3)) Lambda B_(1 2) (1).
  $
  Вычисляя здесь верхние левые клетки порядка 3, получим
  $
    mat(a^2, b e, a e b; a c, d e, b e c; c, 0, e d)
    = mat(a^2, a b, b; e c, e d, 0; a e c, b e c, e d).
  $

  #source(181)Так как $e$ — обратимый элемент, то $b c = 0$, $a^2 = d^2 = 1$.
  Прямое вычисление с использованием соотношения $mat(c, d; -a, -b)^3 = I$,
  вытекающего из @eq:pomfret-transvection-permutation-relation, показывает, что
  один из элементов $b, c$ обратим и, значит, другой равен нулю (так как
  $b c = 0$). Если $c = 0$, то, в силу
  @eq:pomfret-transvection-permutation-relation, $b a d = 1$. Так как
  $a = d = plus.minus 1$, то $b = 1$. Аналогично, если $b = 0$, то $c = -1$.

  Итак, либо $Lambda B_(1 2) (1) = e I_n + E_(1 2)$, либо
  $Lambda B_(1 2) (1) = e I_n - E_(2 1)$ и, ввиду
  @eq:pomfret-transvection-conjugation, либо
  $Lambda B_(1 3) (1) = e I_n + e E_(1 3)$, либо
  $Lambda B_(1 3) (1) = e I_n - e E_(3 1)$ соответственно.

  Теперь мы утверждаем, что $e = 1$. Заметим, что
  $S_(1 2)^(-1) B_(1 3) (1) S_(1 2) = B_(2 3) (1)$, поэтому либо
  $Lambda B_(2 3) (1) = e I_n + E_(2 3)$, либо
  $Lambda B_(2 3) (1) = e I_n - E_(3 2)$ соответственно. Так как коммутатор
  $[Lambda B_(1 2) (1), Lambda B_(2 3) (1)] = Lambda B_(1 3) (1)$, то $e^4 = e$
  и, значит, $e = 1$.

  Осталось при $n != 4$ определить образы других коммутаторов.

  Предположим, что $Lambda B_(1 2) (1) = B_(1 2) (1)$, и заметим, что
  $Lambda B_(2 1) (1) = Lambda(S_(1 2)^(-1) B_(1 2) (-1) S_(1 2)) = B_(2 1)
  (1)$. Примем предположение индукции, что $Lambda B_(1 i) (1) = B_(1 i) (1)$ и
  $Lambda B_(i 1) (1) = B_(i 1) (1)$. Из равенств
  $
    S_(i, i+1)^(-1) B_(1 i) (1) S_(i, i+1) = B_(1, i+1) (1), quad
    S_(i, i+1)^(-1) B_(i 1) (1) S_(i, i+1) = B_(i+1, 1) (1)
  $
  вытекает, что $Lambda B_(1, i+1) (1) = B_(1, i+1) (1)$ и
  $Lambda B_(i+1, 1) (1) = B_(i+1, 1) (1)$. Поэтому, если
  $Lambda B_(1 2) (1) = B_(1 2) (1)$, то $Lambda B_(1 i) (1) = B_(1 i) (1)$ и
  $Lambda B_(i 1) (1) = B_(i 1) (1)$, $i = 2, 3, dots, n$.

  Используя соотношения $[B_(i j) (1), B_(j k) (1)] = B_(i k) (1)$ при различных
  $i, j, k$, получаем $Lambda B_(i j) (1) = B_(i j) (1)$ для всех $i$ и $j$.
  Если $Lambda B_(1 2) (1) = B_(2 1) (-1)$, то аналогичные рассуждения дают
  $Lambda B_(i j) (1) = B_(j i) (-1)$ для всех $i$ и $j$.

  Этим заканчивается доказательство для $n != 4$.

  Пусть теперь $n = 4$. Вычисления, которые необходимо проделать, довольно
  длинные, но не трудные, поэтому мы лишь набросаем доказательство. Так как
  матрица $Lambda B_(1 2) (1)$ перестановочна с $J_(1 2)$, то
  $ Lambda B_(1 2) (1) = mat(a, b; c, d) ⊕ mat(w, x; y, z). $
  Так как $B_(1 2) (1)$ и $S_(3 4)$ перестановочны, то $x = -y$, $z = w$. Из
  соотношения @eq:pomfret-transvection-involution-relation следует, что один из
  элементов $b, c$ обратим, $x = 0$ и $a = d = w$. Наконец, используя
  @eq:pomfret-transvection-conjugation и перестановочность матриц
  $Lambda B_(1 2) (1)$ и $Lambda B_(1 3) (1)$, заключаем, что если $b$ обратим,
  то $c = 0$, и наоборот. На этом шаге $Lambda B_(1 2) (1)$ имеет одну из
  следующих форм: либо $Lambda B_(1 2) (1) = mat(a, b; 0, a) ⊕ diag(a, a)$, либо
  $Lambda B_(1 2) (1) = mat(a, 0; c, a) ⊕ diag(a, a)$. #source(182)Дальнейшие
  рассуждения проводятся так же, как и в случае $n > 4$.
]

Заметим, что $B_(j i) (-1)$ — матрица, обратно-транспонированная к
$B_(i j) (1)$. Для $A in GL_n (R)$ обозначим матрицу $(A^t)^(-1) = (A^(-1))^t$
через $A^*$.

#theorem[
  Если $Lambda: GL_n (R) -> GL_n (R)$ — групповой автоморфизм, то существуют
  кольцевой автоморфизм $sigma: R -> R$ и матрица $P in GL_n (R)$, такие, что
  $ Lambda A = P^(-1) A^sigma P quad "для всех" A in SL_n (R) $
  или
  $ Lambda A = P^(-1) (A^sigma)^* P quad "для всех" A in SL_n (R). $
] <th:pomfret-special-linear-automorphisms>
#proof[
  В силу замечания после предложения @prop:pomfret-local-linear-generation
  группа $SL_n (R)$ порождается элементарными трансвекциями, поэтому достаточно
  найти кольцевой автоморфизм $sigma$ и обратимую матрицу $P$, такие, что
  $P Lambda B_(i j) (lambda) P^(-1) = B_(i j) (lambda^sigma)$ для всех
  $B_(i j) (lambda)$ или
  $P Lambda B_(i j) (lambda) P^(-1) = B_(j i) (-lambda^sigma)$ для всех
  $B_(i j) (lambda)$. В силу @th:pomfret-elementary-unit-images и
  @th:pomfret-signed-permutation-images можно предполагать, что
  $P Lambda B_(i j) (1) P^(-1) = B_(i j) (1)$ и
  $P Lambda S_(i, i+1) P^(-1) = S_(i, i+1)$. Так как матрица $B_(1 2) (lambda)$,
  $lambda in R$, перестановочна с $B_(1 2) (1)$ и $B_(i j) (1)$,
  $3 <= i, j <= n$, то
  $P Lambda B_(1 2) (lambda) P^(-1) = mat(a, b; 0, a) ⊕ f I_(n-2)$. Так как
  $S_(2 3)^(-1) B_(1 2) (lambda) S_(2 3) = B_(1 3) (lambda)$, то
  $
    P Lambda B_(1 3) (lambda) P^(-1)
    = mat(a, 0, b; 0, f, 0; 0, 0, a) ⊕ f I_(n-3).
  $ <eq:pomfret-transvection-ring-image>
  Коммутаторное соотношение $[B_(1 2) (lambda), B_(2 3) (1)] = B_(1 3) (lambda)$
  дает $P [Lambda B_(1 2) (lambda), Lambda B_(2 3) (1)] P^(-1)
  = P Lambda B_(1 3) (lambda) P^(-1)$ и
  <passage:pomfret-commutator-target>
  $
    P Lambda B_(1 3) (lambda) P^(-1)
    = mat(1, 0, b f a^(-2); 0, 1, 1 - f a^(-1); 0, 0, 1)
    ⊕ I_(n-3).
  $ <eq:pomfret-transvection-commutator-image>
  Теперь определим $sigma: R -> R$, полагая $lambda^sigma = beta$, если
  $P Lambda B_(1 2) (lambda) P^(-1) = I_n + beta E_(1 2)$. Очевидно,
  $P Lambda B_(i j) (lambda) P^(-1) = B_(i j) (lambda^sigma)$ и отображение
  $sigma$ аддитивно. Если $lambda^sigma = 0$, то $Lambda B_(1 2) (lambda) = I_n$
  и $lambda = 0$. Поэтому $sigma$ инъективно. Чтобы показать мультипликативность
  отображения #source(183)$sigma$, рассмотрим цепочку равенств
  $
    B_(1 3) ((lambda_1 lambda_2)^sigma)
    = P Lambda B_(1 3) (lambda_1 lambda_2) P^(-1) \
    = P [Lambda B_(1 2) (lambda_1), Lambda B_(2 3) (lambda_2)] P^(-1)
    = B_(1 3) (lambda_1^sigma lambda_2^sigma).
  $
  Итак, $sigma$ — кольцевой мономорфизм. Остается показать, что $sigma$
  сюръективно. Очевидно, $Lambda(SL_n (R))$ лежит в $SL_n (R)$ и имеет
  порядковый идеал $R$ (см. @bib:pomfret-mcdonald-Klingenberg1961). Далее,
  подгруппа $Lambda(SL_n (R))$ нормальна в $GL_n (R)$, поэтому, в силу
  результатов Клингенберга о нормальных подгруппах
  @bib:pomfret-mcdonald-Klingenberg1961, она совпадает с $SL_n (R)$. Если $r$ —
  произвольный элемент из $R$, то существует произведение
  $B = product B_(i j) (lambda_(i j))$ элементарных трансвекций, такое, что
  $P Lambda(B) P^(-1) = B_(1 2) (r)$. Следовательно, $r$ является конечной
  суммой конечных произведений элементов вида $lambda_(i j)^sigma$. Поэтому
  $sigma$ сюръективно и, значит, является автоморфизмом кольца $R$.
]

Теперь мы в состоянии описать действие автоморфизмов на группе $GL_n (R)$.
Сформулируем наши предположения полностью.

#theorem[
  Пусть $R$ — локальное кольцо, причем характеристика поля $R / frak(m)$ отлична
  от 2. Предположим, что $n >= 3$ и $Lambda: GL_n (R) -> GL_n (R)$ — групповой
  автоморфизм. Тогда существуют матрица $P in GL_n (R)$, кольцевой автоморфизм
  $sigma: R -> R$ и групповой гомоморфизм $chi: R^* -> R^*$, такие, что
  $
    Lambda A = chi(det A) P^(-1) A^sigma P
    quad "для всех" A in GL_n (R)
  $
  или
  $
    Lambda A = chi(det A) P^(-1) (A^sigma)^* P
    quad "для всех" A in GL_n (R).
  $
] <th:pomfret-general-linear-automorphisms>
#proof[
  Если $A in GL_n (R)$, то $A = D_n (r) B$, где $det A = r$, $B$ — произведение
  элементарных трансвекций. Поскольку вид $Lambda B$ уже определен, остается
  определить $Lambda D_n (r)$. Будем считать, что
  $Lambda B_(i j) (lambda) = P^(-1) B_(i j) (lambda^sigma)^* P$
  (первый случай рассматривается аналогично).
  <passage:pomfret-contragredient-case-reference>
  Для любых $(i, j)$ матрица $D_n (r) B_(i j) (1) D_n (r^(-1))$ лежит в
  $SL_n (R)$, поэтому
  $
    P (Lambda D_n (r) Lambda B_(i j) (1) Lambda D_n (r^(-1))) P^(-1) \
    = ((D_n (r) B_(i j) (1) D_n (r^(-1)))^sigma)^* \
    = D_n (r^sigma)^(-1) B_(j i) (-1) D_n (r^sigma).
  $
  Отсюда
  $
    D_n (r^sigma) P Lambda D_n (r) P^(-1) B_(j i) (-1) \
    = B_(j i) (-1) D_n (r^sigma) P Lambda D_n (r) P^(-1).
  $
  #source(184)Таким образом, матрица $D_n (r^sigma) P Lambda D_n (r) P^(-1)$
  перестановочна с $B_(j i) (-1)$ при $i != j$ и, следовательно, скалярна, т.~е.
  $ Lambda D_n (r) = ("скаляр") dot P^(-1) D_n (r^sigma)^(-1) P. $
  Определим $chi: R^* -> R^*$, полагая
  $ chi(r) = "скаляр, ассоциированный с" Lambda D_n (r). $
  Из соотношения $Lambda(D_n (r_1) D_n (r_2)) = Lambda D_n (r_1 r_2)$ следует,
  что $chi(r_1) chi(r_2) = chi(r_1 r_2)$, т.~е. $chi$ — гомоморфизм группы
  $R^*$. Этим заканчивается доказательство.
]

Кольцевые гомоморфизмы $rho_t: R -> R / frak(m)^t$ индуцируют гомоморфизмы групп
$b_t: GL_n (R) -> GL_n (R / frak(m)^t)$, $t = 1, 2, 3, dots$. Для каждого $t$
$ b_t^(-1) ("центр группы" GL_n (R / frak(m)^t)) $
есть _общая конгруэнц-подгруппа_ #idx("общая", "конгруэнц-подгруппа") #idx(
  "конгруэнц-подгруппа",
  "общая",
)по модулю $frak(m)^t$, обозначаемая через $upright("GC")_n (R, t)$.
_Специальная конгруэнц-подгруппа_ #idx(
  "специальная",
  "конгруэнц-подгруппа",
)#idx("конгруэнц-подгруппа", "специальная") $upright("SC")_n (R, t)$ по модулю
$frak(m)^t$ — это множество матриц $P$ из $GL_n (R)$, таких, что $b_t (P) = I$,
$det(P) = 1$. Для кольца $R = ZZ / (ZZ p^s)$ вычетов по модулю $p^s$, где $p$ —
простое число, с помощью комбинаторных соображений доказано, что определенные
выше конгруэнц-подгруппы автоморфно допустимы.

#corollary[
  Пусть $R$ — локальное кольцо, причем характеристика поля вычетов $R / frak(m)$
  отлична от 2. Тогда при $n >= 3$ подгруппы $upright("GC")_n (R, t)$ и
  $upright("SC")_n (R, t)$ автоморфно допустимы в $GL_n (R)$ для $t >= 1$.
] <cor:pomfret-congruence-characteristic>
#proof[
  Пусть $Lambda(A) = chi(det A) P^(-1) A^sigma P$ для всех $A$ из $GL_n (R)$
  (второй случай разбирается аналогично). Если $A in upright("GC")_n (R, t)$, то
  $A = r I + N$, где $N$ — матрица порядка $n$ с элементами из $frak(m)^t$.
  Прямое вычисление показывает, что $Lambda(A)$ лежит в
  $upright("GC")_n (R, t)$. Как показал Клингенберг
  @bib:pomfret-mcdonald-Klingenberg1961,
  $upright("SC")_n (R, t) = [GL_n (R), upright("GC")_n (R, t)]$, откуда и
  следует утверждение.
]
