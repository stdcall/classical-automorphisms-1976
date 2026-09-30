#import "main-defs.typ": *
#import "statements.typ": *

== Теорема <sec:ojanguren-theorem>

В данном параграфе мы докажем следующее обобщение классической основной теоремы
проективной геометрии.

#theorem(numbered: false)[
  Пусть $M$, $N$ — свободные модули конечного ранга $>= 3$ над коммутативными
  кольцами $A$ и $B$ соответственно. Если $alpha: P(M) arrow.r P(N)$ —
  проективность, то существуют изоморфизм $sigma: A arrow.r B$ и
  $sigma$-полулинейный изоморфизм $Phi: M arrow.r N$, такие, что
  $alpha = P(Phi)$. Если $sigma_i: A arrow.r B$ — изоморфизм и
  $Phi_i: M arrow.r N$ есть $sigma_i$-полулинейный изоморфизм, $i = 1, 2$,
  причем $P(Phi_1) = P(Phi_2)$, то $sigma_1 = sigma_2$ и существует такое
  $b in B$, что $Phi_1 = b Phi_2$.
] <th:ojanguren-fundamental-projective-geometry>
#proof[
  Пусть $e_1, dots, e_n$ — база модуля $M$ и $alpha A e_i = B f_i$,
  $1 <= i <= n$. Докажем, что $f_1, dots, f_n$ порождают $B$-модуль $N$. Так как
  всякий элемент модуля $N$ является линейной комбинацией элементов его базы, то
  достаточно проверить, что всякий унимодулярный элемент $f in N$ является
  линейной комбинацией элементов $f_1, dots, f_n$. Если $e in M$ — унимодулярный
  элемент и $alpha A e = B f$, $e = sum_(i=1)^n a_i e_i$, то
  $A e subset.eq sum_(i=1)^n A e_i$ и, согласно лемме
  @lem:ojanguren-projectivity-span, $B f subset.eq sum_(i=1)^n B f_i$.

  Этим доказано, что элементы $f_1, dots, f_n$ порождают модуль $N$. Так как $B$
  — коммутативное кольцо, то $upright("ранг") N <= n$. Так как $alpha^(-1)$
  также является проективностью, то $upright("ранг") M = upright("ранг") N$ и
  элементы $f_1, dots, f_n$ образуют базу модуля $N$.

  Пусть $alpha A e_1 = B f_1$, $alpha A e_2 = B g_2$. Элемент $e_1 + e_2$
  унимодулярен и $A(e_1 + e_2) subset.eq A e_1 + A e_2$, поэтому
  $alpha A(e_1 + e_2) subset.eq B f_1 + B g_2$. Следовательно,
  $alpha A(e_1 + e_2) = B(b_1 f_1 + b_2 g_2)$. Так как
  $A e_2 subset.eq A e_1 + A(e_1 + e_2)$, то
  $B g_2 subset.eq B f_1 + B(b_1 f_1 + b_2 g_2)$. Таким образом,
  $g_2 = b f_1 + c(b_1 f_1 + b_2 g_2)$. Так как $f_1$ и $g_2$ независимы, то
  $c b_2 = 1$, т.~е. $b_2$ — обратимый элемент в $B$. Аналогично показываем, что
  $b_1$ также обратим. Взяв $f_2 = b_1^(-1) b_2 g_2$, видим, что $f_2$
  унимодулярен, $B f_2 = B g_2$ и $alpha A(e_1 + e_2) = B(f_1 + f_2)$. Проделав
  эту процедуру для каждого $i > 1$, получим базу $f_1, dots, f_n$ модуля $N$,
  такую, что
  $
           alpha A e_i & = B f_i,        & 1 <= i <= n, \
    alpha A(e_1 + e_i) & = B(f_1 + f_i), & 2 <= i <= n.
  $
  <eq:ojanguren-normalized-bases>

  #source(169)Как и раньше, ясно, что
  $alpha A(e_1 + a e_2) = B(b_1 f_1 + b_2 f_2)$ для всякого $a in A$ и $b_1$
  обратим в $B$. Таким образом, можно написать
  $ alpha A(e_1 + a e_2) = B(f_1 + sigma(a) f_2), $
  <eq:ojanguren-ring-map-definition>
  где $sigma: A arrow.r B$ — корректно определенное отображение. Очевидно,
  $ sigma(0) = 0, quad sigma(1) = 1. $ <eq:ojanguren-ring-map-unit>

  Для любого фиксированного $i > 2$ аналогично можно определить
  $tau: A arrow.r B$, удовлетворяющее условию
  $ alpha A(e_1 + a e_i) = B(f_1 + tau(a) f_i), $
  <eq:ojanguren-other-coordinate-map>
  причем
  $ tau(0) = 0, quad tau(1) = 1. $ <eq:ojanguren-other-coordinate-unit>

  Так как $e_1 + a e_2 + a' e_i in A(e_1 + a e_2) + A e_i$, то
  $alpha A(e_1 + a e_2 + a' e_i) subset.eq B(f_1 + sigma(a) f_2) + B f_i$.
  Следовательно,
  $alpha A(e_1 + a e_2 + a' e_i) = B(b(f_1 + sigma(a) f_2) + b' f_i)$.
  Аналогично,
  $alpha A(e_1 + a e_2 + a' e_i) = B(c(f_1 + tau(a') f_i) + c' f_2)$. Комбинируя
  приведенные равенства, найдем, что
  $ alpha A(e_1 + a e_2 + a' e_i) = B(f_1 + sigma(a) f_2 + tau(a') f_i). $
  <eq:ojanguren-three-coordinate-map>

  Так как $a e_2 + e_i in A(e_1 + a e_2 + e_i) + A e_1$, то, используя
  @eq:ojanguren-three-coordinate-map и @eq:ojanguren-other-coordinate-unit,
  получим $alpha A(a e_2 + e_i) = B(b(f_1 + sigma(a) f_2 + f_i) + c f_1)$. Так
  как $alpha A(a e_2 + e_i) subset.eq B f_2 + B f_i$, то $b + c = 0$ и этим
  доказано, что
  $ alpha A(a e_2 + e_i) = B(sigma(a) f_2 + f_i). $
  <eq:ojanguren-two-coordinate-map>

  Теперь, используя @eq:ojanguren-three-coordinate-map и
  @eq:ojanguren-other-coordinate-unit, получим для $a, a' in A$ равенство
  $alpha A(e_1 + (a + a') e_2 + e_i) = B(f_1 + sigma(a + a') f_2 + f_i)$. Но
  $alpha A(e_1 + (a + a') e_2 + e_i) subset.eq
  alpha A(e_1 + a e_2) + alpha A(a' e_2 + e_i)$. Используя
  @eq:ojanguren-two-coordinate-map, получим включение
  $
    alpha A(e_1 + (a + a') e_2 + e_i) subset.eq
    B(f_1 + sigma(a) f_2) + B(sigma(a') f_2 + f_i).
  $
  С учетом всего сказанного ясно, что для $a, a' in A$ выполняется равенство
  $ sigma(a + a') = sigma(a) + sigma(a'). $ <eq:ojanguren-additivity>

  Теперь для $a, a' in A$ получаем, используя
  @eq:ojanguren-three-coordinate-map, что
  $ alpha A(e_1 + a a' e_2 + a e_i) = B(f_1 + sigma(a a') f_2 + tau(a) f_i). $
  С другой стороны, $alpha A(e_1 + a a' e_2 + a e_i) subset.eq
  alpha A e_1 + alpha A(a' e_2 + e_i)$, откуда следует равенство
  $alpha A(e_1 + a a' e_2 + a e_i) = B(b f_1 + b'(sigma(a') f_2 + f_i))$.
  Сравнивая коэффициенты, видим, что #source(
    170,
  )$sigma(a a') = tau(a) sigma(a')$. Полагая $a' = 1$, получим
  $
    sigma(a) = tau(a) quad "для всех" quad a in A
  $ <eq:ojanguren-coordinate-maps-agree>
  и
  $ sigma(a a') = sigma(a) sigma(a') quad "для" quad a, a' in A. $
  <eq:ojanguren-multiplicativity>

  Итак, отображение $sigma: A arrow.r B$, определенное формулой
  @eq:ojanguren-ring-map-definition, является гомоморфизмом. Заменив $alpha$ на
  $alpha^(-1)$, найдем гомоморфизм $sigma': B arrow.r A$, удовлетворяющий
  равенству
  $ alpha^(-1) B(f_1 + b f_2) = A(e_1 + sigma'(b) e_2), $
  причем $sigma$ и $sigma'$ взаимно обратны. Значит, $sigma: A arrow.r B$ —
  изоморфизм.

  Покажем теперь, что для $a_2, dots, a_n in A$ выполняется равенство
  $
    alpha A(e_1 + a_2 e_2 + dots + a_n e_n) &= \
    &= B(f_1 + sigma(a_2) f_2 + dots + sigma(a_n) f_n).
  $
  <eq:ojanguren-normalized-vector-map>
  По индукции можно предполагать, что
  $
    alpha A(e_1 + a_2 e_2 + dots + a_(n-1) e_(n-1)) &= \
    &= B(f_1 + sigma(a_2) f_2 + dots + sigma(a_(n-1)) f_(n-1)).
  $
  Так как
  $
    alpha A(e_1 + a_2 e_2 + dots + a_n e_n) &= \
    &subset.eq alpha A(e_1 + a_2 e_2 + dots + a_(n-1) e_(n-1)) + alpha A e_n,
  $
  то
  $
    alpha A(e_1 + a_2 e_2 + dots + a_n e_n) &= \
    &= B(b(f_1 + sigma(a_2) f_2 + dots + sigma(a_(n-1)) f_(n-1)) + b' f_n).
  $
  С другой стороны,
  $
    alpha A(e_1 + a_2 e_2 + dots + a_n e_n) &= \
    &subset.eq alpha A(e_1 + a_n e_n) + alpha A e_2 + dots + alpha A e_(n-1).
  $
  Сравнивая коэффициенты, получим $b' = b sigma(a_n)$, чем и доказано
  @eq:ojanguren-normalized-vector-map.

  Если $a_2, dots, a_n in A$ таковы, что элемент $a_2 e_2 + dots + a_n e_n in M$
  унимодулярен, то
  $
    alpha A(a_2 e_2 + dots + a_n e_n) subset.eq
    alpha A(e_1 + a_2 e_2 + dots + a_n e_n) + alpha A e_1.
  $
  <passage:ojanguren-projected-inclusion>
  Используя @eq:ojanguren-normalized-vector-map, получим
  $
    alpha A(a_2 e_2 + dots + a_n e_n) &= \
    &= B(b(f_1 + sigma(a_2) f_2 + dots + sigma(a_n) f_n) + b' f_1).
  $

  #source(171)Кроме того,
  $ alpha A(a_2 e_2 + dots + a_n e_n) subset.eq B f_2 + dots + B f_n. $
  Комбинируя эти два соотношения, получим
  $
    alpha A(a_2 e_2 + dots + a_n e_n) = B(sigma(a_2) f_2 + dots + sigma(a_n)
      f_n).
  $
  <eq:ojanguren-vanishing-first-coordinate>

  Теперь мы утверждаем, что для любых
  $a_1, dots, a_(i-1), a_(i+1), dots, a_n in A$, $i = 2, dots, n$, имеет место
  равенство
  $
    & alpha A(e_i + a_1 e_1 + dots + a_(i-1) e_(i-1)
        + a_(i+1) e_(i+1) + dots + a_n e_n) = \
    & = B(f_i + sigma(a_1) f_1 + dots + sigma(a_n) f_n).
  $
  <eq:ojanguren-normalized-other-coordinate>

  Чтобы доказать его, заметим сначала, используя @eq:ojanguren-normalized-bases
  и @eq:ojanguren-vanishing-first-coordinate, что
  $alpha A(e_i + e_j) = B(f_i + f_j)$ для любых $j != i$. Фиксируя $i$ и заменяя
  $e_1$ на $e_i$, можно повторить предыдущие рассуждения и получить изоморфизм
  $rho: A arrow.r B$, такой, что для
  $a_1, dots, a_(i-1), a_(i+1), dots, a_n in A$ справедлив следующий аналог
  равенства @eq:ojanguren-normalized-vector-map:
  $
    & alpha A(e_i + a_1 e_1 + dots + a_(i-1) e_(i-1)
        + a_(i+1) e_(i+1) + dots + a_n e_n) = \
    & = B(f_i + rho(a_1) f_1 + dots + rho(a_n) f_n).
  $
  <eq:ojanguren-renormalized-ring-map>

  Полагая в @eq:ojanguren-renormalized-ring-map $a_1 = 0$ и сравнивая результат
  с @eq:ojanguren-vanishing-first-coordinate, найдем, что $sigma = rho$. Теперь
  @eq:ojanguren-renormalized-ring-map дает
  @eq:ojanguren-normalized-other-coordinate.

  Пусть элемент $e = sum_(i=1)^n a_i e_i in M$ унимодулярен. Покажем, что
  $
    alpha A(a_1 e_1 + dots + a_n e_n) = B(sigma(a_1) f_1 + dots + sigma(a_n)
      f_n).
  $
  <eq:ojanguren-arbitrary-vector-map>
  Положим $w_i = e_i + sum_(j != i) a_j e_j$, $i = 1, 2, 3$. Элемент $w_i$
  унимодулярен, а $e = w_i + (a_i - 1) e_i$; поэтому
  $ alpha A e subset.eq B f_i + B sum_(j != i) sigma(a_j) f_j. $
  Запишем $alpha A e = B f$, $f = sum_(j=1)^n q_j f_j$. Из указанных включений
  следует, что $q_j = c_i sigma(a_j)$ при $j != i$. Для любых различных $j, k$
  можно выбрать $i in {1, 2, 3} without {j, k}$. Отсюда
  $ q_j sigma(a_k) = q_k sigma(a_j). $
  <eq:ojanguren-coefficient-relations>

  Так как элемент $e = sum a_i e_i$ унимодулярен, то отсюда следует, что и
  $sum sigma(a_i) f_i$ унимодулярен, поэтому существуют такие #source(
    172,
  )$k_1, dots, k_n in B$, что $sum sigma(a_i) k_i = 1$. Положим
  $ d = sum_(j=1)^n q_j k_j. $
  Используя @eq:ojanguren-coefficient-relations, легко проверить, что
  $d sigma(a_i) = q_i$ для всех $i$. Так как $f$ унимодулярен, а
  $q_i = d sigma(a_i)$, элемент $d$ обратим, и
  @eq:ojanguren-arbitrary-vector-map доказано.#ed-note[
    В исходном доказательстве после удаления координаты может получиться вектор,
    не представляющий точку проективного пространства. Например, над $ZZ$ вектор
    $(2, 3, 0)$ унимодулярен, а $(0, 3, 0)$ — нет. Определение $P(M)$ см. в
    #cite(<Ojanguren1976>, form: "full"), §~1.
  ]
  <passage:ojanguren-unimodular-coordinate-proof>

  Пусть $Phi: M arrow.r N$ есть $sigma$-полулинейный изоморфизм, причем
  $Phi(e_i) = f_i$. Равенство @eq:ojanguren-arbitrary-vector-map показывает, что
  $alpha = P(Phi)$. Второе утверждение теоремы доказывается точно так же, как и
  в классическом случае (см., например, @bib:ojanguren-sridharan-Artin1957, гл.
  II).
]
