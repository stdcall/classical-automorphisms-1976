
#import "diagrams/omeara-rich-transvections.typ": *
#import "main-defs.typ": *
#import "statements.typ": *

=== Сохранение проективных трансвекций в линейном случае
<sec:omeara-transvection-preservation>

Напомним, что в §~@sec:omeara-cdc и @sec:omeara-transvection-preservation мы
предполагаем, что группы $G$ и $Delta$ обладают следующими дополнительными
свойствами:
$
  Delta subset.eq PGL_n, quad G = P^(-1) Delta inter XiL_n, quad
  G subset.eq GL_n.
$
Чтобы применить результаты §~@sec:omeara-cdc к группам $G_1$ и $Delta_1$, мы
предполагаем всюду в §~@sec:omeara-transvection-preservation, что $G_1$ и
$Delta_1$ также имеют #source(119)дополнительные свойства
$
  Delta_1 subset.eq PGL_(n_1), quad G_1 = P^(-1) Delta_1 inter XiL_(n_1),
  quad G_1 subset.eq GL_(n_1).
$
Наша цель — показать, что при этих предположениях всякий изоморфизм
$Lambda: Delta arrow.r.double Delta_1$ сохраняет проективные трансвекции, если
размерности соответствующих пространств $>= 3$. Начнем с доказательства того,
что «$Lambda$ сохраняет вычет 2 хотя бы один раз».

#numbered-paragraph[
  Пусть $n >= 3$, $n_1 >= 3$. Исключим из рассмотрения случай, когда $F$ имеет
  характеристику $!= 2$, а $F_1 = FF_2$. Тогда существуют $sigma in D G$,
  $sigma_1 in D G_1$ с $upright("res") sigma = upright("res") sigma_1 = 2$,
  такие, что $Lambda overline(sigma) = overline(sigma)_1$. Более того, для
  данной трансвекции $tau in G$ с пространствами $L subset.eq H$ преобразования
  $sigma$ и $sigma_1$ можно выбрать так, что будет $sigma tau != tau sigma$,
  $ L subset.eq R, quad H supset.eq P, quad sigma|_R in.not RL_2 (R) $
  и
  $ R_1 inter P_1 = 0, quad sigma_1|_(R_1) in.not RL_2 (R_1). $
] <prop:omeara-isomorphism-preserves-residue-two>
#proof[
  1) Имеем $Lambda overline(tau) = overline(Phi)$ для некоторого $Phi in G_1$.
  Так как $overline(Phi) != 1$, то в пространстве $V_1$ существует такая прямая
  $L_1 = F_1 a$, что $Phi L_1 != L_1$. Выберем гиперплоскость $H_1$ в $V_1$ так,
  чтобы было
  $ L_1 subset.eq H_1, quad Phi L_1 ⊈ H_1, quad Phi^(-1) L_1 ⊈ H_1 $
  (почему это возможно?). Имеем
  $
    L_1 ⊈ Phi H_1, quad H_1 != Phi H_1, \
    dim(L_1 + Phi L_1) = 2, quad dim(H_1 inter Phi H_1) = n_1 - 2
  $
  <passage:omeara-hyperplane-intersection-dimension>
  и
  $ V_1 = (L_1 + Phi L_1) ⊕ (H_1 inter Phi H_1). $

  2) Зафиксируем $rho in V'_1$ с $Ker rho = H_1$. Разумеется, существует
  несколько ненулевых $a$ в $L_1$, таких, что $tau_(a,rho) in G_1$, так как
  $G_1$ богата трансвекциями. Мы утверждаем, что найдется по крайней мере один
  такой вектор $a$, для которого $Phi$ не является проективно перестановочным с
  $tau_(a,rho) Phi^(-1) tau_(a,rho)^(-1)$. Предположим, что это не выполняется
  при первом выборе $a$. Тогда существует такой скаляр $alpha in F_1$, что
  $
    Phi tau_(a,rho) Phi^(-1) tau_(a,rho)^(-1)
    = alpha tau_(a,rho) Phi^(-1) tau_(a,rho)^(-1) Phi,
  $
  т.~е.
  $
    tau_(Phi a,rho Phi^(-1)) tau_(-a,rho)
    = alpha tau_(a,rho) tau_(-Phi^(-1)a,rho Phi).
  $
  #source(120)Отсюда
  $
    (alpha-1)x + ((alpha+1)(rho x)
      - alpha(rho Phi x)(rho Phi^(-1)a))a + \
    + ((rho x)(rho Phi^(-1)a) - (rho Phi^(-1)x))Phi a
    = alpha(rho Phi x)Phi^(-1)a
  $
  для всех $x in V_1$. Полагая $x = a$, находим, что векторы $a$, $Phi a$,
  $Phi^(-1)a$ линейно зависимы, т.~е. лежат в некоторой плоскости. Беря $x$ вне
  этой плоскости, получим, что $alpha = 1$. Таким образом,
  $
    (2(rho x) - (rho Phi x)(rho Phi^(-1)a))a
    + ((rho x)(rho Phi^(-1)a) - (rho Phi^(-1)x))Phi a = \
    = (rho Phi x)Phi^(-1)a.
  $
  Если $F_1 != FF_2$, то ввиду @prop:omeara-two-transvections можно заменить в
  этом равенстве $a$ на $lambda a$ для некоторого $lambda != 0, 1$. Тогда два
  эти равенства (для $a$ и $lambda a$) дают
  $ (rho Phi x)(rho Phi^(-1)a) = lambda(rho Phi x)(rho Phi^(-1)a), $
  что противоречиво, так как $lambda != 1$ и $rho Phi^(-1)a != 0$. Итак, если
  $F_1 != FF_2$ и вектор $a$ не годится, то подходит вектор $lambda a$. С другой
  стороны, если $F_1 = FF_2$, то $Phi^2 = 1_(V_1)$, так как $tau$ — трансвекция
  и 1 — единственный ненулевой скаляр в $F_1$. Наше равенство принимает вид
  $ (rho Phi x)(rho Phi a)a + (rho x)(rho Phi a)Phi a = 0, $
  а это противоречит независимости векторов $a$ и $Phi a$. Утверждение доказано.

  3) Итак, мы имеем $rho in V'_1$ с $Ker rho = H_1$ и ненулевой вектор $a$ в
  $L_1$, такой, что $tau_(a,rho) in G_1$ и $Phi$ не является проективно
  перестановочным с $tau_(a,rho) Phi^(-1) tau_(a,rho)^(-1)$. Выберем $psi in G$
  так, чтобы было $Lambda overline(psi) = overline(tau_(a,rho))$, и положим
  $
    sigma = tau psi tau^(-1) psi^(-1) in D G, quad
    sigma_1 = Phi tau_(a,rho) Phi^(-1) tau_(a,rho)^(-1) in D G_1.
  $
  Очевидно, $Lambda overline(sigma) = overline(sigma)_1$. Кроме того, $tau$ не
  перестановочно с $psi tau^(-1) psi^(-1)$, поэтому $sigma tau != tau sigma$.

  4) Что касается преобразования $sigma_1$, то достаточно проверить равенства
  $ R_1 = L_1 + Phi L_1, quad P_1 = H_1 inter Phi H_1, $
  так как тогда соотношения $upright("res") sigma_1 = 2$ и $R_1 inter P_1 = 0$
  очевидны, а условие $sigma_1|_(R_1) in.not RL_2 (R_1)$ является следствием
  того, что по теореме @prop:omeara-generation-2-1-8 большая дилатация вычета 2
  не может быть #source(121)произведением двух трансвекций. Далее, $sigma_1$ —
  произведение двух трансвекций с пространствами $Phi L_1 subset.eq Phi H_1$ и
  $L_1 subset.eq H_1$. Кроме того, $Phi H_1 + H_1 = V_1$, поэтому
  $R_1 = L_1 + Phi L_1$ ввиду @prop:omeara-residue-product-equality. Наконец,
  $L_1 inter Phi L_1 = 0$, поэтому $P_1 = H_1 inter Phi H_1$, снова в силу
  @prop:omeara-residue-product-equality.

  5) Теперь рассмотрим $sigma$. Достаточно проверить, что
  $ psi L != L, quad R = L + psi L, quad P = H inter psi H, quad R ⊈ P, $
  так как тогда условия $upright("res") sigma = 2$, $L subset.eq R$,
  $H supset.eq P$ очевидны, а $sigma|_R in.not RL_2 (R)$ следует из теоремы
  @prop:omeara-generation-2-1-8, как и выше. Очевидно, $psi L != L$, иначе
  трансвекция $tau$ была бы перестановочна с трансвекцией
  $psi tau^(-1) psi^(-1)$. Точно так же $psi H != H$, поэтому $R$ и $P$ имеют
  требуемый вид. Наконец, $R ⊈ P$, так как иначе
  $L + psi L subset.eq H inter psi H$,
  <passage:omeara-residue-fixed-intersection>
  т.~е. $L subset.eq psi H$ и $psi L subset.eq H$, т.~е. $tau$ была бы
  перестановочна с $psi tau^(-1) psi^(-1)$ ввиду
  @prop:omeara-transvection-commutation. Предложение доказано.
]

Теперь мы покажем, что «$Lambda$ сохраняет хотя бы раз вычет 1».

#numbered-paragraph[
  Если $n >= 3$, $n_1 >= 3$, то существуют элементы $tau in D G$,
  $tau_1 in D G_1$, с $upright("res") tau = upright("res") tau_1 = 1$, такие,
  что $Lambda overline(tau) = overline(tau)_1$.
] <prop:omeara-isomorphism-preserves-residue-one>
#proof[
  1) Пусть обе размерности $>= 4$. В случае необходимости, меняя местами $V$,
  $n$, $F$ и $V_1$, $n_1$, $F_1$ и рассматривая $Lambda^(-1)$ вместо $Lambda$,
  можно считать, что характеристика поля $F$ равна 2, если $F_1 = FF_2$.
  Рассмотрим произвольную нетривиальную трансвекцию $T in G$, удовлетворяющую
  условию $T in D C(T)$. Пусть $L subset.eq H$ — пространства трансвекции $T$. В
  силу @prop:omeara-isomorphism-preserves-residue-two существуют $sigma in D G$,
  $sigma_1 in D G_1$ с $upright("res") sigma = upright("res") sigma_1 = 2$,
  такие, что $Lambda overline(sigma) = overline(sigma)_1$, $sigma T != T sigma$
  и
  $
    L subset.eq R, quad H supset.eq P, quad sigma|_R in.not RL_2 (R), \
    R_1 inter P_1 = 0, quad sigma_1|_(R_1) in.not RL_2 (R_1).
  $
  Очевидно, что $overline(T)$ — нетривиальная проективная трансвекция из
  $Delta(R, P)$. Но в силу @prop:omeara-residue-two-cdc-inclusion
  $Delta(R, P) subset.eq C D C(overline(sigma))$, поэтому
  $overline(T) in C D C(overline(sigma))$. Далее,
  $overline(sigma) overline(T) != overline(T) overline(sigma)$ и
  $overline(sigma) in Delta(R, P) subset.eq C D C(overline(sigma))$, поэтому
  $overline(T)$ — нецентральный элемент из $C D C(overline(sigma))$ и
  $overline(T) in D C(overline(T))$. Следовательно, $Lambda overline(T)$ — также
  нецентральный элемент из $C D C(overline(sigma)_1)$ и
  $Lambda overline(T) in D C(Lambda overline(T))$.

  1a) Рассмотрим сначала случай, когда $F_1 != FF_2$ или $n_1 != 4$. Тогда,
  согласно @prop:omeara-residue-two-cdc-equality,
  $Lambda overline(T) in C D C(overline(sigma)_1) = Delta(R_1, P_1)$. Поэтому
  $Lambda overline(T)$ имеет в группе $G_1$ представитель $sigma_3$ с
  $R_3 subset.eq R_1$ и $P_3 supset.eq P_1$. На самом деле $R_3 subset R_1$, так
  как в противном случае было бы $R_3 = R_1$,
  $P_3 = P_1$ <passage:omeara-image-fixed-space>
  и, если $sigma_3$ не является большой #source(122)дилатацией, то, согласно
  @prop:omeara-residue-two-not-derived, было бы
  $overline(sigma)_3 in.not D C(overline(sigma)_3)$, что противоречит включению
  $Lambda overline(T) in D C(Lambda overline(T))$; если же $sigma_3$ — большая
  дилатация, то она была бы центральным элементом в $G_1 (R_1,P_1)$, что
  противоречит нецентральности элемента $Lambda overline(T)$ в
  $C D C(overline(sigma)_1)$. Итак, $R_3 subset R_1$. Тем самым доказано, что
  если $T$ — произвольная трансвекция из $G$ и $T in D C(T)$, то
  $Lambda overline(T) = overline(sigma)_3$ для некоторого $sigma_3$ из $G_1$ с
  $upright("res") sigma_3 = 1$. Ввиду @prop:omeara-self-derived-transvection для
  данных $L subset.eq H$ в группе $G$ всегда найдется трансвекция $T$ с
  пространствами $L subset.eq H$, такая, что $T in D C(T)$. Рассматривая
  элементарные трансвекции, легко найти в группе $G$ такие трансвекции $T_i$
  $(1 <= i <= 3)$, что $T_i in D C(T_i)$ и $T_1 = [T_2,T_3]$. В силу только что
  доказанного, каждая трансвекция $Lambda overline(T)_i$ имеет в группе $G_1$
  представитель $phi_i$ с $upright("res") phi_i = 1$. Поэтому
  $Lambda overline(T)_1$ имеет в $G_1$ представитель с вычетом 1, а в $D G_1$
  представитель с вычетом $<= 2$. Так как $n_1 >= 4$, то эти представители
  должны совпадать. Другими словами, $Lambda overline(T)_1 = overline(tau)_1$
  для некоторого $tau_1 in D G_1$ с $upright("res") tau_1 = 1$. Положим
  $tau = T_1$.

  1b) Рассмотрим теперь случай, когда $F_1 = FF_2$ и $n_1 = 4$. Разумеется,
  тогда характеристика поля $F$ равна 2. Так как $T$ — трансвекция в
  характеристике 2, то $overline(T)^2 = 1$. Ввиду того что $F_1 = FF_2$,
  $Lambda overline(T)$ имеет в $G_1$ представитель $sigma_3$ с $sigma_3^2 = 1$,
  т.~е. $Lambda overline(T)$ — проективное унипотентное преобразование, лежащее
  в $C D C(overline(sigma)_1)$. Отсюда, в силу
  @prop:omeara-residue-two-cdc-unipotents, следует, что $Lambda overline(T)$ —
  проективная трансвекция. Далее, ввиду @prop:omeara-self-derived-transvection в
  группе $G$ существует нетривиальная трансвекция $T$, удовлетворяющая условию
  $T in D C(T)$. Для нее преобразование $Lambda overline(T)$ должно иметь
  представитель $tau_1 in G_1$, являющийся трансвекцией. В частности,
  $upright("res") tau_1 = 1$. Но $G_1 = SL_4 (V_1)$, так как $F_1 = FF_2$.
  Поэтому в силу @prop:omeara-commutators-3-3-3 $tau_1 in G_1 = D G_1$. Положим
  $tau = T$.

  2) Пусть теперь одна из размерностей равна 3, другая $>= 4$. Переходя, если
  необходимо, к обратному изоморфизму, можно считать, что $n = 3$, $n_1 >= 4$.

  2a) Сначала предположим, что характеристика поля $F$ равна 2, если
  $F_1 = FF_2$. В этом случае процедура точно такая же, как в п. 1), за
  единственным исключением, когда элемент $sigma$ имеет вычет 2, $n = 3$,
  $det sigma = 1$, $sigma$ диагонализируем над $F$ и $sigma^3 = 1$ — тогда
  @prop:omeara-residue-two-cdc-inclusion нельзя применить. Покажем, что на самом
  деле этот исключительный случай невозможен. Пусть, напротив, он имеет место.
  Если характеристика поля $F_1$ равна 3, то $overline(sigma)^3 = 1$, откуда
  $overline(sigma)_1^3 = 1$, и, значит, $sigma_1^3 = 1_(V_1)$, так как
  $upright("res") sigma_1 = 2$. Далее, $(sigma_1|_(R_1))^3 = 1_(R_1)$, поэтому
  преобразование $sigma_1|_(R_1)$ унипотентно на плоскости $R_1$. Отсюда
  следует, что $sigma_1|_(R_1)$ — трансвекция, а значит, и $sigma_1$ —
  трансвекция, так как $R_1 inter P_1 = 0$. Но это #source(123)невозможно,
  поскольку $upright("res") sigma_1 = 2$. С другой стороны, если характеристика
  поля $F_1$ не равна 3, то мы используем тот факт, что ввиду
  @exm:omeara-projective-commutation-three группа $⟨(C_V (overline(sigma)))^3⟩$
  абелева. Группа $⟨(C(overline(sigma)))^3⟩$ тогда также абелева, следовательно,
  и группа $⟨(C(overline(sigma)_1))^3⟩$ абелева. Но $C(sigma_1)$ заведомо
  содержит неперестановочные трансвекции, и их кубы также неперестановочны,
  поскольку характеристика не равна 3. Снова получаем противоречие.

  2b) Пусть теперь характеристика поля $F$ не равна 2, а $F_1 = FF_2$.
  Зафиксируем гиперплоскость $H_1$ в $V_1$, пусть $L_1$ — переменная прямая в
  $H_1$. Так как группа $D Delta_1$ богата проективными трансвекциями, то
  существует трансвекция $tau_1 in G_1$ с пространствами $L_1 subset.eq H_1$,
  такая, что $overline(tau)_1 in D Delta_1$. Прообраз
  $Lambda^(-1) overline(tau)_1$ лежит в $D Delta = overline(D G)$, поэтому имеет
  в $D G$ представитель $sigma$, в частности, $det sigma = 1$. Далее,
  $tau_1^2 = 1_(V_1)$, так как $tau_1$ — трансвекция в характеристике 2, поэтому
  $sigma^2 = alpha 1_V$ и $alpha^3 = 1$. Заменив $tau_1$ на $tau_1^3$, можно
  считать, что на самом деле $sigma^2 = 1_V$. Гиперплоскость $H_1$ содержит по
  крайней мере четыре различные прямые, поэтому в группе $G_1$ можно найти
  различные попарно перестановочные трансвекции $tau_1, dots, tau_5 = 1$, для
  которых соответствующие $sigma_1, dots, sigma_5 = 1_V$ являются попарно
  проективно перестановочными инволюциями с определителем 1. Как легко следует
  из @prop:omeara-involution-residue, инволюции $-sigma_1, dots, -sigma_4$,
  $sigma_5$ имеют вычет $<= 1$, поэтому, ввиду
  @prop:omeara-projective-commutation, $sigma_1, dots, sigma_5$ попарно
  перестановочны. В силу @prop:omeara-commuting-involutions
  $
    upright("card")(overline(sigma)_1, dots, overline(sigma)_5)
    <= 2^(3-1) = 4,
  $
  а это противоречит тому, что $overline(tau)_1, dots, overline(tau)_5$
  различны.

  3) Пусть обе размерности равны 3. В силу
  @prop:omeara-self-derived-transvection существует трансвекция $tau in G$ с
  $tau in D C(tau)$. В частности, $tau in D G$ и $upright("res") tau = 1$. Так
  как $overline(tau) in D C(overline(tau))$, то
  $
    Lambda overline(tau) in D C(Lambda overline(tau))
    subset.eq D Delta_1 = overline(D G_1).
  $
  Следовательно, можно выбрать такой элемент $tau_1 in D G_1$, что
  $Lambda overline(tau) = overline(tau)_1$ и
  $overline(tau)_1 in D C(overline(tau)_1)$.

  3a) Если по крайней мере одна из характеристик $!= 2, 3$, то можно считать,
  что такова характеристика поля $F$. Тогда, согласно
  @prop:omeara-three-dimensional-transvection-powers, $tau_1^18$ является
  трансвекцией. Остается заменить $tau$ на $tau^18$.

  3b) Если обе характеристики равны 3, то в силу
  @prop:omeara-three-dimensional-transvection-powers $tau_1^2$ является
  трансвекцией. Заменим $tau$ на $tau^2$.

  3c) Если обе характеристики равны 2, рассуждаем точно так же, используя
  $tau_1^9$.

  #source(124)3d) Осталось разобрать случай, когда одна характеристика равна 3,
  а другая — 2. Можно считать, что характеристику 3 имеет поле $F$, а 2 — поле
  $F_1$. Если $F_1 != FF_2$, то поступаем, как в пункте 2b). Пусть $F_1 = FF_2$.
  Тогда $Delta_1 = PSL_3 (V_1)$, так что $upright("card") Delta_1 = 168$ по
  теореме @th:omeara-finite-orders. Если $F = FF_3$, то
  $PSL_3 (V) subset.eq Delta subset.eq PGL_3 (V)$ и
  $upright("card") PSL_3 (V) = 5616$, так что в этом случае изоморфизм
  $Lambda: Delta arrow.r.double Delta_1$ невозможен. Если
  $upright("card") F > 3$, то $V$ содержит $q^2 + q + 1$ прямых, где
  $q = upright("card") F$, поэтому имеет по крайней мере 91 прямую. Отсюда
  следует, что $Delta$ имеет по крайней мере 182 проективные трансвекции и,
  значит, изоморфизм $Lambda$ снова невозможен. Предложение доказано.
]

#numbered-paragraph[
  Если $n >= 3$, $n_1 >= 3$, то $Lambda$ сохраняет проективные трансвекции.
] <prop:omeara-linear-transvection-preservation>
#proof[
  1) Заметим сначала, что если $Lambda$ сохраняет проективную трансвекцию
  $overline(sigma) in Delta$ и $overline(tau)$ — произвольная проективная
  трансвекция из $Delta$ с теми же пространствами, что и $overline(sigma)$, то
  $Lambda$ сохраняет $overline(tau)$, причем пространства у
  $Lambda overline(tau)$ те же, что и у $Lambda overline(sigma)$. Это следует из
  включения
  $
    Lambda overline(tau) in Lambda Delta(R, P)
    = Lambda C C(overline(sigma)) \
    = C C(Lambda overline(sigma)) = Delta_1 (R_1,P_1)
  $
  $(Lambda overline(sigma) = overline(sigma)_1)$, которое вытекает из
  @prop:omeara-transvection-double-centralizer.

  2) Далее, заметим, что если $Lambda$ сохраняет проективные трансвекции
  $overline(sigma)$ и $overline(tau)$ из $Delta$ и $overline(sigma)$,
  $overline(tau)$ имеют одинаковые неподвижные гиперплоскости, то у
  $Lambda overline(sigma)$, $Lambda overline(tau)$ совпадают либо неподвижные
  гиперплоскости, либо вычетные прямые. В самом деле, ввиду п. 1) можно считать,
  что $overline(sigma)$ и $overline(tau)$ имеют различные вычетные прямые.
  Существует база $x_1, dots, x_n$ пространства $V$ и сопряженная база
  $rho_1, dots, rho_n$ пространства $V'$, такие, что
  $
    overline(sigma) = overline(tau_(x_1,rho_n)), quad
    overline(tau) = overline(tau_(x_2,rho_n)).
  $
  Пусть $overline(tau_(alpha x_1,rho_2))$ — нетривиальная проективная
  трансвекция из $Delta$. Тогда
  $
    overline(tau_(alpha x_1,rho_n))
    = [overline(tau_(alpha x_1,rho_2)), overline(tau_(x_2,rho_n))]
  $
  — нетривиальная проективная трансвекция из $Delta$ с теми же пространствами,
  что и у $overline(sigma)$, поэтому ввиду 1)
  $Lambda overline(tau_(alpha x_1,rho_n))$ — проективная трансвекция из
  $Delta_1$ с теми же пространствами, что и у $Lambda overline(sigma)$. Но
  $
    (Lambda overline(tau_(alpha x_1,rho_n))) dot (Lambda overline(tau)) \
    = (Lambda overline(tau_(alpha x_1,rho_2))) dot (Lambda overline(tau))
    dot (Lambda overline(tau_(alpha x_1,rho_2)))^(-1)
  $
  в силу приведенного выше коммутаторного соотношения, поэтому выражение в левой
  части есть проективная трансвекция. Ввиду
  @prop:omeara-projective-transvection-product, у проективных трансвекций
  $Lambda overline(tau_(alpha x_1,rho_n))$, $Lambda overline(tau)$ #source(
    125,
  )совпадают либо неподвижные гиперплоскости, либо вычетные прямые.
  Следовательно, это же справедливо и для $Lambda overline(sigma)$,
  $Lambda overline(tau)$.

  3) Покажем теперь, что если $Lambda$ сохраняет нетривиальную проективную
  трансвекцию $overline(sigma) in Delta$, то $Lambda$ сохраняет все проективные
  трансвекции группы $Delta$ с той же неподвижной гиперплоскостью, что и у
  $overline(sigma)$. Пусть $overline(tau)$ — такая трансвекция. Мы можем снова
  считать, что выбрана база, в которой
  $
    overline(sigma) = overline(tau_(x_1,rho_n)), quad
    overline(tau) = overline(tau_(x_2,rho_n)).
  $
  Пусть $overline(tau_(alpha x_2,rho_1))$ — нетривиальная проективная
  трансвекция из $Delta$. Тогда
  $
    overline(tau_(alpha x_2,rho_n))
    = [overline(tau_(alpha x_2,rho_1)), overline(tau_(x_1,rho_n))] \
    = (overline(tau_(alpha x_2,rho_1)) overline(tau_(x_1,rho_n))
      overline(tau_(alpha x_2,rho_1))^(-1)) overline(tau_(x_1,rho_n))^(-1) \
    = overline(tau_(x_1 + alpha x_2,rho_n)) overline(tau_(x_1,rho_n))^(-1).
  $
  Очевидно, что проективные трансвекции $overline(tau_(x_1 + alpha x_2,rho_n))$
  и $overline(tau_(x_1,rho_n)) = overline(sigma)$ сопряжены в $Delta$ и имеют
  одинаковые неподвижные гиперплоскости. По предположению
  $Lambda overline(sigma)$ — проективная трансвекция, поэтому и
  $Lambda overline(tau_(x_1 + alpha x_2,rho_n))$ — проективная трансвекция,
  причем в силу п. 2) она имеет ту же вычетную прямую или ту же неподвижную
  гиперплоскость, что и $Lambda overline(sigma)$. Следовательно,
  $Lambda overline(tau_(alpha x_2,rho_n))$, будучи произведением проективных
  трансвекций, у которых совпадают либо прямые, либо гиперплоскости, является
  проективной трансвекцией. Поэтому ввиду 1) преобразование
  $Lambda overline(tau) = Lambda overline(tau_(x_2,rho_n))$ является проективной
  трансвекцией.

  4) Если изоморфизм $Lambda$ сохраняет нетривиальную проективную трансвекцию
  $overline(sigma) in Delta$, то он сохраняет все проективные трансвекции из
  $Delta$, у которых вычетные прямые такие же, как у $overline(sigma)$. Для
  доказательства надо воспользоваться двойственностью.

  #align(center, duality-triangle())

  5) $Lambda$ сохраняет по крайней мере одну нетривиальную проективную
  трансвекцию $overline(sigma) in Delta$ в силу
  @prop:omeara-isomorphism-preserves-residue-one. Пусть $overline(tau)$ — любая
  другая нетривиальная проективная трансвекция из $Delta$. Пусть $L subset.eq H$
  — ее пространства. Так как $Lambda$ сохраняет $overline(sigma)$, то, согласно
  3), $Lambda$ сохраняет и проективные трансвекции из $Delta$, у которых
  неподвижная гиперплоскость такая же, как у $overline(sigma)$, а вычетная
  #source(126)прямая содержится в $P inter H$. Следовательно, согласно 4),
  $Lambda$ сохраняет некоторую проективную трансвекцию из $Delta$ с вычетной
  прямой из $P inter H$ и неподвижной гиперплоскостью $H$. Отсюда ввиду 3)
  следует, что $Lambda$ сохраняет $overline(tau)$.

  #align(center, transvection-chain())

  Таким образом, $Lambda$ сохраняет все проективные трансвекции из $Delta$. По
  той же причине $Lambda^(-1)$ сохраняет все проективные трансвекции из
  $Delta_1$. Значит, $Lambda$ сохраняет проективные трансвекции, что и
  требовалось доказать.
]
