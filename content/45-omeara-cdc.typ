
#import "diagrams/omeara-rich-transvections.typ": *
#import "main-defs.typ": *
#import "statements.typ": *

=== $C D C$ в линейном случае <sec:omeara-cdc>

Если определить $G$ как прообраз группы $Delta$ относительно гомоморфизма
$P|_(XiL_n)$, то $G$ будет группой, богатой трансвекциями, и потому к ней
применима теория §~@sec:omeara-rich-transvections. Если $Delta$ удовлетворяет
условию $Delta subset.eq PGL_n (V)$, то соответствующая группа $G$ будет
удовлетворять условию $G subset.eq GL_n (V)$. В §~@sec:omeara-cdc и
@sec:omeara-transvection-preservation мы будем считать, что $G$ и $Delta$
удовлетворяют этим дополнительным условиям, т.~е.
$
  Delta subset.eq PGL_n, quad G = P^(-1) Delta inter XiL_n, quad
  G subset.eq GL_n.
$
Легко видеть, что тогда $breve(G)$ и $breve(Delta)$ удовлетворяют аналогичным
условиям над $V'$, т.~е.
$
  breve(Delta) subset.eq PGL_n, quad
  breve(G) = P^(-1) breve(Delta) inter XiL_n, quad breve(G) subset.eq GL_n.
$
Будем обозначать через $C$ централизатор $C_Delta$, $C_G$, $C_(breve(Delta))$,
$C_(breve(G))$ в соответствии с тем, какая из групп $Delta$, $G$,
$breve(Delta)$, $breve(G)$ рассматривается.

#numbered-paragraph[
  Для любого $sigma$ из $G$
  $
    overline(C(sigma)) subset.eq C(overline(sigma)), quad
    overline(D C(sigma)) subset.eq D C(overline(sigma)).
  $
  Если, кроме того, $sigma$ перестановочно с каждым элементом группы $G$, с
  которым оно проективно перестановочно, то
  $
    overline(C(sigma)) = C(overline(sigma)), quad
    overline(D C(sigma)) = D C(overline(sigma)).
  $
] <prop:omeara-projective-centralizer-image>

#source(112)Для произвольных подпространств $U$, $W$ из $V$ определим
$ G(U,W) = {sigma in G | R subset.eq U, P supset.eq W}, $
$ Delta(U, W) = overline(G(U,W)). $
Согласно @prop:omeara-residue-product, $G(U,W)$ и $Delta(U, W)$ — подгруппы в
$G$ и $Delta$ соответственно, причем $Delta(U, W)$ состоит из таких
преобразований $Sigma in Delta$, которые имеют по крайней мере один
представитель $sigma$ с $R subset.eq U$ и $P supset.eq W$. Заметим, что
$
  sigma U = U, quad sigma W = W quad "для всех" sigma in G(U,W), \
  Sigma U = U, quad Sigma W = W quad "для всех" Sigma in Delta(U, W).
$

#example[
  Если $H$ — гиперплоскость в $V$ и $L$ — прямая, лежащая в $H$, то $G(L,H)$
  состоит из всех трансвекций группы $G$ с вычетной прямой $L$ и неподвижной
  гиперплоскостью $H$ и тождественного преобразования $1_V$, а $Delta(L, H)$ —
  из всех проективных трансвекций группы $Delta$ с вычетной прямой $L$ и
  неподвижной гиперплоскостью $H$ и 1.
] <exm:omeara-transvection-subgroups>

#numbered-paragraph[
  Если $U$, $W$ — подпространства в $V$, то
  $
    breve(G(U,W)) = breve(G)(W^0,U^0), quad
    breve(Delta(U, W)) = breve(Delta)(W^0,U^0).
  $
] <prop:omeara-dual-residue-subgroups>

#numbered-paragraph[
  Пусть $sigma_1$, $sigma_2$ — нетривиальные трансвекции из $G$. Тогда следующие
  утверждения равносильны:
  + $R_1 = R_2$, $P_1 = P_2$,
  + $C(sigma_1) = C(sigma_2)$,
  + $C(overline(sigma)_1) = C(overline(sigma)_2)$.
] <prop:omeara-transvection-centralizer-equality>
#proof[
  1) $=>$ 2). Пусть $R_1 = R_2$ и $P_1 = P_2$. Рассмотрим произвольный элемент
  $Sigma in C(sigma_1)$. Представим $sigma_1$ и $sigma_2$, как обычно, в виде
  $sigma_1 = tau_(a,rho)$, $sigma_2 = tau_(alpha a,rho)$. Имеем
  $
    tau_(a,rho) = Sigma tau_(a,rho) Sigma^(-1)
    = tau_(Sigma a,rho Sigma^(-1)),
  $
  поэтому $Sigma a = lambda a$, $rho Sigma^(-1) = lambda^(-1) rho$ для
  некоторого $lambda in dot(F)$, откуда
  $
    Sigma tau_(alpha a,rho) Sigma^(-1) = tau_(alpha Sigma a,rho Sigma^(-1))
    = tau_(alpha lambda a,lambda^(-1) rho) = tau_(alpha a,rho),
  $
  так что $Sigma in C(sigma_2)$. Значит, $C(sigma_1) = C(sigma_2)$.

  2) $=>$ 3). Применить @prop:omeara-projective-centralizer-image.

  3) $=>$ 1). Пусть $P_1 != P_2$. Тогда существует прямая $L$, лежащая в $P_2$,
  но не в $P_1$. Так как $G$ богата трансвекциями, то существует трансвекция
  $sigma_3$ с $R_3 = L$ и $P_3 = P_2$. Тогда $sigma_3 in C(sigma_2)$, но
  $sigma_3 in.not C(sigma_1)$ в силу @prop:omeara-transvection-commutation,
  следовательно, $overline(sigma)_3 in C(overline(sigma)_2)$, но
  $overline(sigma)_3 in.not C(overline(sigma)_1)$ в силу
  @prop:omeara-projective-commutation. Поэтому
  $C(overline(sigma)_2) != C(overline(sigma)_1)$, что противоречит нашим
  предположениям. Значит, $P_1 = P_2$. Равенство $R_1 = R_2$ получаем
  применением изоморфизма $breve(quad)$.
]

#numbered-paragraph[
  #source(113)Если $n >= 3$ и $sigma$ — нетривиальная трансвекция из $G$, то
  $ G(R,P) inter D C(sigma) != 1_V, $
  т.~е. $D C(sigma)$ содержит нетривиальную трансвекцию с теми же
  пространствами, что и данная трансвекция $sigma$.
] <prop:omeara-centralizer-derived-transvection>
#proof[
  Существует база $x_1, dots, x_n$ пространства $V$, такая, что
  $sigma = tau_(x_1,rho_n)$, где $rho_1, dots, rho_n$ — сопряженная база.
  Поэтому $R = F x_1$ и $P = Ker rho_n$. Так как $G$ богата трансвекциями, то
  для некоторых $alpha$, $beta in dot(F)$ имеем $tau_(x_1,alpha rho_2) in G$ и
  $tau_(x_2,beta rho_n) in G$. Тогда $tau_(x_1,alpha rho_2) in C(sigma)$ и
  $tau_(x_2,beta rho_n) in C(sigma)$. Положим
  $Sigma = tau_(x_1,alpha beta rho_n)$. Очевидно, $Sigma$ — трансвекция в $G$ с
  вычетной прямой $R$ и неподвижной гиперплоскостью $P$. Но
  $ Sigma = [tau_(x_1,alpha rho_2), tau_(x_2,beta rho_n)], $
  поэтому $Sigma in D C(sigma)$.
]

#numbered-paragraph[
  Если $n >= 3$, $H$ — гиперплоскость в $V$ и $L$ — прямая в $H$, то существует
  нетривиальная трансвекция $tau in G$ с пространствами $L subset.eq H$, такая,
  что $tau in D C(tau)$.
] <prop:omeara-self-derived-transvection>
#proof[
  Пусть $sigma$ — трансвекция из $G$ с пространствами $L subset.eq H$. В силу
  @prop:omeara-centralizer-derived-transvection в $G$ найдется трансвекция $tau$
  с пространствами $L subset.eq H$, такая, что $tau in D C(sigma)$. Но
  $C(tau) = C(sigma)$ ввиду @prop:omeara-transvection-centralizer-equality.
]

#numbered-paragraph[
  Если $n >= 4$ и $sigma$ — нетривиальная трансвекция из $G$, то
  $ G(L,P) inter D C(sigma) != 1_V $
  для всех прямых $L$ из $P$.
] <prop:omeara-centralizer-derived-lines>
#proof[
  Зафиксируем прямую $K$ в $P$, такую, что $K ⊈ R + L$. Пусть $M$ —
  гиперплоскость в $V$, содержащая $R + L$, но не содержащая $K$. Пусть $tau_L$
  — трансвекция из $G$ с пространствами $L subset.eq M$, а $tau_K$ — трансвекция
  из $G$ с пространствами $K subset.eq P$. В силу
  @prop:omeara-transvection-commutation $tau_L$ и $tau_K$ лежат в $C(sigma)$.

  #align(center, rich-centralizer-spaces())

  #source(114)Положим $Sigma = tau_L tau_K tau_L^(-1) tau_K^(-1)$. Очевидно,
  $Sigma in D C(sigma)$. Далее, $tau_L K != K$, так как $K ⊈ M$, и,
  следовательно, $tau_L tau_K tau_L^(-1)$ — трансвекция с вычетной прямой
  $tau_L K$, отличной от $K$, и с неподвижной гиперплоскостью $tau_L P = P$.
  Поэтому $Sigma = (tau_L tau_K tau_L^(-1)) tau_K^(-1)$ — нетривиальная
  трансвекция с неподвижной гиперплоскостью $P$. Аналогично получаем, что
  $Sigma = tau_L (tau_K tau_L^(-1) tau_K^(-1))$ имеет вычетную прямую $L$. Итак,
  $Sigma$ — неединичный элемент из $G(L,P) inter D C(sigma)$. Предложение
  доказано.
]

#numbered-paragraph[
  Пусть $sigma$ — нетривиальная трансвекция из $G$. Тогда
  $
    C C(overline(sigma)) = Delta(R, P) quad "при" n >= 2, \
    C D C(overline(sigma)) = Delta(R, P) quad "при" n >= 4.
  $
] <prop:omeara-transvection-double-centralizer>
#proof[
  1) Пусть $overline(Sigma)$ — произвольный неединичный элемент из
  $Delta(R, P)$. Ввиду @prop:omeara-transvection-centralizer-equality
  $C(overline(Sigma)) = C(overline(sigma))$, откуда
  $ overline(Sigma) in C C(overline(Sigma)) = C C(overline(sigma)) $
  и, значит, $Delta(R, P) subset.eq C C(overline(sigma))$.

  1a) Пусть сначала $n >= 3$. Рассмотрим $Sigma in G$, такой, что
  $overline(Sigma) in C C(overline(sigma))$. Для каждой прямой $L subset.eq P$
  группа $Delta$ содержит проективную трансвекцию $tau_L$ с вычетной прямой $L$
  и неподвижной гиперплоскостью $P$. В силу
  @prop:omeara-projective-transvection-commutation
  $tau_L in C(overline(sigma))$, поэтому $overline(Sigma)$ перестановочен с
  $tau_L$, а значит, и $Sigma$ перестановочен с трансвекцией, представляющей
  $tau_L$, откуда получаем, что $Sigma L = L$ для всех $L$ из $P$.
  Следовательно, существует такой элемент $alpha in dot(F)$, что неподвижное
  пространство преобразования $alpha Sigma$ содержит $P$. Применение этого
  результата к $breve(Sigma)$ и $breve(sigma)$ даст нам такое $beta in dot(F)$,
  что вычетное пространство преобразования $beta Sigma$ содержится в $R$.
  <passage:omeara-dual-residue>
  Легко видеть, что $alpha = beta$. Но тогда $alpha Sigma in G(R,P)$ и, значит,
  $overline(Sigma) in Delta(R, P)$. Тем самым равенство
  $C C(overline(sigma)) = Delta(R, P)$ доказано при $n >= 3$.

  1b) Пусть теперь $n = 2$. Снова рассмотрим $Sigma in G$, такой, что
  $overline(Sigma) in C C(overline(sigma))$. Так как
  $overline(sigma) in C(overline(sigma))$, то
  $overline(Sigma) in C(overline(sigma))$, поэтому $Sigma in C(sigma)$ в силу
  @prop:omeara-projective-commutation. Если выбрать базу пространства $V$, в
  которой $sigma$ имеет матрицу $mat(1, lambda; 0, 1)$, то матрица
  преобразования $Sigma$ в этой базе будет иметь вид $mat(p, q; 0, p)$, т.~е.
  $overline(Sigma)$ будет иметь представитель с матрицей вида
  $mat(1, alpha; 0, 1)$. Другими словами, $overline(Sigma) in Delta(R, P)$.
  Итак, при $n = 2$ также $C C(overline(sigma)) = Delta(R, P)$.

  #source(115)2) Пусть теперь $n >= 4$. Очевидно,
  $Delta(R, P) = C C(overline(sigma)) subset.eq C D C(overline(sigma))$. Для
  доказательства обратного включения поступаем как в п. 1a), используя
  проективный вариант предложения @prop:omeara-centralizer-derived-lines.
]

#numbered-paragraph[
  Предположим, что $n >= 3$. Пусть $sigma$ — элемент группы $G$ с
  $upright("res") sigma = 2$, причем $(sigma|_R)$ не является растяжением.
  Исключим также случай, когда $n = 3$, $det sigma = 1$, $sigma$ диагонализируем
  над $F$, $sigma^3 = 1$. Тогда $Delta(R, P) subset.eq C D C(overline(sigma))$.
] <prop:omeara-residue-two-cdc-inclusion>
#proof[
  1) Покажем вначале, что достаточно доказать включение
  $D C(sigma) subset.eq G(P,R)$. В самом деле, пусть оно доказано. Рассмотрим
  произвольный элемент $overline(Sigma) in D C(overline(sigma))$. Тогда
  $D C(overline(sigma)) = overline(D C(sigma))$ ввиду
  @prop:omeara-projective-commutation, @exm:omeara-projective-commutation-three
  и @prop:omeara-projective-centralizer-image, и, значит, $overline(Sigma)$
  имеет представитель $Sigma$ в $D C(sigma)$. В силу нашего предположения
  $Sigma in G(P,R)$, поэтому для каждого $phi in G(R,P)$
  $
    R_Sigma subset.eq P subset.eq P_phi, quad
    P_Sigma supset.eq R supset.eq R_phi,
  $
  т.~е. $phi$ перестановочен со всеми $Sigma in D C(sigma)$. Следовательно,
  любой элемент $overline(phi) in Delta(R, P)$ перестановочен со всеми
  $overline(Sigma) in D C(overline(sigma))$, т.~е.
  $overline(phi) in C D C(overline(sigma))$, откуда
  $Delta(R, P) subset.eq C D C(overline(sigma))$.

  2) Легко проверить, что если $sigma in G$ удовлетворяет перечисленным выше
  условиям, то $breve(sigma) in breve(G)$ также им удовлетворяет (для
  доказательства рассмотреть случаи, когда $(breve(sigma)|_(P^0))$ —
  нетривиальное растяжение и когда $(breve(sigma)|_(P^0)) = 1$). Поэтому, если
  показать, что
  $ sigma_3 in D C(sigma) => R subset.eq P_3, $
  то в силу двойственности будем иметь $P supset.eq R_3$, откуда
  $D C(sigma) subset.eq G(P,R)$, и доказательство тем самым будет закончено.
  Остается доказать импликацию. По предположению
  $sigma|_R in GL_2 (R) - RL_2 (R)$, поэтому $D C_R (sigma|_R) = 1_R$ в силу
  @prop:omeara-two-dimensional-centralizer. Но легко проверяется, что
  $ D C(sigma)|_R subset.eq D C_R (sigma|_R). $
  Следовательно, $sigma_3|_R = 1_R$, откуда $R subset.eq P_3$, что и требовалось
  доказать.
]

#numbered-paragraph[
  Пусть $n >= 4$. Пусть $sigma$ — элемент группы $G$ с
  $upright("res") sigma = 2$, $R inter P = 0$ и $sigma$ не является большой
  дилатацией. Исключим также случай, когда $n = 4$ и $F = FF_2$. Тогда
  $Delta(R, P) = C D C(overline(sigma))$.
] <prop:omeara-residue-two-cdc-equality>
#proof[
  Ввиду @prop:omeara-residue-two-cdc-inclusion достаточно убедиться, что
  $C D C(overline(sigma)) subset.eq Delta(R, P)$.

  1) Для каждой гиперплоскости $H$ пространства $P$ и каждой прямой $L$ в $H$
  зафиксируем в группе $G$ трансвекцию $tau_(L,H)$ #source(116)с вычетной прямой
  $L$ и неподвижной гиперплоскостью $R ⊕ H$.
  <passage:omeara-transvection-fixed-hyperplane> (Если $n = 4$, то $F != FF_2$,
  поэтому в силу @prop:omeara-two-transvections можно выбрать — и мы выберем —
  две различные трансвекции $tau_(L,H)$ и $tau'_(L,H)$ для любых таких $L$ и
  $H$.) Очевидно, подпространства $R$ и $P$ инвариантны относительно
  $tau_(L,H)$, $tau_(L,H)|_P$ — трансвекция с пространствами $L subset.eq H$ и
  $tau_(L,H)|_R = 1_R$ (аналогично для $tau'_(L,H)$). Пусть $G_P$ обозначает
  подгруппу в $GL_(n-2) (P)$, порожденную всеми $tau_(L,H)|_P$ (и
  $(tau'_(L,H)|_P)$ при $n = 4$). Очевидно, что $G_P$ богата трансвекциями
  (вдвойне богата при $n = 4$) и
  $
    1_R ⊕ G_P subset.eq C(sigma), \
    1_R ⊕ D G_P = D(1_R ⊕ G_P) subset.eq D C(sigma), \
    C_P (D G_P) = RL_(n-2) (P),
  $
  где последнее равенство есть следствие утверждения
  @prop:omeara-derived-centralizer.

  2) Предположим сначала, что $n >= 5$. Рассмотрим произвольный элемент
  $overline(Sigma) in C D C(overline(sigma))$, и пусть $Sigma$ — один из его
  представителей. Тогда $Sigma$ проективно перестановочен с любым элементом
  группы $1_R ⊕ D G_P$. Для любой прямой $L$ из $P$ в группе $D G_P$ существует
  трансвекция с вычетной прямой $L$, так как в силу
  @prop:omeara-rich-derived-groups $D G_P$ богата трансвекциями. Значит, и
  $1_R ⊕ D G_P$ содержит трансвекцию с вычетной прямой $L$. Ввиду
  @prop:omeara-projective-commutation $Sigma$ перестановочен с этой
  трансвекцией, откуда $Sigma L = L$ для любой прямой $L$ из $P$. В частности,
  $Sigma P = P$ и $Sigma|_P in RL_(n-2) (P)$. В силу двойственности
  $Sigma R = R$. Следовательно, $overline(Sigma) in Delta(R, P)$.

  3) Пусть $n = 4$. Теперь наши $tau_(L,H)$ можно обозначить через $tau_L$.
  Снова рассмотрим произвольный элемент
  $overline(Sigma) in C D C(overline(sigma))$, пусть $Sigma$ — один из его
  представителей. Пусть $L$, $K$ — две произвольные различные прямые в $P$.
  Ввиду @prop:omeara-transvection-commutators преобразование
  $
    (tau_L tau_K tau_L^(-1) tau_K^(-1))|_P
    = (tau_L|_P)(tau_K|_P)(tau_L|_P)^(-1)(tau_K|_P)^(-1)
  $
  лежит в $GL_2 (P) - RL_2 (P)$ и имеет вычет 2, согласно
  @prop:omeara-transvection-commutators. Следовательно, преобразование
  $tau_L tau_K tau_L^(-1) tau_K^(-1)$ имеет вычетное пространство $P$ и
  неподвижное пространство $R$, не является большой дилатацией и принадлежит
  группе $D C(sigma)$. Поэтому $Sigma$ проективно перестановочен, а потому и
  просто перестановочен с $tau_L tau_K tau_L^(-1) tau_K^(-1)$, откуда
  $Sigma R = R$, $Sigma P = P$. Далее, $Sigma$ проективно перестановочен со
  всеми элементами группы
  $ 1_R ⊕ D G_P subset.eq D C(sigma), $
  поэтому, ввиду @prop:omeara-projective-commutation, $Sigma$ перестановочен со
  всеми элементами группы $1_R ⊕ D G_P$, которые не являются большими
  дилатациями #source(117)вычета 2. Но, очевидно, $Sigma$ перестановочен и со
  всеми большими дилатациями вычета 2, т.~е. вообще со всеми элементами группы
  $1_R ⊕ D G_P$, поэтому
  $ Sigma|_P in C_P (D G_P) = RL_2 (P), $
  откуда $overline(Sigma) in Delta(R, P)$.
]

#numbered-paragraph[
  Пусть $n >= 4$. Пусть $sigma$ — элемент группы $G$ с
  $upright("res") sigma = 2$, причем $R inter P = 0$ и $sigma$ не является
  большой дилатацией. Тогда всякое проективное унипотентное преобразование из
  $C D C(overline(sigma))$ является проективной трансвекцией и лежит в
  $Delta(R, P)$.
] <prop:omeara-residue-two-cdc-unipotents>
#proof[
  Если $n >= 5$ или если $n = 4$ и $F != FF_2$, то применяем предложение
  @prop:omeara-residue-two-cdc-equality. Если же $n = 4$ и $F = FF_2$, то
  поступаем как при доказательстве @prop:omeara-residue-two-cdc-equality,
  используя третью часть предложения @prop:omeara-derived-centralizer.
]

#numbered-paragraph[
  Пусть $n >= 4$. Пусть $sigma$ — элемент группы $G$ с
  $upright("res") sigma = 2$, причем $R inter P = 0$ и $sigma$ не является
  большой дилатацией. Тогда $overline(sigma) in.not D C(overline(sigma))$.
] <prop:omeara-residue-two-not-derived>

#numbered-paragraph[
  Если $Sigma$ — элемент группы $G$ и $Sigma in D C(Sigma)$, то преобразование
  $Sigma^(n!)$ унипотентно.
] <prop:omeara-self-derived-unipotent-power>
#proof[
  Не нарушая общности, можно считать, что $F$ алгебраически замкнуто и
  $G = GL_n (V)$. Пусть $alpha$, $beta$, … — различные характеристические корни
  преобразования $Sigma$. Жорданова форма преобразования $Sigma$ дает разложения
  $
    V = V_alpha ⊕ V_beta ⊕ dots, \
    Sigma = Sigma_alpha ⊕ Sigma_beta ⊕ dots,
  $
  где все корни преобразования $Sigma_alpha$ равны $alpha$ и т.~д. Заметим, что
  $det Sigma_alpha = alpha^(n_alpha)$, где $n_alpha = dim V_alpha$, и т.~д.
  Теперь
  $
    V_alpha = {x in V | (Sigma-alpha 1_V)^k x = 0
      "для некоторого" k > 0},
  $
  откуда
  $ T in C(Sigma) => T V_alpha = V_alpha quad "и т. д." $
  Следовательно, произвольный элемент $Psi in D C(Sigma)$ имеет вид
  $ Psi = Psi_alpha ⊕ Psi_beta ⊕ dots, $
  где $Psi_alpha in SL_(n_alpha) (V_alpha)$ и т.~д. В частности,
  $Sigma_alpha in SL_(n_alpha) (V_alpha)$, откуда $alpha^(n_alpha) = 1$ и,
  значит, $alpha^(n!) = 1$ и т.~д. Поэтому все характеристические корни
  преобразования $Sigma^(n!)$ равны 1.
]

#numbered-paragraph[
  #source(118)Пусть $n = 3$. Пусть $sigma$ — элемент группы $D G$, причем
  $overline(sigma) in D C(overline(sigma))$. Тогда
  + если $sigma$ унипотентно, то $sigma$ — трансвекция,
  + $sigma^18$ — трансвекция,
  + если $F$ имеет характеристику 3, то $sigma^2$ — трансвекция,
  + если $F$ имеет характеристику 2, то $sigma^9$ — трансвекция.
] <prop:omeara-three-dimensional-transvection-powers>
#proof[
  Очевидно, можно считать, что $sigma != 1_V$.

  1) Так как $sigma$ унипотентно и $n = 3$, то $upright("res") sigma = 1$ или 2.
  Допустим, $upright("res") sigma = 2$. Тогда $sigma R = R$ и
  $sigma|_R in GL_2 (R) - RL_2 (R)$ снова ввиду унипотентности преобразования
  $sigma$. Отсюда следует, что $R$ инвариантно относительно $C(sigma)$ и ввиду
  @prop:omeara-two-dimensional-centralizer группа $D C(sigma)$ действует
  тождественно на $R$. С другой стороны,
  $overline(sigma) in D C(overline(sigma)) = overline(D C(sigma))$ в силу
  @prop:omeara-projective-commutation и
  @prop:omeara-projective-centralizer-image, поэтому $alpha sigma$ действует на
  $R$ тождественно для некоторого $alpha$. Но $sigma$ унипотентно, поэтому
  $alpha = 1$, т.~е. $sigma$ действует тождественно на $R$, а это противоречит
  нашему допущению, что $upright("res") sigma = 2$. Следовательно, на самом деле
  $upright("res") sigma = 1$. Но $det sigma = 1$, так как $sigma in D G$.
  Значит, $sigma$ — трансвекция, что и утверждалось.

  2) В силу @prop:omeara-projective-commutation-power имеем
  $C(overline(sigma)) subset.eq C(sigma^3)$, поэтому
  $overline(sigma) in D C(overline(sigma)) subset.eq overline(D C(sigma^3))$,
  откуда $alpha sigma in D C(sigma^3)$. Но $alpha^3 = 1$, так как преобразования
  $sigma$ и $alpha sigma$ имеют определитель 1. Поэтому
  $sigma^3 in D C(sigma^3)$, и в силу @prop:omeara-self-derived-unipotent-power
  преобразование $sigma^18$ унипотентно. Далее,
  $
    overline(sigma)^18 in D C(overline(sigma))
    subset.eq D C(overline(sigma)^18),
  $
  и можно применить утверждение п. 1).

  3) В силу 2), $(sigma^2)^(3^2)$ — трансвекция. Так как характеристика $F$
  равна 3, то $(sigma^2)^(3^3) = 1_V$. Ввиду @prop:omeara-unipotent-prime-power
  $sigma^2$ унипотентно. Но
  $
    overline(sigma)^2 in D C(overline(sigma))
    subset.eq D C(overline(sigma)^2),
  $
  и можно применить 1).

  4) Поступаем, как в 3). Предложение доказано.
]
