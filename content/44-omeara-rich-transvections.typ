
#import "diagrams/omeara-rich-transvections.typ": *
#import "main-defs.typ": *
#import "statements.typ": *

=== Группы, богатые трансвекциями <sec:omeara-rich-transvections>

Будем говорить, что подгруппа $G$ из $XiL_n (V)$ _богата трансвекциями_, #idx(
  "подгруппа, богатая трансвекциями",
)если $n >= 2$ и для любой гиперплоскости $H subset.eq V$ и любой прямой
$L subset.eq H$ в группе $G$ найдется по крайней мере одна трансвекция, для
которой $R = L$, $P = H$.

Аналогично, подгруппа $Delta$ из $PXiL_n (V)$ называется _богатой проективными
трансвекциями_, #idx("подгруппа, богатая проективными трансвекциями")если
$n >= 2$ и для любой гиперплоскости $H subset.eq V$ и любой прямой
$L subset.eq H$ в группе $Delta$ найдется по крайней мере одна проективная
трансвекция, для которой $R = L$, $P = H$.

#example[
  При $n >= 2$ группа $SL_n (V)$ богата трансвекциями, а группа $PSL_n (V)$
  богата проективными трансвекциями. Разумеется, этими группами примеры не
  исчерпываются. Позже мы увидим, например, что $SL_n (V)$ и $PSL_n (V)$
  содержат бесконечно много таких подгрупп в случае, когда $F$ — поле
  рациональных чисел $QQ$.
] <exm:omeara-rich-special-linear>

_С этого момента $G$ будет обозначать подгруппу из $XiL_n (V)$, богатую
трансвекциями, а $Delta$ — подгруппу из $PXiL_n (V)$, богатую проективными
трансвекциями. Через $G_1$ и $Delta_1$ обозначаются аналогичные группы,
связанные с пространством $V_1$ размерности $n_1$ над полем $F_1$. Наконец,
пусть $Lambda$ — изоморфизм групп_
$ Lambda: Delta arrow.r.double Delta_1. $
Будем говорить, что $Lambda$ _сохраняет проективную трансвекцию_ $sigma$ из
$Delta$, если $Lambda sigma$ — проективная трансвекция, и что $Lambda$ #source(
  108,
)сохраняет проективную трансвекцию $sigma_1 in Delta_1$, если
$Lambda^(-1) sigma_1$ — проективная трансвекция. Изоморфизм $Lambda$ называется
_сохраняющим проективные трансвекции_, если он сохраняет все проективные
трансвекции из $Delta$ и $Delta_1$.

#numbered-paragraph[
  Группы $breve(G)$ и $breve(Delta)$ также богаты.
] <prop:omeara-dual-rich-groups>
#proof[
  См. §~@sec:omeara-contragredient, особенно утверждение
  @prop:omeara-contragredient.
]

#numbered-paragraph[
  Если $n >= 3$, то группы $D G$ и $D Delta$ также богаты.
] <prop:omeara-rich-derived-groups>
#proof[
  Начнем с $G$. Для данной гиперплоскости $H$ и данной прямой $L subset.eq H$ мы
  должны найти трансвекцию $sigma in D G$, такую, что $R = L$ и $P = H$. Выберем
  базу $x_1, dots, x_n$ пространства $V$ так, чтобы было $F x_1 = L$ и
  $F x_1 + dots + F x_(n-1) = H$. Пусть $rho_1, dots, rho_n$ — сопряженная база.
  Так как группа $G$ богата, то существуют $alpha$, $beta in dot(F)$, такие, что
  $ tau_(x_1, alpha rho_2) in G, quad tau_(x_2, beta rho_n) in G. $
  Тогда трансвекция
  $
    sigma = tau_(x_1, alpha beta rho_n)
    = [tau_(x_1, alpha rho_2), tau_(x_2, beta rho_n)] in D G
  $
  является искомой. Теперь разберемся с $Delta$. Так как $Delta$ богата
  проективными трансвекциями, то $P^(-1) Delta$ богата трансвекциями,
  следовательно, $D P^(-1) Delta$ также богата трансвекциями, и, значит,
  $D Delta = P(D P^(-1) Delta)$ богата проективными трансвекциями, что и
  требовалось доказать.
]

#numbered-paragraph[
  Пусть $R_0$, $P_0$ — произвольные подпространства пространства $V$,
  удовлетворяющие условию $dim R_0 + dim P_0 = n$. Если $R_0$ — прямая, то
  предположим дополнительно, что $R_0 subset.eq P_0$. Тогда существует
  преобразование $sigma$, являющееся произведением $dim R_0$ трансвекций из $G$
  и такое, что $R = R_0$, $P = P_0$.
] <prop:omeara-prescribed-transvection-product>
#proof[
  Если $R_0 = 0$ или $R_0$ — прямая, то утверждение очевидно. Пусть теперь $R_0$
  — плоскость. Выберем прямые $L_1$, $L_2$ и гиперплоскости $H_1$, $H_2$ так,
  чтобы было
  $
    L_1 subset.eq H_1, quad L_2 subset.eq H_2, \
    R_0 = L_1 + L_2, quad P_0 = H_1 inter H_2.
  $
  Для того чтобы убедиться в возможности такого выбора, рассмотрим отдельно
  случаи, когда пересечение $R_0 inter P_0$ является точкой, прямой и
  плоскостью. Так как $G$ богата трансвекциями, то можно найти в ней трансвекции
  $sigma_1$ и $sigma_2$, #source(109)для которых $R_1 = L_1$, $P_1 = H_1$,
  $R_2 = L_2$, $P_2 = H_2$. Положим $sigma = sigma_1 sigma_2$ и применим
  @prop:omeara-residue-product-equality.

  Теперь проводим индукцию по $dim R_0$. По предыдущему можно считать, что
  $dim R_0 >= 3$ и, значит, $dim P_0 <= n - 3$. Пусть $P_1$ — гиперплоскость,
  содержащая подпространство $P_0$, а $P_2$ — подпространство из $V$,
  удовлетворяющее условиям $dim P_2 = dim P_0 + 1$, $P_2 inter P_1 = P_0$. В
  частности, $V = P_1 + P_2$.

  #align(center, rich-transvection-product())

  Пусть $R_1$ — произвольная прямая в $P_1 inter R_0$. Выберем $R_2$ так, чтобы
  было $R_0 = R_1 ⊕ R_2$. Ввиду того что группа $G$ богата, найдется трансвекция
  $sigma_1 in G$ с вычетным пространством $R_1$ и неподвижным пространством
  $P_1$. По индукции существует преобразование $sigma_2$, являющееся
  произведением $dim R_2$ трансвекций из $G$, причем связанные с $sigma_2$
  пространства есть $R_2$ и $P_2$. Положим теперь $sigma = sigma_1 sigma_2$ и
  применим @prop:omeara-residue-product-equality.
]

#numbered-paragraph[
  При $n >= 2$ группа $D G$ содержит $sigma$ с $R = V$.
] <prop:omeara-derived-full-residue>
#proof[
  При $n >= 3$ использовать @prop:omeara-rich-derived-groups и
  @prop:omeara-prescribed-transvection-product. Если $n = 2$, то применить
  @prop:omeara-transvection-commutators.
]

#numbered-paragraph[
  Предположим, что $n >= 2$. Тогда
  + централизатор группы $G$ в $XiL_n (V)$ содержится в $RL_n$, в частности,
    $
      G inter upright("cen") XiL_n subset.eq upright("cen") G
      subset.eq upright("cen") GL_n;
    $
  + централизатор группы $Delta$ в $PXiL_n$ тривиален, в частности, центр группы
    $Delta$ тривиален.
] <prop:omeara-rich-projective-centralizer>

#numbered-paragraph[
  #source(110)Предположим, что $n >= 2$, $G subset.eq GL_n$. Тогда
  $C_V (G) = RL_n$ и $upright("cen") G = G inter RL_n$.
] <prop:omeara-rich-linear-centralizer>

#numbered-paragraph[
  Пусть $n >= 3$ и $F != FF_2$. Тогда для любой гиперплоскости $H subset.eq V$ и
  любой прямой $L subset.eq H$ в группе $G$ найдутся по крайней мере две
  различные трансвекции, а в группе $Delta$ — по крайней мере две различные
  проективные трансвекции с вычетной прямой $L$ и неподвижной гиперплоскостью
  $H$.
] <prop:omeara-two-transvections>
#proof[
  Пусть функционал $rho in V'$ задает $H$. Выберем в $H$ два линейно независимых
  вектора $a$ и $b$ так, чтобы было $L = F a$ и
  $ tau_(a,rho), quad tau_(b,rho), quad tau_(a+b,rho) in G. $
  Так как $F != FF_2$, то в плоскости $F a + F b$ существует прямая
  $F(lambda a + mu b)$, отличная от $F a$, $F b$ и $F(a+b)$ и такая, что
  $tau_(lambda a + mu b,rho) in G$. Если $mu = 1$, то $lambda != 0, 1$, поэтому
  $
    tau_((1-lambda)a,rho) = tau_(a,rho)
    tau_(lambda a + mu b,rho)^(-1) tau_(b,rho) in G,
  $
  и все доказано. Пусть теперь $mu != 1$. Пусть $sigma$ — трансвекция в $G$ с
  вычетной прямой $L$, неподвижная гиперплоскость которой содержит $L$, но не
  $b$. Тогда $sigma b = b + nu a$ для некоторого $nu in dot(F)$. Для любого
  $x in V$
  $ rho(sigma x - x) in rho L subset.eq rho H = 0, $
  поэтому $rho sigma = rho$, откуда $rho sigma^(-1) = rho$. Имеем
  $
    tau_(nu a,rho) = tau_(sigma b - b,rho)
    = sigma tau_(b,rho) sigma^(-1) tau_(b,rho)^(-1) in G.
  $
  Аналогично
  $
    tau_(mu nu a,rho) = tau_(mu(sigma b-b),rho)
    = tau_(sigma(lambda a + mu b),rho) tau_(lambda a + mu b,rho)^(-1) \
    = sigma tau_(lambda a + mu b,rho) sigma^(-1)
    tau_(lambda a + mu b,rho)^(-1) in G.
  $
  Но $mu != 1$, поэтому $tau_(nu a,rho)$ и $tau_(mu nu a,rho)$ — различные
  трансвекции из $G$ с пространствами $L subset.eq H$.

  В проективном случае применяем только что полученный результат к
  $P^(-1) Delta$.
]

#numbered-paragraph[
  Пусть $G subset.eq GL_n$. Тогда
  + $C_V (D G) = RL_n$, если $n >= 3$,
  + $C_V (D G) = RL_n$, если $n >= 2$ и $G$ содержит по крайней мере две
    различные трансвекции с одной и той же вычетной прямой,
  + $1_V$ — единственное унипотентное преобразование, содержащееся в
    $C_V (D G)$.
] <prop:omeara-derived-centralizer>
#proof[
  1) Если $n >= 3$, то применяем @prop:omeara-rich-derived-groups и
  @prop:omeara-rich-linear-centralizer.

  #source(111)2) Группа $D G$ не абелева в силу
  @prop:omeara-transvection-commutators. Для произвольного $sigma in C_V (D G)$
  имеем
  $ C_V (sigma) supset.eq C_V (C_V (D G)) = C_V C_V (D G) supset.eq D G, $
  так что и $C_V (sigma)$ не абелева. Поэтому $D C_V (sigma) != 1_V$, откуда
  ввиду @prop:omeara-two-dimensional-centralizer $sigma in RL_2$. Следовательно,
  $C_V (D G) = RL_2$.

  3) Утверждение очевидно, если $C_V (D G) = RL_n$, поэтому необходимо
  рассмотреть только случай $n = 2$. Тогда произвольный унипотентный элемент
  $sigma in C_V (D G)$ является трансвекцией. Пусть $L$ — соответствующая
  вычетная прямая. Зафиксируем прямую $K$, отличную от $L$, и выберем в $G$
  трансвекции $tau_L$, $tau_K$ с вычетными прямыми $L$ и $K$. Тогда $sigma$
  перестановочно с $tau_L tau_K tau_L^(-1) tau_K^(-1)$ и, очевидно, с $tau_L$, а
  поэтому и с трансвекцией $tau_K tau_L^(-1) tau_K^(-1)$, для которой вычетной
  прямой является $tau_K L$. Следовательно, каждая из прямых $L$ и $tau_K L$
  инвариантна относительно $sigma$. Они различны, так как $L != K$. Но $sigma$
  унипотентно, поэтому $sigma = 1$.
]
