#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/omeara-transvections.typ": (
  transvection-action, transvection-dilatation,
)

=== Трансвекции <sec:omeara-transvections>

Элемент $sigma$ из $GL_n (V)$ называется _трансвекцией_, если $sigma = 1_V$ или
$ upright("res") sigma = 1, quad det sigma = 1; $
$sigma$ называется _дилатацией_, если
$ upright("res") sigma = 1, quad det sigma != 1. $
Если $sigma$ — трансвекция (дилатация), а $Sigma$ — любой элемент из $GL_n (V)$,
то $Sigma sigma Sigma^(-1)$ — тоже трансвекция (дилатация) ввиду
@prop:omeara-residue-conjugacy.
#idx("трансвекция")
#idx("дилатация")

#numbered-paragraph[
  Пусть $n >= 2$ и $sigma$ — элемент из $GL_n (V)$, для которого
  $upright("res") sigma = 1$.
  + $R subset.eq P$ тогда и только тогда, когда $sigma$ — трансвекция.
  + $V = R plus.o P$ тогда и только тогда, когда $sigma$ — дилатация.
  + Если $sigma$ — трансвекция, то множество ее собственных векторов совпадает с
    $dot(P)$, а все собственные значения равны $1$.
  + Если $sigma$ — дилатация, то множество ее собственных векторов совпадает с
    $dot(R) union dot(P)$, а $1$ и $det sigma$ являются ее собственными
    значениями.
] <prop:omeara-transvection-eigenvectors>

#proof[
  Для доказательства 1) достаточно применить @prop:omeara-residue-determinant.
  Далее, 2) следует из 1). Для нахождения собственных значений в 3) возьмем базу
  подпространства $P$, расширим ее до базы пространства $V$ и рассмотрим матрицу
  трансвекции $sigma$ в этой базе. Ясно, что множество собственных векторов
  трансвекции $sigma$ совпадает с $dot(P)$. Для доказательства 4) нужно взять
  базу пространства $V$, составленную из баз подпространств $P$ и $R$.
  Предложение доказано.
]

Таким образом, трансвекции и дилатации можно изобразить так:
#align(center, transvection-dilatation())

#source(64)Если $n = 1$, то $1_V$ является единственной трансвекцией, а если
$F = bb(F)_2$, то дилатаций не существует.

Для произвольных $a in V$, $rho in V'$ определим линейное отображение
$tau_(a,rho)$ пространства $V$ в себя равенством
$ tau_(a,rho) x = x + rho(x) a, quad x in V. $
Очевидно, $(tau_(a,rho) - 1_V) V subset.eq F a$, поэтому отображение
$tau_(a,rho)$, если оно обратимо, является трансвекцией или дилатацией. Заметим,
что
$ tau_(a,rho) = 1_V <=> a = 0 quad "или" quad rho = 0 $
и
$ tau_(lambda a,rho) = tau_(a,lambda rho) quad "для всех" lambda in dot(F). $

#numbered-paragraph[
  Пусть $a, a'$ — ненулевые векторы, $rho, rho'$ — ненулевые функционалы, так
  что $tau_(a,rho)$ и $tau_(a',rho')$ отличны от $1_V$. Тогда
  + $tau_(a,rho) = tau_(a',rho')$ в том и только том случае, когда существует
    такое $lambda in dot(F)$, что $a' = lambda a$ и $rho' = lambda^(-1) rho$,
  + $tau_(a,rho) = tau_(a',rho)$ равносильно $a = a'$,
  + $tau_(a,rho) = tau_(a,rho')$ равносильно $rho = rho'$.
] <prop:omeara-transvection-parameters>

#proof[Все утверждения прямо следуют из определений.]

#numbered-paragraph[
  $det tau_(a,rho) = 1 + rho a$.
] <prop:omeara-transvection-determinant>

#proof[
  Возьмем $n - 1$ линейно независимых векторов $x_1, dots, x_(n-1)$, для которых
  $rho x_1 = dots = rho x_(n-1) = 0$, и положим $H = F x_1 + dots + F x_(n-1)$.
  Если $a in H$, то, взяв $x_n in V - H$, видим, что $tau_(a,rho) x_n - x_n$
  лежит в $H$. Из вида матрицы преобразования $tau_(a,rho)$ в базе
  $x_1, dots, x_n$ получаем требуемое. Если $a in.not H$, то берем $x_n = a$ и
  рассуждаем точно так же. Предложение доказано.
]

Итак, $tau_(a,rho)$ тогда и только тогда лежит в $GL_n (V)$, когда
$rho a != -1$; $tau_(a,rho)$ — трансвекция (дилатация), если и только если
$rho a = 0$ (соответственно $rho a != 0, -1$). Если $sigma$ — неединичный
элемент из $GL_n (V)$ и $sigma = tau_(a,rho)$, то $R = F a$, $P = rho^(-1)(0)$.
В общем случае
$
  tau_(a,rho) tau_(b,phi) x = brace(x + (rho x) a + (phi x) b)
  + (phi x)(rho b) a.
$
Если $tau_(a,rho)$ и $tau_(b,rho)$ — трансвекции, то
$ tau_(a,rho) tau_(b,rho) = tau_(a+b,rho); $
если $tau_(a,rho)$ и $tau_(a,phi)$ — трансвекции, то
$ tau_(a,rho) tau_(a,phi) = tau_(a,rho+phi). $

#source(65)
В частности, если $tau_(a,rho)$ — трансвекция, $m$ — положительное целое число,
то
$ tau_(a,rho)^m = tau_(m a,rho). $
Для произвольного $sigma$ из $GL_n (V)$
$ sigma tau_(a,rho) sigma^(-1) = tau_(sigma a,rho sigma^(-1)). $

#numbered-paragraph[
  Допустим, что $n >= 2$. Пусть $L$ — прямая, а $H$ — гиперплоскость
  пространства $V$. Если $L subset.eq H$, то существует трансвекция $sigma$ из
  $GL_n (V)$, для которой $R = L$, $P = H$. Если $L subset.eq.not H$ и
  $F != bb(F)_2$, то существует дилатация из $GL_n (V)$, для которой $R = L$,
  $P = H$.
] <prop:omeara-transvection-spaces-existence>

#proof[Взять подходящее $tau_(a,rho)$.]

#numbered-paragraph[
  Пусть $sigma$ — элемент из $GL_n (V)$ и $upright("res") sigma = 1$. Тогда $R$
  — прямая, а $P$ — гиперплоскость.

  Если $rho$ — ненулевой функционал из $P^0$, то существует такой вектор $a$ из
  $R$, что $sigma = tau_(a,rho)$.

  Если $b$ — ненулевой вектор из $R$, то существует такой функционал $phi$ из
  $P^0$, что $sigma = tau_(b,phi)$.
] <prop:omeara-transvection-representation>

#proof[
  Пусть сначала задан функционал $rho$. Зафиксируем $z in V - P$, для которого
  $rho z = 1$. Положим $a = sigma z - z in R$. Ясно, что $tau_(a,rho)$ и $sigma$
  совпадают на $P$. Но они совпадают и на $z$, так как
  $ tau_(a,rho) z = z + (rho z) a = z + a = sigma z. $
  Следовательно, $sigma = tau_(a,rho)$. Для доказательства второй части положим
  $a = lambda b$, тогда $sigma = tau_(b,lambda rho)$.
]

#numbered-paragraph[
  Пусть $tau_1, tau_2$ — трансвекции из $GL_n (V)$ и $alpha$ — скаляр. Равенство
  $alpha tau_1 = tau_2$ имеет место тогда и только тогда, когда $alpha = 1$ и
  $tau_1 = tau_2$. В частности, $alpha tau_1$ не является трансвекцией, если
  $alpha != 1$.
] <prop:omeara-transvection-scalar>

#proof[
  Надо воспользоваться тем, что все собственные значения трансвекции равны $1$.
]

#numbered-paragraph[
  Пусть $sigma_1, sigma_2$ — элементы из $GL_n (V)$, имеющие вычет $1$, и
  $sigma_1 sigma_2 != 1_V$. Равенство $upright("res") sigma_1 sigma_2 = 1$
  выполняется тогда и только тогда, когда $R_1 = R_2$ или $P_1 = P_2$.
] <prop:omeara-transvection-product-residue>

#proof[
  Положим $sigma = sigma_1 sigma_2$. Если $R_1 = R_2$, то из включения
  $R subset.eq R_1 + R_2$ следует, что $R$ — прямая, поэтому
  $upright("res") sigma = 1$. Если $P_1 = P_2$, то из включения
  $P supset.eq P_1 inter P_2$ следует, что $P$ — гиперплоскость, поэтому
  $upright("res") sigma = 1$. Обратно, пусть
  $upright("res") sigma_1 sigma_2 = 1$. Если $P_1 = P_2$, то доказывать нечего,
  поэтому предположим, что $V = P_1 + P_2$. Тогда $R = R_1 + R_2$ по #source(
    66,
  )@prop:omeara-residue-product-equality. Но $R$ — прямая, следовательно,
  $R_1 = R_2$. Предложение доказано.
]

#numbered-paragraph[
  Если $sigma_1$ и $sigma_2$ — нетривиальные трансвекции из $GL_n (V)$, то
  $sigma_1 sigma_2$ тогда и только тогда является трансвекцией, когда
  $R_1 = R_2$ или $P_1 = P_2$.
] <prop:omeara-transvection-product>

#proof[Применить @prop:omeara-transvection-product-residue.]

#numbered-paragraph[
  Пусть $X$ — подгруппа группы $GL_n (V)$, состоящая только из трансвекций.
  Тогда все нетривиальные элементы из $X$ либо имеют одинаковые вычетные прямые,
  либо одинаковые неподвижные гиперплоскости.
] <prop:omeara-transvection-subgroup>

#proof[
  Предположим, что существуют две нетривиальные трансвекции $sigma_1, sigma_2$
  из $X$, для которых $R_1 != R_2$, иначе доказывать нечего. Тогда $P_1 = P_2$
  по @prop:omeara-transvection-product. Мы должны убедиться, что для
  произвольной нетривиальной трансвекции $sigma$ из $X$ имеет место равенство
  $P = P_1 = P_2$. Но если $P != P_1$, то только что использованное рассуждение
  дает $R = R_1$ и $R = R_2$. Отсюда $R_1 = R_2$, противоречие.
]

#numbered-paragraph[
  Нетривиальные трансвекции $sigma_1$ и $sigma_2$ тогда и только тогда
  перестановочны, когда
  $ R_1 subset.eq P_2 quad "и" quad R_2 subset.eq P_1. $
] <prop:omeara-transvection-commutation>

#proof[
  Если имеют место включения, то $sigma_1 sigma_2 = sigma_2 sigma_1$ по
  @prop:omeara-residue-commutation. Обратно, пусть
  $sigma_1 sigma_2 = sigma_2 sigma_1$. Имеем $R_1 subset.eq P_1$ и
  $R_2 subset.eq P_2$, так как $sigma_1$ и $sigma_2$ — трансвекции. Если
  $R_1 inter R_2 = 0$, то достаточно сослаться на
  @prop:omeara-residue-commutation-converse. Пусть $R_1 inter R_2 != 0$. Тогда
  $R_1 = R_2$, так как $R_1, R_2$ — прямые. Следовательно,
  $R_1 = R_2 subset.eq P_1$ и $R_2 = R_1 subset.eq P_2$. Предложение доказано.
]

#numbered-paragraph[
  Пусть $x, y$ — линейно независимые векторы пространства $V$, а $H$ —
  гиперплоскость в $V$, содержащая разность $y - x$, но не содержащая $x$.
  Существует такая трансвекция $sigma$, для которой $P = H$, $R = F(y - x)$ и
  $sigma x = y$.
] <prop:omeara-transvection-vector-action>

#align(center, transvection-action())
#proof[
  Ясно, что здесь $n > 1$. Возьмем #source(67)функционал $rho in V'$, для
  которого $rho H = 0$ и $rho x = 1$. Тогда $rho(y - x) = 0$, так как
  $y - x in H$. Поэтому $sigma = tau_(y-x,rho)$ — трансвекция, для которой
  $R = F(y - x)$, $P = H$. Наконец,
  $sigma x = tau_(y-x,rho) x = x + (rho x) (y - x) = y$.
]

#numbered-paragraph[
  Пусть $H, H'$ — различные гиперплоскости в $V$, а $L$ — прямая в $V$, не
  лежащая ни в $H$, ни в $H'$. Тогда существует трансвекция $tau$ с вычетной
  прямой $L$, такая, что $tau H = H'$.
] <prop:omeara-transvection-hyperplane-action>

#proof[
  Положим $L = F a$. Пусть $x_1, dots, x_(n-1)$ — база пространства $H$. Так как
  $V = H' plus.o L$, то каждое $x_i$ имеет вид $x_i = X_i + lambda_i a$, где
  $X_i in H'$, $lambda_i in F$. Поскольку $x_1, dots, x_(n-1), a$ — база
  пространства $V$, то найдется такой линейный функционал $rho$, что
  $ rho x_i = -lambda_i, quad rho a = 0, quad 1 <= i <= n - 1. $
  Тогда $tau_(a,rho)$ — нетривиальная трансвекция, ибо $a != 0$, $rho != 0$ и
  $rho a = 0$; ее вычетной прямой является $F a = L$. Но
  $ tau_(a,rho) x_i = x_i + (rho x_i) a = x_i - lambda_i a = X_i, $
  поэтому $tau_(a,rho) H subset.eq H'$ и, следовательно, $tau_(a,rho) H = H'$.
]
