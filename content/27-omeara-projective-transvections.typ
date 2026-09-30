#import "main-defs.typ": *
#import "statements.typ": *

=== Проективные трансвекции <sec:omeara-projective-transvections>

Проективность $k$ пространства $V$ называется _проективной трансвекцией_, если
$k = overline(sigma)$ для некоторой трансвекции $sigma$ из $GL_n (V)$. Ввиду
@prop:omeara-transvection-scalar трансвекция $sigma$, являющаяся представителем
проективной трансвекции $k = overline(sigma)$, единственна, она называется
_представляющей трансвекцией_ проективной трансвекции $k$. Определим вычетное и
неподвижное пространства проективной трансвекции как соответствующие
пространства ее представляющей трансвекции и распространим соглашение параграфа
@sec:omeara-residues на проективные трансвекции — например, если #source(
  69,
)рассматривается проективная трансвекция $sigma$ из $PGL_n (V)$ (или
$overline(sigma)$, где $sigma$ — трансвекция из $GL_n (V)$), то $R$ будет
обозначать ее вычетное, а $P$ — неподвижное пространство. Заметим, что мы не
пытаемся определить вычетное и неподвижное пространства для произвольного
элемента из $PGL_n (V)$. Конечно, если $sigma$ — проективная трансвекция и
$sigma != 1$, то $R$ — прямая, $P$ — гиперплоскость и $R subset.eq P$. С другой
стороны, если даны $L in P^1 (V)$, $H in P^(n-1)(V)$ и $L subset.eq H$, то
всегда существует проективная трансвекция $sigma$ из $PGL_n (V)$, для которой
$R = L$ и $P = H$. Если $sigma$ — проективная трансвекция, а $Sigma$ —
произвольный элемент из $PGL_n (V)$, то $Sigma sigma Sigma^(-1)$ — также
проективная трансвекция и ее пространствами будут $Sigma R$ и $Sigma P$
соответственно. В частности,
$ (Sigma sigma = sigma Sigma) => (Sigma R = R, quad Sigma P = P). $
Заметим, что мы иногда будем записывать элементы из $PGL_n (V)$ в виде
$overline(sigma)$, где $sigma in GL_n (V)$, а иногда — в виде $sigma$, где
$sigma in PGL_n (V)$.
#idx("трансвекция", "проективная")
#idx("проективная", "трансвекция")
#idx("трансвекция", "представляющая")
#idx("представляющая трансвекция")

#numbered-paragraph[
  Предположим, что $n >= 3$. Если $sigma_1, sigma_2$ — нетривиальные проективные
  трансвекции, то $sigma_1 sigma_2$ — проективная трансвекция тогда и только
  тогда, когда $R_1 = R_2$ или $P_1 = P_2$.
] <prop:omeara-projective-transvection-product>

#proof[Применить @prop:omeara-transvection-product.]

#numbered-paragraph(italic: false, family: "exm")[
  *Пример.* Если $n = 2$, характеристика поля $F$ отлична от $2$ и $x_1, x_2$ —
  база пространства $V$, а $rho_1, rho_2$ — сопряженная с ней база пространства
  $V'$, то равенство
  $
    tau_(-2 x_1,rho_2) tau_(2 x_2,rho_1)
    = -tau_(x_1-x_2,2 rho_1+2 rho_2)
  $
  легко следует из § @sec:omeara-transvections. Написав черту над обеими частями
  этого равенства, получим две нетривиальные проективные трансвекции,
  произведение которых является также проективной трансвекцией, хотя их
  пространства не совпадают. Поэтому в
  @prop:omeara-projective-transvection-product необходимо предполагать, что
  $n >= 3$.
] <exm:omeara-projective-transvection-dimension-two>

#numbered-paragraph[
  Пусть $X$ — подгруппа группы $PGL_n (V)$, состоящая только из проективных
  трансвекций. Тогда все нетривиальные элементы из $X$ имеют либо общую вычетную
  прямую, либо общую неподвижную гиперплоскость.
] <prop:omeara-projective-transvection-subgroup>

#proof[
  Если $n >= 3$, то применяем @prop:omeara-projective-transvection-product и
  заканчиваем доказательство, как в @prop:omeara-transvection-subgroup. Пусть
  $n = 2$. Ясно, что $X subset.eq PSL_2$. Пусть $G$ — прообраз $X$ относительно
  гомоморфизма $P|_(SL_2)$. Тогда $G$ — подгруппа в $SL_2$, содержащая ядро
  $plus.minus 1_V$ гомоморфизма $P|_(SL_2)$, и каждый элемент группы $G$ имеет
  вид $plus.minus tau$ для некоторой трансвекции $tau$ из $G$. Достаточно
  #source(70)доказать, что если $tau_L, tau_K$ — трансвекции из $G$ с вычетными
  прямыми $L$ и $K$, то $L = K$. Допустим противное. По определению $G$ имеем
  $tau_L tau_K = plus.minus tau_J$ для некоторой прямой $J$, отличной от $L$ и
  $K$. Если $tau_L tau_K = tau_J$, то $L = K$ в силу
  @prop:omeara-transvection-product. Значит, $tau_L tau_K != tau_J$, т. е.
  характеристика поля $F$ отлична от $2$ и $tau_L tau_K = -tau_J$. Ввиду
  @prop:omeara-transvection-product $tau_J tau_K$ не является трансвекцией,
  поэтому и по определению $G$ имеем $tau_J tau_K = -tau_H$ для некоторой прямой
  $H$. Подставив одно равенство в другое, получим $tau_L tau_K^2 = tau_H$. Но
  $tau_K^2$ — нетривиальная трансвекция с вычетной прямой $K$, так как
  характеристика поля не равна $2$. Ввиду @prop:omeara-transvection-product
  отсюда следует, что $L = K$ — противоречие.
]

#numbered-paragraph[
  Две нетривиальные проективные трансвекции $sigma_1$ и $sigma_2$ из $PGL_n (V)$
  тогда и только тогда перестановочны, когда $R_1 subset.eq P_2$ и
  $R_2 subset.eq P_1$.
] <prop:omeara-projective-transvection-commutation>

#proof[
  Применить предложения @prop:omeara-transvection-commutation и
  @prop:omeara-transvection-scalar.
]

#numbered-paragraph[
  Пусть характеристика поля $F$ отлична от $2$. Если $X$ — множество попарно
  перестановочных инволюций из $GL_n (V)$, то существует такая база пространства
  $V$, в которой
  $
    Sigma ~ diag(plus.minus 1, dots, plus.minus 1)
    quad "для всех" Sigma in X.
  $
  В частности, $upright("card") X <= 2^n$ и $upright("card") P X <= 2^(n-1)$.
] <prop:omeara-commuting-involutions>

#proof[
  Проведем индукцией по $n$. Для $n = 1$ результат очевиден. Пусть $n > 1$.
  Возьмем в $X$ элемент $sigma != plus.minus 1_V$ (если таких нет, то доказывать
  нечего). Ввиду @prop:omeara-involution-residue $sigma|_R = -1_R$, откуда
  $R inter P = 0$, $V = R plus.o P$. Пространства $R$ и $P$ ненулевые, поскольку
  $sigma != plus.minus 1_V$. Так как произвольное $Sigma$ из $X$ перестановочно
  с $sigma$, то $Sigma R = R$ и $Sigma P = P$ по @prop:omeara-residue-conjugacy.
  Остается применить индукцию к попарно перестановочным семействам $Sigma|_R$ и
  $Sigma|_P$, где $Sigma$ пробегает $X$.
]
