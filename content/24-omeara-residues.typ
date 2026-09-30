#import "main-defs.typ": *
#import "statements.typ": *

=== Вычеты <sec:omeara-residues>

Для произвольного $sigma$ из $GL_n (V)$ определим _вычетное пространство_ $R$,
_неподвижное пространство_ $P$ и _вычет_ $upright("res") sigma$ следующими
равенствами:
$
  R = (sigma - 1_V) V, quad P = Ker(sigma - 1_V), \
  upright("res") sigma = dim R.
$
Подпространства $R$ и $P$ называются пространствами преобразования $sigma$.
Очевидно,
$
  dim R + dim P = n, \
  sigma R = R, quad sigma P = P, \
  upright("res") sigma = 0 <=> sigma = 1_V.
$
#idx("вычет")
#idx("пространство", "вычетное")
#idx("вычетное пространство")
#idx("пространство", "неподвижное")
#idx("неподвижное пространство")

#source(61)Ясно, что $sigma$ и $sigma^(-1)$ имеют одинаковые $R$, $P$,
$upright("res")$ и
$ P = brace(x in V | sigma x = x). $
Если $R inter P = 0$, то $V = R plus.o P$ и $R$ характеризует отклонение $sigma$
от тождественного преобразования. Однако в дальнейшем нам встретятся примеры,
когда $R inter P != 0$ и даже $R subset.eq P$. Если $R$ — прямая (плоскость,
гиперплоскость), то мы будем называть ее вычетной прямой (плоскостью,
гиперплоскостью) преобразования $sigma$. Аналогичный смысл имеют понятия
неподвижной прямой, плоскости и т. д.

*Соглашение.* Всякий раз, когда рассматривается преобразование $sigma$ из
$GL_n (V)$, буква $R$ будет обозначать вычетное, а $P$ — неподвижное
пространство этого $sigma$. Аналогично $R_i$ и $P_i$ будут ассоциироваться с
$sigma_i$.

#numbered-paragraph[
  Пусть $sigma_1, sigma_2$ — элементы из $GL_n (V)$ и $sigma = sigma_1 sigma_2$.
  Тогда
  $
    R subset.eq R_1 + R_2, quad P supset.eq P_1 inter P_2, \
    upright("res") sigma_1 sigma_2 <= upright("res") sigma_1
    + upright("res") sigma_2.
  $
] <prop:omeara-residue-product>

#numbered-paragraph(italic: false, family: "exm")[
  *Примеры.* Вычетное пространство нетривиального растяжения пространства $V$
  совпадает с самим пространством $V$. Если взять прямую сумму $V = U plus.o W$
  и положить $sigma_1 = (1_U) plus.o (alpha 1_W)$, где $alpha != 0, 1$, то, как
  легко видеть, $R_1 = W$, $P_1 = U$. Полагая
  $sigma_2 = (alpha 1_U) plus.o (1_W)$, получаем пример равенства во всех
  соотношениях @prop:omeara-residue-product. С другой стороны, если $sigma$ —
  произвольный элемент из $GL_n (V)$, отличный от тождественного преобразования,
  то, положив $sigma_1 = sigma$, $sigma_2 = sigma^(-1)$, получим строгие
  неравенства во всех соотношениях @prop:omeara-residue-product.
] <exm:omeara-residue-product>

#numbered-paragraph[
  Пусть $sigma_1, sigma_2$ — элементы из $GL_n (V)$ и $sigma = sigma_1 sigma_2$.
  Тогда
  + $V = P_1 + P_2 => R = R_1 + R_2$,
  + $R_1 inter R_2 = 0 => P = P_1 inter P_2$.
] <prop:omeara-residue-product-equality>

#proof[
  Сначала докажем 1). Имеем
  $
    R_1 = (sigma_1 - 1_V) V = (sigma_1 - 1_V)(P_1 + P_2)
    = (sigma_1 - 1_V) P_2 = \
    = (sigma_1 sigma_2 - 1_V) P_2 subset.eq (sigma - 1_V) V = R.
  $
  Аналогично, рассматривая $sigma^(-1) = sigma_2^(-1) sigma_1^(-1)$, получим
  $R_2 subset.eq R$. Следовательно, $R = R_1 + R_2$ по
  @prop:omeara-residue-product. Теперь докажем 2). Для любого $x$ из $P$ имеем
  $
    sigma_2 x - x = -(sigma_1 (sigma_2 x) - sigma_2 x)
    in R_1 inter R_2 = 0,
  $
  поэтому $P subset.eq P_2$, $P subset.eq P_1$. Но тогда $P = P_1 inter P_2$.
  Предложение доказано.
]

#source(62)
#numbered-paragraph[
  Пусть $sigma$ и $Sigma$ — элементы из $GL_n (V)$. Вычетным и неподвижным
  пространствами преобразования $Sigma sigma Sigma^(-1)$ являются $Sigma R$ и
  $Sigma P$ соответственно. В частности,
  $upright("res") Sigma sigma Sigma^(-1) = upright("res") sigma$ и
  $ (sigma Sigma = Sigma sigma) => (Sigma R = R "и" Sigma P = P). $
] <prop:omeara-residue-conjugacy>

#numbered-paragraph[
  Пусть $sigma_1, sigma_2$ — элементы из $GL_n (V)$. Если $R_1 subset.eq P_2$ и
  $R_2 subset.eq P_1$, то $sigma_1 sigma_2 = sigma_2 sigma_1$.
] <prop:omeara-residue-commutation>

#proof[
  Для произвольного $x$ из $V$ имеем
  $
    sigma_1 sigma_2 (x) = sigma_1 (sigma_2 x - x) + sigma_1 x
    = sigma_2 x - x + sigma_1 x = \
    = (sigma_1 x - x) + sigma_2 x = sigma_2 (sigma_1 x - x)
    + sigma_2 x = sigma_2 sigma_1 x,
  $
  что и требовалось доказать.
]

Взяв подходящие $sigma_1 = sigma_2 = sigma$, легко убедиться, что обратное к
@prop:omeara-residue-commutation утверждение верно не всегда. Однако имеет место
следующее предложение.

#numbered-paragraph[
  Если $sigma_1, sigma_2$ — элементы из $GL_n (V)$ и
  $sigma_1 sigma_2 = sigma_2 sigma_1$, то
  $ R_1 subset.eq P_2 quad "и" quad R_2 subset.eq P_1 $
  при условии, что либо $R_1 inter R_2 = 0$, либо $V = P_1 + P_2$.
] <prop:omeara-residue-commutation-converse>

#proof[
  Пусть сначала $R_1 inter R_2 = 0$. Из @prop:omeara-residue-conjugacy и
  определения пространства $R_1$ следует
  $(sigma_1 - 1_V) R_2 subset.eq R_1 inter R_2 = 0$, откуда $R_2 subset.eq P_1$.
  Аналогично получается соотношение $R_1 subset.eq P_2$. Если же
  $V = P_1 + P_2$, то
  $
    R_1 = (sigma_1 - 1_V) V = (sigma_1 - 1_V)(P_1 + P_2)
    = (sigma_1 - 1_V) P_2 subset.eq P_2.
  $
  Аналогично получается соотношение $R_2 subset.eq P_1$.
]

#numbered-paragraph[
  Пусть $sigma$ — элемент из $GL_n (V)$. Преобразование $sigma^2$ тогда и только
  тогда тривиально, когда $sigma|_R = -1_R$.
] <prop:omeara-involution-residue>

#proof[
  $
    sigma^2 = 1_V <=> sigma^2 x = x quad "для всех" x in V <=> \
    <=> sigma(sigma x - x) = -(sigma x - x) quad "для всех" x in V <=> \
    <=> sigma y = -y quad "для всех" y in R <=> \
    <=> sigma|_R = -1_R.
  $
]

#definition(numbered: false, named: false)[
  Элемент $sigma$, такой, что $sigma^2 = 1_V$, и вообще любой элемент $xi$
  абстрактной группы, удовлетворяющий условию $xi^2 = 1$, называется
  _инволюцией_.
] <def:omira-involution>
#idx("инволюция")

#numbered-paragraph[
  Если $sigma != 1$ — произвольный элемент группы $GL_n (V)$, то
  $det(sigma|_R) = det sigma$.
] <prop:omeara-residue-determinant>

#source(63)
#proof[
  Возьмем базу подпространства $R$ и расширим ее до базы пространства $V$. Из
  вида матрицы преобразования $sigma$ в этой базе сразу получается наше
  утверждение.
]

#numbered-paragraph[
  Если $V = V_1 plus.o V_2$ и $sigma = sigma_1 plus.o sigma_2$, где
  $sigma_1 in GL_(n_1) (V_1)$, $sigma_2 in GL_(n_2) (V_2)$, то
  $ R = R_1 plus.o R_2, quad P = P_1 plus.o P_2. $
] <prop:omeara-residue-direct-sum>
