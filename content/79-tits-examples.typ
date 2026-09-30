#import "main-defs.typ": *
#import "statements.typ": *

#heading(level: 2, numbering: none)[Не полупростые группы:
  примеры] <sec:tits-nonsemisimple>

#numbered-paragraph(italic: false)[
  Все алгебраические группы, рассматриваемые выше, предполагались полупростыми.
  Проиллюстрируем примерами некоторые явления, происходящие при отказе от этого
  предположения. Как и в п. @prop:tits-almost-simple-fields, $frak(G)$ (соотв.
  $frak(G)'$) обозначает алгебраическую группу, определенную над полем $K$
  (соотв. $K'$).
] <prop:tits-nonsemisimple>

#numbered-paragraph(
  base: [@prop:tits-nonsemisimple],
  suffix: ".1",
  italic: false,
)[
  Пусть $K=K'=RR$ и $frak(G)=frak(G)'$ — аддитивная группа. Группа $frak(G)(RR)$
  (являющаяся векторным пространством размерности $2^(aleph_0)$ над $QQ$)
  обладает $2^(2^(aleph_0))$ эндоморфизмами. Из них только эндоморфизмы вида
  $x ↦ a x$, $a in RR$, полуалгебраические.
] <prop:tits-additive-example>

#numbered-paragraph(
  base: [@prop:tits-nonsemisimple],
  suffix: ".2",
  italic: false,
)[
  Пусть $frak(G)$ (соотв. $frak(G)'$) — группа над $K$ (соотв. $K'$), равная
  полупрямому произведению мультипликативной группы на аддитивную группу с
  обычным действием первой на второй (группа аффинных преобразований
  $x ↦ a x+b$). Легко видеть, что всякий инъективный гомоморфизм группы
  $frak(G)(K)$ в $frak(G)'(K')$ полуалгебраичен.
] <prop:tits-affine-example>

#numbered-paragraph(
  base: [@prop:tits-nonsemisimple],
  suffix: ".3",
  italic: false,
)[
  Пусть $K=K'$ и $frak(G)=frak(G)'=GL_n dot M_n$ — полупрямое произведение
  группы $GL_n$ на (алгебраическую) аддитивную группу $M_n$ квадратных матриц
  порядка $n$, на которой $GL_n$ действует сопряжениями. Тогда в обычных
  обозначениях $frak(G)(K)=GL_n (K) dot M_n (K)$. Пусть $d$ — дифференцирование
  поля $K$. Легко проверить, что отображение $beta:frak(G)(K) arrow frak(G)(K)$,
  определяемое формулой
  $ beta(x, y)=(x,x^(-1)d x+y), $
  есть гомоморфизм, который обладает свойством @cond:tits-standard-homomorphism
  только при $d=0$. Заметим, что если $K=RR$ и $d != 0$, то сужение $beta$ на
  подгруппу $GL_n (RR)$ является «разрывным сечением Леви» группы Ли
  $frak(G)(RR)$.
] <prop:tits-derivation-example>
