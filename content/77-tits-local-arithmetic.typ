#import "main-defs.typ": *
#import "statements.typ": *

#heading(level: 2, numbering: none)[Локальные кольца и арифметические
  кольца] <sec:tits-local-arithmetic>

#numbered-paragraph(italic: false)[
  Пусть $R$ — область целостности характеристики $!=2$, $K$ — ее поле частных.
  Предположим, что выполняется одно из следующих условий:

  #symbolic-condition("G")[
    $K$ — глобальное поле (конечное расширение поля $QQ$ или поля $FF_p (t)$),
    $S$ — конечное множество плейсов поля $K$, содержащее все архимедовы плейсы,
    $R$ — пересечение колец нормирования плейсов, не принадлежащих $S$;
  ] <cond:tits-global>
  #symbolic-condition("L")[
    $R$ — локальное кольцо.
  ] <cond:tits-local>

  Пусть $M$ — ограниченный (см. п. @prop:tits-integral-domains) $R$-модуль ранга
  $n >= 7$, $n != 8$, снабженный невырожденной квадратичной формой $Q$,
  #source(219)
  т. е. сужением невырожденной квадратичной формы на векторном пространстве
  $M ⊗ K$. Пусть $frak(G)$ — ортогональная группа $O(M,Q)$#footnote[В случае
    @cond:tits-local $frak(G)$ — не обязательно групповая схема, но во всяком
    случае $R$-функторная группа в смысле @bib:tits-DemazureGabriel1970.] и $H$
  — подгруппа из $frak(G)(R)$, содержащая $-1$ и некоторую конгруэнц-группу
  (группу элементов из $frak(G)(R)$, сравнимых с $1$ по модулю заданного
  ненулевого идеала из $R$). Основной результат работы
  @bib:tits-OMeara1969Orthogonal гласит:

  _при некоторых дополнительных предположениях (заведомо выполняющихся,
  например, в случаях @cond:tits-global и @cond:tits-local, если $K$ — поле
  алгебраических чисел, не являющееся вполне вещественным), то всякий
  автоморфизм $beta$ группы $H$ обладает свойством
  #[@cond:tits-standard-homomorphism]._
] <prop:tits-local-and-global-rings>

#numbered-paragraph(italic: false)[
  В этом пункте излагаются некоторые результаты работы @bib:tits-Borel1968.
  Пусть $K=K'$ — конечное алгебраическое расширение поля $QQ$; $S,R$ имеют то же
  значение, что и в п. @prop:tits-local-and-global-rings @cond:tits-global,
  $R'=R$, $frak(G),frak(G)'$ — связные полупростые групповые $R$-схемы, почти
  простые над $K$, и $r$ обозначает $K$-ранг группы $frak(G)$. В
  @prop:tits-arithmetic-rational и @prop:tits-chevalley-arithmetic
  предполагается, что $frak(G)$ односвязна или $frak(G)'$ — присоединенная
  группа.
] <prop:tits-arithmetic>

#numbered-paragraph(base: [@prop:tits-arithmetic], suffix: ".1", italic: false)[
  Пусть $K=QQ$, $R=ZZ$ и $frak(G)(ZZ) subset H subset frak(G)(QQ)$. Тогда _при
  $r >= 2$ всякий гомоморфизм $beta:H arrow H'=frak(G)'(QQ)$, для которого
  $beta(frak(G)(ZZ))$ плотно по Зарисскому в $frak(G)'$, обладает свойством
  #[@cond:tits-standard-homomorphism]._
] <prop:tits-arithmetic-rational>

#numbered-paragraph(base: [@prop:tits-arithmetic], suffix: ".2", italic: false)[
  Пусть $frak(G)=frak(G)'$ — схема Шевалле. Предположим, что $r >= 2$ или
  $"card" S >= 2$. Тогда _всякий автоморфизм $beta$ группы $H=frak(G)(R)$
  обладает свойством #[@cond:tits-standard-homomorphism]._ (Теорема 4.3 из
  @bib:tits-Borel1968 дает более точное описание этих автоморфизмов.)
] <prop:tits-chevalley-arithmetic>

#numbered-paragraph(base: [@prop:tits-arithmetic], suffix: ".3", italic: false)[
  Пусть $R=ZZ$, $K=QQ$. _Если алгебра Ли группы $frak(G)(RR)$ не имеет фактора,
  изоморфного $frak(s l)(2,RR)$, то группа
  $Aut frak(G)(ZZ) "/" "Int" frak(G)(ZZ)$ конечна._ (См. теорему 1.5 (ii) в
  @bib:tits-Borel1968 — впрочем, несколько более общую.)
] <prop:tits-finite-outer-automorphisms>
