#import "main-defs.typ": *
#import "statements.typ": *

#heading(level: 2, numbering: none)[Поля] <sec:tits-fields>

#numbered-paragraph(italic: false)[
  Пусть $K$ — поле характеристики $!=2$, не изоморфное $FF_3$, $V$ — векторное
  пространство над $K$ размерности $n >= 7$, $n != 8$, снабженное невырожденной
  квадратичной формой $Q$, $frak(G)$ — ортогональная группа $O(Q)$ и
  $H subset frak(G)(K)$ — подгруппа, являющаяся либо ядром спинорной нормы (в
  $O^+(Q,K)$), либо коммутантом группы $frak(G)(K)$. Тогда
  @bib:tits-OMeara1968Orthogonal _всякий автоморфизм $beta$ группы $H$
  #source(220)
  обладает свойством #[@cond:tits-standard-homomorphism]._ (По поводу других,
  более старых результатов о классических группах и, в частности, об
  ортогональных группах $frak(G)(K)$ см. @bib:tits-Dieudonne1963.)
] <prop:tits-orthogonal-fields>

#numbered-paragraph(italic: false)[
  В этом пункте $K$ и $K'$ — поля, $frak(G)$ (соотв. $frak(G)'$) — абсолютно
  почти простая алгебраическая группа, определенная над $K$ (соотв. $K'$), $G^+$
  — подгруппа из $frak(G)(K)$, порожденная подгруппами вида $frak(A)(K)$, где
  $frak(A) subset frak(G)$ $K$-изоморфна аддитивной группе, и $H$ — подгруппа из
  $frak(G)(K)$, содержащая $G^+$. Предположим, что $frak(G)$ односвязна или
  $frak(G)'$ — присоединенная группа.
] <prop:tits-almost-simple-fields>

#numbered-paragraph(
  base: [@prop:tits-almost-simple-fields],
  suffix: ".1",
  italic: false,
)[
  _Всякий гомоморфизм $beta:H arrow frak(G)'(K')$, такой, что $beta(G^+)$ плотно
  по Зарисскому в $frak(G)'$, обладает свойством
  #[@cond:tits-standard-homomorphism]_ @bib:tits-BorelTits1968,
  @bib:tits-BorelTits1973. Заметим, что из существования $beta$ следует, что $K$
  бесконечно, а группа $frak(G)$ изотропна над $K$ ($G^+ != {1}$); в частности,
  этот результат не дает ни результатов Картана @bib:tits-Cartan1930 и ван дер
  Вардена @bib:tits-VanDerWaerden1933 о компактных группах (см. п.
  @prop:tits-topology-and-structure), ни результатов об ортогональных и
  унитарных группах (см., например, п. @prop:tits-orthogonal-fields), когда
  рассматриваемые квадратичные и эрмитовы формы анизотропны.
] <prop:tits-zariski-dense-homomorphisms>

#numbered-paragraph(
  base: [@prop:tits-almost-simple-fields],
  suffix: ".2",
  italic: false,
)[
  Предположим, что поля $K$ и $K'$ конечны, но не изоморфны $FF_2$ и $FF_3$, а
  гомоморфизм $beta:H arrow frak(G)'(K')$ таков, что $beta(H)$ содержит
  коммутант группы $frak(G)'(K')$. Тогда _$beta$ обладает свойством
  @cond:tits-standard-homomorphism или же $K,K'$ изоморфны соответственно полям
  $FF_4,FF_5$, а $frak(G),frak(G)'$ имеют тип $A_1$ (изоморфны группам $SL_2$
  или $PSL_2$)._ Это непосредственно следует из результатов работ
  @bib:tits-Artin1955 (надлежащим образом дополненных, см., например,
  @bib:tits-Tits1962, 4.5) и @bib:tits-Steinberg1960. Если допустить к
  рассмотрению поля $FF_2$ и $FF_3$, то добавляются еще некоторые хорошо
  известные исключения (см., например, @bib:tits-Artin1955 или
  @bib:tits-Tits1962, таблица 4).
] <prop:tits-finite-fields>

#heading(level: 2, numbering: none)[Дополнение: обобщение основной теоремы
  проективной геометрии] <sec:tits-projective-geometry>

#numbered-paragraph(italic: false)[
  Для $i=1,2$ пусть $K_i$ обозначает поле, $frak(G)_i$ — алгебраическую
  абсолютно простую присоединенную группу, определенную над $K_i$ и имеющую
  $K_i$-ранг $>=2$, $P_i$ — множество параболических $K_i$-подгрупп группы
  $frak(G)_i$, упорядоченное по включению. Тогда (@bib:tits-Tits1974, теорема
  5.8) _для каждого изоморфизма упорядоченных множеств $pi:P_1 arrow P_2$
  существуют изоморфизм $sigma:K_1 arrow K_2$ и изогения
  $phi:attach(frak(G), tl: sigma)_1 arrow frak(G)_2$, индуцирующие $pi$;
  изогения $phi$ является изоморфизмом, за исключением, быть может, случая,
  когда $K$ — совершенное поле характеристики $2$, а $frak(G)_i$ имеет тип
  $B_n,C_n$ или $F_4$, или же когда
  #source(221)
  $K$ — совершенное поле характеристики $3$, а $frak(G)_i$ имеет тип $G_2$._
  Этот результат обобщает также одну хорошо известную теорему Чжоу (см.
  @bib:tits-Dieudonne1963, гл. III, § 4).
] <prop:tits-generalized-projective-geometry>
