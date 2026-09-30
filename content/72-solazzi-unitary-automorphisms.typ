#import "main-defs.typ": *
#import "statements.typ": *

== Применение к теории автоморфизмов <sec:solazzi-unitary-automorphisms>

#numbered-paragraph[
  Допустим, что $Lambda$ — изоморфизм группы $G$ в группу $PU(V)$, отображающий
  всякую проективную трансвекцию из $G$ в проективную трансвекцию с той же самой
  собственной прямой. Тогда $Lambda$ тождествен на $G$.
] <prop:solazzi-unitary-axis-rigidity>

#proof[
  Пусть $L$ — изотропная прямая пространства $V$, $overline(tau)$ —
  нетривиальная проективная трансвекция из $G$ с собственной прямой $L$. Пусть
  $overline(sigma)$ — произвольный элемент группы $G$ и
  $overline(sigma)_1=Lambda overline(sigma)$,
  $overline(tau)_1=Lambda overline(tau)$, $f=sigma tau sigma^(-1)$,
  $g=sigma_1 tau_1 sigma_1^(-1)$. Тогда $Lambda overline(f)$ — проективная
  трансвекция с собственной прямой $sigma L$, а $overline(g)$ — проективная
  трансвекция с собственной прямой $sigma_1 L$. Так как
  $Lambda overline(f)=overline(g)$, то $sigma_1 sigma^(-1)$ оставляет на месте
  все изотропные прямые из $V$, а потому, согласно
  @prop:solazzi-unitary-isotropic-line-rigidity, $sigma=lambda sigma_1$, где
  $lambda in RL(V) inter U(V)$. Значит,
  $overline(sigma)=overline(lambda sigma_1)=Lambda overline(sigma)$ для всех
  $overline(sigma)$ из $G$.
]

#definition(numbered: false)[
  Пусть $g$ — полулинейный изоморфизм пространства $V$ на себя. Будем называть
  $g$ _унитарным полулинейным изоморфизмом_, если существует элемент
  $lambda in F$,
  #source(208)
  такой, что $(g x,g y)=lambda(x, y)^u$ для всех $x,y$ из $V$, где $u$ —
  автоморфизм поля $F$, связанный с $g$.
]
#idx("унитарный полулинейный изоморфизм")
#idx("изоморфизм, унитарный полулинейный")

Данный унитарный полулинейный изоморфизм $g$ пространства $V$ на себя определяет
отображение $Lambda_g:U_n (V) arrow.r U_n (V)$ по правилу
$Lambda_g (sigma)=g sigma g^(-1)$ для всех $sigma in U_n (V)$. Аналогично
определяется отображение $overline(Lambda)_g:PU_n (V) arrow.r PU_n (V)$ по
правилу $overline(Lambda)_g (overline(sigma))=overline(Lambda_g (sigma))$ для
всех $overline(sigma) in PU_n (V)$. Легко видеть, что $Lambda_g$ и
$overline(Lambda)_g$ — автоморфизмы групп $U_n (V)$ и $PU_n (V)$ соответственно.

#numbered-paragraph[
  Пусть $g$ — полулинейный изоморфизм пространства $V$ на себя и $n >= 2$.
  Преобразование $g$ тогда и только тогда является унитарным полулинейным
  изоморфизмом, когда из $(x,y)=0$ следует $(g x,g y)=0$.
] <prop:solazzi-unitary-semilinear-similitude>

Доказательство см. в @bib:solazzi-unitary-Dieudonne1971, стр.~18.

#remark(numbered: false)[
  В оставшейся части
  @sec:solazzi-unitary-automorphisms[§~@sec:solazzi-unitary-automorphisms]
  предполагается, что $chi(F) != 2$.
]

#numbered-paragraph[
  Пусть $Lambda$ — автоморфизм группы $G$, $sigma$ — сдвиг из группы $Delta$ с
  вычетной прямой $L$. Предположим, что $nu(V) >= 3$. Тогда
  $Lambda overline(sigma)$ является проективной трансвекцией или проективной
  квазисимметрией.
] <prop:solazzi-unitary-shearing-preservation>

#proof[
  Можно считать, что $overline(sigma) != overline(1)_V$. Положим
  $overline(Sigma)=Lambda overline(sigma)$. В силу
  @prop:solazzi-unitary-isotropic-line-rigidity существует изотропная прямая
  $F a$ из $V$, такая, что $Sigma F a != F a$. Пусть $tau_(a,lambda)$ —
  нетривиальная трансвекция из $Delta$ с собственной прямой $F a$. Полагая
  $T=tau_(a,lambda)$ и используя @prop:solazzi-unitary-noncommutation, получим,
  что $Sigma$ и $T Sigma^(-1)T^(-1)$ не перестановочны. Принимая во внимание
  размерности, видим, что равенство $[Sigma,T]=alpha T Sigma^(-1)T^(-1)Sigma$,
  $alpha in RL(V)$, невозможно. Положим $Lambda overline(tau)=overline(T)$,
  $h=[Sigma,T]$, $f=[sigma,tau]$. Так как $overline(Sigma)$ и
  $overline(T)overline(Sigma)^(-1)overline(T)^(-1)$ не перестановочны, то
  $sigma$ и $tau sigma^(-1)tau^(-1)$ тоже не перестановочны, откуда
  $L != tau L$, $(L,tau L) != 0$ и $L+tau L$ — вычетное пространство для $f$.
  Преобразование $h$ является произведением двух трансвекций
  $Sigma T Sigma^(-1)$ и $T^(-1)$, которые имеют разные собственные прямые
  $Sigma F a$ и $F a$. Значит, $h$ — плоское вращение с вычетным пространством
  $R=Sigma F a+F a$. Поскольку вектор $a$ изотропен, то плоскость $R$ или
  гиперболична, или вполне вырождена. Покажем, что справедливо первое.

  Из формул $Sigma T Sigma^(-1)=tau_(Sigma a,lambda)$, $T^(-1)=tau_(a,-lambda)$
  следует, что плоскость $R$ инвариантна относительно $Sigma T Sigma^(-1)$ и
  $T^(-1)$. Преобразования $Sigma T Sigma^(-1)$ и $T^(-1)$ индуцируют на $R$
  одновременно либо $1_R$, либо нетривиальные трансвекции с разными собственными
  прямыми (в зависимости от соотношений $(a,Sigma a)=0$ или
  #source(209)
  $(a,Sigma a) != 0$). В каждом случае $h|_R=[Sigma,T]|_R != -1_R$, так как
  $chi(F) != 2$. В силу 1.7 из @bib:solazzi-unitary-OMeara1969 $h^2 != 1_V$ и,
  конечно, $h^2 != gamma dot 1_V$ при $gamma != 1$. Таким образом, $overline(h)$
  не является инволюцией, а поскольку $Lambda overline(f)=overline(h)$, то и $f$
  — не инволюция. Так как $f$ удовлетворяет условию утверждения
  @prop:solazzi-unitary-regular-cdc-inclusion, то
  $E(L+tau L) subset.eq C D C(f)$. Поэтому
  $
    overline(E(L+tau L)) subset.eq overline(C D C(f))
    subset.eq C D overline(C(f))=C D C(overline(f)),
  $
  если иметь в виду, что $overline(C(f))=C(overline(f))$
  (см.~@prop:solazzi-unitary-projective-commutation-lift). Но $overline(sigma)$,
  $overline(tau)overline(sigma)^(-1)overline(tau)^(-1)$ принадлежат
  $overline(E(L+tau L))$ и не перестановочны, поэтому группа
  $C D C(overline(f))$ неабелева, а тогда и группа $C D C(overline(h))$
  неабелева. Если бы плоскость $R$ была вполне вырожденной, то из
  @prop:solazzi-unitary-cdc-abelian-characterization следовала бы абелевость
  группы $C D C(overline(h))$. Значит, $R$ — гиперболическая плоскость.

  Наконец, покажем, что $Lambda overline(sigma)$ — проективный сдвиг. Поскольку
  $overline(sigma) in C D C(overline(f))$, то
  $Lambda overline(sigma) in C D C(Lambda overline(f))=C D C(overline(h))$. В
  силу @prop:solazzi-unitary-cdc-residual-inclusion
  $
    overline(Sigma)=Lambda overline(sigma) in C D C(overline(h))
    subset.eq overline(E(R)),
  $
  и можно считать, что вычетное пространство для $Sigma$ содержится в $R$.
  Допустим, что вычетное пространство для $Sigma$ совпадает с $R$ и $Sigma|_R$ —
  скалярное преобразование. Так как
  $C D C(overline(h)) subset.eq overline(E(R))$, то $overline(Sigma)$
  централизует $C D C(overline(h))$, а это противоречит тому, что
  $overline(sigma) in.not C C D C(overline(f))$. Допустим теперь, что вычетное
  пространство преобразования $Sigma$ совпадает с $R$ и $Sigma|_R$ не скалярно.
  Тогда из доказательства утверждения
  @prop:solazzi-unitary-regular-cdc-inclusion следует, что
  $E(R) subset.eq C D C(Sigma)$, а это противоречит абелевости группы
  $C D C(overline(sigma))$. Таким образом, вычетное пространство для $Sigma$
  является прямой. Предложение доказано.
]

Итак, предложение @prop:solazzi-unitary-shearing-preservation утверждает, что
произвольный автоморфизм $Lambda$ группы $G$ (при сделанных предположениях)
отображает проективные сдвиги в проективные сдвиги. Оставим предположения из
@prop:solazzi-unitary-shearing-preservation в силе до конца
@sec:solazzi-unitary-automorphisms[§~@sec:solazzi-unitary-automorphisms] и
покажем, что в действительности $Lambda$ отображает проективные трансвекции в
проективные трансвекции. Отметим, что если $sigma_1$ и $sigma_2$ —
нетождественные сдвиги с вычетными пространствами $L_1$ и $L_2$, то
$sigma_1 sigma_2=sigma_2 sigma_1$ в том и только том случае, когда $L_1=L_2$ или
$(L_1,L_2)=0$. Поэтому, если $overline(sigma) in G$ — нетривиальный сдвиг с
вычетной прямой $L$, то $C C(overline(sigma))=overline(E(L))$.

#definition(numbered: false)[
  Для подпространства $W$ пространства $V$ обозначим через $S(W)$ множество всех
  проективных сдвигов из $G$, вычетные прямые которых содержатся в $W$. Если
  $X subset.eq G$,
  #source(210)
  то $C'(X)$ обозначает множество всех проективных сдвигов из $G$,
  перестановочных с любым элементом из $X$.
]

#lemma[
  Пусть $overline(sigma)_1$ и $overline(sigma)_2$ — нетривиальные
  перестановочные сдвиги из $G$ с различными вычетными прямыми $L_1$ и $L_2$.
  Тогда
  $ C' C'(overline(sigma)_1,overline(sigma)_2) subset.eq S(L_1+L_2), $
  причем
  $ C' C'(overline(sigma)_1,overline(sigma)_2)=S(L_1+L_2), $
  если $overline(sigma)_1$ и $overline(sigma)_2$ — трансвекции.
] <lem:solazzi-unitary-shearing-double-centralizer>

#proof[
  Очевидно,
  $
    C'(overline(sigma)_1,overline(sigma)_2)
    =S((L_1+L_2)^*) union S(L_1) union S(L_2),
  $
  поэтому $C' C'(overline(sigma)_1,overline(sigma)_2) subset.eq S(L_1+L_2)$.
  Если $sigma_1$, $sigma_2$ — трансвекции, то
  $C'(overline(sigma)_1,overline(sigma)_2)=S((L_1+L_2)^*)$, откуда
  $S(L_1+L_2) subset.eq C' C'(overline(sigma)_1,overline(sigma)_2)$.
]

#lemma[
  Пусть справедливы предположения из
  @prop:solazzi-unitary-shearing-preservation. Если $overline(sigma)_1$ является
  проективной трансвекцией из $G$, то $Lambda overline(sigma)_1$ — тоже
  проективная трансвекция.
] <lem:solazzi-unitary-transvection-preservation>

#proof[
  Если поле $F$ имеет характеристику $p > 0$, то каждая неединичная трансвекция
  имеет порядок $p$, тогда как порядок любой квазисимметрии не равен $p$.
  Значит, можно предполагать, что $chi(F)=0$.

  Будем считать, что $overline(sigma)_1 != overline(1)$. Пусть $L_1$ —
  собственная прямая проективной трансвекции $overline(sigma)_1$. Выберем такую
  изотропную прямую $L_2$ из $V$, что $(L_2,L_1)=0$ и $L_2 != L_1$, а затем
  возьмем в $G$ нетривиальную проективную трансвекцию $overline(sigma)_2$ с
  собственной прямой $L_2$. Пусть $L'_1$ и $L'_2$ — вычетные прямые сдвигов
  $Lambda overline(sigma)_1$ и $Lambda overline(sigma)_2$ соответственно.

  Так как вполне вырожденная плоскость $L_1+L_2$ содержит бесконечное число
  различных попарно ортогональных изотропных прямых, то подпространство
  $S(L_1+L_2)=C' C'(overline(sigma)_1,overline(sigma)_2)$ содержит бесконечно
  много различных попарно перестановочных проективных трансвекций с попарно
  различными двойными централизаторами. Следовательно,
  $C' C'(Lambda overline(sigma)_1,Lambda overline(sigma)_2)$ содержит
  бесконечное число различных проективных сдвигов с аналогичными свойствами.
  Поскольку $C' C'(Lambda overline(sigma)_1,Lambda overline(sigma)_2)
  subset.eq S(L'_1+L'_2)$, то плоскость $L'_1+L'_2$ содержит бесконечно много
  различных попарно ортогональных прямых. Значит, плоскость $L'_1+L'_2$ вполне
  вырождена, а $Lambda overline(sigma)_1$ — проективная трансвекция. Лемма
  доказана.
]

Итак, в предположениях из @prop:solazzi-unitary-shearing-preservation
автоморфизм $Lambda$ группы $G$ переводит проективные трансвекции снова в
проективные трансвекции.

#source(211)
Для изотропной прямой $L$ обозначим через $overline(T)(L)$ группу всех
проективных трансвекций из $G$ с собственной прямой $L$. Согласно
@prop:solazzi-unitary-transvection-product, $overline(T)(L)$ — максимальная
группа проективных трансвекций из $G$ и каждая максимальная группа проективных
трансвекций из $G$ совпадает с группой $overline(T)(L)$ при подходящей
изотропной прямой $L$. Пусть $Lambda$ — автоморфизм группы $G$. В силу леммы
@lem:solazzi-unitary-transvection-preservation $Lambda overline(T)(L)$ —
максимальная группа проективных трансвекций из $G$, а потому существует
единственная изотропная прямая $L'$, такая, что
$Lambda overline(T)(L)=overline(T)(L')$. Легко видеть, что отображение
$L arrow.r.bar L'$ является биекцией на множестве изотропных прямых пространства
$V$. Так как перестановочность двух проективных трансвекций равносильна
ортогональности их собственных прямых, то $(L_1,L_2)=0$ в том и только том
случае, когда $(L'_1,L'_2)=0$ для любых двух изотропных прямых $L_1$ и $L_2$.
Ясно также, что обратная биекция $L' arrow.r.bar L$ индуцируется автоморфизмом
$Lambda^(-1)$ группы $G$.

Пусть теперь $L_1,L_2$ — различные ортогональные изотропные прямые, а
$overline(tau)_1$, $overline(tau)_2$ — нетривиальные проективные трансвекции из
$G$ с собственными прямыми $L_1$ и $L_2$ соответственно. Выше было доказано, что
$C' C'(overline(tau)_1,overline(tau)_2)$ совпадает с множеством всех проективных
трансвекций из $G$, собственные прямые которых принадлежат вполне вырожденной
плоскости $L_1+L_2$. Отсюда и из сохранения автоморфизмом $Lambda$ проективных
трансвекций следует, что если $L_3 subset L_1+L_2$, то $L'_3 subset L'_1+L'_2$ и
$L'_1+L'_2$ — вполне вырожденное подпространство из $V$.

#numbered-paragraph[
  Предположим, что $L_1,L_2,dots,L_r$ — конечное множество попарно ортогональных
  изотропных проективных прямых. Тогда
  $
    L_1 subset.eq L_2+dots+L_r arrow.l.r.double
    L'_1 subset.eq L'_2+dots+L'_r.
  $
] <prop:solazzi-unitary-isotropic-incidence>

#proof[
  Будем доказывать одну импликацию:
  $ L_1 subset.eq L_2+dots+L_r arrow.r.double L'_1 subset.eq L'_2+dots+L'_r $
  (другая получается аналогично, если использовать $Lambda^(-1)$). Выше было
  замечено, что утверждение справедливо при $r=3$; если $r=1$ или 2, то оно
  тривиально. Пусть теперь $r >= 4$, воспользуемся индукцией по $r$. При
  $L_1=L_r$ утверждение очевидно. Предположим, что $L_1 != L_r$, тогда
  $L_1 subset.eq K+L_r$, где $K$ — прямая из $L_2+dots+L_(r-1)$. Прямая $K$
  изотропна и ортогональна прямым $L_2,dots,L_(r-1)$. По индуктивному
  предположению $K' subset.eq L'_2+dots+L'_(r-1)$, а ввиду справедливости
  утверждения при $r=3$ получаем, что $L'_1 subset.eq K'+L'_r$. Значит,
  $L'_1 subset.eq K'+L'_r subset.eq L'_2+dots+L'_r$, что и требовалось доказать.
]

#source(212)
Из предложения @prop:solazzi-unitary-isotropic-incidence следует, что биекция
$L arrow.r.bar L'$ на множестве изотропных прямых, индуцированная автоморфизмом
$Lambda$, отображает любое конечное множество независимых попарно ортогональных
изотропных прямых на такое же множество. Пусть $W$ — некоторое $m$-мерное вполне
вырожденное подпространство пространства $V$. Выберем некоторую базу
$x_1,dots,x_m$ этого подпространства и обозначим через $W'$ $m$-мерное (вполне
вырожденное) подпространство из $V$, порожденное независимыми прямыми
$(F x_1)',dots,(F x_m)'$. Принимая во внимание
@prop:solazzi-unitary-isotropic-incidence, легко убедиться, что $W'$ не зависит
от выбора базы пространства $W$. Следовательно, автоморфизм $Lambda$ индуцирует
отображение $W arrow.r.bar W'$ на множестве вполне вырожденных подпространств из
$V$, причем оно сохраняет размерности и является биекцией. Очевидно, обратное
отображение индуцировано автоморфизмом $Lambda^(-1)$ группы $G$.

Таким образом, биекция $W arrow.r.bar W'$ вполне вырожденных подпространств,
индуцированная автоморфизмом $Lambda$, удовлетворяет предположениям теоремы на
стр.~132 из @bib:solazzi-unitary-Dieudonne1971. Применяя эту теорему, заключаем,
что существует унитарный полулинейный изоморфизм $g$ пространства $V$ на себя,
такой, что $g W=W'$ для всех вполне вырожденных подпространств $W$ размерности
$nu(V)-1$, принадлежащих $V$.

Пусть $L$ — произвольная изотропная прямая из $V$. Выберем максимальное вполне
вырожденное подпространство $W$ из $V$, содержащее $L$. Тогда
$L=inter.big_alpha W_alpha$, где ${W_alpha}$ — семейство всех подпространств из
$W$ размерности $nu(V)-1$, содержащих $L$. Отсюда
$g L=inter.big_alpha g W_alpha=inter.big_alpha W'_alpha=L'$. Значит, $g L=L'$
для всех изотропных прямых $L$ из $V$. Мы видим, что изоморфизм
$overline(Lambda)_g^(-1) compose Lambda$ группы $G$ в $PU_n (V)$ удовлетворяет
предположениям из @prop:solazzi-unitary-axis-rigidity. Значит,
$Lambda=overline(Lambda)_g$, и доказана

#numbered-paragraph(family: "th")[
  *Теорема.* Допустим, что подгруппа $G$ группы $PU_n (V)$ имеет достаточно
  много проективных трансвекций, $nu(V) >= 3$, $chi(F) != 2$. Пусть $Lambda$ —
  автоморфизм группы $G$. Тогда существует такой унитарный полулинейный
  изоморфизм $g$ пространства $V$ на себя, что $Lambda=overline(Lambda)_g|_G$.
] <th:solazzi-unitary-projective-automorphisms>

#numbered-paragraph(
  base: [@th:solazzi-unitary-projective-automorphisms],
  suffix: "а",
  family: "cor",
)[
  *Следствие.* Пусть $nu(V) >= 3$, $chi(F) != 2$ и $S$ — подгруппа группы
  $U_n (V)$, имеющая достаточно много трансвекций. Пусть $Lambda$ — автоморфизм
  группы $S$. Тогда существуют гомоморфизм $chi$ группы $S$ в центр группы
  $U_n (V)$ и унитарный полулинейный изоморфизм $g$ пространства $V$ на себя,
  такие, что $Lambda sigma=chi(sigma) dot g sigma g^(-1)$ для всех $sigma$ из
  $S$.
] <cor:solazzi-unitary-linear-automorphisms>

#proof[
  #source(213)
  Автоморфизм $Lambda$ индуцирует автоморфизм $overline(Lambda)$ группы
  $overline(S)$ по правилу
  $overline(Lambda)(overline(sigma))=overline(Lambda(sigma))$ для всех $sigma$
  из $S$. По теореме @th:solazzi-unitary-projective-automorphisms
  $overline(Lambda)=overline(Lambda)_g$, т.~е.
  $overline(Lambda sigma)=overline(Lambda_g (sigma))$ для всех $sigma$ из $S$.
  Отсюда $Lambda sigma=chi(sigma) dot Lambda_g (sigma)$, где $chi(sigma)$ —
  скалярное преобразование из $U_n (V)$. Так как $Lambda$ — автоморфизм, то
  $chi$ является гомоморфизмом. Следствие доказано.
]
