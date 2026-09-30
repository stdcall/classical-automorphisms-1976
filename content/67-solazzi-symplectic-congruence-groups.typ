#import "main-defs.typ": *
#import "statements.typ": *

== Автоморфизмы конгруэнц-групп <sec:solazzi-symplectic-congruence-groups>

Пусть в дальнейшем $frak(o)$ обозначает область целостности с полем частных $F$,
$V$ — регулярное $n$-мерное симплектическое пространство над $F$. Назовем
размерностью свободного $frak(o)$-модуля мощность любой базы этого модуля. В
работе @bib:solazzi-symplectic-OMeara1968 определен _ограниченный_
$frak(o)$-модуль $M$ как модуль, для которого существует $frak(o)$-линейный
изоморфизм в свободный $frak(o)$-модуль конечной размерности. #idx(
  "модуль",
  "ограниченный",
) Мы будем обозначать через $M$ ограниченный $frak(o)$-модуль, содержащийся в
$V$ и такой, что $V=F M$, где $F M={alpha x | alpha in F, x in M}$. Определим
коэффициент $frak(c)_x$ вектора $x in V$, полагая
$frak(c)_x={alpha in F | alpha x in M}$; $frak(c)_x$ — дробный идеал кольца
$frak(o)$. _Симплектическая группа_ $Sp_n (M)$ ограниченного модуля $M$ — это по
определению группа ${sigma in Sp(V) | sigma M=M}$.#idx("симплектическая группа")
#idx("группа", "симплектическая")

#source(198)
Допустим, что $frak(a)$ — ненулевой идеал, содержащийся в $frak(o)$. Пусть
$ frak(a) M={sum_("кон.") beta x | beta in frak(a), x in M}. $
_Симплектические конгруэнц-группы_ — это по определению группа
$Sp_n (M;frak(a))={sigma in Sp_n (M) | (sigma-1_V)M subset.eq frak(a)M}$ и
группа $TSp_n (M;frak(a))$, порожденная всеми трансвекциями, лежащими в
$Sp_n (M;frak(a))$.#idx("симплектическая конгруэнц-группа") #idx(
  "конгруэнц-группа",
  "симплектическая",
) Отметим, что $Sp_n (M;frak(o))=Sp_n (M)$, $TSp_n (M;frak(o))=TSp_n (M)$,
$TSp_n (M;frak(a)) subset.eq Sp_n (M;frak(a))$ и все эти подгруппы нормальны в
$Sp_n (M)$. Если $M$ — ненулевой ограниченный $frak(o)$-модуль, а $rho$ —
произвольный ненулевой линейный функционал на $V=F M$, то $rho M$ — дробный
идеал кольца $frak(o)$. Легко видеть, что
$
  lambda(a, M) subset.eq frak(c)_a dot frak(a)
  arrow.r.double lambda(a, M)a subset.eq frak(a)M
  arrow.r.double tau_(a,lambda) in Sp_n (M;frak(a)).
$

#proposition[
  При $n >= 2$ группа $TSp_n (M;frak(a))$ имеет достаточно много трансвекций.
] <prop:solazzi-symplectic-congruence-transvections>

#proof[
  Пусть $L=F a$ — прямая из $V=F M$. Так как $(a,x)$ — ненулевой линейный
  функционал на $V$, то $(a,M)$ — дробный идеал. Выберем ненулевой элемент
  $lambda in F$, удовлетворяющий условию
  $lambda(a, M) subset.eq frak(c)_a dot frak(a)$. Тогда, как и выше,
  $tau_(a,lambda) in TSp_n (M;frak(a))$. Предложение доказано.
]

Пусть $macron$ обозначает естественное отображение $Sp_n (V)$ на
$Sp_n (V) slash plus.minus 1_V$. Определим $PSp_n (M;frak(a))$ как
$overline(Sp_n (M;frak(a)))$, а $PTSp_n (M;frak(a))$ как
$overline(TSp_n (M;frak(a)))$. Назовем эти группы _проективными симплектическими
конгруэнц-группами_.
#idx("проективная симплектическая конгруэнц-группа")
#idx("конгруэнц-группа", "проективная симплектическая")

#proposition[
  Пусть $n >= 6$, $G$ — одна из групп $PSp_n (M;frak(a))$, $PTSp_n (M;frak(a))$,
  а $Lambda$ — автоморфизм $G$. Тогда существует полулинейный изоморфизм $g$
  пространства $V$ на себя, сохраняющий ортогональность и такой, что
  $Lambda=overline(Lambda)_g$.
] <prop:solazzi-symplectic-projective-congruence-automorphisms>

#proof[
  Если $chi(F) != 2$, то достаточно применить
  @th:solazzi-symplectic-projective-automorphisms и
  @prop:solazzi-symplectic-congruence-transvections. Если $chi(F)=2$, то к таким
  группам без изменений применимы рассуждения из
  @bib:solazzi-symplectic-OMeara1968, стр.~125–131, показывающие, что при
  подходящем $g$ автоморфизм $overline(Lambda)_g^(-1) compose Lambda$ сохраняет
  все трансвекции. Используя рассуждения из доказательства
  @th:solazzi-symplectic-projective-automorphisms, получим
  $Lambda=overline(Lambda)_g$, что и требовалось доказать.
]

Теперь пусть $n >= 6$, $S$ — одна из групп $Sp_n (M;frak(a))$,
$TSp_n (M;frak(a))$, а $Lambda$ — автоморфизм $S$. Как и в доказательстве
@cor:solazzi-symplectic-linear-automorphisms, $Lambda$ индуцирует автоморфизм
$overline(Lambda)$ группы $overline(S)$ и в силу
@prop:solazzi-symplectic-projective-congruence-automorphisms
$overline(Lambda)=overline(Lambda)_g$ для некоторого полулинейного изоморфизма
$g$
#source(199)
пространства $V$ на себя, сохраняющего ортогональность. Тогда, как и в
доказательстве @cor:solazzi-symplectic-linear-automorphisms,
$Lambda sigma=chi_1(sigma) dot Lambda_g (sigma)$ для всех $sigma$ из $S$, где
$chi_1$ — некоторый гомоморфизм $S$ в $plus.minus 1_V$. Если $-1_V in S$, то из
@prop:solazzi-symplectic-homothety-decomposition следует, что найдется гомотетия
$P_chi$ группы $S$, такая, что $Lambda=P_chi compose Lambda_g$. Таким образом,
справедлива

#theorem[
  Пусть $n >= 6$, $S$ — одна из симплектических конгруэнц-групп
  $Sp_n (M;frak(a))$, $TSp_n (M;frak(a))$, а $Lambda$ — автоморфизм группы $S$.
  Тогда существуют гомоморфизм $chi_1$ группы $S$ в $plus.minus 1_V$ и
  сохраняющий ортогональность полулинейный изоморфизм $g$ пространства $V$ на
  себя, такие, что $Lambda sigma=chi_1(sigma)Lambda_g (sigma)$ для всех
  $sigma in S$. Если $-1_V in S$, то найдется гомотетия $P_chi$ группы $S$,
  удовлетворяющая условию $Lambda=P_chi compose Lambda_g$.
] <th:solazzi-symplectic-congruence-automorphisms>
