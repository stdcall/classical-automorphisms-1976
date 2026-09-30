#import "main-defs.typ": *
#import "statements.typ": *

== Применение к теории автоморфизмов <sec:solazzi-symplectic-automorphisms>

Начнем с определения двух специальных типов автоморфизмов группы $Sp(V)$. Вскоре
мы убедимся, что каждый автоморфизм группы $Sp(V)$ будет произведением
автоморфизмов этих типов.

#definition(numbered: false)[
  Пусть $S$ — подгруппа группы $Sp(V)$, имеющая достаточно много трансвекций.
  Назовем автоморфизм $P_chi$ группы $S$ _гомотетией_, если
  $P_chi (sigma)=chi(sigma) dot sigma$ для всех $sigma in S$, где $chi$ —
  гомоморфизм группы $S$ в группу $plus.minus 1_V$.
]
#idx("гомотетия")

Легко доказать следующий результат.

#proposition[
  #source(195)
  Пусть $S$ — подгруппа группы $Sp(V)$, имеющая достаточно много трансвекций.
  Предположим, что $-1_V in S$ и $chi$ — гомоморфизм $S$ в $plus.minus 1_V$.
  Отображение $sigma arrow.r.bar chi(sigma) dot sigma$, $sigma in S$, является
  автоморфизмом группы $S$ тогда и только тогда, когда
  $chi(plus.minus 1_V)=1_V$.
] <prop:solazzi-symplectic-homothety-criterion>

#definition(numbered: false)[
  Пусть $g$ — полулинейный изоморфизм $V$ на $V$. Будем говорить, что $g$
  _сохраняет ортогональность_, если из равенства $(x,y)=0$ следует, что
  $(g x,g y)=0$ для всех $x,y$ из $V$.
]
#idx("изоморфизм, сохраняющий ортогональность")

#proposition[
  Пусть $g$ — полулинейный изоморфизм пространства $V$ на себя. Тогда $g$
  сохраняет ортогональность в том и только том случае, когда
  $(g x,g y)=lambda(x, y)^u$ для всех $x,y$ из $V$, где $lambda$ — ненулевой
  скаляр, не зависящий от $x$ и $y$, а $u$ — автоморфизм поля, связанный с $g$.
] <prop:solazzi-symplectic-semilinear-similitude>

#proof[
  Очевидно, если $(g x,g y)=lambda(x, y)^u$ для всех $x,y$, то $g$ сохраняет
  ортогональность. Обратное доказано в @bib:solazzi-symplectic-OMeara1968,
  стр.~113.
]

#corollary(base: [@prop:solazzi-symplectic-semilinear-similitude], suffix: "а")[
  Если $g$ — полулинейный изоморфизм $V$ на себя, то $g$ сохраняет
  ортогональность тогда и только тогда, когда таков $g^(-1)$.
] <cor:solazzi-symplectic-inverse-orthogonality>

#proposition[
  Пусть $g$ — полулинейный изоморфизм $V$ на себя, сохраняющий ортогональность.
  Отображение $Lambda_g$, определенное правилом
  $Lambda_g (sigma)=g sigma g^(-1)$ для всех $sigma$ из $Sp(V)$, является
  автоморфизмом группы $Sp(V)$.
] <prop:solazzi-symplectic-semilinear-conjugation>

#proof[
  Если $sigma in Sp(V)$, то $g sigma g^(-1)$ — линейное преобразование. Прямые
  вычисления с помощью @prop:solazzi-symplectic-semilinear-similitude
  показывают, что $(g sigma g^(-1)(x),g sigma g^(-1)(y))=(x,y)$ для всех $x,y$
  из $V$. Значит, $g sigma g^(-1) in Sp(V)$. Точно так же
  $g^(-1) sigma g in Sp(V)$. Поэтому $Lambda_g$ отображает $Sp(V)$ на $Sp(V)$.
  Очевидно, $Lambda_g$ взаимно однозначно и мультипликативно, следовательно,
  $Lambda_g$ — автоморфизм группы $Sp(V)$.
]

#definition(numbered: false)[
  Пусть $g$ — полулинейный изоморфизм $V$ на $V$, сохраняющий ортогональность.
  При $sigma in Sp(V)$ положим $Lambda_g (sigma)=g sigma g^(-1)$, тогда
  $Lambda_g$ — автоморфизм группы $Sp(V)$. Определим автоморфизм
  $overline(Lambda)_g$ группы $PSp(V)$, полагая
  $overline(Lambda)_g (overline(sigma))=overline(Lambda_g (sigma))$ для всех
  $overline(sigma) in PSp(V)$. Если $overline(Lambda)_g (G)=G$, то обозначим
  ограничение $overline(Lambda)_g$ на $G$ снова через $overline(Lambda)_g$.
  Точно так же, если $S$ — подгруппа из $Sp(V)$, имеющая достаточно много
  трансвекций, и $Lambda_g (S)=S$, то мы обозначаем ограничение $Lambda_g$ на
  $S$ тем же символом $Lambda_g$.
]

#proposition[
  #source(196)
  Предположим, что $dim V >= 2$, а $G$ — подгруппа группы $PSp(V)$, имеющая
  достаточно много трансвекций. Пусть $Lambda$ — изоморфизм $G$ в $PSp(V)$,
  такой, что если $overline(tau)$ — проективная трансвекция из $G$, то и
  $Lambda overline(tau)$ — проективная трансвекция с той же собственной прямой,
  что и у $overline(tau)$. Тогда $Lambda$ действует на $G$ тождественно.
] <prop:solazzi-symplectic-axis-rigidity>

#proof[
  Пусть $overline(sigma)$ — произвольный элемент из $G$ и
  $overline(sigma)'=Lambda overline(sigma)$. Для всякой прямой $L$ из $V$
  существует нетривиальная проективная трансвекция $overline(tau) in G$ такая,
  что $L$ — ее собственная прямая. Тогда
  $overline(sigma)overline(tau)overline(sigma)^(-1)$ — проективная трансвекция с
  собственной прямой $sigma L$. По условию ту же собственную прямую имеет
  $Lambda(overline(sigma)overline(tau)overline(sigma)^(-1))$. Но
  $Lambda(overline(sigma)overline(tau)overline(sigma)^(-1))=
  overline(sigma)' Lambda overline(tau) overline(sigma)'^(-1)$ и, так как $L$ —
  собственная прямая для $Lambda overline(tau)$, то $sigma'L$ — собственная
  прямая для $Lambda(overline(sigma)overline(tau)overline(sigma)^(-1))$. Отсюда
  следует, что $sigma L=sigma'L$ для всех прямых $L$, значит,
  $sigma=plus.minus sigma'$. Таким образом,
  $overline(sigma)=overline(plus.minus sigma')=
  Lambda overline(sigma)$ для всех $overline(sigma)$ из $G$, что и требовалось
  доказать.
]

Пусть теперь $dim V >= 6$, $chi(F) != 2$ и $G$ — подгруппа группы $PSp(V)$,
имеющая достаточно много проективных трансвекций. Предположим, что $Lambda$ —
автоморфизм группы $G$. Ввиду @prop:solazzi-symplectic-transvection-preservation
и
@prop:solazzi-symplectic-maximal-transvection-groups
$Lambda overline(T)(L)$ — максимальная группа трансвекций из $G$ для любой
прямой $L$ в пространстве $V$. Снова используя
@prop:solazzi-symplectic-maximal-transvection-groups, найдем единственную прямую
$L'$, такую, что $Lambda overline(T)(L)=overline(T)(L')$. Легко видеть, что
соответствие $L arrow.r.bar L'$ — биекция на множестве прямых из $V$. Поскольку
перестановочность нетривиальных проективных трансвекций равносильна
ортогональности их собственных прямых, то условие $(L_1,L_2)=0$ влечет за собой
$(L'_1,L'_2)=0$. Любая гиперплоскость описывается как ортогональное дополнение к
некоторой прямой, поэтому образы (при соответствии $L arrow.r.bar L'$) всех
прямых из некоторой гиперплоскости образуют гиперплоскость. Таким образом,
биекция $L arrow.r.bar L'$ удовлетворяет предпосылкам основной теоремы
проективной геометрии, а потому существует полулинейный изоморфизм $g$
пространства $V$ на себя с условием, что $g L=L'$ для всех прямых $L$.
Непосредственно видно, что $g$ сохраняет ортогональность. Значит, $Lambda_g$ —
автоморфизм группы $Sp(V)$ по предложению
@prop:solazzi-symplectic-semilinear-conjugation. Теперь нетрудно заметить, что
$overline(Lambda)_g^(-1) compose Lambda$ — изоморфизм группы $G$ в $PSp(V)$,
удовлетворяющий предположениям из @prop:solazzi-symplectic-axis-rigidity.
Следовательно, $Lambda=overline(Lambda)_g$ и справедлива

#theorem[
  Пусть $V$ — векторное пространство над полем $F$, $chi(F) != 2$, $dim V >= 6$.
  Пусть $G$ — подгруппа группы $PSp(V)$, имеющая достаточно много проективных
  трансвекций,
  #source(197)
  а $Lambda$ — автоморфизм группы $G$. Тогда существует полулинейный изоморфизм
  $g$ пространства $V$ на себя, сохраняющий ортогональность и такой, что
  $Lambda=overline(Lambda)_g$.
] <th:solazzi-symplectic-projective-automorphisms>

#corollary(
  base: [@th:solazzi-symplectic-projective-automorphisms],
  suffix: "а",
)[
  Пусть $V$, $chi(F)$ и $n$ удовлетворяют предпосылкам из
  @th:solazzi-symplectic-projective-automorphisms. Пусть $S$ — подгруппа группы
  $Sp(V)$, имеющая достаточно много трансвекций, и $Lambda$ — автоморфизм группы
  $S$. Тогда существуют полулинейный изоморфизм $g$ пространства $V$ на себя,
  сохраняющий ортогональность, и гомоморфизм $chi$ группы $S$ в
  $plus.minus 1_V$, такие, что $Lambda sigma=chi(sigma) dot Lambda_g (sigma)$
  для всех $sigma in S$.
] <cor:solazzi-symplectic-linear-automorphisms>

#proof[
  Отображение $overline(Lambda)$ группы $overline(S)$, определенное по правилу
  $overline(Lambda)(overline(sigma))=overline(Lambda sigma)$, $sigma in S$,
  является автоморфизмом группы $overline(S)$, значит,
  $overline(Lambda)=overline(Lambda)_g$ для некоторого $g$. Поскольку
  $overline(Lambda sigma)=overline(Lambda_g (sigma))$ для всех $sigma$ из $S$,
  то $Lambda sigma=chi(sigma) dot Lambda_g (sigma)$, где
  $chi(sigma)=plus.minus 1_V$. Но $Lambda$ — автоморфизм, поэтому $chi$ —
  гомоморфизм. Следствие доказано.
]

#proposition[
  Пусть $n >= 6$, $chi(F) != 2$ и $S$ — подгруппа группы $Sp(V)$, имеющая
  достаточно много трансвекций. Предположим, что $-1_V in S$. Тогда существуют
  гомотетия $P_chi$ и автоморфизм $Lambda_g$ группы $S$, такие, что
  $Lambda=P_chi compose Lambda_g$.
] <prop:solazzi-symplectic-homothety-decomposition>

#proof[
  Ввиду @cor:solazzi-symplectic-linear-automorphisms имеем
  $Lambda sigma=chi_1(sigma)Lambda_g (sigma)$ для всех $sigma$ из $S$, где
  $chi_1$ — гомоморфизм $S$ в $plus.minus 1_V$, а $Lambda_g$ — автоморфизм
  группы $Sp(V)$. Положим $chi(sigma)=chi_1(Lambda_g^(-1)(sigma))$ для всех
  $sigma$ из $S$. Так как $chi(plus.minus 1_V)=1_V$, то из
  @prop:solazzi-symplectic-homothety-criterion следует, что отображение
  $sigma arrow.r.bar chi(sigma)sigma=P_chi (sigma)$ — гомотетия на $S$.
  Очевидно, $Lambda=P_chi compose Lambda_g$, что и требовалось доказать.
]
