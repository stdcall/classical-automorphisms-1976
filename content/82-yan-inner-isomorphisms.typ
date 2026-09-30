#import "main-defs.typ": *
#import "statements.typ": *

== Теорема о «внутреннем» изоморфизме и некоторые элементарные применения
<sec:yan-inner-isomorphisms>

Основная цель этого параграфа — доказать следующую теорему.

#theorem[
  Пусть $R$ — коммутативная область целостности. Если $P$ — невырожденная
  матрица порядка $n$ над $R$ и
  #source(226)
  для всякого $E_(i j)$, $i != j$, $1 <= i,j <= n$, существует матрица $X_(i j)$
  порядка $n$ над $R$, такая, что
  $ P X_(i j)=E_(i j)P, $ <eq:yan-elementary-intertwining>
  то $P$ удовлетворяет условию @eq:yan-ideal-condition. Обратно, если $P$
  удовлетворяет условию @eq:yan-ideal-condition, то для всякой матрицы $X$
  порядка $n$ над $R$ существуют матрицы $Y$ и $Z$ порядка $n$, такие, что
  $ P X=Y P, quad X P=P Z. $ <eq:yan-two-sided-intertwining>
] <th:yan-inner-isomorphism>

#proof[
  а) Пусть $P=(a_(i j))$, $X_(i j)=(x_(k l))$. Ввиду
  @eq:yan-elementary-intertwining
  $ a_(j k)=sum_(l=1)^n a_(i l)x_(l k), quad k=1,2,...,n, $
  откуда $(a_(j 1),...,a_(j n)) subset.eq (a_(i 1),...,a_(i n))$, $i != j$.
  Следовательно
  $
    (a_11,...,a_(1n))=(a_(i 1),...,a_(i n)), quad i=1,2,...,n.
  $ <eq:yan-row-ideals>
  Пусть, далее, $K(R)$ обозначает поле частных кольца $R$. Снова ввиду
  @eq:yan-elementary-intertwining
  $
    X_(i j)=1/abs(P) (A_(k l))' E_(i j)(a_(k l))=(A_(i k)a_(j l)/abs(P)),
    quad i != j, quad 1 <= i,j <= n.
  $
  Так как $X_(i j)$ — матрица над $R$, то
  $
    A_(i k)a_(j l) in (abs(P)), quad i != j, quad 1 <= i,j <= n, quad 1 <=
    k,l <= n.
  $ <eq:yan-cofactor-ideal-inclusion>
  Из @eq:yan-row-ideals видно, что $A_(i k)a_(i l) in (abs(P))$, и,
  следовательно, $P$ удовлетворяет условиям @eq:yan-row-ideals и
  @eq:yan-cofactor-ideal-inclusion (включая случай $i=j$).

  б) Предположим, что $P$ удовлетворяет условиям @eq:yan-row-ideals и
  @eq:yan-cofactor-ideal-inclusion. Тогда для любой матрицы $X=(x_(i j))$
  порядка $n$ над $R$ имеем
  $ P X P^(-1)=(sum_(k,l=1)^n (a_(i k)x_(k l)A_(j l))/abs(P)). $
  Из @eq:yan-cofactor-ideal-inclusion следует, что $P X P^(-1)$ — матрица над
  $R$ и аналогично $P^(-1)X P$ — также матрица над $R$.

  в) Покажем теперь, что @eq:yan-row-ideals и @eq:yan-cofactor-ideal-inclusion в
  совокупности равносильны условию @eq:yan-ideal-condition. Очевидно,
  @eq:yan-row-ideals и @eq:yan-cofactor-ideal-inclusion непосредственно следуют
  из @eq:yan-ideal-condition. Обратно, если @eq:yan-row-ideals и
  @eq:yan-cofactor-ideal-inclusion выполняются, то из
  @eq:yan-cofactor-ideal-inclusion следует, что
  $ (abs(P)) supset.eq (A_11,A_12,...,A_(n n))(a_11,...,a_(1n)). $
  #source(227)
  Отсюда и из теоремы об определителях
  $
    (abs(P))^n & supset.eq (A_11,...,A_(n n))^(n)(a_11,...,a_(1n))^n \
               & supset.eq (abs(A_(i j)))(a_11,...,a_(1n))^n \
               & =(abs(P)^(n-1))(a_11,...,a_(1n))^n \
               & =(abs(P))^(n-1)(a_11,...,a_(1n))^n.
  $
  С другой стороны,
  $
    (a_11,...,a_(1n))^n=(a_11,...,a_(1n)) dots (a_(n 1),...,a_(n n))
    supset.eq (abs(P)),
  $
  и, значит,
  $ (abs(P))^n=(abs(P))^(n-1)(a_11,...,a_(1n))^n. $
  Следовательно, $(abs(P))=(a_11,...,a_(1n))^n$, и теорема доказана.
]

#corollary[
  Множество всех невырожденных матриц порядка $n$ над $R$, удовлетворяющих
  условию @eq:yan-ideal-condition, является полугруппой относительно матричного
  умножения.
] <cor:yan-intertwiner-semigroup>

Многие вопросы, касающиеся матриц над $R$, можно изучать над полем частных
кольца $R$, и теорема @th:yan-inner-isomorphism обеспечивает нам обратный
переход. Например, справедлива

#theorem[
  Пусть $R$ — коммутативная область целостности, $M_n (R)$ — кольцо всех матриц
  порядка $n$ над $R$. Всякий автоморфизм $cal(A)$ кольца $M_n (R)$ может быть
  записан в виде
  $
    P cal(A)(X)=X^sigma P, quad X in M_n (R),
  $ <eq:yan-matrix-ring-automorphism>
  где $P$ — матрица, удовлетворяющая @eq:yan-ideal-condition, $sigma$ —
  автоморфизм кольца $R$. Обратно, отображение, определенное формулой
  @eq:yan-matrix-ring-automorphism, является автоморфизмом кольца $M_n (R)$.
] <th:yan-matrix-ring-automorphisms>

#proof[
  Пусть $K(R)$ — поле частных кольца $R$. Так как
  $E_(i j)E_(k l)=delta_(j k)E_(i l)$, то
  $
    cal(A)(E_(i j))cal(A)(E_(k l))=cases(
      0 & "при" k != j, cal(A)(E_(i l))
      & "при" k=j
    ).
  $
  По хорошо известной теореме существует невырожденная матрица $Q$ порядка $n$
  над $K(R)$, такая, что
  $
    cal(A)(E_(i j))=Q^(-1)E_(i j)Q, quad 1 <= i,j <= n.
  $ <eq:yan-matrix-units-conjugation>
  Более того, можно выбрать элемент $a != 0$ в $R$ так, что $a Q=P$ будет
  матрицей порядка $n$ над $R$. Тогда ввиду @eq:yan-matrix-units-conjugation
  $
    P cal(A)(E_(i j))=E_(i j)P, quad 1 <= i,j <= n.
  $ <eq:yan-matrix-units-intertwining>
  #source(228)
  Из теоремы @th:yan-inner-isomorphism видно, что $P$ удовлетворяет условию
  @eq:yan-ideal-condition.

  Теперь рассмотрим $cal(A)(lambda E_(i j))$, $lambda in R$. Так как
  $cal(A)(lambda E_(i j))=cal(A)(E_(i i))cal(A)(lambda E_(i j))cal(A)(E_(j j))$,
  то ввиду @eq:yan-matrix-units-intertwining
  $
    cal(A)(lambda E_(i j))=P^(-1)(lambda^(sigma_(i j)) E_(i j))P, quad
    i,j=1,2,...,n.
  $ <eq:yan-entry-field-map>
  Используя тот факт, что
  $cal(A)(lambda E_(i j))=cal(A)(E_(i 1))cal(A)(lambda E_11)cal(A)(E_(1j))$, мы
  видим, что для любого $lambda in R$
  $ lambda^sigma=lambda^(sigma_11)=lambda^(sigma_(i j)), quad i,j=1,2,...,n, $
  другими словами, $sigma=sigma_11=sigma_(i j)$. Из @eq:yan-entry-field-map
  следует, что $sigma$ — взаимно однозначное отображение кольца $R$ на себя,
  сохраняющее сложение. Далее, из
  $cal(A)(lambda mu E_11)=cal(A)(lambda E_11)cal(A)(mu E_11)$ следует, что
  $sigma$ сохраняет умножение и потому является автоморфизмом кольца $R$. Так
  как $cal(A)$ — автоморфизм кольца $M_n (R)$, то получаем первую часть теоремы.

  Обратно, отображение, определенное формулой @eq:yan-matrix-ring-automorphism,
  является, очевидно, изоморфизмом кольца $M_n (R)$ в себя. Из условия, которому
  удовлетворяет $P$, легко вывести, что если $X in M_n (R)$, то
  $P X P^(-1) in M_n (R)$. Отсюда сразу следует, что это отображение кольца
  $M_n (R)$ на себя. Теорема доказана.
]

Аналогично доказывается

#theorem[
  Предположим, что $R,R_1$ — коммутативные области целостности, $cal(A)$ —
  изоморфизм кольца $M_n (R)$ на $M_m (R_1)$. Тогда $m=n$, $R$ и $R_1$ изоморфны
  и существует матрица $P$ порядка $n$ над $R_1$, удовлетворяющая условию
  @eq:yan-ideal-condition и такая, что
  $
    cal(A)(X)=P^(-1)X^sigma P, quad X in M_n (R),
  $ <eq:yan-matrix-ring-isomorphism>
  где $sigma$ — изоморфизм $R$ на $R_1$. Обратно, всякое отображение,
  определенное формулой @eq:yan-matrix-ring-isomorphism, является изоморфизмом
  $M_n (R)$ на $M_n (R_1)$.
] <th:yan-matrix-ring-isomorphisms>

Отметим, что теорема @th:yan-inner-isomorphism может быть применена также к
описанию автоморфизмов и антиавтоморфизмов кольца всех квадратных матриц над
коммутативной областью целостности и к описанию автоморфизмов полугруппы матриц
по умножению.

Для некоммутативного $R$ может быть доказана

#theorem[
  Если $R$ — область главных идеалов (не обязательно коммутативная) и $P$ —
  невырожденная матрица порядка $n$ над $R$, удовлетворяющая условию
  @eq:yan-elementary-intertwining, то
  #source(229)
  существует матрица $P_1 in GL_n (R)$, такая, что
  $
    P_1 X_(i j)=E_(i j)P_1, quad i != j, quad 1 <= i,j <= n,
  $ <eq:yan-principal-intertwiner>
  где $X_(i j)$ — матрицы с условием @eq:yan-elementary-intertwining.
] <th:yan-principal-domain-intertwiner>

#proof[
  Из доказательства теоремы @th:yan-inner-isomorphism видно, что правый идеал,
  порожденный элементами $a_11,...,a_(1n)$, совпадает с правым идеалом,
  порожденным элементами $a_(i 1),...,a_(i n)$, $i=1,...,n$. Поэтому все правые
  идеалы $(a_(i 1),...,a_(i n))$, $i=1,...,n$, совпадают с некоторым главным
  правым идеалом $a R$ и $a_(i j)=a a'_(i j)$. Пусть $P=a P_1$. Тогда $P_1$ —
  невырожденная матрица над $R$, и выполняется @eq:yan-principal-intertwiner.
  Докажем, что $P_1 in GL_n (R)$.

  Так как $R$ — область главных идеалов, то ее можно вложить
  @bib:yan-Jacobson1943 в тело частных $K(R)$. В $GL_n (K(R))$ существует
  матрица, обратная к $P_1$, скажем, $P_1^(-1)=(b_(i j))$, $b_(i j) in K(R)$.
  Чтобы показать, что $P_1 in GL_n (R)$, достаточно проверить включения
  $b_(i j) in R$. Из доказательства теоремы @th:yan-inner-isomorphism видно, что
  $ b_(i j)a'_(k l) in R, quad 1 <= i,j,k,l <= n. $
  Но, как замечено выше, $a=a_(k 1)x_1+dots+a_(k n)x_n$, $x_i in R$,
  $a_(k l)=a a'_(k l)$. Отсюда $a'_(k 1)x_1+dots+a'_(k n)x_n=1$ и
  $ b_(i j)=b_(i j)a'_(k 1)x_1+dots+b_(i j)a'_(k n)x_n in R. $
  Теорема доказана.
]
