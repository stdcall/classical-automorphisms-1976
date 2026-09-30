#import "main-defs.typ": *
#import "statements.typ": *

== Доказательство основной теоремы <sec:yan-main-proof>

В этом параграфе мы докажем утверждение, упомянутое в §~@sec:yan-introduction, а
также соответствующий результат для областей главных идеалов.

#theorem[
  #source(238)
  Пусть $R$ — коммутативная область целостности характеристики $!=2$, $n>=3$.
  Пусть $cal(A)$ — изоморфизм группы $SL_n (R)$ в $GL_n (R)$. Тогда $cal(A)$
  имеет вид @eq:yan-standard-isomorphism или @eq:yan-contragredient-isomorphism.
  Обратное также справедливо.
] <th:yan-main-isomorphism>

#proof[
  По теореме @th:yan-elementary-matrix-images существует матрица
  $P_1 in GL_n (K(R))$ ($K(R)$ — поле частных кольца $R$), такая, что
  $
    P_1 cal(A)(B_(i j)(1))P_1^(-1)=B_(i j)(1), quad
    i!=j, quad i,j=1,...,n,
  $
  или
  $
    P_1 cal(A)(B_(i j)(1))P_1^(-1)=B_(j i)(-1), quad
    i!=j, quad i,j=1,...,n.
  $
  Существует элемент $a in R$, такой, что $a P_1=P$ — невырожденная матрица
  порядка $n$ над $R$ и, значит,
  $ P cal(A)(B_(i j)(1))=B_(i j)(1)P, quad i!=j, quad i,j=1,...,n, $
  <eq:yan-main-positive>
  или
  $ P cal(A)(B_(i j)(1))=B_(j i)(-1)P, quad i!=j, quad i,j=1,...,n. $
  <eq:yan-main-negative>
  Из теоремы @th:yan-inner-isomorphism немедленно следует, что $P$ удовлетворяет
  условию @eq:yan-ideal-condition. Покажем теперь, что в случае
  @eq:yan-main-positive имеет место @eq:yan-standard-isomorphism. В случае
  @eq:yan-main-negative можно использовать тот же метод.

  Прежде всего, из теоремы @th:yan-inner-isomorphism мы знаем, что
  $P cal(A)(B_12(lambda))P^(-1)$ — матрица над $R$. Далее, так как
  $cal(A)(B_12(lambda))$ перестановочна с $cal(A)(B_12(1))$ и
  $cal(A)(B_(i j)(1))$, $3<=i,j<=n$, то, используя @eq:yan-main-positive,
  получаем
  $ P cal(A)(B_12(lambda))P^(-1)=mat(a, b; 0, a)⊕(a_1 I)^((n-2)). $
  Кроме того, так как
  $cal(A)(S_23^(-1))cal(A)(B_12(lambda))cal(A)(S_23)=cal(A)(B_13(lambda))$, то
  $
    P cal(A)(B_13(lambda))P^(-1)=mat(a, 0, b; 0, a_1, 0; 0, 0, a)⊕(a_1
      I)^((n-3)).
  $
  Снова, так как
  $
    P cal(A)(B_13(lambda))P^(-1)
    =P(cal(A)(B_12(-lambda))cal(A)(B_23(-1))
      cal(A)(B_12(lambda))cal(A)(B_23(1)))P^(-1),
  $
  то
  $
    P cal(A)(B_13(lambda))P^(-1)
    =mat(1, 0, a_1 a^(-2)b; 0, 1, 1-a^(-1)a_1; 0, 0, 1)⊕I^((n-3)).
  $
  #source(239)
  Сравнивая эти две формулы, получаем $a=a_1=1$. Таким образом,
  $
    P cal(A)(B_12(lambda))P^(-1)=I^((n))+lambda^sigma E_12, quad
    P cal(A)(B_13(lambda))P^(-1)=I^((n))+lambda^sigma E_13.
  $
  <eq:yan-elementary-parameter>
  Используя эти формулы и @eq:yan-main-positive, получаем
  $
    P cal(A)(B_(1j)(lambda))P^(-1)
    &=[P cal(A)(B_12(-lambda))P^(-1)]
    [P cal(A)(B_(2j)(-1))P^(-1)]\
    &quad [P cal(A)(B_12(lambda))P^(-1)]
    [P cal(A)(B_(2j)(1))P^(-1)]\
    &=B_12(-lambda^sigma)B_(2j)(-1)B_12(lambda^sigma)B_(2j)(1)
    =B_(1j)(lambda^sigma),\
    P cal(A)(B_(i j)(lambda))P^(-1)
    &=[P cal(A)(B_(i 1)(-1))P^(-1)]
    [P cal(A)(B_(1j)(-lambda))P^(-1)]\
    &quad [P cal(A)(B_(i 1)(1))P^(-1)]
    [P cal(A)(B_(1j)(lambda))P^(-1)]\
    &=B_(i 1)(-1)B_(1j)(-lambda^sigma)
    B_(i 1)(1)B_(1j)(lambda^sigma)=B_(i j)(lambda^sigma).
  $ <eq:yan-all-elementary-parameters>
  Покажем теперь, что $sigma$ — изоморфизм кольца $R$ в себя. Из соотношений
  $cal(A)(B_12(lambda))cal(A)(B_12(mu))=cal(A)(B_12(lambda+mu))$ и
  @eq:yan-elementary-parameter следует, что
  $ (lambda+mu)^sigma=lambda^sigma+mu^sigma, quad lambda,mu in R. $
  Если $cal(A)(B_12(lambda))=I$, то $B_12(lambda)=I$, откуда $lambda=0$; поэтому
  из $lambda^sigma=0$ следует $lambda=0$. Далее, ввиду
  @eq:yan-all-elementary-parameters имеем
  $
    B_13((lambda mu)^sigma)&=P cal(A)(B_13(lambda mu))P^(-1)\
    &=[P cal(A)(B_12(-lambda))P^(-1)]
    [P cal(A)(B_23(-mu))P^(-1)]\
    &quad [P cal(A)(B_12(lambda))P^(-1)]
    [P cal(A)(B_23(mu))P^(-1)]\
    &=B_12(-lambda^sigma)B_23(-mu^sigma)
    B_12(lambda^sigma)B_23(mu^sigma)=B_13(lambda^sigma mu^sigma).
  $
  Следовательно,
  $ (lambda mu)^sigma=lambda^sigma mu^sigma, $
  и теорема доказана.
]

В случае, когда $R$ — область главных идеалов, аналогом теоремы
@th:yan-main-isomorphism является

#theorem[
  Если $R$ — область главных идеалов (не обязательно коммутативная)
  характеристики $!=2$, $n>=3$ и $cal(A)$ — изоморфизм группы $SL_n (R)$ в
  $GL_n (R)$, то либо
  $ cal(A)(X)=P^(-1)X^sigma P, quad X in SL_n (R), $ <eq:yan-pid-positive>
  #source(240)
  либо
  $ cal(A)(X)=P^(-1)((X^tau)')^(-1)P, quad X in SL_n (R), $
  <eq:yan-pid-negative>
  где $sigma$ — изоморфизм кольца $R$ в себя, $tau$ — антиизоморфизм кольца $R$
  в себя и $P in GL_n (R)$.
] <th:yan-pid-isomorphism>

#proof[
  Из теоремы @th:yan-elementary-matrix-images следует существование матрицы
  $P_1 in GL_n (K(R))$, такой, что $P_1 cal(A)(B_(i j)(1))=B_(i j)(1)P_1$,
  $i!=j$, $i,j=1,...,n$, или $P_1 cal(A)(B_(i j)(1))=B_(j i)(-1)P_1$, $i!=j$,
  $i,j=1,...,n$. Следовательно, существует элемент $a in R$, такой, что
  $a P_1=P_2$ — невырожденная матрица над $R$ и $a B_(i j)(1)P_1=B_(i j)(1)P_2$,
  $a B_(j i)(-1)P_1=B_(j i)(-1)P_2$. Значит, либо
  $P_2 cal(A)(B_(i j)(1))=B_(i j)(1)P_2$, либо
  $P_2 cal(A)(B_(i j)(1))=B_(j i)(-1)P_2$. По теореме
  @th:yan-principal-domain-intertwiner существует матрица $P in GL_n (R)$,
  такая, что
  $ cal(A)(B_(i j)(1))=P^(-1)B_(i j)(1)P, quad i!=j, quad i,j=1,...,n, $
  <eq:yan-pid-elementary-positive>
  или
  $ cal(A)(B_(i j)(1))=P^(-1)B_(j i)(-1)P, quad i!=j, quad i,j=1,...,n. $
  <eq:yan-pid-elementary-negative>
  Так же как и в теореме @th:yan-main-isomorphism, из
  @eq:yan-pid-elementary-positive можно вывести соотношение
  @eq:yan-pid-positive, а из @eq:yan-pid-elementary-negative — соотношение
  @eq:yan-pid-negative. Теорема доказана.
]

Теорема @th:yan-pid-isomorphism была впервые доказана Вань Чже-сянем
@bib:yan-Wan1957 и Лэндином и Райнером @bib:yan-LandinReiner1957. Наше
доказательство значительно проще, чем в @bib:yan-Wan1957, за счет использования
теоремы @th:yan-principal-domain-intertwiner.

#theorem[
  Пусть $R$ — коммутативная область целостности характеристики $!=2$, $n>=3$ и
  $S_n (R)$ — произвольная подгруппа из $GL_n (R)$, содержащая $T_n (R)$. Тогда
  $T_n (R)$ — автоморфно допустимая подгруппа группы $S_n (R)$ (т. е. всякий
  автоморфизм группы $S_n (R)$ индуцирует автоморфизм группы $T_n (R)$).
] <th:yan-characteristic-transvection-group>

#proof[
  Пусть $SL_n (R,P)$ — подгруппа, порожденная матрицами $T_(i j)(lambda,P)$
  (§~@sec:yan-introduction), полученными из некоторой фиксированной матрицы $P$,
  удовлетворяющей условию @eq:yan-ideal-condition. Пусть $cal(A)$ — произвольный
  автоморфизм группы $S_n (R)$. Тогда $cal(A)$ индуцирует изоморфизм группы
  $SL_n (R,P)$ в $S_n (R)$. Пусть $cal(A)_1(X)=P^(-1)X P$, $X in SL_n (R)$.
  Отображение $cal(A)_1$ является изоморфизмом группы $SL_n (R)$ в $SL_n (R,P)$,
  и $cal(A)_1(B_(i j)(lambda))=T_(i j)(lambda,P)$. Следовательно,
  $cal(A)cal(A)_1$ — изоморфизм группы $SL_n (R)$ в $S_n (R)$. По теореме
  @th:yan-main-isomorphism
  $
    cal(A)(Y)=cal(A)(cal(A)_1(X))=P_1^(-1)X^sigma P_1, quad
    Y in SL_n (R,P), quad X in SL_n (R),
  $ <eq:yan-subgroup-positive>
  #source(241)
  или
  $
    cal(A)(Y)=cal(A)(cal(A)_1(X))=P_1^(-1)[(X^sigma)']^(-1)P_1, quad
    Y in SL_n (R,P),\
    X in SL_n (R).
  $ <eq:yan-subgroup-negative>
  Так как $sigma$ — изоморфизм кольца $R$ в себя, то $cal(A)$ отображает
  $T_n (R)$ в себя.

  Из сказанного выше ясно, что для доказательства теоремы достаточно установить
  следующие два факта: (а) $sigma$ в @eq:yan-subgroup-positive или
  @eq:yan-subgroup-negative является автоморфизмом кольца $R$ при любой группе
  $SL_n (R,P)$; (б) если $P$ может быть произвольной матрицей, удовлетворяющей
  условию @eq:yan-ideal-condition, то и $P_1$ может быть такой же.

  Докажем сначала (а). Мы ограничимся случаем @eq:yan-subgroup-positive, так как
  доказательство в случае @eq:yan-subgroup-negative вполне аналогично. Допустим,
  что $sigma$ не является автоморфизмом кольца $R$. Тогда существует
  $mu!=lambda^sigma$ для всех $lambda in R$, поэтому
  $cal(A)(T_12(lambda,P))!=P_1^(-1)B_12(mu)P_1$ для всех $lambda in R$. Пусть
  $P_1^(-1)B_12(mu)P_1=cal(A)(B)$, $B in S_n (R)$. Так как матрица
  $P_1^(-1)B_12(mu)P_1$ перестановочна с $P_1^(-1)B_(i j)(1)P_1$, $3<=i,j<=n$,
  $P_1^(-1)J_12 P_1$ и $P_1^(-1)B_13(1)P_1$, то из @eq:yan-subgroup-positive
  следует, что $B$ перестановочна с $P^(-1)B_(i j)(1)P$, $3<=i,j<=n$,
  $P^(-1)J_12 P$ и $P^(-1)B_13(1)P$. Отсюда простым вычислением получаем
  $ B=e P^(-1)B_12(lambda_1)P, quad lambda_1,e^(-1) in R. $
  Так как $B_12(mu)J_13 B_12(mu)=J_13$, то $e^2=1$, $e=±1$. Следовательно, из
  @eq:yan-subgroup-positive и того, что $cal(A)$ — автоморфизм группы $S_n (R)$,
  получаем
  $
    cal(A)(B)=e P_1^(-1)B_12(lambda_1^sigma)P_1
    =P_1^(-1)B_12(mu)P_1.
  $
  Отсюда $e=1$, $lambda_1^sigma=mu$. Но это противоречит тому, что
  $mu!=lambda^sigma$, и (а) доказано.

  Теперь докажем (б). Допустим, что существует матрица $P_1$, удовлетворяющая
  условию @eq:yan-ideal-condition и такая, что для всех матриц $P$,
  удовлетворяющих @eq:yan-ideal-condition, не выполняется ни одно из соотношений
  @eq:yan-subgroup-positive, @eq:yan-subgroup-negative. Рассмотрим
  $cal(A)^(-1)$. Так как $cal(A)$ — автоморфизм группы $S_n (R)$, то
  $cal(A)^(-1)$ — также автоморфизм. Из теоремы @th:yan-main-isomorphism
  заключаем, что существует матрица $P_2$, удовлетворяющая
  @eq:yan-ideal-condition и такая, что
  $
    cal(A)^(-1)(T_(i j)(lambda,P_1))=P_2^(-1)B_(i j)(lambda^(sigma_1))P_2,
    quad i!=j, quad i,j=1,2,...,n, quad lambda in R,
  $
  #source(242)
  или
  $
    cal(A)^(-1)(T_(i j)(lambda,P_1))=P_2^(-1)B_(j i)(-lambda^(sigma_1))P_2,
    quad i!=j, quad i,j=1,...,n, quad lambda in R,
  $
  где $sigma_1$ — автоморфизм кольца $R$. Применив $cal(A)$ к этим равенствам,
  получим противоречие с нашим допущением. Таким образом, утверждение (б), а
  вместе с ним теорема доказаны.
]

В случае когда $R$ — область главных идеалов, теорема
@th:yan-characteristic-transvection-group имеет следующий аналог:

#theorem[
  Предположим, что $R$ — область главных идеалов характеристики $!=2$, $n>=3$ и
  $T_n (R)$ обозначает группу, порожденную всеми матрицами
  $P^(-1)B_(i j)(lambda)P$, $P in GL_n (R)$, $lambda in R$, $i!=j$,
  $i,j=1,2,...,n$. Пусть $S_n (R)$ — произвольная подгруппа группы $GL_n (R)$,
  содержащая $T_n (R)$. Тогда $T_n (R)$ — автоморфно допустимая подгруппа группы
  $S_n (R)$.
] <th:yan-pid-characteristic-transvection-group>

Доказательство аналогично доказательству теоремы
@th:yan-characteristic-transvection-group и потому опускается.

Результаты этого параграфа естественно приводят к вопросу: если $R$ —
коммутативная область целостности с единицей характеристики $!=2$, то каковы
автоморфизмы групп $GL_n (R)$ и $L_n (R)$ при $n>=3$? Его решение зависит от
описания автоморфизмов группы $T_n (R)$. Автор предполагает, что если $R$
удовлетворяет указанным выше условиям и $n>=3$, то для всякого автоморфизма
$cal(A)$ группы $T_n (R)$ либо $P cal(A)(X)=X^sigma P$ для всех $X in T_n (R)$,
либо $P cal(A)(X)=(X^sigma)'^(-1)P$ для всех $X in T_n (R)$, где $sigma$ —
автоморфизм кольца $R$ и $P$ удовлетворяет условию @eq:yan-ideal-condition.
