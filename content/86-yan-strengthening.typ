#import "main-defs.typ": *
#import "statements.typ": *

== Усиление результатов предыдущих параграфов <sec:yan-strengthening>

В этом параграфе мы укажем, как результаты предыдущих параграфов могут быть
усилены. Для доказательств, вполне аналогичных предыдущим или доказательствам,
данным в работе @bib:yan-Yan1957b, мы приводим только наброски. Доказательства,
не совсем аналогичные, будут приведены детально.

#condition-series[
  #condition[
    Пусть $R$ — произвольное кольцо (не обязательно коммутативное) с единицей
    $1$, причем $1+1!=0$. Пусть $G$ — абстрактная группа с единичным элементом
    $I$, порождающими которой являются символы $T_(i j)(lambda)$, $i!=j$,
    $i,j=1,...,n$, $lambda in R$,
    #source(243)
    а соотношения таковы:
    $
      T_(i j)(lambda)T_(i j)(mu)=T_(i j)(lambda+mu),\
      T_(i j)(lambda)=I quad "тогда и только тогда, когда" lambda=0,
    $
    <eq:yan-abstract-additivity>
    $
      T_(i j)(lambda) quad "перестановочно с"
      T_(k j)(mu),T_(i k)(mu),T_(k l)(mu),
    $ <eq:yan-abstract-commutation>
    $
      T_(i j)(-lambda)T_(j k)(-mu)T_(i j)(lambda)T_(j k)(mu)
      =T_(i k)(lambda mu),
    $ <eq:yan-abstract-commutator>
    где индексы $i,j,k,l=1,...,n$ попарно различны, $lambda$ — произвольный
    элемент кольца $R$. Имеем также
    $ T_12(1)T_21(-1)T_12(lambda)=T_21(-lambda)T_12(1)T_21(-1), $
    <eq:yan-abstract-rotation-positive>
    $ T_12(-1)T_21(1)T_12(lambda)=T_21(-lambda)T_12(-1)T_21(1), $
    <eq:yan-abstract-rotation-negative>
    $ (T_12(1)T_21(-1)T_12(2))^3=I, $ <eq:yan-abstract-order-three>
    где $lambda$ — произвольный элемент из $R$.

    Как и в @bib:yan-Yan1957b, положим
    $ U_(i j)=T_(i j)(1)T_(j i)(-1)T_(i j)(1), quad W_(i j)=U_(i j)^2. $
    Можно доказать, что выполняются следующие соотношения:
    <passage:yan-sandwich-sign>
    $
      T_(i k)(lambda)U_(i j)=U_(i j)T_(j k)(lambda), quad
      T_(k i)(lambda)U_(i j)=U_(i j)T_(k j)(lambda),
    $
    <eq:yan-abstract-conjugation-positive>
    $
      T_(j k)(lambda)U_(i j)=U_(i j)T_(i k)(-lambda), quad
      T_(k j)(lambda)U_(i j)=U_(i j)T_(k i)(-lambda),
    $
    <eq:yan-abstract-conjugation-negative>
    $
      U_(i j)=U_(j i)^(-1), quad W_(i j)^2=I, quad W_(i j)=W_(j i), quad
      (U_(i j)T_(i j)(1))^3=I,
    $ <eq:yan-abstract-basic-orders>
    $
      U_(i j)T_(i j)(lambda)=T_(j i)(-lambda)U_(i j), quad
      U_(i j)T_(j i)(lambda)=T_(i j)(-lambda)U_(i j),
    $
    <eq:yan-abstract-reverse-conjugation>
    $ W_(i j) quad "перестановочно с" T_(i j)(lambda),T_(j i)(lambda),U_(i j), $
    <eq:yan-abstract-square-centralizer>
    $
      U_(i j)U_(k i)=U_(k i)U_(j k)=U_(j k)U_(i j),\
      U_(i j)U_(j k)=U_(i k)U_(i j)^(-1)=U_(j k)U_(i k),\
      (U_(i j)U_(j k))^3=I,\
      W_(i j)=T_(i k)(lambda)W_(i j)T_(i k)(lambda)
      =T_(k j)(lambda)W_(i j)T_(k j)(lambda)\
      =T_(k i)(lambda)W_(i j)T_(k i)(lambda)
      =T_(j k)(lambda)W_(i j)T_(j k)(lambda),
    $
    <eq:yan-abstract-three-index-relations>
    $ (T_(i j)(lambda)U_(i k))^4=I, $ <eq:yan-abstract-order-four>
    $ W_(i j)W_(j k)=W_(i k), $ <eq:yan-abstract-square-product>
    $ W_(i j), quad i,j=1,...,n, quad "попарно перестановочны." $
    <eq:yan-abstract-square-commutation>
    В этих соотношениях $i,j,k$ обозначают попарно различные числа из
    последовательности $1,...,n$, $lambda$ — произвольный элемент кольца $R$.

    С тем же доказательством, что и в @bib:yan-Yan1957b, справедлива #theorem[
      Пусть $i_1,...,i_(2m)$ и $i'_1,...,i'_(2l)$ — два множества попарно
      различных чисел из $1,...,n$. Тогда
      #source(244)
      (а) $W_(i_1 i_2)⋯W_(i_(2m-1) i_(2m))$ и
      $W_(i'_1 i'_2)⋯W_(i'_(2l-1) i'_(2l))$ — две перестановочные инволюции
      (элемент $X in G$ называется инволюцией, если $X^2=I$);

      (б) если $m=l$, то $W_(i_1 i_2)⋯W_(i_(2m-1) i_(2m))$ и
      $W_(i'_1 i'_2)⋯W_(i'_(2l-1) i'_(2l))$ сопряжены в $G$;

      (в) если $m=l$ и $i'_1,...,i'_(2m)$ являются перестановкой чисел
      $i_1,...,i_(2m)$, то две инволюции, указанные выше, эквивалентны;

      (г) если $2m<n$, то $W_(i_1 i_2)⋯W_(i_(2m-1) i_(2m))$ не лежит в центре
      группы $G$.
    ] <th:yan-abstract-involution-products>
  ] <cond:yan-abstract-relations>

  #condition[
    В этой части $R$ и $T_(i j)(lambda)$ удовлетворяют не только условиям
    @cond:yan-abstract-relations, но также следующим условиям: $R$ не имеет
    делителей нуля и любые два ненулевых элемента из $R$ имеют общее ненулевое
    правое кратное (т. е. если $a,b in R$, $a,b != 0$, то существует ненулевой
    элемент $m in R$, такой, что $m=a a_1=b b_1$, $a_1,b_1 in R$), и,
    следовательно, $R$ может быть вложено в тело частных $K(R)$. Допустим, что
    $T_(i j)(lambda) in GL_n (R)$ и $W_(i j)$ и $U_(i j)$ определены так же, как
    в @cond:yan-abstract-relations. Тогда справедлива #theorem[
      Если $n$ — четное число, $n>=4$, то
      $ W_12 W_34⋯W_(n-1,n)=-I. $
    ] <th:yan-abstract-even-product>
    #proof[
      Используя @eq:yan-abstract-conjugation-negative,
      @eq:yan-abstract-order-four и части (б) и (в) теоремы
      @th:yan-abstract-involution-products, поступим, как в доказательстве п.
      @cond:yan-even-involution-rank теоремы @th:yan-involution-conjugation, и
      получим, что $W_(i j)$ является $(p,n-p)$-инволюцией группы $GL_n (R)$,
      $2 divides p$. Оставшаяся часть доказательства проводится так же, как
      доказательство соответствующей теоремы в @bib:yan-Yan1957b.
    ]
    <passage:yan-even-product-theorem-reference>

    Учитывая формулы, указанные выше, теоремы
    @th:yan-abstract-involution-products, @th:yan-abstract-even-product и
    замечая, что $W_(i j)$ имеет все свойства матрицы $cal(A)(J_(i j))$, которые
    использовались при доказательстве теоремы @th:yan-involution-conjugation, мы
    получаем следующую теорему: #theorem(
      base: [@th:yan-involution-conjugation],
      suffix: "′",
    )[
      (а) Если $n=3$ или $>=5$, то существует матрица $P in GL_n (K(R))$, такая,
      что
      $ W_(i j)=P^(-1)J_(i j)P, quad i!=j, quad i,j=1,...,n. $

      (б) Если $n=4$, то существует матрица $P in GL_4 (K(R))$, такая, что
      $ W_12=P^(-1)J_12 P. $
    ] <th:yan-involution-conjugation-strengthened>
    Это означает, что справедлива также #theorem(
      base: [@th:yan-elementary-matrix-images],
      suffix: "′",
    )[
      #source(245)
      Если $n>=3$, то существует матрица $P in GL_n (K(R))$, такая, что
      $ P T_(i j)(1)P^(-1)=B_(i j)(1), quad i!=j, quad i,j=1,...,n, $
      или
      $ P T_(i j)(1)P^(-1)=B_(j i)(-1), quad i!=j, quad i,j=1,...,n. $
    ] <th:yan-elementary-images-strengthened>
    #proof[
      а) Если $n=3$ или $>=5$, то мы применяем теорему
      @th:yan-involution-conjugation-strengthened и замечаем, что свойства
      матриц $cal(A)(B_(i j))$, $cal(A)(S_(i j))$ и $cal(A)(J_(i j))$,
      использованные в доказательстве теоремы @th:yan-elementary-matrix-images,
      выполняются для элементов $T_(i j)(1)$, $U_(i j)$ и $W_(i j)$
      соответственно. Отсюда следует, что теорема
      @th:yan-elementary-images-strengthened справедлива при $n=3$ или $>=5$.

      б) Если $n=4$, то в силу леммы @lem:yan-simultaneous-diagonalization,
      теоремы @th:yan-involution-conjugation-strengthened (б) и
      @eq:yan-abstract-square-commutation существует элемент $P$ группы
      $SL_4 (K(R))$, такой, что $P W_12 P^(-1)=J_12$, $P W_23 P^(-1)=J_23$.
      Таким образом, можно положить
      $ W_12=J_12, quad W_23=J_23. $ <eq:yan-strengthened-normalization>
      Так как $U_12$ перестановочна с $W_12=U_12^2$ и $(U_12 W_23)^2=I$, то
      $
        U_12=mat(a, b; c, d)⊕mat(e, f; g, h), quad mat(a, b; c, d)^2=-I,\
        mat(a, -b; c, -d)^2=mat(e, f; g, h)^2=mat(-e, f; -g, h)^2=I.
      $
      Поэтому в силу леммы @lem:yan-two-by-two-squares
      $
        mat(a, b; c, d)=mat(0, b; -b^(-1), 0), quad e^2±f g=h^2±g f=1,\
        e f±f h=g e±h g=0,
      $
      откуда
      $ f g=0, quad e^2=h^2=1, quad e=±1, quad h=±1. $
      Так как $e+h$ и $e-h$ не могут одновременно равняться нулю, то
      $
        f=g=0, quad e=±1, quad h=±1, quad
        U_12=mat(0, b; -b^(-1), 0)⊕mat(e, 0; 0, h).
      $
      Таким же способом получаем, что
      $ U_23=(e_1)⊕mat(0, b_1; -b_1^(-1), 0)⊕(h_1), quad e_1=±1, quad h_1=±1, $
      #source(246)
      Так как $(U_12 U_23)^3=I$, то $h=h_1$, $e=e_1$. Взяв композицию $cal(A)$ с
      сопряжением при помощи матрицы $op("diag")(b_1^(-1)b^(-1),b_1^(-1),1,1)$,
      <passage:yan-rotation-normalization>
      можно считать, что
      $
        U_12=mat(0, 1; -1, 0)⊕mat(e, 0; 0, h),\
        U_23=(e)⊕mat(0, 1; -1, 0)⊕(h), quad e=±1, quad h=±1.
      $
      <eq:yan-strengthened-rotations>
      Покажем теперь, что
      $ W_34=-W_12. $ <eq:yan-strengthened-complement>
      Так как $W_34$ перестановочно с $W_12$ и $W_23$, то
      $W_34=op("diag")(a,b,c,d)$. Далее, $W_34$ перестановочно с $U_12$. Кроме
      того, из @eq:yan-abstract-conjugation-positive,
      @eq:yan-abstract-conjugation-negative следует
      $U_23 W_34 U_23=W_34$. <passage:yan-sandwich-relations> Ввиду
      @eq:yan-strengthened-rotations
      $W_34=op("diag")(a,a,-a,d)$. Из соотношения $W_34^2=I$ следует, что
      $a=±1$, $d=±1$. Но из утверждения (б) теоремы
      @th:yan-involution-conjugation-strengthened можно заключить, что $d=-a$ и,
      следовательно,
      $ W_34=-a W_12, quad a=±1. $
      Таким образом, для доказательства @eq:yan-strengthened-complement
      достаточно убедиться, что $a=1$. Допустим, что $a=-1$. Тогда $W_34=W_12$
      и, как и прежде, можно доказать, что
      $
        U_34=mat(0, b_2; -b_2^(-1), 0)⊕mat(e_2, 0; 0, h_2), quad e_2=±1, quad
        h_2=±1.
      $
      Так как $I=W_12 W_34=(U_12 U_34)^2$ и $(U_23 U_34)^3=I$, то $b_2=±1$,
      $e_2=e$, $h_2=h$. Из этих соотношений и из @eq:yan-strengthened-rotations
      и @eq:yan-strengthened-normalization получаем
      $
        (U_12 U_23 U_34)^2=op("diag")(b_2,1,b_2,1)
        =cases(W_13 & "если" b_2=-1, I & "если" b_2=1).
      $
      С другой стороны, из @eq:yan-abstract-square-centralizer легко вывести,
      что $(U_12 U_23 U_34)^2=U_13 U_34^2 U_12^2 U_24$. Ввиду этих двух формул
      $ U_13^(±1)U_34^2 U_12^2 U_24=I. $
      Отсюда из @eq:yan-abstract-conjugation-positive,
      @eq:yan-abstract-basic-orders, @eq:yan-abstract-three-index-relations
      имеем $T_13(1)=T_31(-1)$. Если характеристика кольца $R$ равна $3$, то
      $W_13=T_13(6)=I$, и это противоречит утверждению (г) теоремы
      @th:yan-abstract-involution-products. Если характеристика кольца $R$ не
      равна $3$, то, подставляя это равенство в последнее из соотношений
      @eq:yan-abstract-conjugation-negative, получаем $T_13(12)=I$. Но
      #source(247)
      это противоречит соотношению @eq:yan-abstract-additivity, и, таким
      образом, @eq:yan-strengthened-complement доказано. Поэтому можно положить
      $ W_(i j)=J_(i j), quad i!=j, quad 1<=i,j<=4. $
      Начиная с этого момента можно провести доказательство, как в теореме
      @th:yan-elementary-matrix-images, и установить справедливость теоремы
      @th:yan-elementary-images-strengthened для $n=4$. Тем самым теорема
      полностью доказана.
    ]
  ] <cond:yan-linear-abstract-relations>
]

Используя теорему @th:yan-elementary-images-strengthened, можно теперь провести
доказательство, как в теореме @th:yan-main-isomorphism, и усилить ее следующим
образом:

#theorem(base: [@th:yan-main-isomorphism], suffix: "′")[
  Пусть $R$ — коммутативная область целостности характеристики $!=2$, $n>=3$.
  Пусть $cal(A)$ — гомоморфизм группы $SL_n (R)$ в $GL_n (R)$, такой, что
  $cal(A)(B_(i j)(lambda))=I$ равносильно условию $lambda=0$. Тогда $cal(A)$ —
  изоморфизм вида @eq:yan-standard-isomorphism или
  @eq:yan-contragredient-isomorphism.
] <th:yan-main-isomorphism-strengthened>

Как и теорема @th:yan-pid-isomorphism, результат Вань Чже-сяня @bib:yan-Wan1957
и Райнера об автоморфизмах общей линейной группы над областью главных идеалов
(не обязательно коммутативной) характеристики $!=2$, а также упомянутый в
§~@sec:yan-introduction результат Вань Чже-сяня об автоморфизмах линейной группы
над дедекиндовым кольцом характеристики $!=2$ могут быть усилены в духе теоремы
@th:yan-main-isomorphism-strengthened.
