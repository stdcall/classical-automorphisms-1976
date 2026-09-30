#import "main-defs.typ": *
#import "statements.typ": *

== Вид элемента $cal(A)(B_(i j)(1))$ <sec:yan-elementary-images>

Пусть $cal(A)$ — изоморфизм группы $SL_n (R)$ в $GL_n (R)$. В этом параграфе мы
наложим дополнительные ограничения на $R$ и определим вид элемента
$cal(A)(B_(i j)(1))$. В дополнение к теореме из §~@sec:yan-involutions нам
понадобятся некоторые соотношения между $cal(A)(B_(i j)(1))$. Заметим, что
полученные здесь результаты можно несколько усилить. Мы вернемся к этому вопросу
в конце статьи.

Начнем со следующего простого замечания:

#lemma[
  Предположим, что $R$ — кольцо без делителей нуля с единицей и характеристики
  $!=2$. Пусть $a,b,c,d in R$. Если
  $ mat(a, b; c, d)^2=-I, quad mat(a, -b; c, -d)^2=I, $
  то $a=d=0$, $c=-b^(-1)$.
] <lem:yan-two-by-two-squares>

#proof[
  Из предположений следует, что $a^2+b c=-1$, $a^2-b c=1$, $d^2+c b=-1$,
  $d^2-c b=1$ и, значит, $2a^2=2d^2=0$. Так как $R$ имеет характеристику $!=2$,
  то $a=d=0$ и $b c=c b=-1$.
]

В этом параграфе предполагается, что $R$ удовлетворяет тем же условиям, что и в
§~@sec:yan-involutions. Пусть $K(R)$ — тело частных кольца $R$.

#theorem[
  Если $n >= 3$ и $cal(A)$ — изоморфизм группы $SL_n (R)$ в $GL_n (R)$, то
  существует матрица $P in GL_n (K(R))$, такая, что
  $ P cal(A)(B_(i j)(1))P^(-1)=B_(i j)(1), quad i != j, quad i,j=1,...,n, $
  или
  $ P cal(A)(B_(i j)(1))P^(-1)=B_(j i)(-1), quad i != j, quad i,j=1,...,n. $
] <th:yan-elementary-matrix-images>

#proof[
  #condition-series[
    #condition[
      Ввиду теоремы @th:yan-involution-conjugation можно считать, что
      $
        cal(A)(J_(i,i+1))=J_(i,i+1), quad i=1,2,...,n-1.
      $ <eq:yan-adjacent-involution-images>
      #source(234)
      Теперь рассмотрим $cal(A)(S_(i,i+1))$, где
      $
        S_(i,i+1)=I^((i-1)) ⊕ mat(0, 1; -1, 0) ⊕ I^((n-i-1)), quad i=1,...,n-1.
      $
      Если $n=3$ или $>=5$, то в силу перестановочности $cal(A)(S_12)$ с
      $cal(A)(J_12)=J_12$ и $cal(A)(J_(i,i+1))$, $3 <= i <= n-1$, после простых
      вычислений получаем
      $
        cal(A)(S_12)=mat(a^((1)), b^((1)); c^((1)), d^((1))) ⊕ diag(
          a_3^((1)),
          ..., a_n^((1))
        ).
      $
      Если $n=4$, то ввиду перестановочности $cal(A)(S_12)$ с $cal(A)(J_12)$ и
      соотношений
      $
        (cal(A)(S_12))^2=cal(A)(J_12), quad (cal(A)(S_12)cal(A)(J_23))^2=I
      $ <eq:yan-adjacent-rotation-relations>
      снова получаем тот же результат, что и выше. Из
      @eq:yan-adjacent-rotation-relations видно, что матрица
      $ mat(a^((1)), b^((1)); c^((1)), d^((1))) $
      удовлетворяет условию леммы @lem:yan-two-by-two-squares и
      $(a_i^((1)))^2=1$, $3 <= i <= n$, следовательно,
      $
        cal(A)(S_12)=mat(0, b^((1)); -(b^((1)))^(-1), 0) ⊕ diag(
          a_3^((1)), ...,
          a_n^((1))
        ), quad a_i^((1))=plus.minus 1.
      $
      Таким же способом получаем, что
      $
        cal(A)(S_(i,i+1))=diag(a_1^((i)), ..., a_(i-1)^((i)))
        ⊕ mat(0, b^((i)); -(b^((i)))^(-1), 0)
        ⊕ diag(a_(i+2)^((i)), ..., a_n^((i))), \
        1 <= i <= n-1, quad a_j^((i))=plus.minus 1, quad j != i,i+1,
        quad i=1,...,n-1.
      $ <passage:yan-rotation-block-diagonal>
      Беря композицию изоморфизма $cal(A)$ с сопряжением при помощи матрицы
      $
        P=diag(
          (b^((n-1)))^(-1) dots (b^((1)))^(-1),
          (b^((n-1)))^(-1) dots (b^((2)))^(-1),
          ..., (b^((n-1)))^(-1), 1
        ),
      $
      можем считать, что $b^((i))=1$. Так как $cal(A)(S_(i,i+1))$ перестановочно
      с $cal(A)(S_(j,j+1))$, $1 <= j <= i-2$, $i+2 <= j <= n-1$, то
      $a_1^((i))=dots=a_(i-1)^((i))$, $a_(i+2)^((i))=dots=a_n^((i))$
      <passage:yan-rotation-tail-equality>. Следовательно, можно считать, что
      $
        cal(A)(S_(i,i+1))=(a_i I)^((i-1)) ⊕ mat(0, 1; -1, 0)
        ⊕ (a'_i I)^((n-i-1)), \
        1 <= i <= n-1, quad a'_i=plus.minus 1, quad a_i=plus.minus 1.
      $
      #source(235)
      Из этих соотношений и равенства $(cal(A)(S_(i-1,i))cal(A)(S_(i,i+1)))^3=I$
      получаем $a_(i-1)=a_i$, $a'_(i-1)=a_i$, $2 <= i <= n-1$, откуда
      $
        cal(A)(S_(i,i+1))=(e I)^((i-1)) ⊕ mat(0, 1; -1, 0)
        ⊕ (e I)^((n-i-1)), \
        i=1,...,n-1, quad e=plus.minus 1.
      $ <eq:yan-adjacent-rotation-images>
      С этого момента будем рассматривать @eq:yan-adjacent-rotation-images как
      предположение и определим $cal(A)(B_12(1))$ в двух случаях: когда $n=3$
      или $>=5$ и когда $n=4$.
    ] <cond:yan-normalize-rotations>

    #condition[
      $n=3$ или $>=5$. Так как $cal(A)(B_12(1))$ перестановочно с $cal(A)(J_12)$
      и $cal(A)(J_(i,i+1))$, $3 <= i <= n-1$, то
      $ cal(A)(B_12(1))=mat(a, b; c, d) ⊕ diag(a_3, ..., a_n). $
      Так как $cal(A)(B_12(1))$ перестановочно с $cal(A)(S_(i,i+1))$,
      $3 <= i <= n-1$, то $a_3=dots=a_n=a'$. Из соотношения
      $(cal(A)(B_12(1))cal(A)(J_23))^2=I$ следует, что $a_i^2=1$ и,
      $ mat(a, -b; c, -d)^2=I, $ <passage:yan-elementary-involution-square>
      и, значит,
      $
        cal(A)(B_12(1))=mat(a, b; c, d) ⊕ diag(a', ..., a'),
        quad a'=plus.minus 1, \
        a^2-b c=1, quad d^2-c b=1, quad a b-b d=c a-d c=0.
      $ <eq:yan-elementary-block-relations>
      Но $cal(A)(B_13(1))=cal(A)(S_23^(-1))cal(A)(B_12(1))cal(A)(S_23)$ и
      матрица $cal(A)(B_12(1))$ перестановочна с $cal(A)(B_13(1))$. Отсюда
      $
        mat(a^2, a b, e a' b; c a', a' d, 0; e c a, e c b, a' d)
        =mat(a^2, a' b, e a b; c a, a' d, e c b; e c a', 0, a' d)
      $ <eq:yan-three-by-three-commutation>
      и $b c=0$, $(a-a')b=c(a-a')=0$. Но $(cal(A)(B_12(1)))^2 != I$, поэтому
      ввиду @eq:yan-elementary-block-relations $b$ и $c$ не могут одновременно
      равняться нулю. Следовательно, $a=a'$ и либо $b=0$, $c != 0$, либо $c=0$,
      $b != 0$. Снова ввиду @eq:yan-elementary-block-relations $d=a'$, поэтому
      $
        cal(A)(B_12(1))=mat(a', b; 0, a') ⊕ (a'I)^((n-2)) quad "или" mat(
          a', 0;
          c, a'
        ) ⊕ (a'I)^((n-2)).
      $
      Используя соотношение $(cal(A)(S_12)cal(A)(B_12(1)))^3=I$,
      @eq:yan-adjacent-rotation-images и последние формулы, получаем $a'=e$,
      $b=1$, $c=-1$. Это
      #source(236)
      означает, что
      $
        cal(A)(B_12(1))=(e I)^((n))+E_12 quad "или" (e I)^((n))-E_21, quad
        e=plus.minus 1.
      $ <eq:yan-elementary-signed-image>
      Наконец, докажем, что $e=1$. Из соотношений
      $ cal(A)(S_23^(-1))cal(A)(B_12(1))cal(A)(S_23)=cal(A)(B_13(1)), $
      @eq:yan-adjacent-rotation-images и @eq:yan-elementary-signed-image имеем
      $
        cal(A)(B_13(1))=(e I)^((n))+e E_13 quad "или" (e I)^((n))-e E_31.
      $ <eq:yan-elementary-thirteen-image>
      Так как $cal(A)(S_12^(-1))cal(A)(S_23^(-1))cal(A)(B_12(1))cal(A)(S_23)
      cal(A)(S_12)=cal(A)(B_23(1))$, то в силу @eq:yan-adjacent-rotation-images
      и
      @eq:yan-elementary-signed-image
      $
        cal(A)(B_23(1))=(e I)^((n))+E_23 quad "или" (e I)^((n))-E_32,
      $ <eq:yan-elementary-twentythree-image>
      Используя @eq:yan-adjacent-rotation-images,
      @eq:yan-elementary-thirteen-image, @eq:yan-elementary-twentythree-image и
      соотношение
      $
        cal(A)(B_12(-1))cal(A)(B_23(-1))cal(A)(B_12(1))
        cal(A)(B_23(1))=cal(A)(B_13(1)),
      $
      непосредственно заключаем, что
      $ e=1. $ <eq:yan-elementary-sign>
      Из @eq:yan-adjacent-rotation-images, @eq:yan-elementary-signed-image,
      @eq:yan-elementary-sign и соотношений
      $
        cal(A)(S_12^(-1))cal(A)(B_12(-1))cal(A)(S_12)=cal(A)(B_21(1)), \
        cal(A)(S_(i j)^(-1))cal(A)(B_(k i)(1))cal(A)(S_(i j))=cal(A)(B_(k
          j)(1)), \
        cal(A)(S_(i j)^(-1))cal(A)(B_(i k)(1))cal(A)(S_(i j))=cal(A)(B_(j k)(1))
      $
      следует, что
      $
        cal(A)(B_(1i)(1))=B_(1i)(1), quad cal(A)(B_(i 1)(1))=B_(i 1)(1), quad
        i=2,...,n,
      $
      или
      $
        cal(A)(B_(1i)(1))=B_(i 1)(-1), quad cal(A)(B_(i 1)(1))=B_(1i)(-1), quad
        i=2,...,n.
      $
      Далее, так как
      $cal(A)(B_(i j)(-1))cal(A)(B_(j k)(-1))cal(A)(B_(i j)(1))cal(A)(B_(j
        k)(1))=cal(A)(B_(i k)(1))$
      при попарно различных $i,j,k$, то $cal(A)(B_(i j)(1))=B_(i j)(1)$,
      $i != j$, $i,j=1,...,n$, или $cal(A)(B_(i j)(1))=B_(j i)(-1)$, $i != j$,
      $i,j=1,...,n$.
    ] <cond:yan-elementary-nonthree-block>

    #condition[
      $n=4$. Так как $cal(A)(B_12(1))$ и $cal(A)(J_12)$ перестановочны, то
      $ cal(A)(B_12(1))=mat(a, b; c, d) ⊕ mat(a_1, b_1; c_1, d_1). $
      Далее, так как $cal(A)(B_12(1))$ и $cal(A)(S_34)$ перестановочны, то
      $a_1=d_1$, $c_1=-b_1$. Так как $(cal(A)(B_12(1))cal(A)(J_23))^2=I$, то
      $ mat(-a_1, b_1; b_1, a_1)^2=I, quad mat(a, -b; c, -d)^2=I, $
      #source(237)
      и, следовательно, $a_1^2+b_1^2=1$, $b_1 a_1=a_1 b_1$. Из
      @eq:yan-adjacent-rotation-images после вычислений с применением
      результатов, найденных выше, получаем
      $
        cal(A)(B_13(1))=cal(A)(S_23^(-1))cal(A)(B_12(1))cal(A)(S_23)=mat(
          a, 0,
          e b, 0; 0, a_1, 0, -e b_1; e c, 0, d, 0; 0, e b_1, 0, a_1
        ).
      $
      Так как $cal(A)(B_12(1))$ и $cal(A)(B_13(1))$ перестановочны, то
      $
        & mat(
            delim: "[", a^2, b a_1, e a b, -e b b_1;
            c a, d a_1, e c b, -e d b_1;
            e a_1 c, e b_1^2, a_1 d, a_1 b_1;
            -e b_1 c, e a_1 b_1, -b_1 d, a_1^2
          ) \
        & =mat(
            delim: "[", a^2, a b, e b a_1, e b b_1;
            a_1 c, a_1 d, e b_1^2, -e b_1 a_1;
            e c a, e c b, d a_1, d b_1;
            e b_1 c, e b_1 d, -a_1 b_1, a_1^2
          ).
      $ <eq:yan-four-by-four-commutation>
      Таким образом, $2e b_1 c=2e b b_1=0$. Если $b=c=0$, то $a^2=d^2=1$, и
      ввиду @eq:yan-four-by-four-commutation $e b_1^2=e c b=0$, откуда $b_1=0$.
      Следовательно, $cal(A)(B_12(1))=diag(a, d, a_1, a_1)$ и
      $(cal(A)(B_12(1)))^2=I$. Но это невозможно.
      <passage:yan-four-dimensional-diagonal>
      Поэтому либо $b != 0$, либо $c != 0$. Так как характеристика кольца $R$
      отлична от $2$, то $b_1=0$, откуда $a_1^2=1$, $e c b=e b_1^2=0$. Таким
      образом, $a_1=plus.minus 1$ и либо $b=0$, либо
      $c=0$. <passage:yan-four-dimensional-scalar-square>
      Из @eq:yan-four-by-four-commutation получаем $e c a=e a_1 c$,
      $e a b=e b a_1$, откуда $a=a_1$. Так как
      $ mat(a, -b; c, -d)^2=I, $
      то $d=a$. Учитывая все сказанное, имеем
      $
        cal(A)(B_12(1))=(a_1 I)^((4))+b E_12 quad "или" (a_1 I)^((4))+c E_21,
        quad a_1=plus.minus 1.
      $
      Из @eq:yan-adjacent-rotation-images и соотношения
      $(cal(A)(S_12)cal(A)(B_12(1)))^3=I$ немедленно получаем
      $ a_1=e, quad b=1, quad c=-1. $
      Далее точно так же, как и в случае @cond:yan-elementary-nonthree-block,
      устанавливается справедливость теоремы для $n=4$. Теорема доказана.
    ] <cond:yan-elementary-four-dimensional>
  ]
]
