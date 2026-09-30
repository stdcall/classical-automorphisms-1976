#import "main-defs.typ": *
#import "statements.typ": *

=== Растяжения <sec:omeara-dilatations>

Для любого ненулевого элемента $alpha$ из $F$ определим линейное преобразование
$r_alpha$ по правилу
$ r_alpha x = alpha x, quad x in V. $
Ясно, что $r_alpha$ — элемент группы $GL_n (V)$. Произвольное $sigma$ из
$GL_n (V)$ вида $sigma = r_alpha$ для некоторого $alpha$ будем называть
_растяжением_ пространства $V$. Множество растяжений $RL_n (V)$ пространства $V$
является нормальной подгруппой в $GL_n (V)$. Очевидно, $RL_n ≃ dot(F)$.
#idx("растяжение")

#numbered-paragraph[
  Элемент $sigma$ из $GL_n (V)$ тогда и только тогда является растяжением, когда
  $sigma L = L$ для всех прямых $L$ из $V$. В частности,
  $ Ker(P|_(GL_n)) = RL_n, quad Ker(P|_(SL_n)) = SL_n inter RL_n $
  и
  $ PGL_n ≃ GL_n \/ RL_n, quad PSL_n ≃ SL_n \/ (SL_n inter RL_n). $
] <prop:omeara-dilatation-lines>

#source(60)
#proof[
  Зафиксируем $z$ из $dot(V)$. Существует $beta$ из $dot(F)$, для которого
  $sigma z = beta z$. Нужно доказать, что $sigma x = beta x$ для произвольного
  $x$ из $dot(V)$. По предположению $sigma x = alpha x$ для некоторого $alpha$
  из $dot(F)$. Если $x in F z$, то $x$ имеет вид $lambda z$, поэтому
  $ sigma x = sigma(lambda z) = lambda(sigma z) = lambda beta z = beta x. $
  Если $x in.not F z$, то
  $ alpha x + beta z = sigma(x + z) = gamma(x + z), $
  поэтому, в силу независимости $x$ и $z$, $alpha = gamma = beta$, что и
  требовалось доказать.
]

#numbered-paragraph[
  Подгруппа $PSL_n (V)$ нормальна в $PGL_n (V)$ и
  $PGL_n \/ PSL_n ≃ dot(F) \/ dot(F)^n$.
] <prop:omeara-projective-determinant>

#proof[
  Нормальность очевидна. Далее, ядром композиции гомоморфизмов
  $
    GL_n arrow.r.twohead_(P) PGL_n
    arrow.r.twohead_("кан") PGL_n \/ PSL_n
  $
  является группа
  $ G = brace(sigma in GL_n | det sigma in dot(F)^n). $
  С другой стороны, ядром композиции гомоморфизмов
  $
    GL_n arrow.r.twohead_(det) dot(F)
    arrow.r.twohead_("кан") dot(F) \/ dot(F)^n
  $
  является также $G$. Значит,
  $ PGL_n \/ PSL_n ≃ GL_n \/ G ≃ dot(F) \/ dot(F)^n. $
  Предложение доказано.
]
