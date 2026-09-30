#import "main-defs.typ": *
#import "statements.typ": *

=== Изоморфизмы $Phi_g$ <sec:omeara-geometric-isomorphisms>

Теперь мы определим групповые изоморфизмы $Phi_g$ — сначала для коллинеации
$g: V arrow.r.twohead.tail V_1$ пространства $V$ на пространство $V_1$, а затем
для проективной коллинеации $g: P(V) arrow.r.twohead.tail P(V_1)$ пространства
$V$ на пространство $V_1$.

Пусть сначала задана коллинеация $g: V arrow.r.twohead.tail V_1$ пространства
$V$ на пространство $V_1$ и $mu: F arrow.r.twohead.tail F_1$ — связанный с ней
изоморфизм полей. В частности, $n = n_1$. Ясно, что отображение $Phi_g$,
определенное равенством
$ Phi_g k = g k g^(-1) "для всех" k in GammaL_n (V), $
является изоморфизмом групп
$ Phi_g: GammaL_n (V) arrow.r.twohead.tail GammaL_(n_1) (V_1). $
Для композиции и обращения справедливы равенства
$ Phi_(g_1 g) = Phi_(g_1) Phi_g, quad Phi_g^(-1) = Phi_(g^(-1)). $
Далее, $Phi_g$ индуцирует изоморфизмы
$
  Phi_g: GL_n (V) arrow.r.twohead.tail GL_(n_1) (V_1), \
  Phi_g: SL_n (V) arrow.r.twohead.tail SL_(n_1) (V_1), \
  Phi_g: RL_n (V) arrow.r.twohead.tail RL_(n_1) (V_1).
$
Если $sigma in GL_n (V)$, то
$ det(Phi_g sigma) = (det sigma)^mu, $
#source(99)вычетным и неподвижным пространствами преобразования $Phi_g sigma$
являются $g R$ и $g P$ соответственно. В частности,
$ upright("res") Phi_g sigma = upright("res") sigma. $
Если $H$ — гиперплоскость, $L$ — прямая и $L subset.eq H$, то $g L$ — прямая,
лежащая в гиперплоскости $g H$ пространства $V_1$. Изоморфизм $Phi_g$ отображает
множество трансвекций с пространствами $L subset.eq H$ на множество трансвекций
с пространствами $g L subset.eq g H$. Если $sigma$ — трансвекция вида
$sigma = tau_(a,rho)$, то
$ Phi_g tau_(a,rho) = tau_(g a,mu rho g^(-1)). $

Пусть теперь задана проективная коллинеация
$g: P(V) arrow.r.twohead.tail P(V_1)$ пространства $V$ на пространство $V_1$.
Имеем снова $n = n_1$. Полагая
$ Phi_g k = g k g^(-1) "для всех" k in PGammaL_n (V), $
получим изоморфизм групп
$ Phi_g: PGammaL_n (V) arrow.r.twohead.tail PGammaL_(n_1) (V_1). $
Для композиции и обращения справедливы равенства
$ Phi_(g_1 g) = Phi_(g_1) Phi_g, quad Phi_g^(-1) = Phi_(g^(-1)). $
Так как $g$ — проективная коллинеация, то она имеет вид $g = overline(h)$ для
некоторой коллинеации $h: V arrow.r.twohead.tail V_1$. Легко убедиться, что
$
  Phi_g overline(j) = Phi_(overline(h)) overline(j) = overline(Phi_h j)
  "для всех" j in GammaL_n (V).
$
Следовательно, $Phi_g$ индуцирует изоморфизмы
$
  Phi_g: PGL_n (V) arrow.r.twohead.tail PGL_(n_1) (V_1), \
  Phi_g: PSL_n (V) arrow.r.twohead.tail PSL_(n_1) (V_1).
$
Кроме того, $Phi_g$ отображает множество проективных трансвекций с
пространствами $L subset.eq H$ на множество проективных трансвекций с
пространствами $g L subset.eq g H$.

#numbered-paragraph[
  Пусть $n = n_1 >= 2$. Для любых коллинеаций $g_1$, $g_2$ пространства $V$ на
  пространство $V_1$ следующие утверждения равносильны:
  + Ограничения $Phi_(g_1)$ и $Phi_(g_2)$ на $GL_n (V)$ равны,
  + $overline(g)_1 = overline(g)_2$,
  + $g_1 = g_2 r$ для некоторого $r$ из $RL_n (V)$,
  + $g_1 = r_1 g_2$ для некоторого $r_1$ из $RL_(n_1) (V_1)$.
] <prop:omeara-geometric-isomorphism-equality>
