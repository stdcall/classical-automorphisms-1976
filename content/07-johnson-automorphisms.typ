#import "main-defs.typ": *
#import "statements.typ": *

== Автоморфизмы группы $Delta$ <sec:johnson-automorphisms>

В этом последнем параграфе мы покажем, что произвольный автоморфизм $Lambda$
группы $Delta$ имеет вид $Lambda(sigma) = chi(sigma) dot Phi_g (sigma)$ для
некоторых $chi$ и $g$.

#source(26)
Мы уже убедились, что $Lambda$ переставляет множества $S_x$, т.~е.
$Lambda S_x = S_(x')$, причем $x'$ изотропен в том и только том случае, когда
$x$ изотропен. Так как $Lambda^(-1)$ — тоже автоморфизм, то эта перестановка
взаимно однозначна. Полагая $L = E x$ и $L' = E x'$, видим, что имеется взаимно
однозначное соответствие между прямыми из $V$, потому что $S_x = S_y$ тогда и
только тогда, когда $x in E y$.

#claim[
  Соответствие между прямыми, определенное автоморфизмом $Lambda$, сохраняет
  ортогональность, т.~е. $q(L_1, L_2) = 0$ влечет за собой $q(L'_1, L'_2) = 0$.
] <prop:johnson-line-orthogonality>

#proof[
  Обозначим $L_i = E x_i$ и $L'_i = E x'_i$, $i = 1, 2$. Так как
  $q(x_1, x_2) = 0$, то $S_(x_1) subset.eq C(S_(x_2))$ и либо $x_1 in E x_2$,
  либо $S_(x_1) != S_(x_2)$. Если $x_1 in E x_2$, то $S_(x_1) = S_(x_2)$ и
  $Q(x_1) = Q(x_2) = 0$. Поэтому $S_(x'_1) = S_(x'_2)$ и
  $Q(x'_1) = Q(x'_2) = 0$. Если $x_1 in.not E x_2$, то
  $S_(x'_1) subset.eq C(S_(x'_2))$ и $S_(x'_1) != S_(x'_2)$. Отсюда
  $q(L'_1, L'_2) = 0$, что и требовалось доказать.
]

Так как $Lambda^(-1) compose Lambda = "id"$, то
$q(L_1, L_2) = 0 arrow.l.r.double q(L'_1, L'_2) = 0$.

#claim[
  Если $L_i$ — прямые из $V$ и $L'_i$ — соответствующие им прямые,
  $i = 1, 2, 3$, то из $L_1 subset.eq L_2 + L_3$ следует
  $L'_1 subset.eq L'_2 + L'_3$.
] <prop:johnson-line-incidence>

#proof[
  Пусть $W = L_2 + L_3$, $W' = L'_2 + L'_3$. Тогда
  $
    L subset.eq W^perp & arrow.l.r.double q(L, L_i) = 0, quad i = 2, 3 \
                       & arrow.l.r.double q(L', L'_i) = 0, quad i = 2, 3
                         arrow.l.r.double L' subset.eq (W')^perp.
  $
  Возьмем прямую $L' subset.eq (W')^perp$. Тогда $L subset.eq W^perp$ и
  $q(L, L_1) = 0$. Значит, $q(L', L'_1) = 0$ и
  $L'_1 subset.eq (W')^(perp perp) = W'$, что и требовалось доказать.
]

По основной теореме проективной геометрии это соответствие прямых индуцировано
полулинейным изоморфизмом $g$ пространства $V$ на себя. Очевидно, $g$ сохраняет
ортогональность, поэтому $Phi_g: Delta arrow U_n (V)$ — изоморфизм. Соответствие
прямых, индуцированное автоморфизмом $Phi_g$, совпадает с тем, которое
индуцировано автоморфизмом $Lambda$, т.~е. если $sigma in S_x$, то
$Lambda sigma in overline(S)_(g x)$, где
$
  overline(S)_(g x) = {rho in U_n (V) |
    rho|_((E g x)^perp) in R(E g x^perp)}.
$
Поэтому $Phi_g^(-1) compose Lambda: Delta arrow U_n (V)$ — изоморфизм,
индуцирующий тождественное соответствие прямых.

#claim[
  $psi = Phi_g^(-1) compose Lambda$ — гомотетия группы $Delta$ в группу
  $U_n (V)$.
] <prop:johnson-residual-homothety>

#source(27)
#proof[
  Мы знаем, что $psi(S_x) subset.eq overline(S)_x$ для всех $x in V$. Пусть
  $Sigma$ — произвольный элемент из $Delta$ и $sigma in S_x - Z(Delta)$. Тогда
  $
    psi(Sigma sigma Sigma^(-1)) = psi(Sigma) psi(sigma) psi(Sigma)^(-1)
    in overline(S)_(psi(Sigma) x)
  $
  и
  $ psi(Sigma sigma Sigma^(-1)) in overline(S)_(Sigma x). $
  Отсюда $overline(S)_(psi(Sigma) x) = overline(S)_(Sigma x)$ и
  $psi(Sigma) x in E Sigma x$ для всех $x in V$, $Sigma in Delta$. Поэтому
  $psi(Sigma) Sigma^(-1) (x) in E x$ для всех $x$, $Sigma$ и
  $psi(Sigma) Sigma^(-1) in Z_n (V)$ для всех $Sigma in Delta$. Положим
  $chi(Sigma) = psi(Sigma) Sigma^(-1)$. Тогда
  $psi(Sigma) = chi(Sigma) dot Sigma$, и так как $psi$ — изоморфизм, то
  отображение $chi: Delta arrow Z_n (V)$ должно быть гомоморфизмом. Утверждение
  (@prop:johnson-residual-homothety) доказано.
]

Теперь легко получается наш основной результат.

#claim(family: "th")[
  *Теорема.* Пусть $V$ — невырожденное эрмитово пространство над бесконечным
  полем $E$ размерности $n >= 3$. Пусть $Delta$ — группа, заключенная между
  $U_n^+ (V)$ и $U_n (V)$, т.~е. $U_n^+ (V) subset.eq Delta subset.eq U_n (V)$.
  Если $Lambda$ — автоморфизм группы $Delta$, то
  $
    Lambda(sigma) = Phi_g compose P_chi (sigma)
    = chi(sigma)^mu Phi_g (sigma), quad sigma in Delta,
  $
  <passage:johnson-main-decomposition>
  где изоморфизмы $P_chi$ и $Phi_g$ определены однозначно.
] <th:johnson-main-automorphisms>

#proof[
  По предыдущему для полулинейного отображения $g$, индуцированного
  автоморфизмом $Lambda$, имеем равенство
  $ Phi_g^(-1) compose Lambda = P_chi, $
  где $P_chi$ — гомотетия. Применяя $Phi_g$ к обеим частям, получим
  $
    Lambda(sigma) = Phi_g compose P_chi (sigma)
    = chi(sigma)^mu dot Phi_g (sigma),
  $
  что и требовалось доказать.
]

#claim(family: "cor")[
  *Следствие.* Если $Delta = U_n (V)$ или $Delta = U_n^+ (V)$, то $P_chi$ и
  $Phi_g$ — автоморфизмы группы $Delta$.
] <cor:johnson-full-group-factors>

#proof[
  Если $sigma in U_n^+ (V)$, то $det(Phi_g (sigma)) = (det sigma)^mu = 1$.
  Значит, $Phi_g (sigma) in U_n^+ (V)$, и, следовательно, $Phi_g$ и
  $P_chi = Phi_g^(-1) compose Lambda$ — автоморфизмы группы $Delta$.
]
