#import "main-defs.typ": *
#import "statements.typ": *

=== Центры <sec:omeara-centres>

Заметим, что при $n >= 2$ группа $PSL_n$ и, следовательно, $SL_n$ неабелева —
достаточно взять подходящие проективные трансвекции $sigma_1$ и $sigma_2$ с
различными вычетными прямыми и применить
@prop:omeara-projective-transvection-commutation.

#numbered-paragraph[
  + Централизатор подгруппы $PSL_n$ в $PGL_n$ тривиален.
  + Централизатором подгруппы $SL_n$ в $GL_n$ является $RL_n$.
  + Группы $PGL_n$ и $PSL_n$ не имеют центра.
  + $upright("cen") GL_n = RL_n$, $upright("cen") SL_n = SL_n inter RL_n$.
] <prop:omeara-centres>

#proof[
  Допустим, что некоторое $sigma$ из $PGL_n$ перестановочно со всеми элементами
  из $PSL_n$. Докажем, что $sigma = 1$. Пусть $L$ — произвольная прямая
  пространства $V$. Возьмем неединичную проективную трансвекцию $tau$ с вычетной
  прямой $L$. Согласно @sec:omeara-projective-transvections, вычетной прямой
  проективной трансвекции $sigma tau sigma^(-1)$ является $sigma L$. Но
  $sigma tau sigma^(-1) = tau$. Следовательно, $sigma L = L$ для всех прямых $L$
  из $V$. Отсюда ввиду @prop:omeara-projectivity-preservation $sigma = 1$. Тем
  самым доказано 1). Теперь 2) и 3) следуют из 1), а 4) следует из 2).
]
