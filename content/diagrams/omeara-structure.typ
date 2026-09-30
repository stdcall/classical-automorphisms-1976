#import "@preview/cetz:0.3.4"
#import "../main-defs.typ": *

// Inclusion lattice; labels on edges give the quotient groups in the source.
#let structure-diagrams() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  let nodes = (
    xi: (0, 4.7),
    gamma: (0, 3.7),
    gl: (0, 2.7),
    sl: (-1.4, 1.5),
    rl: (1.4, 0.7),
    centre: (0.6, -0.5),
    one: (0.6, -1.7),
    pxi: (4, 2.7),
    pgamma: (4, 1.5),
    pgl: (4, 0.3),
    psl: (4, -0.9),
    pone: (4, -2.1),
  )
  for (a, b) in (
    ("xi", "gamma"),
    ("gamma", "gl"),
    ("gl", "sl"),
    ("gl", "rl"),
    ("sl", "centre"),
    ("rl", "centre"),
    ("centre", "one"),
    ("pxi", "pgamma"),
    ("pgamma", "pgl"),
    ("pgl", "psl"),
    ("psl", "pone"),
  ) {
    line(nodes.at(a), nodes.at(b))
  }
  for (key, body) in (
    ("xi", $XiL_n$),
    ("gamma", $GammaL_n$),
    ("gl", $GL_n$),
    ("sl", $SL_n$),
    ("rl", $RL_n$),
    ("centre", $SL_n inter RL_n$),
    ("one", $1_V$),
    ("pxi", $PXiL_n$),
    ("pgamma", $PGammaL_n$),
    ("pgl", $PGL_n$),
    ("psl", $PSL_n$),
    ("pone", $1$),
  ) { content(nodes.at(key), box(fill: white, inset: 2pt, body)) }
  content((0.65, 3.2), $Aut F$)
  content((-1.15, 2.2), $dot(F)$)
  content((-1.25, 0.2), [простая])
  content((1.55, -1.1), $root(n, 1) "в" dot(F)$)
  content((5.1, 2.1), $1 "при" n >= 3$)
  content((4.85, 0.9), $Aut F$)
  content((4.95, -0.3), $dot(F) \/ dot(F)^n$)
  content((4.85, -1.5), [простая])
})
