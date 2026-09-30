#import "@preview/cetz:0.3.4"

#let label(position, body, ..args) = cetz.draw.content(
  position,
  box(fill: white, inset: 2pt, body),
  ..args,
)

#let project(v) = (
  -0.6 * v.at(0) + 1.2 * v.at(1),
  -0.85 * v.at(0) - 0.3 * v.at(1) + 1.2 * v.at(2),
)

#let plane-outline(scale: 1.1) = range(0, 73).map(i => {
  let angle = i * 5deg
  project((scale * calc.cos(angle), scale * calc.sin(angle), 0))
})

// The original sketches encode R ⊆ P (transvection), V = R ⊕ P
// (dilatation), and the motion x ↦ y along the direction y − x ∈ H.
#let transvection-dilatation() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  // P=ker(e3*) is drawn as the projected unit-circle in its basis.
  line(..plane-outline(), close: true)
  line((0, 0), project((1, 0, 0)), mark: (end: ">"))
  label((-0.55, -0.05), $R$)
  label((0.95, -0.55), $P$)
  label((2.15, 0), [и])
  line(..plane-outline().map(p => (4 + p.at(0), p.at(1))), close: true)
  let residual = project((0, 0, 1))
  line((4, 0), (4 + residual.at(0), residual.at(1)), mark: (end: ">"))
  label((4.25, 1.2), $R$)
  label((3.75, -0.8), $P$)
})

// V=Q^3, H=ker(e3*), R=Qe1, tau(v)=v+e3*(v)e1.
// The oblique projection is fixed on the basis; all vector endpoints below
// are calculated from the model, including the translated segment x -> y.
#let transvection-action() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  let x = (0, 0, 1)
  let rho-x = x.at(2)
  let y = (x.at(0) + rho-x, x.at(1), x.at(2))
  let difference = (y.at(0) - x.at(0), y.at(1) - x.at(1), y.at(2) - x.at(2))
  assert(difference.at(2) == 0, message: "y-x must belong to H")
  let px = project(x)
  let py = project(y)
  let pdifference = project(difference)
  // The outer V outline is a conventional enclosing boundary,
  // not a projected sphere.
  group({
    rotate(-30deg)
    circle((0, 0), radius: (1.45, 2))
  })
  // H=ker(e3*); its outline comes from the same basis projection.
  line(..plane-outline(), close: true)
  label((0.65, 1.75), $V$)
  label((0.1, -1.35), $H$)
  line((0, 0), px, mark: (end: ">"))
  line((0, 0), py, mark: (end: ">"))
  line((0, 0), pdifference, mark: (end: ">"))
  line(px, py, mark: (end: ">"), stroke: (dash: "dashed"))
  label((px.at(0) + 0.15, px.at(1)), $x$)
  label((py.at(0) - 0.2, py.at(1) + 0.1), $y$)
  label((pdifference.at(0), pdifference.at(1) - 0.25), $y - x$)
})

#let large-dilatation() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  group({
    rotate(-20deg)
    circle((-0.9, 0), radius: (0.8, 1.1))
  })
  circle((0.65, 0), radius: (0.8, 0.45))
  label((-1.3, 1.15), $U$)
  label((0.85, 0.65), $W$)
  label((-0.9, 0), $1_U$)
  label((0.65, 0), $alpha 1_W$)
  label((0, -1.55), $(alpha != 1, W != 0).$)
})

#let generation-nested() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  // Q^6: N(e5)=e1, N(e6)=e2, sigma=I+N.
  // R=<e1,e2> subset P=<e1,e2,e3,e4> subset H=<e1,e2,e3,e4,e6>.
  // b=e5 is outside H; these outlines are projected circles in R,
  // with larger radii illustrating the containing subspaces P and H.
  let proj(v) = (
    -0.55 * v.at(0) + 0.7 * v.at(1),
    -0.65 * v.at(0) - 0.1 * v.at(1) + 1.45 * v.at(4),
  )
  let outline(scale) = range(0, 73).map(i => {
    let a = i * 5deg
    proj((scale * calc.cos(a), scale * calc.sin(a), 0, 0, 0, 0))
  })
  line(..outline(1.7), close: true)
  line(..outline(1.4), close: true)
  line(..outline(1.1), close: true)
  let b = (0, 0, 0, 0, 1, 0)
  let sb = (1, 0, 0, 0, 1, 0)
  let delta = (1, 0, 0, 0, 0, 0)
  line((0, 0), proj(sb), mark: (end: ">"))
  line((0, 0), proj(b), mark: (end: ">"))
  line((0, 0), proj(delta), mark: (end: ">"))
  line(proj(b), proj(sb), stroke: (dash: "dashed"))
  label((-0.7, 0.95), $sigma b$)
  label((0.15, 1.5), $b$)
  label((-0.55, -1.25), $sigma b - b$)
  label((-1.5, -0.8), $H$)
  label((1.2, -0.95), $n - 1$)
  label((-1.25, -0.5), $P$)
  label((1.1, -0.55), $n - r$, anchor: "west")
  label((-0.8, -0.2), $R$)
  label((0.7, -0.4), $r$)
})

#let generation-intersecting() = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(stroke: 0.8pt)
  // sigma=diag(1,2,3), P=<e1>, R=<e2,e3>,
  // b=e2+e3, delta=e2+2e3, H=<e1,delta>; b is outside H.
  let project-intersecting(v) = (
    0.9 * v.at(0) + 2.3 * v.at(1) - 1.6 * v.at(2),
    -0.6 * v.at(0) + 2.2 * v.at(1) - 1.4 * v.at(2),
  )
  // Outlines are projected basis circles; P is one-dimensional, so a line.
  let h-outline = range(0, 73).map(i => {
    let a = i * 5deg
    let c = 1.3 * calc.cos(a)
    let s = 1.3 * calc.sin(a)
    project-intersecting((c, s, 2 * s))
  })
  let r-outline = range(0, 73).map(i => {
    let a = i * 5deg
    let c = 1.6 * calc.cos(a)
    let s = 1.6 * calc.sin(a)
    project-intersecting((0, c + s, c + 2 * s))
  })
  line(..h-outline, close: true)
  line(..r-outline, close: true)
  line(project-intersecting((-0.8, 0, 0)), project-intersecting((0.8, 0, 0)))
  let b = (0, 1, 1)
  let sb = (0, 2, 3)
  let delta = (0, 1, 2)
  line((0, 0), project-intersecting(sb), mark: (end: ">"))
  line((0, 0), project-intersecting(b), mark: (end: ">"))
  line((0, 0), project-intersecting(delta), mark: (end: ">"))
  line(
    project-intersecting(b),
    project-intersecting(sb),
    stroke: (dash: "dashed"),
  )
  label((-0.5, 0.35), $sigma b$)
  label((0.85, 0.8), $b$)
  label((-1.1, -0.85), $sigma b - b$)
  label((-1.65, -0.6), $H$)
  label((0.6, -0.6), $P$)
  label((1.8, 0.5), $R$)
})
