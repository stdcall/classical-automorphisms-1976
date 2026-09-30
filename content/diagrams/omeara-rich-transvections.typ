#import "@preview/cetz:0.5.2": canvas, draw

#let label(position, body, ..args) = draw.content(
  position,
  box(fill: white, inset: 2pt, body),
  ..args,
)

// All vertices are images under a single linear map of basis vectors.
#let project(v, basis) = (
  v.zip(basis).map(((a, b)) => a * b.at(0)).sum(),
  v.zip(basis).map(((a, b)) => a * b.at(1)).sum(),
)
#let ellipse-points(u, v, basis) = range(0, 73).map(i => {
  let t = i * calc.tau / 72
  project(u.zip(v).map(((a, b)) => a * calc.cos(t) + b * calc.sin(t)), basis)
})
#let projected-ball(indices, basis) = {
  let images = indices.map(i => basis.at(i))
  let xx = images.map(v => v.at(0) * v.at(0)).sum()
  let yy = images.map(v => v.at(1) * v.at(1)).sum()
  let xy = images.map(v => v.at(0) * v.at(1)).sum()
  let delta = calc.sqrt((xx - yy) * (xx - yy) + 4 * xy * xy)
  let high = (xx + yy + delta) / 2
  let low = (xx + yy - delta) / 2
  let eigenvector = if calc.abs(xy) < 0.000001 {
    if xx >= yy { (1, 0) } else { (0, 1) }
  } else { (xy, high - xx) }
  let norm = calc.sqrt(eigenvector.map(v => v * v).sum())
  let u = eigenvector.map(v => v / norm)
  let v = (-u.at(1), u.at(0))
  (
    points: range(0, 73).map(i => {
      let angle = i * calc.tau / 72
      let a = calc.sqrt(high) * calc.cos(angle)
      let b = calc.sqrt(low) * calc.sin(angle)
      (a * u.at(0) + b * v.at(0), a * u.at(1) + b * v.at(1))
    }),
    top: (xy / calc.sqrt(yy), calc.sqrt(yy)),
    left: (-calc.sqrt(xx), -xy / calc.sqrt(xx)),
    right: (calc.sqrt(xx), xy / calc.sqrt(xx)),
  )
}
#let rich-transvection-product() = canvas(length: 1cm, {
  import draw: *
  let basis = ((-2, -.45), (-.35, 1.7), (.3, 1.3), (1.7, .45))
  // V=Q^4; R0=<e1,e2,e3>, R1=<e1>, R2=<e2,e3>, P0=<e4>.
  // P1=<e1,e2,e4> is a hyperplane, P2=<e3,e4>, P1∩P2=P0.
  // Subspace outlines are projections of their unit balls, with one origin.
  let r0 = projected-ball((0, 1, 2), basis)
  let r2 = projected-ball((1, 2), basis)
  let p1 = projected-ball((0, 1, 3), basis)
  let p2 = projected-ball((2, 3), basis)
  set-style(stroke: .5pt, content: (padding: 2pt))
  line(..r0.points, stroke: (dash: "dashed"))
  line(..p1.points)
  line(..p2.points)
  line(..r2.points)
  for (v, name) in (((1, 0, 0, 0), $R_1$), ((0, 0, 0, 1), $P_0$)) {
    line((0, 0), project(v, basis), mark: (end: "stealth"))
    label(project(v, basis), name, anchor: "east")
  }
  label(p1.left, $P_1$, anchor: "east")
  label(p2.right, $P_2$, anchor: "west")
  label(r0.top, $R_0$, anchor: "south")
  label(r2.top, $R_2$, anchor: "north")
})

#let rich-centralizer-spaces() = canvas(length: 1cm, {
  import draw: *
  let basis = ((-.7, -.6), (.1, -.9), (-1.6, .1), (2, .6))
  // M=<e1,e2,e3>, P=<e1,e2,e4>, R=<e1>, L=<e2>, K=<e4>.
  // Each outline is the linear image of the unit ball of its subspace.
  // Both contain the common <e1,e2> ball; K is outside the M outline.
  let m = projected-ball((0, 1, 2), basis)
  let p = projected-ball((0, 1, 3), basis)
  set-style(stroke: .5pt, content: (padding: 2pt))
  line(..m.points)
  line(..p.points)
  label(m.left, $M$, anchor: "east")
  label(p.top, $P$, anchor: "south")
  for (v, name, dashed, anchor) in (
    ((1, 0, 0, 0), $R$, true, "north-east"),
    ((0, 1, 0, 0), $L$, false, "north"),
    ((0, 0, 0, 1), $K$, false, "west"),
  ) {
    line(
      (0, 0),
      project(v, basis),
      stroke: (dash: if dashed { "dashed" } else { "solid" }),
      mark: (end: "stealth"),
    )
    label(project(v, basis), name, anchor: anchor)
  }
})

#let duality-triangle() = canvas(length: 1cm, {
  import draw: *
  content((0, 0), $Delta$)
  content((0, 1.6), $breve(Delta)$)
  content((3, .8), $Delta_1$)
  set-style(stroke: .5pt)
  line((.12, .25), (.12, 1.35), mark: (end: "stealth"))
  line((-.12, 1.35), (-.12, .25), mark: (end: "stealth"))
  line((.35, .1), (2.65, .7), mark: (end: "stealth"))
  line((.35, 1.5), (2.65, .9), mark: (end: "stealth"))
})

#let transvection-chain() = canvas(length: 1cm, {
  import draw: *
  let basis = ((2.2, .35), (-.6, .5), (.8, 1.4), (.8, -1.4))
  let e1 = (1, 0, 0, 0)
  let e3 = (0, 0, 1, 0)
  let e4 = (0, 0, 0, 1)
  set-style(stroke: .5pt, content: (padding: 2pt))
  line(..ellipse-points(e1, e3, basis))
  line(..ellipse-points(e1, e4, basis))
  line(project(e1.map(a => -a), basis), project(e1, basis), stroke: (
    dash: "dashed",
  ))
  for (v, name, anchor) in (
    (e3, $R$, "south"),
    (e4, $L$, "north"),
  ) {
    line((0, 0), project(v, basis), mark: (end: "stealth"))
    label(project(v, basis), name, anchor: anchor)
  }
  label(project((-.65, 0, .55, 0), basis), $P$)
  label(project((-.65, 0, 0, .55), basis), $H$)
  label(project((.6, 0, 0, 0), basis), $K$, anchor: "south")
  // The four ordered pairs are (residue line, fixed hyperplane).
  // Their positions form a combinatorial chain, not geometric vertices.
  content((0, -2.1), $ (R,P) arrow.r (K,P) arrow.r (K,H) arrow.r (L,H) $)
})
