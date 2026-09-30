#import "numbering.typ": *
#import "statements.typ": numbered-display
#import "main-defs.typ": reference-rules
#import "russian-typography.typ": russian-typography
#let running-author = state("running-author", [])
#let running-title = state("running-title", [])
#let heading-note-state = state("heading-note", none)
#let heading-note(body) = heading-note-state.update(body)
#let title-note(it) = context {
  let note = heading-note-state.at(it.location())
  heading-note-state.update(none)
  if note != none { footnote(note) }
}
#let article-heading-numbering(..n) = {
  let n = n.pos()
  if n.len() == 2 { "§ " + str(n.last()) + "." } else {
    "§ " + n.slice(1).map(str).join(".") + "."
  }
}
#let lecture-heading-numbering(..n) = {
  let n = n.pos()
  if n.len() == 2 { "Глава " + str(n.last()) + "." } else {
    "§ " + n.slice(1).map(str).join(".") + "."
  }
}
#let paper(
  key,
  title,
  author: [],
  mode: "section",
  shared: true,
  equation-mode: none,
  family-modes: (:),
  family-series: (:),
) = {
  paper-state.update((
    key: key,
    title: title,
    author: author,
    mode: mode,
    shared: shared,
    equation-mode: equation-mode,
    family-modes: family-modes,
    family-series: family-series,
  ))
  reset-families()
  counter(heading).update((0, 0, 0))
  running-author.update(author)
  running-title.update(title)
  heading(level: 1, numbering: none, title)
}
#let frontmatter(key, title) = {
  paper(key, title)
  running-author.update(title)
}
#let opening-page() = {
  query(heading.where(level: 1)).any(it => (
    it.location().page() == here().page()
  ))
}
#let running-header = context {
  if opening-page() { return }
  let n = counter(page).get().first()
  let author = running-author.get()
  let title = running-title.get()
  let folio = text(size: 9pt, str(n))
  let head = text(size: 9pt, style: "italic", if calc.even(n) { author } else {
    title
  })
  stack(
    dir: ttb,
    spacing: 1.2mm,
    grid(
      columns: (1fr, 8fr, 1fr),
      align: (left, center, right),
      if calc.even(n) { folio } else { [] },
      head,
      if calc.odd(n) { folio } else { [] },
    ),
    line(length: 100%, stroke: 0.4pt),
  )
}
#let heading-number(it) = {
  let n = counter(heading).at(it.location())
  let paper = paper-state.at(it.location())
  if paper.mode == "chapter-section" {
    if it.level == 2 { str(n.at(1)) } else { n.slice(1, 3).map(str).join(".") }
  } else { str(n.at(1, default: 0)) }
}
#let book-style(body) = {
  set document(
    title: "Автоморфизмы классических групп",
    author: "Под редакцией Ю. И. Мерзлякова",
  )
  set page(
    width: 145mm,
    height: 215mm,
    margin: (x: 14mm, top: 17mm, bottom: 15mm),
    header: counter(footnote).update(0) + running-header,
    footer: context if opening-page() {
      align(center, text(size: 9pt, counter(page).display()))
    },
  )
  set text(
    font: "Libertinus Serif",
    size: 10.5pt,
    lang: "ru",
    fill: rgb("202020"),
  )
  set par(
    justify: true,
    first-line-indent: 1.25em,
    leading: 0.6em,
    spacing: 0.55em,
  )
  set math.equation(numbering: none)
  // Native item spacing leaves room for inline fractions in adjacent items.
  set enum(spacing: 0.9em)
  set footnote(numbering: "1)")
  show math.equation: set text(font: "STIX Two Math")
  show math.equation.where(block: true): it => {
    if it.has("label") and str(it.label).starts-with("eq:") {
      numbered-display(it)
    } else { it }
  }
  set heading(numbering: article-heading-numbering)
  show heading: set text(hyphenate: false)
  show heading.where(level: 1): it => {
    set par(first-line-indent: 0pt, justify: false)
    pagebreak(weak: true)
    block(width: 100%, above: 12mm, below: 8mm, align(center, {
      let author = context paper-state.get().author
      text(size: 12pt, style: "italic", author)
      linebreak()
      text(size: 15pt, weight: "bold", it.body + title-note(it))
    }))
  }
  show heading.where(level: 2): it => context {
    set par(first-line-indent: 0pt, justify: false)
    if it.numbering != none {
      restart-counters(2)
      record("heading", number: (heading-number(it),), level: 2)
    }
    block(width: 100%, above: 5mm, below: 3mm, sticky: true, align(
      center,
      strong[
        #if it.numbering != none {
          if paper-state.get().mode == "chapter-section" {
            [Глава #heading-number(it). ]
          } else { [§ #heading-number(it). ] }
        }#it.body#title-note(it)
      ],
    ))
  }
  show heading.where(level: 3): it => context {
    set par(first-line-indent: 0pt, justify: false)
    if it.numbering != none {
      restart-counters(3)
      record("heading", number: (heading-number(it),), level: 3)
    }
    block(width: 100%, above: 4mm, below: 2.5mm, sticky: true, align(
      center,
      strong[
        #if it.numbering != none { [§ #heading-number(it). ] }#it.body
        #title-note(it)
      ],
    ))
  }
  show outline: set par(first-line-indent: 0pt)
  show outline.entry: set block(breakable: false)
  russian-typography(reference-rules(body))
}
