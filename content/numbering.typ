// Counting schemes of the independently numbered works in the collection.
#let paper-state = state("paper", (
  key: "",
  author: [],
  title: [],
  mode: "section",
  shared: true,
  equation-mode: none,
  family-modes: (:),
  family-series: (:),
))
#let family-counter(family) = counter("numbered:" + family)
#let number-families = (
  "statement",
  "th",
  "lem",
  "prop",
  "cor",
  "def",
  "exm",
  "eq",
  "bib",
  "fig",
  "tab",
  "cond",
)
#let reset-families() = {
  for family in number-families { family-counter(family).update(0) }
}
#let family-mode(family, paper) = {
  paper.family-modes.at(family, default: if family == "eq" {
    if paper.equation-mode == none { paper.mode } else { paper.equation-mode }
  } else { paper.mode })
}
#let number-series(family, paper) = {
  paper.family-series.at(family, default: if paper.shared
    and family
      in (
        "th",
        "lem",
        "prop",
        "cor",
        "def",
        "exm",
      ) { "statement" } else { family })
}
#let restart-counters(level) = context {
  let paper = paper-state.get()
  for family in number-families {
    let mode = family-mode(family, paper)
    if (
      (mode == "section" and level == 2)
        or (
          mode == "local"
            and level == if paper.mode == "chapter-section" { 3 } else { 2 }
        )
        or (
          mode == "chapter-section" and level <= 3
        )
    ) {
      if family not in ("bib", "fig", "tab") {
        family-counter(family).update(0)
      }
    }
  }
}
#let number-prefix(location, mode) = {
  let paper = paper-state.at(location)
  let n = counter(heading).at(location)
  if mode == "section" { (str(n.at(1, default: 0)),) } else if (
    mode == "chapter-section"
  ) {
    n.slice(1, 3).map(str)
  } else { () }
}
#let object-number(family, location) = {
  let paper = paper-state.at(location)
  let series = number-series(family, paper)
  let prefix = if family in ("bib", "fig", "tab", "cond") { () } else {
    number-prefix(location, family-mode(family, paper))
  }
  (..prefix, str(family-counter(series).at(location).first()))
}
#let record(family, number: none, level: none) = context {
  let number = if number == none { object-number(family, here()) } else {
    number
  }
  [#metadata((
    kind: "numbered",
    family: family,
    number: number,
    level: level,
  ))<numbered>]
}
#let record-number(record) = record.value.number
#let semantic-record(family) = [#metadata((
  kind: "numbered",
  family: family,
  number: none,
  level: none,
))<numbered>]
#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}
#let counted(family, format) = context {
  let paper = paper-state.get()
  let series = number-series(family, paper)
  family-counter(series).step()
  context {
    record(family)
    format(object-number(family, here()).join("."))
  }
}

// Explicit exceptions in the abridged Cohn translation. A seed is the
// preceding number, so the next object remains automatically counted.
#let series-seed(family, preceding) = {
  family-counter(family).update(preceding)
}
#let section-seed(preceding) = counter(heading).update((0, preceding))

// A derived theorem takes its numeric part from the base theorem's label.
#let references-in(it) = {
  if it.func() == ref { (it.target,) } else if it.has("children") {
    it.children.map(references-in).flatten()
  } else if it.has("body") { references-in(it.body) } else { () }
}
#let derived-number(family, base, suffix, format) = context {
  let refs = references-in(base)
  assert(
    refs.len() == 1,
    message: "A derived statement needs one base reference",
  )
  let base-record = numbered-record(refs.first())
  let number = if base-record == none { ("?",) } else {
    base-record.value.number
  }
  let number = (..number.slice(0, -1), number.last() + suffix)
  record(family, number: number)
  format(number.join("."))
}
