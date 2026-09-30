#import "numbering.typ": *
#let sequence = [].func()
#let prepend-heading(body, head) = {
  if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let first = children.position(it => it.func() not in ([ ].func(), parbreak))
    if first == none { head + body } else {
      (
        children.slice(0, first).join()
          + prepend-heading(children.at(first), head)
          + children.slice(first + 1).join()
      )
    }
  } else if body.func() in (enum, enum.item, list, list.item, terms) {
    block(sticky: true, below: 0.6em, head) + body
  } else if body.func() == math.equation and body.block {
    grid(
      columns: (auto, 1fr),
      align: (left + horizon, center + horizon),
      column-gutter: 0.6em,
      head, body,
    )
  } else { head + body }
}
#let indent-first(body) = {
  let styled(it) = {
    set par(first-line-indent: (amount: 1.25em, all: true))
    it
  }
  let breaks(it) = (
    it.func()
      in (
        parbreak,
        block,
        grid,
        table,
        figure,
        list,
        enum,
        terms,
      )
      or (it.func() == math.equation and it.block)
  )
  if body.func() == sequence and body.children.len() > 0 {
    let end = body.children.position(breaks)
    if end == none { styled(body) } else {
      (
        styled(body.children.slice(0, end).join())
          + body.children.slice(end).join()
      )
    }
  } else { styled(body) }
}
#let statement-block(body) = {
  context v(par.spacing + 0.2em, weak: true)
  indent-first(body)
  parbreak()
  context v(par.spacing + 0.2em, weak: true)
}
#let statement(
  family,
  name,
  body,
  numbered: true,
  italic: true,
  base: none,
  suffix: "",
) = {
  let format(n) = context {
    if paper-state.get().mode == "chapter-section" {
      strong[#n. ] + if name != none { emph[#name. ] } else { [] }
    } else if name == none { strong[(#n) ] } else { strong[#name #n. ] }
  }
  let head = if base != none {
    derived-number(family, base, suffix, format)
  } else if numbered { counted(family, format) } else {
    semantic-record(family) + if name == none { [] } else { strong[#name. ] }
  }
  let body = if italic { emph(body) } else { body }
  statement-block(prepend-heading(body, head))
}
#let claim(body, family: "prop") = statement(family, none, body)
#let unnumbered-claim(body, family: "th") = {
  statement(family, none, body, numbered: false)
}
#let numbered-paragraph(
  body,
  family: "prop",
  italic: true,
  base: none,
  suffix: "",
) = {
  let format(n) = text(style: "normal", weight: "bold")[#n. ]
  let head = if base == none { counted(family, format) } else {
    derived-number(family, base, suffix, format)
  }
  let body = prepend-heading(body, head)
  statement-block(if italic { emph(body) } else { body })
}
#let remark(body, numbered: true) = {
  statement("prop", [Замечание], body, numbered: numbered, italic: false)
}
#let theorem(body, numbered: true, base: none, suffix: "") = {
  statement(
    "th",
    [Теорема],
    body,
    numbered: numbered,
    base: base,
    suffix: suffix,
  )
}
#let lemma(body, numbered: true, base: none, suffix: "") = {
  statement(
    "lem",
    [Лемма],
    body,
    numbered: numbered,
    base: base,
    suffix: suffix,
  )
}
#let proposition(body, numbered: true, base: none, suffix: "") = {
  statement(
    "prop",
    [Предложение],
    body,
    numbered: numbered,
    base: base,
    suffix: suffix,
  )
}
#let corollary(body, numbered: true, base: none, suffix: "") = {
  statement(
    "cor",
    [Следствие],
    body,
    numbered: numbered,
    base: base,
    suffix: suffix,
  )
}
#let definition(body, numbered: true, named: true) = {
  statement(
    "def",
    if named { [Определение] } else { none },
    body,
    numbered: numbered,
    italic: false,
  )
}
#let example(body, numbered: true) = {
  statement("exm", [Пример], body, numbered: numbered, italic: false)
}
#let proof(body) = statement-block(prepend-heading(
  body,
  [#emph[Доказательство.] ],
))
#let bib-item(body) = block(above: 0.2em, below: 0.2em, {
  set par(first-line-indent: 0pt, hanging-indent: 1.3em)
  counted("bib", n => [#n. ])
  body
})
#let notations(body) = {
  set list(marker: [], indent: 0pt, body-indent: 0pt, spacing: 0.6em)
  body
}
#let condition-series(body) = {
  family-counter("cond").update(0)
  body
}
#let condition(body) = block(above: 0.3em, below: 0.3em, {
  set par(first-line-indent: 0pt, hanging-indent: 1.5em)
  counted("cond", n => [(#n) ])
  body
})
#let symbolic-condition(symbol, body, italic: false) = block(
  above: 0.3em,
  below: 0.3em,
  {
    set par(first-line-indent: 0pt, hanging-indent: 1.5em)
    let head = context {
      record("cond", number: (symbol,))
      text(style: "normal", weight: "bold")[(#symbol) ]
    }
    let body = prepend-heading(body, head)
    if italic { emph(body) } else { body }
  },
)
#let numbered-display(it) = {
  family-counter("eq").step()
  context {
    record("eq")
    let shown = object-number("eq", here()).join(".")
    math.equation(
      block: true,
      numbering: _ => text(font: "Libertinus Serif", style: "normal")[(#shown)],
      number-align: right + horizon,
      it.body,
    )
  }
}
