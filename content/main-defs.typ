#import "numbering.typ": *
#let editorial-notes = sys.inputs.at("editorial-notes", default: "on") != "off"
#let source(n, printed: none) = [#metadata((
  kind: "source",
  file-page: n,
  printed-page: if printed == none { str(n + 2) } else { printed },
))]
#let number-text(body) = text(weight: "semibold", style: "normal", body)
#let copyright-line(body) = text(size: 8pt, body)
#let reference-body(it) = context {
  let caption = it.supplement not in (auto, none, [])
  let record = if it.element != none { numbered-record(it.target) }
  let numeric = record != none and record.value.number != none
  let resolved = it.element != none and (numeric or caption)
  let number = if numeric { record.value.number.join(".") } else { "?" }
  let destination = if record != none { record.location() } else if (
    it.element != none
  ) { it.element.location() }
  let shown = if caption { it.supplement } else if ("eq:", "cond:").any(
    prefix => str(it.target).starts-with(prefix),
  ) { [(#number-text(number))] } else if str(it.target).starts-with("bib:") {
    [\[#number-text(number)\]]
  } else { number-text(number) }
  metadata((
    kind: "cross-reference",
    target: str(it.target),
    resolved: resolved,
    printed: number,
    target-location: if resolved { destination },
  ))
  if resolved { link(destination, shown) } else { shown }
}
#let reference-rules(body) = {
  show ref: it => reference-body(it)
  body
}
#let idx(..path) = [#metadata((
  kind: "index-mark",
  path: path.pos(),
))<index-mark>]
#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = if editorial-notes {
  context {
    let mark = "*" + str(editorial-note-counter.get().first() + 1) + ")"
    footnote(numbering: _ => mark)[#body~— _Прим. ред._]
    // Emit the native footnote first so it attaches to the preceding word.
    editorial-note-counter.step()
    counter(footnote).update(n => n - 1)
  }
}
#let group-name(name) = math.class("normal", math.upright(name))
#let GL = group-name("GL")
#let SL = group-name("SL")
#let PGL = group-name("PGL")
#let PSL = group-name("PSL")
#let PU = group-name("PU")
#let Sp = group-name("Sp")
#let PSp = group-name("PSp")
#let TSp = group-name("TSp")
#let PTSp = group-name("PTSp")
#let TL = group-name("TL")
#let PTL = group-name("PTL")
#let GammaL = group-name("ΓL")
#let PGammaL = group-name("PΓL")
#let XiL = group-name("ΞL")
#let PXiL = group-name("PΞL")
#let RL = group-name("RL")
#let Aut = math.op("Aut")
#let Hom = math.op("Hom")
#let End = math.op("End")
#let Ker = math.op("Ker")
#let Im = math.op("Im")
#let rad = math.op("rad")
#let rank = math.op("rank")
#let char = math.op("char")
#let diag = math.op("diag")
#let editorial-bibliography = [
  #show bibliography: none
  #bibliography("../editorial.bib", style: "chicago-notes")
]
