// The subject index is generated from the marked passages of the text.
// Each page number links to the actual occurrence and follows reflow.
#let sort-key(path) = {
  let key = lower(path.join(" "))
  key = key.replace("ё", "е")
  key = key.replace(regex("[,’'.]"), "")
  for (prefix, russian) in (
    ("ge", "ге"),
    ("k-", "к-"),
    ("r-", "р-"),
    (
      "u-",
      "у-",
    ),
  ) {
    if key.starts-with(prefix) {
      key = russian + key.slice(prefix.len())
      break
    }
  }
  if key.starts-with("(r") { key = "инволюция " + key }
  key
}
#let dashes(part) = part.split(" ").map(_ => "—").join(" ")
#let printed(path, previous) = {
  let words = path.join(" ").split(" ")
  if previous == none { return words.join(" ") }
  let prior = previous.join(" ").split(" ")
  let shared = true
  let result = ()
  for (i, word) in words.enumerate() {
    if shared and i < prior.len() and word == prior.at(i) {
      result.push("—")
    } else {
      shared = false
      result.push(word)
    }
  }
  result.join(" ")
}
#let locator(location) = box(context {
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    target-location: location,
  ))
  link(location, str(counter(page).at(location).first()))
})
#let entries = context {
  let collected = (:)
  for mark in query(<index-mark>) {
    let key = mark.value.path.join("\u{1f}")
    let item = collected.at(key, default: (path: mark.value.path, at: ()))
    let folio = counter(page).at(mark.location()).first()
    if item.at.all(l => counter(page).at(l).first() != folio) {
      item.at.push(mark.location())
    }
    collected.insert(key, item)
  }
  let previous = none
  let initial = none
  for item in collected.values().sorted(key: item => sort-key(item.path)) {
    let letter = upper(sort-key(item.path).first())
    if letter != initial {
      if initial != none { v(0.8em, weak: true) }
      initial = letter
      previous = none
    }
    let name = printed(item.path, previous)
    block(above: 0pt, below: 0.3em, par(hanging-indent: 1.2em)[
      #name #item.at.map(locator).join([, ])
    ])
    previous = item.path
  }
}
#let subject-index() = {
  set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  set text(size: 9pt)
  columns(2, gutter: 6mm, entries)
}
