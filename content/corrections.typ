#import "main-defs.typ" as book-defs
#show: book-defs.reference-rules
#let book-scope = dictionary(book-defs)
#let entries = json("../corrections.json").entries
#let markup(field) = eval(field, mode: "markup", scope: book-scope)
#set document(
  title: "Автоморфизмы классических групп. Исправления",
  author: "Под редакцией Ю. И. Мерзлякова",
  date: none,
)
#set page(
  width: 145mm,
  height: 215mm,
  margin: (x: 14mm, top: 17mm, bottom: 15mm),
  footer: context align(center, text(size: 9pt, counter(page).display())),
)
#set text(font: "Libertinus Serif", size: 10.5pt, lang: "ru")
#set par(justify: true, leading: 0.6em, spacing: 0.7em)
#show math.equation: set text(font: "STIX Two Math")
#align(center, text(size: 16pt)[Исправления])

_Автоморфизмы классических групп_. Сборник переводов под редакцией
Ю.~И.~Мерзлякова. Москва: Мир, 1976. Номера страниц ниже относятся к печатному
изданию.

#show heading: set text(size: 12pt)
#if entries.len() == 0 [
  Подтвержденных исправлений пока нет.
] else {
  let section = none
  for entry in entries {
    if entry.section != section {
      section = entry.section
      heading(level: 1, section)
    }
    block(breakable: false, above: 1em)[
      #metadata((correction: entry.id))
      *#entry.id* · с. #entry.printed_page#if (
        entry.place != entry.section
      ) [, #entry.place]

      В оригинале: #markup(entry.original)

      Исправлено: #markup(entry.corrected)

      #text(size: 9pt, markup(entry.reason))
    ]
  }
}
