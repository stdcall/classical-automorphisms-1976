// Титул по печатному оригиналу; печатный счёт задаёт main.typ.
#import "main-defs.typ": source
#let title-page() = page(
  width: 145mm,
  height: 215mm,
  margin: 0pt,
  fill: white,
  numbering: none,
  header: none,
  footer: none,
)[
  #source(1)
  #set text(font: "Libertinus Serif", weight: "regular", fill: black)
  #set par(first-line-indent: 0pt)
  #place(top + center, dy: 9mm)[
    #text(size: 40pt)[АВТОМОРФИЗМЫ]
  ]
  #place(top + center, dy: 25mm)[
    #text(size: 40pt)[КЛАССИЧЕСКИХ]
  ]
  #place(top + center, dy: 41mm)[
    #text(size: 40pt)[ГРУПП]
  ]
  #place(top + center, dy: 82mm)[
    #text(size: 17pt)[Сборник переводов]
  ]
  #place(top + center, dy: 91mm)[
    #text(size: 17pt)[с английского и французского]
  ]
  #place(top + center, dy: 112mm)[
    #text(size: 17pt)[Под редакцией]
  ]
  #place(top + center, dy: 121mm)[
    #text(size: 17pt)[Ю. И. МЕРЗЛЯКОВА]
  ]
  #place(top + center, dy: 189mm)[
    #text(size: 17pt)[ИЗДАТЕЛЬСТВО «МИР»]
  ]
  #place(top + center, dy: 198mm)[
    #text(size: 17pt)[МОСКВА 1976]
  ]
]
