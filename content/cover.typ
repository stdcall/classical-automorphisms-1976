// Типографическая обложка: фон, набор и линейка без растров.
#let cover-page() = page(
  width: 145mm,
  height: 215mm,
  margin: 0pt,
  fill: rgb("79aaa6"),
  numbering: none,
  header: none,
  footer: none,
)[
  #set text(font: "Libertinus Serif", weight: "regular", fill: black)
  #set par(first-line-indent: 0pt)
  #place(top + center, dy: 16mm)[
    #text(size: 41pt)[АВТОМОРФИЗМЫ]
  ]
  #place(top + center, dy: 35mm)[
    #text(size: 41pt)[КЛАССИЧЕСКИХ]
  ]
  #place(top + center, dy: 54mm)[
    #text(size: 41pt)[ГРУПП]
  ]
  #place(top + left, dy: 193mm)[
    #line(length: 145mm, stroke: 0.45pt)
  ]
  #place(top + center, dy: 200mm)[
    #text(size: 18pt)[ИЗДАТЕЛЬСТВО «М И Р» МОСКВА]
  ]
]
