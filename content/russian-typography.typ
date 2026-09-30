// Keep compound abbreviations together; the preceding space stays breakable.
#let russian-typography(body) = {
  let patterns = (
    "[тТ]\\.[ \\t]+[еЕоОпПдД]\\.",
    "[иИ]\\.[ \\t]+[оО]\\.",
    "[нН]\\.[ \\t]+[эЭ]\\.",
  )
  show regex("\\b(?:" + patterns.join("|") + ")"): it => {
    text(it.text.replace(regex("[ \\t]+"), "\u{a0}"))
  }
  body
}
