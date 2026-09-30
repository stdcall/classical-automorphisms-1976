"""Render heading mathematics only in PDF bookmark titles.

The Typst heading tree supplies the index structure. Nothing is written back
to the document, its printed contents or its heading text.
"""
import re

SUBSCRIPTS = str.maketrans(dict(zip(
    '0123456789+-=()aehijklmnoprstuvxβγρφχ',
    '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᵦᵧᵨᵩᵪ')))
SUPERSCRIPTS = str.maketrans(dict(zip(
    '0123456789+-=()abcdefghijklmnoprstuvwxyz',
    '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ')))


def index_text(value, *, upper=False):
    table = SUPERSCRIPTS if upper else SUBSCRIPTS
    if value and all(ord(c) in table for c in value):
        return value.translate(table)
    marker = '^' if upper else '_'
    return marker + (value if len(value) == 1 else '{'+value+'}')


def heading_text(node, *, pretty=False, math=False):
    """Serialize the supported heading tree, declining unfamiliar notation."""
    func = node['func']
    if func in ('text', 'symbol'):
        return node['text']
    if func == 'space':
        return '' if math else ' '
    if func == 'sequence':
        return ''.join(heading_text(c, pretty=pretty, math=math)
                       for c in node['children'])
    if func == 'styled':
        return heading_text(node['child'], pretty=pretty, math=math)
    if func in ('equation', 'class', 'lr'):
        return heading_text(node['body'], pretty=pretty,
                            math=math or func == 'equation')
    if func == 'attach':
        if set(node) - {'func', 'base', 'b', 't'}:
            raise ValueError('Unsupported mathematical attachment')
        result = heading_text(node['base'], pretty=pretty, math=True)
        for key in ('b', 't'):
            if key in node:
                value = heading_text(node[key], math=True)
                result += index_text(value, upper=key == 't') if pretty else value
        return result
    raise ValueError('Unsupported heading element: '+func)


def bookmark_title(title, page_number, headings):
    """Keep the native numbering prefix and change only a matching body.

    Page and complete heading text must both match; a word that resembles
    flattened mathematics elsewhere cannot acquire an index accidentally.
    """
    matches = []
    for heading in headings:
        if heading['position']['page'] != page_number:
            continue
        try:
            plain = heading_text(heading['body'])
            pretty = heading_text(heading['body'], pretty=True)
        except (ValueError, KeyError):
            continue
        if plain == pretty:
            continue
        pattern = r'\s*'.join(re.escape(c) for c in plain if not c.isspace())
        found = re.search(pattern+r'\s*$', title)
        if found:
            matches.append(title[:found.start()]+pretty)
    if len(matches) > 1:
        raise ValueError('Ambiguous bookmark heading: '+title)
    return matches[0] if matches else title
