"""Bookmark indices retain their position, case and mathematical meaning."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'scripts'))
from outline_titles import bookmark_title, heading_text, index_text


class OutlineTitles(unittest.TestCase):
    def test_exact_scripts_and_explicit_fallbacks(self):
        self.assertEqual(index_text('n'), 'ₙ')
        self.assertEqual(index_text('ij'), 'ᵢⱼ')
        self.assertEqual(index_text('χ'), 'ᵪ')
        self.assertEqual(index_text('g'), '_g')
        self.assertEqual(index_text('N'), '_N')
        self.assertEqual(index_text('ng'), '_{ng}')
        self.assertEqual(index_text('2', upper=True), '²')

    def test_matching_heading_only_and_native_numbering(self):
        body = {'func': 'sequence', 'children': [
            {'func': 'text', 'text': 'Группа '},
            {'func': 'equation', 'body': {'func': 'attach',
             'base': {'func': 'text', 'text': 'GL'},
             'b': {'func': 'symbol', 'text': 'n'}}}]}
        headings = [{'body': body, 'position': {'page': 3}}]
        title = '§ 2. Группа GLn'
        self.assertEqual(bookmark_title(title, 3, headings), '§ 2. Группа GLₙ')
        self.assertEqual(bookmark_title(title, 4, headings), title)
        other = '§ 2. Другая группа GLn'
        self.assertEqual(bookmark_title(other, 3, headings), other)
        self.assertEqual(heading_text(body), 'Группа GLn')

    def test_unknown_mathematics_keeps_original_title(self):
        headings = [{'body': {'func': 'frac'}, 'position': {'page': 3}}]
        self.assertEqual(bookmark_title('§ 2. A/B', 3, headings), '§ 2. A/B')


if __name__ == '__main__':
    unittest.main()
