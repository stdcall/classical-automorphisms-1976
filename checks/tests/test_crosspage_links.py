"""Exercise wrapped semantic references against actual PDF annotations."""
import sys
import tempfile
import unittest
from pathlib import Path

import fitz

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from check_links import check_links


class CrosspageLinksTests(unittest.TestCase):
    def fixture(self, path, wrong_first=False, prefix=False, earlier=False):
        doc = fitz.open()
        for _ in range(3):
            doc.new_page(width=411.024, height=609.449)
        doc[0].insert_text((40, 553), 'Before marker', fontsize=10)
        if earlier:
            doc[0].insert_text((40, 565), 'Later body line', fontsize=10)
        last = doc[0].get_text('words')[1]
        text = 'Plain [9] first' if prefix else '[9] first'
        doc[1].insert_text((40, 53), text, fontsize=10)
        word = doc[1].get_text('words')[1 if prefix else 0]
        rect = fitz.Rect(word[:4])
        doc[1].insert_link({'kind': fitz.LINK_GOTO, 'from': rect,
                           'page': 0 if wrong_first else 2,
                           'to': fitz.Point(40, 200)})
        if wrong_first:
            doc[1].insert_text((100, 53), '[9]', fontsize=10)
            doc[1].insert_link({'kind': fitz.LINK_GOTO,
                               'from': fitz.Rect(100, 42, 115, 56),
                               'page': 2, 'to': fitz.Point(40, 200)})
        doc.save(path)
        doc.close()
        return [{'target': 'bib:test', 'resolved': True,
                 'position': {'page': 1, 'x': f'{last[2]}pt', 'y': '553pt'},
                 'target-position': {'page': 3, 'x': '40pt', 'y': '210pt'}}]

    def run_case(self, **options):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'wrapped.pdf'
            references = self.fixture(path, **options)
            return check_links(path, references)

    def test_first_body_line_link_is_verified(self):
        report = self.run_case()
        self.assertEqual(report['semantic_references_checked'], 1)
        self.assertTrue(report['references'][0]['crosspage_wrapped_origin'])

    def test_wrong_first_target_not_bypassed_by_later_correct_link(self):
        with self.assertRaisesRegex(AssertionError, 'wrong target page'):
            self.run_case(wrong_first=True)

    def test_later_link_on_first_line_is_not_the_wrapped_origin(self):
        with self.assertRaisesRegex(AssertionError, 'expected one clickable'):
            self.run_case(prefix=True)

    def test_marker_before_last_body_line_cannot_cross_page(self):
        with self.assertRaisesRegex(AssertionError, 'expected one clickable'):
            self.run_case(earlier=True)


if __name__ == '__main__':
    unittest.main()
