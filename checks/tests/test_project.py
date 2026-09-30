"""Project schema and PDF navigation invariants; no book-specific fixtures."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

from pypdf import PdfReader, PdfWriter
from pypdf.generic import Fit, NullObject

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'scripts'))
from build import normalize_outline_destinations
from check_indexes import index_checks
from lint_typst import (coverage_checks, label_problem, pitfall_checks,
                        scan, unresolved_references)
from project import editor_settings, settings, stage


class ProjectSchema(unittest.TestCase):
    def test_stage_editor_and_outline_policy(self):
        self.assertIn('--input=stage='+stage(),
                      editor_settings()['tinymist.typstExtraArgs'])
        self.assertEqual(settings()['pdf_navigation']['outline_left'], 0)
        self.assertEqual(settings()['prose']['checker'], 'vale')

    def test_corrections_schema(self):
        data = json.loads((ROOT/'corrections.json').read_text())
        self.assertEqual(set(data), {'entries'})
        self.assertIsInstance(data['entries'], list)
        fields = {'id', 'printed_page', 'section', 'place', 'original',
                  'corrected', 'reason', 'verified_by'}
        ids = []
        for entry in data['entries']:
            self.assertEqual(set(entry), fields)
            for field in fields:
                self.assertTrue(str(entry[field]).strip(), field)
            self.assertNotEqual(entry['original'], entry['corrected'])
            page = entry['printed_page']
            self.assertTrue((isinstance(page, int) and page > 0)
                            or (isinstance(page, str) and bool(page.strip())))
            ids.append(entry['id'])
        self.assertEqual(len(ids), len(set(ids)))

    def test_semantic_labels(self):
        for label in ('th:isometry-factorization', 'eq:form-identity',
                      'sec:linear-groups', 'bib:Dieudonne1955'):
            self.assertIsNone(label_problem(label))
        self.assertIsNotNone(label_problem('th:1.2'))

    def test_nested_bookmarks_use_explicit_left_and_preserve_zoom(self):
        writer = PdfWriter()
        writer.add_blank_page(400, 600)
        parent = writer.add_outline_item('Chapter', 0,
                                         fit=Fit.xyz(30, 510, 2))
        writer.add_outline_item('Section', 0, parent=parent,
                                fit=Fit.xyz(40, 320, 1))
        with tempfile.TemporaryDirectory() as directory:
            before = Path(directory)/'before.pdf'
            after = Path(directory)/'after.pdf'
            writer.write(before)
            original = PdfReader(before)
            result = PdfWriter(before, incremental=True)
            self.assertEqual(normalize_outline_destinations(result, original), 2)
            result.write(after)
            reader = PdfReader(after)
            nodes = [reader.outline[0], reader.outline[1][0]]
            for node, top in zip(nodes, (510, 320)):
                dest = node.dest_array
                self.assertEqual(str(dest[1]), '/XYZ')
                self.assertNotIsInstance(dest[2], NullObject)
                self.assertEqual(float(dest[2]), 0)
                self.assertEqual(float(dest[3]), top)
                self.assertIsInstance(dest[4], NullObject)
            self.assertNotIn('/OpenAction', reader.trailer['/Root'])

    def test_unresolved_reference_retains_source_page(self):
        position = {'page': 1, 'x': '20pt', 'y': '40pt'}
        data = {'metadata': [
            {'value': {'kind': 'source', 'file-page': 12,
                       'position': position}},
            {'value': {'kind': 'cross-reference', 'target': 'th:missing',
                       'resolved': False, 'position': position}}]}
        report = unresolved_references(data, 'draft')
        self.assertEqual(report['count'], 1)
        self.assertEqual(report['targets'][0]['occurrences'][0]['source_page'], 12)

    def test_chapter_opens_page_and_nested_section_keeps_its_height(self):
        writer = PdfWriter()
        writer.add_blank_page(400, 600)
        parent = writer.add_outline_item('Chapter', 0, fit=Fit.xyz(30, 510, 2))
        writer.add_outline_item('Section', 0, parent=parent,
                                fit=Fit.xyz(40, 320, 1))
        with tempfile.TemporaryDirectory() as directory:
            before = Path(directory)/'before.pdf'
            after = Path(directory)/'after.pdf'
            writer.write(before)
            original = PdfReader(before)
            result = PdfWriter(before, incremental=True)
            normalize_outline_destinations(result, original,
                                           chapter_page_starts=True)
            result.write(after)
            reader = PdfReader(after)
            self.assertEqual(float(reader.outline[0].dest_array[3]), 600)
            self.assertEqual(float(reader.outline[1][0].dest_array[3]), 320)
            for node in (reader.outline[0], reader.outline[1][0]):
                self.assertNotIsInstance(node.dest_array[2], NullObject)
                self.assertEqual(float(node.dest_array[2]), 0)
                self.assertIsInstance(node.dest_array[4], NullObject)

    def test_index_path_rejects_empty_levels(self):
        errors, _ = index_checks([{'value': {'kind': 'index-mark',
                                            'path': ['Group', '']}}], final=False)
        self.assertTrue(errors)

    def test_page_anchor_after_block_is_not_sentence_break(self):
        for block in ('#idx("неподвижное пространство")',
                      '#align(center, transvection-dilatation())'):
            text = block+'\n\n#source(61)Ясно, что это новый абзац.\n'
            kinds, ends = scan(text)
            self.assertFalse([f for f in pitfall_checks('chapter.typ', text,
                                                       kinds, ends)
                              if f['rule'] == 'T044'])
        text = 'Линейное отображение переводит\n\n#source(61)каждый вектор.\n'
        kinds, ends = scan(text)
        self.assertTrue([f for f in pitfall_checks('chapter.typ', text, kinds, ends)
                         if f['rule'] == 'T044'])

    def test_numbered_record_requires_matching_label(self):
        position = {'page': 1, 'x': '20pt', 'y': '40pt'}
        record = {'value': {'kind': 'numbered', 'family': 'th',
                            'number': ['1.1']}, 'position': position,
                  'label': '<numbered>'}
        data = {'metadata': [record], 'labelled': {
            'th:factorization': {'count': 1, 'record': record}}}
        self.assertEqual(coverage_checks(data, {}, True), [])
        data['labelled']['th:factorization']['count'] = 2
        self.assertTrue(coverage_checks(data, {}, True))


if __name__ == '__main__':
    unittest.main()
