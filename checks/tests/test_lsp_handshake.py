"""Compilation notifications queued while focusMain's response is pending."""
import queue
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from check_lsp import wait_main_compile


def status(path, value):
    return {'method': 'tinymist/compileStatus',
            'params': {'path': path, 'status': value}}


class MainCompilationTests(unittest.TestCase):
    def test_queued_chapter_error_then_main_success(self):
        chapter = status('/content/01-johnson-introduction.typ', 'compileError')
        pending = [chapter, status('/content/main.typ', 'compiling'),
                   status('/content/main.typ', 'compileSuccess')]
        self.assertEqual(wait_main_compile(pending, queue.Queue()), [chapter])
        self.assertEqual(pending, [])

    def test_selected_project_error_is_fatal(self):
        pending = [status('/content/chapter.typ', 'compileError'),
                   status('/content/main.typ', 'compileError'),
                   status('/content/main.typ', 'compileSuccess')]
        with self.assertRaisesRegex(AssertionError, 'main.typ'):
            wait_main_compile(pending, queue.Queue())

    def test_foreign_success_cannot_satisfy_barrier(self):
        inbox = queue.Queue()
        inbox.put(status('/content/main.typ', 'compileError'))
        with self.assertRaisesRegex(AssertionError, 'main.typ'):
            wait_main_compile([status('/content/chapter.typ', 'compileSuccess')],
                              inbox)


if __name__ == '__main__':
    unittest.main()
