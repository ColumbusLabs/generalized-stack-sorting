"""Offline package integrity tests. These never launch Lean or access the network."""
from pathlib import Path
import shutil
import tempfile
import unittest
import replay

class IntegrityTests(unittest.TestCase):
    def test_exact_packet(self):
        replay.verify(); replay.verify_files()
    def test_comments_and_strings(self):
        text='/-- nested /- sorry -/ axiom -/\nimport Std -- unsafe\ndef s := "admit"\n'
        self.assertEqual(replay.imports(text),['Std'])
        for word in ['sorry','axiom','unsafe','admit']: self.assertNotIn(word,replay.code_only(text))
    def test_multiline_nested_comments(self):
        self.assertEqual(replay.imports('/- a\n/-b-/\n-/\nimport Std\nimport Lean.Elab.Tactic.Omega\n'),['Std','Lean.Elab.Tactic.Omega'])
    def test_unterminated_comment(self):
        with self.assertRaises(ValueError): replay.code_only('/-')
    def test_manifest_tampering(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'SOURCE_MANIFEST.json').write_bytes((replay.ROOT/'SOURCE_MANIFEST.json').read_bytes()+b' ')
            with self.assertRaisesRegex(ValueError,'manifest digest'): replay.verify(root)
    def test_missing_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); shutil.copyfile(replay.ROOT/'SOURCE_MANIFEST.json',root/'SOURCE_MANIFEST.json')
            with self.assertRaisesRegex(ValueError,'Missing or symlink source'): replay.verify(root)
    def test_source_tampering(self):
        manifest=replay.verify(); row=manifest['modules'][0]
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'certificate'; root.mkdir(); shutil.copyfile(replay.ROOT/'SOURCE_MANIFEST.json',root/'SOURCE_MANIFEST.json')
            path=root/row['path']; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes((replay.ROOT/row['path']).read_bytes()+b'\n')
            with self.assertRaisesRegex(ValueError,'Source bytes changed'): replay.verify(root)
    def test_forbidden_path(self):
        with self.assertRaisesRegex(ValueError,'Unexpected source location'): replay.source_path(replay.ROOT,'/etc/passwd')

if __name__=='__main__': unittest.main()
