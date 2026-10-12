import importlib.util
import json
from pathlib import Path
import os
import sys
import unittest

DIRECTORY=Path(__file__).resolve().parents[1]/'evidence'/'bounded-rank-four-equations'/'author'


def load(name):
    sys.path.insert(0,str(DIRECTORY))
    try:
        spec=importlib.util.spec_from_file_location('d4_test_'+name,DIRECTORY/(name+'.py'))
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        return module
    finally:
        sys.path.pop(0)


class BoundedRankFourEquationTests(unittest.TestCase):
    def test_exact_system_shape(self):
        data=json.loads((DIRECTORY/'d4-univariate-system.json').read_text())
        self.assertEqual(data['root'],[1,0,0,[0]])
        self.assertEqual(len(data['equations']),4886)
        self.assertEqual(sum(map(len,data['equations'])),62208)
        self.assertEqual(max(x+y+len(children) for terms in data['equations'] for c,x,y,children in terms),4)

    def test_equation_only_coefficients_through_regression_degree(self):
        module=load('readback_d4_system');cwd=Path.cwd()
        try:
            os.chdir(DIRECTORY);result=module.readback(13)
        finally:
            os.chdir(cwd)
        self.assertEqual(result['coefficients'],[1,1,2,6,24,120,696,4434,29994,211248,1531326,11343804,85470360,652838112])
        self.assertTrue(result['zero_size_jacobian_acyclic'])
        self.assertEqual(result['constant_fixed_point_rounds'],7)

    def test_corrected_compiler_accepts_partial_clause_regression(self):
        module=load('check_d4_compiler_regression')
        self.assertTrue(module.replay(minimized=False)[0])
        self.assertTrue(module.replay(minimized=True)[0])

    def test_control_quotient_is_exact_and_small(self):
        pda=load('prune_d4_pda_returns');minimizer=load('minimize_d4_pda_controls')
        _,transitions,labels,certificate=minimizer.quotient(*pda.build_pda(with_labels=True))
        self.assertEqual(certificate['partition_sizes'],[82,154,205,211,211])
        self.assertEqual((certificate['quotient_controls'],len(transitions),len(labels)),(211,566,566))


if __name__=='__main__':
    unittest.main()
