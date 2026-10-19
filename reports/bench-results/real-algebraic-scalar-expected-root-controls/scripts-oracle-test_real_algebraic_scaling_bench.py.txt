"""Exact scalar fixtures, cleanup, and rejection at the persistent boundary."""
import json
import subprocess
import sys
import unittest
from pathlib import Path
from scripts.oracle import real_algebraic_scaling_bench as bench


class Scaling(unittest.TestCase):
    def test_all_sizes_and_cleanup(self):
        for factory in (bench.Flint,bench.Z3):
            for op,sizes in [('add',(2,4,8)),('sqrt',(2,4,8)),('compare',(4,16,64,256)),
                             ('floor',(4,16,64,256)),('ceil',(4,16,64,256)),
                             ('rational',(16,64,256,1024))]:
                if factory is bench.Z3 and op in ('floor','ceil'):
                    continue
                for size in sizes:
                    endpoint=factory(op,size)
                    try:
                        for _ in range(2):
                            self.assertTrue(endpoint.run(),(factory,op,size))
                            if factory is bench.Flint:
                                self.assertEqual(len(endpoint.oracle.owned),endpoint.retained)
                    finally:
                        endpoint.close()

    def test_wrong_expected_result_is_detected(self):
        for factory in (bench.Flint,bench.Z3):
            endpoint=factory('add',4)
            try:
                endpoint.expected=(endpoint.oracle.number(0) if factory is bench.Flint else endpoint.num(0))
                self.assertFalse(endpoint.run())
            finally:
                endpoint.close()

    def test_persistent_process_owns_contexts_without_shutdown_cycle(self):
        good=[dict(operation='sqrt',size=4),dict(operation='compare',size=64),
              dict(operation='rational',size=1024)]
        bad=[dict(operation='sqrt',size=True),dict(operation='floor',size=3),
             dict(operation='unknown',size=4),dict(operation='compare',size=4,control=1),{}]
        for tool in ('flint','z3'):
            completed=subprocess.run([sys.executable,str(Path(bench.__file__)),'--tool',tool],
                input='\n'.join(map(json.dumps,good+bad))+'\ninvalid JSON\n',
                capture_output=True,text=True,check=True)
            replies=[json.loads(row) for row in completed.stdout.splitlines()]
            self.assertEqual(replies[:3],[dict(ok=True,result=True)]*3)
            self.assertEqual(len(replies),len(good+bad)+1)
            self.assertTrue(all(not reply['ok'] and 'result' not in reply for reply in replies[3:]))

    def test_z3_rounding_is_not_emulated(self):
        with self.assertRaisesRegex(ValueError,'no matching'):
            bench.Z3('floor',16)


if __name__=='__main__':unittest.main()
