#! /usr/bin/env python

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
import yaml

TESTS_DIR = os.path.join(os.path.dirname(__file__), 'satconf-tests')

def main():
    parser = argparse.ArgumentParser()
    args = parser.parse_args()

    prog = re.compile(r'^===testcases$', flags=re.M)

    tmpdir = tempfile.mkdtemp()

    for name in sorted(os.listdir(TESTS_DIR)):
        if not name.startswith('Kconfig.'):
            continue

        with open(os.path.join(TESTS_DIR, name)) as f:
            Kconfig, testcases = prog.split(f.read())

        Kconfig_path = os.path.join(tmpdir, '.Kconfig')
        with open(Kconfig_path, 'w') as f:
            f.write(Kconfig)

        testcases = list(yaml.load_all(testcases))

        nr_success = 0
        for testcase in testcases:
            if not testcase:
                testcase = {}

            input_path = os.path.join(tmpdir, '.satconfig')
            with open(input_path, 'w') as f:
                for var, value in testcase.get('input', {}).iteritems():
                    print >>f, 'CONFIG_%s=%s' % (var, value)

            output_path = os.path.join(tmpdir, '.output')
            p = subprocess.Popen([
                'env', 'KCONFIG_CONFIG=' + output_path,
                'scripts/kconfig/satconf', Kconfig_path, input_path,
            ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdoutdata, stderrdata = p.communicate()

            success = True
            if p.returncode == 0:
                if testcase.get('failure'):
                    success = False
                else:
                    config = {}
                    with open(output_path) as f:
                        for line in f:
                            if not line.startswith('CONFIG_'):
                                continue

                            var, value = line[len('CONFIG_'):].strip().split('=')
                            config[var] = value

                    for var, value in testcase.get('output', {}).iteritems():
                        config_value = config.get(var, 'n')
                        if config_value != value:
                            print "Expected %s=%s, got %s=%s" % (var, value, var, config_value)
                            success = False
            else:
                if not testcase.get('failure'):
                    success = False

            if success:
                nr_success += 1
            else:
                print stdoutdata
                print stderrdata

        print "[%2u/%2u] %s" % (nr_success, len(testcases), name)

    shutil.rmtree(tmpdir)

if __name__ == '__main__':
    main()
