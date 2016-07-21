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

        print name

        with open(os.path.join(TESTS_DIR, name)) as f:
            Kconfig, testcases = prog.split(f.read())

        Kconfig_path = os.path.join(tmpdir, '.Kconfig')
        with open(Kconfig_path, 'w') as f:
            f.write(Kconfig)

        testcases = list(yaml.load_all(testcases))

        nr_success = 0
        for i, testcase in enumerate(testcases):
            if not testcase:
                testcase = {}

            input_path = os.path.join(tmpdir, '.satconfig')
            with open(input_path, 'w') as f:
                for var, value in testcase.get('input', {}).iteritems():
                    print >>f, 'CONFIG_%s=%s' % (var, value)

            output_path = os.path.join(tmpdir, '.output')
            p = subprocess.Popen([
                'env', 'KCONFIG_CONFIG=' + output_path,
                'scripts/kconfig/satconfig', Kconfig_path, input_path,
            ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdoutdata, stderrdata = p.communicate()

            success = True
            if p.returncode == 0:
                config = {}
                with open(output_path) as f:
                    lines = f.read().splitlines()

                for line in lines:
                    if not line.startswith('CONFIG_'):
                        continue

                    var, value = line[len('CONFIG_'):].strip().split('=')
                    config[var] = value

                if testcase.get('failure'):
                    success = False
                    print " - %u. error: expected no solution" % (i, )
                    for var, value in config.iteritems():
                        print "      got %s=%s" % (var, value)
                else:

                    for var, value in testcase.get('output', {}).iteritems():
                        config_value = config.get(var, 'n')
                        if config_value != value:
                            print " - %u. error: expected %s=%s, got %s=%s" % (i, var, value, var, config_value)
                            success = False
            else:
                if not testcase.get('failure'):
                    print " - %u. error: satconfig exited with return code %d" % (i, p.returncode, )
                    success = False

            if success:
                print " - %u. success" % (i, )

        print

        #print "[%2u/%2u] %s" % (nr_success, len(testcases), name)

    shutil.rmtree(tmpdir)

if __name__ == '__main__':
    main()
