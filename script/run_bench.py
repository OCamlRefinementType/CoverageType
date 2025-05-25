import sys
import argparse
import os
import subprocess

cmd_prefix = ["dune", "exec", "--", "bin/main.exe", "type-check"]

workdir = ""

meta_config_file = "meta-config.json"

def invoc_cmd(verbose, cmd, output_file):
    if output_file is not None:
        if (verbose):
            print(" ".join(cmd + [">>", output_file]))
        with open(output_file, "a+") as ofile:
            try:
                subprocess.run(cmd, stdout=ofile)
            except subprocess.CalledProcessError as e:
                print(e.output)
    else:
        if (verbose):
            print(" ".join(cmd))
        try:
            subprocess.run(cmd)
        except subprocess.CalledProcessError as e:
            print(e.output)

def run(source_file, verbose):
    invoc_cmd(verbose, cmd_prefix + [source_file], None)

if __name__ == '__main__':
    try:
        if sys.argv[2] == "verbose":
            verbose = True
    except:
        verbose = False
    run(sys.argv[1], verbose)
