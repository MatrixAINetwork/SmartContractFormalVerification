#!/usr/bin/env python

import os
import re
from sys import exit
import six
import json
import symExec
import logging
import requests
import argparse
import subprocess
import global_params
from utils import run_command
from input_helper import InputHelper

#from memory_profiler import memory_usage
#from time import sleep
def cmd_exists(cmd):
    return subprocess.call("type " + cmd, shell=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE) == 0

def compare_versions(version1, version2):
    def normalize(v):
        return [int(x) for x in re.sub(r'(\.0+)*$','', v).split(".")]
    version1 = normalize(version1)
    version2 = normalize(version2)
    if six.PY2:
        return cmp(version1, version2)
    else:
        return (version1 > version2) - (version1 < version2)

def has_dependencies_installed():
    try:
        import z3
        import z3.z3util
        z3_version =  z3.get_version_string()
        tested_z3_version = '4.5.1'
        if compare_versions(z3_version, tested_z3_version) > 0:
            logging.debug("You are using an untested version of z3. %s is the officially tested version" % tested_z3_version)
    except:
        logging.critical("Z3 is not available. Please install z3 from https://github.com/Z3Prover/z3.")
        return False

    if not cmd_exists("evm"):
        logging.critical("Please install evm from go-ethereum and make sure it is in the path.")
        return False
    else:
        cmd = "evm --version"
        out = run_command(cmd).strip()
        global_params.EVM_VERSION = re.findall(r"evm version (\d*.\d*.\d*)", out)[0]
    return True

def analyze_bytecode():
    global args

    helper = InputHelper(InputHelper.BYTECODE, source=args.source)
    inp = helper.get_inputs()[0]

    result, exit_code = symExec.run(disasm_file=inp['disasm_file'])
    helper.rm_tmp_files()

    return exit_code

def run_solidity_analysis(inputs):
    results = {}
    exit_code = 0
    for inp in inputs:
        logging.info("contract %s:", inp['contract'])
        result, return_code = symExec.run(disasm_file=inp['disasm_file'], source_map=inp['source_map'], source_file=inp['source'])

        try:
            c_source = inp['c_source']
            c_name = inp['c_name']
            results[c_source][c_name] = result
        except:
            results[c_source] = {c_name: result}

        if return_code == 1:
            exit_code = 1
    return results, exit_code

def analyze_solidity(input_type='solidity'):
    global args

    if input_type == 'solidity':
        helper = InputHelper(InputHelper.SOLIDITY, source=args.source, compilation_err=args.compilation_error, root_path=args.root_path, remap=args.remap, allow_paths=args.allow_paths)
    elif input_type == 'standard_json':
        helper = InputHelper(InputHelper.STANDARD_JSON, source=args.source, allow_paths=args.allow_paths)
    elif input_type == 'standard_json_output':
        helper = InputHelper(InputHelper.STANDARD_JSON_OUTPUT, source=args.source)
    inputs = helper.get_inputs()
    results, exit_code = run_solidity_analysis(inputs)
    helper.rm_tmp_files()

    return exit_code
def main():
    # TODO: Implement -o switch.

    global args

    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)

    group.add_argument("-s",  "--source",    type=str, help="local source file name. Solidity by default. Use -b to process evm instead. Use stdin to read from stdin.")


    parser.add_argument("--version", action="version", version="merify version 0.0.1 - Commonwealth")

    parser.add_argument("-t",   "--timeout",        help="Timeout for Z3 in ms.", action="store", type=int)
    parser.add_argument("-gl",  "--gaslimit",       help="Limit Gas", action="store", dest="gas_limit", type=int)
    parser.add_argument("-ll",  "--looplimit",      help="Limit number of loops", action="store", dest="loop_limit", type=int)
    parser.add_argument("-dl",  "--depthlimit",     help="Limit DFS depth", action="store", dest="depth_limit", type=int)
    parser.add_argument("-glt", "--global-timeout", help="Timeout for symbolic execution", action="store", dest="global_timeout", type=int)
    parser.add_argument("-ap",  "--allow-paths",    help="Allow a given path for imports", action="store", dest="allow_paths", type=str)
    parser.add_argument("-rp",   "--root-path",     help="Root directory path used for the online version", action="store", dest="root_path", type=str)
    parser.add_argument("-rmp", "--remap",          help="Remap directory paths", action="store", type=str)
    parser.add_argument("-td", "--targetDepth" ,    help= "The detect depth of target",action="store", dest="target_depth", type=int)
    parser.add_argument("-md", "--modifierDepth",   help = "The detect depth of modifier",action="store", dest="modifier_depth", type=int)
    parser.add_argument( "-db",  "--debug",                  help="Display debug information", action="store_true")
    parser.add_argument( "-st",  "--state",                  help="Get input state from state.json", action="store_true")
    parser.add_argument( "-v",   "--verbose",                help="Verbose output, print everything.", action="store_true")
    parser.add_argument( "-pl",  "--parallel",               help="Run Merify in parallel. Note: The performance may depend on the contract", action="store_true")
    parser.add_argument( "-b",   "--bytecode",               help="read bytecode in source instead of solidity file.", action="store_true")
    parser.add_argument( "-sj",  "--standard-json",          help="Support Standard JSON input", action="store_true")
    parser.add_argument( "-ce",  "--compilation-error",      help="Display compilation errors", action="store_true")
    parser.add_argument( "-eval", "--eval",        help="Support no docx for testing contracts", action="store_true")
    parser.add_argument("-reportfile",   "--reportfile",     help="Report Name for the report", action="store", dest="reportfile", type=str)

    args = parser.parse_args()

    if args.root_path:
        if args.root_path[-1] != '/':
            args.root_path += '/'
    else:
        args.root_path = ""

    args.remap = args.remap if args.remap else ""
    args.allow_paths = args.allow_paths if args.allow_paths else ""

    if args.timeout:
        global_params.TIMEOUT = args.timeout

    if args.verbose:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig(level=logging.INFO)
    global_params.INPUT_STATE = 1 if args.state else 0
    global_params.DEBUG_MODE = 1 if args.debug else 0
    global_params.PARALLEL = 1 if args.parallel else 0
    global_params.EVAL = 1 if args.eval else 0
    global_params.reportName = args.reportfile if args.reportfile else ""
    if args.depth_limit:
        global_params.DEPTH_LIMIT = args.depth_limit
    if args.gas_limit:
        global_params.GAS_LIMIT = args.gas_limit
    if args.loop_limit:
        global_params.LOOP_LIMIT = args.loop_limit

    if not has_dependencies_installed():
        return
    if args.target_depth:
        global_params.TARGET_DEPTH = args.target_depth
    if args.modifier_depth:
        global_params.MODIFIER_DEPTH = args.modifier_depth

    exit_code = 0
    if args.bytecode:
        exit_code = analyze_bytecode()
    elif args.standard_json:
        exit_code = analyze_solidity(input_type='standard_json')
    else:
        exit_code = analyze_solidity()
    exit(exit_code)

if __name__ == '__main__':
    main()

