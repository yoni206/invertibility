#!/usr/bin/env python

import argparse
import os
import sys

from bv_to_int import tokenize, translate, formula_str

REWRITE_TEMPLATE = """(forall ({vars})
  (=>
   {guard}
   {rewrite}
  )
 )
"""

def die(msg):
    print('[error] gen-input-problems.py: {}'.format(msg))
    sys.exit(1)


def translate_to_int(sexpr, symbols={}):
    tokens = tokenize(sexpr)
    extracts = {}
    bwvars = set()
    translated_tokens, _ = translate(tokens, symbols, bwvars, extracts)
    return formula_str(translated_tokens)

def generate_problem(check, header):
    formula = []
    formula.append(header)
    formula.append(';; problem start')
    formula.append('(assert two_to_the_is_ok)')
    formula.append(check)
    formula.append('(check-sat)')
    formula.append('(exit)')
    return '\n'.join(formula)


def rewrite_forall(rewrite):
    assert rewrite.startswith('(rewrite ')

    # TODO: properly detect variables
    vars = []
    if ' s' in rewrite:
        vars.append('s')
    if ' t' in rewrite:
        vars.append('t')

    guard = ['(is_bv_var k {})'.format(x) for x in vars]
    guard.append('(is_bv_width k)')

    if len(guard) >= 2:
        guard = '(and {})'.format(' '.join(guard))
    else:
        guard = guard[0]

    vars.append('k')
    vars_sorted = ['({} Int)'.format(x) for x in vars]

    rw = translate_to_int(rewrite)
    rw = rw.replace('rewrite', '=')
    return REWRITE_TEMPLATE.format(
            vars=' '.join(vars_sorted),
            guard=guard,
            rewrite=rw)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bvbenchmarks')
    ap.add_argument('headers')
    ap.add_argument('out')
    ap.add_argument('--helpers')
    ap.add_argument('--axioms')
    ap.add_argument('--axioms-rw')
    ap.add_argument('--consistent',default=False,action='store_true')
    args = ap.parse_args()

    if not os.path.isdir(args.bvbenchmarks):
        die("dir '{}' does not exist".format(args.bvbenchmarks))

    if not os.path.isdir(args.headers):
        die("Headers dir '{}' does not exist".format(args.headers))

    if os.path.isdir(args.out):
        die("Directory '{}' already exists".format(args.out))

    with open(args.header) as file:
        header = file.read()

    if args.helpers:
        with open(args.helpers) as file:
            helpers = file.read()
            header = '{}\n\n;; HELPERS\n{}\n\n'.format(header, helpers)

    if args.axioms:
        with open(args.axioms) as file:
            axioms = file.read()
            header = '{}\n\n;; CUSTOM AXIOMS\n{}\n\n'.format(header, axioms)

    if args.axioms_rw:
        with open(args.axioms_rw) as file:
            axioms = []
            vars = ['({} Int)'.format(x) for x in ['k', 's', 't']]
            for rewrite in file:
                rewrite = rewrite.strip()
                if rewrite.startswith(';'):
                    continue


                axioms.append('; from rewrite: {}'.format(rewrite))
                axioms.append('(assert {})'.format(rewrite_forall(rewrite)))

            header = '{}\n\n;; REWRITE AXIOMS\n{}\n\n'.format(
                        header,'\n'.join(axioms))

    with open(args.rewrites) as file:
        i = 1
        os.mkdir(args.out)
        for rewrite in file:
            rewrite = rewrite.strip()
            check = ''
            if not args.consistent:
                check = '(assert (not {}))'.format(rewrite_forall(rewrite))
            problem = generate_problem(check, header)

            path = os.path.join(args.out, '{}.smt2'.format(i))
            i += 1
            with open(path, 'w') as outfile:
                outfile.write(problem)

            if args.consistent:
                break


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print()
        sys.exit('Interrupted')
