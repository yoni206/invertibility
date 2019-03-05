#!/usr/bin/env python

import argparse
import csv
import os
import sys

SUBST_MAP = {
    'bvult' : '<',
    'bvugt' : '>',
    'bvule' : '<=',
    'bvuge' : '>=',
    'bvslt' : 'intslt',
    'bvsgt' : 'intsgt',
    'bvsle' : 'intsle',
    'bvsge' : 'intsge',

    'bvnot' : 'intnot',
    'bvneg' : 'intneg',

    'bvand' : 'intand',

    'bvor' : 'intor',
    'bvxor' : 'intxor',

    'bvshl' : 'intshl',
    'bvlshr' : 'intlshr',
    'bvashr' : 'intashr',

    'bvsub'  :  'intsub',
    'bvadd' : 'intadd',
    'bvmul' : 'intmul',

    'uremtotal' : 'intmodtotal',
    'udivtotal' : 'intudivtotal',

    'bvurem' : 'intmodtotal',
    'bvudiv' : 'intudivtotal',

    'bvconcat' : 'intconcat',
    'extract' : 'intextract',

#    '(_ bv0 4)' : '0',
#    '(_ bv1 4)' : '1',
#    '(_ bv4 4)' : 'k',

#    '(bvnot (_ bv0 4))' : '(intmax {k})',
#    'max' : '(intmaxs k)',
#    'min' : '(intmins k)',
#    '#b1000' : '(intmins k)',
#    '#b0000' : '0',
#    '#b0111' : '(intmaxs k)',
#    '(BitVec 4)' : 'Int'
}

TYPE_RULES = {
    'bvnot' : lambda x : x[0],
    'bvneg' : lambda x : x[0],

    'bvand' : lambda x : x[0],

    'bvor' : lambda x : x[0],
    'bvxor' : lambda x : x[0],

    'bvshl' : lambda x : x[0],
    'bvlshr' : lambda x : x[0],
    'bvashr' : lambda x : x[0],

    'bvsub'  : lambda x : x[0],
    'bvadd' : lambda x : x[0],
    'bvmul' : lambda x : x[0],

    'bvurem' : lambda x : x[0],
    'bvudiv' : lambda x : x[0],

    'concat' : lambda x : x[0] + x[1],
    'extract' : lambda x : x[1] - x[0] + 1,
}

def get_subst(s):
    if s in SUBST_MAP:
        return SUBST_MAP[s]
    return s

def die(msg):
    print('[error] gen-input-problems.py: {}'.format(msg))
    sys.exit(1)

#def startswith(s, prefixes):
#    for p in prefixes:
#        if s.startswith(p):
#            return True
#    return False

def compact(l):
    compacted = []
    sym = []
    for e in l:
        if isinstance(e, list) or e == ' ' or e == '\n':
            # End of symbol
            if sym:
                compacted.append(''.join(sym))
                sym = []
            # Keep newlines
            if e != ' ':
                compacted.append(e)
        else:
            sym.append(e)

    if sym:
        compacted.append(''.join(sym))

    assert ' ' not in compacted
    return compacted


def tokenize(s):
    exprs = []
    tokens = []
    cur_expr = None
    for char in s:
        # Open s-expression
        if char == '(':
            cur_expr = []
            exprs.append(cur_expr)
        # Close s-expression
        elif char == ')':
            cur_expr = exprs.pop()
            cur_expr = compact(cur_expr)
            if exprs:
                exprs[-1].append(cur_expr)
                cur_expr = exprs[-1]
            else:
                tokens.append(cur_expr)
                cur_expr = None
        elif exprs:
            assert cur_expr is not None
            cur_expr.append(char)
        else:
            tokens.append(char)

    return tokens


def sexpr_str(sexpr, indent):
    exprs = []
    for t in sexpr:
        if isinstance(t, list):
            t = sexpr_str(t, indent + 1)
        if t == '\n':
            t = '{}{}'.format(t, ' ' * indent)
        exprs.append(t)
    return '({})'.format(' '.join(exprs))

def formula_str(tokens):
    exprs = []
    for t in tokens:
        if isinstance(t, list):
            t = sexpr_str(t, 0)
        exprs.append(t)
    return ''.join(exprs)

def is_bv_sort(l):
    return len(l) == 3 and l[0] == '_' and l[1] == 'BitVec'

def is_bv_const(l):
    return len(l) == 3 and l[0] == '_' and l[1].startswith('bv')

def translate(tokens, symbols, bwvars, extracts):
    if isinstance(tokens, list):
        bws = []
        exprs = []
        for t in tokens:
            e, k = translate(t, symbols, bwvars, extracts)
            exprs.append(e)
            bws.append(k)

        # Determine bit-width of operator
        k = None
        if tokens and isinstance(tokens[0], str) and tokens[0] in TYPE_RULES:
            type_rule = TYPE_RULES[tokens[0]]
            k = type_rule(bws[1:])

        if is_bv_sort(exprs):
            exprs = 'Int'

        elif is_bv_const(exprs):
            k = int(exprs[2])
            exprs = exprs[1][2:]

        # extract
        elif len(exprs) == 4 and exprs[0] == '_' and exprs[1] == 'extract':
            # Skip the _
            exprs = [exprs[1], exprs[2], exprs[3]]
            k = int(exprs[2]) - int(exprs[3]) + 1

        # declare-fun/define-fun
        elif exprs and exprs[0] in ['declare-fun', 'define-fun'] \
                and is_bv_sort(tokens[3]):
            assert exprs[1] not in symbols
            symbols[exprs[1]] = tokens[3][2]
            k = int(tokens[3][2])

        # declare-const
        elif exprs and exprs[0] == 'declare-const':
            assert exprs[1] not in symbols
            assert len(tokens[2]) == 3 # BitVec sort
            symbols[exprs[1]] = tokens[2][2]
            k = int(tokens[2][2])

        # sorted vars (x (_ BitVec 10))
        elif len(exprs) == 2 and exprs[1] == 'Int' and exprs[0] not in symbols:
            assert is_bv_sort(tokens[1])
            symbols[tokens[0]] = tokens[1][2]
            k = int(tokens[1][2])

        # Add bit-width sort variables
        if exprs and isinstance(exprs[0], str) and exprs[0].startswith('int'):
            bwvar = 'k{}'.format(k)
            bwvars.add(bwvar)
            #exprs[0] = '{} {}'.format(exprs[0], bwvar)
            # TODO: handle multiple bit-width sorts
            exprs[0] = '{} {}'.format(exprs[0], 'k')
        return exprs, k

    # Convert #b... constants
    if tokens.startswith('#b'):
        bits = tokens[2:]
        return str(int(bits, 2)), len(bits)

    k = None
    if tokens in symbols:
        k = symbols[tokens]

    return get_subst(tokens), k

def parse_sexpr(formula):
    tokens = tokenize(formula)
    symbols = {}
    extracts = {}
    bwvars = {}
    concats = {}
    tokens_translated, _ = translate(tokens, symbols, bwvars, extracts)
    #print(formula_str(tokens), end='')
    print(formula_str(tokens_translated), end='')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('formula')
    args = ap.parse_args()

    if not os.path.isfile(args.formula):
        die("SMT2 file '{}' does not exist".format(args.formula))

    with open(args.formula) as file:
        formula = file.read()
        parse_sexpr(formula)



if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print()
        sys.exit('Interrupted')
