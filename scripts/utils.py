import re
import sys
import os

L_PREFIX = "(=> (SC s t) (exists ((x (_ BitVec 4)))"
SC_PREFIX = "(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool"

def map_l_to_sc(dir_of_SC_verification, prefix, x_to_inv = False):
    result = {}
    files = os.listdir(dir_of_SC_verification)
    files_4bit = [f for f in files if (f.endswith("_4bit.smt2") and "bvconcat" not in f)]
    for f in files_4bit:
        name = f.split(".")[0]
        name = name.replace("check", prefix)
        path = dir_of_SC_verification + "/" + f
        l, SC = get_l_SC_from_file(path, x_to_inv)
        result[name] = [l, SC]
    return result

def get_l_SC_from_file(path, x_to_inv):
    lines_list = open(path).read().splitlines()
    actual_sc = ""
    actual_l = ""
    for i in range(0, len(lines_list)):
        line = lines_list[i].strip()
        if line.startswith(SC_PREFIX):
            actual_sc = lines_list[i+1]
        if line.startswith(L_PREFIX):
            actual_l = line[len(L_PREFIX):-2]
            #replace x with inverse
            if x_to_inv:
                actual_l = actual_l.replace("x", "(inv s t)")
    assert (actual_sc != "" and actual_l != "")
    return [actual_l, actual_sc]

#escape is used to avoid double-substitutions
#make sure it does not occur in string nor in substitutions
#e.g.if string = aa and substitutions =  {'a->ab', 'b->c'}
#the desired result of this function is abab, and not acac.
def substitute(string, substitutions, escape='@'):
    keys = sorted(substitutions.keys(), key=len, reverse=True)
    keys_to_escaped_keys = escape_keys(keys, escape)
    local_substitutions = get_local_substitutions(substitutions, keys_to_escaped_keys)
    local_string = get_local_string(string, keys_to_escaped_keys)
    result = local_string
    for old in local_substitutions.keys():
        new = local_substitutions[old]
        if new is not None:
            result = result.replace(old, new)
        else:
            if old in result:
                return None
    return result




def get_file_or_dir_name_no_ext(path):
    full_name = path.split("/")[-1]
    if "." in full_name:
        assert(full_name.count(".") == 1)
        result = full_name.split(".")[0]
    else:
        result = full_name
    return result
#HELPER FUNCTIONS


def escape_keys(keys, escape):
    #all prefixes should have the same length
    digits = len(str(len(keys)))
    i = 0
    sorted_keys = sorted(keys, key=len, reverse=True)
    result = {}
    for key in sorted_keys:
        result[key] = escape + str(i).zfill(digits) + escape
        i = i+1
    return result

def get_local_substitutions(substitutions, keys_to_escaped_keys):
    result = {}
    keys = sorted(substitutions.keys(), key=len, reverse=True)
    for key in keys:
        new_key = keys_to_escaped_keys[key]
        result[new_key] = substitutions[key]
    return result

def get_local_string(string, keys_to_escaped_keys):
    result = string
    keys = sorted(keys_to_escaped_keys.keys(), key=len, reverse=True)
    for key in keys:
        result = result.replace(key, keys_to_escaped_keys[key])
    return result


#find all beinning indexes of substring in s.
def find_all(s, substring):
    result = [m.start() for m in re.finditer(substring, s)]
    return result

def find_parens(s):
    toret = {}
    pstack = []

    for i, c in enumerate(s):
        if c == '(':
            pstack.append(i)
        elif c == ')':
            if len(pstack) == 0:
                raise IndexError("No matching closing parens at: " + str(i))
            toret[pstack.pop()] = i

    if len(pstack) > 0:
        raise IndexError("No matching opening parens at: " + str(pstack.pop()))

    return toret
