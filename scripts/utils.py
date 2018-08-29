import sys
import os

L_PREFIX = "(=> (SC s t) (exists ((x (_ BitVec 4)))"
SC_PREFIX = "(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool"

def map_l_to_sc(dir_of_SC_verification, prefix):
    result = {}
    files = os.listdir(dir_of_SC_verification)
    files_4bit = [f for f in files if (f.endswith("_4bit.smt2") and "bvconcat" not in f)]
    for f in files_4bit:
        name = f.split(".")[0]
        name = name.replace("check", prefix)
        path = dir_of_SC_verification + "/" + f
        l, SC = get_l_SC_from_file(path)
        result[name] = [l, SC]
    return result

def get_l_SC_from_file(path):
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
            actual_l = actual_l.replace("x", "(inv s t)")
    assert (actual_sc != "" and actual_l != "")
    return [actual_l, actual_sc]

def substitute(string, substitutions):
    result = string
    for old, new in substitutions.items():
        if new is not None:
            result = result.replace(old, new)
        else:
            if old in result:
                return None
    return result


