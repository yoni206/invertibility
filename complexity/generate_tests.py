import sys
import os
TEMPLATE_PATH = "template.smt2"
L_PH = "<l>"
SC_PH = "<SC>"
n_PH = "<n>"
with open(TEMPLATE_PATH, 'r') as myfile: TEMPLATE=myfile.read()

def main():
    directory = "smt/eq"
    l="(define-fun l ((x (_ BitVec <n>)) (s (_ BitVec <n>)) (t (_ BitVec <n>))) Bool (= (bvshl x s) t))"
    SC = "(define-fun SC ((s (_ BitVec <n>)) (t (_ BitVec <n>))) Bool (= (bvand (bvshl (bvnot (_ bv0000 <n>)) s) t) t))"

    #directory = "smt/ne"
    #l="(define-fun l ((x (_ BitVec <n>)) (s (_ BitVec <n>)) (t (_ BitVec <n>))) Bool (distinct (bvshl x s) t))"
    #SC = "(define-fun SC ((s (_ BitVec <n>)) (t (_ BitVec <n>))) Bool (not (= (bvor (bvshl (_ bv7 <n>) s) t) (_ bv0 <n>))))"
    for n in range(1, 100):
        smt = generate_smt(n, l, SC)
        save_smt(smt, directory, "vef"+str(n))


def generate_smt(n, l, sc):
    substitutions = {}
    substitutions[L_PH] = l
    substitutions[SC_PH] = sc
    smt = substitute(TEMPLATE, substitutions)
    substitutions = {}
    substitutions[n_PH] = str(n)
    smt = substitute(smt, substitutions)
    return smt

def save_smt(smt, generated_smt_dir, f_name):
    smt_file_path = generated_smt_dir + "/" +  f_name + ".smt2"
    smt_file = open(smt_file_path, "w")
    smt_file.write(smt)
    smt_file.close()

def substitute(string, substitutions):
    result = string
    for old, new in substitutions.items():
        result = result.replace(old, new)
    return result

if __name__ == "__main__":
    main()
