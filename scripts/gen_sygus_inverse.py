import sys
import os
import utils

skeleton = """
(set-logic BV)
(synth-fun inv ((s (BitVec 4)) (t (BitVec 4))) (BitVec 4)
  <syntax>
)
(declare-var s (BitVec 4))
(declare-var t (BitVec 4))
(define-fun udivtotal ((a (BitVec 4)) (b (BitVec 4))) (BitVec 4) (ite (= b #x0) #xF (bvudiv a b)))
(define-fun uremtotal ((a (BitVec 4)) (b (BitVec 4))) (BitVec 4) (ite (= b #x0) a (bvurem a b)))
(define-fun min () (BitVec 4) (bvnot (bvlshr (bvnot #x0) #x1)))
(define-fun max () (BitVec 4) (bvnot min))
(define-fun l ( (s (BitVec 4)) (t (BitVec 4))) Bool <l>)
(define-fun SC ((s (BitVec 4)) (t (BitVec 4))) Bool <SC>)

"""

constraint = "(constraint (=> (SC s t) (l s t)))"
check_synth = "(check-synth)"

shared_syntaxes = {
        "syntax_d1": ["s", "t", "#x0", "#x8", "#x7", "(bvneg Start)", "(bvnot Start)", "(bvshl Start Start)"],
        "syntax_d2": ["s", "t", "#x0", "#x8", "#x7", "(bvneg Start)", "(bvnot Start)"],
        "syntax_d3": ["s", "t", "#x0", "#x8", "#x7"],
        "syntax_a": ["s", "t", "#x0", "#x8", "#x7", "(bvneg Start)", "(bvnot Start)", "(bvadd Start Start)", "(bvsub Start Start)", "(bvmul Start Start)"],
        "syntax_g": ["s", "t", "#x0", "#x8", "#x7", "(bvneg Start)", "(bvnot Start)", "(bvadd Start Start)", "(bvsub Start Start)", "(bvand Start Start)", "(bvlshr Start Start)", "(bvor Start Start)", "(bvshl Start Start)"],
        "syntax_r": ["s", "t", "#x0", "#x8", "#x7", "(bvneg Start)", "(bvnot Start)", "(bvand Start Start)", "(bvor Start Start)"]
}

#operators in each sygus file, regardless of the literal
#for each op, what are the ops that are needed for the syntax?
additional_syntax_lines = {
    "bvadd":  ["(bvadd Start Start)", "(bvsub Start Start)"],
    "bvsub":  ["(bvsub Start Start)", "(bvadd Start Start)"],
    "bvmul":  ["(bvmul Start Start)", "(bvudiv Start Start)"],
    "bvudiv": ["(bvudiv Start Start)", "(bvmul Start Start)"],
    "bvurem": ["(bvurem Start Start)", "(bvadd Start Start)"],
    "bvnot":  ["(bvnot Start)", "(bvneg Start)"], 
    "bvneg":  ["(bvneg Start)", "(bvnot Start)"], 
    "bvand":  ["(bvand Start Start)", "(bvor Start Start)"],
    "bvor":   ["(bvor Start Start)", "(bvor Start Start)"],
    "bvshl":  ["(bvshl Start Start)", "(bvlshr Start Start)", "(bvashr Start Start)"],
    "bvlshr": ["(bvlshr Start Start)", "(bvshl Start Start)", "(bvashr Start Start)"],
    "bvashr": ["(bvashr Start Start)", "(bvlshr Start Start)", "(bvshl Start Start)"]
    }

def main(dir_of_SC_verification, generated_sygus_dir):
    if os.path.exists(generated_sygus_dir):
        print('directory exists, aborting')
        return
    os.makedirs(generated_sygus_dir)
    l_name_to_l_sc = utils.map_l_to_sc(dir_of_SC_verification, "find_inv", True) #file_name -> <l,sc>
    for syn_name in shared_syntaxes:
        generate_sygus_files(syn_name, l_name_to_l_sc, generated_sygus_dir, constraint)


def generate_sygus_files(syn_name, l_name_to_l_sc, generated_sygus_dir, constraint):
        syntax_dir = generated_sygus_dir + "/" + syn_name 
        os.makedirs(syntax_dir)
        for l_name in l_name_to_l_sc.keys():
            l, sc = l_name_to_l_sc[l_name]
            syntax = gen_syntax(syn_name, l_name)
            sygus = generate_sygus(syntax, l, sc, constraint)
            save_sygus(sygus, syntax_dir, l_name)

def gen_syntax(syn_name, l_name):
    op_name = l_name.split("_")[3].replace("0","").replace("1","")
    #add relevant operators only for the dynamic syntaxes, not to the original a,g,r ones.
    if syn_name in ["syntax_a", "syntax_g", "syntax_r"]:
        syntax_lines = shared_syntaxes[syn_name]
    else:
        syntax_lines = shared_syntaxes[syn_name] + additional_syntax_lines[op_name]
    syntax_lines = list(dict.fromkeys(syntax_lines)) #remove duplicates
    syntax = "((Start (BitVec 4) ("
    syntax += "\n"
    syntax += "\n".join(syntax_lines)
    syntax += ")))"
    return syntax

def generate_sygus(syntax, l, sc, constraint):
    substitutions = {}
    substitutions["<syntax>"] = syntax
    substitutions["<l>"] = l
    substitutions["<SC>"] = sc
    result = utils.substitute(skeleton, substitutions)
    result = result + constraint + "\n"
    result = result + check_synth + "\n"
    return result

def save_sygus(sygus, syntax_dir, l_name):
    smt_file_path = syntax_dir + "/" +  l_name + ".sy"
    smt_file = open(smt_file_path, "w")
    smt_file.write(sygus)
    smt_file.close()

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: dir of SC verification\narg2: dir of generated smt files')
        sys.exit(1)
    dir_of_SC_verification = sys.argv[1]
    generated_sygus_dir = sys.argv[2]
    main(dir_of_SC_verification, generated_sygus_dir)
