import sys
import os

L_PREFIX = "(=> (SC s t) (exists ((x (_ BitVec 4)))"
SC_PREFIX = "(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool"
SYNTAX_PH = "<syntax>"
L_PH = "<l>"
SC_PH = "<SC>"
TEMPLATE_PATH = "template.sy"
with open(TEMPLATE_PATH, 'r') as myfile: TEMPLATE=myfile.read()

def main(dir_of_syntaxes, dir_of_SC_verification, generated_smt_dir):
    if os.path.exists(generated_smt_dir):
        print('directory exists, aborting')
        return
    os.makedirs(generated_smt_dir)
    syntaxes = generate_syntaxes(dir_of_syntaxes) #name-to-real-syntax
    make_syntaxes_dirs(generated_smt_dir, syntaxes.keys())
    l_name_to_l_sc = map_l_to_sc(dir_of_SC_verification) #file_name -> <l,sc>
    generate_smts(syntaxes, l_name_to_l_sc, generated_smt_dir)

def make_syntaxes_dirs(generated_smt_dir, syntaxes_names):
    for name in syntaxes_names:
        os.makedirs(generated_smt_dir + "/" + name)

def generate_syntaxes(dir_of_syntaxes):
    result = {}
    files = os.listdir(dir_of_syntaxes)
    for f in files:
        name = f.split(".")[0]
        path = dir_of_syntaxes + "/" + f
        with open(path, 'r') as myfile:
            syntax=myfile.read()
        result[name]=syntax
    return result

def map_l_to_sc(dir_of_SC_verification):
    result = {}
    files = os.listdir(dir_of_SC_verification)
    files_4bit = [f for f in files if (f.endswith("_4bit.smt2") and "bvconcat" not in f)]
    for f in files_4bit:
        name = f.split(".")[0]
        name = name.replace("check", "find_inv")
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

def generate_smts(syntaxes, l_name_to_l_sc, generated_smt_dir):
    for syntax_name in syntaxes.keys():
        syntax = syntaxes[syntax_name]
        for l_name in l_name_to_l_sc.keys():
            l, sc = l_name_to_l_sc[l_name]
            smt = generate_smt(syntax, l, sc)
            save_smt(smt, generated_smt_dir, syntax_name, l_name)

def generate_smt(syntax, l, sc):
    substitutions = {}
    substitutions[SYNTAX_PH] = syntax
    substitutions[L_PH] = l
    substitutions[SC_PH] = sc
    smt = substitute(TEMPLATE, substitutions)
    return smt

def save_smt(smt, generated_smt_dir, syntax_name, l_name):
    smt_file_path = generated_smt_dir + "/" + syntax_name + "/" +  l_name + ".sy"
    smt_file = open(smt_file_path, "w")
    smt_file.write(smt)
    smt_file.close()

def substitute(string, substitutions):
    result = string
    for old, new in substitutions.items():
        result = result.replace(old, new)
    return result

if __name__ == "__main__":
    dir_of_syntaxes = sys.argv[1]
    dir_of_SC_verification = sys.argv[2]
    generated_smt_dir = sys.argv[3]
    main(dir_of_syntaxes, dir_of_SC_verification, generated_smt_dir)
