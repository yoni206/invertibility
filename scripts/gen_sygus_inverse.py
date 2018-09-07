import sys
import os
import utils

SYNTAX_PH = "<syntax>"
L_PH = "<l>"
SC_PH = "<SC>"
TEMPLATE_PATH = "templates/template.sy"
with open(TEMPLATE_PATH, 'r') as myfile: TEMPLATE=myfile.read()

def main(dir_of_syntaxes, dir_of_SC_verification, generated_smt_dir):
    if os.path.exists(generated_smt_dir):
        print('directory exists, aborting')
        return
    os.makedirs(generated_smt_dir)
    syntaxes = generate_syntaxes(dir_of_syntaxes) #name-to-real-syntax
    make_syntaxes_dirs(generated_smt_dir, syntaxes.keys())
    l_name_to_l_sc = utils.map_l_to_sc(dir_of_SC_verification, "find_inv", True) #file_name -> <l,sc>
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
    smt = utils.substitute(TEMPLATE, substitutions)
    return smt

def save_smt(smt, generated_smt_dir, syntax_name, l_name):
    smt_file_path = generated_smt_dir + "/" + syntax_name + "/" +  l_name + ".sy"
    smt_file = open(smt_file_path, "w")
    smt_file.write(smt)
    smt_file.close()

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print('arg1: dir of syntaxes\narg2: dir of SC verification\narg3: dir of generated smt files')
        sys.exit(1)
    dir_of_syntaxes = sys.argv[1]
    dir_of_SC_verification = sys.argv[2]
    generated_smt_dir = sys.argv[3]
    main(dir_of_syntaxes, dir_of_SC_verification, generated_smt_dir)
