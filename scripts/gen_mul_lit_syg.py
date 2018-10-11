import sys
import os
import utils

L1_PH = "<l1>"
L2_PH = "<l2>"
SC1_PH = "<SC1>"
SC2_PH = "<SC2>"
EQUALITY_ASSUMPTIONS_PH = "<equality_assumptions>"

def main(template_path, dir_of_SC_verification, result_dir):
    if os.path.exists(result_dir):
        print('directory exists, aborting')
        return
    os.makedirs(result_dir)
    with open(template_path, 'r') as myfile:
        template = myfile.read()
        myfile.close()
    l_name_to_l_sc = utils.map_l_to_sc(dir_of_SC_verification, "find_inv", False) 
    generate_sygus_files(result_dir, template, l_name_to_l_sc)

def generate_sygus_files(result_dir, template, l_name_to_l_sc):
    l_names = sorted(list(l_name_to_l_sc))
    for i in range(0, len(l_names)):
        for j in range(i+1, len(l_names)):
            l_name_1 = l_names[i]
            l_name_2 = l_names[j]
            l1, SC1 = l_name_to_l_sc[l_name_1]
            l2, SC2 = l_name_to_l_sc[l_name_2]
            gen_sygus_for_pair(result_dir, template, l_name_1, l1, SC1, l_name_2, l2, SC2)

def fix_name(name):
    return name[len("find_inv_"):-len("_4bit")]

def gen_sygus_for_pair(result_dir, template, l_name_1, l1, SC1, l_name_2, l2, SC2):

    #keep essense of names:
    l_name_1 = fix_name(l_name_1)
    l_name_2 = fix_name(l_name_2)
    l_name = l_name_1 + "_" + l_name_2

    #define the substitutions
    base_substitutions = {}
    base_substitutions[L1_PH] = l1
    base_substitutions[L2_PH] = l2
    base_substitutions[SC1_PH] = SC1
    base_substitutions[SC2_PH] = SC2
    base_sy = utils.substitute(template, base_substitutions)

    #generate the sygus queries
    #s1, s2, t1, t2 may or may not be equal
    plain_sy = utils.substitute(base_sy, {EQUALITY_ASSUMPTIONS_PH: "true"})
    #s1=s2
    s_sy = utils.substitute(base_sy, {EQUALITY_ASSUMPTIONS_PH: "(= s1 s2)"})
    #t1=t2
    t_sy = utils.substitute(base_sy, {EQUALITY_ASSUMPTIONS_PH: "(= t1 t2)"})
    #s1=s2 and t1=t2
    st_sy = utils.substitute(base_sy, {EQUALITY_ASSUMPTIONS_PH: "(and (= s1 s2) (= t1 t2))"})
    #save
    save_string_to_file_in_dir(plain_sy, l_name + "_plain.sy", result_dir)
    save_string_to_file_in_dir(s_sy, l_name + "_s.sy", result_dir)
    save_string_to_file_in_dir(t_sy, l_name + "_t.sy", result_dir)
    save_string_to_file_in_dir(st_sy, l_name + "_st.sy", result_dir)

def save_string_to_file_in_dir(s, f, d):
    sy_file = open(d + "/" + f, "w")
    sy_file.write(s)
    sy_file.close()

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("arg1: template path\narg2: dir of SC verification\narg3: result dir")
        sys.exit(1)
    template_path = sys.argv[1]
    dir_of_SC_verification = sys.argv[2]
    result_dir = sys.argv[3]
    main(template_path, dir_of_SC_verification, result_dir)

