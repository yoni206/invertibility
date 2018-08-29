import sys
import os
import utils

substitutions = {
    "bvult":"<",
    "bvugt":">",
    "bvule":"<=",
    "bvuge":">=",
    "bvslt":None,
    "bvsgt":None,
    "bvsle":None,
    "bvsge":None,
    "bvnot":None,
    "bvneg":"intneg k",
    "bvand":None,
    "bvor":None,
    "bvshl":"intshl k",
    "bvlshr":"intlshr k",
    "bvashr":None,
    "bvadd":"intadd k",
    "bvmul":"intmul k",
    "modtotal":"intmodtotal k",
    "udivtotal":"intudivtotal k",
    "bvconcat":"intconcat k1 k2",
    "extract":None,
    "(_ bv0 4)":"0",
    "max":"intmax k",
    "min":"intmin k"
}

def main(dir_of_SC_verification, generated_file_path):
    old_l_name_to_l_sc = utils.map_l_to_sc(dir_of_SC_verification, "int_check") #file_name -> <l,sc>
    new_l_name_to_l_sc = make_substitutions(old_l_name_to_l_sc)
    lines = get_lines(old_l_name_to_l_sc, new_l_name_to_l_sc)
    with open(generated_file_path, 'w') as f:
        f.writelines(lines)

def get_lines(old, new):
    lines = []
    for name in new.keys():
        old_l, old_sc = old[name]
        new_l, new_sc = new[name]
        display_name = name[:-5]
        line = ",".join([display_name,old_l,old_sc,new_l,new_sc])
        line = line + "\n"
        lines.append(line)
    return lines

def make_substitutions(l_name_to_l_sc):
    result = {}
    for name in l_name_to_l_sc.keys():
        l, sc = l_name_to_l_sc[name]
        l = utils.substitute(l, substitutions)
        sc = utils.substitute(sc, substitutions)

        if l is not None and sc is not None:
            result[name] = [l,sc]
    return result

if __name__ == "__main__":
    dir_of_SC_verification = sys.argv[1]
    generated_file_path = sys.argv[2]
    main(dir_of_SC_verification, generated_file_path)
