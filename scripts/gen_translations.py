import sys
import os
import utils
import re

substitutions = {
    "bvult":"<",
    "bvugt":">",
    "bvule":"<=",
    "bvuge":">=",
    "bvslt":"intslt k",
    "bvsgt":"intsgt k",
    "bvsle":"intsle k",
    "bvsge":"intsge k",
    "bvnot":"intnot k",
    "bvsub":"intsub k",
    "bvneg":"intneg k",
    "bvand":"intand k",
    "bvor":"intor k",
    "bvshl":"intshl k",
    "bvlshr":"intlshr k",
    "bvashr":"intashr k",
    "bvadd":"intadd k",
    "bvmul":"intmul k",
    "uremtotal":"intmodtotal k",
    "udivtotal":"intudivtotal k",
    "bvconcat":"intconcat k1 k2",
#    "extract":"intextract k",
    "(_ bv0 4)":"0",
    "(_ bv1 4)":"1",
    "(_ bv4 4)":"k",
    "(bvnot (_ bv0 4))":"(intmax k)",
    "max":"(intmaxs k)",
    "min":"(intmins k)",
    "#b1000":"(intmins k)",
    "#b0000":"0",
    "#b0111":"(intmaxs k)",
    "(BitVec 4)":"Int"
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
        #some side conditions include a big disjunction. This should be transform to existential
        if "bv2" in sc:
            sc = replace_disj_with_exists(sc)
        sc = utils.substitute(sc, substitutions)
        if l is not None and sc is not None:
            result[name] = [l,sc]
    return result

def replace_disj_with_exists(sc):
    assert(sc.startswith("(or"))
    assert(sc.count("(_ bv") == 5)
    insert_i = re.sub(r'\(_ bv\d 4\)','i',"(or  (bvuge (bvshl s (_ bv0 4)) t) (bvuge (bvshl s (_ bv1 4)) t) (bvuge (bvshl s (_ bv2 4)) t) (bvuge (bvshl s (_ bv3 4)) t) (bvuge (bvshl s (_ bv4 4)) t))")
    matrix = get_matrix(insert_i)
    return "(exists ((i Int)) (and (>= i 0) (<= i k) " + matrix + "))"

def get_matrix(s):
    assert(s.startswith("(or"))
    body = s[3:-1].strip()
    parens = utils.find_parens(body)
    all_disjuncts_same(body, parens)
    i,j = list(parens.items())[0]
    return body[i:j+1]

def all_disjuncts_same(s, parens):
    expressions = []
    i = 0
    while (i != -1):
        start = i
        end = parens[i]
        assert(start<end)
        subs = s[start:end+1]
        expressions.append(subs)
        distance = s[end:].find("(")
        if distance == -1:
            i = -1
        else:
            i =  distance + end

    for i in range(0, len(expressions)):
        for j in range(i+1, len(expressions)):
            assert (expressions[i] == expressions[j])


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: dir of sc verification\narg2: generated csv path')
        sys.exit(1)
    dir_of_SC_verification = sys.argv[1]
    generated_file_path = sys.argv[2]
    main(dir_of_SC_verification, generated_file_path)
