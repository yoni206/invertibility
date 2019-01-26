import os
import sys
import gen_smt_from_translations as gsft
import utils

DEF_INV_PREFIX = "(define-fun inv ((s (BitVec 4)) (t (BitVec 4))) (BitVec 4) "

TEMPLATE = '''
(set-logic QF_BV)

(define-fun min () (_ BitVec <k_PH>) (bvnot (bvlshr (bvnot (_ bv0 <k_PH>)) (_ bv1 <k_PH>))))

(define-fun max () (_ BitVec <k_PH>) (bvnot min))

(define-fun udivtotal ((a (_ BitVec <k_PH>)) (b (_ BitVec <k_PH>))) (_ BitVec <k_PH>)
  (ite (= b (_ bv0 <k_PH>)) (bvnot (_ bv0 <k_PH>)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec <k_PH>)) (b (_ BitVec <k_PH>))) (_ BitVec <k_PH>)
  (ite (= b (_ bv0 <k_PH>)) a (bvurem a b))
)

(declare-fun s () (_ BitVec <k_PH>))
(declare-fun t () (_ BitVec <k_PH>))
(define-fun inv ((s (_ BitVec <k_PH>)) (t (_ BitVec <k_PH>))) (_ BitVec <k_PH>) <INV_PH>)
(define-fun l ((x (_ BitVec <k_PH>))) Bool <l_PH>)
(define-fun SC () Bool <SC_PH>)
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
'''

def main(syg_res_file, dest_dir, dir_of_SC_verification):
    inverses = get_inverses(syg_res_file)
    create_dirs(inverses, dest_dir)
    gen_bms(inverses, dest_dir, dir_of_SC_verification)

def get_inverses(syg_res_file):
    dic = gsft.get_inverses(syg_res_file)
    result = {change_name(name) : change_invs(dic[name]) for name in dic.keys()}
    return result

def change_name(name):
    return name.replace("find_inv", "verify_inv").replace(".sy", "")

#remove define-fun...
def change_invs(invs):
    return {syntax : invs[syntax][len(DEF_INV_PREFIX) :len(invs[syntax])-1] for syntax in invs}

def adjust_term(inv, k):
    return inv.replace("#b0000", get_zero(k)).replace("#b1000", get_min(k)).replace("#b0111", get_max(k)).replace("(_ BitVec 4)", "(_ BitVec <k_PH>)").replace("(_ bv0 4)", "(_ bv0 <k_PH>)").replace("(_ bv1 4)", "(_ bv1 <k_PH>)").replace("(_ bv4 4)", "(_ bv<k_PH> <k_PH>)")

def get_zero(k):
    return "#b" + "0" * k

def get_min(k):
    return "#b1" + "0"*(k-1)

def get_max(k):
    return "#b0" + "1"*(k-1)

def gen_bms(inverses, dest_dir, dir_of_SC_verification):
    l_name_to_l_sc = utils.map_l_to_sc(dir_of_SC_verification, "verify_inv", True) #file_name -> <l,sc>
    for name in inverses:
        invs = inverses[name]
        for syn in invs:
            if inv_exists(invs, syn):
                for k in range(4,64):
                    inv = adjust_term(invs[syn], k)
                    path = dest_dir + "/" + syn + "/" + name + str(k) + ".smt2"
                    l, SC = l_name_to_l_sc[name]
                    l = adjust_term(l, k)
                    SC = adjust_term(SC, k)
                    gen_bm(path, inv, SC, l, k)

def inv_exists(invs, syn):
    return invs[syn].strip() != "" 

def gen_bm(path, inv, SC, l, k):
    content = gen_content(inv, SC, l, k)
    with open(path, "w") as myfile:
        myfile.write(content)

def gen_content(inv, SC, l, k):
    content = TEMPLATE.replace("<INV_PH>", inv).replace("<SC_PH>", SC).replace("<l_PH>", l).replace("<k_PH>", str(k))
    return content

def create_dirs(inverses, dest_dir):
    syntaxes = get_syntaxes(inverses)
    for syntax in syntaxes:
        path_of_dir = dest_dir + "/" + syntax
        os.makedirs(path_of_dir)

def get_syntaxes(inverses):
    list_of_lists_of_syntaxes = [list(inverses[name].keys()) for name in inverses]
    syntaxes = list_of_lists_of_syntaxes[0]
    return syntaxes

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("arg1: sygus results file\n arg2: dest dir\n arg3: dir of SC verification")
        exit(1)
    syg_res_file = sys.argv[1]
    dest_dir = sys.argv[2]
    sc_verif_dir = sys.argv[3]
    main(syg_res_file, dest_dir, sc_verif_dir)
