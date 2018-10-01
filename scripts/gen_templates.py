import sys
import os
import utils

T_FUN_DEC = "(declare-fun t () Int)"
X_FUN_DEC = "(declare-fun x () Int)"
QF_RTL_LINE = "(define-fun assertion_rtl () Bool (and (in_range k x) (two_to_the_is_ok x) (and_or_are_ok k x) (l k x s t) (not (SC k s t)) ))"
RTL_DEF_PREF = "(define-fun assertion_rtl () Bool"
USUAL_LOGIC = "(set-logic UFNIA)"
QF_LOGIC = "(set-logic QF_UFNIA)"
QUANT_REC_PREFIXES = ["\(define-fun-rec", 
                      "\(define-fun left_to_right", 
                      "\(define-fun right_to_left", 
                      "\(define-fun assertion_ltr", 
                      "\(define-fun assertion_ltr_ind",
                      "\(define-fun assertion_rtl_ind",
                      "\(define-fun two_to_the_is_ok_unbounded",
                      "\(define-fun and_or_are_ok_unbounded",
                      "\(assert two_to_the_is_ok_unbounded", 
                      "\(assert and_or_are_ok_unbounded", 
                      "\(define-fun two_to_the_is_ok_full", 
                      "\(define-fun two_to_the_is_ok_partial",
                      "\(define-fun or_is_ok_full",
                      "\(define-fun or_is_ok_partial",
                      "\(define-fun and_is_ok_full",
                      "\(define-fun and_is_ok_partial",]


replacements = {"rec":
                    {"<two_to_the>": "two_to_the_def",
                     "<intor>": "intor_def",
                     "<intand>": "intand_def",
                     "<two_to_the_is_ok>": "two_to_the_is_ok_rec",
                     "<or_is_ok>": "or_is_ok_rec",
                     "<and_is_ok>": "and_is_ok_rec"},
                "full":
                    {"<two_to_the>": "two_to_the_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<two_to_the_is_ok>": "two_to_the_is_ok_full",
                     "<or_is_ok>": "or_is_ok_full",
                     "<and_is_ok>": "and_is_ok_full"},
                "partial":
                    {"<two_to_the>": "two_to_the_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<two_to_the_is_ok>": "two_to_the_is_ok_partial",
                     "<or_is_ok>": "or_is_ok_partial",
                     "<and_is_ok>": "and_is_ok_partial"},
                "qf":
                    {"<two_to_the>": "two_to_the_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<two_to_the_is_ok>": "two_to_the_is_ok_qf",
                     "<or_is_ok>": "or_is_ok_qf",
                     "<and_is_ok>": "and_is_ok_qf"},
                }


def main(templates_dir, meta_template_file):
    with open(meta_template_file) as f:
        meta_template = f.read()
    for key in replacements.keys():
        generate_template(templates_dir, meta_template, key)

def generate_template(templates_dir, meta_template, sf):
    template = meta_template
    if (sf == "qf"):
        template = replace_rtl_fun(template)
        template = add_x_constant(template)
        template = get_rid_of_quants_and_recs(template)
        template = template.replace(USUAL_LOGIC, QF_LOGIC)
    template = utils.substitute(template, replacements[sf])
    write_content_to_file(template, sf + ".smt2", templates_dir)

def replace_rtl_fun(template):
    lines = template.splitlines()
    def_list = [i for i in range(0, len(lines)) if lines[i].startswith(RTL_DEF_PREF)]
    assert(len(def_list) == 1)
    index = def_list[0]
    lines[index] = QF_RTL_LINE
    result = "\n".join(lines)
    return result

def add_x_constant(template):
    lines = template.splitlines()
    def_list = [i for i in range(0, len(lines)) if lines[i].startswith(T_FUN_DEC)]
    assert(len(def_list) == 1)
    index = def_list[0]
    lines.insert(index, X_FUN_DEC)
    result = "\n".join(lines)
    return result


def get_rid_of_quants_and_recs(template):
    template = get_rid_of_commands(QUANT_REC_PREFIXES, template)
    return template

def get_rid_of_commands(prefixes, template):
    result = template
    for prefix in prefixes:
        parens = utils.find_parens(result)
        prefix_indexes = utils.find_all(result, prefix)
        subs = {}
        for index in prefix_indexes:
            start = index
            end = parens[start]
            command = result[start:end+1]
            subs[command] = ""
        result = utils.substitute(result, subs)
    return result


def write_content_to_file(content, filename, d):
    f = open(d + "/" + filename, "w")
    f.write(content)

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: templates dir\narg2: meta template file')
        exit(1)
    templates_dir = sys.argv[1]
    meta_template_file = sys.argv[2]
    main(templates_dir, meta_template_file)
