import sys
import os
import utils
from gen_translations import substitutions

FIND_INV = "find_inv"
SYGUS_SUFFIX = "_4bit.sy"
INT_CHECK = "int_check"
EXISTENTIAL_L = "(exists ((x Int)) (l k x s t))"
DELIMITER = ";"
l_part_PH = "<l_part>"
l_PH = "<l>"
SC_PH = "<SC>"
assertion_PH = "<assertion>"
AND_OP = "intand"
OR_OP = "intor"
AND_OR_ARE_OK_DEF_PREFIX = "(define-fun and_or_are_ok "
AND_OR_ARE_OK_TRIVIAL = "(define-fun and_or_are_ok ((k Int) (a Int) ) Bool true)"
AND_OR_COMMENT = ";in this file, l and SC don't use intand nor intor. Therefore, there is no point in verifying that these functions satisfy their axiomatizations."
T_FUN_DEC = "(declare-fun t () Int)"
RTL_DEF_PREF = "(define-fun assertion_rtl () Bool"
L_PART_DEF_PREF = "(define-fun l_part ((k Int) (s Int) (t Int))"
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


def main(csv_path, dir_name, templates_dir, inverses_file):
    files = os.listdir(templates_dir)
    for f in files:
        work_on_template(csv_path, dir_name, templates_dir + "/" + f, inverses_file)

def work_on_template(csv_path, dir_name, template_path, inverses_file):
    template_name = get_name_no_ext(template_path)
    directory = dir_name + "/" + template_name
    if os.path.exists(directory):
        print('directory exists, aborting')
        exit(1)
    os.makedirs(directory)
    os.makedirs(directory + "_ind")
    with open(template_path, 'r') as myfile:
        template = myfile.read()
    with open(csv_path) as f:
        lines = f.readlines()
    lines = filter_lines(lines)
    process_lines(lines, directory, template, inverses_file, False)
    process_lines(lines, directory, template, inverses_file, True)


def get_name_no_ext(path):
    parts = path.split("/")
    filename = parts[-1]
    name = filename.split(".")[0]
    return name

def filter_lines(lines):
    return list(filter(lambda x: (x.strip() and ";" not in x and "?" not in x and "NA" not in x), lines))

def get_inverses(inverses_file):
    result = {}
    with open(inverses_file) as f:
        lines = f.readlines()
        lines = [l.strip() for l in lines]
        title_line = lines[0]
        syntaxes = title_line.split(DELIMITER)[1:]
        for line in lines[1:]:
            add_line_to_inverses_map(line, result, syntaxes)
    return result

def add_line_to_inverses_map(line, inv_map, syntaxes):
    data = line.split(DELIMITER)
    name = data[0]
    inverses = data[1:]
    assert(name not in inv_map)
    inv_map[name] = {}
    for i in range(0, len(syntaxes)):
        syntax = syntaxes[i]
        inv_map[name][syntax] = inverses[i]

#ind=true means we generate an inductive version
#and put the generated file in directory_ind
def process_lines(lines, directory, template, inverses_file, ind):
    inverses = get_inverses(inverses_file)
    for line in lines:
        process_line(line, directory, template, inverses, ind)

def process_line(line, directory, template, inverses, ind):
    name, orig_l, orig_SC, new_l, new_SC = line.split(",")
    if ind:
        d = directory + "_ind"
    else:
        d = directory
    ltr_content = generate_content_ltr(name, template, new_l, new_SC, inverses, d, ind)
    rtl_content = generate_content_rtl(name, template, new_l, new_SC, d, ind)
    ltr_fname = name + "_ltr.smt2"
    rtl_fname = name + "_rtl.smt2"
    write_content_to_file(ltr_content, ltr_fname, d)
    write_content_to_file(rtl_content, rtl_fname, d)

def get_l_part_and_extra_definitions(name, inverses):
    inverses_for_name = get_inverses_for_name(name, inverses)
    if len(inverses_for_name) == 0:
        return EXISTENTIAL_L, []
    else:
        disjunction, definitions = get_disjunctive_L_and_inv_definitions(inverses_for_name)
        return disjunction, definitions

#find the inverses for the current benchmark.
#make needed translations
def get_inverses_for_name(name, inverses):
    name = name[len(INT_CHECK):]
    name = FIND_INV + name + SYGUS_SUFFIX
    inverses_for_name = inverses[name]
    inverses_for_name = {"inv_" + syntax: inverses_for_name[syntax] for syntax in inverses_for_name if inverses_for_name[syntax] != "unknown"}
    return inverses_for_name

def get_disjunctive_L_and_inv_definitions(inverses_for_name):
    disjuncts = ["(l k (" + inv + " k s t) s t)" for inv in inverses_for_name.keys()]
    disjunctive_L = "(or " + " ".join(disjuncts) + ")"
    definitions = [translate(inverses_for_name[inv_name]).replace("inv ",  inv_name + " ") for inv_name in inverses_for_name.keys()]
    definitions = add_k_to_defs(definitions)
    return disjunctive_L, definitions

def add_k_to_defs(definitions):
    result = []
    for defi in definitions:
        defi = defi.replace("((s Int)", "((k Int) (s Int)")
        result.append(defi)
    return result

def translate(definition):
    return utils.substitute(definition, substitutions)

def generate_content_ltr(name,template, new_l, new_SC, inverses, directory, ind):
    assertion = "assertion_ltr"
    if ind:
        assertion = assertion + "_ind"
    l_part, extra_definitions = get_l_part_and_extra_definitions(name, inverses)
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion, l_part_PH: l_part})
    content = add_extra_definitions_to_content(content, extra_definitions)
    if (not uses_and_or(new_l)) and (not uses_and_or(new_SC)):
        content = try_to_eliminate_and_or(content)
    content = remove_rtl_stuff(content)
    return content

def remove_rtl_stuff(content):
    rtl_stuff = ["_rtl", " x0", "right_to_left"]
    return remove_lines_with(content, rtl_stuff)

def remove_ltr_stuff(content):
    ltr_stuff = ["_ltr", "left_to_right", "l_part", "define-fun inv "]
    return remove_lines_with(content, ltr_stuff)

#stuff is a *list* of stuff to remove
def remove_lines_with(content, stuff):
    result_lines = []
    lines = [l.strip() for l in content.splitlines()]
    for line in lines:
        line_has_stuff = False
        for s in stuff:
            if s in line:
                line_has_stuff = True
        if not line_has_stuff:
            result_lines.append(line)
    return "\n".join(result_lines)

def add_extra_definitions_to_content(content, extra_detinitions):
    lines = content.splitlines()
    lines = [line.strip() for line in lines]
    index_of_l_part_def = index_of_line_starting_with(lines, L_PART_DEF_PREF)
    for definition in extra_detinitions:
        lines.insert(index_of_l_part_def, definition)
    return "\n".join(lines)

def index_of_line_starting_with(lines, pref):
    candidates = [l for l in lines if l.startswith(pref)]
    assert(len(candidates) == 1)
    return lines.index(candidates[0])

def generate_content_rtl(name, template, new_l, new_SC, directory, ind):
    assertion = "assertion_rtl"
    if ind:
        assertion = assertion + "_ind"
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion})
    if (not uses_and_or(new_l)) and (not uses_and_or(new_SC)):
        content = try_to_eliminate_and_or(content)
    if is_qf(assertion, directory):
        content = massage_qf_rtl(content)
    content = remove_ltr_stuff(content)
    return content

def is_qf(assertion, directory):
    return directory.endswith("qf")

def massage_qf_rtl(content):
        content = get_rid_of_quants_and_recs(content)
        return content

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


def uses_and_or(formula):
    return (AND_OP in formula) or (OR_OP in formula)

def try_to_eliminate_and_or(content):
    lines = content.splitlines()
    index = get_andor_dec_index(lines)
    result = content
    lines[index] = ";" + lines[index]
    lines.insert(index, AND_OR_COMMENT)
    lines.insert(index+2, AND_OR_ARE_OK_TRIVIAL)
    result = "\n".join(lines)
    return result

def get_andor_dec_index(lines):
    indexes = [i for i in range(0, len(lines)-1) if lines[i].startswith(AND_OR_ARE_OK_DEF_PREFIX)]
    if len(indexes) == 1:
        return indexes[0]
    else:
        assert(False)

def write_content_to_file(content, filename, d):
    f = open(d + "/" + filename, "w")
    f.write(content)
    f.close()

if __name__ == "__main__":
    if len(sys.argv) < 5:
        print('arg1: csv file\narg2: generated files dir\narg3: templates dir\narg4: sygus inverses file')
        exit(1)
    csv = sys.argv[1]
    result_dir = sys.argv[2]
    templates_dir = sys.argv[3]
    inverses_file = sys.argv[4]
    main(csv, result_dir, templates_dir, inverses_file)
