import sys
import os
import utils
from gen_translations import substitutions

FIND_INV = "find_inv_"
SYGUS_SUFFIX = "_4bit.sy"
INT_CHECK = "int_check_"
EXISTENTIAL_L = "(exists ((x Int)) (and (everything_is_ok_for k x) (in_range k x) (l k x s t)))"
DELIMITER = ";"
l_part_PH = "<l_part>"
l_PH = "<l>"
SC_PH = "<SC>"
assertion_PH = "<assertion>"
AND_OP = "intand"
OR_OP = "intor"
USUAL_LOGIC = "(set-logic UFNIA)"
QF_LOGIC = "(set-logic QF_UFNIA)"
AND_IS_OK_FOR_DELETION = "and_is_ok"
OR_IS_OK_FOR_DELETION = "or_is_ok"
L_PART_PREFIX = "(define-fun l_part"
SC_PREFIX = "(define-fun SC"
BEGIN_LTR_SECTION = ";<BEGIN_LTR>"
END_LTR_SECTION = ";<END_LTR>"
BEGIN_RTL_SECTION = ";<BEGIN_RTL>"
END_RTL_SECTION = ";<END_RTL>"
AND_OK_ASSERTION = "(assert (and_is_ok k))"
OR_OK_ASSERTION = "(assert (or_is_ok k))"
DEFINE_FUN_PREFIX_REGEX = "\\(define-fun "
DEFINE_FUN_REC_PREFIX_REGEX = "\\(define-fun-rec "
DEFINE_FUN_PREFIX = "(define-fun "
DEFINE_FUN_REC_PREFIX = "(define-fun-rec "

def main(csv_path, dir_name, templates_dir, inverses_file, verified_inverses_file):
    files = os.listdir(templates_dir)
    verified_inverses = get_list_of_verified_inverses(verified_inverses_file)
    for f in files:
        work_on_template(csv_path, dir_name, templates_dir + "/" + f, inverses_file, verified_inverses)

def get_list_of_verified_inverses(verified_inverses_file):
    result = []
    with open(verified_inverses_file, "r") as myfile:
        lines = [l.strip() for l in myfile.readlines()]
    for line in lines:
        syn, name = line.split(",")
        result.append((syn, name))
    return result

def work_on_template(csv_path, dir_name, template_path, inverses_file, verified_inverses):
    template_name = utils.get_file_or_dir_name_no_ext(template_path)
    directory = dir_name + "/" + template_name
    if os.path.exists(directory):
        print('directory exists, aborting')
        exit(1)
    os.makedirs(directory)
#    os.makedirs(directory + "_ind")
    with open(template_path, 'r') as myfile:
        template = myfile.read()
    with open(csv_path) as f:
        lines = f.readlines()
    lines = filter_lines(lines)
    process_lines(lines, directory, template, inverses_file, False, verified_inverses)
#   process_lines(lines, directory, template, inverses_file, True, verified_inverses)

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
def process_lines(lines, directory, template, inverses_file, ind, verified_inverses):
    inverses = get_inverses(inverses_file)
    for line in lines:
        process_line(line, directory, template, inverses, ind, verified_inverses)

def process_line(line, directory, template, inverses, ind, verified_inverses):
    name, orig_l, orig_SC, new_l, new_SC = line.split(",")
    if ind:
        d = directory + "_ind"
    else:
        d = directory
    
    rtl_content = generate_content_rtl(name, template, new_l, new_SC, d, ind)
    rtl_fname = name + "_rtl.smt2"
    write_content_to_file(rtl_content, rtl_fname, d)
    
    ltr_contents = generate_contents_ltr(name, template, new_l, new_SC, inverses, d, ind, verified_inverses)
    for ltr_subname in ltr_contents:
        ltr_fname = name + "_ltr_" +  ltr_subname + ".smt2"
        ltr_content = ltr_contents[ltr_subname]
        write_content_to_file(ltr_content, ltr_fname, d)

def get_l_part_and_extra_definition(name, inv):
    l_part = "(l k ( inv k s t) s t)"
    definition = translate(inv) 
    definition = add_k_to_def(definition)
    return l_part, definition

#find the inverses for the current benchmark.
#make needed translations
def get_inverses_for_name(name, inverses, verified_inverses):
    name = name[len(INT_CHECK):]
    full_name = FIND_INV + name + SYGUS_SUFFIX
    inverses_for_name = inverses[full_name]
    inverses_for_name = {get_syntax_name(syntax): inverses_for_name[syntax] for syntax in inverses_for_name if inverses_for_name[syntax] != "unknown" and inverse_verified(syntax, name, verified_inverses)}
    return inverses_for_name

def inverse_verified(syntax, name, verified_inverses):
    pair = (get_syntax_name(syntax), name)
    return pair in verified_inverses

def get_syntax_name(syntax):
    return syntax[len("syntax_"):]

def add_k_to_def(definition):
    result = definition.replace("((s Int)", "((k Int) (s Int)")
    return result

def translate(definition):
    return utils.substitute(definition, substitutions)

def generate_contents_ltr(name,template, new_l, new_SC, inverses, directory, ind, verified_inverses):
    result = {}
    result["no_inv"] = gen_no_inv(name,template, new_l, new_SC, directory, ind)
    inverses_for_name = get_inverses_for_name(name, inverses, verified_inverses)
    for syn in inverses_for_name:
        result["inv_" + syn] = gen_with_inv(name,template, new_l, new_SC, inverses_for_name[syn], directory, ind)
    return result

def gen_no_inv(name,template, new_l, new_SC, directory, ind):
    assertion = "assertion_ltr"
    if ind:
        assertion = assertion + "_ind"
    l_part = EXISTENTIAL_L
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion, l_part_PH: l_part})
    content = remove_rtl_stuff(content)
    if is_rec(directory):
        content = massage_rec(content)
    return content
    
def gen_with_inv(name,template, new_l, new_SC, inv, directory, ind):
    assertion = "assertion_ltr"
    if ind:
        assertion = assertion + "_ind"
    l_part, extra_definition = get_l_part_and_extra_definition(name, inv)
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion, l_part_PH: l_part})
    content = add_extra_definition_to_content(content, extra_definition)
    content = remove_rtl_stuff(content)
    if is_rec(directory):
        content = massage_rec(content)
    return content


def generate_content_rtl(name, template, new_l, new_SC, directory, ind):
    assertion = "assertion_rtl"
    if ind:
        assertion = assertion + "_ind"
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion})
    content = remove_ltr_stuff(content)
    content = massage(content, new_l, new_SC, directory)
    if is_rec(directory):
        content = massage_rec(content)
    return content

def massage(content, new_l, new_SC, directory):
    content = try_to_eliminate_and_or(content, new_l, new_SC)
    #if is_qf(directory):
    #    content = massage_qf(content)
    #TODO fix qf to use mathsat etc.
    return content


def remove_rtl_stuff(content):
    lines = [l.strip() for l in content.splitlines()]
    rtl_start_index = utils.get_index_of_line_with(lines, BEGIN_RTL_SECTION)
    rtl_end_index = utils.get_index_of_line_with(lines, END_RTL_SECTION)
    lines = utils.remove_lines_from_i_to_j(lines, rtl_start_index, rtl_end_index)
    return "\n".join(lines)

def remove_ltr_stuff(content):
    lines = [l.strip() for l in content.splitlines()]
    ltr_start_index = utils.get_index_of_line_with(lines, BEGIN_LTR_SECTION)
    ltr_end_index = utils.get_index_of_line_with(lines, END_LTR_SECTION)
    lines = utils.remove_lines_from_i_to_j(lines, ltr_start_index, ltr_end_index)
    return "\n".join(lines)

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

def add_extra_definition_to_content(content, extra_definition):
    lines = content.splitlines()
    lines = [line.strip() for line in lines]
    index_of_l_part_def = index_of_line_starting_with(lines, L_PART_PREFIX)
    lines.insert(index_of_l_part_def, extra_definition)
    return "\n".join(lines)

def index_of_line_starting_with(lines, pref):
    candidates = [l for l in lines if l.startswith(pref)]
    assert(len(candidates) == 1)
    return lines.index(candidates[0])


def is_qf(directory):
    return directory.endswith("qf")

def is_rec(directory):
    return "rec" in directory

def massage_rec(content):
    content = content.replace(USUAL_LOGIC, "")
    return content

def massage_qf(content):
        content = get_rid_of_quants_and_recs(content)
        content = change_logic_if_possible(content)
        return content


def has_l_part_with_exists(content):
    lines = [l.strip() for l in content.split("\n")]
    l_part_lines = utils.get_lines_starting_with(lines, L_PART_PREFIX)
    if (len(l_part_lines) == 0):
        return False
    else:
        l_part_line = utils.get_line_starting_with(lines, L_PART_PREFIX)
        return "exists" in l_part_line

def change_logic_if_possible(content):
    lines = content.splitlines()
    lines = [l.strip() for l in lines]
    assert(lines[0].strip() == USUAL_LOGIC)
    if (not sc_has_exists(content)) and (not has_l_part_with_exists(content)):
        lines[0] = QF_LOGIC
    result = "\n".join(lines)
    return result

def sc_has_exists(content):
    lines = [l.strip() for l in content.split("\n")]
    sc_line = utils.get_line_starting_with(lines, SC_PREFIX)
    return "exists" in sc_line

def has_quantifiers(line):
    return "forall " in line or "exists " in line

def get_def_fun_defs(template):
    result = []
    parens = utils.find_parens(template)
    for opening in parens:
        closing = parens[opening]
        substring = template[opening:closing]
        if DEFINE_FUN_PREFIX in substring:
            result.append(substring)
    return result

def get_quantified_prefixes(template):
    result = []
    define_fun_defs = get_def_fun_defs(template)
    for def_fun in define_fun_defs:
        if has_quantifiers(def_fun):
            first_space_index = def_fun.find(" ")
            suffix = def_fun[first_space_index + 1 : ]
            second_space_index = suffix.index(" ")
            prefix = def_fun[0:second_space_index]
            result.append(prefix)
    return result

def get_rid_of_quants_and_recs(template):
    prefixes = get_quantified_prefixes(template)
    prefixes.append(DEFINE_FUN_REC_PREFIX)
    template = get_rid_of_commands(prefixes, template)
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

def uses_and(formula):
    return (AND_OP in formula)

def uses_or(formula):
    return   (OR_OP in formula)

def try_to_eliminate_and_or(content, new_l, new_SC):
    lines = content.splitlines()
    index_and = utils.get_index_of_line_with(lines, AND_OK_ASSERTION)
    index_or = utils.get_index_of_line_with(lines, OR_OK_ASSERTION)
    if (not uses_and(new_l)) and (not uses_and(new_SC)):
        lines[index_and] = ""
    if (not uses_or(new_l) and (not uses_or(new_SC))):
        lines[index_or] = ""
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
        print('arg1: csv file\narg2: generated files dir\narg3: templates dir\narg4: sygus inverses file\narg5: verified inverses file')
        exit(1)
    csv = sys.argv[1]
    result_dir = sys.argv[2]
    templates_dir = sys.argv[3]
    inverses_file = sys.argv[4]
    verified_inverses_file = sys.argv[5]
    main(csv, result_dir, templates_dir, inverses_file, verified_inverses_file)
