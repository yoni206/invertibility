import sys
import os
import utils

l_PH = "<l>"
SC_PH = "<SC>"
assertion_PH = "<assertion>"
AND_OP = "intand"
OR_OP = "intor"
AND_OR_ARE_OK_DEF_PREFIX = "(define-fun and_or_are_ok "
AND_OR_ARE_OK_TRIVIAL = "(define-fun and_or_are_ok ((k Int) (a Int) ) Bool true)"
AND_OR_COMMENT = ";in this file, l and SC don't use intand nor intor. Therefore, there is no point in verifying that these functions satisfy their axiomatizations."


def main(csv_path, dir_name, templates_dir):
    #TODO work on all files in templates_dir
    Assert(False)

def work_on_template(csv_path, dir_name, template_path):
    template_name = get_name_no_ext(template_path)
    directory = dir_name + "/" + template_name
    if os.path.exists(directory):
        print('directory exists, aborting')
        return
    os.makedirs(directory)
    os.makedirs(directory + "_ind")
    with open(template_path, 'r') as myfile:
        template = myfile.read()
    with open(csv_path) as f:
        lines = f.readlines()
    lines = filter_lines(lines)
    process_lines(lines, directory, template, False)
    process_lines(lines, directory, template, True)


def get_name_no_ext(path):
    parts = path.split("/")
    filename = parts[-1]
    name = filename.split(".")[0]
    return name

def filter_lines(lines):
    return list(filter(lambda x: (x.strip() and ";" not in x and "?" not in x and "NA" not in x), lines))

#ind=true means we generate an inductive version
#and put the generated file in directory_ind
def process_lines(lines, directory, template, ind):
    for line in lines:
        process_line(line, directory, template, ind)

def process_line(line, directory, template, ind):
    name, orig_l, orig_SC, new_l, new_SC = line.split(",")
    assertion_ltr = "assertion_ltr"
    assertion_rtl = "assertion_rtl"
    d = directory
    if ind:
        assertion_ltr = assertion_ltr + "_ind"
        assertion_rtl = assertion_rtl + "_ind"
        d = d + "_ind"
    ltr_content = generate_content(template, new_l, new_SC, assertion_ltr)
    rtl_content = generate_content(template, new_l, new_SC, assertion_rtl)
    ltr_fname = name + "_ltr.smt2"
    rtl_fname = name + "_rtl.smt2"
    write_content_to_file(ltr_content, ltr_fname, d)
    write_content_to_file(rtl_content, rtl_fname, d)

def generate_content(template, new_l, new_SC, assertion):
    content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion})
    if (not uses_and_or(new_l)) and (not uses_and_or(new_SC)):
        content = try_to_eliminate_and_or(content)
    return content

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

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print('arg1: csv file\narg2: generated files dir\narg3: templates dir')
        exit(1)
    csv = sys.argv[1]
    result_dir = sys.argv[2]
    template = sys.argv[3]
    main(csv, result_dir, template)
