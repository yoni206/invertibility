import sys
import os
import utils

l_PH = "<l>"
SC_PH = "<SC>"
assertion_PH = "<assertion>"

def main(csv_path, dir_name, template_path):
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
    ltr_content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion_ltr})
    rtl_content = utils.substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion_rtl })
    ltr_fname = name + "_ltr.smt2"
    rtl_fname = name + "_rtl.smt2"
    write_content_to_file(ltr_content, ltr_fname, d)
    write_content_to_file(rtl_content, rtl_fname, d)


def write_content_to_file(content, filename, d):
    f = open(d + "/" + filename, "w")
    f.write(content)

if __name__ == "__main__":
    csv = sys.argv[1]
    result_dir = sys.argv[2]
    template = sys.argv[3]
    main(csv, result_dir, template)
