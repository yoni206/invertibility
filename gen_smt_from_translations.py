import sys
import os

directory = ""
template = ""
l_PH = "<l>"
SC_PH = "<SC>"
assertion_PH = "<assertion>"


def main(csv_path, dir_name, template_path):
    global directory
    global template
    directory = dir_name
    if os.path.exists(directory):
        print('directory exists, aborting')
        return
    os.makedirs(directory)
    with open(template_path, 'r') as myfile:
        template = myfile.read()
    with open(csv_path) as f:
        lines = f.readlines()
    lines = filter_lines(lines)
    process_lines(lines)

def filter_lines(lines):
    return list(filter(lambda x: (x.strip() and ";" not in x and "?" not in x and "NA" not in x), lines))

def process_lines(lines):
    for line in lines:
        process_line(line)

def process_line(line):
    name, orig_l, orig_SC, new_l, new_SC = line.split(",")
    assertion_ltr = "assertion_ltr"
    assertion_rtl = "assertion_rtl"
    ltr_content = substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion_ltr})
    rtl_content = substitute(template, {l_PH: new_l, SC_PH: new_SC, assertion_PH: assertion_rtl })
    ltr_fname = name + "_ltr.smt2"
    rtl_fname = name + "_rtl.smt2"
    write_content_to_file(ltr_content, ltr_fname)
    write_content_to_file(rtl_content, rtl_fname)

def substitute(string, substitutions):
    result = string
    for old, new in substitutions.items():
        result = result.replace(old, new)
    return result


def write_content_to_file(content, path):
    f = open(directory + "/" + path, "w")
    f.write(content)


if __name__ == "__main__":
    csv = sys.argv[1]
    result_dir = sys.argv[2]
    template = sys.argv[3]
    main(csv, result_dir, template)
