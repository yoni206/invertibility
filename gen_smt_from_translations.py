import sys
import os

with open("definitions.txt") as f:
    definitions = f.readlines()
directory = ""


def main(path, dir_name):
    global directory
    directory = dir_name
    if os.path.exists(directory):
        print('directory exists, aborting')
        return
    os.makedirs(directory)

    with open(path) as f:
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
    l_def = " ".join(["(define-fun l ((n Int) (x Int) (s Int) (t Int)) Bool", new_l, ")"])
    SC_def = " ".join(["(define-fun SC ((n Int) (s Int) (t Int)) Bool", new_SC, ")"])
    logic_def = "(set-logic NIA)"
    divtotal_def = "(define-fun divtotal ((n Int) (a Int) (b Int)) Int (ite (= b 0) (- n 1) (div a b) ))"
    modtotal_def = "(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))"
    assert1 = "(assert (not hypothesis1))"
    assert2 = "(assert (not hypothesis2))"
    check_sat = "(check-sat)"
    shared_prefix = []
    shared_prefix.extend( [logic_def, divtotal_def, modtotal_def, l_def, SC_def])
    shared_prefix.extend(definitions)
    shared_prefix_txt = "\n".join(shared_prefix)

    ltr_fname = name + "_ltr.smt2"
    rtl_fname = name + "_rtl.smt2"
    ltr_content = "\n".join([shared_prefix_txt,assert1,check_sat])
    rtl_content = "\n".join([shared_prefix_txt,assert2,check_sat])

    write_content_to_file(ltr_content, ltr_fname)
    write_content_to_file(rtl_content, rtl_fname)

def write_content_to_file(content, path):
    f = open(directory + "/" + path, "w")
    f.write(content)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
