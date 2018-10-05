import sys
import os
import utils


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
    template = utils.substitute(template, replacements[sf])
    write_content_to_file(template, sf + ".smt2", templates_dir)


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
