import sys
import os
import utils

replacements = {"rec":
                    {"<pow>": "pow_def",
                     "<intor>": "intor_def",
                     "<intand>": "intand_def",
                     "<pow_is_ok>": "pow_is_ok_rec",
                     "<or_is_ok>": "or_is_ok_rec",
                     "<and_is_ok>": "and_is_ok_rec"},
                "full":
                    {"<pow>": "pow_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<pow_is_ok>": "pow_is_ok_full",
                     "<or_is_ok>": "or_is_ok_full",
                     "<and_is_ok>": "and_is_ok_full"},
                "partial":
                    {"<pow>": "pow_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<pow_is_ok>": "pow_is_ok_partial",
                     "<or_is_ok>": "or_is_ok_partial",
                     "<and_is_ok>": "and_is_ok_partial"},
                "qf":
                    {"<pow>": "pow_dec",
                     "<intor>": "intor_dec",
                     "<intand>": "intand_dec",
                     "<pow_is_ok>": "pow_is_ok_qf",
                     "<or_is_ok>": "or_is_ok_qf",
                     "<and_is_ok>": "and_is_ok_qf"},
                }


def main(templates_dir, meta_template_file):
    with open(meta_template_file) as f:
        meta_template = f.read()
    for key in replacements.keys():
        generate_template(templates_dir, meta_template, key)

def generate_template(templates_dir, meta_template, sf):
    template = utils.substitute(meta_template, replacements[sf])
    write_content_to_file(template, sf + ".smt2", templates_dir)



def write_content_to_file(content, filename, d):
    f = open(d + "/" + filename, "w")
    f.write(content)

if __name__ == "__main__":
    templates_dir = sys.argv[1]
    meta_template_file = sys.argv[2]
    main(templates_dir, meta_template_file)
