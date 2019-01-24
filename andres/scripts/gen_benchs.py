import sys
import os
import re
sys.path.insert(0, '../scripts')
import utils

def main(dir_of_rw, output_dir, dir_of_templates):
    templates_files = [f for f in os.listdir(dir_of_templates) if not f.startswith(".")]
    rewrite_files =  [f for f in os.listdir(dir_of_rw) if not f.startswith(".")]
    try:
      os.mkdir(output_dir)
    except FileExistsError:
        pass
    for t_f in templates_files:
        template_name = utils.get_file_or_dir_name_no_ext(t_f)
        try:
          os.makedirs(output_dir + "/" + template_name)
        except FileExistsError:
            pass
        t_path = dir_of_templates + "/" + t_f
        template_content = get_template_content_and_filter(t_path)
        for rw_f in rewrite_files:
            original_path = dir_of_rw + "/" + rw_f
            original_content = get_str_from_file(original_path)
            output_content = template_content + "\n" + original_content
            with open(output_dir + "/" +  template_name + "/" + rw_f, 'w') as myfile:
                myfile.write(output_content)

def get_str_from_file(f):
    with open(f, 'r') as myfile:
        return myfile.read()

def get_template_content_and_filter(t_path):
    s = get_str_from_file(t_path)
    lines = [l.strip() for l in s.splitlines()]
    new_lines = []
    for line in lines:
        if "main course" not in line.lower():
            new_lines.append(line)
        else:
            new_lines.append(";THE ACTUAL REWRITE")
            new_lines.append(";;;;;;;;;;;;;;;;;;;;;;;;;")
            new_lines.append("")
            break
    return "\n".join(new_lines)


if __name__ == "__main__":
    if len(sys.argv) < 4:
        print('arg1: dir of original rewrites\narg2: output dir\narg3: dir of templates')
        sys.exit(1)
    dir_of_rw = sys.argv[1]
    dir_of_bm = sys.argv[2]
    dir_of_templates = sys.argv[3]
    main(dir_of_rw, dir_of_bm, dir_of_templates)
