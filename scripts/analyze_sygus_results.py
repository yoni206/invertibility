import pandas as ps
import sys
import os

def main(results_dir, output_file):
    err_files = [f for f in os.listdir(results_dir) if f.endswith(".err")]
    for err_file in err_files:
        log_file = err_file.replace(".sy.err", ".sy.log")
        sygus_file = err_file.replace(".sy.err", ".sy")
        with open(results_dir + "/" + err_file, "r") as myfile:
            err_content = myfile.read()
        with open(results_dir + "/" + log_file, "r") as myfile:
            log_content = myfile.read()
        is_ok = get_is_ok(err_content)
        syntax, filename_no_syntax = get_syn_and_fname(sygus_file)
        if is_ok:
            inv_def = get_inv_definition(log_content)
            results[filename_no_syntax][syntax] = inv_def
        else:
            results[filename_no_syntax][syntax] = "unknown"
        df = ps.DataFrame.from_dict(results)
        df.to_csv(output_file)

def get_inv_definition(log_content):
    lines = err_content.splitlines()
    prefix = "(define-fun inv)"
    definition_lines = [line for line in lines if line.startswith(prefix)]
    assert(len(definition_lines) == 1)
    definition_line = definition_lines[0]
    return definition_line.strip()

def get_is_ok(err_content):
    lines = err_content.splitlines()
    prefix = "[runlim] status:"
    status_lines = [line for line in lines if line.startswith(prefix)]
    assert(len(status_lines) == 1)
    status_line = status_lines[0]
    status = status_line[len(prefix):].strip()
    result = (status == "ok")
    return result

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: cluster results dir\narg2: output file\n')
        exit(1)
    results_dir = sys.argv[1]
    output_file = sys.argv[2]
    main(results_dir, output_file)
