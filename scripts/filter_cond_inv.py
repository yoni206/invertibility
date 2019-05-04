import pandas as ps
import sys
import os


def main(input_file, output_file):
    raw = get_raw_data(input_file)
    raw.to_csv("~/tmp.csv")
    raw["syntax"] = raw["benchmark"].apply(get_syntax)
    raw["ic_name"] = raw.benchmark.apply(get_name)
    raw["width"] = raw.benchmark.apply(get_width)
    raw["proved"] = raw.apply(proved, axis=1)
    raw.to_csv("~/tmp1.csv")
    grouped = raw.groupby(['syntax', 'ic_name'])
    df = grouped.agg({'proved': agg_all_true})
    df.to_csv("~/tmp2.csv")
    df_proved = df[df.proved == True]
    df_proved.to_csv("~/tmp3.csv")
    df_output = df_proved.drop(['proved'], axis=1)
    df_output.to_csv(output_file)

def agg_all_true(values):
    trues = [v for v in values if v == True]
    falses = [v for v in values if v == False]
    return len(falses) == 0 

def proved(row):
    return row.status == "ok" and (row.result == 20)

def get_string_between_prefix_and_suffix_exclusive(s, prefix, suffix):
    n = s.find(prefix)
    m = len(prefix)
    start = n + m
    end = s.find(suffix, start)
    result = s[start:end]
    return result

def get_name(bm_path):
    return get_string_between_prefix_and_suffix_exclusive(bm_path, "verify_inv_", "_4bit")

def get_width(bm_path):
    s = get_string_between_prefix_and_suffix_exclusive(bm_path, "_4bit", ".smt2")
    result = int(s)
    return result

def get_syntax(benchmark_path):
    return get_string_between_prefix_and_suffix_exclusive(benchmark_path, "syntax_", "/")


def get_raw_data(input_file):
    delete_first_row_if_redundent(input_file)
    return ps.read_csv(input_file, sep=',')

#the cluster results file hav ehieracrchy. But I never compare more than one.
def delete_first_row_if_redundent(input_file):
    if is_first_row_redundent(input_file):
        delete_first_row_from_file(input_file)

def is_first_row_redundent(input_file):
    with open(input_file, 'r') as fin:
        data = fin.read().splitlines(True)
    first_row = data[0]
    return "DIRECTORY" in first_row and not first_row.startswith("0")

def delete_first_row_from_file(input_file):
    with open(input_file, 'r') as fin:
        data = fin.read().splitlines(True)
    with open(input_file, 'w') as fout:
        fout.writelines(data[1:])

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: cluster results csv (result of compare-smt-runs.py on the verification benchmarks)\narg2: output file\n')
        exit(1)
    csv_file = sys.argv[1]
    output_file = sys.argv[2]
    main(csv_file, output_file)
