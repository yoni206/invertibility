import sys
import os
import subprocess

def main(output_file, dirs):
    try:
        os.remove(output_file)
    except OSError:
        pass
    results = {}
    for d in dirs:
        process_dir(d, results)
    write_to_file(results, output_file)

def write_to_file(results, output_file):
    title_columns = []
    title_columns.append('file')
    first_filename = list(results.keys())[0]
    columns = list(results[first_filename].keys())
    title_columns.extend(columns)
    with open(output_file, 'w') as myfile:
        myfile.write(":".join(title_columns))
        myfile.write("\n")
        for filename in results.keys():
            line = filename
            for i in range(0, len(columns)):
                column = columns[i]
                line = line + ":" + results[filename][column]
            myfile.write(line)
            myfile.write('\n')

def process_dir(d, results):

    with open(d + "/results.txt", 'r') as myfile:
        lines = [l.strip() for l in myfile.readlines()]
    #ignore title
    for line in lines[1:]:
        cells = line.split(':')
        filename = cells[0]
        values = cells[1:]
        value = aggregate_values(values)
        add_to_results(results, filename, d, value)

def add_to_results(results, filename, d, value):
    if filename not in results.keys():
        results[filename] = {}
    assert d not in results[filename]
    results[filename][d] = value

def aggregate_values(values):
    if 'unsat' in values and 'sat' in values:
        return 'bug'
    if 'unsat' in values:
        return 'unsat'
    if 'sat' in values:
        return 'sat'
    assert 'unknown' in values
    return 'unknown'


if __name__ == "__main__":
    output_file = sys.argv[1]
    dirs = sys.argv[2:]
    main(output_file, dirs)
