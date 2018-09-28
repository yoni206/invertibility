import sys
import os
import subprocess

TOTAL = "total"
DELIMITER = ";"

def main(output_file, results_dir):
    try:
        os.remove(output_file)
    except OSError:
        pass
    results = {}
    stats = init_stats(results_dir)
    for f in os.listdir(results_dir):
        process_file(results_dir + "/" + f, results, stats)
    print_stats(stats)
    write_to_file(results, output_file)

def print_stats(stats):
    for f in stats:
        print("\n" +f)
        for command in stats[f]:
            if command != TOTAL:
                print(command, ": ", stats[f][command]["unsat"])
        print(TOTAL, ": :", stats[f][TOTAL]["unsat"])

def init_stats(results_dir):
    stats = {}
    for f in os.listdir(results_dir):
        path = results_dir + "/" + f
        stats[path] = {}
        with open(path, 'r') as myfile:
            lines = [l.strip() for l in myfile.readlines()]
            titles = lines[0].split(DELIMITER)
            for command in titles[1:]:
                stats[path][command] = {}
                stats[path][command]["sat"] = 0
                stats[path][command]["unsat"] = 0
                stats[path][command]["unknown"] = 0
            stats[path][TOTAL] = {}
            stats[path][TOTAL]["sat"] = 0
            stats[path][TOTAL]["unsat"] = 0
            stats[path][TOTAL]["unknown"] = 0
    return stats

def write_to_file(results, output_file):
    title_columns = []
    title_columns.append('file')
    first_filename = list(results.keys())[0]
    columns = list(results[first_filename].keys())
    title_columns.extend(columns)
    with open(output_file, 'w') as myfile:
        myfile.write(DELIMITER.join(title_columns))
        myfile.write("\n")
        for filename in results.keys():
            line = filename
            for i in range(0, len(columns)):
                column = columns[i]
                line = line + DELIMITER + results[filename][column]
            myfile.write(line)
            myfile.write('\n')

def process_file(f, results, stats):
    with open(f, 'r') as myfile:
        lines = [l.strip() for l in myfile.readlines()]
    #ignore title
    for line in lines[1:]:
        cells = line.split(DELIMITER)
        filename = cells[0]
        values = cells[1:]
        add_to_results(results, filename, f, values)
        add_to_stats(stats, f, values, lines[0])

def add_to_stats(stats, f, values, title_line):
    #take commands (filename not needed
    commands = title_line.split(';')[1:]
    assert(len(commands) == len(values))
    length = len(commands)
    for i in range(0, length):
        increment(stats, f, commands[i], values[i])
    value = aggregate_values(values)
    increment(stats, f, TOTAL, value)

def increment(stats, f, command, value):
    if value != '':
        stats[f][command][value] += 1

def add_to_results(results, filename, d, values):
    value = aggregate_values(values)
    if filename not in results.keys():
        results[filename] = {}
    assert d not in results[filename]
    results[filename][d] = value

def aggregate_values(values):
    if 'unsat' in values and 'sat' in values:
        print('some solver has a bug!!!')
        assert(False)
    if 'unsat' in values:
        return 'unsat'
    if 'sat' in values:
        return 'sat'
    if 'unknown' in values:
        return 'unknown'
    else:
        print('panda ', values)
        assert(False)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("arg1: output file\narg2: results_dir")
        sys.exit(1)
    output_file = sys.argv[1]
    results_dir = sys.argv[2]
    main(output_file, results_dir)
