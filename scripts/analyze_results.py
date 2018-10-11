import sys
import os
import subprocess
import utils

TOTAL = "total"
DELIMITER = ";"

def main(output_file, results_dir, sygus_results_file):
    try:
        os.remove(output_file)
    except OSError:
        pass
    #all encodings, all configurations
    complete_results = {}
    print("\n")
    for f in os.listdir(results_dir):
        process_file(results_dir + "/" + f, complete_results)
    save_complete_csv(complete_results, output_file)
    results, stats = gen_results_and_stats(complete_results)
    save_short_csv(results, output_file, sygus_results_file)
    print_stats(stats)
    print_totals(results)
    print_redundents(complete_results)
    write_to_file(results, output_file)

def save_short_csv(results, output_file, sygus_results_file):
    csv_path = utils.get_file_or_dir_name_no_ext(output_file) + "_short.csv"
    title_line = "filename,inv,ltr,rtl"
    content_lines = []
    problem_names = sorted(list(set([filename[0:-len("_rtl.smt2")] for filename in results])))
    for problem in problem_names:
        ltr_results = [results[problem + "_ltr.smt2"][enc] for enc in results[problem + "_ltr.smt2"].keys()]
        ltr_result = "unsat" in ltr_results
        rtl_results = [results[problem + "_rtl.smt2"][enc] for enc in results[problem + "_rtl.smt2"].keys()]
        rtl_result = "unsat" in rtl_results
        inv = do_we_have_inverse(problem, sygus_results_file)
        line = str(problem) + "," + str(inv) + "," + str(ltr_result) + "," + str(rtl_result)
        content_lines.append(line)
    lines = [title_line]
    lines.extend(content_lines)
    utils.save_lines_to_file(lines, csv_path)

def do_we_have_inverse(problem, sygus_result_path):
    with open(sygus_result_path, "r") as f:
        inverse_results = f.readlines()
        sygus_name = problem
        sygus_name = sygus_name.replace("int_check", "find_inv")
        sygus_name = sygus_name.replace("_ltr.smt2", "4bit.smt2")
        sygus_name = sygus_name.replace("_rtl.smt2", "4bit.smt2")
        line = utils.get_line_starting_with(inverse_results, sygus_name)
        has_inv = "define-fun" in line
        return has_inv

def save_complete_csv(complete_results, output_file):
    csv_path = utils.get_file_or_dir_name_no_ext(output_file) + "_complete.csv"
    encodings, configurations = get_encodings_and_configurations(complete_results)
    #all possible combinations
    combinations = [[enc, conf] for enc in sorted(encodings) for conf in sorted(configurations)]
    combinations_as_strings = [enc + "_" + conf for enc in sorted(encodings) for conf in sorted(configurations)] 
    title_line = "filename" + "," + ",".join(combinations_as_strings)
    content_lines = []
    for filename in complete_results:
        results = []
        for combination in combinations:
            enc = combination[0]
            conf = combination[1]
            result = complete_results[filename][enc][conf]
            results.append(result)
        line = filename + "," + ",".join(results)
        content_lines.append(line)
    lines = [title_line]
    lines.extend(content_lines)
    utils.save_lines_to_file(lines, csv_path)


def get_encodings_and_configurations(complete_results):
    #infer encodings and configs by the first entry
    first_filename = list(complete_results.keys())[0]
    encodings = complete_results[first_filename].keys()
    encodings = sorted(list(encodings))
    first_encoding = encodings[0]
    configurations = complete_results[first_filename][first_encoding].keys()
    configurations = sorted(list(configurations))
    return encodings, configurations

def get_red_encodings(redundents, encodings, configurations):
    result = []
    for enc in encodings:
        red = True
        for conf in configurations:
            if [enc, conf] not in redundents:
                red = False
        if red:
            result.append(enc)
    return result


def get_red_configs(redundents, encodings, configurations):
    result = []
    for conf in configurations:
        red = True
        for enc in encodings:
            if [enc, conf] not in redundents:
                red = False
        if red:
            result.append(conf)
    return result

def print_redundents(complete_results):
    print("\n")
    encodings, configurations = get_encodings_and_configurations(complete_results)
    redundents = []
    for enc in encodings:
        for config in configurations:
            if is_redundent(enc, config, complete_results):
                redundents.append([enc, config])
    redundent_encodings = get_red_encodings(redundents, encodings, configurations)
    redundent_configs = get_red_configs(redundents, encodings, configurations)
    if redundents:
        print("The followings pairs were redundent:")
        print(redundents)
        if redundent_encodings:
            print("\n")
            print("The following encodings were redundent:")
            print(redundent_encodings)
        if redundent_configs:
            print("\n")
            print("The following configs were redundent:")
            print(redundent_configs)

    else: 
        print("nothing was redundent")

def copy_without(complete_results, enc, config):
    encodings, configurations = get_encodings_and_configurations(complete_results)
    complete_results_without = {}
    for filename in complete_results:
        complete_results_without[filename] = {}
        for encoding in encodings:
            complete_results_without[filename][encoding] = {}
            for conf in configurations:
                if encoding != enc or conf != config:
                    complete_results_without[filename][encoding][conf] = complete_results[filename][encoding][conf]
    return complete_results_without

def proved(filename, complete_results):
    values = []
    for enc in complete_results[filename].keys():
        for conf in complete_results[filename][enc].keys():
            values.append(complete_results[filename][enc][conf])
    is_proved = "unsat" in values
    return is_proved

def is_redundent(enc, config, complete_results):
    proved_with = set([filename for filename in complete_results.keys() if proved(filename, complete_results)])
    complete_results_without = copy_without(complete_results, enc, config)
    proved_without = set([filename for filename in complete_results.keys() if proved(filename, complete_results_without)])
    benefit = proved_with - proved_without
    if benefit:
        one_benefit = sorted(list(benefit))[0]
    return len(benefit) == 0
    
def name_of_ic(s):
    return "_".join((s.split("_"))[0:4])

def print_totals(results):
    proved_formulas = set([f for f in results if "unsat" in [d for [c,d] in results[f].items()] ])
    proved_formulas_ltr = set([name_of_ic(l) for l in proved_formulas if name_of_ic(l)+"_ltr.smt2" in proved_formulas]) 
    proved_formulas_rtl = set([name_of_ic(l) for l in proved_formulas if name_of_ic(l)+"_rtl.smt2" in proved_formulas]) 
    proved_ics = proved_formulas_ltr.intersection(proved_formulas_rtl)
    proved_only_ltr = proved_formulas_ltr - proved_formulas_rtl
    proved_only_rtl = proved_formulas_rtl - proved_formulas_ltr
    print("\n")
    print("total formulas proved: ", len(proved_formulas))
    print("only ltr: ", len(proved_only_ltr))
    print("only rtl: ", len(proved_only_rtl))
    print("total ics proved (both ltr and rtl): ", len(proved_ics))
    

def print_stats(stats):
    for f in stats:
        print("\n" +f)
        for command in stats[f]:
            if command != TOTAL:
                print(command, ": ", stats[f][command]["unsat"])
        print(TOTAL, ": :", stats[f][TOTAL]["unsat"])

def init_stats(encodings, configurations):
    stats = {}
    for enc in encodings:
        stats[enc] = {}
        for config in configurations:
            stats[enc][config] = {}
            stats[enc][config]["sat"] = 0
            stats[enc][config]["unsat"] = 0
            stats[enc][config]["unknown"] = 0
            stats[enc][config]["timeout"] = 0
            stats[enc][config]["skip"] = 0
        stats[enc][TOTAL] = {}
        stats[enc][TOTAL]["sat"] = 0
        stats[enc][TOTAL]["unsat"] = 0
        stats[enc][TOTAL]["unknown"] = 0
        stats[enc][TOTAL]["timeout"] = 0
        stats[enc][TOTAL]["skip"] = 0
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

def process_file(f, complete_results):
    with open(f, 'r') as myfile:
        lines = [l.strip() for l in myfile.readlines()]
    configurations_line = lines[0]
    #ignore smt2-filename
    configurations = configurations_line.split(DELIMITER)[1:]
    #ignore title
    for line in lines[1:]:
        cells = line.split(DELIMITER)
        filename = cells[0]
        values = cells[1:]
        add_to_complete_results(complete_results, filename, f, values, configurations)

def gen_results_and_stats(complete_results):
    encodings, configurations = get_encodings_and_configurations(complete_results)
    #init
    stats = init_stats(encodings, configurations)
    results = {}
    
    #fill
    for filename in complete_results:
        for encoding in encodings:
            values = [complete_results[filename][encoding][config] for config in configurations]
            add_to_results(results, filename, encoding, values)
            add_to_stats(stats, encoding, values, configurations)
    return results, stats

def add_to_complete_results(complete_results, filename, f, values, configurations):
    for i in range(0, len(configurations)):
        config = configurations[i]
        value = values[i]
        if filename not in complete_results:
            complete_results[filename] = {}
        if f not in complete_results[filename]:
            complete_results[filename][f] = {}
        complete_results[filename][f][config] = value

def add_to_stats(stats, f, values, configurations):
    #take commands (filename not needed
    commands = configurations
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
    elif 'unsat' in values:
        return 'unsat'
    elif 'sat' in values:
        return 'sat'
    elif 'unknown' in values:
        return 'unknown'
    elif 'timeout' in values:
        return 'timeout'
    elif 'skip' in values:
        return 'skip'
    else:
        print('panda ', values)
        assert(False)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("arg1: output file\narg2: results_dir\narg3: sygus results file")
        sys.exit(1)
    output_file = sys.argv[1]
    results_dir = sys.argv[2]
    sygus_results_file = sys.argv[3]
    main(output_file, results_dir, sygus_results_file)
