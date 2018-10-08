import sys
import os
import subprocess
import utils
import multiprocessing as mp
import time

DELIMITER = ";"
SC_PREFIX = "(define-fun SC"
USUAL_LOGIC = "(set-logic UFNIA)"
QF_LOGIC = "(set-logic QF_UFNIA)"
TMP_DIR_FOR_YICES_AND_MATHSAT = "/home/yoniz/tmp/inv"
tmp_path = ""

def main(dir_path, commands_txt_file, results_dir, timeout):
    global tmp_path
    dir_name = utils.get_file_or_dir_name_no_ext(dir_path)
    tmp_path = TMP_DIR_FOR_YICES_AND_MATHSAT + "/" + dir_name
    if os.path.exists(tmp_path):
        print('run: rm -rf '+ TMP_DIR_FOR_YICES_AND_MATHSAT + "/*")
        exit(1)
    os.mkdir(tmp_path)
    if not os.path.exists(results_dir):
        print('results dir does not exist' )
        exit(1)
    result_file = results_dir + "/" + dir_name + ".txt"
    try:
        os.remove(result_file)
    except OSError:
        pass
    with open(commands_txt_file, 'r') as f:
        commands = f.readlines()
    commands = [x.strip() for x in commands]
    files = [f for f in os.listdir(dir_path) if f.endswith(".smt2")]
    with open(result_file, 'w') as rf:
        rf.write("filename")
        rf.write(DELIMITER)
        rf.write(DELIMITER.join(commands))
        rf.write("\n")
    process_files(files, dir_path, result_file, commands, timeout)


def process_files(files, directory, result_file, commands, timeout):
    pool = mp.Pool()
    for f in files:
        f_path = directory + "/" + f
        res = pool.apply_async(process_file,
            args = (f_path,commands,result_file,f,timeout), callback = handler, error_callback = error_handler)
    pool.close()
    pool.join()

def handler(tup): #tup = (results, result_file,commands)
    write_to_file(tup[0], tup[1], tup[2], tup[3])

def error_handler(arg):
    print('fail!!!! check why!')

def write_to_file(results, result_file, commands,f):
        line = f + DELIMITER
        line = line + DELIMITER.join([results[command] for command in commands])
        with open(result_file, "a") as myfile:
            myfile.write(line)
            myfile.write("\n")

def yices_or_mathsat_cmd(command):
    result = ("yices-smt2" in command) or ("mathsat" in command)
    return result

def qf_dir(path):
    return "/qf/" in path

def rtl_path(path):
    return "_rtl" in path


def run(full_command, timeout):
        try:
            result_object = subprocess.run(full_command.split(), stdout=subprocess.PIPE, timeout=int(timeout))
            result_string = result_object.stdout.decode('utf-8').strip()
        except subprocess.TimeoutExpired:
            result_string = "timeout"
        return result_string

def sc_has_exists(path):
    with open(path, 'r') as f:
        lines = f.readlines()
    sc_line = get_sc_line(lines)
    return "exists" in sc_line

def get_sc_line(lines):
    candidates = [l for l in lines if l.startswith(SC_PREFIX)]
    assert(len(candidates) == 1)
    return candidates[0]

def further_massage_for_yices_and_mathsat(path):
    name = utils.get_file_or_dir_name_no_ext(path)
    result_path = tmp_path +  "/" + name + "_tmp.smt2"
    with open(path, 'r') as f:
        lines = f.readlines()
    assert(lines[0].strip() == USUAL_LOGIC)
    lines[0] = QF_LOGIC
    with open(result_path, 'w') as g:
        g.write("\n".join(lines))
        g.write("\n")
    return result_path


def get_result(command, f_path, timeout):
        print("running: ", command, f_path) 
        start = time.time()
        #yices and mathsat should only run on qf rtl.
        if (yices_or_mathsat_cmd(command)):
            if (qf_dir(f_path) and rtl_path(f_path) and (not sc_has_exists(f_path))):
                tmp_path = further_massage_for_yices_and_mathsat(f_path)
                full_command = command + " " + tmp_path
                result_string = run(full_command, timeout)
                #os.remove(tmp_path)
            else:
                result_string = "skip"
        else:
            full_command = command + " " + f_path
            result_string = run(full_command, timeout)
        end = time.time()
        log_time(start, end, command + " " + f_path, result_string)
        return result_string


def log_time(start, end, full_command, result):
        with open("time.log", 'a') as timelog:
            timelog.write(full_command + ": " + str(end-start) + ": " + result + "\n")

def process_file(f_path, commands, result_file,f, timeout):
    results = {}
    for command in commands:
        result_string = get_result(command, f_path, timeout)
        results[command] = result_string
    return (results,result_file,commands,f,)


if __name__ == "__main__":
    if len(sys.argv) < 5:
        print('arg1: dir path\narg2: commands file\narg3: results dir\narg4: timeout')
        exit(1)
    dir_path = sys.argv[1]
    commands = sys.argv[2]
    results_dir = sys.argv[3]
    timeout = int(sys.argv[4])
    main(dir_path, commands, results_dir, timeout)
