import sys
import os
import subprocess
import utils
import multiprocessing as mp

def main(dir_path, commands_txt_file, results_dir):
    dir_name = utils.get_file_or_dir_name_no_ext(dir_path)
    if not os.exists(results_dir):
        print('results dir does not exist' )
    result_file = results_dir + "/" + dir_name + ".txt"
    try:
        os.remove(result_file)
    except OSError:
        pass
    with open(commands_txt_file, 'r') as f:
        commands = f.readlines()
    commands = [x.strip() for x in commands]
    files = os.listdir(dir_path)
    with open(result_file, 'w') as rf:
        rf.write(":".join(commands))
        rf.write("\n")
    process_files(files, dir_path, result_file, commands)

def process_files(files, directory, result_file, commands):
    pool = mp.Pool()
    handler = lambda results: write_to_file(results, result_file, commands)
    process_file_for_commands = lambda f_path: process_file(f_path, commands)
    for f in files:
        f_path = directory + "/" + f
        pool.apply_async(process_file_for_commands, args = (f_path,), callback = handler)
    pool.close()
    pool.join()

def write_to_file(results, result_file, commands):
        line = f + ":"
        line = line + ":".join([results[command] for command in commands])
        with open(result_file, "a") as myfile:
            myfile.write(line)
            myfile.write("\n")

def process_file(f_path, commands):
    results = {}
    for command in commands:
        full_command = command + " " + f_path
        result_object = subprocess.run(full_command.split(), stdout=subprocess.PIPE)
        result_string = result_object.stdout.decode('utf-8').strip()
        results[command] = result_string
        print(command, f_path, ": ", result_string)
    return results


if __name__ == "__main__":
    dir_path = sys.argv[1]
    commands = sys.argv[2]
    results_dir = sys.argv[3]
    main(dir_path, commands, results_dir)
