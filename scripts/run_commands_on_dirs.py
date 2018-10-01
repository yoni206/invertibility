import sys
import os
import subprocess
import utils
import run_commands_on_dir

#skip list - don't run benchmarks from these directores
#SKIP_LIST = ["rec_ind"]
SKIP_LIST = []


def clear_log():
        try:
            os.remove('time.log')
        except OSError:
            print("time.log doesn't exist, which is ok")
            pass

def main(dir_of_dirs_path, commands_txt_file, results_dir, timeout):
    #clear time log
    clear_log()
    dirs = os.listdir(dir_of_dirs_path)

    for directory in [d for d in dirs if d not in SKIP_LIST]:
        d = dir_of_dirs_path + "/" + directory
        run_commands_on_dir.main(d, commands_txt_file, results_dir, timeout)

if __name__ == "__main__":
    if len(sys.argv) < 5:
        print('arg1: dir of dirs path\narg2: commands file\narg3: results dir\narg4=timeout')
        sys.exit(1)
    dir_of_dirs_path = sys.argv[1]
    commands = sys.argv[2]
    results_dir = sys.argv[3]
    timeout = sys.argv[4]
    main(dir_of_dirs_path, commands, results_dir, timeout)
