import sys
import os
import subprocess
import utils
import run_commands_on_dir

def main(dir_of_dirs_path, commands_txt_file, results_dir):
    dirs = os.listdir(dir_of_dirs_path)
    for directory in dirs:
        d = dir_of_dirs_path + "/" + directory
        run_commands_on_dir.main(d, commands_txt_file, results_dir)

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print('arg1: dir of dirs path\narg2: commands file\narg3: results dir')
        sys.exit(1)
    dir_of_dirs_path = sys.argv[1]
    commands = sys.argv[2]
    results_dir = sys.argv[3]
    main(dir_of_dirs_path, commands, results_dir)
