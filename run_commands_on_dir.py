import sys
import os
import subprocess

def main(dir_name, commands_txt_file):
    result_file = dir_name + "/" + "results.txt"
    try:
        os.remove(result_file)
    except OSError:
        pass
    with open(commands_txt_file, 'r') as f:
        commands = f.readlines()
    commands = [x.strip() for x in commands]
    files = os.listdir(dir_name)
    with open(result_file, 'w') as rf:
        rf.write(":".join(commands))
        rf.write("\n")
    process_files(files, dir_name, result_file, commands)

def process_files(files, directory, result_file, commands):
    results = {}
    for f in files:
        f_path = directory + "/" + f
        for command in commands:
            full_command = command + " " + f_path
            print(command)
            result_object = subprocess.run(full_command.split(), stdout=subprocess.PIPE)
            result_string = result_object.stdout.decode('utf-8').strip()
            results[command] = result_string
        line = f + ":"
        line = line + ":".join([results[command] for command in commands])
        with open(result_file, "a") as myfile:
            myfile.write(line)
            myfile.write("\n")


if __name__ == "__main__":
    dir_name = sys.argv[1]
    commands = sys.argv[2]
    main(dir_name, commands)
