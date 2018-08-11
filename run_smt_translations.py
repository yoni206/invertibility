import sys
import os
import subprocess

directory = ""
result_file= ""
timeout = 1000

def main(dir_name, arg_timeout):
    global directory
    global result_file
    global timeout
    directory = dir_name
    result_file = directory + "/" + "results.txt"
    timeout = arg_timeout
    try:
        os.remove(result_file)
    except OSError:
        pass
    files = os.listdir(directory)
    process_files(files)

def process_files(files):
    for f in files:
        f_path = directory + "/" + f
        timeout_arg = "--t:" + str(timeout)
        z3_command = ["z3", timeout_arg, f_path]
        result_object = subprocess.run(z3_command, stdout=subprocess.PIPE)
        result_string = result_object.stdout.decode('utf-8')
        with open(result_file, "a") as myfile:
            myfile.write(": ".join([f, result_string]))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
