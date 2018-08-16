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
        cvc4_timeout_arg = "--tlimit=" + str(timeout)
        cvc4_command = ["cvc4", cvc4_timeout_arg, f_path]
        cvc4_result_object = subprocess.run(cvc4_command, stdout=subprocess.PIPE)
        cvc4_result_string = cvc4_result_object.stdout.decode('utf-8').strip()
        cvc4_result_string = cvc4_result_string.replace('\n',":")
        with open(result_file, "a") as myfile:
            myfile.write(":".join([f, cvc4_result_string]))
            myfile.write("\n")


if __name__ == "__main__":
    directory = sys.argv[1]
    timeout = sys.argv[2]
    main(directory, timeout)
