import sys
import os
import subprocess

def main(dir_name, arg_timeout):
    directory = dir_name
    result_file = directory + "/" + "results.txt"
    timeout = arg_timeout
    try:
        os.remove(result_file)
    except OSError:
        pass
    files = os.listdir(directory)
    process_files(files, directory, result_file, timeout)

def process_files(files, directory, result_file, timeout):
    for f in files:
        f_path = directory + "/" + f
        z3_timeout_arg = "--t:" + str(timeout)
        cvc4_timeout_arg = "--tlimit=" + str(timeout)
        z3_command = ["z3", z3_timeout_arg, f_path]
        cvc4_command = ["cvc4", cvc4_timeout_arg, f_path]
        z3_result_object = subprocess.run(z3_command, stdout=subprocess.PIPE)
        z3_result_string = z3_result_object.stdout.decode('utf-8').strip()
        cvc4_result_object = subprocess.run(cvc4_command, stdout=subprocess.PIPE)
        cvc4_result_string = cvc4_result_object.stdout.decode('utf-8').strip()
        with open(result_file, "a") as myfile:
            myfile.write(":".join([f, z3_result_string, cvc4_result_string]))
            myfile.write("\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
