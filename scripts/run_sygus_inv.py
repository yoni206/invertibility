import sys
import multiprocessing as mp
import os
import subprocess

DELIMITER = ";"

def main(dir_name, arg_timeout, output_path):
    directory = dir_name
    result_file = output_path
    timeout = arg_timeout
    dirs = os.listdir(directory)
    #in order to not re-run stuff that we already found
    if os.path.exists(result_file):
        results = get_results_from_file(result_file)
    else:
        results = init_results
    for d in dirs:
        process_dir(directory + "/" + d, timeout, results)
    #each directory now has a "results.txt file.
    #we analyze it.
    results = {}
    write_results_to_file(dirs, results, result_file)

def write_results_to_file(dirs, results, result_file):
    with open(result_file, "w") as f:
        f.write("filename" + DELIMITER + DELIMITER.join(dirs))
        f.write("\n")
        for filename in results:
            f.write(filename + DELIMITER + DELIMITER.join([results[filename][d] for d in dirs]))
            f.write("\n")
            
        f.close()

def process_dir(d, timeout, results):
    files = os.listdir(d)
    process_files(d, files, timeout, results)

def process_files(dirname, files, timeout):
    pool = mp.Pool()
    for f in files:
        res = pool.apply_async(process_file,
            args = (dirname,f, timeout), callback = handler, error_callback = error_handler)
    pool.close()
    pool.join()

def error_handler(arg):
    print('fail!!!! check why!')


def process_file(dirname, f, timeout):
        f_path = dirname + "/" + f
        cvc4_command = ["cvc4", f_path]
        print("running ", f_path)
        try: 
            cvc4_result_object = subprocess.run(cvc4_command, stdout=subprocess.PIPE, timeout=int(timeout))
            cvc4_result_string = cvc4_result_object.stdout.decode('utf-8').strip()
            cvc4_result_string = cvc4_result_string.replace('\n',DELIMITER)
        except subprocess.TimeoutExpired:
            cvc4_result_string = "timeout"
        return (cvc4_result_string, dirname, f)

def handler(tup): #tup = result_string, dirname, file
    result_string = tup[0]
    dirname = tup[1]
    filename = tup[2]
    with open(dirname + "/results.txt", "a") as myfile:
         myfile.write(DELIMITER.join([filename, result_string]))
         myfile.write("\n")
         myfile.close()

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("arg1: dir of dirs of smt files\narg2: timeout\narg3: output_file")
        sys.exit(1)
    directory = sys.argv[1]
    timeout = sys.argv[2]
    output_path = sys.argv[3]
    main(directory, timeout, output_path)
