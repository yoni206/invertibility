import sys
import os

def main(result_path):
    fixed_path = result_path + "_fixed.txt"
    try:
        os.remove(fixed_path)
    except OSError:
        pass
    orig_file = open(result_path, "r")
    new_file = open(fixed_path, "a" )
    previous_line = ""
    for line in orig_file:
        if line.startswith("(define"):
            new_file.write(previous_line.strip() + ";" + line)
            previous_line = ""
        else:
            new_file.write(previous_line)
            previous_line = line
    orig_file.close()
    new_file.close()

if __name__ == "__main__":
    main(sys.argv[1])
