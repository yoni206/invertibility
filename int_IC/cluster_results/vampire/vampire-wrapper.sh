#!/bin/bash

base_dir="/barrett/scratch/preiner/papers/2019-cade/solvers/vampire-git"
LD_LIBRARY_PATH="$base_dir/include/" $base_dir/vampire $*
