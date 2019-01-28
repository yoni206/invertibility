#!/bin/bash

exp_base_dir="/barrett/scratch/yoniz/git/invertibility/cond_inv_synthesis"
cvc4_binary="/barrett/scratch/yoniz/git/CVC4/build/bin/cvc4"
z3_binary="/barrett/scratch/yoniz/git/z3/build/z3"
partition="normal"         # default
num_cores=1
space_limit="4000"

benchmark_set=foo
time_limit=5
subdir_name=cluster_results

#
# cvc4 runs
#
directory_name="$exp_base_dir/$subdir_name/cvc4_default"
options=""
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary

