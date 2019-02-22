#!/bin/bash

exp_base_dir="/barrett/scratch/yoniz/git/invertibility/int_IC"
cvc4_binary="/barrett/scratch/yoniz/git/CVC4/build/bin/cvc4"
z3_binary="/barrett/scratch/yoniz/git/z3/build/z3"
vampire_binary="/barrett/scratch/preiner/papers/2019-cade/solvers/vampire-wrapper.sh"
partition="normal"         # default
num_cores=1
space_limit="4000"

benchmark_set=foo_no_axioms
time_limit=300
subdir_name=cluster_results_no_axioms

#
# cvc4 runs
#
#directory_name="$exp_base_dir/$subdir_name/cvc4_default"
#options=""
#echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary

directory_name="$exp_base_dir/$subdir_name/cvc4_tplanes"
options="--nl-ext-tplanes"
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary
#
#directory_name="$exp_base_dir/$subdir_name/cvc4_tplanes_fmf"
#options="--nl-ext-tplanes --fmf-fun-rlv"
#echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary
#
#directory_name="$exp_base_dir/$subdir_name/cvc4_tplanes_cbqi"
#options="--nl-ext-tplanes --cbqi-all"
#echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary

directory_name="$exp_base_dir/$subdir_name/cvc4_tplanes_saturate_no_e_matching"
options="--nl-ext-tplanes --full-saturate-quant --no-e-matching"
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary

directory_name="$exp_base_dir/$subdir_name/cvc4_tplanes_saturate_interleave"                                    
options="--nl-ext-tplanes --full-saturate-quant --fs-interleave"                                                                             
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary     

#directory_name="$exp_base_dir/$subdir_name/cvc4_cbqi"
#options="--cbqi-all"
#echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary
#
#directory_name="$exp_base_dir/$subdir_name/cvc4_fmf"
#options="--fmf-fun-rlv"
#echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $cvc4_binary

# z3 runs
#
directory_name="$exp_base_dir/$subdir_name/z3_default"
options=""
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $z3_binary
#

#vampire runs
directory_name="$exp_base_dir/$subdir_name/vampire"
options="--ignore_missing on --mode smtcomp"
echo -e "$benchmark_set\n$directory_name\n$options\n$partition\n$time_limit\n$space_limit\n$num_cores\n" | submit-solver.sh $vampire_binary
