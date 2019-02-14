#!/bin/sh
#SBATCH -e /dev/null
#SBATCH -o /dev/null
#SBATCH -c 1
#SBATCH -a 1-21
#SBATCH --qos=normal
#SBATCH -t 00:00:3600
#SBATCH -D /barrett/scratch/yoniz/git/invertibility/lemmas/cluster_results/z3_default

prefix="/barrett/scratch/yoniz/git/invertibility/lemmas/bench/"
runlim_binary="/barrett/scratch/local/bin/runlim"
runlim_options="--time-limit=3600 --space-limit=4000"
solver="./z3"
solver_options=""
benchmarks="/barrett/scratch/yoniz/git/invertibility/lemmas/cluster_results/z3_default/benchmarks"
scrambler=""

# pick benchmark file from list of benchmarks
benchmark="`sed ${SLURM_ARRAY_TASK_ID}'q;d' $benchmarks`"
out="$(echo ${benchmark#$prefix} | sed -e 's,/,-,g')"
# set stdout log file
log="/barrett/scratch/yoniz/git/invertibility/lemmas/cluster_results/z3_default/${out}.log"
# set stderr log file
err="/barrett/scratch/yoniz/git/invertibility/lemmas/cluster_results/z3_default/${out}.err"

(
filename="$(basename $benchmark)"
extension="${filename##*.}"
[ -n "$extension" ] && extension=".$extension"
benchmark_tmp="$(mktemp --suffix="$extension" /tmp/XXXXXXXX)"

echo "c host: $(hostname)"
echo "c start: $(date)"
echo "c benchmark: $benchmark"
echo "c solver: $solver"
echo "c solver options: $solver_options"

# copy benchmark from NFS to /tmp
cp "$benchmark" "$benchmark_tmp"

# scramble benchmark if scrambler is given
if [ -e "$scrambler" ]; then
  benchmark_tmp_scrambled="${benchmark_tmp}_scrambled"
  $scrambler "$benchmark_tmp"  > \
    "$benchmark_tmp_scrambled"
  mv "$benchmark_tmp_scrambled" "$benchmark_tmp"
fi

$runlim_binary $runlim_options "$solver" $solver_options "$benchmark_tmp"

# remove benchmark from /tmp
rm -f "$benchmark_tmp"

echo "c done"
) > "$log" 2> "$err"
