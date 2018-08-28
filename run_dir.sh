#!/bin/bash
SMT_DIR=$1
COMMAND=$2
echo $SMT_DIR
echo $COMMAND
echo $OUTPUT_FILE
for f in $SMT_DIR/*smt2; do
        echo $f
        echo $COMMAND:$(eval $COMMAND $f) 
done;
