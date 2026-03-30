#!/bin/bash

scriptDir=$(dirname "$0")

BENCH_RUNS=${1:-}

# flag whether this script is currently executed as part of a CI
isCi=$CI

gobraJar="/gobra/gobra.jar"
additionalGobraArgs="--parallelizeBranches --input nat.go nat-spec.gobra sync_flag_fixed.go -I .verification"


JAVA_CMD="java -Xss128m -jar $gobraJar -I $scriptDir $additionalGobraArgs"

if [[ -n "${BENCH_RUNS}" ]]; then
    echo "Benchmarking GCD verification ($BENCH_RUNS runs)"
    for i in $(seq 1 "$BENCH_RUNS"); do
        echo "--- Run $i/$BENCH_RUNS ---"
        sudo nice -n -20 caffeinate -s time $JAVA_CMD
        exitCode=$?
        if [[ $exitCode -ne 0 ]]; then
            echo "Run $i failed with exit code $exitCode"
            break
        fi
    done
else
    echo "Verifying GCD implementation"
    $JAVA_CMD
    exitCode=$?
fi

# set exit code:
exit $exitCode
