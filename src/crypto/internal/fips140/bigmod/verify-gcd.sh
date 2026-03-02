#!/bin/bash

scriptDir=$(dirname "$0")

fileName=$1

# flag whether this script is currently executed as part of a CI
isCi=$CI

gobraJar="/gobra/gobra.jar"
additionalGobraArgs="--parallelizeBranches --input nat.go nat-spec.gobra -I .verification"

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying package: $packageName"
fi

TIMEOUT=${2:-120}

echo "Verifying file: $fileName"
java -Xss128m -jar $gobraJar -I $scriptDir $additionalGobraArgs
exitCode=$?

if [ $isCi ]; then
    echo -e "\033[0Ksection_end:`date +%s`:verify\r\033[0K"
fi

# set exit code:
exit $exitCode
