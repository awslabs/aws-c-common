#!/bin/sh

# Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

opt="$1"; shift
result="results.txt"

COMMANDS_IN_PATH=true
for i in cbmc-batch cbmc-status aws cbmc-kill cbmc; do
    command -v "$i" >/dev/null 2>&1 || {
        echo >&2 "Command $i required in \$PATH";
        COMMANDS_IN_PATH=false;
    }
done
if [ "$COMMANDS_IN_PATH" = false ]; then
    echo >&2 "Aborting."
    exit 1;
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$script_dir" || { echo "Cannot change directory to $script_dir"; exit 1; }

if [ "$#" = "0" ]; then
    all_jobs=""
    for job in jobs/*/; do
        job=${job%/} #remove trailing slash
        job=${job#*/} #job name
        all_jobs="$all_jobs $job"
    done
else
    all_jobs="$@"
fi

# Start CBMC Batch Jobs
if [ "$opt" = "--start" ]; then
    for job in $all_jobs; do
        echo "Starting job $job"
            cbmc-batch \
                --no-report \
                --no-coverage \
                --wsdir jobs/"$job" \
                --srcdir ../ \
                --jobprefix $job-local \
                --yaml jobs/$job/cbmc-batch.yaml
    done
# Check CBMC Batch Job Results
elif [ "$opt" = "--end" ]; then
    if [ -f $result ]; then
        rm $result
    fi
    for Makefile in Makefile-*-local-*; do
        make -f "$Makefile" monitor
        make -f "$Makefile" copy
        dir=${Makefile#*-} # directory name from copy
        job=${dir%-local-*-*} # original job name
        check="$( python3 check_result.py "$dir" jobs/"$job"/cbmc-batch.yaml )"
        echo "$job: $check" >> $result
    done
# Cleanup
elif [ "$opt" = "--cleanup" ]; then
    for Makefile in Makefile-*-local-*; do
        make -f "$Makefile" cleanup
    done
elif [ "$opt" = "--lsjobs" ]; then
    echo $all_jobs | tr '[[:space:]]' '\n'
else
    echo "Specify option --start to start jobs, --end to check results,"\
    "--cleanup to cleanup bookkeeping and --lsjobs to list jobs"
fi
