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

opt="$1"
result="results.txt"

# Start CBMC Batch Jobs
if [ "$opt" = "--start" ]; then
    for job in jobs/*/; do
        job=${job%/} #remove trailing slash
        job=${job#*/} #job name
        echo "Starting job $job"
            cbmc-batch \
                --no-report \
                --no-coverage \
                --wsdir jobs/$job \
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
        make -f $Makefile monitor
        make -f $Makefile copy
        dir=${Makefile#*-} # directory name from copy
        job=${dir%-local-*-*} # original job name
        check="$( python check_result.py $dir jobs/$job/cbmc-batch.yaml )"
        echo "$job: $check" >> $result
    done
# Cleanup
elif [ "$opt" = "--cleanup" ]; then
    for Makefile in Makefile-*-local-*; do
        make -f $Makefile cleanup
    done
else
    echo "Specify option --start to start jobs, --end to check results, and --cleanup to cleanup bookkeeping"
fi
