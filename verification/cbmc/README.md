# CBMC Batch

Running CBMC Batch jobs for a project.

## Expected Directory Structure

    project
    │   ...   
    │
    └───.cbmc-batch
    │   │   ...
    │   │
    │   └───jobs
    │       └───job1
    │       │   |    Makefile
    │       │   |    cbmc-batch.yaml
    │       └───job2
    │       │   |    Makefile
    │       │   |    cbmc-batch.yaml
    │       ...

It is expected that the repository contains a directory `.cbmc-batch`, which itself contains a directory `jobs`. Each directory in `.cbmc-batch/jobs` should correspond to a CBMC Batch job. Each job directory must contain a `Makefile` to be used by CBMC Batch to build the goto for CBMC and a `cbmc-batch.yaml` file to provide CBMC Batch options and provide an expected substring in the result of the CBMC run.

## Running Locally

In order to start the CBMC Batch jobs and check results locally, you need to have installed CBMC Batch.

You can start the CBMC Batch jobs locally by running

    bash cbmc-batch.sh --start

You can then check CBMC Batch results locally by running

	bash cbmc-batch.sh --end

This will run until all the jobs have finished and output results in `results.txt`.

You can clean up the local CBMC Batch bookkeeping files by running

    bash cbmc-batch.sh --cleanup
