#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

import sys
import argparse
import yaml
import os

def check_result():
    parser = argparse.ArgumentParser(description = "Check CBMC Batch outputs against expected result.")
    parser.add_argument("batch_result_dir", help = "The directory containing the CBMC Batch result.")
    parser.add_argument("yaml", help = "The yaml containing expected CBMC Batch result substring.")
    args = parser.parse_args()
    if not os.path.isfile(args.yaml):
        print("Expected file " + args.yaml + ": Not found")
        return
    with open(args.yaml, "r") as yaml_file:
        try:
            expected = yaml.load(yaml_file)["expected"]
        except yaml.YAMLError as e:
            print(e)
            return
        except KeyError as e:
            print("Expected CBMC Batch result not found in " + args.yaml)
            return
    cbmc_output = os.path.join(args.batch_result_dir, "cbmc.txt")
    if not os.path.isfile(cbmc_output):
        print("Expected file " + cbmc_output + ": Not found")
    with open(cbmc_output, "r") as cbmc:
        if expected in cbmc.read():
            print("Expected output matches.")
        else:
            print("Expected output does not match.")

if __name__ == "__main__":
    check_result()
