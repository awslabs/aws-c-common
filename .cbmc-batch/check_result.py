#!/usr/bin/env python3
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
