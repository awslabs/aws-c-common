# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Built-in
from asyncio import subprocess
import argparse
import subprocess
import os
import json
# Needs to be installed via pip
from termcolor import colored  # - for terminal colored output

def main():
    argument_parser = argparse.ArgumentParser(
        description="AppVerifier Ctest runner util")
    argument_parser.add_argument("--ctest_path", metavar="<Absolute path to CTest project to run>",
                                required=True, default="../aws-c-common", help="Absolute path to CMake project containing CTest to run")
    argument_parser.add_argument("--build_directory", metavar="<Absolute path to CTest project to run>",
                                required=True, default="../aws-c-common-build", help="Absolute path to CMake build folder")
    argument_parser.add_argument("--xml_util_path", metavar="<Absolute path to appverifier_xml_util.py>",
                                required = True, default="./appverifier_xml_util.py", help="Absolute path to AppVerifier XML Utility script")
    argument_parser.add_argument("--xml_file_path", metavar="<Absolute path to XML file output>",
                                required = True, default="./xml_output.xml", help="Absolute path to where you want XML from AppVerifier to be ouput to")
    parsed_commands = argument_parser.parse_args()

    os.chdir(parsed_commands.build_directory)

    launch_arguments = ["ctest", parsed_commands.ctest_path, "--show-only=json-v1"]
    sample_return = subprocess.run(args=launch_arguments, capture_output=True, encoding="utf8")
    if (sample_return.returncode != 0):
        print (colored("CTest returned error!", color="red"), flush=True)
    
    output_json = json.loads(sample_return.stdout)
    test_names = []
    test_executables = []

    # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
    # also set AppVerifier here too then, simplifying the setup and running process
    app_verified_executables = []
    app_verifier_tests = ["Exceptions", "Handles", "Heaps", "Leak", "Locks", "Memory", "SRWLock", "Threadpool", "TLS"]

    json_tests_list = output_json["tests"]
    for test_data in json_tests_list:
        test_names.append(test_data["name"])
        tmp_path = os.path.basename(test_data["command"][0])
        test_executables.append(tmp_path)

        if not (tmp_path in app_verified_executables):
            app_verified_executables.append(tmp_path)
            # arguments = ["appverif", "-enable"] + app_verifier_tests + ["-for", test_data["command"][0]]
            arguments = ["appverif", "-enable"] + app_verifier_tests + ["-for", tmp_path]
            # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
            # also set AppVerifier here too then, simplifying the setup and running process
            subprocess.run(args=arguments)
    
    # Run all the tests!
    for i in range(0, len(test_names)):
        print ("Running test " + test_names[i] + "(" + str(i) + "/" + str(len(test_names)) + ")", flush=True)
        subprocess.run(args=["ctest", parsed_commands.ctest_path, "-R", "^" + test_names[0] + "$"])

        # NOTE: Needs elevated permissions, not sure on best way to work around this...
        subprocess.run(args=["appverif", "-export", "log", "-for", test_executables[0], "-with", "to="+ str(parsed_commands.xml_file_path)])

        xml_verif = subprocess.run(args=["python", parsed_commands.xml_util_path, "--parse_xml", "True", "--xml_file", parsed_commands.xml_file_path])
        if (xml_verif.returncode != 0):
            print (colored("Test " + test_names[i] + "failed!", "red"), flush=True)
            exit(xml_verif.returncode)
        else:
            print (colored("Test " + test_names[i] + "passed!", "green"), flush=True)
        
        # Delete XML file
        os.remove(str(parsed_commands.xml_file_path))
    
    # Delete AppVerifier settings
    for test_executable in app_verified_executables:
        # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
        # also set AppVerifier here too then, simplifying the setup and running process
        subprocess.run(args=["appverif", "-delete", "settings", "-for", test_executable])
    
    print (colored("Finished running all tests!", "green"), flush=True)
    exit(0)

if __name__ == "__main__":
    main()
