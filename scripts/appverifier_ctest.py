#!/usr/bin/env python3
#
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Built-in
import argparse
import subprocess
import os
import json
import tempfile
import sys
import appverifier_xml

def add_app_verifier_settings(app_verified_executables, app_verifier_tests):
    for test_executable in app_verified_executables:
        arguments = ["appverif", "-enable"] + app_verifier_tests + ["-for", test_executable]
        print (f'Calling AppVerifier with: {subprocess.list2cmdline(arguments)}')
        # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
        # also set AppVerifier here too then, simplifying the setup and running process
        subprocess.run(args=arguments)

def remove_app_verifier_settings(app_verified_executables):
    for test_executable in app_verified_executables:
        arguments = ["appverif", "-delete", "settings", "-for", test_executable]
        print (f'Calling AppVerifier with: {subprocess.list2cmdline(arguments)}')
        # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
        # also set AppVerifier here too then, simplifying the setup and running process
        subprocess.run(args=arguments)

def main():
    argument_parser = argparse.ArgumentParser(
        description="AppVerifier Ctest runner util")
    argument_parser.add_argument("--build_directory", metavar="<Path to CTest project to run>",
                                required=True, default="../aws-c-common-build", help="Path to CMake build folder to run CTest in")
    parsed_commands = argument_parser.parse_args()

    ctest_execute_directory = parsed_commands.build_directory
    print (f"CTest execute directory: {ctest_execute_directory}")
    os.chdir(ctest_execute_directory)
    print (f"Current working directory {os.getcwd()}")
    tmp_xml_file_path = os.path.join(tempfile.gettempdir(), "tmp.xml")

    launch_arguments = ["ctest", "--show-only=json-v1"]
    print (f"Launching CTest with arguments: {subprocess.list2cmdline(launch_arguments)}")
    ctest_json_output = subprocess.run(args=launch_arguments, capture_output=True, encoding="utf8", check=True)

    output_json = json.loads(ctest_json_output.stdout)
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
    if (len(test_names) <= 0):
        sys.exit("ERROR: No tests found via CTest")

    # Register with AppVerifier
    add_app_verifier_settings(app_verified_executables, app_verifier_tests)

    # Run all the tests!
    for i in range(0, len(test_names)):
        try:
            print (f"Running test {test_names[i]} ({i}/{len(test_names)})")
            ctest_args = ["ctest", "-R", "^" + test_names[i] + "$"]
            print (f"With arguments: {subprocess.list2cmdline(ctest_args)}")
            subprocess.run(args=ctest_args)

            appverif_xml_dump_args = ["appverif", "-export", "log", "-for", test_executables[i], "-with", "to="+ tmp_xml_file_path]
            print (f'Calling AppVerifier with: {subprocess.list2cmdline(appverif_xml_dump_args)}')
            # NOTE: Needs elevated permissions
            subprocess.run(args=appverif_xml_dump_args)

            xml_result = appverifier_xml.parseXML(tmp_xml_file_path, True)
            if (xml_result != 0):
                print (f"ERROR: Test {test_names[i]} - failed!")
                remove_app_verifier_settings(app_verified_executables)
                sys.exit(xml_result)
        finally:
            # Delete the temporary XML file AppVerifier made on each run, ensuring we have a new one each time.
            # We cannot use tempfile directly and just pass the path to it, because
            # AppVerifier freaks out - so we just have to make files in a temporary directory
            # and delete them when we're finished
            os.remove(tmp_xml_file_path)

    # Delete AppVerifier settings
    remove_app_verifier_settings(app_verified_executables)

    print ("SUCCESS: Finished running all tests!")

if __name__ == "__main__":
    main()
