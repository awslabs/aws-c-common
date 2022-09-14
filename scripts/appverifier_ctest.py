# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Built-in
import argparse
import subprocess
import os
import json
import tempfile

def add_app_verifier_settings(app_verified_executables, app_verifier_tests):
    for test_executable in app_verified_executables:
        arguments = ["appverif", "-enable"] + app_verifier_tests + ["-for", test_executable]
        print (f'Calling AppVerifier with: {subprocess.list2cmdline(arguments)}', flush=True)
        # NOTE: Needs elevated permissions. We need this for the XML dump below so I figured we might as well
        # also set AppVerifier here too then, simplifying the setup and running process
        subprocess.run(args=arguments)

def remove_app_verifier_settings(app_verified_executables):
    for test_executable in app_verified_executables:
        arguments = ["appverif", "-delete", "settings", "-for", test_executable]
        print (f'Calling AppVerifier with: {subprocess.list2cmdline(arguments)}', flush=True)
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
    xml_util_path = os.path.join(os.path.dirname(__file__), "appverifier_xml.py")
    tmp_xml_file_path = os.path.join(tempfile.gettempdir(), "tmp.xml")

    launch_arguments = ["ctest", "--show-only=json-v1"]
    print (f"Launching CTest with arguments: {subprocess.list2cmdline(launch_arguments)}")
    sample_return = subprocess.run(args=launch_arguments, capture_output=True, encoding="utf8")
    if (sample_return.returncode != 0):
        print (f"ERROR: CTest returned error! {sample_return.returncode}", flush=True)
    
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
    if (len(test_names) <= 0):
        print("ERROR: No tests found via CTest")
        exit(-1)

    # Register with AppVerifier
    add_app_verifier_settings(app_verified_executables, app_verifier_tests)

    # Run all the tests!
    for i in range(0, len(test_names)):
        print (f"Running test {test_names[i]} ({str(i)}/{str(len(test_names))})", flush=True)
        ctest_args = ["ctest", "-R", "^" + test_names[0] + "$"]
        print (f"With arguments: {subprocess.list2cmdline(ctest_args)}")
        subprocess.run(args=ctest_args)

        appverif_xml_dump_args = ["appverif", "-export", "log", "-for", test_executables[0], "-with", "to="+ tmp_xml_file_path]
        print (f'Calling AppVerifier with: {subprocess.list2cmdline(appverif_xml_dump_args)}', flush=True)
        # NOTE: Needs elevated permissions
        subprocess.run(args=appverif_xml_dump_args)

        xml_parser_args = ["python", xml_util_path, "--xml_file", tmp_xml_file_path]
        print (f'Calling XML parser utility with: {subprocess.list2cmdline(xml_parser_args)}', flush=True)
        xml_verif = subprocess.run(args=xml_parser_args)
        if (xml_verif.returncode != 0):
            print (f"ERROR: Test {test_names[i]} - failed!", flush=True)
            os.remove(tmp_xml_file_path)
            remove_app_verifier_settings(app_verified_executables)
            exit(xml_verif.returncode)
        else:
            print (f"SUCCESS: Test {test_names[i]} - passed!", flush=True)
        
        # Delete the temporary XML file AppVerifier made
        # We cannot use tempfile directly and just pass the path to it, because
        # AppVerifier freaks out - so we just have to make files in a temporary directory
        # and delete them when we're finished
        os.remove(tmp_xml_file_path)
    
    # Delete AppVerifier settings
    remove_app_verifier_settings(app_verified_executables)
    
    print ("SUCCESS: Finished running all tests!", flush=True)
    exit(0)

if __name__ == "__main__":
    main()
