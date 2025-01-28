#!/usr/bin/env python3
import argparse
import os
from pathlib import Path
import platform
import re
import subprocess
from typing import Dict, List, Optional

PARSER = argparse.ArgumentParser(
    description="Run print-sys-info to detect CPU features. Fail if the results seem wrong.")
PARSER.add_argument("--print-sys-info-path",
                    help="Path to print-sys-info app")
PARSER.add_argument("--build-dir",
                    help="Search this dir for print-sys-info app")


FEATURE_ALIASES = {
    'avx512': ['avx512f'],
    'clmul': ['pclmulqdq'],
    'crc': ['crc32'],
    'crypto': ['aes'],
}


def main():
    args = PARSER.parse_args()

    if args.print_sys_info_path:
        app = Path(args.print_sys_info_path)
    else:
        app = find_app(args.build_dir)

    # run print-sys-info. get feature names and whether it thinks they're supported
    app_features_presence: Dict[str, bool] = detect_features_from_app(app)

    # get feature info from OS (i.e. read /proc/cpuinfo on linux), get back list of supported features
    os_features_list = detect_features_from_os()

    # For each feature that print-sys-info says was (or wasn't) there,
    # check the os_features_list and make sure it is (or isn't_ present.
    for (feature, app_presence) in app_features_presence.items():
        os_presence = feature in os_features_list
        if not os_presence:
            # sometimes a feature has a mildly different name across platforms
            for alias in FEATURE_ALIASES.get(feature, []):
                if alias in os_features_list:
                    os_presence = True
                    break

        if app_presence != os_presence:
            exit(f"FAILED: aws-c-common and OS disagree on whether CPU supports feature '{feature}'\n" +
                 f"\taws-c-common:{app_presence} OS:{os_presence}")

    print("SUCCESS: aws-c-common and OS agree on CPU features")


def find_app(build_dir: Optional[str]) -> Path:
    if build_dir is None:
        build_dir = find_build_dir()
    else:
        build_dir = Path(build_dir).absolute()

    app_name = 'print-sys-info'
    if os.name == 'nt':
        app_name = app_name + '.exe'

    for file in build_dir.glob(f"**/{app_name}"):
        return file

    exit(f"FAILED: Can't find '{app_name}' under: {build_dir}"
         "\nPass --build-dir to hint location.")


def find_build_dir() -> Path:
    dir = Path(__file__).parent.absolute()
    while dir is not None:
        for build_dir in dir.glob('build'):
            return build_dir
        dir = dir.parent

    exit("FAILED: Can't find build dir. Pass --build-dir to hint location.")


def detect_features_from_app(app_path: Path) -> Dict[str, bool]:
    result = subprocess.run([str(app_path)],
                            universal_newlines=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    print(f"--- {app_path} ---")
    print(result.stderr)
    print(result.stdout)
    if result.returncode != 0:
        exit(f"FAILED: {app_path.name} exited with {result.returncode}")

    lines = result.stdout.splitlines()

    machine = platform.machine().lower()
    if machine in ['x86_64', 'amd64']:
        machine = 'amd'
    elif machine.startswith('arm') or machine == 'aarch64':
        machine = 'arm'
    else:
        print(f"SKIP TEST: unknown platform.machine(): {machine}")
        exit(0)

    # looking for lines like:
    #        'arm_crypto': true,
    #        'amd_sse4_1': false
    features = {}
    for line in lines:
        m = re.search(f"'{machine}_(.+)': (false|true)", line)
        if m:
            name = m.group(1)
            is_present = m.group(2) == 'true'
            features[name] = is_present

    # if aws-c-common compiled with -DUSE_CPU_EXTENSIONS=OFF, skip this this test
    for line in lines:
        m = re.search(f"'use cpu extensions': false", line)
        if m:
            print("SKIP TEST: aws-c-common compiled with -DUSE_CPU_EXTENSIONS=OFF")
            exit(0)

    if not features:
        raise RuntimeError("Cannot find features text in stdout ???")

    return features


def detect_features_from_os() -> List[str]:
    features = []

    cpuinfo_path = '/proc/cpuinfo'
    try:
        with open(cpuinfo_path) as f:
            cpuinfo_text = f.read()
    except:
        print(f"SKIP TEST: currently, this test only works on machines with /proc/cpuinfo")
        exit(0)

    # looking for line like:
    # flags           : fpu vme de pse ...
    # OR
    # features        : fp asimd evtstrm ...
    print(f"--- {cpuinfo_path} ---")
    for line in cpuinfo_text.splitlines():
        line = line.lower()
        print(line)
        m = re.match(r"(flags|features)\s+:(.*)", line)
        if m:
            features = m.group(2).split()
            return features

    exit(f"FAILED: Cannot detect CPU features in {cpuinfo_path}")


if __name__ == '__main__':
    main()
