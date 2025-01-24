#!/usr/bin/env python3
import argparse
import os
from pathlib import Path
import platform
import re
from subprocess import run
from typing import Dict, List, Optional

PARSER = argparse.ArgumentParser(
    description="Run print-sys-info to detect CPU features. Fail if the results seem wrong.")
PARSER.add_argument("--print-sys-info-path",
                    help="Path to print-sys-info app")
PARSER.add_argument("--build-dir",
                    help="Search this dir for print-sys-info app")


def main():
    args = PARSER.parse_args()

    if args.print_sys_info_path:
        app = Path(args.print_sys_info_path)
    else:
        app = find_app(args.build_dir)

    app_features_yesno: Dict[str, bool] = detect_features_from_app(app)

    os_features_list = detect_features_from_os()

    # TODO: compare app_features_yesno and os_features_list


def find_app(build_dir: Optional[str]) -> Path:
    if build_dir is None:
        build_dir = find_build_dir()

    app_name = 'print-sys-info'
    if os.name == 'nt':
        app_name = app_name + '.exe'

    for file in build_dir.glob(f"**/{app_name}"):
        return file

    exit(f"FAILED: Can't find '{app_name}' under: {build_dir}."
         "\nPass --build-dir to hint location.")


def find_build_dir() -> Path:
    dir = Path(__file__).parent
    while dir is not None:
        for build_dir in dir.glob('build'):
            return build_dir
        dir = dir.parent

    exit("FAILED: Can't find build dir. Pass --build-dir to hint location.")


def detect_features_from_app(app_path: Path) -> Dict[str, bool]:
    result = run([str(app_path)],
                 capture_output=True,
                 text=True)
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

    # looking for line like: flags           : fpu vme de pse ...
    print(f"--- {cpuinfo_path} ---")
    for line in cpuinfo_text.splitlines():
        print(line)
        m = re.match(r"flags\s+:(.*)", line)
        if m:
            flags = m.group(1).split()
            return flags

    exit(f"FAILED: Cannot detect 'flags' in {cpuinfo_path}")


if __name__ == '__main__':
    main()
