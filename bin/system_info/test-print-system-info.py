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
PARSER.add_argument("print-sys-info-path",
                    help="Path to print-sys-info app")


def main():
    args = PARSER.parse_args()

    if args.print_sys_info:
        app = Path(args.print_sys_info_path)
        if not app.exists:
            exit("FAILED: file not found: {app}")
    else:
        app = find_app()

    app_features_yesno: Dict[str, bool] = detect_features_from_app(app)

    os_features_list = detect_features_from_os()


def find_app(build_dir: Optional[str]) -> Path:
    build_dir = find_build_dir()

    app_name = 'print-sys-info'
    if os.name == 'nt':
        app_name = app_name + '.exe'

    for file in build_dir.glob(f"**/{app_name}"):
        return file

    exit("FAILED: Can't find print-sys-info. Pass location as argument")


def find_build_dir() -> Path:
    dir = Path(__file__).parent
    while dir is not None:
        for build_dir in dir.glob('build'):
            return build_dir
        dir = dir.parent

    exit("FAILED: Can't find print-sys-info. Pass location as argument")


def detect_features_from_app(app_path: Path) -> Dict[str, bool]:
    result = run([str(app_path)],
                 capture_output=True,
                 text=True)
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
        if m := re.search(f"'{machine}_(.+)': (false|true)", line):
            name = m.group(1)
            is_present = m.group(2) == 'true'
            features[name] = is_present
    if not features:
        raise RuntimeError("Cannot find features text in stdout ???")

    return features


def detect_features_from_os() -> List[str]:
    features = []

    try:
        with open('/proc/cpuinfo') as f:
            cpuinfo_text = f.read()
    except:
        exit("SKIP TEST: currently, this test only works on machines with /proc/cpuinfo")

    # for line in cpuinfo_text:


if __name__ == '__main__':
    main()
