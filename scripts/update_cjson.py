#!/usr/bin/env python3
import os
import shutil
import tempfile
import subprocess
import re


def run_command(cmd, cwd=None):
    """Run a command and return its output."""
    print(f"Running: {cmd}")
    result = subprocess.run(cmd, shell=True, check=True, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    return result.stdout.strip()


def main():
    # Create a temporary directory
    temp_dir = tempfile.mkdtemp()
    print(f"Created temporary directory: {temp_dir}")

    try:
        # 1. Clone the cJSON repository
        run_command(
            f"git clone https://github.com/DaveGamble/cJSON.git {temp_dir}")

        # 2. Get the latest release tag
        tags = run_command("git tag -l", cwd=temp_dir).split('\n')
        # Filter for version tags (e.g., v1.7.15)
        version_tags = [tag for tag in tags if re.match(
            r'^v\d+\.\d+\.\d+$', tag)]
        # Sort by version number
        version_tags.sort(key=lambda v: [int(x) for x in v[1:].split('.')])
        latest_tag = version_tags[-1]
        latest_version = latest_tag[1:]  # Remove 'v' prefix

        print(f"Latest cJSON version: {latest_version}")

        # Checkout the latest tag
        run_command(f"git checkout {latest_tag}", cwd=temp_dir)

        # 3. Copy cJSON.h and cJSON.c to ./source/external/
        base_dir = os.path.join(os.path.dirname(
            __file__), "..")
        source_dir = os.path.join(base_dir, "source", "external")
        shutil.copy(os.path.join(temp_dir, "cJSON.h"),
                    os.path.join(source_dir, "cJSON.h"))
        shutil.copy(os.path.join(temp_dir, "cJSON.c"),
                    os.path.join(source_dir, "cJSON.c"))

        print(f"Copied cJSON.h and cJSON.c to {source_dir}")

        # 4. Apply the changes from commit f005fdc06c34fdd663031661eff5c5575843e998
        run_command(
            f"git add *", cwd=base_dir)
        run_command(
            f"git commit -m \"update cjson to {latest_version}\"", cwd=base_dir)
        run_command(
            f"git cherry-pick f005fdc06c34fdd663031661eff5c5575843e998", cwd=base_dir)

        # 5. Update the version number in THIRD-PARTY-LICENSES.txt
        license_path = os.path.join(base_dir, "THIRD-PARTY-LICENSES.txt")
        with open(license_path, 'r') as f:
            content = f.read()

        # Update the version number - using a simpler approach to avoid regex issues
        pattern = r'\*\* cJSON; version \d+\.\d+\.\d+ -- https://github\.com/DaveGamble/cJSON'
        replacement = f'** cJSON; version {latest_version} -- https://github.com/DaveGamble/cJSON'
        content = content.replace(pattern.replace('\\', ''), replacement)

        with open(license_path, 'w') as f:
            f.write(content)

        print(
            f"Updated cJSON to version {latest_version} and applied Amazon modifications")

    finally:
        # Clean up the temporary directory
        shutil.rmtree(temp_dir)
        print(f"Removed temporary directory: {temp_dir}")


if __name__ == "__main__":
    main()
