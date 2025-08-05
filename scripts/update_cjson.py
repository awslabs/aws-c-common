#!/usr/bin/env python3
import os
import shutil
import tempfile
import subprocess
import re


def run_command(cmd, cwd=None, check=True):
    """Run a command and return its output."""
    print(f"Running: {cmd}")
    result = subprocess.run(cmd, shell=True, check=check, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    return result.stdout.strip(), result.returncode


def main():
    # Create a temporary directory
    temp_dir = tempfile.mkdtemp()
    print(f"Created temporary directory: {temp_dir}")

    try:
        # 1. Clone the cJSON repository
        _, _ = run_command(
            f"git clone https://github.com/DaveGamble/cJSON.git {temp_dir}")

        # 2. Get the latest release tag
        tags_output, _ = run_command("git tag -l", cwd=temp_dir)
        tags = tags_output.split('\n')
        # Filter for version tags (e.g., v1.7.15)
        version_tags = [tag for tag in tags if re.match(
            r'^v\d+\.\d+\.\d+$', tag)]
        # Sort by version number
        version_tags.sort(key=lambda v: [int(x) for x in v[1:].split('.')])
        latest_tag = version_tags[-1]
        latest_version = latest_tag[1:]  # Remove 'v' prefix

        print(f"Latest cJSON version: {latest_version}")

        # Checkout the latest tag
        _, _ = run_command(f"git checkout {latest_tag}", cwd=temp_dir)

        # 3. Copy cJSON.h and cJSON.c to ./source/external/
        base_dir = os.path.join(os.path.dirname(
            __file__), "..")
        source_dir = os.path.join(base_dir, "source", "external")
        shutil.copy(os.path.join(temp_dir, "cJSON.h"),
                    os.path.join(source_dir, "cJSON.h"))
        shutil.copy(os.path.join(temp_dir, "cJSON.c"),
                    os.path.join(source_dir, "cJSON.c"))

        print(f"Copied cJSON.h and cJSON.c to {source_dir}")

        # 4. Update the version number in THIRD-PARTY-LICENSES.txt
        license_path = os.path.join(base_dir, "THIRD-PARTY-LICENSES.txt")
        with open(license_path, 'r') as f:
            content = f.read()

        # Update the version number using regex for more accurate replacement
        pattern = r'\*\* cJSON; version \d+\.\d+\.\d+ --'
        replacement = f'** cJSON; version {latest_version} --'
        content = re.sub(pattern, replacement, content)

        with open(license_path, 'w') as f:
            f.write(content)

        print(f"Updated cJSON to version {latest_version}")

        # 5. Apply the changes from commit f005fdc06c34fdd663031661eff5c5575843e998
        # https://github.com/awslabs/aws-c-common/pull/1211/commits/f005fdc06c34fdd663031661eff5c5575843e998
        # it applies the amazon edit to cJSON.h and cJSON.c
        _, returncode = run_command(
            f"git add *", cwd=source_dir, check=False)
        if returncode == 0:
            _, returncode = run_command(
                f"git commit -m \"update cjson to {latest_version}\"", cwd=base_dir, check=False)
            if returncode == 0:
                _, returncode = run_command(
                    f"git cherry-pick f005fdc06c34fdd663031661eff5c5575843e998", cwd=base_dir, check=False)
                if returncode == 0:
                    print(
                        "Successfully applied Amazon modifications from commit f005fdc06c34fdd663031661eff5c5575843e998")
                else:
                    print(
                        "\nWARNING: Failed to apply changes from commit f005fdc06c34fdd663031661eff5c5575843e998")
                    print(
                        "You will need to manually apply these changes. Please run the following command:")
                    print(f"  git cherry-pick f005fdc06c34fdd663031661eff5c5575843e998")
                    print("If there are conflicts, resolve them and then run:")
                    print("  git cherry-pick --continue")
            else:
                print("\nWARNING: Failed to commit the updated cJSON files")
                print("You will need to manually commit and then apply the changes from commit f005fdc06c34fdd663031661eff5c5575843e998")
        else:
            print("\nWARNING: Failed to add the updated cJSON files to git")
            print("You will need to manually add, commit, and then apply the changes from commit f005fdc06c34fdd663031661eff5c5575843e998")

    finally:
        # Clean up the temporary directory
        shutil.rmtree(temp_dir)
        print(f"Removed temporary directory: {temp_dir}")


if __name__ == "__main__":
    main()
