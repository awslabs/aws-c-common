import os
import tempfile
import shutil
import subprocess
import re

# Create a temporary directory for cloning the repository
temp_repo_dir = tempfile.mkdtemp()

try:
    # Clone the repository into the temporary directory
    repo_url = "https://github.com/PJK/libcbor.git"
    clone_command = f"git clone {repo_url} {temp_repo_dir}"
    subprocess.run(clone_command, shell=True, check=True)

    # Create a separate folder for the copied files
    output_dir = os.path.join(
        os.path.dirname(__file__), "..", "source", "external", "libcbor")
    os.makedirs(output_dir, exist_ok=True)

    # Copy files ending with .c and .h from the /src directory
    src_dir = os.path.join(temp_repo_dir, "src")

    # Use our customized configurations
    src_customize_cbor_dir = os.path.join(
        os.path.dirname(__file__), "libcbor_customize")
    shutil.copytree(src_customize_cbor_dir, os.path.join(
        output_dir, "cbor/"), dirs_exist_ok=True)

    for root, dirs, files in os.walk(src_dir):
        dir_name = os.path.basename(root)
        for file in files:
            if file.endswith((".c", ".h")):
                src_file = os.path.join(root, file)
                rel_path = os.path.relpath(src_file, src_dir)
                dest_file = os.path.join(output_dir, rel_path)
                os.makedirs(os.path.dirname(dest_file), exist_ok=True)
                if dir_name == "cbor":
                    with open(src_file, 'r') as f:
                        contents = f.read()
                    pattern = r'#include "cbor/'
                    new_contents = re.sub(pattern, '#include "', contents)
                    with open(dest_file, 'w') as f:
                        f.write(new_contents)
                elif dir_name == "internal":
                    with open(src_file, 'r') as f:
                        contents = f.read()
                    pattern = r'#include "cbor/'
                    new_contents = re.sub(pattern, '#include "../', contents)
                    with open(dest_file, 'w') as f:
                        f.write(new_contents)
                else:
                    shutil.copy(src_file, dest_file)


except subprocess.CalledProcessError as e:
    print(f"An error occurred while cloning the repository: {e}")

except Exception as e:
    print(f"An error occurred: {e}")

finally:
    # Remove the temporary directory
    shutil.rmtree(temp_repo_dir, ignore_errors=True)
