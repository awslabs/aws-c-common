import os
import tempfile
import shutil
import subprocess
import re

# TODO support pass-in version and use the tag

major_version = 0
minor_version = 11
patch_version = 0

GENERATED_NOTES = """/**
 * DO NOT DIRECTLY MODIFY THIS FILE:
 *
 * The code in this file is generated from scripts/import_libcbor.py
 *  and any modifications should be in there.
 */
"""

CBOR_EXPORT_H = """
#ifndef CBOR_EXPORT_H
#define CBOR_EXPORT_H

/* Don't export anything from libcbor */
#define CBOR_EXPORT

#endif /* CBOR_EXPORT_H */
"""

CONFIGURATION_H = f"""
#ifndef LIBCBOR_CONFIGURATION_H
#define LIBCBOR_CONFIGURATION_H

#define CBOR_MAJOR_VERSION {major_version}
#define CBOR_MINOR_VERSION {minor_version}
#define CBOR_PATCH_VERSION {patch_version}

#define CBOR_BUFFER_GROWTH 2
#define CBOR_MAX_STACK_SIZE 2048
#define CBOR_PRETTY_PRINTER 1

#if defined(_MSC_VER)
#    define CBOR_RESTRICT_SPECIFIER
#else
#    define CBOR_RESTRICT_SPECIFIER restrict
#endif

#define CBOR_INLINE_SPECIFIER

/* Ignore the compiler warnings for libcbor. */
#ifdef _MSC_VER
#    pragma warning(disable : 4028)
#    pragma warning(disable : 4715)
#    pragma warning(disable : 4232)
#    pragma warning(disable : 4068)
#    pragma warning(disable : 4244)
#endif

#ifdef __clang__
#    pragma clang diagnostic push
#    pragma clang diagnostic ignored "-Wreturn-type"
#elif defined(__GNUC__)
#    pragma GCC diagnostic push
#    pragma GCC diagnostic ignored "-Wreturn-type"
#    pragma GCC diagnostic ignored "-Wunknown-pragmas"
#endif

#endif // LIBCBOR_CONFIGURATION_H
"""

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
    for root, dirs, files in os.walk(src_dir):
        dir_name = os.path.basename(root)
        for file in files:
            if file.endswith((".c", ".h")):
                # copy the source code to ../source/external/libcbor
                src_file = os.path.join(root, file)
                rel_path = os.path.relpath(src_file, src_dir)
                dest_file = os.path.join(output_dir, rel_path)
                os.makedirs(os.path.dirname(dest_file), exist_ok=True)
                shutil.copy(src_file, dest_file)

    # Use our customized configurations

    with open(os.path.join(output_dir, "cbor/cbor_export.h"), "w") as file:
        file.write(GENERATED_NOTES)
        file.write(CBOR_EXPORT_H)
    with open(os.path.join(output_dir, "cbor/configuration.h"), "w") as file:
        file.write(GENERATED_NOTES)
        file.write(CONFIGURATION_H)

except subprocess.CalledProcessError as e:
    print(f"An error occurred while cloning the repository: {e}")

except Exception as e:
    print(f"An error occurred: {e}")

finally:
    # Remove the temporary directory
    shutil.rmtree(temp_repo_dir, ignore_errors=True)
