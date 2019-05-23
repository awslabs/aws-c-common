# Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.

from __future__ import print_function
import os, sys, glob

# Class to refer to a specific build permutation
class BuildSpec(object):
    __slots__ = ('host', 'target', 'arch', 'compiler', 'compiler_version')

    def __init__(self, **kwargs):
        if 'spec' in kwargs:
            # Parse the spec from a single string
            self.host, self.compiler, self.compiler_version, self.target, self.arch = kwargs['spec'].split('-')

        # Pull out individual fields. Note this is not in an else to support overriding at construction time
        for slot in BuildSpec.__slots__:
            if slot in kwargs:
                setattr(self, slot, kwargs[slot])

    def name(self):
        return '-'.join([self.host, self.compiler, self.compiler_version, self.target, self.arch])

    def __str__(self):
        return self.name()

    def __repr__(self):
        return self.name()

########################################################################################################################
# DATA DEFINITIONS
########################################################################################################################

# CMake config to build with
BUILD_CONFIG = "RelWithDebInfo"

KEYS = {
    # Build
    'python': "",
    'pre_build_steps': [],
    'post_build_steps': [],
    'build_env': {},
    'build_args': [],
    'run_tests': True,

    # Linux
    'apt_keys': [],
    'apt_repos': [],
    'apt_packages': [],

    # CodeBuild
    'image': "",
    'image_type': "",
    'compute_type': "",
    'requires_privilege': False,
}

HOSTS = {
    'linux': {
        'architectures': {
            'x86': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/ubuntu-16.04:x86",
            },
            'x64': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/ubuntu-16.04:x64",
            },
        },

        'python': "python3",

        'build_args': [
            "-DPERFORM_HEADER_CHECK=ON",
        ],

        'apt_repos': [
            "ppa:ubuntu-toolchain-r/test",
        ],

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'al2012': {
        'build_args': [
            "-DENABLE_SANITIZERS=OFF",
            "-DPERFORM_HEADER_CHECK=OFF",
        ],

        'python': "python3",

        'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/al2012:x64",
        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'manylinux': {
        'architectures': {
            'x86': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/manylinux1:x86",
            },
            'x64': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/manylinux1:x64",
            },
        },

        'python': "/opt/python/cp37-cp37m/bin/python",

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'windows': {
        'python': "python.exe",

        'build_args': [
            "-DPERFORM_HEADER_CHECK=ON",
        ],

        'image_type': "WINDOWS_CONTAINER",
        'compute_type': "BUILD_GENERAL1_MEDIUM",
    },
    'macos': {
        'python': "python3",


    }
}

TARGETS = {
    'linux': {
        'architectures': {
            'x86': {
                'build_args': [
                    '-DCMAKE_C_FLAGS="-m32"',
                    '-DCMAKE_CXX_FLAGS="-m32"',
                ],
            },
        },

        'build_args': [
            "-DENABLE_SANITIZERS=ON",
        ],
    },
    'macos': {
        'architectures': {
            'x86': {
                'build_args': [
                    '-DCMAKE_C_FLAGS="-m32"',
                    '-DCMAKE_CXX_FLAGS="-m32"',
                ],
            },
        },
    },
    'android': {
        'build_args': [
            "-DTARGET_ARCH=ANDROID",
            "-DCMAKE_TOOLCHAIN_FILE=/opt/android-ndk/build/cmake/android.toolchain.cmake",
            "-DANDROID_NDK=/opt/android-ndk",
        ],
        'run_tests': False,

        'architectures': {
            'arm64v8a': {
                'build_args': [
                    "-DANDROID_ABI=arm64-v8a",
                ],
            },
        },

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'windows': {
    },
}

COMPILERS = {
    'default': {
        'hosts': ['al2012', 'manylinux'],
        'targets': ['linux'],

        'versions': {
            'default': { }
        }
    },
    'clang': {
        'hosts': ['linux', 'macos'],
        'targets': ['linux', 'macos'],

        'post_build_steps': [
            ["./format-check.sh"],
            ["{clang_tidy}", "-p", "{build_dir}", "{sources}"],
        ],
        'build_args': ['-DCMAKE_EXPORT_COMPILE_COMMANDS=ON'],

        'apt_keys': ["http://apt.llvm.org/llvm-snapshot.gpg.key"],

        'versions': {
            'default': {
                '!post_build_steps': [],
                '!apt_keys': [],
                '!apt_repos': [],
                '!apt_packages': [],

                'build_env': {
                    'CC': "clang",
                    'CXX': "clang",
                },
            },
            '3': {
                '!post_build_steps': [],
                '!apt_repos': [],
                '!build_args': [],

                'apt_packages': ["clang-3.9"],
                'build_env': {
                    'CC': "clang-3.9",
                    'CXX': "clang-3.9",
                },
            },
            '6': {
                'apt_repos': [
                    "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-6.0 main",
                ],
                'apt_packages': ["clang-6.0", "clang-format-6.0", "clang-tidy-6.0"],

                'build_env': {
                    'CC': "clang-6.0",
                    'CXX': "clang-6.0",
                    'CLANG_FORMAT': 'clang-format-6.0',
                },

                'variables': {
                    'clang_tidy': 'clang-tidy-6.0',
                },

                'requires_privilege': True,
            },
            '8': {
                'apt_repos': [
                    "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-8 main",
                ],
                'apt_packages': ["clang-8", "clang-format-8", "clang-tidy-8"],

                'build_env': {
                    'CC': "clang-8",
                    'CXX': "clang-8",
                    'CLANG_FORMAT': 'clang-format-8',
                },

                'variables': {
                    'clang_tidy': 'clang-tidy-8',
                },

                'requires_privilege': True,
            },
        },
    },
    'gcc': {
        'hosts': ['linux'],
        'targets': ['linux'],

        'build_env': {
            'CC': "gcc-{version}",
            'CXX': "g++-{version}",
        },
        'apt_packages': ["gcc-{version}", "g++-{version}"],

        'versions': {
            '4': {
                '!apt_packages': ["gcc", "g++"],
                '!build_env': {
                    'CC': "gcc",
                    'CXX': 'g++',
                },
                '!apt_repos': [],

                'architectures': {
                    'x86': {
                        'apt_packages': ["gcc-multilib", "g++-multilib"],
                    },
                },
            },
            '5': {},
            '6': {},
            '7': {},
        },

        'architectures': {
            'x86': {
                'apt_packages': ["gcc-{version}-multilib", "g++-{version}-multilib"],
            },
        },
    },
    'msvc': {
        'hosts': ['windows'],
        'targets': ['windows'],

        'build_args': ["-G", "Visual Studio {generator_version}{generator_postfix}"],

        'versions': {
            '2015': {
                'variables': {
                    'generator_version': "14 2015",
                },

                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/win-vs2015:x64",
            },
            '2017': {
                'variables': {
                    'generator_version': "15 2017",
                },

                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/win-vs2017:x64",
            },
        },

        'architectures': {
            'x64': {
                'variables': {
                    'generator_postfix': " Win64",
                },
            },
        },
    },
    'ndk': {
        'hosts': ['linux'],
        'targets': ['android'],

        'versions': {
            '19': {
                'build_args': [
                    "-DANDROID_NATIVE_API_LEVEL=19",
                ],

                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/android/ndk-r19c:latest",
            }
        }
    }
}

########################################################################################################################
# PRODUCE CONFIG
########################################################################################################################

# Ensure the combination of options specified are valid together
def validate_build(build_spec):

    assert build_spec.host in HOSTS, "Host name {} is invalid".format(build_spec.host)
    assert build_spec.target in TARGETS, "Target {} is invalid".format(build_spec.target)

    assert build_spec.compiler in COMPILERS, "Compiler {} is invalid".format(build_spec.compiler)
    compiler = COMPILERS[build_spec.compiler]

    assert build_spec.compiler_version in compiler['versions'], "Compiler version {} is invalid for compiler {}".format(build_spec.compiler_version, build_spec.compiler)

    supported_hosts = compiler['hosts']
    assert build_spec.host in supported_hosts, "Compiler {} does not support host {}".format(build_spec.compiler, build_spec.host)

    supported_targets = compiler['targets']
    assert build_spec.target in supported_targets, "Compiler {} does not support target {}".format(build_spec.compiler, build_spec.target)

# Moved outside merge_dicts to avoid variable shadowing
def _apply_value(obj, key, new_value):

    key_type = type(new_value)
    if key_type == list:
        # Apply the config's value before the existing list
        obj[key] = new_value + obj[key]

    elif key_type == dict:
        # Iterate each element and recursively apply the values
        for k, v in new_value.items():
            _apply_value(obj[key], k, v)

    else:
        # Unsupported type, just use it
        obj[key] = new_value

# Replace all variable strings with their values
def _replace_variables(value, variables):

    key_type = type(value)
    if key_type == str:

        # If the whole string is a variable, just replace it
        if value and value[0] == '{' and value[-1] == '}':
            return variables.get(value[1:-1], '')

        # Custom formatter for optional variables
        from string import Formatter
        class VariableFormatter(Formatter):
            def get_value(self, key, args, kwds):
                if isinstance(key, str):
                    return kwds.get(key, '')
                else:
                    return super().get_value(key, args, kwds)
        formatter = VariableFormatter()

        # Strings just do a format
        return formatter.format(value, **variables)

    elif key_type == list:
        # Update each element
        return [_replace_variables(e, variables) for e in value]

    elif key_type == dict:
        # Iterate each element and recursively apply the variables
        return dict([(key, _replace_variables(value, variables)) for (key, value) in value.items()])

    else:
        # Unsupported, just return it
        return value

# Traverse the configurations to produce one for the specified
def produce_config(build_spec, **additional_variables):

    validate_build(build_spec)

    # Build the list of config options to poll
    configs = []

    def process_config(map, key):
        config = map[key]
        configs.append(config)

        config_arches = config.get('architectures')
        if config_arches:
            config_arch = config_arches.get(build_spec.arch)
            if config_arch:
                configs.append(config_arch)

        return config


    # Host isn't allowed to specify architectures
    process_config(HOSTS, build_spec.host)
    process_config(TARGETS, build_spec.target)

    compiler = process_config(COMPILERS, build_spec.compiler)
    process_config(compiler['versions'], build_spec.compiler_version)

    new_version = {
        'spec': build_spec,
    }
    # Iterate all keys and apply them
    for key, default in KEYS.items():
        new_version[key] = default

        for config in configs:
            override_key = '!' + key
            if override_key in config:
                # Handle overrides
                new_version[key] = config[override_key]

            elif key in config:
                # By default, merge all values (except strings)
                _apply_value(new_version, key, config[key])

    # Default variables
    replacements = {
        'host': build_spec.host,
        'compiler': build_spec.compiler,
        'version': build_spec.compiler_version,
        'target': build_spec.target,
        'arch': build_spec.arch,
        **additional_variables,
    }

    # Pull variables from the configs
    for config in configs:
        if 'variables' in config:
            variables = config['variables']
            assert type(variables) == dict

            # Copy into the variables list
            for k, v in variables.items():
                replacements[k] = v

    # Post process
    new_version = _replace_variables(new_version, replacements)

    return new_version

########################################################################################################################
# RUN BUILD
########################################################################################################################

def run_build(build_spec, is_dryrun):

    if not is_dryrun:
        import tempfile, shutil, subprocess

    #TODO These platforms don't succeed when doing a RelWithDebInfo build
    if build_spec.host in ("al2012", "manylinux"):
        global BUILD_CONFIG
        BUILD_CONFIG = "Debug"

    source_dir = os.environ.get("CODEBUILD_SRC_DIR", os.getcwd())
    sources = [os.path.join(source_dir, file) for file in glob.glob('**/*.c')]

    def _run_command(command):
        # Process out lists
        new_command = []
        for e in command:
            e_type = type(e)
            if e_type == str:
                new_command.append(e)
            elif e_type == list:
                new_command.extend(e)

        if is_dryrun:
            print(' '.join(new_command))
        else:
            print('>', ' '.join(new_command), flush=True)
            subprocess.check_call(new_command, stdout=sys.stdout, stderr=sys.stderr)

    # Make the build directory
    if is_dryrun:
        build_dir = "$TEMP/build"
        _run_command(["mkdir", build_dir])
    else:
        build_dir = tempfile.mkdtemp()

    # Build the config object
    config = produce_config(build_spec, sources=sources, source_dir=source_dir, build_dir=build_dir)

    # INSTALL

    # Install keys
    for key in config['apt_keys']:
        _run_command(["sudo", "apt-key", "adv", "--fetch-keys", key])

    # Add APT repositories
    for repo in config['apt_repos']:
        _run_command(["sudo", "apt-add-repository", repo])

    # Install packages
    if config['apt_packages']:
        _run_command(["sudo", "apt-get", "update", "-y"])
        _run_command(["sudo", "apt-get", "install", "-y", "-f", config['apt_packages']])

    # PRE BUILD

    # Set build environment
    for var, value in config['build_env'].items():
        os.environ[var] = value

    # Run configured pre-build steps
    for step in config['pre_build_steps']:
        _run_command(step)

    # BUILD

    # CD to the build directory
    if is_dryrun:
        _run_command(["cd", build_dir])
    else:
        os.chdir(build_dir)

    # Run CMake
    _run_command(["cmake", config['build_args'], "-DCMAKE_BUILD_TYPE=" + BUILD_CONFIG, source_dir])

    # Run the build
    _run_command(["cmake", "--build", ".", "--config", BUILD_CONFIG])

    # Run tests if necessary
    if config['run_tests']:
        _run_command(["ctest", ".", "--output-on-failure"])

    # POST BUILD

    # Go back to the source dir
    if is_dryrun:
        _run_command(["cd", source_dir])
    else:
        os.chdir(source_dir)

    # Run configured post-build steps
    for step in config['post_build_steps']:
        _run_command(step)

    # Delete temp dir
    if not is_dryrun:
        shutil.rmtree(build_dir)

    return commands

########################################################################################################################
# CODEBUILD
########################################################################################################################

CODEBUILD_OVERRIDES = {
    'linux-clang3-x64': 'linux-clang-3-linux-x64',
    'linux-clang6-x64': 'linux-clang-6-linux-x64',
    'linux-clang8-x64': 'linux-clang-8-linux-x64',

    'linux-gcc-4x-x86': 'linux-gcc-4-linux-x86',
    'linux-gcc-4x-x64': 'linux-gcc-4-linux-x64',
    'linux-gcc-5x-x64': 'linux-gcc-5-linux-x64',
    'linux-gcc-6x-x64': 'linux-gcc-6-linux-x64',
    'linux-gcc-7x-x64': 'linux-gcc-7-linux-x64',

    'android-arm64-v8a': 'linux-ndk-19-android-arm64v8a',

    "AL2012-gcc44": 'al2012-default-default-linux-x64',

    "ancient-linux-x86": 'manylinux-default-default-linux-x86',
    "ancient-linux-x64": 'manylinux-default-default-linux-x64',

    'windows-msvc-2015-x86': 'windows-msvc-2015-windows-x86',
    'windows-msvc-2015': 'windows-msvc-2015-windows-x64',
    'windows-msvc-2017': 'windows-msvc-2017-windows-x64',
}

def create_codebuild_project(config, project, github_account):

    variables = {
        'project': project,
        'account': github_account,
        'spec': config['spec'].name(),
        'python': config['python'],
    }

    # This matches the CodeBuild API for expected format
    CREATE_PARAM_TEMPLATE = {
        'name': '{project}-{spec}',
        'source': {
            'type': 'GITHUB',
            'location': 'https://github.com/{account}/{project}.git',
            'gitCloneDepth': 1,
            'buildspec':
                'version: 0.2\n' +
                'phases:\n' +
                '  build:\n' +
                '    commands:\n' +
                '      - "{python} --version"\n' +
                '      - "{python} ./codebuild/builder.py build"',
            'auth': {
                'type': 'OAUTH',
            },
            'reportBuildStatus': True,
        },
        'artifacts': {
            'type': 'NO_ARTIFACTS',
        },
        'environment': {
            'type': config['image_type'],
            'image': config['image'],
            'computeType': config['compute_type'],
            'environmentVariables': [
                {
                    'name': "BUILD_SPEC",
                    'value': "{spec}",
                },
            ],
            'privilegedMode': config['requires_privilege'],
        },
        'serviceRole': 'arn:aws:iam::123124136734:role/CodeBuildServiceRole',
        'badgeEnabled': False,
    }

    return _replace_variables(CREATE_PARAM_TEMPLATE, variables)

########################################################################################################################
# MAIN
########################################################################################################################

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('-d', '--dry-run', action='store_true', help="Don't run the build, just print the commands that would run")
    commands = parser.add_subparsers(dest='command')

    build = commands.add_parser('build', help="Run the requested build")
    build.add_argument('build', type=str, nargs='?', default=None)

    codebuild = commands.add_parser('codebuild', help="Create codebuild jobs")
    codebuild.add_argument('project', type=str, help='The name of the repo to create the projects for')
    codebuild.add_argument('--github-account', type=str, dest='github_account', default='awslabs', help='The GitHub account that owns the repo')
    codebuild.add_argument('--profile', type=str, default='default', help='The profile in ~/.aws/credentials to use when creating the jobs')

    args = parser.parse_args()

    if args.command == 'build':
        # If build name not passed
        build_name = args.build
        if not build_name:
            build_name = os.environ.get('BUILD_SPEC', None)
            assert build_name, "Build must be specified via command line or BUILD_SPEC env variable"

        build_spec = BuildSpec(spec=build_name)

        print("Running build", build_spec.name(), flush=True)
        print("Current directory:", os.getcwd(), flush=True)

        run_build(build_spec, args.dry_run)

    if args.command == 'codebuild':

        # Setup AWS connection
        import boto3
        session = boto3.Session(profile_name=args.profile, region_name='us-east-1')
        codebuild = session.client('codebuild')

        # Get project status

        existing_projects = []
        new_projects = []

        project_prefix_len = len(args.project) + 1

        old_project_names = ['{}-{}'.format(args.project, build) for build in CODEBUILD_OVERRIDES.keys()]
        old_projects_response = codebuild.batch_get_projects(names=old_project_names)
        existing_projects += [project['name'][project_prefix_len:] for project in old_projects_response['projects']]

        old_missing_projects = [name[project_prefix_len:] for name in old_projects_response['projectsNotFound']]
        # If old project names are not found, search for the new names, and if those aren't present, add for creation
        if old_missing_projects:
            new_project_names = [CODEBUILD_OVERRIDES[old_name] for old_name in old_missing_projects]
            new_projects_response = codebuild.batch_get_projects(names=new_project_names)
            existing_projects += [project['name'] for project in new_projects_response['projects']]
            new_projects += new_projects_response['projectsNotFound']

        # Update all existing projects
        for cb_spec in existing_projects:
            # If the project being updated is in CB_OVERRIDES, use it, otherwise just spec
            new_spec = CODEBUILD_OVERRIDES.get(cb_spec, cb_spec)
            build_name = '{}-{}'.format(args.project, cb_spec)

            build_spec = BuildSpec(spec=new_spec)
            config = produce_config(build_spec)
            cb_project = create_codebuild_project(config, args.project, args.github_account)
            cb_project['name'] = build_name

            print('Updating: {} ({})'.format(new_spec, cb_spec))
            if not args.dry_run:
                codebuild.update_project(**cb_project)

        # Create any missing projects
        for spec in new_projects:
            build_spec = BuildSpec(spec=spec)
            config = produce_config(build_spec)
            cb_project = create_codebuild_project(config, args.project, args.github_account)

            print('Creating: {}'.format(spec))
            if not args.dry_run:
                codebuild.create_project(**cb_project)
                codebuild.create_webhook(projectName=cb_project['name'])
