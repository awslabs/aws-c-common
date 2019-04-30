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

# Class to refer to a specific build permutation
class BuildSpec():
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

KEYS = {
    # Build
    'pre_build_steps': list,
    'post_build_steps': list,
    'build_env': dict,
    'build_args': list,

    # Linux
    'apt_keys': list,
    'apt_repos': list,
    'apt_packages': list,

    # CodeBuild
    'image': str,
    'image_type': str,
    'compute_type': str,
    'requires_privilege': bool,
}

HOSTS = {
    'linux': {
        'apt_repos': [
            "ppa:ubuntu-toolchain-r/test",
        ],
        'apt_packages': ["cmake3"],

        'image': "aws/codebuild/ubuntu-base:14.04",
        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'al2012': {
        'build_args': [
            "-DENABLE_SANITIZERS=OFF",
            "-DPERFORM_HEADER_CHECK=OFF",
        ],

        'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/amzn-linux:latest",
        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'ancientlinux': {
        'architectures': {
            'x86': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/ancientlinux-x86:latest",
            },
            'x64': {
                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/ancientlinux-x64:latest",
            },
        },

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'windows': {
        'image_type': "WINDOWS_CONTAINER",
        'compute_type': "BUILD_GENERAL1_MEDIUM",
    },
}

TARGETS = {
    'linux': {
        'architectures': {
            'x86': {
                'build_args': [
                    "-DCMAKE_C_FLAGS=\"-m32\"",
                    "-DCMAKE_LINK_FLAGS=\"-m32\"",
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
    'windows': { },
}

COMPILERS = {
    'default': {
        'hosts': ['al2012', 'ancientlinux'],
        'targets': ['linux'],

        'versions': {
            'default': { }
        }
    },
    'clang': {
        'hosts': ['linux'],
        'targets': ['linux'],

        'post_build_steps': [
            "./format-check.sh",
            "{clang_tidy} -p build **/*.c"
        ],
        'build_args': ['-DCMAKE_EXPORT_COMPILE_COMMANDS=ON'],

        'apt_keys': ["https://apt.llvm.org/llvm-snapshot.gpg.key"],

        'versions': {
            '3': {
                '!post_build_steps': [],
                '!apt_repos': [],
                '!build_args': [],

                'apt_packages': ["clang-3.9"],
                'build_env': {
                    'CC': "clang-3.9",
                },
            },
            '6': {
                'apt_repos': [
                    "deb http://apt.llvm.org/trusty/ llvm-toolchain-trusty-6.0 main",
                ],
                'apt_packages': ["clang-6.0", "clang-format-6.0", "clang-tidy-6.0"],

                'build_env': {
                    'CC': "clang-6.0",
                },

                'variables': {
                    'clang_tidy': 'clang-tidy-6.0',
                },

                'requires_privilege': True,
            },
            '8': {
                'apt_repos': [
                    "deb http://apt.llvm.org/trusty/ llvm-toolchain-trusty-8 main",
                ],
                'apt_packages': ["clang-8", "clang-format-8", "clang-tidy-8"],

                'build_env': {
                    'CC': "clang-8",
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
        },
        'apt_packages': ["gcc-{version}"],

        'versions': {
            '4': {
                '!apt_packages': ["gcc"],
                '!build_env': { 'CC': "gcc" },
                '!apt_repos': [],

                'architectures': {
                    'x86': {
                        'apt_packages': ["gcc-multilib"],
                    },
                },
            },
            '5': {},
            '6': {},
            '7': {},
        },

        'architectures': {
            'x86': {
                'apt_packages': ["gcc-{version}-multilib"],
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

                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/codebulid-windows-vs-2015:latest",
            },
            '2017': {
                'variables': {
                    'generator_version': "15 2017",
                },

                'image': "123124136734.dkr.ecr.us-east-1.amazonaws.com/codebulid-windows-vs-2017:latest",
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
        return { key: _replace_variables(value, variables) for (key, value) in value.items() }

    else:
        # Unsupported, just return it
        return value

# Traverse the configurations to produce one for the specified
def produce_config(build_spec):

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
    for key, key_type in KEYS.items():
        new_version[key] = key_type()

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

def _quote_escape(args):
    if type(args) == str:
        return '"{}"'.format(args.replace('"', '\\"'))
    elif type(args) == list:
        return [_quote_escape(arg) for arg in args]

def run_build_linux(config):

    commands = []

    # INSTALL

    # Install keys
    for key in config['apt_keys']:
        commands.append("wget -O - {} | sudo apt-key add -".format(key))

    # Add APT repositories
    for repo in config['apt_repos']:
        commands.append("sudo apt-add-repository \"{}\"".format(repo))

    # Install packages
    if config['apt_packages']:
        commands.append("sudo apt-get update -y")
        commands.append("sudo apt-get install -y -f " + ' '.join(config['apt_packages']))

    # PRE BUILD

    # Set build environment
    for var, value in config['build_env'].items():
        commands.append("export {}={}".format(var, value))

    # Run configured pre-build steps
    commands += config['pre_build_steps']

    # BUILD

    # Run the repo's build script
    commands.append("./codebuild/common-poxix.sh " + ' '.join(_quote_escape(config['build_args'])))

    # POST BUILD

    # Run configured post-build steps
    commands += config['post_build_steps']

    return commands

def run_build_android(config):

    commands = []

    # INSTALL

    # Install keys
    for key in config['apt_keys']:
        commands.append("wget -O - {} | sudo apt-key add -".format(key))

    # Add APT repositories
    for repo in config['apt_repos']:
        commands.append("sudo apt-add-repository \"{}\"".format(repo))

    # Install packages
    if config['apt_packages']:
        commands.append("sudo apt-get update -y")
        commands.append("sudo apt-get install -y -f " + ' '.join(config['apt_packages']))

    # PRE BUILD

    # Set build environment
    for var, value in config['build_env'].items():
        commands.append("export {}={}".format(var, value))

    # Run configured pre-build steps
    commands += config['pre_build_steps']

    # BUILD

    # Run the repo's build script
    commands.append("./codebuild/common-android.sh " + ' '.join(_quote_escape(config['build_args'])))

    # POST BUILD

    # Run configured post-build steps
    commands += config['post_build_steps']

    return commands

def run_build_windows(config):

    commands = []

    # PRE BUILD

    # Set build environment
    for var, value in config['build_env'].items():
        commands.append("set {}=\"{}\"".format(var, value))

    # Run configured pre-build steps
    commands += config['pre_build_steps']

    # BUILD

    # Run the repo's build script
    commands.append("./codebuild/common-windows.sh " + ' '.join(_quote_escape(config['build_args'])))

    # POST BUILD

    # Run configured post-build steps
    commands += config['post_build_steps']

    return commands

run_build = {
    'linux': run_build_linux,
    'android': run_build_android,
    'windows': run_build_windows,
}

########################################################################################################################
# CODEBUILD
########################################################################################################################

CODEBUILD_BUILDS = [
    'linux-clang-3-linux-x64',
    'linux-clang-6-linux-x64',
    'linux-clang-8-linux-x64',

    'linux-gcc-4-linux-x86',
    'linux-gcc-4-linux-x64',
    'linux-gcc-5-linux-x64',
    'linux-gcc-6-linux-x64',
    'linux-gcc-7-linux-x64',

    'linux-ndk-19-android-arm64v8a',

    'al2012-default-default-linux-x64',

    'ancientlinux-default-default-linux-x86',
    'ancientlinux-default-default-linux-x64',

    'windows-msvc-2015-windows-x86',
    'windows-msvc-2015-windows-x64',
    'windows-msvc-2017-windows-x64',
]

def create_codebuild_project(config, project, github_account):

    variables = {
        'project': project,
        'account': github_account,
        'spec': config['spec'].name(),
    }

    # This matches the CodeBuild API for expected format
    CREATE_PARAM_TEMPLATE = {
        'name': '{project}-{spec}',
        'source': {
            'type': 'GITHUB',
            'location': 'https://github.com/{account}/{project}.git',
            'gitCloneDepth': 1,
            'buildspec': 'codebuild/common.yml',
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
                }
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
    build.add_argument('build', type=str)

    codebuild = commands.add_parser('codebuild', help="Create codebuild jobs")
    codebuild.add_argument('project', type=str, help='The name of the repo to create the projects for')
    codebuild.add_argument('--github-account', type=str, dest='github_account', default='awslabs', help='The GitHub account that owns the repo')
    codebuild.add_argument('--profile', type=str, default='default', help='The profile in ~/.aws/credentials to use when creating the jobs')

    args = parser.parse_args()

    if args.command == 'build':
        build_spec = BuildSpec(spec=args.build)
        config = produce_config(build_spec)

        print("Running build {}".format(config['spec'].name()))

        commands = run_build[build_spec.target](config)
        if args.dry_run:
            print('\n'.join(commands))
        else:
            import subprocess
            for command in commands:
                subprocess.check_call(command)

    if args.command == 'codebuild':

        # Setup AWS connection
        import boto3
        session = boto3.Session(profile_name=args.profile, region_name='us-east-1')
        codebuild = session.client('codebuild')

        # Get project status
        all_project_names = ['{}-{}'.format(args.project, build) for build in CODEBUILD_BUILDS]
        existing_projects = codebuild.batch_get_projects(names=all_project_names)
        new_projects = existing_projects['projectsNotFound']
        existing_projects = [project['name'] for project in existing_projects['projects']]

        for build in CODEBUILD_BUILDS:

            build_spec = BuildSpec(spec=build)
            config = produce_config(build_spec)
            cb_project = create_codebuild_project(config, args.project, args.github_account)

            cb_name = '{}-{}'.format(args.project, build)

            if cb_name in new_projects:
                print('Creating: {} ({})'.format(cb_name, build))
                if not args.dry_run:
                    codebuild.create_project(**cb_project)
                    codebuild.create_webhook(projectName=cb_name)

            elif cb_name in existing_projects:
                print('Updating: {} ({})'.format(cb_name, build))
                if not args.dry_run:
                    codebuild.update_project(**cb_project)

            else:
                assert False, "Build name not found in new or existing projects"
