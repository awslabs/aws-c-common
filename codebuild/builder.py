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
import os, sys, glob, shutil, subprocess, tempfile

# Class to refer to a specific build permutation
class BuildSpec(object):
    def __init__(self, **kwargs):
        if 'spec' in kwargs:
            # Parse the spec from a single string
            self.host, self.compiler, self.compiler_version, self.target, self.arch, *rest = kwargs['spec'].split('-')

            for variant in ('downstream',):
                if variant in rest:
                    setattr(self, variant, True)
                else:
                    setattr(self, variant, False)

        # Pull out individual fields. Note this is not in an else to support overriding at construction time
        for slot in ('host', 'target', 'arch', 'compiler', 'compiler_version'):
            if slot in kwargs:
                setattr(self, slot, kwargs[slot])

        self.name = '-'.join([self.host, self.compiler, self.compiler_version, self.target, self.arch])
        if self.downstream:
            self.name += "-downstream"

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


# borrow the technique from the virtualmod module
import importlib
from importlib.abc import Loader, MetaPathFinder
_virtual_modules = dict()
class VirtualModuleMetaclass(type):
    def __init__(cls, name, bases, attrs):
        # Initialize the class
        super(VirtualModuleMetaclass, cls).__init__(name, bases, attrs)

        # Do not register VirtualModule
        if name == 'VirtualModule':
            return

        module_name = getattr(cls, '__module_name__', cls.__name__) or name
        module = VirtualModule.create_module(module_name)

        # Copy over class attributes
        for key, value in attrs.items():
            if key in ('__name__', '__module_name__', '__module__', '__qualname__'):
                continue
            setattr(module, key, value)


class VirtualModule(metaclass=VirtualModuleMetaclass):
    class Finder(MetaPathFinder):
        def find_spec(fullname, path, target=None):
            if fullname in _virtual_modules:
                return _virtual_modules[fullname].__spec__
            return None

    class VirtualLoader(Loader):
        def create_module(spec):
            if spec.name not in _virtual_modules:
                return None

            return _virtual_modules[spec.name]

        def exec_module(module):
            module_name = module.__name__
            if hasattr(module, '__spec__'):
                module_name = module.__spec__.name

            sys.modules[module_name] = module

    @staticmethod
    def create_module(name):
        module_cls = type(sys)
        spec_cls = type(sys.__spec__)
        module = module_cls(name)
        setattr(module, '__spec__', spec_cls(
            name=name, loader=VirtualModule.VirtualLoader))
        _virtual_modules[name] = module
        return module

sys.meta_path.insert(0, VirtualModule.Finder)

########################################################################################################################
# DATA DEFINITIONS
########################################################################################################################

KEYS = {
    # Build
    'python': "",
    'c': None,
    'cxx': None,
    'pre_build_steps': [],
    'post_build_steps': [],
    'build_env': {},
    'cmake_args': [],
    'run_tests': True,

    # Linux
    'use_apt': False,
    'apt_keys': [],
    'apt_repos': [],
    'apt_packages': [],

    # macOS
    'use_brew': False,
    'brew_packages': [],

    # CodeBuild
    'enabled': True,
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

        'cmake_args': [
            "-DPERFORM_HEADER_CHECK=ON",
        ],

        'use_apt': True,
        'apt_repos': [
            "ppa:ubuntu-toolchain-r/test",
        ],

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'al2012': {
        'cmake_args': [
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

        'cmake_args': [
            "-DPERFORM_HEADER_CHECK=ON",
        ],

        'image_type': "WINDOWS_CONTAINER",
        'compute_type': "BUILD_GENERAL1_MEDIUM",
    },
    'macos': {
        'python': "python3",

        'use_brew': True,
    }
}

TARGETS = {
    'linux': {
        'architectures': {
            'x86': {
                'cmake_args': [
                    '-DCMAKE_C_FLAGS=-m32',
                    '-DCMAKE_CXX_FLAGS=-m32',
                ],
            },
        },

        'cmake_args': [
            "-DENABLE_SANITIZERS=ON",
        ],
    },
    'macos': {
        'architectures': {
            'x86': {
                'cmake_args': [
                    '-DCMAKE_C_FLAGS=-m32',
                    '-DCMAKE_CXX_FLAGS=-m32',
                ],
            },
        },
    },
    'android': {
        'cmake_args': [
            "-DTARGET_ARCH=ANDROID",
            "-DCMAKE_TOOLCHAIN_FILE=/opt/android-ndk/build/cmake/android.toolchain.cmake",
            "-DANDROID_NDK=/opt/android-ndk",
        ],
        'run_tests': False,

        'architectures': {
            'arm64v8a': {
                'cmake_args': [
                    "-DANDROID_ABI=arm64-v8a",
                ],
            },
        },

        'image_type': "LINUX_CONTAINER",
        'compute_type': "BUILD_GENERAL1_SMALL",
    },
    'windows': {
        "variables": {
            "exe": ".exe"
        }
    },
}

COMPILERS = {
    'default': {
        'hosts': ['macos', 'al2012', 'manylinux'],
        'targets': ['macos', 'linux'],

        'versions': {
            'default': { }
        }
    },
    'clang': {
        'hosts': ['linux', 'macos'],
        'targets': ['linux', 'macos'],

        'post_build_steps': [
            ["{clang_tidy}", "-p", "{build_dir}", "{sources}"],
        ],
        'cmake_args': ['-DCMAKE_EXPORT_COMPILE_COMMANDS=ON', '-DENABLE_FUZZ_TESTS=ON'],

        'apt_keys': ["http://apt.llvm.org/llvm-snapshot.gpg.key"],

        'versions': {
            '3': {
                '!post_build_steps': [],
                '!apt_repos': [],
                '!cmake_args': [],

                'apt_packages': ["clang-3.9"],
                'c': "clang-3.9",
                'cxx': "clang-3.9",
            },
            '6': {
                'apt_repos': [
                    "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-6.0 main",
                ],
                'apt_packages': ["clang-6.0", "clang-tidy-6.0"],

                'c': "clang-6.0",
                'cxx': "clang-6.0",

                'variables': {
                    'clang_tidy': 'clang-tidy-6.0',
                },

                'requires_privilege': True,
            },
            '8': {
                'apt_repos': [
                    "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-8 main",
                ],
                'apt_packages': ["clang-8", "clang-tidy-8"],

                'c': "clang-8",
                'cxx': "clang-8",

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

        'c': "gcc-{version}",
        'cxx': "g++-{version}",
        'apt_packages': ["gcc-{version}", "g++-{version}"],

        'versions': {
            '4.8': {},
            '5': {},
            '6': {},
            '7': {},
            '8': {},
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

        'cmake_args': ["-G", "Visual Studio {generator_version}{generator_postfix}"],

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
                'cmake_args': [
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
        if value and value.rfind('{') == 0 and value.find('}') == len(value) - 1:
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
def produce_config(build_spec, config_file, **additional_variables):

    validate_build(build_spec)

    # Build the list of config options to poll
    configs = []

    # Processes a config object (could come from a file), searching for keys hosts, targets, and compilers
    def process_config(config):

        def process_element(map, element_name, instance):
            if not map:
                return

            element = map.get(element_name)
            if not element:
                return

            new_config = element.get(instance)
            if not new_config:
                return

            configs.append(new_config)

            config_archs = new_config.get('architectures')
            if config_archs:
                config_arch = config_archs.get(build_spec.arch)
                if config_arch:
                    configs.append(config_arch)

            return new_config

        process_element(config, 'hosts', build_spec.host)
        process_element(config, 'targets', build_spec.target)

        compiler = process_element(config, 'compilers', build_spec.compiler)
        process_element(compiler, 'versions', build_spec.compiler_version)

    process_config({
        'hosts': HOSTS,
        'targets': TARGETS,
        'compilers': COMPILERS,
    })

    if config_file:
        if not os.path.exists(config_file):
            raise Exception("Config file {} specified, but could not be found".format(config_file))

        import json
        with open(config_file, 'r') as config_fp:
            try:
                project_config = json.load(config_fp)
                process_config(project_config)
            except Exception as e:
                print("Failed to parse config file", config_file, e)
                sys.exit(1)

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
    new_version['variables'] = replacements

    return new_version


########################################################################################################################
# ACTIONS
########################################################################################################################
class Builder(VirtualModule):
    """ The interface available to scripts that define projects, builds, actions, or configuration """
    # Must cache available actions or the GC will delete them
    all_actions = set()
    def __init__(self):
        Builder.all_actions = set(Builder.Action.__subclasses__())
        self._load_scripts()

    @staticmethod
    def _load_scripts():
        """ Loads all scripts from ${cwd}/.builder/**/*.py to make their classes available """
        import importlib.util

        if not os.path.isdir('.builder'):
            return
        
        scripts = glob.glob('.builder/**/*.py')
        for script in scripts:
            print("Importing {}".format(os.path.abspath(script)), flush=True)
            
            name = os.path.split(script)[1].split('.')[0]
            spec = importlib.util.spec_from_file_location(name, script)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            actions = frozenset(Builder._find_actions())
            new_actions = actions.difference(Builder.all_actions)
            print("Imported {}".format(', '.join([a.__name__ for a in new_actions])))
            Builder.all_actions.update(new_actions)


    @staticmethod
    def _find_actions():
        return Builder.Action.__subclasses__()

    @staticmethod
    def find_action(name):
        name = name.replace('-', '').lower()
        all_actions = Builder._find_actions()
        for action in all_actions:
            if action.__name__.lower() == name:
                return action

    @staticmethod
    def run_action(action, env):
        action_type = type(action)
        if action_type is str:
            try:
                action_cls = Builder.find_action(action)
                action = action_cls()
            except:
                print("Unable to find action {} to run".format(action))
                all_actions = [a.__name__ for a in Builder._find_actions()]
                print("Available actions: \n\t{}".format('\n\t'.join(all_actions)))
                sys.exit(2)

        print("Running: {}".format(action), flush=True)
        children = action.run(env)
        if children:
            for child in children:
                Builder.run_action(child, env)
        print("Finished: {}".format(action), flush=True)

    class Shell(object):
        """ Virtual shell that abstracts away dry run and tracks/logs state """

        def __init__(self, dryrun=False):
            # Used in dry-run builds to track simulated working directory
            self._cwd = os.getcwd()
            # pushd/popd stack
            self.dir_stack = []
            self.dryrun = dryrun

        def _flatten_command(self, *command):
            # Process out lists
            new_command = []

            def _proc_segment(command_segment):
                e_type = type(command_segment)
                if e_type == str:
                    new_command.append(command_segment)
                elif e_type == list or e_type == tuple:
                    for segment in command_segment:
                        _proc_segment(segment)
            _proc_segment(command)
            return new_command

        def _log_command(self, *command):
            print('>', subprocess.list2cmdline(
                self._flatten_command(*command)), flush=True)

        def _run_command(self, *command):
            self._log_command(*command)
            if not self.dryrun:
                subprocess.check_call(self._flatten_command(
                    *command), stdout=sys.stdout, stderr=sys.stderr)

        def _cd(self, directory):
            if self.dryrun:
                if os.path.isabs(directory) or directory.startswith('$'):
                    self._cwd = directory
                else:
                    self._cwd = os.path.join(self._cwd, directory)
            else:
                os.chdir(directory)

        # Helper to run chdir regardless of dry run status
        def cd(self, directory):
            self._log_command("cd", directory)
            self._cd(directory)

        def pushd(self, directory):
            self._log_command("pushd", directory)
            self.dir_stack.append(self.cwd())
            self._cd(directory)

        def popd(self):
            if len(self.dir_stack) > 0:
                self._log_command("popd", self.dir_stack[-1])
                self._cd(self.dir_stack[-1])
                self.dir_stack.pop()

        # Helper to run makedirs regardless of dry run status
        def mkdir(self, directory):
            self._log_command("mkdir", "-p", directory)
            if not self.dryrun:
                os.makedirs(directory, exist_ok=True)

        def mktemp(self):
            if self.dryrun:
                return os.path.expandvars("$TEMP/build")

            return tempfile.mkdtemp()

        def cwd(self):
            if self.dryrun:
                return self._cwd
            else:
                return os.getcwd()

        def setenv(self, var, value):
            self._log_command(["export", "{}={}".format(var, value)])
            if not self.dryrun:
                os.environ[var] = value

        def rm(self, path):
            self._log_command(["rm -rf", path])
            if not self.dryrun:
                try:
                    shutil.rmtree(path)
                except Exception as e:
                    print("Failed to delete dir {}: {}".format(path, e))

        def where(self, exe, path=None):
            if path is None:
                path = os.environ['PATH']
            paths = path.split(os.pathsep)
            extlist = ['']

            def is_executable(path):
                return os.path.isfile(path) and os.access(path, os.X_OK)
            if sys.platform == 'win32':
                pathext = os.environ['PATHEXT'].lower().split(os.pathsep)
                (base, ext) = os.path.splitext(exe)
                if ext.lower() not in pathext:
                    extlist = pathext
            for ext in extlist:
                exe_name = exe + ext
                for p in paths:
                    exe_path = os.path.join(p, exe_name)
                    if is_executable(exe_path):
                        return exe_path

            return None

        def exec(self, *command, **kwargs):
            if kwargs.get('always', False):
                prev_dryrun = self.dryrun
                self.dryrun = False
                self._run_command(*command)
                self.dryrun = prev_dryrun
            else:
                self._run_command(*command)


    class Env(object):
        """ Encapsulates the environment in which the build is running """
        def __init__(self, config={}):
            self._projects = {}

            # DEFAULTS
            self.dryrun = False # overwritten by config
            # default the branch to whatever the current dir+git says it is
            self.branch = self._get_git_branch()
            
            # OVERRIDES: copy incoming config, overwriting defaults
            for key, val in config.items():
                setattr(self, key, val)
            
            # default the project to whatever can be found
            if not hasattr(self, 'project'):
                self.project = self._default_project()

            if not hasattr(self, 'shell'):
                self.shell = Builder.Shell(self.dryrun)

        @staticmethod
        def _get_git_branch():
            travis_pr_branch = os.environ.get("TRAVIS_PULL_REQUEST_BRANCH")
            if travis_pr_branch:
                print("Found branch:", travis_pr_branch)
                return travis_pr_branch

            github_ref = os.environ.get("GITHUB_REF")
            if github_ref:
                origin_str = "refs/heads/"
                if github_ref.startswith(origin_str):
                    branch = github_ref[len(origin_str):]
                    print("Found github ref:", branch)
                    return branch

            branches = subprocess.check_output(
                ["git", "branch", "-a", "--contains", "HEAD"]).decode("utf-8")
            branches = [branch.strip('*').strip()
                        for branch in branches.split('\n') if branch]

            print("Found branches:", branches)

            for branch in branches:
                if branch == "(no branch)":
                    continue

                origin_str = "remotes/origin/"
                if branch.startswith(origin_str):
                    branch = branch[len(origin_str):]

                return branch

            return None

        def _cache_project(self, project):
            self._projects[project.name] = project
            return project

        def _default_project(self):
            project = self._project_from_cwd()
            if project:
                return self._cache_project(project)
            if not self.args.project:
                print(
                    "Multiple projects available and no project (-p|--project) specified")
                print("Available projects:", ', '.join(
                    [p.__name__ for p in Builder.Project.__subclasses__()]))
                sys.exit(1)
            
            project_name = self.args.project
            projects = Builder.Project.__subclasses__()
            for project_cls in projects:
                if project_cls.__name__ == project_name:
                    project = project_cls()
                    return self._cache_project(project)
            print("Could not find project named {}".format(project_name))
            sys.exit(1)


        def _project_from_cwd(self, name_hint=None):
            project_config = None
            project_config_file = os.path.abspath("builder.json")
            if os.path.exists(project_config_file):
                import json
                with open(project_config_file, 'r') as config_fp:
                    try:
                        project_config = json.load(config_fp)
                        return self._cache_project(Builder.Project(**project_config))
                    except Exception as e:
                        print("Failed to parse config file",
                            project_config_file, e)
                        sys.exit(1)
        
            # load any builder scripts and check them
            Env._load_scripts()
            projects = Builder.Project.__subclasses__()
            if len(projects) == 1:
                project_cls = projects[0]
                project = project_cls()
                return self._cache_project(project)
            # if there are multiple projects, try to use the hint if there is one
            if name_hint:
                for project_cls in projects:
                    if project_cls.__name__ == name_hint:
                        project = project_cls()
                        return self._cache_project(project)

            return None

        def find_project(self, name):
            project = self._projects.get(name, None)
            if project
                return project
            
            sh = self.shell
            search_dirs = [os.cwd(), name, os.path.join(sh.cwd(), 'deps'), os.path.join(sh.cwd(), 'build', 'deps', name)]

            for search_dir in search_dirs:
                if (os.path.basename(search_dir) == name):
                    sh.pushd(search_dir)
                    project = self._project_from_cwd(name)
                    sh.popd()
                    if project:
                        return self._cache_project(project)

            # Enough of a project to get started, note that this is not cached
            return Builder.Project(name=name)
                

        def _find_compiler_tool(self, name, versions):
            for version in versions:
                for pattern in ('{name}-{version}', '{name}-{version}.0'):
                    exe = pattern.format(name=name, version=version)
                    path = self.shell.where(exe)
                    if path:
                        return path
            return None

        def find_gcc_tool(self, name, version=None):
            versions = [version] if version else list(range(8, 5, -1))
            return self._find_compiler_tool(name, versions)

        def find_llvm_tool(self, name, version=None):
            versions = [version] if version else list(range(10, 6, -1))
            return self._find_compiler_tool(name, versions)
    

    class Action(object):
        """ A build step """
        def run(self, env):
            pass
        
        def __str__(self):
            return self.__class__.__name__

    class Script(Action):
        """ A build step that runs a series of shell commands or python functions """

        def __init__(self, commands):
            self.commands = commands

        def run(self, env):
            sh = env.shell

            for cmd in self.commands:
                cmd_type = type(cmd)
                if cmd_type == str:
                    sh.exec(cmd)
                elif cmd_type == list:
                    sh.exec(*cmd)
                elif isinstance(cmd, Builder.Action):
                    Builder.run_action(cmd, env)
                elif callable(cmd):
                    return cmd(env)
                else:
                    print('Unknown script sub command: {}: {}', cmd_type, cmd)
                    sys.exit(4)

        def __str__(self):
            cmds = []
            for cmd in self.commands:
                cmd_type = type(cmd)
                if cmd_type == str:
                    cmds.append(cmd)
                elif cmd_type == list:
                    cmds.append(' '.join(cmd))
                elif isinstance(cmd, Builder.Action):
                    cmds.append(str(cmd))
                elif callable(cmd):
                    cmds.append(cmd.__func__.__name__)
                else:
                    cmds.append("UNKNOWN: {}".format(cmd))
            return '{}: (\n\t{})'.format(self.__class__.__name__, '\n\t'.join(cmds))
    

    class Project(object):
        """ Describes a given library and its dependencies/consumers """
        def __init__(self, **kwargs):
            self.upstream = self.dependencies = kwargs.get('upstream', [])
            self.downstream = self.consumers = kwargs.get('downstream', [])
            self.account = kwargs.get('account', 'awslabs')
            self.name = kwargs['name']
            self.url = "https://github.com/{}/{}.git".format(self.account, self.name)

        def __repr__(self):
            return "{}: {}".format(self.name, self.url)

    class Toolchain(object):
        """ Represents a compiler toolchain """
        def __init__(self, **kwargs):
            if 'default' in kwargs or len(kwargs) == 0:
                for slot in ('host', 'target', 'arch', 'compiler', 'compiler_version'):
                    setattr(self, slot, 'default')

            if 'spec' in kwargs:
                # Parse the spec from a single string
                self.host, self.compiler, self.compiler_version, self.target, self.arch, * \
                    rest = kwargs['spec'].split('-')

            # Pull out individual fields. Note this is not in an else to support overriding at construction time
            for slot in ('host', 'target', 'arch', 'compiler', 'compiler_version'):
                if slot in kwargs:
                    setattr(self, slot, kwargs[slot])

            self.name = '-'.join([self.host, self.compiler,
                                self.compiler_version, self.target, self.arch])


        def compiler_path(self, env):
            if self.compiler == 'default':
                env_cc = os.environ.get('CC', None)
                if env_cc:
                    return env.shell.where(env_cc)
                return env.shell.where('cc')
            elif self.compiler == 'clang':
                return env.find_llvm_tool('clang', self.compiler_version if self.compiler_version != 'default' else None)
            elif self.compiler == 'gcc':
                return env.find_gcc_tool('gcc', self.compiler_version if self.compiler_version != 'default' else None)
            elif self.compiler == 'msvc':
                return env.shell.where('cl.exe')
            return None

        def __str__(self):
            return self.name

        def __repr__(self):
            return self.name


    class InstallTools(Action):
        def run(self, env):
            config = env.config
            sh = env.shell

            if getattr(env.args, 'skip_install', False):
                return

            if config['use_apt']:
                # Install keys
                for key in config['apt_keys']:
                    sh.exec("sudo", "apt-key", "adv", "--fetch-keys", key)

                # Add APT repositories
                for repo in config['apt_repos']:
                    sh.exec("sudo", "apt-add-repository", repo)

                # Install packages
                if config['apt_packages']:
                    sh.exec("sudo", "apt-get", "-qq", "update", "-y")
                    sh.exec("sudo", "apt-get", "-qq", "install",
                            "-y", "-f", config['apt_packages'])

            if config['use_brew']:
                for package in config['brew_packages']:
                    sh.exec("brew", "install", package)


    class DownloadDependencies(Action):
        def run(self, env):
            project = env.project
            sh = env.shell
            branch = env.branch
            deps = project.upstream

            if deps:
                for dep in deps:
                    dep_proj = env.find_project(dep)
                    download_project(dep_proj)

            def download_project(proj):
                sh.exec("git", "clone", "project", always=True)
                sh.pushd(project.name)
                try:
                    sh.exec("git", "checkout", branch, always=True)
                except:
                    print("Project {} does not have a branch named {}, using master".format(
                        project.name, branch))
                sh.popd()


    class CMakeBuild(Action):
        def run(self, env):
            try:
                toolchain = env.toolchain
            except:
                try:
                    toolchain = env.toolchain = Builder.Toolchain(spec=env.args.build)
                except:
                    toolchain = env.toolchain = Builder.Toolchain(default=True)

            sh = env.shell

            #TODO These platforms don't succeed when doing a RelWithDebInfo build
            build_config = env.args.config
            if toolchain.host in ("al2012", "manylinux"):
                build_config = "Debug"

            source_dir = os.environ.get("CODEBUILD_SRC_DIR", sh.cwd())

            # Make the install directory
            install_dir = os.path.join(source_dir, 'install')
            sh.mkdir(install_dir)

            config = getattr(env, 'config', None)
            if config:
                env.build_tests = config.get('build_tests', True)

            def build_project(project, build_tests=False):
                project_source_dir = sh.cwd()
                project_build_dir = os.path.join(project_source_dir, 'build')
                sh.mkdir(project_build_dir)
                sh.pushd(project_build_dir)

                # Set compiler flags
                compiler_flags = []
                if toolchain.compiler != 'default':
                    compiler_path = toolchain.compiler_path(env)
                    if compiler_path:
                        for opt in ['c', 'cxx']:
                            compiler_flags.append(
                                '-DCMAKE_{}_COMPILER={}'.format(opt.upper(), compiler_path))

                    if config:
                        for opt, variable in {'c': 'CC', 'cxx': 'CXX'}.items():
                            if opt in config and config[opt]:
                                os.environ[variable] = config[opt]

                cmake_args = [
                    "-Werror=dev",
                    "-Werror=deprecated",
                    "-DCMAKE_INSTALL_PREFIX=" + install_dir,
                    "-DCMAKE_PREFIX_PATH=" + install_dir,
                    # Each image has a custom installed openssl build, make sure CMake knows where to find it
                    "-DLibCrypto_INCLUDE_DIR=/opt/openssl/include",
                    "-DLibCrypto_SHARED_LIBRARY=/opt/openssl/lib/libcrypto.so",
                    "-DLibCrypto_STATIC_LIBRARY=/opt/openssl/lib/libcrypto.a",
                    "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                    "-DCMAKE_BUILD_TYPE=" + build_config,
                    "-DBUILD_TESTING=" + ("ON" if build_tests else "OFF"),
                ] + compiler_flags + getattr(project, 'cmake_args', []) + getattr(config, 'cmake_args', [])

                # configure
                sh.exec("cmake", cmake_args, project_source_dir)

                # build
                #sh.exec("cmake", "--build", ".", "--config", build_config)

                # install
                sh.exec("cmake", "--build", ".", "--config",
                        build_config, "--target", "install")

                sh.popd()

            def build_projects(projects):
                project_build_dir = os.path.join(source_dir, 'build')
                sh.mkdir(project_build_dir)
                sh.pushd(project_build_dir)

                for proj in projects:
                    project = env.find_project(proj)
                    build_project(project)

                sh.popd()

            sh.pushd(source_dir)

            build_projects(env.project.upstream)
            build_project(env.project, getattr(env, 'build_tests', False))

            spec = getattr(env, 'build_spec', None)
            if spec and spec.downstream:
                build_projects(env.project.downstream)

            sh.popd()

    class CTestRun(Action):
        def run(self, env):
            has_tests = getattr(env, 'build_tests', False)
            if not has_tests:
                print("No tests were built, skipping test run")
                return

            sh = env.shell

            project_source_dir = sh.cwd()
            project_build_dir = os.path.join(project_source_dir, 'build')
            sh.pushd(project_build_dir)

            sh.exec("ctest", "--output-on-failure")

            sh.popd()



########################################################################################################################
# RUN BUILD
########################################################################################################################
def run_build(build_spec, env):

    # Build the config object
    config_file = os.path.join(env.shell.cwd(), "builder.json")
    env.config = produce_config(build_spec, config_file)
    if not env.config['enabled']:
        raise Exception("The project is disabled in this configuration")

    Builder.run_action(
        Builder.Script([
            Builder.InstallTools(),
            Builder.DownloadDependencies(),
            Builder.CMakeBuild(),
            Builder.CTestRun()
        ]),
        env
    )

    return

    shell = Builder.Shell(is_dryrun)

    #TODO These platforms don't succeed when doing a RelWithDebInfo build
    if build_spec.host in ("al2012", "manylinux"):
        build_config = "Debug"

    source_dir = os.environ.get("CODEBUILD_SRC_DIR", os.getcwd())
    sources = [os.path.join(source_dir, file) for file in glob.glob('**/*.c')]

    built_projects = []

    git_branch = Builder.Env.get_git_branch()
    if git_branch:
        print("On git branch {}".format(git_branch))

    # Make the build directory
    build_dir = shell.mktemp()

    # Make the install directory
    install_dir = os.path.join(build_dir, 'install')
    shell.mkdir(install_dir)

    # Build a list of projects from a config file
    def _build_dependencies(project_list, build_tests, run_tests):

        shell.pushd(build_dir)

        for project in project_list:
            name = project.get("name", None)
            if not name:
                raise Exception("Project definition missing name: " + project)

            # Skip project if already built
            if name in built_projects:
                continue

            hosts = project.get("hosts", None)
            if hosts and build_spec.host not in hosts:
                print("Skipping dependency {} as it is not enabled for this host".format(name))
                continue

            targets = project.get("targets", None)
            if targets and build_spec.target not in targets:
                print("Skipping dependency {} as it is not enabled for this target".format(name))
                continue

            account = project.get("account", "awslabs")
            pin = project.get("revision", None)

            git = "https://github.com/{}/{}".format(account, name)
            shell.exec("git", "clone", git)

            shell.pushd(name)

            # Attempt to checkout a branch with the same name as the current branch
            try:
                shell.exec("git", "checkout", git_branch)
            except:
                print("Project {} does not have a branch {}".format(name, git_branch))
                # Attempt to checkout the pinned revision
                if pin:
                    shell.exec("git", "checkout", pin)

            # Build/install
            _build_project(name, build_tests=build_tests, run_tests=run_tests)

            shell.popd()

        shell.popd()

    # Helper to build
    def _build_project(project=None, build_tests=False, run_tests=False, build_downstream=False):

        if not project:
            project_source_dir = source_dir
            project_build_dir = build_dir
        else:
            project_source_dir = os.path.join(build_dir, project)
            project_build_dir = os.path.join(project_source_dir, 'build')

        def _build_project_cmake():
            # If the build directory doesn't already exist, make it
            shell.mkdir(project_build_dir)

            # CD to the build directory
            shell.pushd(project_build_dir)

            # Set compiler flags
            compiler_flags = []
            for opt in ['c', 'cxx']:
                if opt in config and config[opt]:
                    compiler_flags.append('-DCMAKE_{}_COMPILER={}'.format(opt.upper(), config[opt]))

            # Run CMake
            cmake_args = [
                "-Werror=dev",
                "-Werror=deprecated",
                "-DCMAKE_INSTALL_PREFIX=" + install_dir,
                "-DCMAKE_PREFIX_PATH=" + install_dir,
                # Each image has a custom installed openssl build, make sure CMake knows where to find it
                "-DLibCrypto_INCLUDE_DIR=/opt/openssl/include",
                "-DLibCrypto_SHARED_LIBRARY=/opt/openssl/lib/libcrypto.so",
                "-DLibCrypto_STATIC_LIBRARY=/opt/openssl/lib/libcrypto.a",
                "-DCMAKE_BUILD_TYPE=" + build_config,
                "-DBUILD_TESTING=" + ("ON" if build_tests else "OFF"),
            ]
            shell.exec("cmake", config['cmake_args'], compiler_flags, cmake_args, project_source_dir)

            # Run the build
            shell.exec("cmake", "--build", ".", "--config", build_config)

            # Do install
            shell.exec("cmake", "--build", ".", "--config", build_config, "--target", "install")

            shell.popd()

        def _test_project_ctest():
            shell.pushd(project_build_dir)
            shell.exec("ctest", ".", "--output-on-failure")
            shell.popd()

        upstream = []
        downstream = []
        build_fn = _build_project_cmake
        test_fn = _test_project_ctest

        project_config_file = os.path.join(project_source_dir, "builder.json")
        if os.path.exists(project_config_file):
            import json
            with open(project_config_file, 'r') as config_fp:
                try:
                    project_config = json.load(config_fp)
                except Exception as e:
                    print("Failed to parse config file", project_config_file, e)
                    sys.exit(1)

            project = project_config.get("name", project)
            upstream = project_config.get("upstream", [])
            downstream = project_config.get("downstream", [])

            command_variables = {
                **config,
                **config['variables'],
                'source_dir': project_source_dir,
                'build_dir': project_build_dir,
                'install_dir': install_dir,
                'build_config': build_config,
            }

            config_build = project_config.get("build", None)
            if config_build:
                assert isinstance(config_build, list)
                def _build_project_config():
                    for opt, variable in {'c': 'CC', 'cxx': 'CXX'}.items():
                        if opt in config and config[opt]:
                            os.environ[variable] = config[opt]
                    for command in config_build:
                        final_command = _replace_variables(command, command_variables)
                        shell.exec(final_command)

                build_fn = _build_project_config

            config_test = project_config.get("test", None)
            if config_test:
                assert isinstance(config_test, list)
                def _test_project_config():
                    for command in config_test:
                        final_command = _replace_variables(command, command_variables)
                        shell.exec(final_command)
                test_fn = _test_project_config

        pwd = shell.cwd()

        # If project not specified, and not pulled from the config file, default to file path
        if not project:
            project = os.path.basename(source_dir)

        # Build upstream dependencies (don't build or run their tests)
        _build_dependencies(upstream, build_tests=False, run_tests=False)

        build_fn()

        # Run the tests
        if run_tests:
            test_fn()

        # Mark project as built
        if project:
            built_projects.append(project)

        # Build downstream dependencies (build and run their tests if this build is setup for that)
        if build_downstream:
            _build_dependencies(downstream, build_tests=build_tests, run_tests=run_tests)

        # CD back to the beginning directory
        shell.cd(pwd)

    # Build the config object
    config_file = os.path.join(shell.cwd(), "builder.json")
    config = produce_config(build_spec, config_file, sources=sources, source_dir=source_dir, build_dir=build_dir)
    if not config['enabled']:
        raise Exception("The project is disabled in this configuration")

    # INSTALL
    if config['use_apt']:
        # Install keys
        for key in config['apt_keys']:
            shell.exec("sudo", "apt-key", "adv", "--fetch-keys", key)

        # Add APT repositories
        for repo in config['apt_repos']:
            shell.exec("sudo", "apt-add-repository", repo)

        # Install packages
        if config['apt_packages']:
            shell.exec("sudo", "apt-get", "-qq", "update", "-y")
            shell.exec("sudo", "apt-get", "-qq", "install", "-y", "-f", config['apt_packages'])

    if config['use_brew']:
        for package in config['brew_packages']:
            shell.exec("brew", "install", package)

    # PRE BUILD

    # Set build environment
    for var, value in config['build_env'].items():
        shell.setenv(var, value)
        
    # Run configured pre-build steps
    for step in config['pre_build_steps']:
        shell.exec(step)

    # BUILD

    # Actually run the build (always build tests, even if we won't run them)
    _build_project(project=None, build_tests=True, run_tests=config['run_tests'], build_downstream=build_spec.downstream)

    # POST BUILD

    # Run configured post-build steps
    for step in config['post_build_steps']:
        shell.exec(step)

    # Delete temp dir
    shell.rm(build_dir)

########################################################################################################################
# CODEBUILD
########################################################################################################################

CODEBUILD_OVERRIDES = {
    'linux-clang-3-linux-x64': ['linux-clang3-x64'],
    'linux-clang-6-linux-x64': ['linux-clang6-x64'],
    'linux-clang-8-linux-x64': ['linux-clang8-x64'],
    'linux-clang-6-linux-x64-downstream': ['downstream'],

    'linux-gcc-4.8-linux-x86': ['linux-gcc-4x-x86', 'linux-gcc-4-linux-x86'],
    'linux-gcc-4.8-linux-x64': ['linux-gcc-4x-x64', 'linux-gcc-4-linux-x64'],
    'linux-gcc-5-linux-x64': ['linux-gcc-5x-x64'],
    'linux-gcc-6-linux-x64': ['linux-gcc-6x-x64'],
    'linux-gcc-7-linux-x64': ['linux-gcc-7x-x64'],
    'linux-gcc-8-linux-x64': [],

    'linux-ndk-19-android-arm64v8a': ['android-arm64-v8a'],

    'al2012-default-default-linux-x64': ["AL2012-gcc44"],

    'manylinux-default-default-linux-x86': ["ancient-linux-x86"],
    'manylinux-default-default-linux-x64': ["ancient-linux-x64"],

    'windows-msvc-2015-windows-x86': ['windows-msvc-2015-x86'],
    'windows-msvc-2015-windows-x64': ['windows-msvc-2015'],
    'windows-msvc-2017-windows-x64': ['windows-msvc-2017'],
}

def create_codebuild_project(config, project, github_account, inplace_script):

    variables = {
        'project': project,
        'account': github_account,
        'spec': config['spec'].name,
        'python': config['python'],
    }

    if inplace_script:
        run_commands = ["{python} ./codebuild/builder.py build {spec}"]
    else:
        run_commands = [
            "{python} -c \\\"from urllib.request import urlretrieve; urlretrieve('https://raw.githubusercontent.com/awslabs/aws-c-common/master/codebuild/builder.py', 'builder.py')\\\"",
            "{python} builder.py build {spec}"
        ]

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
                '\n'.join(['      - "{}"'.format(command) for command in run_commands]),
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
    parser.add_argument('-p', '--project', action='store', type=str, help="Project to work on")
    parser.add_argument('--config', type=str, default='RelWithDebInfo', help='The native code configuration to build with')
    commands = parser.add_subparsers(dest='command')

    build = commands.add_parser('build', help="Run target build, formatted 'host-compiler-compilerversion-target-arch'. Ex: linux-ndk-19-android-arm64v8a")
    build.add_argument('build', type=str, default='default')
    build.add_argument('--skip-install', action='store_true', help="Skip the install phase, useful when testing locally")

    run = commands.add_parser('run', help='Run action. Ex: do-thing')
    run.add_argument('run', type=str)

    codebuild = commands.add_parser('codebuild', help="Create codebuild jobs")
    codebuild.add_argument('project', type=str, help='The name of the repo to create the projects for')
    codebuild.add_argument('--github-account', type=str, dest='github_account', default='awslabs', help='The GitHub account that owns the repo')
    codebuild.add_argument('--profile', type=str, default='default', help='The profile in ~/.aws/credentials to use when creating the jobs')
    codebuild.add_argument('--inplace-script', action='store_true', help='Use the python script in codebuild/builder.py instead of downloading it')
    codebuild.add_argument('--config', type=str, help='The config file to use when generating the projects')

    args = parser.parse_args()

    builder = Builder()
    env = Builder.Env({
        'dryrun': args.dry_run,
        'args': args
    })

    if args.command == 'build':
        # If build name not passed
        build_name = args.build
        build_spec = env.build_spec = BuildSpec(spec=build_name)
        print("Running build", build_spec.name, flush=True)

        run_build(build_spec, env)

    elif args.command == 'run':
        action = args.run
        builder.run_action(action, env)

    elif args.command == 'codebuild':

        # Setup AWS connection
        import boto3
        session = boto3.Session(profile_name=args.profile, region_name='us-east-1')
        codebuild = session.client('codebuild')

        # Get project status

        existing_projects = []
        new_projects = []

        project_prefix_len = len(args.project) + 1

        # Map of canonical builds to their existing codebuild projects (None if creation required)
        canonical_list = {key: None for key in CODEBUILD_OVERRIDES.keys()}
        # List of all potential names to search for
        all_potential_builds = list(CODEBUILD_OVERRIDES.keys())
        # Reverse mapping of codebuild name to canonical name
        full_codebuild_to_canonical = {key.replace('.', ''): key for key in CODEBUILD_OVERRIDES.keys()}
        for canonical, cb_list in CODEBUILD_OVERRIDES.items():
            all_potential_builds += cb_list
            for cb in cb_list:
                full_codebuild_to_canonical[cb] = canonical

        # Search for the projects
        full_project_names = ['{}-{}'.format(args.project, build.replace('.', '')) for build in all_potential_builds]
        old_projects_response = codebuild.batch_get_projects(names=full_project_names)
        existing_projects += [project['name'][project_prefix_len:] for project in old_projects_response['projects']]

        # Mark the found projects with their found names
        for project in existing_projects:
            canonical = full_codebuild_to_canonical[project]
            canonical_list[canonical] = project

        # Update all existing projects
        for canonical, cb_name in canonical_list.items():
            if cb_name:
                create = False
            else:
                cb_name = canonical
                create = True

            build_name = '{}-{}'.format(args.project, cb_name)

            build_spec = BuildSpec(spec=canonical)
            config = produce_config(build_spec, args.config)
            if not config['enabled']:
                print("Skipping spec {}, as it's disabled".format(build_spec.name))
                continue

            cb_project = create_codebuild_project(config, args.project, args.github_account, args.inplace_script)
            cb_project['name'] = build_name.replace('.', '')

            if create:
                print('Creating: {}'.format(canonical))
                if not args.dry_run:
                    codebuild.create_project(**cb_project)
            else:
                print('Updating: {} ({})'.format(canonical, cb_name))
                if not args.dry_run:
                    codebuild.update_project(**cb_project)
