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

import argparse
import boto3

# Parse required options
parser = argparse.ArgumentParser(description='Creates all required AWS CodeBuild projects for a repo')
parser.add_argument('project', type=str, help='The name of the repo to create the projects for')
parser.add_argument('--github-account', type=str, dest='github_account', default='awslabs', help='The GitHub account that owns the repo')
parser.add_argument('--profile', type=str, default='default', help='The profile in ~/.aws/credentials to use when creating the jobs')
args = parser.parse_args()

# The template for the arguments to be passed to create_project
CREATE_PARAM_TEMPLATE = {
    'name': '{project}-{build}',
    'source': {
        'type': 'GITHUB',
        'location': 'https://github.com/{account}/{project}.git',
        'gitCloneDepth': 1,
        'buildspec': 'codebuild/{build}.yml',
        'auth': {
            'type': 'OAUTH',
        },
        'reportBuildStatus': True,
    },
    'artifacts': {
        'type': 'NO_ARTIFACTS',
    },
    'environment': None,
    'serviceRole': 'arn:aws:iam::123124136734:role/CodeBuildServiceRole',
    'badgeEnabled': False,
}

# The common enviroment objects to feed to CodeBuild
ENVIRONMENTS = {
    'linux': {
        'type': 'LINUX_CONTAINER',
        'image': 'aws/codebuild/ubuntu-base:14.04',
        'computeType': 'BUILD_GENERAL1_SMALL',
        'environmentVariables': [],
        'privilegedMode': False,
    },
    'windows-2017': {
        'type': 'WINDOWS_CONTAINER',
        'image': '123124136734.dkr.ecr.us-east-1.amazonaws.com/codebulid-windows-vs-2017:latest',
        'computeType': 'BUILD_GENERAL1_MEDIUM',
        'environmentVariables': [],
        'privilegedMode': False,
    },
    'windows-2015': {
        'type': 'WINDOWS_CONTAINER',
        'image': '123124136734.dkr.ecr.us-east-1.amazonaws.com/codebulid-windows-vs-2015:latest',
        'computeType': 'BUILD_GENERAL1_MEDIUM',
        'environmentVariables': [],
        'privilegedMode': False,
    },
}

# The list of all of our build configs paired with their environments
BUILD_CONFIGS = [
    {
        'build': 'linux-clang3-x64',
        'env': 'linux'
    },
    {
        'build': 'linux-clang6-x64',
        'env': 'linux',
        'privileged': True
    },
    {
        'build': 'linux-gcc-4x-x64',
        'env': 'linux'
    },
    {
        'build': 'linux-gcc-4x-x86',
        'env': 'linux'
    },
    {
        'build': 'linux-gcc-5x-x64',
        'env': 'linux'
    },
    {
        'build': 'linux-gcc-6x-x64',
        'env': 'linux'
    },
    {
        'build': 'linux-gcc-7x-x64',
        'env': 'linux'
    },
    {
        'build': 'windows-msvc-2017',
        'env': 'windows-2017'
    },
    {
        'build': 'windows-msvc-2015',
        'env': 'windows-2015'
    },
    {
        'build': 'windows-msvc-2015-x86',
        'env': 'windows-2015'
    },
]

# Fully populate the BUILDS list with all final build objects
BUILDS = {}
for config in BUILD_CONFIGS:

    build_name = config['build']

    build = dict(CREATE_PARAM_TEMPLATE)
    env = dict(ENVIRONMENTS[config['env']])
    if 'privileged' in config:
        env['privilegedMode'] = config['privileged']
    build['environment'] = env

    sub_params = {
        'project': args.project,
        'build': build_name,
        'account': args.github_account,
    }

    # Replace all templates with the values above
    def do_replace(obj):
        if isinstance(obj, dict):
            for key, value in obj.items():
                obj[key] = do_replace(value)
            return obj
        elif isinstance(obj, str):
            return obj.format(**sub_params)
        else:
            return obj

    do_replace(build)

    BUILDS['{}-{}'.format(args.project, build_name)] = build

# Connect to codebuild
session = boto3.Session(profile_name=args.profile, region_name='us-east-1')
codebuild = session.client('codebuild')

# Find out which projects already exist and should be updated, and which must be created
all_project_names = list(BUILDS.keys())
existing_projects = codebuild.batch_get_projects(names=all_project_names)
new_projects = existing_projects['projectsNotFound']
existing_projects = [project['name'] for project in existing_projects['projects']]

# Actually create the projects
for build_name, build in BUILDS.items():
    if build_name in new_projects:
        print('{}: Creating'.format(build_name))
        codebuild.create_project(**build)
        codebuild.create_webhook(projectName=build_name)
    elif build_name in existing_projects:
        print('{}: Updating'.format(build_name))
        codebuild.update_project(**build)
    else:
        assert False
