#!/usr/bin/env python3
import argparse
import os
import os.path
import re
import subprocess
import sys


def run(*args, check=True):
    return subprocess.run(args, capture_output=True, check=check, universal_newlines=True)


def get_submodules():
    """
    Return list of submodules for current repo, sorted by name.

    Each item looks like:
    {
        'name': 'aws-c-common',
        'path': 'crt/aws-c-common',
        'url': 'https://github.com/awslabs/aws-c-common.git',
    }
    """
    if not os.path.exists('.gitmodules'):
        sys.exit(f'No .gitmodules found in {os.getcwd()}')

    submodules = []
    start_pattern = re.compile(r'\[submodule')
    path_pattern = re.compile(r'\s+path = (\S+)')
    url_pattern = re.compile(r'\s+url = (\S+)')

    current = None
    with open('.gitmodules', 'r') as f:
        for line in f.readlines():
            m = start_pattern.match(line)
            if m:
                current = {}
                submodules.append(current)
                continue

            m = path_pattern.match(line)
            if m:
                current['path'] = m.group(1)
                current['name'] = os.path.basename(current['path'])
                continue

            m = url_pattern.match(line)
            if m:
                current['url'] = m.group(1)
                continue

    return sorted(submodules, key=lambda x: x['name'])


def get_release_tags(prefix='v'):
    """
    Return list of release tags for current repo, sorted high to low.

    Each item looks like:
    {
        'commit': 'e18f041a0c8d17189f2eae2a32f16e0a7a3f0f1c',
        'version': 'v0.5.18'
        'num_tuple': (0,5,18),
    }
    """
    git_output = run('git', 'ls-remote', '--tags').stdout
    tags = []
    for line in git_output.splitlines():
        # line looks like: "e18f041a0c8d17189f2eae2a32f16e0a7a3f0f1c refs/tags/v0.5.18"
        match = re.match(
            r'([a-f0-9]+)\s+refs/tags/(' + prefix + r'([0-9]+)\.([0-9]+)\.([0-9]+))$', line)
        if not match:
            # skip malformed release tags
            continue
        tags.append({
            'commit': match.group(1),
            'version': match.group(2),
            'num_tuple': (int(match.group(3)), int(match.group(4)), int(match.group(5))),
        })

    # sort highest version first
    return sorted(tags, reverse=True, key=lambda tag: tag['num_tuple'])


def get_current_commit():
    git_output = run('git', 'rev-parse', 'HEAD').stdout
    return git_output.splitlines()[0]


def is_ancestor(ancestor, descendant):
    """Return whether first commit is an ancestor to the second'"""
    result = run('git', 'merge-base', '--is-ancestor',
                 ancestor, descendant, check=False)
    return result.returncode == 0


def get_tag_for_commit(tags, commit):
    for tag in tags:
        if tag['commit'] == commit:
            return tag
    return None


def main():
    parser = argparse.ArgumentParser(
        description="Update submodules to latest tags")
    parser.add_argument('ignore', nargs='*', help="submodules to ignore")
    parser.add_argument('--dry-run', action='store_true',
                        help="print without actually updating")
    args = parser.parse_args()

    root_path = os.getcwd()
    submodules = get_submodules()
    name_pad = max([len(x['name']) for x in submodules])
    for submodule in submodules:
        name = submodule['name']

        os.chdir(os.path.join(root_path, submodule['path']))

        version_prefix = 'v'
        # aws-crt-java uses FIPS releases of aws-lc
        if name == 'aws-lc' and 'aws-crt-java' in root_path:
            version_prefix = 'AWS-LC-FIPS-'

        tags = get_release_tags(version_prefix)
        current_commit = get_current_commit()
        current_tag = get_tag_for_commit(tags, current_commit)
        sync_from = current_tag['version'] if current_tag else current_commit

        if name in args.ignore:
            print(f"{name:<{name_pad}} {sync_from} (ignored)")
            continue

        latest_tag = tags[0]
        sync_to = latest_tag['version']

        # The only time we don't want to sync to the latest release is:
        # The submodule is at some commit beyond the latest release,
        # and the CRT team doesn't control this repo so can't just cut a new release
        if sync_from != sync_to and current_tag is None:
            if name in ['aws-lc', 's2n', 's2n-tls']:
                # must fetch tags before we can check their ancestry
                run('git', 'fetch', '--tags', '--prune', '--prune-tags', '--force')
                if not is_ancestor(ancestor=current_commit, descendant=sync_to):
                    sync_to = sync_from

        if sync_from == sync_to:
            print(f"{name:<{name_pad}} {sync_from} ✓")
        else:
            print(f"{name:<{name_pad}} {sync_from} -> {sync_to}")
            if not args.dry_run:
                run('git', 'fetch', '--tags', '--prune', '--prune-tags', '--force')
                run('git', 'checkout', sync_to)
                run('git', 'submodule', 'update')


if __name__ == '__main__':
    main()
