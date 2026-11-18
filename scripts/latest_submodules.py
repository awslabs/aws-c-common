#!/usr/bin/env python3
"""
Update every git submodule of the current repo to its latest release.

Run from the root of a repo that has a .gitmodules file (e.g. aws-crt-java):

    python3 crt/aws-c-common/scripts/latest_submodules.py --dry-run
    python3 crt/aws-c-common/scripts/latest_submodules.py [SUBMODULE ...]

--dry-run prints what would change without checking anything out.
SUBMODULE names (e.g. aws-c-common) are left where they are.

By default, a submodule moves to its highest vX.Y.Z tag. For aws-lc and s2n,
which the CRT team doesn't release, a submodule already past the latest tag
is left alone.

A submodule with `branch` set in .gitmodules moves to the latest commit on
that branch instead. For example, aws-crt-java's aws-lc tracks the AWS-LC
FIPS branch:

    [submodule "aws-lc"]
        path = crt/aws-lc
        url = https://github.com/awslabs/aws-lc.git
        branch = fips-2024-09-27

The script only updates the submodule checkouts. Review and commit the
changes yourself.
"""
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

    'branch' is also present if the submodule sets it in .gitmodules.
    """
    if not os.path.exists('.gitmodules'):
        sys.exit(f'No .gitmodules found in {os.getcwd()}')

    submodules = []
    start_pattern = re.compile(r'\[submodule')
    path_pattern = re.compile(r'\s+path = (\S+)')
    url_pattern = re.compile(r'\s+url = (\S+)')
    branch_pattern = re.compile(r'\s+branch = (\S+)')

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

            m = branch_pattern.match(line)
            if m:
                current['branch'] = m.group(1)
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
    tags = {}
    for line in git_output.splitlines():
        # line looks like: "e18f041a0c8d17189f2eae2a32f16e0a7a3f0f1c refs/tags/v0.5.18"
        # Annotated tags also have a peeled line pointing at the actual commit:
        #                  "bf9994952db54440754f1eff9b5d41582e71ee52 refs/tags/v0.5.18^{}"
        match = re.match(
            r'([a-f0-9]+)\s+refs/tags/(' + prefix + r'([0-9]+)\.([0-9]+)\.([0-9]+))(\^\{\})?$', line)
        if not match:
            # skip malformed release tags
            continue
        version = match.group(2)
        peeled = match.group(6) is not None
        # For annotated tags the unpeeled SHA is the tag object, not the commit,
        # so the peeled entry takes precedence.
        if version in tags and not peeled:
            continue
        tags[version] = {
            'commit': match.group(1),
            'version': version,
            'num_tuple': (int(match.group(3)), int(match.group(4)), int(match.group(5))),
        }

    # sort highest version first
    return sorted(tags.values(), reverse=True, key=lambda tag: tag['num_tuple'])


def get_branch_head(branch):
    git_output = run('git', 'ls-remote', 'origin', f'refs/heads/{branch}').stdout
    if not git_output:
        sys.exit(f'Branch {branch} not found on origin in {os.getcwd()}')
    return git_output.split()[0]


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

        # A submodule with `branch` set in .gitmodules tracks the latest commit
        # on that branch instead of the latest release tag
        # (e.g. aws-crt-java's aws-lc tracks fips-2024-09-27).
        branch = submodule.get('branch')
        if branch:
            current_commit = get_current_commit()
            if name in args.ignore:
                print(f"{name:<{name_pad}} {current_commit} (ignored)")
                continue
            head = get_branch_head(branch)
            if head == current_commit:
                print(f"{name:<{name_pad}} {branch}@{current_commit} ✓")
            else:
                print(f"{name:<{name_pad}} {current_commit} -> {branch}@{head}")
                if not args.dry_run:
                    run('git', 'fetch', 'origin', branch)
                    run('git', 'checkout', head)
                    run('git', 'submodule', 'update')
            continue

        tags = get_release_tags()
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
