#!/usr/bin/env python3
"""
Remote Sync Script

This script pulls a branch from a remote repository and pushes it to a new branch
called 'external-pr' in the original repository.

Helper for CRT developers to accept pull requests from forks.

Usage:
    python remote_sync.py <remote_repo_url>

Example:
    python remote_sync.py https://github.com/WillChilds-Klein/aws-crt-java/tree/main
"""

import sys
import subprocess
import re
import argparse
from urllib.parse import urlparse
import os


class RemoteSyncError(Exception):
    """Custom exception for remote sync operations"""
    pass


class RemoteSync:
    def __init__(self, remote_url, target_branch="external-pr", verbose=False):
        self.remote_url = remote_url
        self.target_branch = target_branch
        self.verbose = verbose
        self.temp_remote_name = "temp_remote_sync"

        # Parse the remote URL
        self.repo_url, self.branch_name = self._parse_remote_url(remote_url)

    def _parse_remote_url(self, url):
        """
        Parse the remote URL to extract repository URL and branch name.

        Supports formats like:
        - https://github.com/user/repo/tree/branch
        - https://github.com/user/repo (defaults to main)
        - git@github.com:user/repo.git
        """
        # Handle GitHub tree URLs
        tree_match = re.match(
            r'(https://github\.com/[^/]+/[^/]+)/tree/(.+)', url)
        if tree_match:
            repo_url = tree_match.group(1) + '.git'
            branch_name = tree_match.group(2)
            return repo_url, branch_name

        # Handle direct repository URLs
        if url.endswith('.git'):
            return url, 'main'
        else:
            parsed_url = urlparse(url)
            hostname = (parsed_url.hostname or "").lower()
            if hostname == 'github.com':
                return url + '.git', 'main'

        raise RemoteSyncError(f"Unable to parse remote URL: {url}")

    def _run_command(self, cmd, check=True, capture_output=True):
        """Run a shell command and return the result"""
        if self.verbose:
            print(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                check=check,
                capture_output=capture_output,
                text=True,
                cwd=os.getcwd()
            )
            return result
        except subprocess.CalledProcessError as e:
            error_msg = f"Command failed: {' '.join(cmd)}"
            if e.stderr:
                error_msg += f"\nError: {e.stderr}"
            raise RemoteSyncError(error_msg)

    def _check_git_repo(self):
        """Check if we're in a git repository"""
        try:
            self._run_command(['git', 'rev-parse', '--git-dir'])
            return True
        except RemoteSyncError:
            return False

    def _remote_exists(self, remote_name):
        """Check if a remote already exists"""
        try:
            result = self._run_command(
                ['git', 'remote', 'get-url', remote_name])
            return True
        except RemoteSyncError:
            return False

    def _branch_exists(self, branch_name):
        """Check if a local branch exists"""
        try:
            self._run_command(['git', 'rev-parse', '--verify', branch_name])
            return True
        except RemoteSyncError:
            return False

    def _get_current_branch(self):
        """Get the current branch name"""
        try:
            result = self._run_command(['git', 'branch', '--show-current'])
            return result.stdout.strip()
        except RemoteSyncError:
            return None

    def add_remote(self):
        """Add the temporary remote repository"""
        print(f"Adding remote repository: {self.repo_url}")

        # Remove existing remote if it exists
        if self._remote_exists(self.temp_remote_name):
            print(f"Removing existing remote: {self.temp_remote_name}")
            self._run_command(
                ['git', 'remote', 'remove', self.temp_remote_name])

        # Add the new remote
        self._run_command(
            ['git', 'remote', 'add', self.temp_remote_name, self.repo_url])
        print(f"✓ Remote '{self.temp_remote_name}' added successfully")

    def fetch_remote_branch(self):
        """Fetch the specified branch from the remote repository"""
        print(
            f"Fetching branch '{self.branch_name}' from remote repository...")

        # Always do a general fetch to avoid ambiguous refname issues
        self._run_command(['git', 'fetch', self.temp_remote_name])

        # Verify the branch exists
        try:
            self._run_command([
                'git', 'rev-parse', '--verify',
                f'{self.temp_remote_name}/{self.branch_name}'
            ])
            print(f"✓ Branch '{self.branch_name}' fetched successfully")
        except RemoteSyncError:
            raise RemoteSyncError(
                f"Branch '{self.branch_name}' not found in remote repository"
            )

    def create_sync_branch(self):
        """Create or update the external-pr branch"""
        print(f"Creating/updating branch '{self.target_branch}'...")

        # Store current branch to return to it later
        current_branch = self._get_current_branch()

        try:
            # If the target branch already exists, delete it
            if self._branch_exists(self.target_branch):
                print(
                    f"Branch '{self.target_branch}' already exists, updating it...")
                # Switch to a different branch if we're on the target branch
                if current_branch == self.target_branch:
                    # Try to switch to main or master
                    for default_branch in ['main', 'master']:
                        if self._branch_exists(default_branch):
                            self._run_command(
                                ['git', 'checkout', default_branch])
                            current_branch = default_branch
                            break

                # Delete the existing branch
                self._run_command(['git', 'branch', '-D', self.target_branch])

            # Create new branch from the fetched remote branch
            # Use the full SHA to avoid ambiguous refname issues
            remote_sha = self._run_command([
                'git', 'rev-parse', f'{self.temp_remote_name}/{self.branch_name}'
            ]).stdout.strip()

            self._run_command([
                'git', 'checkout', '-b', self.target_branch, remote_sha
            ])
            print(f"✓ Branch '{self.target_branch}' created successfully")

            # Return to original branch
            if current_branch and current_branch != self.target_branch:
                self._run_command(['git', 'checkout', current_branch])
                print(f"✓ Returned to original branch: {current_branch}")

        except RemoteSyncError as e:
            # Try to return to original branch if something went wrong
            if current_branch and current_branch != self.target_branch:
                try:
                    self._run_command(['git', 'checkout', current_branch])
                except:
                    pass
            raise e

    def push_sync_branch(self):
        """Push the external-pr branch to origin"""
        print(f"Pushing branch '{self.target_branch}' to origin...")

        try:
            # Push the branch to origin
            self._run_command(['git', 'push', 'origin', self.target_branch])
            print(f"✓ Branch '{self.target_branch}' pushed successfully")
        except RemoteSyncError:
            # If push fails, try force push (in case branch exists on remote)
            print("Regular push failed, trying force push...")
            self._run_command(
                ['git', 'push', '--force', 'origin', self.target_branch])
            print(f"✓ Branch '{self.target_branch}' force-pushed successfully")

    def cleanup(self):
        """Remove the temporary remote"""
        print("Cleaning up temporary remote...")
        try:
            self._run_command(
                ['git', 'remote', 'remove', self.temp_remote_name])
            print(f"✓ Temporary remote '{self.temp_remote_name}' removed")
        except RemoteSyncError:
            print(
                f"⚠ Could not remove temporary remote '{self.temp_remote_name}'")

    def sync(self):
        """Perform the complete sync operation"""
        print(f"Starting remote sync operation...")
        print(f"Remote URL: {self.remote_url}")
        print(f"Repository: {self.repo_url}")
        print(f"Branch: {self.branch_name}")
        print(f"Target branch: {self.target_branch}")
        print("-" * 50)

        # Verify we're in a git repository
        if not self._check_git_repo():
            raise RemoteSyncError("Not in a git repository")

        try:
            # Step 1: Add remote repository
            self.add_remote()

            # Step 2: Fetch the remote branch
            self.fetch_remote_branch()

            # Step 3: Create/update the sync branch
            self.create_sync_branch()

            # Step 4: Push to origin
            self.push_sync_branch()

            print("-" * 50)
            print("✓ Remote sync completed successfully!")
            print(
                f"✓ Branch '{self.target_branch}' now contains the latest code from:")
            print(f"  {self.repo_url} (branch: {self.branch_name})")

        finally:
            # Always cleanup, even if something fails
            self.cleanup()


def main():
    parser = argparse.ArgumentParser(
        description="Pull a branch from a remote repository and push it to 'external-pr' branch",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s https://github.com/WillChilds-Klein/aws-crt-java/tree/main
  %(prog)s https://github.com/user/repo/tree/feature-branch
  %(prog)s https://github.com/user/repo.git --branch main
  %(prog)s https://github.com/user/repo --target-branch my-sync-branch
        """
    )

    parser.add_argument(
        'remote_url',
        help='Remote repository URL (supports GitHub tree URLs)'
    )

    parser.add_argument(
        '--target-branch',
        default='external-pr',
        help='Name of the target branch to create (default: external-pr)'
    )

    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )

    args = parser.parse_args()

    try:
        syncer = RemoteSync(
            remote_url=args.remote_url,
            target_branch=args.target_branch,
            verbose=args.verbose
        )
        syncer.sync()

    except RemoteSyncError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except KeyboardInterrupt:
        print("\nOperation cancelled by user", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
