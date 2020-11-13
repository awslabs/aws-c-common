

import Builder
import glob
import os
import sys


def run_clang_tidy(env):
    sh = env.shell
    toolchain = env.toolchain
    clang_tidy = Builder.Util.where('clang-tidy')
    if not clang_tidy:
        clang_tidy = toolchain.find_llvm_tool('clang-tidy')[0]
    if not clang_tidy:
        print("No clang-tidy executable could be found")
        sys.exit(1)

    sources = [os.path.join(env.source_dir, file)
               for file in glob.glob('source/**/*.c') + glob.glob('source/*.c')
               if not ('windows' in file or 'android' in file)]

    return Builder.Script([
        [clang_tidy, '-p',
            os.path.join(env.build_dir, env.project.name)] + sources
    ])


class ClangTidy(Builder.Action):
    def is_main(self):
        return True

    def run(self, env):
        return Builder.Script([
            Builder.InstallPackages(['clang-tidy']),
            Builder.DownloadDependencies(),
            Builder.CMakeBuild(env.project),
            run_clang_tidy,
        ])
