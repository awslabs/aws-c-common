
# import codebuild.builder
# import glob, os, sys

# def find_clang_tidy(shell):
#     for version in range(10, 6):
#         for pattern in ('clang-tidy-{}', 'clang-tidy-{}.0'):
#             exe = pattern.format(version)
#             path = shell.where(exe)
#             return path if path
#     return None

# class ClangTidy(Builder.Action):
#     def run(self):
#         shell = Builder.Shell()
#         clang_tidy = find_clang_tidy()
#         if not clang_tidy:
#             print("No clang-tidy executable could be found")
#             sys.exit(1)
#         source_dir = shell.cwd()
#         sources = [os.path.join(source_dir, file)
#                    for file in glob.glob('**/*.c')]
#         shell.exec(clang_tidy, '-p', build_dir)
        
