#!/usr/bin/env python3

import os
import pathlib
import shutil


def main():
    jobs_dir = pathlib.Path(".")
    suffixes = [m.name[9:] for m in jobs_dir.glob("Makefile.*")]
    suffixes.sort(key=lambda x: len(x), reverse=True)

    misc = pathlib.Path("aws_misc")
    moves = {misc: []}

    for dyr in jobs_dir.iterdir():
        if not dyr.is_dir():
            continue
        found = False
        for suffix in suffixes:
            if not dyr.name.startswith(suffix):
                continue
            group = pathlib.Path(suffix)
            pair = (dyr, group / dyr.name[len(suffix) + 1:])
            try:
                moves[group].append(pair)
            except KeyError:
                moves[group] = [pair]
            found = True
            break
        if not found:
            moves[misc].append((dyr, misc / dyr.name))

    for group, dyrs in moves.items():
        if len(dyrs) != len(set(dyrs)):
            print(f"group {group} contains duplicates")
            exit(1)
    for group, dyrs in moves.items():
        print()
        print(group.name)
        group.mkdir(exist_ok=True, parents=True)
        makefile = pathlib.Path(f"Makefile.{group.name}")
        if makefile.exists():
            makefile.rename(group / makefile.name)
        for src, dst in sorted(dyrs):
            if dst.name == group.name:
                continue
            src.rename(dst)


if __name__ == "__main__":
    main()
