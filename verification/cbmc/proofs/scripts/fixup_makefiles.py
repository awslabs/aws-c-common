#!/usr/bin/env python3

import re
import sys
import pathlib


def replace(makefile, included):
    if included == "../Makefile.common":
        return "../../Makefile.common"
    if included == "../Makefile.aws_array_list":
        return "../../aws_array_list/Makefile"
    if included == "../Makefile.aws_string":
        return "../../aws_string/Makefile"
    if included == "../Makefile.aws_byte_buf":
        return "../../aws_byte_buf/Makefile"
    if included == "../Makefile.aws_linked_list":
        return "../../aws_linked_list/Makefile"
    if included == "../Makefile.aws_hash_table":
        return "../../aws_hash_table/Makefile"
    if included == "../Makefile.aws_priority_queue_sift":
        return "../../aws_priority_queue_sift/Makefile"
    return None

ok = True

pat = re.compile("include\s+(?P<path>[-/.\w]+)")
for fyle in pathlib.Path(".").rglob("Makefile"):
    this_ok = True
    buf = []
    with open(fyle) as handle:
        for line in handle:
            line = line.rstrip()
            m = pat.match(line)
            if not m:
                buf.append(line)
                continue
            included = fyle.parent / m["path"]
            if included.exists():
                buf.append(line)
            else:
                rep = replace(fyle, m["path"])
                if rep and (fyle.parent / rep).exists():
                    buf.append(f"include {rep}")
                else:
                    print(f"{fyle}: {line}", file=sys.stderr)
                    ok = False
    if this_ok:
        with open(fyle, "w") as handle:
            print("\n".join(buf), file=handle)

if not ok:
    sys.exit(1)
