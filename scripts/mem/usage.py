#!/usr/bin/env python3
#
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

import plotly.express as px

input = "sample.txt"
data = []

with open(input) as file:
    for line in file:
        if "TRACE MEM USAGE;" not in line:
            continue

        stripped = line[line.find("TRACE MEM USAGE;"):]
        
        nums = [int(s) for s in stripped.split() if s.isdigit()]
        data.append({'ts': nums[0], 'rss': nums[1], 'maxrss' : nums[2], 'alloc': nums[3], 'total' : nums[4]})

fig = px.line(data, x="ts", y=["rss", "alloc"], title='RSS over time')
fig.show()