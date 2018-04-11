#!/usr/bin/env python

import matplotlib.pyplot as plt; plt.rcdefaults()
import numpy as np
import matplotlib.pyplot as plt

import sys
import csv
import pdb

def main():
    if len(sys.argv) != 2:
        print("Usage: <csv>")
        exit(1)

    data = slurp(sys.argv[1])
    tests = set(r["test_name"] for r in data)
    test_data = [[r for r in data if r["test_name"] == t] for t in tests]
    graph_tests(test_data)
    plt.savefig("8000-bar.png")

YMAX = 1000000
def graph_tests(tests):
    width = 1.0

    x = []
    height = []
    errors = []
    features = []
    cs = []
    hs = []

    group_ticks = []
    group_labs = []

    fig = plt.gcf()
    ax = fig.add_subplot(111)

    xstart = 2.0
    for test in tests:
        x.extend([ xstart + (x * width) for x in range(len(test))])
        height.extend([height_of(r["time"]) for r in test])
        errors.extend([error_of(r) for r in test])
        features.extend([feature_name(r["feature"]) for r in test])
        cs.extend(colors[0:len(test)])
        hs.extend(hatches[0:len(test)])

        xend = x[len(x) - 1]

        group_ticks.append((xstart + xend - 1.0) / 2.0)
        group_labs.append(test[0]["test_name"])

        xstart = xend + 4.0


    for i in range(len(x)):
        ax.bar(x[i], height[i],
            yerr=errors[i],
            color=cs[i],
            hatch=hs[i]
        )

    plt.ylim((0, YMAX))
    plt.ylabel("Running Time in ns")
    plt.xticks(x, features, rotation=45, ha="right")

    fig.set_size_inches(18.5, 10.5)
    fig.subplots_adjust(bottom=0.2, left=0.1)

    for (tick, lab) in zip(group_ticks, group_labs):
        ax.text(tick, -200000.0, test_name_of(lab),
            ha='center',
            clip_on=False,
            size='x-large',
        )


def fence_group(ax, group_name, xstart, xend):
    startline = plt.Line2D([xstart, xstart], [0.0, -0.1],
                            transform=ax.transAxes, color='black')
    startline.set_clip_on(False)
    ax.add_line(startline)

    endline = plt.Line2D([xend, xend], [0.0, -0.1],
                          transform=ax.transAxes, color='black')
    endline.set_clip_on(False)
    ax.add_line(endline)


def error_of(r):
    e = int(r["error"].replace(",", ""))
    if height_of(r["time"]) == YMAX:
        return 0
    else:
        return e

def height_of(h):
    h = int(h.replace(",", ""))
    if h > YMAX:
        return YMAX
    else:
        return h

def test_name_of(name):
    return bench_names[name[len("captures::cap_"):]]

hatches = ['-', '+', 'x', '\\', '*', 'o', 'O', '.']
colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']
bench_names = {
    "leading_dotstar": "Leading .*",
    "leading_estar": "Leading el Scan",
    "dotstar_bounce": ".* Bounce",
    "a_big_skip": "A Big Skip",
    "aplus_trailing": "Trailing .*",
    "no_opt": "No Opt",
}

def slurp(csv_file):
    data = []
    with open(csv_file, "r") as f:
        for row in csv.DictReader(f):
            data.append(row)
    return data

def feature_name(feature):
    return feature[len("catpures-"):].replace("ds-es-sl", "all")


if __name__ == "__main__":
    main()
