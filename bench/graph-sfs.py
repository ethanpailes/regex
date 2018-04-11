#!/usr/bin/env python3

import matplotlib.pyplot as plt; plt.rcdefaults()
import numpy as np
import matplotlib.pyplot as plt

import sys
import csv
import pdb

def main():
    for test in sys.argv[1:]:
        graph_test(test)
        plt.savefig(test_name(test) + ".png", bbox_inches="tight")
        plt.close()

def graph_all_features(sf_data, test):
    """ Graph a test with one line for every feature found in the data.
    """
    _, data = sf_data[0]
    
    features = []
    for col in data[test].keys():
        if col.endswith("_time"):
            features.append(col[:-len("_time")])

    graph_test(sf_data, test, features)

def slurp(test):
    data = []
    with open(test, "r") as f:
        for row in csv.DictReader(f):
            data.append(row)
    return data
    

def graph_test(test):
    """ Produce a line graph with one line per feature.
    """

    data = slurp(test + ".csv")
    features = set(row["feature"] for row in data)

    xmin = sys.maxsize
    xmax = 0

    ymax = 0
    ymin = sys.maxsize
    for (feature, marker) in zip(features, markers):
        rows = [r for r in data if r["feature"] == feature]
        scale = [int(r["scaling_factor"]) for r in rows]
        running_time = [int(r["time"].replace(",", "")) for r in rows]
        error = [int(r["error"].replace(",", "")) for r in rows]

        xmax = max(xmax, max(scale))
        xmin = min(xmin, min(scale))

        ymax = max(ymax, max(map(lambda x: x[0] + x[1],
                            zip(running_time, error))))
        ymin = min(ymin, min(map(lambda x: x[0] - x[1],
                                zip(running_time, error))))

        plt.errorbar(
            scale,
            running_time,
            yerr=error, fmt=marker,
            label=feature_name(feature),
        )

    plt.xlabel("Scaling Factor")
    plt.ylabel("Running Time in ns")
    # plt.title(test_name(test))
    plt.ylim((percent_shift(ymin, ymax - ymin, -10.0),
              percent_shift(ymax, ymax - ymin, 10.0)))
    plt.xlim((percent_shift(xmin, xmax - xmin, -10.0),
              percent_shift(xmax, xmax - xmin, 10.0)))
    plt.legend()

markers = ["o", "s", "v", "^", ">", "<", "8", "p"]

def percent_shift(n, span, p):
    """ Shift down by -p% of p if p is negative, else shift up by p% of span
    """
    return n + (span * (p / 100.0))

def tests_of(sf_data):
    return sf_data[0][1].keys()

def test_name(test):
    return test[len("captures::cap_"):].replace("_", "-")

def feature_name(feature):
    return feature[len("captures-"):].replace("ds-es-sl", "all")

if __name__ == "__main__":
    main()
