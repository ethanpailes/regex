#!/usr/bin/env python3

import matplotlib.pyplot as plt; plt.rcdefaults()
import numpy as np
import matplotlib.pyplot as plt

import sys
import csv
import pdb

def main():
    sf_data = []
    for sf in sys.argv[1:]:
        rows = {}
        with open(sf + ".bench.csv", "r") as f:
            for row in csv.DictReader(f):
                rows[row["test_name"]] = row
        sf_data.append((int(sf), rows))

    for t in tests_of(sf_data):
        graph_all_features(sf_data, t)
        plt.savefig(test_name(t) + ".png")
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

def graph_test(sf_data, test, features):
    """ Produce a line graph with one line per feature.
    """

    xmin = sys.maxsize
    xmax = 0

    ymax = 0
    ymin = sys.maxsize
    for feature in features:
        scale = []
        running_time = []
        error = []

        for (sf, data) in sf_data:
            scale.append(sf)

            rt = int(data[test][feature + "_time"].replace(",", ""))
            running_time.append(rt)

            err = int(data[test][feature + "_error"].replace(",", ""))
            error.append(err)

        xmax = max(xmax, max(scale))
        xmin = min(xmin, min(scale))

        ymax = max(ymax, max(map(lambda x: x[0] + x[1],
                            zip(running_time, error))))
        ymin = min(ymin, min(map(lambda x: x[0] - x[1],
                                zip(running_time, error))))

        plt.errorbar(
            scale,
            running_time,
            yerr=error, fmt='o',
            label=feature,
        )

    plt.xlabel("Scaling Factor")
    plt.ylabel("Running Time")
    plt.title(test_name(test))
    plt.ylim((percent_shift(ymin, ymax - ymin, -10.0),
              percent_shift(ymax, ymax - ymin, 10.0)))
    plt.xlim((percent_shift(xmin, xmax - xmin, -10.0),
              percent_shift(xmax, xmax - xmin, 10.0)))
    plt.legend()

def percent_shift(n, span, p):
    """ Shift down by -p% of p if p is negative, else shift up by p% of span
    """
    return n + (span * (p / 100.0))

def tests_of(sf_data):
    return sf_data[0][1].keys()

def test_name(test):
    return test[len("captures::cap_"):]

if __name__ == "__main__":
    main()
