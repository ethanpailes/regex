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

    graph_all_features(sf_data, "captures::cap_middle")
    plt.show()

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

        plt.errorbar(
            scale,
            running_time,
            yerr=error, fmt='o',
            label=feature,
        )

    plt.xlabel("Scaling Factor")
    plt.ylabel("Running Time")
    # plt.yscale("log")
    plt.xscale("log")
    plt.title(test)
    plt.legend()

if __name__ == "__main__":
    main()
