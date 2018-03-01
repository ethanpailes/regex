#!/usr/bin/env python3

import urllib.request
import tarfile
import glob
import os
import re
import pdb
import shutil
import json
import sys
from subprocess import call

RE_REGEX = re.compile(r"Regex::new\((r?\".*?\")\)")
CRATES_INDEX_DIR = "../crates.io-index"
OUTFILE = "./scraped_regex.txt"

def main():
    global CRATES_INDEX_DIR

    resume = None
    if len(sys.argv) == 2:
        resume = sys.argv[1]

    CRATES_INDEX_DIR = os.path.abspath(CRATES_INDEX_DIR)
    out = open(OUTFILE, "w" if resume == None else "a")
    os.chdir("/tmp")

    for (name, vers) in iter_crates():
        if resume:
            if name != resume:
                continue
            else:
                resume = None

        print((name, vers))

        with Crate(name, vers) as c:
            for line in c.iter_lines():
                for r in RE_REGEX.findall(line):
                    print(r)
                    out.write("{}\t{}\t{}\n".format(name, vers, r))
                    out.flush()

    #with Crate("regex", "0.2.6") as c:
    #    for line in c.iter_lines():
    #        for r in RE_REGEX.findall(line):
    #            print(r)

def iter_crates():
    exclude = set(["config.json", ".git"])
    for crate_index_file in iter_files(CRATES_INDEX_DIR, exclude=exclude):
        with open(crate_index_file) as f:
            most_recent = list(f)
            most_recent = most_recent[len(most_recent) - 1]

            crate_info = json.loads(most_recent)
            if "regex" not in set(d["name"] for d in crate_info["deps"]):
                continue

            if crate_info["yanked"]:
                continue
            yield (crate_info["name"], crate_info["vers"])

def iter_files(d, exclude=set()):
    for x in os.listdir(d):
        if x in exclude:
            continue

        fullfp = os.path.abspath(d + "/" + x)
        if os.path.isfile(fullfp):
            yield fullfp
        elif os.path.isdir(fullfp):
            for f in iter_files(fullfp, exclude):
                yield f


class Crate(object):
    def __init__(self, name, version):
        self.name = name
        self.version = version
        self.url = "https://crates.io/api/v1/crates/{name}/{version}/download".format(
                name=self.name, version=self.version)
        self.filename = "/tmp/{}-{}.tar.gz".format(self.name, self.version)

    def __enter__(self):
        urllib.request.urlretrieve(self.url, self.filename)

        call("tar -xf {}".format(self.filename), shell=True)
        #tar = tarfile.open(self.filename, "r:gz")
        #tar.extractall()
        #tar.close()

        return self

    def __exit__(self, ty, value, tb):
        shutil.rmtree(self.filename[:-len(".tar.gz")])
        os.remove(self.filename)

    def iter_srcs(self):
        g = "{crate}/**/*.rs".format(crate=self.filename[:-len(".tar.gz")])
        for rsrc in glob.iglob(g):
            yield rsrc

    def iter_lines(self):
        for src in self.iter_srcs():
            with open(src) as f:
                for line in f:
                    yield line

if __name__ == "__main__":
    main()
